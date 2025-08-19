import express, { Request, Response } from "express";
import { request } from "undici";
import * as zlib from "node:zlib";
import { parse as parseUrlLegacy } from "node:url";
import { URL } from "node:url";
import { parse as parseQuery } from "node:querystring";
import { XMLParser } from "fast-xml-parser";
import pLimit from "p-limit";
import { createHash } from "node:crypto";
import { promises as dns } from "node:dns";
import net from "node:net";

const app = express();
app.use(express.json({ limit: "1mb" }));

// -------------------------------
// Types
// -------------------------------
type CrawlOptions = {
  includeSubdomains?: boolean;
  maxDepth?: number;
  maxPages?: number;
  concurrency?: number;
  pageTimeoutMs?: number;
  userAgent?: string;
  chunk?: boolean; // not used in this initial drop; response is one array
  flattenForSheets?: boolean;
  guessCommonSlugs?: boolean;
};

type Row = {
  url: string;
  path: string;
  title: string | null;
  is_orphan: boolean;
  noindex: boolean;
  nofollow: boolean;
};

type PageInfo = {
  url: string;
  depth: number;
  parents: Set<string>;
  discoveredVia: Set<"sitemap" | "crawl" | "guess">;
  status?: number;
  contentType?: string | null;
  title?: string | null;
  noindex?: boolean;
  nofollow?: boolean;
  canonical?: string | null;
  lastmod?: string | null; // from sitemap
  sourceSitemaps?: Set<string>;
};

// -------------------------------
// Config defaults
// -------------------------------
const DEFAULTS: Required<CrawlOptions> = {
  includeSubdomains: false,
  maxDepth: 25,
  maxPages: 5000,
  concurrency: 8,
  pageTimeoutMs: 12000,
  userAgent: "AutoMartianCrawler/1.0 (+https://automartian.example)",
  chunk: false,
  flattenForSheets: true,
  guessCommonSlugs: false
};

// -------------------------------
// Utilities
// -------------------------------
const TRACKING_PARAM_PREFIXES = ["utm_", "utm", "fbclid", "gclid", "mc_cid", "mc_eid"];

function isPrivateIp(ip: string): boolean {
  if (net.isIP(ip) === 4) {
    const parts = ip.split(".").map(Number);
    if (parts[0] === 10) return true;
    if (parts[0] === 172 && parts[1] >= 16 && parts[1] <= 31) return true;
    if (parts[0] === 192 && parts[1] === 168) return true;
    if (parts[0] === 127) return true;
  } else if (net.isIP(ip) === 6) {
    // Basic checks for localhost/link-local/unique-local
    if (ip === "::1") return true;
    if (ip.startsWith("fe80:")) return true; // link-local
    if (ip.startsWith("fd") || ip.startsWith("fc")) return true; // unique local
  }
  return false;
}

async function assertNotSSRF(hostname: string) {
  try {
    const addrs = await dns.lookup(hostname, { all: true, verbatim: false });
    for (const a of addrs) {
      if (isPrivateIp(a.address)) {
        throw new Error(`Resolved to private IP (${a.address})`);
      }
    }
  } catch (e: any) {
    // If DNS fails, allow HTTP to decide; only block if private.
    if (String(e?.message || "").includes("private IP")) throw e;
  }
}

function stripTrackingParams(u: URL) {
  const keysToDelete: string[] = [];
  u.searchParams.forEach((_, key) => {
    const lower = key.toLowerCase();
    if (TRACKING_PARAM_PREFIXES.some(p => lower.startsWith(p))) {
      keysToDelete.push(key);
    }
  });
  keysToDelete.forEach(k => u.searchParams.delete(k));
}

function normalizeInputUrl(raw: string): string {
  let s = raw.trim();
  if (!/^https?:\/\//i.test(s)) {
    // Default to https
    s = "https://" + s.replace(/^\/+/, "");
  }
  // Remove fragments
  const u = new URL(s);
  u.hash = "";
  // Force root path for seed normalization
  // (We'll separately keep a "home" URL to start at root)
  if (!u.pathname || u.pathname === "/" || u.pathname === "") {
    u.pathname = "/";
  }
  stripTrackingParams(u);
  // Lowercase host, strip default ports
  u.host = u.hostname.toLowerCase() + (u.port ? `:${u.port}` : "");
  // Remove trailing slash duplication
  if (!u.search && u.pathname !== "/") {
    u.pathname = u.pathname.replace(/\/+$/, "") || "/";
  }
  return u.toString();
}

function siteRootFromAny(raw: string): { https: string; http: string; host: string } {
  const n = normalizeInputUrl(raw);
  const u = new URL(n);
  // Collapse to root path
  u.pathname = "/";
  u.search = "";
  const https = "https://" + u.host + "/";
  const http = "http://" + u.host + "/";
  return { https, http, host: u.host };
}

function sameHost(target: URL, baseHost: string, includeSubdomains: boolean): boolean {
  const t = target.hostname.replace(/^www\./i, "").toLowerCase();
  const b = baseHost.replace(/^www\./i, "").toLowerCase();
  if (t === b) return true;
  if (includeSubdomains && t.endsWith("." + b)) return true;
  return false;
}

function isLikelyHtml(u: URL): boolean {
  const path = u.pathname.toLowerCase();
  // Skip non-HTML by extension
  if (/\.(pdf|zip|rar|7z|gz|tar|jpg|jpeg|png|gif|webp|svg|mp4|avi|mov|wmv|mkv|mp3|wav|ogg|webm|woff2?|ttf|otf|eot|css|js|json)$/i.test(path)) {
    return false;
  }
  return true;
}

// Skip paths: admin/system + WP taxonomy + search
const SKIP_PATH_PATTERNS: RegExp[] = [
  /^\/wp-admin(?:\/|$)/i,
  /^\/wp-login(?:\/|$)/i,
  /^\/admin(?:\/|$)/i,
  /^\/user(?:\/|$)/i,
  /^\/dashboard(?:\/|$)/i,
  /^\/cgi-bin(?:\/|$)/i,
  /^\/cart(?:\/|$)/i,
  /^\/checkout(?:\/|$)/i,
  /^\/my-account(?:\/|$)/i,
  /^\/xmlrpc\.php$/i,
  /^\/umbraco(?:\/|$)/i,
  /^\/sitecore(?:\/|$)/i,
  /^\/typo3(?:\/|$)/i,
  /^\/drupal(?:\/|$)/i,
  /^\/ghost(?:\/|$)/i,
  /^\/server-status(?:\/|$)/i,
  /^\/[^/]+\.php$/i, // root-level php files

  // WordPress taxonomy archives
  /^\/tag(?:\/|$)/i,
  /^\/category(?:\/|$)/i,
  /^\/author(?:\/|$)/i,

  // Search pages
  /^\/search(?:\/|$)/i,

  // Custom exclusions
  /^\/wpa-stats-type(?:\/|$)/i,   // exclude /wpa-stats-type/
  /\.kml(?:\?|$)/i                // exclude *.kml
];

function shouldSkipPath(u: URL): boolean {
  const p = u.pathname;
  if (SKIP_PATH_PATTERNS.some(rx => rx.test(p))) return true;

  // Search query (?s=)
  const q = u.searchParams.toString().toLowerCase();
  if (/(^|&)s=/.test(q)) return true;

  return false;
}

function canonicalKey(u: URL): string {
  // Normalize: strip fragments (already), strip tracking params; lower host; keep path and query
  const copy = new URL(u.toString());
  copy.hash = "";
  stripTrackingParams(copy);
  copy.host = copy.hostname.toLowerCase() + (copy.port ? `:${copy.port}` : "");
  const key = `${copy.protocol}//${copy.host}${copy.pathname}${copy.search}`;
  return key;
}

function sha1(s: string): string {
  return createHash("sha1").update(s).digest("hex");
}

async function httpGet(
  url: string,
  ua: string,
  timeoutMs: number
): Promise<{ status: number; headers: Record<string, string>; body: Buffer }> {
  const ctrl = new AbortController();
  const t = setTimeout(() => ctrl.abort(), timeoutMs).unref();
  try {
    const res = await request(url, {
      method: "GET",
      headers: { "User-Agent": ua, "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8" },
      signal: ctrl.signal,
      maxRedirections: 5
    });
    const status = res.statusCode;
    const headers: Record<string, string> = {};
    for (const [k, v] of Object.entries(res.headers)) {
      const vv = Array.isArray(v) ? v[0] : (v as string | undefined);
      if (vv) headers[k.toLowerCase()] = vv;
    }
    const arrayBuf = await res.body.arrayBuffer();
    let body: Buffer = Buffer.from(arrayBuf as ArrayBuffer);

    // Transparently handle gzip/deflate if server didn't
    const ce = headers["content-encoding"];
    if (ce === "gzip") body = zlib.gunzipSync(body);
    else if (ce === "deflate") body = zlib.inflateSync(body);

    // Cap body size to ~2MB
    const MAX = 2 * 1024 * 1024;
    if (body.length > MAX) body = body.subarray(0, MAX);

    return { status, headers, body };
  } finally {
    clearTimeout(t);
  }
}

function parseRobotsForSitemaps(robotsTxt: string): string[] {
  const out: string[] = [];
  for (const line of robotsTxt.split(/\r?\n/)) {
    const m = line.match(/^\s*sitemap:\s*(\S+)\s*$/i);
    if (m) out.push(m[1].trim());
  }
  return out;
}

async function tryFetchText(u: string, ua: string, timeoutMs: number): Promise<string | null> {
  try {
    const res = await httpGet(u, ua, timeoutMs);
    if (res.status >= 200 && res.status < 300) {
      return res.body.toString("utf8");
    }
  } catch { /* ignore */ }
  return null;
}

async function tryFetchBuffer(u: string, ua: string, timeoutMs: number): Promise<Buffer | null> {
  try {
    const res = await httpGet(u, ua, timeoutMs);
    if (res.status >= 200 && res.status < 300) {
      return res.body;
    }
  } catch { /* ignore */ }
  return null;
}

async function discoverSitemaps(rootUrl: string, ua: string, timeoutMs: number): Promise<string[]> {
  const base = new URL(rootUrl);
  const host = `${base.protocol}//${base.host}`;
  const candidates = new Set<string>();

  // robots.txt
  const robotsUrl = `${host}/robots.txt`;
  const robots = await tryFetchText(robotsUrl, ua, timeoutMs);
  if (robots) {
    for (const s of parseRobotsForSitemaps(robots)) candidates.add(s);
  }

  // Common fallbacks
  ["/sitemap.xml", "/sitemap_index.xml", "/sitemap.xml.gz", "/sitemap_index.xml.gz"].forEach(p =>
    candidates.add(host + p)
  );

  return Array.from(candidates);
}

function parseXmlSitemap(xml: string): { urls: { loc: string; lastmod?: string }[], nested: string[] } {
  const parser = new XMLParser({
    ignoreAttributes: false,
    attributeNamePrefix: "",
  });
  const j = parser.parse(xml);

  const urls: { loc: string; lastmod?: string }[] = [];
  const nested: string[] = [];

  // urlset -> url[]
  if (j.urlset?.url) {
    const items = Array.isArray(j.urlset.url) ? j.urlset.url : [j.urlset.url];
    for (const it of items) {
      if (it.loc) urls.push({ loc: String(it.loc), lastmod: it.lastmod ? String(it.lastmod) : undefined });
    }
  }

  // sitemapindex -> sitemap[]
  if (j.sitemapindex?.sitemap) {
    const items = Array.isArray(j.sitemapindex.sitemap) ? j.sitemapindex.sitemap : [j.sitemapindex.sitemap];
    for (const it of items) {
      if (it.loc) nested.push(String(it.loc));
    }
  }

  return { urls, nested };
}

async function fetchAndParseSitemap(url: string, ua: string, timeoutMs: number): Promise<{ urls: { loc: string; lastmod?: string }[], nested: string[] } | null> {
  const isGz = /\.gz(\?|$)/i.test(url);
  let xml: string | null = null;
  if (isGz) {
    const buf = await tryFetchBuffer(url, ua, timeoutMs);
    if (!buf) return null;
    try {
      const unz = zlib.gunzipSync(buf);
      xml = unz.toString("utf8");
    } catch {
      return null;
    }
  } else {
    xml = await tryFetchText(url, ua, timeoutMs);
  }
  if (!xml) return null;
  return parseXmlSitemap(xml);
}

async function harvestSitemaps(
  root: string,
  baseHost: string,
  includeSubdomains: boolean,
  ua: string,
  timeoutMs: number
): Promise<{ pages: Map<string, PageInfo>; usedSitemaps: Set<string> }> {
  const pages = new Map<string, PageInfo>();
  const usedSitemaps = new Set<string>();
  const toVisit = await discoverSitemaps(root, ua, timeoutMs);
  const seen = new Set<string>(toVisit);

  while (toVisit.length) {
    const sm = toVisit.pop()!;
    const parsed = await fetchAndParseSitemap(sm, ua, timeoutMs);
    if (!parsed) continue;
    usedSitemaps.add(sm);

    for (const n of parsed.nested) {
      if (!seen.has(n)) {
        seen.add(n);
        toVisit.push(n);
      }
    }
    for (const u of parsed.urls) {
      try {
        const url = new URL(u.loc);
        if (!sameHost(url, baseHost, includeSubdomains)) continue;
        if (!isLikelyHtml(url)) continue;
        if (shouldSkipPath(url)) continue;

        const key = canonicalKey(url);
        const info = pages.get(key) ?? {
          url: url.toString(),
          depth: 0,
          parents: new Set<string>(),
          discoveredVia: new Set<"sitemap" | "crawl" | "guess">(),
          status: undefined,
          contentType: undefined,
          title: undefined,
          noindex: false,
          nofollow: false,
          canonical: null,
          lastmod: undefined,
          sourceSitemaps: new Set<string>()
        };
        info.discoveredVia.add("sitemap");
        if (u.lastmod) info.lastmod = u.lastmod;
        info.sourceSitemaps?.add(sm);
        pages.set(key, info);
      } catch {
        // ignore malformed locs
      }
    }
  }

  // Ensure root is present
  try {
    const u = new URL(root);
    const key = canonicalKey(u);
    if (!pages.has(key)) {
      pages.set(key, {
        url: u.toString(),
        depth: 0,
        parents: new Set<string>(),
        discoveredVia: new Set<"sitemap" | "crawl" | "guess">(),
        status: undefined,
        contentType: undefined,
        title: undefined,
        noindex: false,
        nofollow: false,
        canonical: null,
        lastmod: undefined,
        sourceSitemaps: new Set<string>()
      });
    }
  } catch { /* ignore */ }

  return { pages, usedSitemaps };
}

function extractMetaRobots(content: string): { noindex: boolean; nofollow: boolean } {
  // meta name="robots" content="noindex,nofollow"
  const m = content.toLowerCase();
  const noindex = /\bnoindex\b/.test(m);
  const nofollow = /\bnofollow\b/.test(m);
  return { noindex, nofollow };
}

function getTitleFromHtml(html: string): string | null {
  const m = html.match(/<title[^>]*>([\s\S]*?)<\/title>/i);
  if (!m) return null;
  return decodeHTMLEntities(m[1].trim());
}

function decodeHTMLEntities(s: string): string {
  // Minimal decoding
  return s
    .replace(/&amp;/g, "&")
    .replace(/&lt;/g, "<")
    .replace(/&gt;/g, ">")
    .replace(/&quot;/g, '"')
    .replace(/&#39;/g, "'");
}

function getCanonicalFromHtml(html: string, baseUrl: URL): string | null {
  const m = html.match(/<link\s+[^>]*rel=["']canonical["'][^>]*>/i);
  if (!m) return null;
  const tag = m[0];
  const hrefM = tag.match(/\shref=["']([^"']+)["']/i);
  if (!hrefM) return null;
  try {
    const u = new URL(hrefM[1], baseUrl);
    return u.toString();
  } catch {
    return null;
  }
}

function extractMetaRobotsFromHtml(html: string): { noindex: boolean; nofollow: boolean } {
  // Allow multiple tags; merge
  let noindex = false, nofollow = false;
  const tags = html.match(/<meta\s+[^>]*name=["']robots["'][^>]*>/ig) || [];
  for (const tag of tags) {
    const contentM = tag.match(/\scontent=["']([^"']+)["']/i);
    if (contentM) {
      const r = extractMetaRobots(contentM[1]);
      noindex = noindex || r.noindex;
      nofollow = nofollow || r.nofollow;
    }
  }
  return { noindex, nofollow };
}

// -------------------------------
// Crawl
// -------------------------------
async function crawlSite(
  seedRoot: string,
  baseHost: string,
  includeSubdomains: boolean,
  opts: Required<CrawlOptions>
): Promise<Row[]> {
  await assertNotSSRF(baseHost);

  // 1) Harvest sitemaps
  const { pages: sitemapPages, usedSitemaps } = await harvestSitemaps(seedRoot, baseHost, includeSubdomains, opts.userAgent, opts.pageTimeoutMs);

  // 2) BFS crawl; seed frontier with home + sitemap URLs
  const frontier: { url: URL; depth: number; parent?: string }[] = [];
  const seenKeys = new Set<string>();
  const pageMap: Map<string, PageInfo> = new Map(sitemapPages);

  // Ensure both https and http attempt for home, trying https first
  const homeHttps = new URL(seedRoot);
  const homeHttp = new URL(seedRoot.replace(/^https:/, "http:"));

  frontier.push({ url: homeHttps, depth: 0 });
  const sitemapList = Array.from(sitemapPages.values());
  for (const p of sitemapList) {
    try {
      const u = new URL(p.url);
      frontier.push({ url: u, depth: 0 });
    } catch { /* ignore */ }
  }

  const limit = pLimit(opts.concurrency);
  let processed = 0;

  async function handlePage(target: URL, depth: number, parent?: string) {
    if (depth > opts.maxDepth) return;

    // Host check
    if (!sameHost(target, baseHost, includeSubdomains)) return;
    if (!isLikelyHtml(target)) return;
    if (shouldSkipPath(target)) return;

    const key = canonicalKey(target);
    if (seenKeys.has(key)) {
      // add parent linkage if known
      const info = pageMap.get(key);
      if (info && parent) info.parents.add(parent);
      return;
    }
    seenKeys.add(key);

    // Initialize page info
    const info: PageInfo = pageMap.get(key) ?? {
      url: target.toString(),
      depth,
      parents: new Set<string>(),
      discoveredVia: new Set<"sitemap" | "crawl" | "guess">(),
      status: undefined,
      contentType: undefined,
      title: undefined,
      noindex: false,
      nofollow: false,
      canonical: null,
      lastmod: undefined,
      sourceSitemaps: new Set<string>()
    };
    if (parent) info.parents.add(parent);
    info.discoveredVia.add("crawl");
    info.depth = Math.min(info.depth ?? depth, depth);
    pageMap.set(key, info);

    // request
    let finalUrl = target;
    let res;
    try {
      res = await httpGet(finalUrl.toString(), opts.userAgent, opts.pageTimeoutMs);
      if (res.status >= 400 && finalUrl.protocol === "https:") {
        // quick fallback to http if https fails badly
        const alt = new URL(finalUrl.toString().replace(/^https:/, "http:"));
        res = await httpGet(alt.toString(), opts.userAgent, opts.pageTimeoutMs);
        finalUrl = alt;
      }
    } catch {
      // mark unreachable
      info.status = 0;
      return;
    }
    info.status = res.status;
    info.contentType = (res.headers["content-type"] || null);

    const ctype = info.contentType || "";
    if (!/text\/html|application\/xhtml\+xml/i.test(ctype)) {
      return; // non-HTML: do not parse or enqueue
    }

    const html = res.body.toString("utf8");

    // Title
    info.title = getTitleFromHtml(html);

    // Canonical
    const canon = getCanonicalFromHtml(html, finalUrl);
    if (canon) {
      try {
        const cu = new URL(canon, finalUrl);
        // Re-key to canonical if same-host & viable
        if (sameHost(cu, baseHost, includeSubdomains) && isLikelyHtml(cu) && !shouldSkipPath(cu)) {
          info.canonical = cu.toString();
          const ck = canonicalKey(cu);
          // Merge info under canonical key
          if (ck !== key) {
            const existing = pageMap.get(ck) ?? {
              url: cu.toString(),
              depth: Math.min(depth, info.depth),
              parents: new Set<string>(),
              discoveredVia: new Set<"sitemap" | "crawl" | "guess">(),
              status: undefined,
              contentType: undefined,
              title: undefined,
              noindex: false,
              nofollow: false,
              canonical: null,
              lastmod: info.lastmod,
              sourceSitemaps: new Set<string>()
            };
            // merge fields
            existing.parents = new Set<string>([...existing.parents, ...info.parents]);
            info.discoveredVia.forEach(d => existing.discoveredVia.add(d));
            if (info.title && !existing.title) existing.title = info.title;
            if (info.status && !existing.status) existing.status = info.status;
            if (info.contentType && !existing.contentType) existing.contentType = info.contentType;
            existing.noindex = existing.noindex || info.noindex || false;
            existing.nofollow = existing.nofollow || info.nofollow || false;
            if (info.sourceSitemaps) info.sourceSitemaps.forEach(s => existing.sourceSitemaps?.add(s));
            pageMap.set(ck, existing);
            pageMap.delete(key);
          }
        }
      } catch { /* ignore bad canonical */ }
    }

    // Robots meta
    const meta = extractMetaRobotsFromHtml(html);
    info.noindex = !!meta.noindex;
    info.nofollow = !!meta.nofollow;

    // Extract links
    // Lightweight anchor extraction to avoid full Cheerio cost on huge pages
    const hrefs: string[] = [];
    const anchorRegex = /<a\s+[^>]*href=["']([^"']+)["'][^>]*>/ig;
    let m: RegExpExecArray | null;
    while ((m = anchorRegex.exec(html)) !== null) {
      hrefs.push(m[1]);
    }

    for (const href of hrefs) {
      let next: URL | null = null;
      try {
        next = new URL(href, finalUrl);
      } catch {
        continue;
      }
      if (!sameHost(next, baseHost, includeSubdomains)) continue;
      if (!isLikelyHtml(next)) continue;
      if (shouldSkipPath(next)) continue;

      if (processed < opts.maxPages) {
        frontier.push({ url: next, depth: depth + 1, parent: finalUrl.toString() });
      }
    }
  }

  while (frontier.length && processed < opts.maxPages) {
    const batch = frontier.splice(0, Math.min(frontier.length, opts.concurrency));
    await Promise.all(
      batch.map(item =>
        limit(async () => {
          processed++;
          await handlePage(item.url, item.depth, item.parent);
        })
      )
    );
  }

  // Optional guesser pass for super-common slugs (disabled by default)
  // (Keeps it lightweight and bounded)
  if (DEFAULTS.guessCommonSlugs) {
    const common = ["/privacy", "/terms", "/about", "/contact", "/rss", "/feed", "/sitemap", "/robots"];
    const root = new URL(seedRoot);
    for (const slug of common) {
      const u = new URL(slug, `${root.protocol}//${root.host}`);
      if (!sameHost(u, baseHost, includeSubdomains)) continue;
      if (shouldSkipPath(u)) continue;
      const key = canonicalKey(u);
      if (pageMap.has(key)) continue;
      try {
        const res = await httpGet(u.toString(), opts.userAgent, opts.pageTimeoutMs);
        if (res.status >= 200 && res.status < 400) {
          const info: PageInfo = {
            url: u.toString(),
            depth: 1,
            parents: new Set<string>(),
            discoveredVia: new Set<"sitemap" | "crawl" | "guess">(["guess"]),
            status: res.status,
            contentType: res.headers["content-type"] || null,
            title: getTitleFromHtml(res.body.toString("utf8")),
            noindex: false,
            nofollow: false,
            canonical: null,
            lastmod: undefined,
            sourceSitemaps: new Set<string>()
          };
          pageMap.set(key, info);
        }
      } catch { /* ignore */ }
    }
  }

  // Compute inbound counts and orphan flags
  const inbound = new Map<string, number>();
  for (const [key, info] of pageMap) {
    inbound.set(key, info.parents.size);
  }

  // Prepare rows
  const rows: Row[] = [];
  const discoveredAt = new Date().toISOString();
  for (const [key, info] of pageMap) {
    const via = info.discoveredVia;
    let dv: Row["discovered_via"] = "crawl";
    if (via.has("sitemap") && via.has("crawl")) dv = "both";
    else if (via.has("sitemap")) dv = "sitemap";
    else if (via.has("guess")) dv = "guess";

    // Orphan = present in sitemap set but never found by internal links (in-degree 0)
    const isOrphan = via.has("sitemap") && (inbound.get(key) || 0) === 0;

    // parent_urls flattened
    const parentUrls = Array.from(info.parents.values()).join(";");

    rows.push({
      url: info.url,
      path: new URL(info.url).pathname || "/",
      title: info.title ?? null,
      is_orphan: isOrphan,
      noindex: !!info.noindex,
      nofollow: !!info.nofollow
    });
  }

  return rows;
}

// -------------------------------
// HTTP API
// -------------------------------
app.post("/crawl", async (req: Request, res: Response) => {
  const rawUrl = String(req.body?.url || "").trim();
  if (!rawUrl) return res.status(400).json({ error: "Missing 'url' in body" });

  const o: CrawlOptions = { ...DEFAULTS, ...(req.body?.options || {}) };

  let seedHttps: string, seedHttp: string, host: string;
  try {
    const root = siteRootFromAny(rawUrl);
    seedHttps = root.https;
    seedHttp = root.http;
    host = root.host;
  } catch (e: any) {
    return res.status(400).json({ error: "Invalid URL" });
  }

  try {
    // Prefer HTTPS seed; if it fails immediately, fallback to HTTP by swapping protocol within crawl
    const rows = await crawlSite(seedHttps, host, !!o.includeSubdomains, {
      ...DEFAULTS,
      ...o
    });

    // Sheets-friendly: root-level array of objects
    return res.status(200).json(rows);
  } catch (e: any) {
    return res.status(500).json({ error: String(e?.message || e) });
  }
});

// Healthcheck
app.get("/", (_req, res) => {
  res.type("text/plain").send("OK");
});

// -------------------------------
// Start
// -------------------------------
const PORT = process.env.PORT ? Number(process.env.PORT) : 3000;
app.listen(PORT, () => {
  console.log(`Crawler listening on :${PORT}`);
});
