require('dotenv').config();
// pm2 logs carry no timestamps, which made incidents hard to line up with
// OME's and nginx's logs - every console line now starts with the UTC time.
for (const level of ['log', 'info', 'warn', 'error']) {
  const orig = console[level].bind(console);
  console[level] = (...args) => orig(new Date().toISOString(), ...args);
}
const http = require('http');
const express = require('express');
const { Server } = require('socket.io');
const { parseCookie } = require('cookie');
const Database = require('better-sqlite3');
const bcrypt = require('bcrypt');
const jwt = require('jsonwebtoken');
const cookieParser = require('cookie-parser');
const cors = require('cors');
const { spawn } = require('child_process');
const fs = require('fs');
const { pipeline } = require('stream');
const path = require('path');
const crypto = require('crypto');
const { initAccessTokens, requireAccessSession, gateStream, hasAccessSession } = require('./accessTokens');
const rateLimit = require('express-rate-limit');

// ---------- Channels ----------
// The site runs two streams side by side: "live" (biggboss24hrs.com, OME
// application "app") and "episode" (episode.biggboss24hrs.com, OME application
// "episode"). Both hostnames reach this one backend and serve the same page
// code, so the channel is decided by which hostname the request arrived on -
// that way the episode page can call the exact same API paths as /live and
// automatically get its own stream, title, chat and polls.
const SITE_ORIGIN = process.env.SITE_ORIGIN || 'https://biggboss24hrs.com';
const EPISODE_HOST = 'episode.biggboss24hrs.com';
const EPISODE_ORIGIN = `https://${EPISODE_HOST}`;
const COOKIE_DOMAIN = '.biggboss24hrs.com'; // shared by both hostnames, only ever used in production
const CHANNELS = ['live', 'episode'];
const CHANNEL_OME_APP = { live: 'app', episode: 'episode' };

function channelFromHost(host) {
  return String(host || '').toLowerCase().split(':')[0] === EPISODE_HOST ? 'episode' : 'live';
}
function channelOf(req) { return channelFromHost(req.headers.host); }
function channelOfSocket(socket) { return channelFromHost(socket.handshake.headers.host); }
function roomOf(channel) { return `ch:${channel}`; }

const app = express();
const server = http.createServer(app);
const io = new Server(server, {
  cors: {
    origin: [SITE_ORIGIN, EPISODE_ORIGIN],
    credentials: true
  }
});
const PORT = process.env.PORT || 4000;
const JWT_SECRET = process.env.JWT_SECRET;
const IS_PROD = process.env.NODE_ENV === 'production';

if (!JWT_SECRET) {
  console.error('FATAL: JWT_SECRET is not set in .env. Generate one and set it before starting.');
  process.exit(1);
}

app.set('trust proxy', 1); // Trust Nginx for X-Forwarded-Proto
app.use(express.json());
app.use(cookieParser());
app.use(cors({
  origin: [SITE_ORIGIN, EPISODE_ORIGIN],
  credentials: true
}));

// ---------- Rate limiting ----------
// /api/login and /admin/current-link were both unlimited - the former is
// brute-forceable against 349+ real accounts, the latter leaks the live
// invite link on a single successful guess. nginx now forwards the real
// visitor IP via X-Real-IP (CF-Connecting-IP) rather than Cloudflare's own
// edge IP - every request reaching nginx on 443 already passed through
// Cloudflare (ufw restricts 443 to Cloudflare's ranges only), so this
// header is always authoritative here, unlike trusting X-Forwarded-For's
// chain math. Falls back to req.ip only if the header is ever missing
// (e.g. a direct loopback request during local testing).
//
// Routed through express-rate-limit's own ipKeyGenerator rather than used
// raw: a bare IPv6 address is a near-useless rate-limit key on its own,
// since one client can trivially rotate through billions of addresses
// inside their own /64 - ipKeyGenerator collapses that to a /56 subnet so
// the limit actually holds. (v4 addresses pass through unchanged.) Caught
// this from the library's own startup validation, not the docs - it
// refuses to start with a custom keyGenerator that looks like it skips
// this, exactly to stop this class of bypass from shipping unnoticed.
const { ipKeyGenerator } = rateLimit;

function realIp(req) {
  return ipKeyGenerator(req.headers['x-real-ip'] || req.ip);
}

// Same normalization as realIp() above, for a raw socket.io handshake
// instead of an Express req - used so a banned viewer's IP (or /56 subnet,
// for IPv6) is recorded the same way whether they arrived via HTTP or a
// socket connection.
function realIpFromHandshake(handshake) {
  return ipKeyGenerator(handshake.headers['x-real-ip'] || handshake.address);
}

function makeLimiter(windowMs, max, message) {
  return rateLimit({
    windowMs,
    max,
    keyGenerator: realIp,
    standardHeaders: true,
    legacyHeaders: false,
    message: { error: message }
  });
}

const loginLimiter = makeLimiter(15 * 60 * 1000, 10, 'Too many login attempts. Please try again in 15 minutes.');

// ---------- Access-gated HTML routes (must come BEFORE express.static) ----------
// These intercept requests for the homepage and live page and enforce the
// access_session cookie. Static assets (CSS, JS, images) are still served
// ungated by express.static below so no-access.html can load its own assets.
// The episode address only ever shows the episode page. Main-site pages
// (live, library, sign-in) belong on the main address - sign-in in particular
// must happen there because the X/Google callbacks are registered to it - so
// anything reaching for them on the episode address is sent across.
app.use((req, res, next) => {
  if (channelOf(req) === 'episode'
      && /^\/(live|library)(\/|$)|^\/(login|signup|complete-signup)\.html$/i.test(req.path)) {
    return res.redirect(302, SITE_ORIGIN + req.originalUrl);
  }
  next();
});

// episode.biggboss24hrs.com IS the episode page - its root serves that page
// instead of the home page, behind the same rotating access link as /live.
app.get(['/', '/index.html'], (req, res, next) => {
  if (channelOf(req) !== 'episode') return next();
  if (!EPISODE_REQUIRES_ACCESS_LINK) return servedEpisode();
  return requireAccessSession(req, res, servedEpisode);
  function servedEpisode() {
    res.set('Cache-Control', 'no-store');
    res.sendFile('/var/www/streamflix/episode/index.html');
  }
});

app.get(['/', '/index.html'], requireAccessSession, (req, res) => {
  res.sendFile('/var/www/streamflix/index.html');
});

// Matches production's clean URL (Nginx serves this as /live via the folder trick).
// Locally, this route makes /live work the same way without needing Nginx.
app.get(['/live', '/live/index.html'], requireAccessSession, (req, res) => {
  // Explicit no-store, not just max-age=0: viewers reported seeing hours-old
  // content in a normal (non-incognito) tab while incognito was fine, which
  // points at the browser using a heuristically-cached copy instead of
  // revalidating. no-store removes that ambiguity - the browser can never
  // serve this response from its own cache, full stop.
  res.set('Cache-Control', 'no-store');
  res.sendFile('/var/www/streamflix/live/index.html');
});

// Serve the main website assets from /var/www/streamflix
// dotfiles: 'deny' refuses any path containing a dot-segment (.git/, .claude/,
// .env ...). Express's default ('ignore') only hides dotfiles themselves, NOT
// files inside a dot-folder - which is how the site's .git folder was
// downloadable. nginx refuses these paths as well (first layer).
app.use(express.static('/var/www/streamflix', { dotfiles: 'deny' }));
// Fallback for our own public folder (e.g., no-access.html)
app.use(express.static('public', { dotfiles: 'deny' }));

// ---------- Database setup ----------
const db = new Database('streamflix.db');
db.exec(`
  CREATE TABLE IF NOT EXISTS users (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    email TEXT UNIQUE NOT NULL,
    username TEXT UNIQUE NOT NULL,
    password_hash TEXT NOT NULL,
    role TEXT NOT NULL DEFAULT 'user',
    is_admin INTEGER NOT NULL DEFAULT 0,
    created_at TEXT NOT NULL DEFAULT (datetime('now'))
  );

  CREATE TABLE IF NOT EXISTS settings (
    key TEXT PRIMARY KEY,
    value TEXT
  );

  CREATE TABLE IF NOT EXISTS stream_meta (
    key TEXT PRIMARY KEY,
    value TEXT NOT NULL
  );

  CREATE TABLE IF NOT EXISTS chat_messages (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    username TEXT NOT NULL,
    message TEXT NOT NULL,
    created_at DATETIME DEFAULT CURRENT_TIMESTAMP
  );

  CREATE TABLE IF NOT EXISTS library_folders (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    title TEXT NOT NULL,
    description TEXT,
    thumbnail_url TEXT,
    created_at DATETIME DEFAULT CURRENT_TIMESTAMP
  );

  CREATE TABLE IF NOT EXISTS library_videos (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    folder_id INTEGER NOT NULL,
    title TEXT NOT NULL,
    video_url TEXT NOT NULL,
    drive_id TEXT,
    description TEXT,
    created_at DATETIME DEFAULT CURRENT_TIMESTAMP,
    FOREIGN KEY(folder_id) REFERENCES library_folders(id) ON DELETE CASCADE
  );

  CREATE TABLE IF NOT EXISTS polls (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    question TEXT NOT NULL,
    status TEXT NOT NULL DEFAULT 'open',
    created_by TEXT,
    created_at DATETIME DEFAULT CURRENT_TIMESTAMP,
    closed_at DATETIME
  );

  CREATE TABLE IF NOT EXISTS poll_options (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    poll_id INTEGER NOT NULL,
    label TEXT NOT NULL,
    position INTEGER DEFAULT 0,
    FOREIGN KEY(poll_id) REFERENCES polls(id) ON DELETE CASCADE
  );

  -- UNIQUE(poll_id, user_id) enforces one vote per user in the DB itself,
  -- so a double-submit or race can't double-count.
  CREATE TABLE IF NOT EXISTS poll_votes (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    poll_id INTEGER NOT NULL,
    option_id INTEGER NOT NULL,
    user_id INTEGER NOT NULL,
    created_at DATETIME DEFAULT CURRENT_TIMESTAMP,
    UNIQUE(poll_id, user_id),
    FOREIGN KEY(poll_id) REFERENCES polls(id) ON DELETE CASCADE
  );

  CREATE INDEX IF NOT EXISTS idx_poll_votes_poll ON poll_votes(poll_id);
  CREATE INDEX IF NOT EXISTS idx_poll_options_poll ON poll_options(poll_id);
`);

try {
  db.exec(`ALTER TABLE users ADD COLUMN role TEXT NOT NULL DEFAULT 'user'`);
} catch (e) {}

// Multi-poll support: each poll now carries its own fixed lifecycle instead
// of the old "one poll at a time" model. CREATE TABLE IF NOT EXISTS won't add
// columns to an already-existing table, so these are guarded the same way as
// the users.role migration above.
// Sign in with X: a proven X identity locks the username and drives chat
// styling. x_id IS NOT NULL is itself the "locked" flag - no separate
// column needed, since no route anywhere lets a user edit their username.
// SQLite can't add a UNIQUE column via ALTER, so uniqueness comes from a
// partial index instead (only enforced where x_id is actually set).
try { db.exec(`ALTER TABLE users ADD COLUMN x_id TEXT`); } catch (e) {}
try { db.exec(`ALTER TABLE users ADD COLUMN x_handle TEXT`); } catch (e) {}
try { db.exec(`ALTER TABLE users ADD COLUMN x_name TEXT`); } catch (e) {}
try { db.exec(`ALTER TABLE users ADD COLUMN x_verified INTEGER NOT NULL DEFAULT 0`); } catch (e) {}
try { db.exec(`ALTER TABLE users ADD COLUMN x_linked_at TEXT`); } catch (e) {}
try { db.exec(`ALTER TABLE users ADD COLUMN x_pfp_url TEXT`); } catch (e) {}
db.exec(`CREATE UNIQUE INDEX IF NOT EXISTS idx_users_x_id ON users(x_id) WHERE x_id IS NOT NULL`);

// Sign in with Google: unlike X, Google gives a real verified email, so a
// sign-in matching an existing account's email links onto it rather than
// creating a duplicate - see the resolveAccount transaction in the Google
// callback route. No google_verified column: no such concept exists for a
// consumer Google account. No google_email column either: users.email IS
// the real Google email on first signup, and a linked row's users.email
// already equals it by definition (that's how the match was found).
try { db.exec(`ALTER TABLE users ADD COLUMN google_id TEXT`); } catch (e) {}
try { db.exec(`ALTER TABLE users ADD COLUMN google_name TEXT`); } catch (e) {}
try { db.exec(`ALTER TABLE users ADD COLUMN google_pfp_url TEXT`); } catch (e) {}
try { db.exec(`ALTER TABLE users ADD COLUMN google_linked_at TEXT`); } catch (e) {}
// google_id alone is just a login credential - it's set both when a Google
// sign-in links onto an existing account AND when it creates a new one, so
// it can't be used to decide chat display. google_native is true only for
// an account actually CREATED via Google (picked its own username/avatar in
// the completion step) - only that drives the chat badge/blue name/photo.
// A linked account has google_id set but google_native=0 and renders as a
// completely ordinary user - this is what makes linking invisible, which
// is the fix for the bug where linking silently adopted an admin's photo.
try { db.exec(`ALTER TABLE users ADD COLUMN google_native INTEGER NOT NULL DEFAULT 0`); } catch (e) {}
db.exec(`CREATE UNIQUE INDEX IF NOT EXISTS idx_users_google_id ON users(google_id) WHERE google_id IS NOT NULL`);

// A deleted account can otherwise just sign up again through the same
// OAuth identity, since X/Google callbacks only ever check "does this
// google_id/x_id exist as a user" - not "was it ever banned". This table
// is checked independently of the users table so a ban survives account
// deletion. Keyed by identity_type+identity_value so one ban action can
// cover google_id, x_id, and email all at once for whichever the account
// actually had.
db.exec(`
  CREATE TABLE IF NOT EXISTS banned_identities (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    identity_type TEXT NOT NULL,
    identity_value TEXT NOT NULL,
    reason TEXT,
    banned_at TEXT NOT NULL DEFAULT (datetime('now')),
    UNIQUE(identity_type, identity_value)
  );
`);

function isBannedIdentity(type, value) {
  if (!value) return false;
  return !!db.prepare('SELECT 1 FROM banned_identities WHERE identity_type = ? AND LOWER(identity_value) = LOWER(?)')
    .get(type, String(value));
}

function banIdentity(type, value, reason) {
  if (!value) return;
  db.prepare(`
    INSERT INTO banned_identities (identity_type, identity_value, reason) VALUES (?, ?, ?)
    ON CONFLICT(identity_type, identity_value) DO NOTHING
  `).run(type, String(value), reason || null);
}

// One cheap write per socket connect (not per message, not polled) - this
// is what makes "is user X watching" answerable at all, which previously
// required grepping chat/poll history for indirect evidence.
try { db.exec(`ALTER TABLE users ADD COLUMN last_seen DATETIME`); } catch (e) {}

try {
  db.exec(`ALTER TABLE polls ADD COLUMN closes_at DATETIME`);
} catch (e) {}
try {
  db.exec(`ALTER TABLE polls ADD COLUMN expires_at DATETIME`);
} catch (e) {}
db.exec(`CREATE INDEX IF NOT EXISTS idx_polls_status ON polls(status)`);

// Library: a folder is either 'drive' (Google Drive embeds, the original and
// default) or 'r2' (private files in the Cloudflare R2 bucket, served by the
// media Worker). Existing folders/videos keep the 'drive' default untouched.
try { db.exec(`ALTER TABLE library_folders ADD COLUMN storage TEXT NOT NULL DEFAULT 'drive'`); } catch (e) {}
try { db.exec(`ALTER TABLE library_videos ADD COLUMN r2_key TEXT`); } catch (e) {}
try { db.exec(`ALTER TABLE library_videos ADD COLUMN size_bytes INTEGER`); } catch (e) {}
// Card image for R2 videos (Drive videos get theirs from Google): a frame
// grabbed from the video itself, saved under /library/thumbs/.
try { db.exec(`ALTER TABLE library_videos ADD COLUMN thumbnail_url TEXT`); } catch (e) {}
// When the video was recorded (from its file name) - R2 folders list newest
// recording first, whatever order the cards were added in.
try { db.exec(`ALTER TABLE library_videos ADD COLUMN sort_at TEXT`); } catch (e) {}

// "2026-09-06 23-55-54.mp4" or "stream_20260911031543_...mp4" -> "YYYY-MM-DD HH:MM:SS".
// A name with only a date ("2026-10-01.mp4") gets 00:00:00. Unrecognised -> null.
function recordingTimeFromKey(key) {
  const base = String(key || '').split('/').pop();
  let m = base.match(/(\d{4})-(\d{2})-(\d{2})[ _T](\d{2})-(\d{2})-(\d{2})/);
  if (m) return `${m[1]}-${m[2]}-${m[3]} ${m[4]}:${m[5]}:${m[6]}`;
  m = base.match(/stream_(\d{4})(\d{2})(\d{2})(\d{2})(\d{2})(\d{2})/);
  if (m) return `${m[1]}-${m[2]}-${m[3]} ${m[4]}:${m[5]}:${m[6]}`;
  m = base.match(/^(\d{4})-(\d{2})-(\d{2})\b/);
  return m ? `${m[1]}-${m[2]}-${m[3]} 00:00:00` : null;
}
for (const v of db.prepare('SELECT id, r2_key FROM library_videos WHERE r2_key IS NOT NULL AND sort_at IS NULL').all()) {
  const t = recordingTimeFromKey(v.r2_key);
  if (t) db.prepare('UPDATE library_videos SET sort_at = ? WHERE id = ?').run(t, v.id);
}
// One row per "watch" (a player session) of an R2 video by a user. Times are
// epoch milliseconds. A watch continues while last_seen_at keeps being renewed.
db.exec(`
  CREATE TABLE IF NOT EXISTS library_watches (
    id INTEGER PRIMARY KEY AUTOINCREMENT,
    user_id INTEGER NOT NULL,
    video_id INTEGER NOT NULL,
    started_at INTEGER NOT NULL,
    last_seen_at INTEGER NOT NULL
  );
  CREATE INDEX IF NOT EXISTS idx_library_watches_uv ON library_watches(user_id, video_id);
`);
// The beta folder: same card (image + description) as "24Hrs Channel BB20",
// with " (Beta)" added; its videos live in R2.
(function seedBetaFolder() {
  const BETA_TITLE = 'BB 24Hrs Channel (Beta)';
  if (db.prepare('SELECT 1 FROM library_folders WHERE title = ?').get(BETA_TITLE)) return;
  const src = db.prepare(`SELECT description, thumbnail_url FROM library_folders WHERE title = '24Hrs Channel BB20'`).get();
  db.prepare(`INSERT INTO library_folders (title, description, thumbnail_url, storage, naming) VALUES (?, ?, ?, 'r2', 'livefeed')`)
    .run(BETA_TITLE, src ? src.description : '', src ? src.thumbnail_url : '');
  console.log(`[Library] Created folder "${BETA_TITLE}" (R2).`);
})();

// Title helper per folder for the admin add/rename form: 'episode'
// ("Episode 27 (WKW Saturday)"), 'livefeed' ("Live Feed 1stOct2026 10:00 -
// 01:00(next day)") or NULL (custom name only). A custom name is always allowed.
try { db.exec(`ALTER TABLE library_folders ADD COLUMN naming TEXT`); } catch (e) {}
db.prepare(`UPDATE library_folders SET naming = 'episode' WHERE naming IS NULL AND title = 'Bigg Boss 20'`).run();
db.prepare(`UPDATE library_folders SET naming = 'livefeed' WHERE naming IS NULL AND title = 'BB 24Hrs Channel (Beta)'`).run();

// Per-channel chat and polls: every row belongs to exactly one page. Existing
// rows predate the episode page, so the DEFAULT 'live' assigns them correctly.
try { db.exec(`ALTER TABLE chat_messages ADD COLUMN channel TEXT NOT NULL DEFAULT 'live'`); } catch (e) {}
try { db.exec(`ALTER TABLE polls ADD COLUMN channel TEXT NOT NULL DEFAULT 'live'`); } catch (e) {}
db.exec(`CREATE INDEX IF NOT EXISTS idx_chat_channel ON chat_messages(channel, id)`);

// ---------- Access-token system ----------
// Registers /access, /admin/current-link, and starts the daily rotation
// (every 24h at 23:30 UTC = 05:00 IST).
// Uses the same db, jwt, JWT_SECRET, and IS_PROD already established above.
initAccessTokens(
  db,
  app,
  jwt,
  IS_PROD,
  JWT_SECRET,
  process.env.SITE_ORIGIN || 'https://biggboss24hrs.com'
);

// 2. Automated 24-Hour Cleanup Function
function cleanupOldMessages() {
  try {
    const result = db.prepare(`
      DELETE FROM chat_messages 
      WHERE created_at < datetime('now', '-24 hours')
    `).run();
    if (result.changes > 0) {
      console.log(`[Chat Cleanup] Purged ${result.changes} message(s) older than 24h.`);
    }
  } catch (err) {
    console.error('[Chat Cleanup Error]:', err);
  }
}

// Run cleanup immediately on startup, then every 1 hour
cleanupOldMessages();
setInterval(cleanupOldMessages, 60 * 60 * 1000);

// ---------- Stream titles ----------
// Titles are fully manual now (the old auto-switching schedule, and the reset
// to the default when a stream ended, were removed on purpose): an admin edits
// the title inline on the page it belongs to, and it stays until edited again.
// Each channel keeps its own title.
const TITLE_DEFAULTS = { live: '24Hrs Channel', episode: 'Episode' };

function titleKey(channel) {
  return channel === 'episode' ? 'stream_title:episode' : 'stream_title';
}

function getTitle(channel) {
  const row = db.prepare('SELECT value FROM settings WHERE key = ?').get(titleKey(channel));
  return row ? row.value : TITLE_DEFAULTS[channel];
}

// Seed each channel's default title if none is set yet (first boot).
for (const ch of CHANNELS) {
  if (!db.prepare('SELECT 1 FROM settings WHERE key = ?').get(titleKey(ch))) {
    db.prepare('INSERT INTO settings (key, value) VALUES (?, ?)').run(titleKey(ch), TITLE_DEFAULTS[ch]);
  }
}

// Polls OvenMediaEngine directly so the backend knows stream liveness
// without a webhook. Fails closed on any error so a transient OME API blip
// is never mistaken for the stream ending (or a new one starting). Each
// channel is polled independently - an error on one (e.g. its OME
// application not loaded) must never stop the other.
const OME_APPS_URL = process.env.OME_APPS_URL || 'http://127.0.0.1:8081/v1/vhosts/default/apps';
const STREAM_POLL_INTERVAL_MS = 2000;

// OME names segments seg_<track>_<seq>_..._<fixed id>_llhls.m4s and resets
// <seq> to 0 on every new publish, so each stream reuses the previous one's
// URLs. Cloudflare must be purged per SESSION, not per offline->live flip:
// OBS reconnects in as little as 7-9s, faster than any flip-sampling poll
// can see (the old once-a-minute cron missed them and served stale video).
// OME's createdTime changes on every publish, so it identifies the session
// even when the gap between two streams is shorter than the poll interval.
// Purging at stream END doesn't work either: between streams OME keeps
// serving the previous session's DVR files, so stuck players would refill
// the edge before the next start. After createdTime changes, OME has wiped
// them, and the first new segment is still ~6s away - that's the window.
const streamStates = {
  live: { live: null, sessionId: null, obs: null },
  episode: { live: null, sessionId: null, obs: null }
};

function sessionSettingKey(channel) {
  return channel === 'episode' ? 'stream_session_id:episode' : 'stream_session_id';
}

function readSetting(key) {
  const row = db.prepare('SELECT value FROM settings WHERE key = ?').get(key);
  return row ? row.value : null;
}

function writeSetting(key, value) {
  db.prepare(`
    INSERT INTO settings (key, value) VALUES (?, ?)
    ON CONFLICT(key) DO UPDATE SET value = excluded.value
  `).run(key, value);
}

async function omeApiGet(url) {
  const authHeader = 'Basic ' + Buffer.from(process.env.OME_API_ACCESS_TOKEN, 'utf8').toString('base64');
  const res = await fetch(url, {
    headers: { Authorization: authHeader },
    signal: AbortSignal.timeout(5000)
  });
  if (!res.ok) throw new Error(`OME API returned ${res.status} for ${url}`);
  return res.json();
}

// Cloudflare caches by host + path, and every host can serve a stream path
// (www. included), so a channel's purge covers each of them. Purging by
// prefix clears only that stream - the other channel's warm cache and the
// cached clips are left alone, which matters when the episode starts and
// /live restarts seconds later for the mode switch.
const CHANNEL_PURGE_PREFIXES = {
  live: ['biggboss24hrs.com/app/', 'www.biggboss24hrs.com/app/', 'episode.biggboss24hrs.com/app/'],
  episode: ['biggboss24hrs.com/episode/', 'www.biggboss24hrs.com/episode/', 'episode.biggboss24hrs.com/episode/']
};

async function purgeCloudflareCache(channels) {
  const zoneId = process.env.CLOUDFLARE_ZONE_ID;
  const apiToken = process.env.CLOUDFLARE_API_TOKEN;
  if (!zoneId || !apiToken) {
    console.error('[Stream] Cloudflare purge skipped: CLOUDFLARE_ZONE_ID / CLOUDFLARE_API_TOKEN not set');
    return false;
  }
  const prefixes = (channels || []).flatMap(ch => CHANNEL_PURGE_PREFIXES[ch] || []);
  // Attempts 1-2 purge just the channels' prefixes; if Cloudflare refuses
  // that, the last attempt falls back to purging everything rather than
  // risk serving a previous session's segments.
  for (let attempt = 1; attempt <= 3; attempt++) {
    const everything = prefixes.length === 0 || attempt === 3;
    try {
      const res = await fetch(`https://api.cloudflare.com/client/v4/zones/${zoneId}/purge_cache`, {
        method: 'POST',
        headers: { Authorization: `Bearer ${apiToken}`, 'Content-Type': 'application/json' },
        body: JSON.stringify(everything ? { purge_everything: true } : { prefixes }),
        signal: AbortSignal.timeout(10000)
      });
      const json = await res.json().catch(() => ({}));
      if (json.success) return true;
      console.error(`[Stream] Cloudflare purge attempt ${attempt} failed (HTTP ${res.status}):`, JSON.stringify(json.errors || null));
    } catch (err) {
      console.error(`[Stream] Cloudflare purge attempt ${attempt} error:`, err.message || err);
    }
  }
  return false;
}

// One channel's current OME state. Throws on any OME error so the caller
// leaves that channel's last known state untouched.
//
// Each channel is TWO OME applications: OBS publishes into "<app>_in", and the
// permanent channel "<app>/stream" (an OME scheduled channel) shows that
// stream while it exists and a slate while it doesn't. The channel - and so
// its DVR - never stops, so:
//   live = the channel exists (a player can play it; the DVR is rewindable)
//   obs  = OBS is actually sending right now (drives "on air" status/banner)
// Channels OBS publishes into directly (the original single-application setup:
// no "<app>_in" intake, no permanent channel). There "live" and "obs" are the
// same thing. The episode went back to this on 2026-10-08, live on 2026-10-09
// (a 1 s OBS blip made the relay desync live's audio and froze players).
const DIRECT_INGEST_CHANNELS = new Set(['live', 'episode']);
async function readChannelStream(channel) {
  const app = CHANNEL_OME_APP[channel];
  const base = `${OME_APPS_URL}/${app}/streams`;
  const direct = DIRECT_INGEST_CHANNELS.has(channel);
  const [inList, list] = await Promise.all([direct ? null : omeApiGet(`${OME_APPS_URL}/${app}_in/streams`), omeApiGet(base)]);
  const live = Array.isArray(list.response) && list.response.length > 0;
  const obs = direct ? live : Array.isArray(inList.response) && inList.response.length > 0;
  let sessionId = null;
  let heights = null; // video heights OME is really producing, null = not known
  if (live) {
    const detail = await omeApiGet(`${base}/stream`);
    sessionId = detail?.response?.input?.createdTime || null;
    if (!sessionId) throw new Error('OME stream detail has no input.createdTime');
    // What the channel is REALLY being built as, read from OME itself: a
    // stream keeps the qualities it started with, so this - not a setting -
    // decides which quality choices viewers are offered.
    const h = (detail?.response?.outputs?.[0]?.tracks || []).filter(t => t.type === 'Video').map(t => t.video?.height);
    if (h.length) heights = h;
  }
  return { live, obs, sessionId, heights };
}

// ---------- Quality lists ----------
// Live is produced as 1080p (passthrough) + 720p + 360p (see
// buildLiveProfiles below); the episode keeps the full ladder. The server can
// only transcode about one full ladder at a time, so live skips 480p - the
// same stream, all day, so nothing ever has to restart when the episode
// starts or ends. A stream keeps the qualities it started with, so the list
// offered to viewers follows what OME is really producing.
const LIVE_QUALITY_KEYS = ['auto', 'q1080', 'q720', 'q360'];
const streamHeights = { live: null, episode: null };

function availableQualityKeys(channel) {
  const h = streamHeights[channel];
  if (h) {
    return Object.keys(STREAM_QUALITY_FILES).filter(k =>
      k === 'auto' || k === 'q1080' || h.includes(Number(k.slice(1))));
  }
  return channel === 'live' ? LIVE_QUALITY_KEYS : Object.keys(STREAM_QUALITY_FILES);
}

// ---------- "Episode is starting" banner ----------
// Live viewers get a short-lived banner when the episode goes on air (after
// it has been off for a while, so an OBS reconnect doesn't repeat it). It is
// sent over the socket to people already on the live page, and to anyone who
// opens it within the next minute; after that it is simply gone.
const EPISODE_BANNER_MS = 60 * 1000;
const EPISODE_BANNER_MIN_OFFLINE_MS = 3 * 60 * 1000;
// A short test stream (OBS checks, a mistaken start) must not announce an
// episode to everyone: the banner waits until the stream has been on air this long.
const EPISODE_BANNER_MIN_ONAIR_MS = 2 * 60 * 1000;
let episodeOfflineSince = null;
let episodeOnAirSince = null;
let episodeBannerPending = false;
let episodeBannerAt = 0;

function trackEpisodeStart(ep) {
  if (!ep) return; // episode poll failed - leave things as they are
  if (!ep.live) {
    if (episodeOfflineSince === null) episodeOfflineSince = Date.now();
    episodeOnAirSince = null;
    episodeBannerPending = false;
    return;
  }
  if (episodeOnAirSince === null) {
    episodeOnAirSince = Date.now();
    episodeBannerPending = episodeOfflineSince !== null && Date.now() - episodeOfflineSince >= EPISODE_BANNER_MIN_OFFLINE_MS;
    episodeOfflineSince = null;
  }
  if (episodeBannerPending && Date.now() - episodeOnAirSince >= EPISODE_BANNER_MIN_ONAIR_MS) {
    episodeBannerPending = false;
    episodeBannerAt = Date.now();
    io.to(roomOf('live')).emit('episode_started', { ms: EPISODE_BANNER_MS });
    console.log('[Episode] Episode is on air - banner sent to live viewers.');
  }
}

// ---------- Retiring the idle episode channel ----------
// The episode's permanent channel re-encodes its slate into the full ladder
// all day (~24 points of CPU) although the episode is on for a couple of
// hours. Once OBS has been gone from episode_in long enough for the 2-hour
// DVR to have fully drained, the channel is retired by renaming its schedule
// file - OME watches that folder and deletes the channel by itself (no OME
// restart). As soon as OBS is back on episode_in the file is renamed back and
// OME recreates the channel, straight on the live feed, within ~1-2s. The file
// is the source of truth; only the "OBS gone since" time is kept in settings
// so a backend restart doesn't restart the 2-hour countdown.
const EPISODE_SCHEDULE_DIR = process.env.EPISODE_SCHEDULE_DIR || '/root/ome-config/origin_conf/schedule/episode';
const EPISODE_SCH_ACTIVE = path.join(EPISODE_SCHEDULE_DIR, 'stream.sch');
const EPISODE_SCH_RETIRED = EPISODE_SCH_ACTIVE + '.retired';
const EPISODE_RETIRE_AFTER_MS = Number(process.env.EPISODE_RETIRE_AFTER_MS) || 125 * 60 * 1000;
const EPISODE_OBS_ABSENT_KEY = 'episode_obs_absent_since';
let episodeChannelLastError = null;

function manageEpisodeChannel(ep) {
  if (!ep) return; // episode poll failed - leave things as they are
  if (DIRECT_INGEST_CHANNELS.has('episode')) return; // no permanent channel to retire
  try {
    if (ep.obs) {
      if (readSetting(EPISODE_OBS_ABSENT_KEY) !== '') writeSetting(EPISODE_OBS_ABSENT_KEY, '');
      if (!fs.existsSync(EPISODE_SCH_ACTIVE) && fs.existsSync(EPISODE_SCH_RETIRED)) {
        fs.renameSync(EPISODE_SCH_RETIRED, EPISODE_SCH_ACTIVE);
        console.log('[Episode channel] revived - OBS is on episode_in');
      }
    } else {
      let since = Number(readSetting(EPISODE_OBS_ABSENT_KEY)) || 0;
      if (!since) {
        since = Date.now();
        writeSetting(EPISODE_OBS_ABSENT_KEY, String(since));
      }
      if (Date.now() - since >= EPISODE_RETIRE_AFTER_MS && fs.existsSync(EPISODE_SCH_ACTIVE)) {
        fs.renameSync(EPISODE_SCH_ACTIVE, EPISODE_SCH_RETIRED);
        console.log(`[Episode channel] retired - no OBS for ${Math.round((Date.now() - since) / 60000)} min`);
      }
    }
    episodeChannelLastError = null;
  } catch (err) {
    // Retried on the next poll; logged once per distinct error, not every 2s.
    const msg = err.message || String(err);
    if (msg !== episodeChannelLastError) console.error('[Episode channel] error:', msg);
    episodeChannelLastError = msg;
  }
}

let streamPollInFlight = false;

async function pollStreamLive() {
  if (streamPollInFlight) return;
  streamPollInFlight = true;
  try {
    if (!process.env.OME_API_ACCESS_TOKEN) return; // not configured - nothing to poll

    const results = {};
    await Promise.all(CHANNELS.map(async (ch) => {
      try {
        results[ch] = await readChannelStream(ch);
      } catch (err) {
        console.error(`[Stream Live Poll Error] ${ch}:`, err.message || err);
      }
    }));

    for (const ch of CHANNELS) {
      if (results[ch]) streamHeights[ch] = results[ch].live ? results[ch].heights : null;
    }
    trackEpisodeStart(results.episode ? { live: results.episode.obs } : null);
    manageEpisodeChannel(results.episode);

    // A new session on EITHER channel needs one purge. Session ids are
    // persisted, so a backend restart doesn't re-purge a stream that was
    // already purged - but does purge one that started while it was down.
    const purgeChannels = [];
    for (const ch of CHANNELS) {
      const r = results[ch];
      if (r && r.live && r.sessionId !== readSetting(sessionSettingKey(ch))) {
        writeSetting(sessionSettingKey(ch), r.sessionId);
        purgeChannels.push(ch);
        console.log(`[Stream] New ${ch} session ${r.sessionId}`);
      }
    }
    if (purgeChannels.length) {
      const ok = await purgeCloudflareCache(purgeChannels);
      console.log(`[Stream] Cloudflare purge (${purgeChannels.join('+')}) ${ok ? 'ok' : 'FAILED'}`);
    }

    // Emitted only after the purge above has finished, so players rebuilding
    // for a new session can't fetch anything the purge was meant to clear.
    // Each channel's state goes only to that channel's viewers.
    for (const ch of CHANNELS) {
      const r = results[ch];
      if (!r) continue;
      const prev = streamStates[ch];
      const changed = prev.live !== r.live || prev.sessionId !== r.sessionId || prev.obs !== r.obs;
      streamStates[ch] = { live: r.live, sessionId: r.sessionId, obs: r.obs };
      if (changed) io.to(roomOf(ch)).emit('stream_state', streamStates[ch]);
    }
  } catch (err) {
    console.error('[Stream Live Poll Error]:', err.message || err);
  } finally {
    streamPollInFlight = false;
  }
}

pollStreamLive();
setInterval(pollStreamLive, STREAM_POLL_INTERVAL_MS);

// ---------- OME transcode webhook ----------
// OME calls this when a stream STARTS, asking which output profiles to build.
// The OME container sits on Docker's bridge network, where "127.0.0.1" is the
// container itself - so this listener binds to the bridge gateway address
// (172.17.0.1, reachable only from this machine and its containers, never
// from the internet), separate from the public app on 127.0.0.1:4000.
//   episode  -> answer "allowed: false" = OME builds its own local profiles
//               from Server.xml (the full ladder: 1080/720/480/360).
//   live     -> 1080p (bypass) + 720p + 360p, always (no 480p).
// Anything going wrong (this listener down, slow, or erroring) makes OME fall
// back to its local full ladder (UseLocalProfilesOn* in Server.xml), so a
// stream can never fail to start because of the webhook.
const WEBHOOK_BIND = process.env.OME_WEBHOOK_BIND || '172.17.0.1';
const WEBHOOK_PORT = Number(process.env.OME_WEBHOOK_PORT || 4001);
const WEBHOOK_SECRET = process.env.OME_WEBHOOK_SECRET || '';
let webhookRequestsLogged = 0;

// Live: the original 1080p plus 720p and 360p. Encoder settings match the
// local profiles in Server.xml exactly - only 480p is left out.
function buildLiveProfiles() {
  const x264 = (name, bitrate, width, height) => ({
    name, codec: 'h264', bitrate, framerate: 30, width, height, preset: 'faster', profile: 'main', modules: 'x264'
  });
  const single = (label, fileName, video) => ({
    name: label, fileName, options: { enableTsPackaging: true },
    renditions: [{ name: fileName, video, audio: 'aac_audio' }]
  });
  return {
    outputProfile: [{
      name: 'bypass_stream',
      outputStreamName: 'stream',
      encodes: {
        videos: [{ name: 'bypass_video', bypass: true }, x264('video_720p', 2500000, 1280, 720), x264('video_360p', 600000, 640, 360)],
        audios: [{ name: 'aac_audio', codec: 'aac', bitrate: 128000, samplerate: 48000, channel: 2, bypassIfMatch: { codec: 'eq' } }]
      },
      playlists: [
        { name: 'default', fileName: 'llhls', options: { hlsChunklistPathDepth: 0, enableTsPackaging: true },
          renditions: [
            { name: '1080p', video: 'bypass_video', audio: 'aac_audio' },
            { name: '720p', video: 'video_720p', audio: 'aac_audio' },
            { name: '360p', video: 'video_360p', audio: 'aac_audio' }
          ] },
        single('1080p only', 'q1080', 'bypass_video'),
        single('720p only', 'q720', 'video_720p'),
        single('360p only', 'q360', 'video_360p')
      ]
    }]
  };
}

const webhookApp = express();
webhookApp.post('/internal/ome/transcode', express.raw({ type: '*/*', limit: '256kb' }), (req, res) => {
  try {
    const raw = req.body instanceof Buffer ? req.body : Buffer.from('');
    if (WEBHOOK_SECRET) {
      const expected = crypto.createHmac('sha1', WEBHOOK_SECRET).update(raw).digest('base64url');
      const got = String(req.headers['x-ome-signature'] || '');
      const a = Buffer.from(expected), b = Buffer.from(got);
      if (a.length !== b.length || !crypto.timingSafeEqual(a, b)) {
        console.error('[Webhook] Rejected a transcode request with a bad signature.');
        return res.status(401).json({ allowed: false, reason: 'bad signature' });
      }
    }
    const body = JSON.parse(raw.toString('utf8') || '{}');
    if (webhookRequestsLogged < 6) {
      webhookRequestsLogged++;
      console.log('[Webhook] request:', raw.toString('utf8').slice(0, 1200));
    }
    const omeApp = body?.stream?.application || body?.application || '';
    writeSetting('webhook_seen', '1');

    if (omeApp === 'app') {
      console.log('[Webhook] live stream starting with 1080p/720p/360p.');
      return res.json({ allowed: true, reason: 'live ladder', outputProfiles: buildLiveProfiles() });
    } else if (omeApp === 'episode') {
      console.log('[Webhook] episode stream starting with the full ladder.');
    }
    // "allowed: false" is how OME is told to build its own local profiles
    // (Server.xml UseLocalProfilesOnServerDisallow) - tested on v0.21.0. An
    // "allowed: true" without profiles is rejected by OME as malformed.
    return res.json({ allowed: false, reason: 'use local profiles' });
  } catch (err) {
    console.error('[Webhook] error:', err.message || err);
    return res.status(500).json({ allowed: false, reason: 'error' });
  }
});
const webhookServer = http.createServer(webhookApp);
webhookServer.on('error', (err) => console.error(`[Webhook] listener error on ${WEBHOOK_BIND}:${WEBHOOK_PORT}:`, err.message));
webhookServer.listen(WEBHOOK_PORT, WEBHOOK_BIND, () => console.log(`[Webhook] transcode webhook listening on ${WEBHOOK_BIND}:${WEBHOOK_PORT}`));

// ---------- Helpers ----------
const RESERVED_USERNAMES = ['admin', 'administrator', 'moderator', 'system', 'root', 'support'];

function signToken(user) {
  const isAdmin = user.role === 'admin' || !!user.is_admin;
  return jwt.sign(
    {
      id: user.id,
      username: user.username,
      email: user.email,
      role: user.role || (isAdmin ? 'admin' : 'user'),
      isAdmin,
      isXUser: !!user.x_id,
      xHandle: user.x_handle || null,
      xVerified: !!user.x_verified,
      xPfpUrl: user.x_pfp_url || null,
      isGoogleUser: !!user.google_native,
      googlePfpUrl: user.google_pfp_url || null
    },
    JWT_SECRET,
    { expiresIn: '30d' }
  );
}

// The login cookie is shared by biggboss24hrs.com and episode.biggboss24hrs.com
// (Domain=.biggboss24hrs.com), so signing in on either covers both. Older
// logins were host-only cookies; a host-only cookie and a domain cookie with
// the same name can coexist and the browser may send the stale one first, so
// whenever the domain cookie is written the host-only one is expired in the
// same response.
function setAuthCookie(res, token, { expires } = {}) {
  const opts = {
    httpOnly: true,       // JS on the page can never read this — protects against XSS token theft
    secure: IS_PROD,
    path: '/',     // only sent over HTTPS in production
    sameSite: 'lax'
  };
  if (expires) opts.expires = expires; else opts.maxAge = 30 * 24 * 60 * 60 * 1000;
  if (IS_PROD) {
    res.clearCookie('streamflix_session', { path: '/', secure: true, httpOnly: true, sameSite: 'lax' });
    opts.domain = COOKIE_DOMAIN;
  }
  res.cookie('streamflix_session', token, opts);
}

function clearAuthCookie(res) {
  res.clearCookie('streamflix_session', { path: '/' });
  if (IS_PROD) res.clearCookie('streamflix_session', { path: '/', domain: COOKIE_DOMAIN });
}

// Where to send someone after sign-in. Only a relative path on this site or
// one of our own two hostnames is ever accepted - anything else (another
// domain, protocol-relative //host, backslash tricks) is dropped, so the
// login and OAuth flows can't be used as an open redirect.
function safeReturnTo(value) {
  if (typeof value !== 'string' || value.length === 0 || value.length > 300) return null;
  if (value.startsWith('/') && !value.startsWith('//') && !value.startsWith('/\\')) return value;
  try {
    const u = new URL(value);
    if (u.protocol === 'https:' && (u.origin === SITE_ORIGIN || u.origin === EPISODE_ORIGIN)) return u.toString();
  } catch {}
  return null;
}

function requireAuth(req, res, next) {
  let token = req.cookies.streamflix_session;
  if (!token && req.headers.authorization && req.headers.authorization.startsWith('Bearer ')) {
    token = req.headers.authorization.split(' ')[1];
  }
  if (!token) return res.status(401).json({ error: 'Not logged in', code: 'SESSION_EXPIRED' });
  try {
    const payload = jwt.verify(token, JWT_SECRET);
    // Same fix as the Socket.IO auth middleware, same reason: a valid JWT
    // signature doesn't mean the account still exists - stateless tokens
    // stay valid until their 30-day expiry regardless of what happens to
    // the row behind them. One indexed primary-key lookup per authenticated
    // request; negligible next to everything else already per-request here.
    if (!db.prepare('SELECT id FROM users WHERE id = ?').get(payload.id)) {
      // The client shows "Account suspended" only for ACCOUNT_BANNED - an
      // account deleted without a ban, like any other dead session, just
      // gets asked to sign in again. Same identities as the socket check.
      const banned = (payload.email && !/@x\.local$/i.test(payload.email) && isBannedIdentity('email', payload.email))
        || (payload.xHandle && isBannedIdentity('x_handle', payload.xHandle));
      return banned
        ? res.status(401).json({ error: 'Account suspended', code: 'ACCOUNT_BANNED' })
        : res.status(401).json({ error: 'Account no longer exists', code: 'SESSION_EXPIRED' });
    }
    req.user = payload;
    next();
  } catch {
    res.status(401).json({ error: 'Invalid or expired session', code: 'SESSION_EXPIRED' });
  }
}

function requireAdmin(req, res, next) {
  const isAdmin = req.user?.role === 'admin' || !!req.user?.isAdmin;
  if (!isAdmin) return res.status(403).json({ error: 'Admin access required' });
  next();
}

// ---------- Socket.IO Middleware & Events ----------
io.use((socket, next) => {
  // Held outside the row-existence check below on purpose: a ban deletes the
  // row, so for the one connection this most needs to identify, socket.user
  // is never set. The JWT is the only surviving record of who they are.
  let tokenPayload = null;
  try {
    const rawCookies = socket.handshake.headers.cookie;
    if (rawCookies) {
      const parsed = parseCookie(rawCookies);
      if (parsed.streamflix_session) {
        const payload = jwt.verify(parsed.streamflix_session, JWT_SECRET);
        tokenPayload = payload;
        // A valid JWT signature alone doesn't mean the account still
        // exists - JWTs are stateless, so a deleted account's session
        // stays cryptographically valid until its 30-day expiry with no
        // way to revoke it early. Found live: the Sept 16 account wipe
        // deleted 368 accounts, and every one of them that was already
        // connected kept showing up in chat/presence under their old
        // identity, unrevoked. Same fix either way something's gone
        // wrong with an account (deleted, or a future ban) - if the row
        // isn't there, this connection reverts to fully anonymous, the
        // same as if no cookie had been sent at all.
        const stillExists = db.prepare('SELECT id FROM users WHERE id = ?').get(payload.id);
        if (stillExists) {
          socket.user = payload;
        }
      }
    }
  } catch (err) {
    // Ignore invalid token, socket.user remains undefined
  }

  // Bans are enforced here too, not just on the HTTP routes. Without this a
  // banned viewer simply reconnects as an anonymous socket and keeps
  // receiving chat and viewer counts. Identity values come off the JWT
  // payload because the row itself is already gone by now; signToken()
  // carries no x_id/google_id, so email + xHandle + ip is the complete
  // reachable set (every account has a real email or an x_handle, and
  // re-login is already blocked at both OAuth callbacks).
  const banned = (() => {
    const p = tokenPayload;
    if (p) {
      if (p.email && !/@x\.local$/i.test(p.email) && isBannedIdentity('email', p.email)) return `email:${p.email}`;
      if (p.xHandle && isBannedIdentity('x_handle', p.xHandle)) return `x_handle:${p.xHandle}`;
    }
    // Admins are exempt from the IP check only - a mistyped ip in a ban
    // body shouldn't be able to lock the operator out of their own site.
    if (p?.isAdmin) return null;
    const ip = realIpFromHandshake(socket.handshake);
    if (ip && isBannedIdentity('ip', ip)) return `ip:${ip}`;
    return null;
  })();

  if (banned) {
    console.log(`[Socket] Rejected banned connection (${banned}).`);
    const err = new Error('banned');
    err.data = { code: 'ACCOUNT_BANNED' };
    return next(err);
  }

  // The pages are behind the rotating link, but this socket was open to anyone:
  // chat could be read live, and made-up viewer ids inflated "Watching".
  // Checked after the ban test so a banned viewer still gets the ban notice.
  let hasAccess = false;
  try {
    const raw = parseCookie(socket.handshake.headers.cookie || '').access_session;
    hasAccess = !!raw && jwt.verify(raw, JWT_SECRET).type === 'access_session';
  } catch {}
  if (!hasAccess) {
    const err = new Error('access link required');
    err.data = { code: 'ACCESS_REQUIRED' };
    return next(err);
  }

  next();
});

// 3. Socket.io Connection & History Logic

// Lightweight live presence: an in-memory Map, updated only on
// connect/disconnect (not polled, not per-message) - this is what makes
// "is user X watching right now" answerable at all, rather than the
// indirect chat/poll-history guessing this previously required. One cheap
// DB write per connect keeps a last_seen timestamp for users who aren't
// currently connected. Deliberately NOT persisted beyond that single
// column - a full connection history log was explicitly out of scope
// ("if not machine heavy").
const presenceMap = new Map(); // userId -> { username, socketIds: Set, connectedAt }

// Logged-out viewers (the rotating link admits them without an account) get
// counted the same way - deduped by a client-generated id shared across that
// browser's tabs via localStorage - so "Watching" reflects distinct people,
// not raw socket connections. Without this, one person with 3 tabs open (or
// a flaky connection reconnecting a few times) visibly inflated the count,
// which is what made it "look fake".
const anonPresenceMap = new Map(); // viewerId -> Set(socketIds)

// "Watching" is counted per channel: distinct people connected to that page.
// A person with both pages open counts once on each. Kept incrementally
// (viewerKey -> that viewer's socket ids), so connect/disconnect stay O(1).
const channelViewers = { live: new Map(), episode: new Map() };

// "Watching" used to exist only in memory, so there was no way to answer how
// many people watched yesterday. One row a minute (two small numbers, ~1,440 a
// day) is enough for real history; rows older than 180 days are dropped.
db.exec(`
  CREATE TABLE IF NOT EXISTS viewer_counts (
    ts INTEGER PRIMARY KEY,
    live_viewers INTEGER NOT NULL,
    episode_viewers INTEGER NOT NULL,
    live_on INTEGER NOT NULL,
    episode_on INTEGER NOT NULL
  )
`);
setInterval(() => {
  try {
    const ts = Math.floor(Date.now() / 60000) * 60000;
    db.prepare('INSERT OR IGNORE INTO viewer_counts (ts, live_viewers, episode_viewers, live_on, episode_on) VALUES (?, ?, ?, ?, ?)')
      .run(ts, channelViewers.live.size, channelViewers.episode.size, streamStates.live.obs === true ? 1 : 0, streamStates.episode.obs === true ? 1 : 0);
    if (new Date(ts).getUTCMinutes() === 0) db.prepare('DELETE FROM viewer_counts WHERE ts < ?').run(ts - 180 * 86400 * 1000);
  } catch (err) {
    console.error('[Viewer history] write failed:', err.message || err);
  }
}, 60 * 1000);

function broadcastViewerCount(channel) {
  io.to(roomOf(channel)).emit('viewer_count', channelViewers[channel].size);
}

// Crude UA sniff, only for the admin presence view ("who's on desktop") -
// never used for anything access-related. Tablets count as mobile since
// that's what they are for a "desktop only" idle-limiter-style question.
function classifyDevice(userAgent) {
  if (!userAgent) return 'unknown';
  return /Mobi|Android|iPhone|iPad|iPod|Tablet/i.test(userAgent) ? 'mobile' : 'desktop';
}

io.on('connection', (socket) => {
  const channel = channelOfSocket(socket);
  socket.join(roomOf(channel));
  const presenceUserId = socket.user?.id || null;
  const anonViewerId = !presenceUserId && typeof socket.handshake.auth?.viewerId === 'string'
    ? socket.handshake.auth.viewerId.slice(0, 64)
    : null;
  const deviceType = classifyDevice(socket.handshake.headers['user-agent']);
  const connIp = realIpFromHandshake(socket.handshake);

  if (presenceUserId) {
    let entry = presenceMap.get(presenceUserId);
    if (!entry) {
      entry = { username: socket.user.username, socketIds: new Set(), connectedAt: Date.now(), devices: new Map(), ips: new Set() };
      presenceMap.set(presenceUserId, entry);
    }
    entry.socketIds.add(socket.id);
    entry.devices.set(socket.id, deviceType);
    entry.ips.add(connIp);
    try {
      db.prepare(`UPDATE users SET last_seen = datetime('now') WHERE id = ?`).run(presenceUserId);
    } catch (err) {
      console.error('[Presence] Failed to update last_seen:', err);
    }
  } else if (anonViewerId) {
    let ids = anonPresenceMap.get(anonViewerId);
    if (!ids) {
      ids = new Set();
      anonPresenceMap.set(anonViewerId, ids);
    }
    ids.add(socket.id);
  }
  const viewerKey = presenceUserId ? `u:${presenceUserId}` : (anonViewerId ? `a:${anonViewerId}` : null);
  if (viewerKey) {
    let sockets = channelViewers[channel].get(viewerKey);
    if (!sockets) { sockets = new Set(); channelViewers[channel].set(viewerKey, sockets); }
    sockets.add(socket.id);
  }
  broadcastViewerCount(channel);

  // A (re)connecting player may have missed restarts while its socket was
  // down (backgrounded tab, network drop) - it compares this sessionId with
  // the one it's playing and rebuilds if they differ.
  if (streamStates[channel].live !== null) socket.emit('stream_state', streamStates[channel]);
  // Opened the live page within a minute of the episode starting: show the
  // banner for whatever is left of that minute.
  if (channel === 'live' && Date.now() - episodeBannerAt < EPISODE_BANNER_MS) {
    socket.emit('episode_started', { ms: EPISODE_BANNER_MS - (Date.now() - episodeBannerAt) });
  }

  socket.on('disconnect', () => {
    if (presenceUserId) {
      const entry = presenceMap.get(presenceUserId);
      if (entry) {
        entry.socketIds.delete(socket.id);
        entry.devices.delete(socket.id);
        if (entry.socketIds.size === 0) presenceMap.delete(presenceUserId);
      }
    } else if (anonViewerId) {
      const ids = anonPresenceMap.get(anonViewerId);
      if (ids) {
        ids.delete(socket.id);
        if (ids.size === 0) anonPresenceMap.delete(anonViewerId);
      }
    }
    if (viewerKey) {
      const sockets = channelViewers[channel].get(viewerKey);
      if (sockets) {
        sockets.delete(socket.id);
        if (sockets.size === 0) channelViewers[channel].delete(viewerKey);
      }
    }
    broadcastViewerCount(channel);
  });

  const senderUsername = socket.user?.username || 'User';
  const isSenderAdmin = !!(socket.user?.role === 'admin' || socket.user?.isAdmin);
  const isSenderX = !!socket.user?.isXUser;
  const senderXHandle = socket.user?.xHandle || null;
  const isSenderXVerified = !!socket.user?.xVerified;
  const senderXPfpUrl = socket.user?.xPfpUrl || null;
  const isSenderGoogle = !!socket.user?.isGoogleUser;
  const senderGooglePfpUrl = socket.user?.googlePfpUrl || null;

  // Send the past 24 hours of messages with admin flags to the newly connected user
  try {
    const history = db.prepare(`
      SELECT cm.id, cm.username, cm.message,
             strftime('%H:%M', cm.created_at, 'localtime') as timestamp,
             CASE WHEN u.role = 'admin' OR u.is_admin = 1 THEN 1 ELSE 0 END as isAdmin,
             CASE WHEN u.x_id IS NOT NULL THEN 1 ELSE 0 END as isXUser,
             u.x_handle as xHandle,
             CASE WHEN u.x_verified = 1 THEN 1 ELSE 0 END as xVerified,
             u.x_pfp_url as xPfpUrl,
             CASE WHEN u.google_native = 1 THEN 1 ELSE 0 END as isGoogleUser,
             u.google_pfp_url as googlePfpUrl
      FROM chat_messages cm
      LEFT JOIN users u ON LOWER(cm.username) = LOWER(u.username)
      WHERE cm.created_at >= datetime('now', '-24 hours') AND cm.channel = ?
      ORDER BY cm.id ASC
    `).all(channel);

    socket.emit('chat_history', history);
  } catch (err) {
    console.error('Failed to retrieve chat history:', err);
  }

  // Handle incoming live message
  // A packet with no body (data undefined) used to throw inside this handler
  // and - as an uncaught exception - stopped the whole Node process, so every
  // input is validated first. Posting needs a real account (the page itself
  // already requires login, so this only closes the raw-socket route), is
  // capped in length, and rate limited per account.
  const CHAT_MAX_LEN = 500;
  const CHAT_RATE_WINDOW_MS = 10 * 1000;
  const CHAT_RATE_MAX = 5;
  const chatSendTimes = [];
  socket.on('send_message', (data) => {
    if (!socket.user) return;
    if (!data || typeof data !== 'object' || typeof data.message !== 'string') return;
    const cleanMsg = data.message.trim().slice(0, CHAT_MAX_LEN);
    if (!cleanMsg) return;
    const nowMs = Date.now();
    while (chatSendTimes.length && nowMs - chatSendTimes[0] > CHAT_RATE_WINDOW_MS) chatSendTimes.shift();
    if (chatSendTimes.length >= CHAT_RATE_MAX) return;
    chatSendTimes.push(nowMs);

    try {
      // Save message into SQLite
      const info = db.prepare(`
        INSERT INTO chat_messages (username, message, channel)
        VALUES (?, ?, ?)
      `).run(senderUsername, cleanMsg, channel);

      const timestamp = new Date().toLocaleTimeString([], { hour: '2-digit', minute: '2-digit' });

      // Broadcast to everyone on this page (not the other channel's page)
      io.to(roomOf(channel)).emit('receive_message', {
        id: info.lastInsertRowid,
        username: senderUsername,
        message: cleanMsg,
        timestamp: timestamp,
        isAdmin: isSenderAdmin,
        isXUser: isSenderX,
        xHandle: senderXHandle,
        xVerified: isSenderXVerified,
        xPfpUrl: senderXPfpUrl,
        isGoogleUser: isSenderGoogle,
        googlePfpUrl: senderGooglePfpUrl
      });
    } catch (err) {
      console.error('Failed to save chat message:', err);
    }
  });

});

// ---------- Auth routes ----------
// Password signup is retired - X and Google are the only ways to create a
// new account now. 410 Gone (not 404) because the route existed and was
// deliberately removed, not never-existed. /api/login stays working below:
// it's the only way the admin account (no X/Google link) can sign in, so
// removing it too would lock the admin out entirely rather than just
// closing new registration.
app.post('/api/signup', (req, res) => {
  res.status(410).json({ error: 'Email/password signup has been retired. Please continue with X or Google.' });
});

// Login API
app.post('/api/login', loginLimiter, async (req, res) => {
  try {
    if (isBannedIdentity('ip', realIp(req))) {
      return res.status(403).json({ error: 'Access denied' });
    }

    const identifier = req.body.email || req.body.username;
    const password = req.body.password;

    if (!identifier || !password) {
      return res.status(400).json({ error: 'Email/Username and password are required' });
    }

    const cleanIdentifier = identifier.trim();
    const user = db.prepare('SELECT *, password_hash AS password FROM users WHERE LOWER(email) = LOWER(?) OR LOWER(username) = LOWER(?)').get(cleanIdentifier, cleanIdentifier);

    if (!user || !user.password) {
      return res.status(401).json({ error: 'Invalid email/username or password' });
    }

    const match = await bcrypt.compare(password, user.password);
    if (!match) {
      return res.status(401).json({ error: 'Invalid email/username or password' });
    }

    const userPayload = { id: user.id, username: user.username, email: user.email, role: user.role || (user.is_admin ? 'admin' : 'user'), isAdmin: !!user.is_admin };
    const token = signToken(userPayload);

    setAuthCookie(res, token);

    return res.json({ success: true, token, redirect: '/live', username: user.username, role: userPayload.role, isAdmin: userPayload.isAdmin });

  } catch (err) {
    console.error('Login Handler Error:', err);
    return res.status(500).json({ error: 'Internal server error' });
  }
});

app.post('/api/logout', (req, res) => {
  clearAuthCookie(res);
  res.clearCookie('sf_dom', { path: '/', domain: IS_PROD ? COOKIE_DOMAIN : undefined });
  res.json({ ok: true });
});

app.get('/api/me', requireAuth, (req, res) => {
  // Viewers who signed in before the episode page existed hold a host-only
  // cookie that the episode subdomain never receives. The first time they
  // open the main site after this change, re-issue the SAME token (same
  // expiry) as a domain cookie so they are already signed in over there. The
  // sf_dom marker makes this happen once per browser, not on every heartbeat.
  if (IS_PROD && !req.cookies.sf_dom && req.cookies.streamflix_session && req.user.exp) {
    setAuthCookie(res, req.cookies.streamflix_session, { expires: new Date(req.user.exp * 1000) });
    res.cookie('sf_dom', '1', {
      secure: true, path: '/', sameSite: 'lax', domain: COOKIE_DOMAIN,
      expires: new Date(req.user.exp * 1000)
    });
  }
  res.json({
    username: req.user.username,
    email: req.user.email,
    role: req.user.role || (req.user.isAdmin ? 'admin' : 'user'),
    isAdmin: !!req.user.isAdmin,
    isXUser: !!req.user.isXUser,
    xHandle: req.user.xHandle || null,
    xVerified: !!req.user.xVerified,
    xPfpUrl: req.user.xPfpUrl || null,
    isGoogleUser: !!req.user.isGoogleUser,
    googlePfpUrl: req.user.googlePfpUrl || null
  });
});

// GET /api/admin/presence - live connection status. With no query params,
// lists everyone currently connected (from the in-memory presenceMap - no
// DB query at all, so this is cheap regardless of how often it's called).
// With ?username=, checks one specific account: live presence first, and
// last_seen from the DB as a fallback for "when were they last here" if
// they're not connected right now.
app.get('/api/admin/presence', requireAuth, requireAdmin, (req, res) => {
  const { username } = req.query;

  if (username) {
    const user = db.prepare('SELECT id, username, last_seen FROM users WHERE LOWER(username) = LOWER(?)').get(username);
    if (!user) return res.status(404).json({ error: 'No such user' });
    const live = presenceMap.get(user.id);
    return res.json({
      username: user.username,
      connected: !!live,
      socketCount: live ? live.socketIds.size : 0,
      devices: live ? [...new Set(live.devices.values())] : [],
      connectedSince: live ? new Date(live.connectedAt).toISOString() : null,
      lastSeen: user.last_seen || null
    });
  }

  const connected = [];
  for (const [userId, entry] of presenceMap.entries()) {
    connected.push({
      userId,
      username: entry.username,
      socketCount: entry.socketIds.size,
      devices: [...new Set(entry.devices.values())],
      connectedSince: new Date(entry.connectedAt).toISOString()
    });
  }
  res.json({ totalConnected: connected.length, connected, byChannel: { live: channelViewers.live.size, episode: channelViewers.episode.size } });
});

// POST /api/admin/kick { username } - force-disconnects every live socket
// for that user right now, no restart needed. Their session stays valid
// (this isn't a ban - jwt.verify still passes and the account still exists
// in the DB), so they can simply reconnect; use the DB-existence check
// path (deleting the account) for a permanent removal instead.
app.post('/api/admin/kick', requireAuth, requireAdmin, (req, res) => {
  const { username } = req.body || {};
  if (!username) return res.status(400).json({ error: 'username required' });

  const user = db.prepare('SELECT id, username FROM users WHERE LOWER(username) = LOWER(?)').get(username);
  if (!user) return res.status(404).json({ error: 'No such user' });

  const entry = presenceMap.get(user.id);
  if (!entry || entry.socketIds.size === 0) {
    return res.json({ username: user.username, kicked: 0, message: 'Not currently connected' });
  }

  let kicked = 0;
  for (const socketId of entry.socketIds) {
    const socket = io.sockets.sockets.get(socketId);
    if (socket) {
      socket.disconnect(true);
      kicked++;
    }
  }
  res.json({ username: user.username, kicked });
});

// POST /api/admin/security-check - fires the anti-leak identity overlay
// (each connected viewer sees their own X handle/email for 5s) on demand,
// broadcast to every live socket at once. Manual/on-demand by design - a
// leaker screen-recording won't know when it's coming.
app.post('/api/admin/security-check', requireAuth, requireAdmin, (req, res) => {
  io.emit('security_check');
  res.json({ sent: true, recipients: presenceMap.size + anonPresenceMap.size });
});

// POST /api/admin/ban { username, reason? } - the actual permanent removal:
// kicks their live sockets, bans every OAuth identity the account had
// (google_id/x_id/x_handle/email - whichever exist), then deletes the row.
// Banning happens BEFORE the delete so the identity values are still on
// hand; the account-existence check already deployed this session means
// their current session dies on its next request even before the kick
// lands.
app.post('/api/admin/ban', requireAuth, requireAdmin, (req, res) => {
  const { username, reason, ip } = req.body || {};
  if (!username) return res.status(400).json({ error: 'username required' });

  const user = db.prepare('SELECT * FROM users WHERE LOWER(username) = LOWER(?)').get(username);
  if (!user) return res.status(404).json({ error: 'No such user' });
  if (user.role === 'admin' || user.is_admin) return res.status(400).json({ error: 'Refusing to ban an admin account' });

  const entry = presenceMap.get(user.id);
  // Captured while they're still connected - this is the only source for
  // it, since IPs are never logged anywhere else (see realIp()'s comment).
  // Once kicked, this is gone for good, so read it before disconnecting.
  const liveIps = entry ? [...entry.ips] : [];
  // Snapshot rather than iterate live: entry.socketIds is mutated by the
  // disconnect handler as each socket goes down.
  const socketIds = entry ? [...entry.socketIds] : [];

  // Tell them before cutting the wire. A bare disconnect is invisible to
  // the client (socket.io just reconnects), which is why a banned viewer's
  // video used to keep playing - the player never learns anything happened.
  for (const socketId of socketIds) {
    io.sockets.sockets.get(socketId)?.emit('account_banned');
  }

  const bannedIdentities = [];
  if (user.google_id) { banIdentity('google_id', user.google_id, reason); bannedIdentities.push('google_id'); }
  if (user.x_id) { banIdentity('x_id', user.x_id, reason); bannedIdentities.push('x_id'); }
  if (user.x_handle) { banIdentity('x_handle', user.x_handle, reason); bannedIdentities.push('x_handle'); }
  if (user.email && !/@x\.local$/i.test(user.email)) { banIdentity('email', user.email, reason); bannedIdentities.push('email'); }

  const bannedIps = new Set(liveIps);
  if (ip) bannedIps.add(String(ip).trim());
  for (const bannedIp of bannedIps) {
    if (!bannedIp) continue;
    banIdentity('ip', bannedIp, reason);
    bannedIdentities.push(`ip:${bannedIp}`);
  }

  db.prepare('DELETE FROM users WHERE id = ?').run(user.id);

  // Deferred so the 'account_banned' packet above clears the transport
  // first. Not load-bearing - if it's missed, the handshake rejection in
  // io.use() catches them on the reconnect attempt instead.
  setTimeout(() => {
    for (const socketId of socketIds) {
      io.sockets.sockets.get(socketId)?.disconnect(true);
    }
  }, 750);

  console.log(`[Admin Ban] "${user.username}" (id ${user.id}) banned and deleted. Identities: ${bannedIdentities.join(', ') || 'none'}. Reason: ${reason || 'unspecified'}`);
  res.json({ username: user.username, kicked: socketIds.length, bannedIdentities, deleted: true });
});

// ---------- Signed stream URLs ----------
// The LLHLS stream had zero access control - proven exploitable (a real
// video segment was fetched from the origin with no login at all, just a
// spoofed Referer header, bypassing the site's cookie-based auth entirely).
// OME's SignedPolicy (Server.xml) now requires every playlist URL to carry
// an HMAC-SHA1 signature made with this same secret. Deliberately only the
// .m3u8 manifest is signed, not each .m4s segment: segments stay cacheable
// and shared at Cloudflare's edge this way (measured ~78% cache hit rate
// before this change), where per-viewer-unique signed segment URLs would
// have collapsed that and roughly 4-5x'd origin egress - verified this
// tradeoff before relying on it, since OME's own docs don't state whether
// segments need signing.
const OME_STREAM_APP_PATH = '/app/stream';
// Each channel's stream lives under its own OME application / URL prefix.
const CHANNEL_STREAM_PATH = { live: '/app/stream', episode: '/episode/stream' };

// CRITICAL, verified empirically (not from docs - OME's own docs don't say
// this): the string OME signs against is NOT the public-facing URL. OME
// sits behind nginx/Cloudflare and has no idea it's proxied, so when it
// reconstructs the URL to verify a signature it uses ITS OWN internal
// listening port (3333, confirmed via
// "There is no signature key... in url(http://biggboss24hrs.com:3333/...)"
// in its own logs) and plain http, not the public https:443 a docs example
// assumes. nginx forwards the Host header unchanged (proxy_set_header Host
// $host), so OME sees Host: biggboss24hrs.com + its own port. Signing with
// :443/https here (the docs' literal example) produces a signature that
// silently never validates - confirmed by testing both forms directly
// against the running container before trusting either.
const OME_INTERNAL_SIGNING_ORIGIN = 'http://biggboss24hrs.com:3333';

function signOmeUrl(path, ttlMs, publicHost = 'https://biggboss24hrs.com') {
  const policy = Buffer.from(JSON.stringify({ url_expire: Date.now() + ttlMs })).toString('base64url');
  const signedString = `${OME_INTERNAL_SIGNING_ORIGIN}${path}?policy=${policy}`;
  const signature = crypto.createHmac('sha1', process.env.OME_SIGNED_POLICY_KEY)
    .update(signedString).digest('base64url');
  // The query string (policy + signature) is what actually matters and
  // travels through nginx/Cloudflare unchanged - the URL handed to the
  // browser uses the real public host so it actually reaches the site.
  return `${publicHost}${path}?policy=${policy}&signature=${signature}`;
}

const STREAM_QUALITY_FILES = {
  auto:  { label: 'Auto',  file: 'llhls.m3u8' },
  q1080: { label: '1080p', file: 'q1080.m3u8' },
  q720:  { label: '720p',  file: 'q720.m3u8' },
  q480:  { label: '480p',  file: 'q480.m3u8' },
  q360:  { label: '360p',  file: 'q360.m3u8' }
};

// 12h so a long broadcast is never interrupted mid-session - url_expire
// only gates when a NEW request can start, not sessions already playing.
const STREAM_URL_TTL_MS = 12 * 60 * 60 * 1000;

// requireAuth closes the original hotlinking hole (no account, no URL).
// gateStream is layered on top so the current rotating link is required
// here too - otherwise a logged-in-but-linkless user could still get a
// working signed URL straight from this API, bypassing the point of gating
// '/' and '/live' on the link in the first place. gateStream (not
// requireAccessSession) because this is a JSON endpoint - requireAccessSession
// sends the no-access HTML page with a 200, which loadStreamUrls()'s
// `!res.ok` check wouldn't catch, only a confusing res.json() parse failure.
// Public, read-only: whether each stream is on air right now. Drives the live
// dot on the home page's Episode button; exposes nothing about viewers or URLs.
app.get('/api/stream/status', (req, res) => {
  res.set('Cache-Control', 'no-store');
  res.json({ live: streamStates.live.obs === true, episode: streamStates.episode.obs === true });
});

// The episode channel is under the same rotating access link as /live (Phase
// 2). The flag stays so it can be relaxed again without a code change.
const EPISODE_REQUIRES_ACCESS_LINK = true;
function gateStreamForChannel(req, res, next) {
  if (channelOf(req) === 'episode' && !EPISODE_REQUIRES_ACCESS_LINK) return next();
  return gateStream(req, res, next);
}

app.get('/api/stream/urls', requireAuth, gateStreamForChannel, (req, res) => {
  if (!process.env.OME_SIGNED_POLICY_KEY) {
    console.error('[Stream URLs] OME_SIGNED_POLICY_KEY not configured');
    return res.status(503).json({ error: 'Stream signing is not configured' });
  }
  const channel = channelOf(req);
  // The URL is built on the hostname the viewer is actually on, so the player
  // stays same-origin. The signature is unaffected: OME verifies it against
  // its own internal origin (OME_INTERNAL_SIGNING_ORIGIN), not this host.
  const publicHost = channel === 'episode' ? EPISODE_ORIGIN : 'https://biggboss24hrs.com';
  const qualities = {};
  const available = new Set(availableQualityKeys(channel));
  for (const [key, { label, file }] of Object.entries(STREAM_QUALITY_FILES)) {
    if (!available.has(key)) continue;
    qualities[key] = { label, url: signOmeUrl(`${CHANNEL_STREAM_PATH[channel]}/${file}`, STREAM_URL_TTL_MS, publicHost) };
  }
  res.json({ qualities });
});

// ---------- Sign in with X ----------
// Additive to email/password signup, never a replacement. A proven X
// identity locks the username to the real handle and drives a distinct chat
// look - this exists because most of the audience comes from X and people
// were squatting well-known handles in chat to impersonate them. Costs one
// billed X API read ($0.010) per COMPLETED OAUTH FLOW - new signup or
// returning login alike, since X's callback never tells us who's
// authorizing until we call users/me (see the comment at that call below).
const X_AUTHORIZE_URL = 'https://x.com/i/oauth2/authorize';
const X_TOKEN_URL = 'https://api.x.com/2/oauth2/token';
const X_ME_URL = 'https://api.x.com/2/users/me';

function base64url(buf) {
  return buf.toString('base64').replace(/\+/g, '-').replace(/\//g, '_').replace(/=+$/, '');
}

// X serves profile_image_url at 48x48 (the "_normal" size) - the chat
// avatar renders at 28px desktop / 24px mobile, so on a 2x display "_normal"
// is visibly soft. "_bigger" is 73x73 and still only a few KB. The host
// check matters beyond validation: this string lands in an <img src> on
// every viewer's page, so only a pbs.twimg.com URL is ever accepted.
function normalizeXPfp(url) {
  if (typeof url !== 'string' || !url.startsWith('https://pbs.twimg.com/')) return null;
  return url.replace('_normal.', '_bigger.');
}


// OAuth state (state + PKCE verifier + return page) is kept here as well as in
// the cookie. On iPhones the sign-in often finishes in a different browser
// context than it started in (X's app, in-app browsers), so the cookie never
// arrives and 56% of iPhone X sign-ins failed with "missing cookie". The
// callback's own `state` query value is the key, so it works wherever the
// browser lands. Single-use, 10 minutes.
db.exec(`
  CREATE TABLE IF NOT EXISTS oauth_states (
    state TEXT PRIMARY KEY,
    payload TEXT NOT NULL,
    expires_at INTEGER NOT NULL
  )
`);
function saveOAuthState(state, payload) {
  db.prepare('INSERT OR REPLACE INTO oauth_states (state, payload, expires_at) VALUES (?, ?, ?)')
    .run(state, JSON.stringify(payload), Date.now() + 10 * 60 * 1000);
}
function takeOAuthState(state, type) {
  if (typeof state !== 'string' || state.length === 0 || state.length > 100) return null;
  const row = db.prepare('SELECT payload, expires_at FROM oauth_states WHERE state = ?').get(state);
  if (!row) return null;
  db.prepare('DELETE FROM oauth_states WHERE state = ?').run(state);
  if (row.expires_at < Date.now()) return null;
  try {
    const p = JSON.parse(row.payload);
    return p.type === type && p.state === state ? p : null;
  } catch { return null; }
}
setInterval(() => {
  try { db.prepare('DELETE FROM oauth_states WHERE expires_at < ?').run(Date.now()); } catch {}
}, 10 * 60 * 1000);

app.get('/api/auth/x/start', (req, res) => {
  if (!process.env.X_CLIENT_ID || !process.env.X_REDIRECT_URI) {
    console.error('[X Signup] X_CLIENT_ID/X_REDIRECT_URI not configured');
    return res.status(503).send('X sign-in is not configured');
  }

  const state = base64url(crypto.randomBytes(24));
  const codeVerifier = base64url(crypto.randomBytes(32));
  const codeChallenge = base64url(crypto.createHash('sha256').update(codeVerifier).digest());

  // Ephemeral OAuth state, kept the same way access_session is - a signed,
  // short-expiry JWT in a cookie - rather than a new DB table + sweeper.
  const returnTo = safeReturnTo(req.query.return);
  saveOAuthState(state, { type: 'x_oauth', state, codeVerifier, returnTo });
  const oauthJwt = jwt.sign({ type: 'x_oauth', state, codeVerifier, returnTo }, JWT_SECRET, { expiresIn: '10m' });
  res.cookie('x_oauth', oauthJwt, {
    httpOnly: true,
    secure: IS_PROD,
    path: '/',
    sameSite: 'lax',
    maxAge: 10 * 60 * 1000
  });

  const params = new URLSearchParams({
    response_type: 'code',
    client_id: process.env.X_CLIENT_ID,
    redirect_uri: process.env.X_REDIRECT_URI,
    scope: 'tweet.read users.read',
    state,
    code_challenge: codeChallenge,
    code_challenge_method: 'S256'
  });
  res.redirect(`${X_AUTHORIZE_URL}?${params.toString()}`);
});

app.get('/api/auth/x/callback', async (req, res) => {
  const failRedirect = (reason) => {
    console.error('[X Signup] Callback failed:', reason);
    res.clearCookie('x_oauth');
    return res.redirect('/login.html?x_error=1');
  };

  try {
    if (isBannedIdentity('ip', realIp(req))) {
      res.clearCookie('x_oauth');
      return res.redirect('/login.html?x_error=banned');
    }

    const { code, state } = req.query;
    const oauthCookie = req.cookies.x_oauth;
    if (!code || !state) return failRedirect('missing code/state');

    // Server-side record first (works when the browser came back without its
    // cookie); the cookie still covers sign-ins started before this existed.
    let oauthPayload = takeOAuthState(String(state), 'x_oauth');
    if (!oauthPayload) {
      if (!oauthCookie) return failRedirect('unknown or expired state, no cookie');
      try {
        oauthPayload = jwt.verify(oauthCookie, JWT_SECRET);
      } catch {
        return failRedirect('invalid or expired x_oauth cookie');
      }
      if (oauthPayload.type !== 'x_oauth' || oauthPayload.state !== state) {
        return failRedirect('state mismatch');
      }
    }
    res.clearCookie('x_oauth');

    // ---- Token exchange - confidential client, HTTP Basic id:secret ----
    const basicAuth = Buffer.from(`${process.env.X_CLIENT_ID}:${process.env.X_CLIENT_SECRET}`).toString('base64');
    const tokenRes = await fetch(X_TOKEN_URL, {
      method: 'POST',
      headers: {
        'Content-Type': 'application/x-www-form-urlencoded',
        'Authorization': `Basic ${basicAuth}`
      },
      body: new URLSearchParams({
        code: String(code),
        grant_type: 'authorization_code',
        redirect_uri: process.env.X_REDIRECT_URI,
        code_verifier: oauthPayload.codeVerifier
      }),
      signal: AbortSignal.timeout(5000)
    });
    if (!tokenRes.ok) return failRedirect(`token exchange ${tokenRes.status}`);
    const tokenJson = await tokenRes.json();
    const xAccessToken = tokenJson.access_token;
    if (!xAccessToken) return failRedirect('no access_token in token response');

    // ---- The billed call ($0.010). Runs on EVERY completed OAuth flow, new
    // signup or returning login alike - X's callback only returns a `code`,
    // never the user's identity, so there's no way to know "is this a
    // returning user" without calling users/me first. The cost is bounded
    // by how often someone re-runs this flow, not by page views: a
    // completed login gets the normal 30-day streamflix_session cookie, so
    // the same browser won't hit this route again until that expires or
    // they explicitly log out. ----
    const meRes = await fetch(
      `${X_ME_URL}?user.fields=name,username,verified,verified_type,profile_image_url`,
      { headers: { Authorization: `Bearer ${xAccessToken}` }, signal: AbortSignal.timeout(5000) }
    );
    if (!meRes.ok) return failRedirect(`users/me ${meRes.status}`);
    const meJson = await meRes.json();
    const xUser = meJson.data;
    if (!xUser || !xUser.id || !xUser.username) return failRedirect('malformed users/me response');
    // xAccessToken is discarded here - nothing else in this route touches X again.

    const xId = String(xUser.id);
    const xHandle = xUser.username;
    const xName = xUser.name || xHandle;
    const xVerified = xUser.verified === true ? 1 : 0;
    const xPfpUrl = normalizeXPfp(xUser.profile_image_url);

    if (isBannedIdentity('x_id', xId) || isBannedIdentity('x_handle', xHandle)) {
      res.clearCookie('x_oauth');
      return res.redirect('/login.html?x_error=banned');
    }

    const resolveAccount = db.transaction(() => {
      // 1. Returning X user - refresh everything X gave us on every login
      // (handle, name, verified, picture). This is free: users/me already
      // returned all of it for the billed call above, so there's no reason
      // to leave a lapsed Premium badge or a stale picture stuck on the
      // account. Never counts against account creation (no cap exists).
      const existing = db.prepare('SELECT * FROM users WHERE x_id = ?').get(xId);
      if (existing) {
        db.prepare('UPDATE users SET x_handle = ?, x_name = ?, x_verified = ?, x_pfp_url = ? WHERE id = ?')
          .run(xHandle, xName, xVerified, xPfpUrl, existing.id);
        const refreshed = db.prepare('SELECT * FROM users WHERE id = ?').get(existing.id);
        return { user: refreshed, outcome: 'login' };
      }

      // 2. Name clash. Admins and any account already linked to an OAuth
      // provider (X or Google) are never displaced. Anyone else loses the
      // handle to its proven owner - this is the actual anti-impersonation
      // mechanism the feature exists for. Google accounts don't have a
      // public handle, so they never trigger this eviction themselves -
      // this check only protects them from being evicted BY an X sign-in
      // whose handle happens to coincide with a Google-derived username.
      const clash = db.prepare('SELECT * FROM users WHERE LOWER(username) = LOWER(?)').get(xHandle);
      if (clash) {
        const clashIsAdmin = clash.role === 'admin' || !!clash.is_admin;
        if (clashIsAdmin) return { outcome: 'admin_clash' };
        if (clash.x_id || clash.google_id) return { outcome: 'x_clash' };

        // chat_history re-derives isAdmin/isXUser via a live join on
        // username (see the socket connection handler above) - leaving the
        // squatter's old messages in place would make them immediately
        // render WITH the new X user's badge the moment the handle
        // transfers. Deleting them is what makes the displacement correct,
        // not optional cleanup.
        db.prepare('DELETE FROM chat_messages WHERE LOWER(username) = LOWER(?)').run(clash.username);
        db.prepare('DELETE FROM poll_votes WHERE user_id = ?').run(clash.id);
        db.prepare('DELETE FROM users WHERE id = ?').run(clash.id);
        console.log(`[X Signup] Displaced local user "${clash.username}" (id ${clash.id}) for verified X handle @${xHandle}`);
      }

      // 3. Create the account. password_hash/email get unusable
      // placeholders - the columns are NOT NULL/UNIQUE, but nobody knows
      // the random password and '.local' can never be a real deliverable
      // address, so /api/login can never authenticate this row.
      const placeholderHash = bcrypt.hashSync(crypto.randomBytes(32).toString('hex'), 12);
      const placeholderEmail = `x_${xId}@x.local`;
      const info = db.prepare(`
        INSERT INTO users (username, email, password_hash, role, is_admin, x_id, x_handle, x_name, x_verified, x_pfp_url, x_linked_at)
        VALUES (?, ?, ?, 'user', 0, ?, ?, ?, ?, ?, datetime('now'))
      `).run(xHandle, placeholderEmail, placeholderHash, xId, xHandle, xName, xVerified, xPfpUrl);

      const created = db.prepare('SELECT * FROM users WHERE id = ?').get(info.lastInsertRowid);
      return { user: created, outcome: 'signup' };
    });

    const result = resolveAccount();

    if (result.outcome === 'admin_clash' || result.outcome === 'x_clash') {
      return res.redirect('/login.html?x_error=taken');
    }

    const token = signToken(result.user);
    setAuthCookie(res, token);

    console.log(`[X Signup] ${result.outcome === 'signup' ? 'New' : 'Returning'} X user @${xHandle} (verified=${!!xVerified}) logged in.`);
    return res.redirect(safeReturnTo(oauthPayload.returnTo) || '/live');
  } catch (err) {
    return failRedirect(err.message || err);
  }
});

// ---------- Sign in with Google ----------
// Structurally mirrors Sign in with X above, but Google gives a real
// verified email (X never does) and no public handle. That changes the
// account-resolution shape: a matching email links onto an existing
// account instead of creating a duplicate, and a username collision on a
// brand-new account is resolved by suffixing, never by evicting anyone -
// there's no public handle here for a real person to have proven ownership
// of, so X's eviction argument doesn't transfer. No cost either: unlike
// X's $0.010/flow, Google's OAuth and userinfo calls are free.
const GOOGLE_AUTHORIZE_URL = 'https://accounts.google.com/o/oauth2/v2/auth';
const GOOGLE_TOKEN_URL = 'https://oauth2.googleapis.com/token';
const GOOGLE_USERINFO_URL = 'https://openidconnect.googleapis.com/v1/userinfo';

// Google's photo URLs live on *.googleusercontent.com and take an optional
// "=sNN-c" size/crop suffix. Strip any existing suffix, then request a 96px
// square crop - a bit larger than the 28px render size, for retina. Same
// host-allowlisting rationale as normalizeXPfp: this string lands in an
// <img src> on every viewer's page.
function normalizeGooglePfp(url) {
  if (typeof url !== 'string' || !/^https:\/\/([a-z0-9-]+\.)?googleusercontent\.com\//.test(url)) return null;
  return url.replace(/=s\d+-c$/, '') + '=s96-c';
}

// Google gives no handle to lock a username to, so one is derived from the
// email's local part. Collisions are resolved by the caller appending an
// incrementing suffix - see the "new account" branch below.
const USERNAME_RE = /^[A-Za-z0-9_]{3,20}$/;
function deriveGoogleUsername(email) {
  const base = email.split('@')[0].replace(/[^a-zA-Z0-9_]/g, '').slice(0, 20);
  return base.length >= 3 ? base : (base + 'user').slice(0, 20);
}
// Lookalikes of reserved names ("Admin_", "4dmin") are refused too: compared
// ignoring case, underscores and common digit swaps. Exact match only, so real
// names that merely contain "root" or "admin" (groot, badminton) stay allowed;
// "streamflix" is blocked anywhere since it is the site's own name.
function isReservedLookalike(name) {
  const n = name.toLowerCase().replace(/_/g, '').replace(/0/g, 'o').replace(/[1!]/g, 'i').replace(/3/g, 'e').replace(/4/g, 'a').replace(/5/g, 's');
  return RESERVED_USERNAMES.includes(n) || n.includes('streamflix');
}

// Restricted after a cluster of throwaway-domain (.shop/.store) Google
// accounts correlated with a stream leaker - only gmail.com and the
// company's own domain may sign in with Google. Checked on every
// callback (not just new signups) so it also cuts off a would-be
// email-match link onto an existing password/X account.
const ALLOWED_GOOGLE_DOMAINS = ['gmail.com', 'afenixtechnologies.com'];
function isAllowedGoogleDomain(email) {
  const domain = String(email).split('@')[1]?.toLowerCase();
  return ALLOWED_GOOGLE_DOMAINS.includes(domain);
}

app.get('/api/auth/google/start', (req, res) => {
  if (!process.env.GOOGLE_CLIENT_ID || !process.env.GOOGLE_REDIRECT_URI) {
    console.error('[Google Signup] GOOGLE_CLIENT_ID/GOOGLE_REDIRECT_URI not configured');
    return res.status(503).send('Google sign-in is not configured');
  }

  const state = base64url(crypto.randomBytes(24));
  const codeVerifier = base64url(crypto.randomBytes(32));
  const codeChallenge = base64url(crypto.createHash('sha256').update(codeVerifier).digest());

  // Same ephemeral-cookie pattern as x_oauth above - a signed, short-expiry
  // JWT rather than a new DB table + sweeper.
  const returnTo = safeReturnTo(req.query.return);
  saveOAuthState(state, { type: 'google_oauth', state, codeVerifier, returnTo });
  const oauthJwt = jwt.sign({ type: 'google_oauth', state, codeVerifier, returnTo }, JWT_SECRET, { expiresIn: '10m' });
  res.cookie('google_oauth', oauthJwt, {
    httpOnly: true,
    secure: IS_PROD,
    path: '/',
    sameSite: 'lax',
    maxAge: 10 * 60 * 1000
  });

  const params = new URLSearchParams({
    response_type: 'code',
    client_id: process.env.GOOGLE_CLIENT_ID,
    redirect_uri: process.env.GOOGLE_REDIRECT_URI,
    scope: 'openid email profile',
    state,
    code_challenge: codeChallenge,
    code_challenge_method: 'S256'
  });
  res.redirect(`${GOOGLE_AUTHORIZE_URL}?${params.toString()}`);
});

app.get('/api/auth/google/callback', async (req, res) => {
  const failRedirect = (reason) => {
    console.error('[Google Signup] Callback failed:', reason);
    res.clearCookie('google_oauth');
    return res.redirect('/login.html?g_error=1');
  };

  try {
    if (isBannedIdentity('ip', realIp(req))) {
      res.clearCookie('google_oauth');
      return res.redirect('/login.html?g_error=banned');
    }

    const { code, state } = req.query;
    const oauthCookie = req.cookies.google_oauth;
    if (!code || !state) return failRedirect('missing code/state');

    // Server-side record first (works when the browser came back without its
    // cookie); the cookie still covers sign-ins started before this existed.
    let oauthPayload = takeOAuthState(String(state), 'google_oauth');
    if (!oauthPayload) {
      if (!oauthCookie) return failRedirect('unknown or expired state, no cookie');
      try {
        oauthPayload = jwt.verify(oauthCookie, JWT_SECRET);
      } catch {
        return failRedirect('invalid or expired google_oauth cookie');
      }
      if (oauthPayload.type !== 'google_oauth' || oauthPayload.state !== state) {
        return failRedirect('state mismatch');
      }
    }
    res.clearCookie('google_oauth');

    // ---- Token exchange - client_secret goes in the POST body for Google
    // (X instead uses an Authorization: Basic header - the one concrete
    // mechanical difference between the two token exchanges). ----
    const tokenRes = await fetch(GOOGLE_TOKEN_URL, {
      method: 'POST',
      headers: { 'Content-Type': 'application/x-www-form-urlencoded' },
      body: new URLSearchParams({
        code: String(code),
        client_id: process.env.GOOGLE_CLIENT_ID,
        client_secret: process.env.GOOGLE_CLIENT_SECRET,
        redirect_uri: process.env.GOOGLE_REDIRECT_URI,
        grant_type: 'authorization_code',
        code_verifier: oauthPayload.codeVerifier
      }),
      signal: AbortSignal.timeout(5000)
    });
    if (!tokenRes.ok) return failRedirect(`token exchange ${tokenRes.status}`);
    const tokenJson = await tokenRes.json();
    const googleAccessToken = tokenJson.access_token;
    if (!googleAccessToken) return failRedirect('no access_token in token response');

    // Same shape as X: use the access token to call a profile endpoint
    // directly rather than parsing an ID token JWT, so the two provider
    // flows stay structurally identical. Free - no per-call cost like X.
    const meRes = await fetch(GOOGLE_USERINFO_URL, {
      headers: { Authorization: `Bearer ${googleAccessToken}` },
      signal: AbortSignal.timeout(5000)
    });
    if (!meRes.ok) return failRedirect(`userinfo ${meRes.status}`);
    const googleUser = await meRes.json();
    if (!googleUser || !googleUser.sub || !googleUser.email) return failRedirect('malformed userinfo response');
    // googleAccessToken is discarded here - nothing else in this route touches Google again.

    const googleId = String(googleUser.sub);
    const googleEmail = googleUser.email;
    const googleName = googleUser.name || googleEmail;
    const googlePfpUrl = normalizeGooglePfp(googleUser.picture);

    if (!isAllowedGoogleDomain(googleEmail)) {
      res.clearCookie('google_oauth');
      return res.redirect('/login.html?g_error=domain');
    }

    if (isBannedIdentity('google_id', googleId) || isBannedIdentity('email', googleEmail)) {
      res.clearCookie('google_oauth');
      return res.redirect('/login.html?g_error=banned');
    }

    const resolveAccount = db.transaction(() => {
      // 1. Returning Google user - refresh name unconditionally, but only
      // refresh the picture if one was already stored. A null
      // google_pfp_url means either "linked account" or "chose skip at
      // signup" - both must stay null forever, never silently
      // repopulated the next time this person logs in.
      const existing = db.prepare('SELECT * FROM users WHERE google_id = ?').get(googleId);
      if (existing) {
        db.prepare(`
          UPDATE users SET google_name = ?,
            google_pfp_url = CASE WHEN google_pfp_url IS NOT NULL THEN ? ELSE NULL END
          WHERE id = ?
        `).run(googleName, googlePfpUrl, existing.id);
        return { user: db.prepare('SELECT * FROM users WHERE id = ?').get(existing.id), outcome: 'login' };
      }

      // 2. Real verified email matches an existing account - link Google
      // onto it rather than creating a duplicate. Grants a login method
      // ONLY: no name, no picture, google_native stays at its default 0,
      // so this account keeps rendering exactly as it did before - the fix
      // for the bug where linking silently adopted the admin's Google
      // photo and would-be badge. Never touches password_hash, username,
      // or chat history either.
      const byEmail = db.prepare('SELECT * FROM users WHERE LOWER(email) = LOWER(?)').get(googleEmail);
      if (byEmail) {
        db.prepare(`UPDATE users SET google_id = ?, google_linked_at = datetime('now') WHERE id = ?`)
          .run(googleId, byEmail.id);
        return { user: db.prepare('SELECT * FROM users WHERE id = ?').get(byEmail.id), outcome: 'linked' };
      }

      return { outcome: 'new' };
    });

    const result = resolveAccount();

    if (result.outcome === 'new') {
      // Don't create the account yet - let the user pick their own
      // username and whether to show their Google photo first (see
      // GET /api/auth/google/pending and POST /api/auth/google/complete).
      // Same ephemeral-signed-cookie pattern as google_oauth above.
      const suggested = deriveGoogleUsername(googleEmail);
      const suggestedUsername = RESERVED_USERNAMES.includes(suggested.toLowerCase()) ? suggested + '_g' : suggested;
      const pendingJwt = jwt.sign(
        { type: 'google_pending', googleId, googleEmail, googleName, googlePfpUrl, suggestedUsername, returnTo: safeReturnTo(oauthPayload.returnTo) },
        JWT_SECRET,
        { expiresIn: '15m' }
      );
      res.cookie('google_pending', pendingJwt, {
        httpOnly: true,
        secure: IS_PROD,
        path: '/',
        sameSite: 'lax',
        maxAge: 15 * 60 * 1000
      });
      return res.redirect('/complete-signup.html');
    }

    const token = signToken(result.user);
    setAuthCookie(res, token);

    console.log(`[Google Signup] ${result.outcome} for ${googleEmail} (user id ${result.user.id}).`);
    return res.redirect(safeReturnTo(oauthPayload.returnTo) || '/live');
  } catch (err) {
    return failRedirect(err.message || err);
  }
});

// GET: the completion page's data source - suggested username, name, and
// picture preview, read from the (non-secret) pending cookie without
// exposing its raw signed contents to client JS.
app.get('/api/auth/google/pending', (req, res) => {
  const cookie = req.cookies.google_pending;
  if (!cookie) return res.status(400).json({ error: 'No pending Google sign-in.' });
  try {
    const p = jwt.verify(cookie, JWT_SECRET);
    if (p.type !== 'google_pending') throw new Error('wrong type');
    res.json({ suggestedUsername: p.suggestedUsername, pfpUrl: p.googlePfpUrl, name: p.googleName });
  } catch {
    res.status(400).json({ error: 'Your sign-in session expired. Please try again.' });
  }
});

// POST: finalizes a new Google account with the username and avatar choice
// the user actually made, replacing the old auto-suffix/auto-photo path.
app.post('/api/auth/google/complete', (req, res) => {
  const cookie = req.cookies.google_pending;
  if (!cookie) return res.status(400).json({ error: 'No pending Google sign-in. Please sign in again.' });

  let payload;
  try {
    payload = jwt.verify(cookie, JWT_SECRET);
    if (payload.type !== 'google_pending') throw new Error('wrong type');
  } catch {
    return res.status(400).json({ error: 'Your sign-in session expired. Please sign in again.' });
  }

  try {
    const cleanUsername = String((req.body || {}).username || '').trim();
    const useAvatar = !!(req.body || {}).useAvatar;
    if (!cleanUsername) return res.status(400).json({ error: 'Username is required.' });
    if (!USERNAME_RE.test(cleanUsername)) {
      return res.status(400).json({ error: 'Username must be 3-20 characters: letters, numbers or underscore.' });
    }
    if (isReservedLookalike(cleanUsername)) {
      return res.status(403).json({ error: 'This username is reserved.' });
    }
    if (db.prepare('SELECT id FROM users WHERE LOWER(username) = LOWER(?)').get(cleanUsername)) {
      return res.status(409).json({ error: 'That username is already taken.' });
    }
    // Re-check for a race between /start and /complete - another signup or
    // link could have claimed this identity in the 15-minute window.
    if (
      db.prepare('SELECT id FROM users WHERE google_id = ?').get(payload.googleId) ||
      db.prepare('SELECT id FROM users WHERE LOWER(email) = LOWER(?)').get(payload.googleEmail)
    ) {
      return res.status(409).json({ error: 'This Google account is already linked. Please sign in again.' });
    }

    const finalPfpUrl = useAvatar ? payload.googlePfpUrl : null;
    const placeholderHash = bcrypt.hashSync(crypto.randomBytes(32).toString('hex'), 12);
    const info = db.prepare(`
      INSERT INTO users (username, email, password_hash, role, is_admin, google_id, google_name, google_pfp_url, google_native, google_linked_at)
      VALUES (?, ?, ?, 'user', 0, ?, ?, ?, 1, datetime('now'))
    `).run(cleanUsername, payload.googleEmail, placeholderHash, payload.googleId, payload.googleName, finalPfpUrl);

    const user = db.prepare('SELECT * FROM users WHERE id = ?').get(info.lastInsertRowid);
    const token = signToken(user);
    setAuthCookie(res, token);
    res.clearCookie('google_pending');
    console.log(`[Google Signup] New account "${cleanUsername}" completed for ${payload.googleEmail} (avatar=${useAvatar}).`);
    res.json({ success: true, redirect: safeReturnTo(payload.returnTo) || '/live' });
  } catch (err) {
    console.error('[Google Signup] Complete failed:', err);
    res.status(500).json({ error: 'Something went wrong finishing sign-in. Please try again.' });
  }
});

// ---------- Stream title ----------
// POST: Save updated stream title
app.post('/api/stream-title', requireAuth, requireAdmin, (req, res) => {
  const { title } = req.body;
  if (!title || !title.trim()) {
    return res.status(400).json({ error: 'Title cannot be empty' });
  }

  try {
    const cleanTitle = title.trim();
    const channel = channelOf(req);
    writeSetting(titleKey(channel), cleanTitle);

    // Broadcast new title in real-time to everyone on this page
    io.to(roomOf(channel)).emit('stream_title_updated', { title: cleanTitle });

    return res.json({ success: true, title: cleanTitle });
  } catch (err) {
    console.error('Failed to save stream title:', err);
    return res.status(500).json({ error: 'Database update failed' });
  }
});

// GET: Fetch current title on page load
app.get('/api/stream-title', (req, res) => {
  try {
    return res.json({ title: getTitle(channelOf(req)) });
  } catch (err) {
    return res.json({ title: TITLE_DEFAULTS[channelOf(req)] });
  }
});

// ---------- Library Folders & Videos API ----------

// GET /api/library/folders (Public)
app.get('/api/library/folders', (req, res) => {
  try {
    const folders = db.prepare(`
      SELECT f.id, f.title, f.description, f.thumbnail_url, f.created_at, f.storage, f.naming,
             COUNT(v.id) AS video_count
      FROM library_folders f
      LEFT JOIN library_videos v ON v.folder_id = f.id
      GROUP BY f.id
      ORDER BY f.id DESC
    `).all();
    res.json({ folders });
  } catch (err) {
    console.error('Fetch library folders error:', err);
    res.status(500).json({ error: 'Failed to fetch folders' });
  }
});

// POST /api/library/folders (Admin only)
app.post('/api/library/folders', requireAuth, requireAdmin, (req, res) => {
  try {
    const { title, description, thumbnail_url } = req.body || {};
    if (!title || !title.trim()) {
      return res.status(400).json({ error: 'Folder title is required' });
    }
    const cleanTitle = title.trim();
    const cleanDesc = (description || '').trim();
    const cleanThumb = (thumbnail_url || '').trim();

    const info = db.prepare(`
      INSERT INTO library_folders (title, description, thumbnail_url) VALUES (?, ?, ?)
    `).run(cleanTitle, cleanDesc, cleanThumb);

    res.json({
      success: true,
      folder: { id: info.lastInsertRowid, title: cleanTitle, description: cleanDesc, thumbnail_url: cleanThumb, video_count: 0 }
    });
  } catch (err) {
    console.error('Create folder error:', err);
    res.status(500).json({ error: 'Failed to create folder' });
  }
});

// DELETE /api/library/folders/:id (Admin only)
app.delete('/api/library/folders/:id', requireAuth, requireAdmin, (req, res) => {
  try {
    const folderId = req.params.id;
    db.prepare('DELETE FROM library_watches WHERE video_id IN (SELECT id FROM library_videos WHERE folder_id = ?)').run(folderId);
    db.prepare('DELETE FROM library_videos WHERE folder_id = ?').run(folderId);
    const info = db.prepare('DELETE FROM library_folders WHERE id = ?').run(folderId);
    if (info.changes === 0) return res.status(404).json({ error: 'Folder not found' });
    res.json({ success: true });
  } catch (err) {
    console.error('Delete folder error:', err);
    res.status(500).json({ error: 'Failed to delete folder' });
  }
});

// GET /api/library/folders/:folderId/videos (Public)
app.get('/api/library/folders/:folderId/videos', (req, res) => {
  try {
    const folderId = req.params.folderId;
    const folder = db.prepare('SELECT * FROM library_folders WHERE id = ?').get(folderId);
    if (!folder) return res.status(404).json({ error: 'Folder not found' });

    let videos = db.prepare(folder.storage === 'r2'
      ? 'SELECT * FROM library_videos WHERE folder_id = ? ORDER BY COALESCE(sort_at, created_at) DESC, id DESC'
      : 'SELECT * FROM library_videos WHERE folder_id = ? ORDER BY id DESC').all(folderId);
    if (folder.storage === 'r2') {
      // The bucket file name is never sent to browsers (playback goes through
      // signed passes). Logged-in viewers also get their own watch counts.
      const userId = optionalUserId(req);
      const used = userId
        ? Object.fromEntries(db.prepare(`
            SELECT video_id, COUNT(*) AS n FROM library_watches WHERE user_id = ? GROUP BY video_id
          `).all(userId).map(r => [r.video_id, r.n]))
        : {};
      videos = videos.map(({ r2_key, video_url, drive_id, ...v }) => ({
        ...v,
        storage: 'r2',
        watchesUsed: used[v.id] || 0,
        watchesLeft: Math.max(0, R2_WATCH_LIMIT - (used[v.id] || 0)),
        watchLimit: R2_WATCH_LIMIT
      }));
    }
    res.json({ folder, videos });
  } catch (err) {
    console.error('Fetch videos error:', err);
    res.status(500).json({ error: 'Failed to fetch videos' });
  }
});

// POST /api/library/videos (Admin only)
app.post('/api/library/videos', requireAuth, requireAdmin, (req, res) => {
  try {
    const { folder_id, title, video_url, description } = req.body || {};
    const targetFolder = db.prepare('SELECT storage FROM library_folders WHERE id = ?').get(folder_id);
    if (targetFolder && targetFolder.storage === 'r2') return addR2Video(req, res);
    if (!folder_id || !title || !title.trim() || !video_url || !video_url.trim()) {
      return res.status(400).json({ error: 'Folder ID, video title, and video URL are required' });
    }

    const cleanTitle = title.trim();
    const cleanUrl = video_url.trim();
    const cleanDesc = (description || '').trim();

    // Extract drive ID if Google Drive link
    let driveId = null;
    const matchPath = cleanUrl.match(/\/file\/d\/([a-zA-Z0-9_-]+)/);
    if (matchPath && matchPath[1]) driveId = matchPath[1];
    else {
      const matchQuery = cleanUrl.match(/id=([a-zA-Z0-9_-]+)/);
      if (matchQuery && matchQuery[1]) driveId = matchQuery[1];
      else if (/^[a-zA-Z0-9_-]{20,}$/.test(cleanUrl)) driveId = cleanUrl;
    }

    const info = db.prepare(`
      INSERT INTO library_videos (folder_id, title, video_url, drive_id, description) VALUES (?, ?, ?, ?, ?)
    `).run(folder_id, cleanTitle, cleanUrl, driveId, cleanDesc);

    res.json({
      success: true,
      video: { id: info.lastInsertRowid, folder_id, title: cleanTitle, video_url: cleanUrl, drive_id: driveId, description: cleanDesc }
    });
  } catch (err) {
    console.error('Add video error:', err);
    res.status(500).json({ error: 'Failed to add video' });
  }
});

// PATCH /api/library/videos/:id (Admin only) - rename; changes the title only.
app.patch('/api/library/videos/:id', requireAuth, requireAdmin, (req, res) => {
  try {
    const title = String((req.body || {}).title || '').trim();
    if (!title || title.length > 200) return res.status(400).json({ error: 'Title must be 1-200 characters' });
    const info = db.prepare('UPDATE library_videos SET title = ? WHERE id = ?').run(title, req.params.id);
    if (info.changes === 0) return res.status(404).json({ error: 'Video not found' });
    res.json({ success: true, title });
  } catch (err) {
    console.error('Rename video error:', err);
    res.status(500).json({ error: 'Failed to rename video' });
  }
});

// DELETE /api/library/videos/:id (Admin only)
app.delete('/api/library/videos/:id', requireAuth, requireAdmin, (req, res) => {
  try {
    const videoId = req.params.id;
    db.prepare('DELETE FROM library_watches WHERE video_id = ?').run(videoId);
    const info = db.prepare('DELETE FROM library_videos WHERE id = ?').run(videoId);
    fs.unlink(path.join(THUMB_DIR, `r2-${Number(videoId)}.jpg`), () => {});
    if (info.changes === 0) return res.status(404).json({ error: 'Video not found' });
    res.json({ success: true });
  } catch (err) {
    console.error('Delete video error:', err);
    res.status(500).json({ error: 'Failed to delete video' });
  }
});

// ---------- Library: R2 videos (two watches, then download-only) ----------
// Files sit in a private R2 bucket and are served only by the media Worker
// (media.biggboss24hrs.com), which needs a pass signed here:
//   watch pass    cookie sf_w_<videoId>, 2 min, renewed by a heartbeat while
//                 the player is open - so a watch ends ~2 min after the
//                 player is closed, and reopening within that window
//                 continues the SAME watch (grace for refresh / phone lock).
//   download link one-off URL, 6 h (resumable), whole file as an attachment.
// Each user gets R2_WATCH_LIMIT watches per video; after that the video is
// download-only. Admins are exempt (so testing never locks the owner out).
// Everything sits behind login + the rotating access link (gateStream).
const R2_WATCH_LIMIT = 2;
const R2_WATCH_GRACE_MS = 2 * 60 * 1000;
// 6h so a 20+ GB download that drops can resume with the same link (the Worker now
// honours Range on /d/); the old 10 min only covered an uninterrupted start.
const R2_DOWNLOAD_TTL_MS = 6 * 60 * 60 * 1000;
const MEDIA_ORIGIN = process.env.MEDIA_ORIGIN || 'https://media.biggboss24hrs.com';

function signMediaPass(payload) {
  const body = Buffer.from(JSON.stringify(payload)).toString('base64url');
  const sig = crypto.createHmac('sha256', process.env.MEDIA_SIGNING_SECRET).update(body).digest('base64url');
  return `${body}.${sig}`;
}

function isAdminUser(user) { return user?.role === 'admin' || !!user?.isAdmin; }

// Apple's media engine (every browser on iPhone/iPad, and Safari on Mac)
// can't start the long single-file MP4s in R2 - the 13.6h file's 61.7 MB index
// is fetched in many small requests and playback never begins. Those devices
// get download-only, without using watches. The page applies the same rule.
// A spoofed user agent can reach the download early (accepted by the owner).
function isApplePlayback(ua) {
  ua = String(ua || '');
  if (/iPhone|iPad|iPod/.test(ua)) return true;
  return /Macintosh/.test(ua) && /Safari/.test(ua) && !/Chrome|Chromium|CriOS|FxiOS|Firefox|Edg|OPR/.test(ua);
}

// Lists bucket objects through the Cloudflare API (prefix + exact-match is
// how a file's existence/size is checked - no S3 signing needed here).
async function r2ListObjects(prefix, perPage = 200) {
  const url = `https://api.cloudflare.com/client/v4/accounts/${process.env.R2_ACCOUNT_ID}/r2/buckets/${process.env.R2_BUCKET}/objects`
    + `?per_page=${perPage}` + (prefix ? `&prefix=${encodeURIComponent(prefix)}` : '');
  const res = await fetch(url, {
    headers: { Authorization: `Bearer ${process.env.CLOUDFLARE_R2_TOKEN}` },
    signal: AbortSignal.timeout(10000)
  });
  const json = await res.json().catch(() => ({}));
  if (!json.success) throw new Error('R2 list failed: ' + JSON.stringify(json.errors || res.status));
  return json.result || [];
}

function setWatchCookie(res, videoId, key, userId) {
  const exp = Date.now() + R2_WATCH_GRACE_MS;
  const opts = { httpOnly: true, secure: IS_PROD, path: '/v/', sameSite: 'lax', maxAge: R2_WATCH_GRACE_MS };
  if (IS_PROD) opts.domain = COOKIE_DOMAIN;
  res.cookie(`sf_w_${videoId}`, signMediaPass({ u: userId, k: key, v: videoId, exp }), opts);
}

function clearWatchCookie(res, videoId) {
  const opts = { path: '/v/' };
  if (IS_PROD) opts.domain = COOKIE_DOMAIN;
  res.clearCookie(`sf_w_${videoId}`, opts);
}

function getR2Video(videoId) {
  return db.prepare(`
    SELECT v.id, v.title, v.r2_key, f.storage
    FROM library_videos v JOIN library_folders f ON f.id = v.folder_id
    WHERE v.id = ?
  `).get(videoId);
}

// ---- R2 thumbnails ----
// ffmpeg reads the file through the media Worker with a short-lived pass,
// grabs the first frame (or the frame at 5s if the first is near-black, as
// a recording can start on black), scales it to 640px wide and saves a JPG
// that express.static serves. Generated once per video, one at a time.
const THUMB_DIR = '/var/www/streamflix/library/thumbs';
fs.mkdirSync(THUMB_DIR, { recursive: true });
let thumbQueue = Promise.resolve();

function runFfmpeg(args, { capture = false, timeoutMs = 60000 } = {}) {
  return new Promise((resolve, reject) => {
    const proc = spawn('/usr/bin/ffmpeg', args);
    const out = []; let err = '';
    proc.stdout.on('data', d => { if (capture) out.push(d); });
    proc.stderr.on('data', d => { err += d; });
    const timer = setTimeout(() => proc.kill('SIGKILL'), timeoutMs);
    proc.on('error', (e) => { clearTimeout(timer); reject(e); });
    proc.on('close', (code) => {
      clearTimeout(timer);
      code === 0 ? resolve(Buffer.concat(out)) : reject(new Error(`ffmpeg exited ${code}: ${err.slice(-300)}`));
    });
  });
}

async function makeR2Thumbnail(videoId, key) {
  const pass = signMediaPass({ u: 0, k: key, v: videoId, exp: Date.now() + 5 * 60 * 1000 });
  const src = `${MEDIA_ORIGIN}/v/${videoId}`;
  const tmp = path.join(THUMB_DIR, `.tmp-r2-${videoId}.jpg`);
  const finalPath = path.join(THUMB_DIR, `r2-${videoId}.jpg`);
  for (const at of [0, 5]) {
    await runFfmpeg(['-loglevel', 'error', '-y', '-headers', `Cookie: sf_w_${videoId}=${pass}\r\n`,
      '-ss', String(at), '-i', src, '-frames:v', '1', '-vf', 'scale=640:-2', '-q:v', '4', tmp]);
    // Average brightness: shrink to one grey pixel and read its value.
    const px = await runFfmpeg(['-loglevel', 'error', '-i', tmp, '-vf', 'scale=1:1,format=gray', '-f', 'rawvideo', '-'], { capture: true });
    if ((px[0] ?? 255) >= 16 || at === 5) break;
  }
  fs.renameSync(tmp, finalPath);
  const url = `/library/thumbs/r2-${videoId}.jpg?v=${Date.now()}`;
  db.prepare('UPDATE library_videos SET thumbnail_url = ? WHERE id = ?').run(url, videoId);
  console.log(`[R2] Thumbnail made for video ${videoId}.`);
}

function queueR2Thumbnail(videoId, key) {
  thumbQueue = thumbQueue
    .then(() => makeR2Thumbnail(videoId, key))
    .catch(err => console.error(`[R2] Thumbnail for video ${videoId} failed:`, err.message || err));
  return thumbQueue;
}

// Backfill: R2 videos added before thumbnails existed (or whose grab failed).
setTimeout(() => {
  for (const v of db.prepare('SELECT id, r2_key FROM library_videos WHERE r2_key IS NOT NULL AND thumbnail_url IS NULL').all()) {
    queueR2Thumbnail(v.id, v.r2_key);
  }
}, 10 * 1000);

const r2Limiter = makeLimiter(15 * 60 * 1000, 200, 'Too many requests. Please try again in a few minutes.');

// Admin: pick a file already uploaded to the bucket (the add-video form
// shows this list, so file names never have to be typed).
app.get('/api/library/r2/objects', requireAuth, requireAdmin, async (req, res) => {
  try {
    const used = new Set(db.prepare('SELECT r2_key FROM library_videos WHERE r2_key IS NOT NULL').all().map(r => r.r2_key));
    const objects = (await r2ListObjects('', 500))
      .filter(o => o.size > 0 && /\.(mp4|m4v|mov|webm)$/i.test(o.key))
      .map(o => ({ key: o.key, size: o.size, modified: o.last_modified, used: used.has(o.key) }));
    res.json({ objects });
  } catch (err) {
    console.error('[R2] list error:', err.message || err);
    res.status(502).json({ error: 'Could not list the bucket' });
  }
});

async function addR2Video(req, res) {
  try {
    const { folder_id, title, description, r2_key } = req.body || {};
    const cleanTitle = String(title || '').trim();
    const key = String(r2_key || '').trim();
    if (!folder_id || !cleanTitle || !key) {
      return res.status(400).json({ error: 'Folder, title and a bucket file are required' });
    }
    if (db.prepare('SELECT 1 FROM library_videos WHERE r2_key = ?').get(key)) {
      return res.status(409).json({ error: 'That file is already added' });
    }
    const found = (await r2ListObjects(key, 10)).find(o => o.key === key);
    if (!found) return res.status(404).json({ error: 'That file is not in the bucket' });

    const info = db.prepare(`
      INSERT INTO library_videos (folder_id, title, video_url, drive_id, description, r2_key, size_bytes, sort_at)
      VALUES (?, ?, ?, NULL, ?, ?, ?, ?)
    `).run(folder_id, cleanTitle, `r2:${key}`, String(description || '').trim(), key, found.size, recordingTimeFromKey(key));
    queueR2Thumbnail(Number(info.lastInsertRowid), key);
    res.json({ success: true, video: { id: info.lastInsertRowid, folder_id, title: cleanTitle, size_bytes: found.size, storage: 'r2' } });
  } catch (err) {
    console.error('[R2] add video error:', err.message || err);
    res.status(500).json({ error: 'Failed to add video' });
  }
}

// Start or continue a watch. Counts a new watch only when no watch of this
// video by this user was alive within the last 2 minutes.
app.post('/api/library/r2/:videoId/watch', r2Limiter, requireAuth, gateStream, (req, res) => {
  const video = getR2Video(Number(req.params.videoId));
  if (!video || video.storage !== 'r2' || !video.r2_key) return res.status(404).json({ error: 'Video not found' });
  const userId = req.user.id, now = Date.now(), admin = isAdminUser(req.user);

  const last = db.prepare('SELECT * FROM library_watches WHERE user_id = ? AND video_id = ? ORDER BY id DESC LIMIT 1').get(userId, video.id);
  const count = db.prepare('SELECT COUNT(*) AS n FROM library_watches WHERE user_id = ? AND video_id = ?').get(userId, video.id).n;

  if (!admin) {
    if (last && now - last.last_seen_at <= R2_WATCH_GRACE_MS) {
      db.prepare('UPDATE library_watches SET last_seen_at = ? WHERE id = ?').run(now, last.id);
    } else if (count >= R2_WATCH_LIMIT) {
      return res.status(403).json({ downloadOnly: true, watchesUsed: count, watchLimit: R2_WATCH_LIMIT });
    } else {
      db.prepare('INSERT INTO library_watches (user_id, video_id, started_at, last_seen_at) VALUES (?, ?, ?, ?)').run(userId, video.id, now, now);
    }
  }
  const used = admin ? 0 : db.prepare('SELECT COUNT(*) AS n FROM library_watches WHERE user_id = ? AND video_id = ?').get(userId, video.id).n;
  setWatchCookie(res, video.id, video.r2_key, userId);
  res.json({
    ok: true,
    src: `${MEDIA_ORIGIN}/v/${video.id}`,
    watchesUsed: used,
    watchesLeft: admin ? null : Math.max(0, R2_WATCH_LIMIT - used),
    watchLimit: R2_WATCH_LIMIT,
    heartbeatMs: 45 * 1000
  });
});

// Renews the pass while the player is open. Past the 2-minute window (a
// suspended tab, a lost connection) it refuses, and the page asks /watch
// again - which then counts as a new watch, or turns download-only.
app.post('/api/library/r2/:videoId/heartbeat', requireAuth, gateStream, (req, res) => {
  const video = getR2Video(Number(req.params.videoId));
  if (!video || video.storage !== 'r2' || !video.r2_key) return res.status(404).json({ error: 'Video not found' });
  const userId = req.user.id, now = Date.now();
  if (!isAdminUser(req.user)) {
    const last = db.prepare('SELECT * FROM library_watches WHERE user_id = ? AND video_id = ? ORDER BY id DESC LIMIT 1').get(userId, video.id);
    if (!last || now - last.last_seen_at > R2_WATCH_GRACE_MS) return res.status(410).json({ expired: true });
    db.prepare('UPDATE library_watches SET last_seen_at = ? WHERE id = ?').run(now, last.id);
  }
  setWatchCookie(res, video.id, video.r2_key, userId);
  res.json({ ok: true });
});

// Player closed: drop the pass now. last_seen_at is set to "now" so the
// 2-minute reopen window counts from the moment the viewer closed it.
app.post('/api/library/r2/:videoId/close', requireAuth, (req, res) => {
  const videoId = Number(req.params.videoId);
  if (!isAdminUser(req.user)) {
    const last = db.prepare('SELECT * FROM library_watches WHERE user_id = ? AND video_id = ? ORDER BY id DESC LIMIT 1').get(req.user.id, videoId);
    if (last && Date.now() - last.last_seen_at <= R2_WATCH_GRACE_MS) {
      db.prepare('UPDATE library_watches SET last_seen_at = ? WHERE id = ?').run(Date.now(), last.id);
    }
  }
  clearWatchCookie(res, videoId);
  res.json({ ok: true });
});

// Download link - only once the watches are used up (admins any time).
app.post('/api/library/r2/:videoId/download', r2Limiter, requireAuth, gateStream, (req, res) => {
  const video = getR2Video(Number(req.params.videoId));
  if (!video || video.storage !== 'r2' || !video.r2_key) return res.status(404).json({ error: 'Video not found' });
  const count = db.prepare('SELECT COUNT(*) AS n FROM library_watches WHERE user_id = ? AND video_id = ?').get(req.user.id, video.id).n;
  if (!isAdminUser(req.user) && count < R2_WATCH_LIMIT && !isApplePlayback(req.headers['user-agent'])) {
    return res.status(403).json({ error: 'Downloads unlock after your watches are used', watchesUsed: count, watchLimit: R2_WATCH_LIMIT });
  }
  const token = signMediaPass({
    u: req.user.id, k: video.r2_key, v: video.id, exp: Date.now() + R2_DOWNLOAD_TTL_MS,
    n: `${video.title}.mp4`, dl: 1
  });
  res.json({ url: `${MEDIA_ORIGIN}/d/${video.id}?t=${token}` });
});

// ---------- Live Polls & Predictions ----------
// Poll state lives in the DB, so polls and votes survive a restart.

const POLL_MAX_OPTIONS = 10;
const POLL_MAX_QUESTION_LEN = 300;
const POLL_MAX_OPTION_LEN = 100;
const POLL_MAX_ACTIVE = 5;
const POLL_RUN_HOURS = 12;
const POLL_RESULTS_HOURS = 8;

function buildPollPayload(pollId, userId) {
  const poll = db.prepare('SELECT * FROM polls WHERE id = ?').get(pollId);
  if (!poll) return null;

  const options = db.prepare(`
    SELECT o.id, o.label,
           (SELECT COUNT(*) FROM poll_votes v WHERE v.option_id = o.id) AS votes
    FROM poll_options o
    WHERE o.poll_id = ?
    ORDER BY o.position ASC, o.id ASC
  `).all(pollId);

  const totalVotes = options.reduce((sum, o) => sum + o.votes, 0);

  let yourVote = null;
  if (userId) {
    const row = db.prepare('SELECT option_id FROM poll_votes WHERE poll_id = ? AND user_id = ?').get(pollId, userId);
    if (row) yourVote = row.option_id;
  }

  return {
    id: poll.id,
    channel: poll.channel || 'live',
    question: poll.question,
    status: poll.status,
    created_at: poll.created_at,
    closed_at: poll.closed_at,
    closes_at: poll.closes_at,
    expires_at: poll.expires_at,
    options,
    totalVotes,
    yourVote
  };
}

// Results are broadcast at most once a second per poll, so a burst of votes
// can't flood every connected socket. Leading edge fires immediately; a
// trailing emit catches votes that landed during the window.
const pollResultsThrottle = new Map();

function broadcastPollResults(pollId, { immediate = false } = {}) {
  const emit = () => {
    const payload = buildPollPayload(pollId, null);
    if (payload) io.to(roomOf(payload.channel)).emit('poll_results', payload);
  };

  if (immediate) {
    const entry = pollResultsThrottle.get(pollId);
    if (entry && entry.timer) clearTimeout(entry.timer);
    pollResultsThrottle.delete(pollId);
    emit();
    return;
  }

  const existing = pollResultsThrottle.get(pollId);
  if (existing) {
    existing.pending = true;
    return;
  }

  emit();
  const timer = setTimeout(() => {
    const entry = pollResultsThrottle.get(pollId);
    pollResultsThrottle.delete(pollId);
    if (entry && entry.pending) emit();
  }, 1000);
  pollResultsThrottle.set(pollId, { timer, pending: false });
}

// Resolves the caller's user id if they happen to be logged in, without
// requiring it (used by the public GET so we can return "yourVote").
function optionalUserId(req) {
  try {
    let token = req.cookies && req.cookies.streamflix_session;
    if (!token && req.headers.authorization && req.headers.authorization.startsWith('Bearer ')) {
      token = req.headers.authorization.split(' ')[1];
    }
    if (!token) return null;
    return jwt.verify(token, JWT_SECRET).id || null;
  } catch {
    return null;
  }
}

// GET /api/polls/active — every poll still in the tab (running or showing
// results), newest first. Up to POLL_MAX_ACTIVE at a time (public).
app.get('/api/polls/active', (req, res) => {
  try {
    // status='open' always counts (a NULL closes_at on a pre-migration row
    // just means "no deadline yet", not "not in the tab"). A closed poll
    // only counts while still in its results window - a pre-migration
    // closed poll has NULL expires_at and must NOT resurface here.
    const rows = db.prepare(`
      SELECT id FROM polls
      WHERE channel = ? AND (status = 'open' OR (expires_at IS NOT NULL AND expires_at > datetime('now')))
      ORDER BY id DESC
    `).all(channelOf(req));
    const userId = optionalUserId(req);
    res.json({ polls: rows.map(r => buildPollPayload(r.id, userId)) });
  } catch (err) {
    console.error('Fetch active polls error:', err);
    res.status(500).json({ error: 'Failed to fetch polls' });
  }
});

// GET /api/polls/history — recent closed polls with final results (public)
app.get('/api/polls/history', (req, res) => {
  try {
    const rows = db.prepare(`SELECT id FROM polls WHERE channel = ? AND status = 'closed' ORDER BY id DESC LIMIT 10`).all(channelOf(req));
    res.json({ polls: rows.map(r => buildPollPayload(r.id, null)) });
  } catch (err) {
    console.error('Fetch poll history error:', err);
    res.status(500).json({ error: 'Failed to fetch poll history' });
  }
});

// POST /api/polls/:id/vote — cast or change a vote (login required)
app.post('/api/polls/:id/vote', requireAuth, (req, res) => {
  try {
    const pollId = Number(req.params.id);
    const optionId = Number((req.body || {}).option_id);
    if (!pollId || !optionId) return res.status(400).json({ error: 'Poll and option are required' });

    const poll = db.prepare(`
      SELECT *, (status = 'open' AND (closes_at IS NULL OR closes_at > datetime('now'))) AS is_votable
      FROM polls WHERE id = ?
    `).get(pollId);
    if (!poll) return res.status(404).json({ error: 'Poll not found' });
    // The is_votable check is belt-and-braces alongside sweepPolls(), which
    // flips status at closes_at on a 60s tick - this closes the gap between
    // expiry and the next sweep.
    if (!poll.is_votable) return res.status(409).json({ error: 'This poll is closed' });

    const option = db.prepare('SELECT id FROM poll_options WHERE id = ? AND poll_id = ?').get(optionId, pollId);
    if (!option) return res.status(400).json({ error: 'That option does not belong to this poll' });

    db.prepare(`
      INSERT INTO poll_votes (poll_id, option_id, user_id) VALUES (?, ?, ?)
      ON CONFLICT(poll_id, user_id) DO UPDATE SET option_id = excluded.option_id, created_at = CURRENT_TIMESTAMP
    `).run(pollId, optionId, req.user.id);

    broadcastPollResults(pollId);
    res.json({ success: true, poll: buildPollPayload(pollId, req.user.id) });
  } catch (err) {
    console.error('Vote error:', err);
    res.status(500).json({ error: 'Failed to record vote' });
  }
});

// POST /api/polls — create a poll and open it (Admin only)
app.post('/api/polls', requireAuth, requireAdmin, (req, res) => {
  try {
    const { question, options } = req.body || {};
    const cleanQuestion = (question || '').trim();
    if (!cleanQuestion) return res.status(400).json({ error: 'Question is required' });
    if (cleanQuestion.length > POLL_MAX_QUESTION_LEN) {
      return res.status(400).json({ error: `Question must be ${POLL_MAX_QUESTION_LEN} characters or fewer` });
    }

    const cleanOptions = (Array.isArray(options) ? options : [])
      .map(o => String(o || '').trim())
      .filter(Boolean)
      .slice(0, POLL_MAX_OPTIONS);

    if (cleanOptions.length < 2) return res.status(400).json({ error: 'At least 2 options are required' });
    if (cleanOptions.some(o => o.length > POLL_MAX_OPTION_LEN)) {
      return res.status(400).json({ error: `Options must be ${POLL_MAX_OPTION_LEN} characters or fewer` });
    }

    // Up to POLL_MAX_ACTIVE polls can be in the tab at once (running or
    // showing results). Capacity is checked inside the same transaction as
    // the insert to avoid a race between the check and the create. The
    // lifecycle is now purely time-driven: 12h open, then 8h showing
    // results, then deleted by sweepPolls() - there is no manual close.
    // Polls belong to the page they are created from, and the limit of
    // POLL_MAX_ACTIVE applies per page.
    const channel = channelOf(req);
    let capacityError = false;
    const createPoll = db.transaction(() => {
      const { count } = db.prepare(`
        SELECT COUNT(*) AS count FROM polls
        WHERE channel = ? AND (status = 'open' OR (expires_at IS NOT NULL AND expires_at > datetime('now')))
      `).get(channel);
      if (count >= POLL_MAX_ACTIVE) {
        capacityError = true;
        return null;
      }
      const info = db.prepare(`
        INSERT INTO polls (question, created_by, channel, closes_at, expires_at)
        VALUES (?, ?, ?, datetime('now', '+${POLL_RUN_HOURS} hours'), datetime('now', '+${POLL_RUN_HOURS + POLL_RESULTS_HOURS} hours'))
      `).run(cleanQuestion, req.user.username, channel);
      const insertOption = db.prepare('INSERT INTO poll_options (poll_id, label, position) VALUES (?, ?, ?)');
      cleanOptions.forEach((label, i) => insertOption.run(info.lastInsertRowid, label, i));
      return info.lastInsertRowid;
    });

    const pollId = createPoll();
    if (capacityError) {
      return res.status(409).json({ error: `${POLL_MAX_ACTIVE} polls already in the tab — delete one to make room.` });
    }

    const payload = buildPollPayload(pollId, null);
    io.to(roomOf(channel)).emit('poll_started', payload);
    res.json({ success: true, poll: payload });
  } catch (err) {
    console.error('Create poll error:', err);
    res.status(500).json({ error: 'Failed to create poll' });
  }
});

// DELETE /api/polls/:id (Admin only)
app.delete('/api/polls/:id', requireAuth, requireAdmin, (req, res) => {
  try {
    const pollId = Number(req.params.id);
    const pollChannel = db.prepare('SELECT channel FROM polls WHERE id = ?').get(pollId)?.channel || 'live';
    // Children removed explicitly - FK cascade isn't relied on here, matching
    // how the library folder delete is written.
    const removePoll = db.transaction(() => {
      db.prepare('DELETE FROM poll_votes WHERE poll_id = ?').run(pollId);
      db.prepare('DELETE FROM poll_options WHERE poll_id = ?').run(pollId);
      return db.prepare('DELETE FROM polls WHERE id = ?').run(pollId);
    });

    const info = removePoll();
    if (info.changes === 0) return res.status(404).json({ error: 'Poll not found' });

    io.to(roomOf(pollChannel)).emit('poll_closed', { id: pollId, deleted: true });
    res.json({ success: true });
  } catch (err) {
    console.error('Delete poll error:', err);
    res.status(500).json({ error: 'Failed to delete poll' });
  }
});

// POST /api/polls/:id/end — admin cuts an open poll short RIGHT NOW: declares
// final results to everyone currently watching (the same poll_closed shape
// sweepPolls() sends at the normal 12h mark), then deletes it outright
// instead of leaving it sitting in the results tab for the usual 8h window.
// Distinct from DELETE /api/polls/:id below, which sends {deleted:true} and
// makes the poll just vanish with no results shown at all - that route is
// for "this poll was a mistake", this one is for "call it now".
app.post('/api/polls/:id/end', requireAuth, requireAdmin, (req, res) => {
  try {
    const pollId = Number(req.params.id);
    const poll = db.prepare('SELECT status FROM polls WHERE id = ?').get(pollId);
    if (!poll) return res.status(404).json({ error: 'Poll not found' });
    if (poll.status !== 'open') return res.status(409).json({ error: 'This poll is already closed' });

    // Read while the votes/options rows still exist - buildPollPayload joins
    // against them, so it must run before the delete below.
    const finalPayload = buildPollPayload(pollId, null);
    const pollChannel = finalPayload.channel;
    finalPayload.status = 'closed';
    finalPayload.closed_at = new Date().toISOString();

    const removePoll = db.transaction(() => {
      db.prepare('DELETE FROM poll_votes WHERE poll_id = ?').run(pollId);
      db.prepare('DELETE FROM poll_options WHERE poll_id = ?').run(pollId);
      return db.prepare('DELETE FROM polls WHERE id = ?').run(pollId);
    });
    removePoll();

    // No {deleted:true} - the frontend's poll_closed handler only removes
    // the card on that flag, otherwise it renders status:'closed' as final
    // results (renderPollCard's isClosed branch), which is what we want
    // here: results stay visible on already-open tabs even though the DB
    // row is already gone. A fresh page load won't see it (not in history -
    // the row is deleted, not just status-flipped), which is the "delete"
    // half of what this route promises.
    io.to(roomOf(pollChannel)).emit('poll_closed', finalPayload);

    res.json({ success: true, poll: finalPayload });
  } catch (err) {
    console.error('End poll error:', err);
    res.status(500).json({ error: 'Failed to end poll' });
  }
});

// Every poll now runs on a fixed clock (open -> results -> gone) instead of
// being closed by hand, so something has to advance that clock. Runs on the
// same 60s cadence as the title sweeps; logs only when it actually acted,
// matching the cleanupOldMessages() house pattern.
function sweepPolls() {
  try {
    const toClose = db.prepare(`
      SELECT id, channel FROM polls WHERE status = 'open' AND closes_at <= datetime('now')
    `).all();
    if (toClose.length > 0) {
      const closeStmt = db.prepare(`UPDATE polls SET status = 'closed', closed_at = CURRENT_TIMESTAMP WHERE id = ?`);
      toClose.forEach(({ id, channel }) => {
        closeStmt.run(id);
        io.to(roomOf(channel || 'live')).emit('poll_closed', buildPollPayload(id, null));
      });
      console.log(`[Poll Sweep] Auto-closed ${toClose.length} poll(s).`);
    }

    const toDelete = db.prepare(`
      SELECT id, channel FROM polls WHERE expires_at IS NOT NULL AND expires_at <= datetime('now')
    `).all();
    if (toDelete.length > 0) {
      const removePoll = db.transaction((id) => {
        db.prepare('DELETE FROM poll_votes WHERE poll_id = ?').run(id);
        db.prepare('DELETE FROM poll_options WHERE poll_id = ?').run(id);
        db.prepare('DELETE FROM polls WHERE id = ?').run(id);
      });
      toDelete.forEach(({ id, channel }) => {
        removePoll(id);
        io.to(roomOf(channel || 'live')).emit('poll_closed', { id, deleted: true });
      });
      console.log(`[Poll Sweep] Deleted ${toDelete.length} expired poll(s).`);
    }
  } catch (err) {
    console.error('[Poll Sweep Error]:', err);
  }
}

sweepPolls();
setInterval(sweepPolls, 60 * 1000);

// ---------- Clips ----------
// Cuts an MP4 straight out of the OME LLHLS DVR window with `-c copy` (no
// re-encode - measured at ~0.15s CPU / ~0.6s wall per 30s clip on this box).
// No watermark, no DB row, no retention: the 2h DVR window is already the
// archive, so keeping a saved copy would just duplicate data we already have.
// The file lives just long enough to stream to the requester, then it's gone.
const CLIP_TMP_DIR = '/tmp/streamflix-clips';
const CLIP_STREAM_NAME = 'stream';
// Loopback base of a channel's OME application (clips never go through nginx/Cloudflare).
function clipOrigin(channel) { return `http://127.0.0.1:3333/${CHANNEL_OME_APP[channel]}`; }
const CLIP_MAX_DURATION_SEC = 60; // was 30 - raised so Share/Download can cover a full Reels/Story-length moment
const CLIP_MAX_CONCURRENT = 8;
const CLIP_MAX_QUEUE_DEPTH = 30;
// Clips vary 13x in size (a 360p preview vs a 30s 1080p download), so a
// request-count limit is a poor proxy for cost - it either starves cheap
// previews or, as happened when quality was raised from 720p to 1080p,
// silently becomes far more permissive without anyone changing the number.
// Budgeting by bytes actually served lets a user make many cheap previews OR
// a few full-quality downloads, whichever they need.
const CLIP_BYTE_BUDGET_WINDOW_MS = 15 * 60 * 1000;
const CLIP_BYTE_BUDGET_MAX_BYTES = 300 * 1024 * 1024; // ~9-10 full 60s 1080p clips per 15 min (raised alongside the 60s cap so clip COUNT feels the same as the old 30s/150MB limit)

fs.mkdirSync(CLIP_TMP_DIR, { recursive: true });

// Sweep leftovers from crashed jobs on startup, then hourly - a clip file
// should never live longer than the request that produced it, so anything
// found here is orphaned by definition.
function sweepClipTmpDir() {
  try {
    for (const f of fs.readdirSync(CLIP_TMP_DIR)) {
      try { fs.unlinkSync(path.join(CLIP_TMP_DIR, f)); } catch {}
    }
  } catch (err) {
    console.error('Clip tmp sweep error:', err);
  }
}
sweepClipTmpDir();
setInterval(sweepClipTmpDir, 60 * 60 * 1000);

let clipActiveJobs = 0;
let clipQueueDepth = 0;
const clipByteLedger = new Map(); // userId -> [{ts, bytes}]
setInterval(() => {
  const now = Date.now();
  for (const [userId, entries] of clipByteLedger) {
    const kept = entries.filter(e => now - e.ts < CLIP_BYTE_BUDGET_WINDOW_MS);
    if (kept.length === 0) clipByteLedger.delete(userId);
    else clipByteLedger.set(userId, kept);
  }
}, 60 * 1000);

function clipBytesUsed(userId) {
  const now = Date.now();
  const entries = (clipByteLedger.get(userId) || []).filter(e => now - e.ts < CLIP_BYTE_BUDGET_WINDOW_MS);
  clipByteLedger.set(userId, entries);
  return entries.reduce((sum, e) => sum + e.bytes, 0);
}

function clipByteBudgetExceeded(userId) {
  return clipBytesUsed(userId) >= CLIP_BYTE_BUDGET_MAX_BYTES;
}

function clipRecordBytes(userId, bytes) {
  const entries = clipByteLedger.get(userId) || [];
  entries.push({ ts: Date.now(), bytes });
  clipByteLedger.set(userId, entries);
}

// Picks the highest-resolution video rendition from the master manifest, plus
// the audio chunklist, by URI - OME's internal track numbers are assigned by
// config order and shouldn't be assumed stable here.
//
// The best rendition is the BYPASS track: OBS's own feed passed through
// untouched (measured 3.91 Mbps at 1080p). The transcoded ladder lands well
// under its configured targets - 720p produces ~0.99 Mbps against a 2.5 Mbps
// setting - which made clips look soft. Cutting from the bypass track costs no
// extra CPU, since this pipeline is `-c copy` either way and never invokes an
// encoder; only the file size grows.
// quality: 'preview' picks the lowest-bandwidth rendition (cheap, for the
// Preview button - visual fidelity doesn't matter for confirming timing/
// framing); '720p' picks the closest match to 720p; anything else (including
// the default) picks the tallest available - the bypass track, full quality,
// for an actual Download.
async function getClipSourceChunklists(quality, channel = 'live') {
  // SignedPolicy now gates the manifest (not chunklists/segments), so this
  // loopback fetch needs a signature too - it was missed in the original
  // rollout since only the browser-facing path (/api/stream/urls) and RTMP
  // publish were tested. Reuse signOmeUrl's query string (computed against
  // OME_INTERNAL_SIGNING_ORIGIN, which is what OME actually verifies
  // against) but keep fetching over loopback - CLIP_ORIGIN exists
  // specifically to avoid a round trip through Cloudflare/nginx for every
  // clip cut. Uses http.request rather than fetch() because fetch silently
  // drops a custom Host header (a spec-forbidden header) - confirmed by a
  // direct test where fetch's override was ignored (401) but an identical
  // http.request with the same header succeeded (200). OME needs that
  // header to know which virtual host's signing key to verify against,
  // since the loopback request otherwise arrives as Host: 127.0.0.1:3333.
  const omeApp = CHANNEL_OME_APP[channel];
  const signedQuery = signOmeUrl(`/${omeApp}/${CLIP_STREAM_NAME}/llhls.m3u8`, 5 * 60 * 1000).split('?')[1];
  const masterPath = `/${omeApp}/${CLIP_STREAM_NAME}/llhls.m3u8?${signedQuery}`;
  const text = await new Promise((resolve, reject) => {
    const req = http.request({
      hostname: '127.0.0.1',
      port: 3333,
      path: masterPath,
      method: 'GET',
      headers: { Host: 'biggboss24hrs.com' }
    }, (res) => {
      if (res.statusCode !== 200) {
        res.resume();
        return reject(new Error(`Master manifest fetch failed: ${res.statusCode}`));
      }
      let body = '';
      res.on('data', (d) => { body += d; });
      res.on('end', () => resolve(body));
    });
    req.on('error', reject);
    req.end();
  });
  const lines = text.split('\n').map(l => l.trim());

  let audioChunklist = null;
  const audioMatch = text.match(/#EXT-X-MEDIA:TYPE=AUDIO[^\n]*URI="([^"]+)"/);
  if (audioMatch) audioChunklist = audioMatch[1];

  const renditions = [];
  for (let i = 0; i < lines.length; i++) {
    if (!lines[i].startsWith('#EXT-X-STREAM-INF:')) continue;
    const uri = lines[i + 1];
    if (!uri || !uri.endsWith('.m3u8')) continue;
    const resMatch = lines[i].match(/RESOLUTION=(\d+)x(\d+)/);
    renditions.push({ uri, height: resMatch ? Number(resMatch[2]) : 0 });
  }
  if (renditions.length === 0) {
    throw new Error('Could not locate any video rendition in master manifest');
  }

  let videoChunklist;
  if (quality === 'preview') {
    videoChunklist = renditions.reduce((a, b) => (b.height < a.height ? b : a)).uri;
  } else if (quality === '720p') {
    // 720p if it exists; otherwise the next one UP (live drops 720p while the
    // episode is on - a "720p" clip should then be sharper, not blurrier).
    const atLeast = renditions.filter(r => r.height >= 720);
    videoChunklist = (atLeast.length
      ? atLeast.reduce((a, b) => (b.height < a.height ? b : a))
      : renditions.reduce((a, b) => (b.height > a.height ? b : a))).uri;
  } else {
    videoChunklist = renditions.reduce((a, b) => (b.height > a.height ? b : a)).uri;
  }

  if (!videoChunklist || !audioChunklist) {
    throw new Error('Could not locate video/audio chunklists in master manifest');
  }

  return {
    videoChunklistUrl: `${clipOrigin(channel)}/${CLIP_STREAM_NAME}/${videoChunklist}`,
    audioChunklistUrl: `${clipOrigin(channel)}/${CLIP_STREAM_NAME}/${audioChunklist}`
  };
}

// Parses a chunklist into its init-segment URI plus a table of
// {uri, startMs, durSec} per media segment. Each full segment carries its own
// #EXT-X-PROGRAM-DATE-TIME immediately before its #EXTINF/URI pair (verified
// against the live stream); a segment lacking one (shouldn't happen, but not
// assumed) falls back to the previous segment's end time.
function parseChunklist(text) {
  const lines = text.split('\n').map(l => l.trim());
  let initUri = null;
  const mapMatch = text.match(/#EXT-X-MAP:URI="([^"]+)"/);
  if (mapMatch) initUri = mapMatch[1];

  const segments = [];
  let pendingPdtMs = null;
  let pendingDurSec = null;
  for (const line of lines) {
    if (line.startsWith('#EXT-X-PROGRAM-DATE-TIME:')) {
      pendingPdtMs = new Date(line.slice('#EXT-X-PROGRAM-DATE-TIME:'.length)).getTime();
    } else if (line.startsWith('#EXTINF:')) {
      pendingDurSec = parseFloat(line.slice('#EXTINF:'.length));
    } else if (line && !line.startsWith('#')) {
      const prev = segments[segments.length - 1];
      const durSec = pendingDurSec != null ? pendingDurSec : 6;
      const startMs = pendingPdtMs != null ? pendingPdtMs
        : (prev ? prev.startMs + prev.durSec * 1000 : null);
      segments.push({ uri: line, startMs, durSec });
      pendingPdtMs = null;
      pendingDurSec = null;
    }
  }
  if (!initUri || segments.length === 0 || segments[0].startMs == null) {
    throw new Error('Could not parse chunklist (missing EXT-X-MAP or timing info)');
  }
  return { initUri, segments };
}

class ClipOutOfWindowError extends Error {}

// Fetches exactly the segments overlapping [startMs, endMs] (plus the init
// segment) over loopback and concatenates them into a local fMP4 file. This
// deliberately avoids handing a live HLS playlist URL to ffmpeg at all -
// ffmpeg's HLS demuxer was found to silently ignore input-side -ss against a
// live playlist (verified: cutting at 60s/900s/1800s offsets produced
// byte-identical output every time). Once ffmpeg is operating on a plain
// local file, input -ss behaves correctly.
async function buildTrackTempFile(chunklistUrl, startMs, endMs, outPath) {
  const base = chunklistUrl.slice(0, chunklistUrl.lastIndexOf('/') + 1);
  const res = await fetch(chunklistUrl);
  if (!res.ok) throw new Error(`Chunklist fetch failed: ${res.status}`);
  const { initUri, segments } = parseChunklist(await res.text());

  const windowStartMs = segments[0].startMs;
  const last = segments[segments.length - 1];
  const windowEndMs = last.startMs + last.durSec * 1000;
  if (endMs <= windowStartMs || startMs >= windowEndMs) {
    throw new ClipOutOfWindowError('Requested range has aged out of the DVR window');
  }

  const selected = segments.filter(s => startMs < s.startMs + s.durSec * 1000 && endMs > s.startMs);
  if (selected.length === 0) throw new ClipOutOfWindowError('Requested range not found in DVR window');

  const initRes = await fetch(base + initUri);
  if (!initRes.ok) throw new Error(`Init segment fetch failed: ${initRes.status}`);
  const chunks = [Buffer.from(await initRes.arrayBuffer())];

  for (const seg of selected) {
    const segRes = await fetch(base + seg.uri);
    if (!segRes.ok) throw new Error(`Segment fetch failed: ${segRes.status}`);
    chunks.push(Buffer.from(await segRes.arrayBuffer()));
  }

  fs.writeFileSync(outPath, Buffer.concat(chunks));
  return { firstSegmentStartMs: selected[0].startMs };
}

const CLIP_ALLOWED_QUALITIES = new Set(['preview', '720p', '1080p']);

// Shared by both the direct POST route (used for Preview - fast feedback,
// never cached, since previews are per-user exploratory nudges) and the
// signed GET route (used for Download - deliberately cacheable, since at a
// viral moment many viewers download the exact same clip). Writes the
// response itself; does NOT touch the byte budget - callers decide whether
// and when to charge it, since the GET route's cost only applies to whoever
// actually causes a cache MISS.
async function cutAndStreamClip(req, res, { startMs, durationSec, quality, onProduced, channel = 'live' }) {
  if (clipActiveJobs >= CLIP_MAX_CONCURRENT && clipQueueDepth >= CLIP_MAX_QUEUE_DEPTH) {
    return res.status(429).json({ error: 'Server busy cutting clips - try again in a moment.' });
  }

  clipQueueDepth++;
  try {
    // Simple cooperative wait for a job slot - fine at this scale (jobs
    // finish in well under a second), avoids pulling in a queue library.
    while (clipActiveJobs >= CLIP_MAX_CONCURRENT) {
      await new Promise(r => setTimeout(r, 100));
    }
  } finally {
    clipQueueDepth--;
  }
  clipActiveJobs++;

  const jobId = crypto.randomBytes(12).toString('hex');
  const videoTemp = path.join(CLIP_TMP_DIR, `${jobId}-v.m4s`);
  const audioTemp = path.join(CLIP_TMP_DIR, `${jobId}-a.m4s`);
  const outFile = path.join(CLIP_TMP_DIR, `${jobId}.mp4`);
  const cleanupTemps = () => {
    for (const f of [videoTemp, audioTemp, outFile]) fs.unlink(f, () => {});
  };
  let ffmpegProc = null;

  try {
    const { videoChunklistUrl, audioChunklistUrl } = await getClipSourceChunklists(quality, channel);
    const endMs = startMs + durationSec * 1000;

    // Both tracks are fetched into local files first - ffmpeg then seeks
    // within plain files, never against the live chunklist URL directly.
    const [videoInfo] = await Promise.all([
      buildTrackTempFile(videoChunklistUrl, startMs, endMs, videoTemp),
      buildTrackTempFile(audioChunklistUrl, startMs, endMs, audioTemp)
    ]);

    // Both chunklists share the same segment timeline (verified: identical
    // MEDIA-SEQUENCE and segment count, PDTs within 33ms), so the video
    // track's selected-segment start is used as the seek anchor for both.
    const ss = Math.max(0, (startMs - videoInfo.firstSegmentStartMs) / 1000);

    const args = [
      '-hide_banner', '-loglevel', 'error',
      '-ss', String(ss), '-i', videoTemp,
      '-ss', String(ss), '-i', audioTemp,
      '-t', String(durationSec),
      '-map', '0:v', '-map', '1:a',
      '-c', 'copy',
      '-movflags', '+faststart',
      '-y', outFile
    ];

    await new Promise((resolve, reject) => {
      ffmpegProc = spawn('/usr/bin/ffmpeg', args);
      let stderr = '';
      ffmpegProc.stderr.on('data', d => { stderr += d; });
      ffmpegProc.on('error', reject);
      ffmpegProc.on('close', code => {
        if (code === 0) resolve();
        else reject(new Error(`ffmpeg exited ${code}: ${stderr.slice(-500)}`));
      });

      req.on('close', () => {
        if (ffmpegProc && !ffmpegProc.killed) ffmpegProc.kill('SIGKILL');
      });
    });

    if (!fs.existsSync(outFile)) throw new Error('ffmpeg produced no output');

    if (onProduced) onProduced(fs.statSync(outFile).size);

    res.set('Content-Type', 'video/mp4');
    res.set('Content-Disposition', 'attachment; filename="clip.mp4"');
    // Plain .pipe() does not guarantee cleanup runs when the DESTINATION (the
    // HTTP response) errors first - e.g. the client disconnects mid-transfer
    // - which left real orphaned temp files during testing. pipeline() closes
    // both ends and fires its callback exactly once regardless of which side
    // failed.
    pipeline(fs.createReadStream(outFile), res, (err) => {
      cleanupTemps();
      if (err) console.error('Clip stream error:', err.message);
    });
  } catch (err) {
    if (err instanceof ClipOutOfWindowError) {
      cleanupTemps();
      return res.status(400).json({ error: err.message });
    }
    console.error('Clip creation error:', err);
    cleanupTemps();
    if (!res.headersSent) res.status(500).json({ error: 'Failed to create clip' });
  } finally {
    clipActiveJobs--;
  }
}

// Clips cut the real stream, so they need today's link like the stream URL
// does. JSON, not gateStream's plain text, because the clip dialog reads
// data.error to tell the viewer what to do.
function requireAccessForClips(req, res, next) {
  if (hasAccessSession(req)) return next();
  return res.status(403).json({ error: "Today's access link has changed. Open the new link from the group, then try again." });
}

app.post('/api/clips', requireAuth, requireAccessForClips, async (req, res) => {
  const userId = req.user?.id;
  if (clipByteBudgetExceeded(userId)) {
    return res.status(429).json({ error: 'Clip data limit reached for now - please wait a few minutes.' });
  }

  const { startIso, endIso } = req.body || {};
  const quality = CLIP_ALLOWED_QUALITIES.has(req.body?.quality) ? req.body.quality : '1080p';
  const startMs = Date.parse(startIso);
  const endMs = Date.parse(endIso);
  if (!Number.isFinite(startMs) || !Number.isFinite(endMs) || endMs <= startMs) {
    return res.status(400).json({ error: 'Invalid start/end timestamps' });
  }
  const durationSec = (endMs - startMs) / 1000;
  if (durationSec > CLIP_MAX_DURATION_SEC) {
    return res.status(400).json({ error: `Clips are capped at ${CLIP_MAX_DURATION_SEC}s` });
  }

  // Charge the budget for what was actually produced, not an estimate -
  // sizes vary too much across quality/duration combinations to guess.
  await cutAndStreamClip(req, res, {
    startMs, durationSec, quality,
    channel: channelOf(req),
    onProduced: (bytes) => clipRecordBytes(userId, bytes)
  });
});

// ---- Signed, cacheable clip delivery (Clip Tier 3) ----
// A viral moment gets clipped by many viewers at once, and every one of those
// downloads was, until now, a full uncacheable origin fetch. This splits
// authentication from delivery: POST /sign checks the user's byte budget and
// hands back a URL; GET actually cuts and streams the clip and carries NO
// requireAuth, because a Cloudflare cache HIT never reaches this route at
// all - it's answered entirely at the edge. That is also exactly why the
// signature below is load-bearing rather than decorative: without it, this
// GET route would let anyone enumerate the entire DVR window by timestamp,
// with no login and no access-link check.
//
// startSec is quantized to a 2s grid. This is nearly free: -c copy already
// snaps cuts to keyframes, and the bypass track's keyframes are ~2s apart, so
// a request for a non-grid-aligned time already returns the same bytes as the
// nearest grid point would. Quantizing the URL just lets viewers who ask for
// "the same moment" (inevitable during a shared dramatic beat) collapse onto
// one cache entry instead of each paying full egress.
const CLIP_QUANTUM_SEC = 2;

// The live channel keeps the original signed string so clip links already
// handed out stay valid; the episode channel adds its name, so its links
// can never collide with (or be forged from) a live link for the same
// timestamp - they also sit under a different URL path, which keeps the
// Cloudflare cache entries apart.
function clipSignature(startSec, durationSec, quality, channel = 'live') {
  const suffix = channel === 'live' ? '' : `|${channel}`;
  return crypto.createHmac('sha256', process.env.CLIP_SIGNING_SECRET)
    .update(`${startSec}|${durationSec}|${quality}${suffix}`)
    .digest('hex')
    .slice(0, 24);
}

app.post('/api/clips/sign', requireAuth, requireAccessForClips, (req, res) => {
  const userId = req.user?.id;
  if (clipByteBudgetExceeded(userId)) {
    return res.status(429).json({ error: 'Clip data limit reached for now - please wait a few minutes.' });
  }

  const { startIso, endIso } = req.body || {};
  const quality = CLIP_ALLOWED_QUALITIES.has(req.body?.quality) ? req.body.quality : '1080p';
  const startMs = Date.parse(startIso);
  const endMs = Date.parse(endIso);
  if (!Number.isFinite(startMs) || !Number.isFinite(endMs) || endMs <= startMs) {
    return res.status(400).json({ error: 'Invalid start/end timestamps' });
  }
  const durationSec = Math.round((endMs - startMs) / 1000);
  if (durationSec > CLIP_MAX_DURATION_SEC) {
    return res.status(400).json({ error: `Clips are capped at ${CLIP_MAX_DURATION_SEC}s` });
  }

  const startSec = Math.floor(startMs / 1000 / CLIP_QUANTUM_SEC) * CLIP_QUANTUM_SEC;
  const channel = channelOf(req);
  const sig = clipSignature(startSec, durationSec, quality, channel);

  // Charged here at an estimate, not after the fact: whether this URL turns
  // into an origin cut at all depends on cache state we don't control, so
  // there is no "actual bytes produced" moment to hook for a GET request that
  // might be answered entirely from Cloudflare's edge.
  const ESTIMATED_BYTES_PER_SEC = { preview: 40000, '720p': 125000, '1080p': 520000 };
  clipRecordBytes(userId, durationSec * (ESTIMATED_BYTES_PER_SEC[quality] || ESTIMATED_BYTES_PER_SEC['1080p']));

  const prefix = channel === 'live' ? '/api/clips' : `/api/clips/${channel}`;
  res.json({ url: `${prefix}/${startSec}/${durationSec}/${quality}/${sig}.mp4` });
});

async function handleSignedClipGet(req, res, channel) {
  const startSec = Number(req.params.startSec);
  const durationSec = Number(req.params.durationSec);
  const quality = req.params.quality;

  if (!Number.isInteger(startSec) || startSec < 0
      || !Number.isInteger(durationSec) || durationSec <= 0 || durationSec > CLIP_MAX_DURATION_SEC
      || !CLIP_ALLOWED_QUALITIES.has(quality)) {
    return res.status(400).json({ error: 'Invalid clip parameters' });
  }

  const expectedSig = clipSignature(startSec, durationSec, quality, channel);
  const providedSig = String(req.params.sig || '');
  const expectedBuf = Buffer.from(expectedSig);
  const providedBuf = Buffer.from(providedSig);
  const validSig = expectedBuf.length === providedBuf.length
    && crypto.timingSafeEqual(expectedBuf, providedBuf);
  if (!validSig) {
    return res.status(403).json({ error: 'Invalid or expired clip link' });
  }

  await cutAndStreamClip(req, res, { startMs: startSec * 1000, durationSec, quality, channel });
}

app.get('/api/clips/:startSec/:durationSec/:quality/:sig.mp4', (req, res) => handleSignedClipGet(req, res, 'live'));
app.get('/api/clips/episode/:startSec/:durationSec/:quality/:sig.mp4', (req, res) => handleSignedClipGet(req, res, 'episode'));

// Bound to loopback only - nginx is the sole intended caller (it already
// proxies here via http://127.0.0.1:4000 in every location block). This
// was previously bound to 0.0.0.0/::, reachable from the internet with only
// ufw standing between it and the origin IP directly - defense in depth,
// not a fix on its own (ufw has no rule for 4000 either way).
server.listen(PORT, '127.0.0.1', () => console.log(`Auth server running on port ${PORT} (127.0.0.1 only)`));