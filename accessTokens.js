'use strict';

/**
 * accessTokens.js
 * ---------------
 * Rotating access-link system for biggboss24hrs.com.
 *
 * Exports:
 *   initAccessTokens(db, app, jwt, IS_PROD, JWT_SECRET, SITE_ORIGIN)
 *   requireAccessSession(req, res, next)
 *   gateStream(req, res, next)
 */

const crypto = require('crypto');
const path   = require('path');
const rateLimit = require('express-rate-limit');

const TWENTY_FOUR_HOURS_MS = 24 * 60 * 60 * 1000;
const NO_ACCESS_PAGE    = path.join(__dirname, 'public', 'no-access.html');

// Same X-Real-IP rationale as server.js's realIp()/makeLimiter(): nginx
// forwards CF-Connecting-IP there, and every request on 443 already came
// through Cloudflare (ufw restricts that port to Cloudflare's ranges).
// Routed through ipKeyGenerator so an IPv6 client can't bypass the limit
// by rotating addresses within their own /64 - see server.js's realIp()
// for the fuller explanation (same fix, same reason, caught by
// express-rate-limit's own startup validation in both files).
const { ipKeyGenerator } = rateLimit;

function realIp(req) {
  return ipKeyGenerator(req.headers['x-real-ip'] || req.ip);
}

// /access: unlimited before this, though the 192-bit random token makes
// brute force computationally infeasible regardless - this is mainly
// defense in depth. /admin/current-link: unlimited before this, and a
// single successful guess of ADMIN_KEY leaks the live invite link,
// defeating the whole gate - this one matters more.
const accessLimiter = rateLimit({
  windowMs: 60 * 60 * 1000, max: 20, keyGenerator: realIp,
  standardHeaders: true, legacyHeaders: false,
  message: { error: 'Too many attempts. Please try again later.' }
});
const adminLinkLimiter = rateLimit({
  windowMs: 60 * 60 * 1000, max: 5, keyGenerator: realIp,
  standardHeaders: true, legacyHeaders: false,
  message: { error: 'Too many attempts. Please try again later.' }
});

// Module-level references (populated by initAccessTokens)
let _db;
let _jwt;
let _jwtSecret;
let _isProd;
let _siteOrigin;

// ─── DB migration ─────────────────────────────────────────────────────────
function runMigration(db) {
  db.exec(`
    CREATE TABLE IF NOT EXISTS access_tokens (
      token      TEXT PRIMARY KEY,
      created_at INTEGER NOT NULL,
      expires_at INTEGER NOT NULL,
      is_active  INTEGER NOT NULL DEFAULT 1
    );
  `);
}

// ─── Token rotation ────────────────────────────────────────────────────────
function rotateToken() {
  const now       = Date.now();
  const expiresAt = now + TWENTY_FOUR_HOURS_MS;
  const token     = crypto.randomBytes(24).toString('hex');

  const rotate = _db.transaction(() => {
    _db.prepare('UPDATE access_tokens SET is_active = 0 WHERE is_active = 1').run();
    _db.prepare(
      'INSERT INTO access_tokens (token, created_at, expires_at, is_active) VALUES (?, ?, ?, 1)'
    ).run(token, now, expiresAt);
  });

  rotate();

  const expiresLocal = new Date(expiresAt).toISOString();
  console.log('[AccessTokens] Token rotated. New token expires at ' + expiresLocal);
  return token;
}

function getActiveToken() {
  return _db
    .prepare('SELECT * FROM access_tokens WHERE is_active = 1 AND expires_at > ?')
    .get(Date.now());
}

// ─── Middleware helpers ────────────────────────────────────────────────────
function verifyAccessCookie(req) {
  const token = req.cookies && req.cookies.access_session;
  if (!token) return null;
  try {
    const payload = _jwt.verify(token, _jwtSecret);
    if (payload.type !== 'access_session') return null;
    return payload;
  } catch {
    return null;
  }
}

// Being logged in (any method - Google, X, admin password) USED to be
// enough on its own, independent of the rotating link (see git history for
// the previous verifyUserSession-based OR check). Deliberately reversed:
// no sign-in method may bypass the current link - a valid access_session,
// obtained by redeeming today's rotating /access?token=, is now required
// regardless of login state. mintAccessSession() (server.js) - which used
// to hand OAuth logins a free 24h access_session - is removed for the same
// reason; see its former call sites in the X/Google callbacks.
function requireAccessSession(req, res, next) {
  if (verifyAccessCookie(req)) return next();
  return res.status(200).sendFile(NO_ACCESS_PAGE);
}

function gateStream(req, res, next) {
  if (verifyAccessCookie(req)) return next();
  return res.status(403).send('Forbidden: valid access session required.');
}

// ─── Route: GET /access?token=xxx ─────────────────────────────────────────
function registerAccessRoute(app) {
  app.get('/access', accessLimiter, (req, res) => {
    const { token } = req.query;

    if (!token) {
      return res.status(400).send('<p style="font-family:sans-serif">Missing token parameter.</p>');
    }

    const now = Date.now();
    const row = _db
      .prepare('SELECT * FROM access_tokens WHERE token = ? AND is_active = 1 AND expires_at > ?')
      .get(token, now);

    if (!row) {
      return res.status(403).send(
        '<!DOCTYPE html><html><head><title>Access Denied</title>' +
        '<meta name="viewport" content="width=device-width,initial-scale=1">' +
        '<style>body{font-family:sans-serif;display:flex;align-items:center;justify-content:center;' +
        'min-height:100vh;margin:0;background:#0f0f0f;color:#e0e0e0;}' +
        'p{font-size:1.1rem;text-align:center;max-width:400px;line-height:1.6}</style></head>' +
        '<body><p>This access link is <strong>invalid or has expired</strong>.<br>' +
        'Get the current link from the group.</p></body></html>'
      );
    }

    const remainingMs = row.expires_at - now;
    const remainingS  = Math.floor(remainingMs / 1000);

    const sessionJwt = _jwt.sign(
      { type: 'access_session' },
      _jwtSecret,
      { expiresIn: remainingS }
    );

    res.cookie('access_session', sessionJwt, {
      httpOnly: true,
      secure:   _isProd,
      path:     '/',
      sameSite: 'lax',
      maxAge:   remainingMs
    });

    return res.redirect('/');
  });
}

// ─── Route: GET /admin/current-link?key=xxx ───────────────────────────────
function registerAdminRoute(app, siteOrigin) {
  app.get('/admin/current-link', adminLinkLimiter, (req, res) => {
    const adminKey = process.env.ADMIN_KEY;

    if (!adminKey) {
      console.error('[AccessTokens] ADMIN_KEY is not set in .env');
      return res.status(500).send('Server misconfiguration: ADMIN_KEY not set.');
    }

    const { key } = req.query;
    if (!key) return res.status(403).send('Forbidden.');

    let keysMatch = false;
    try {
      const supplied = Buffer.from(key,      'utf8');
      const expected = Buffer.from(adminKey, 'utf8');
      if (supplied.length === expected.length) {
        keysMatch = crypto.timingSafeEqual(supplied, expected);
      }
    } catch {
      keysMatch = false;
    }

    if (!keysMatch) return res.status(403).send('Forbidden.');

    const row = getActiveToken();
    if (!row) {
      return res.status(404).type('text/plain')
        .send('No active, non-expired token found. A new one will rotate soon.');
    }

    const origin = (siteOrigin || 'https://biggboss24hrs.com').replace(/\/$/, '');
    const link   = `${origin}/access?token=${row.token}`;
    return res.type('text/plain').send(link);
  });
}

// ─── Helper: Get time until next 11:30 PM UTC (5:00 AM IST) ────────────────
function getMsUntilNext1130PMUTC() {
  const now = new Date();
  const target = new Date(now.getTime());
  
  target.setUTCHours(23, 30, 0, 0);
  
  if (now.getTime() >= target.getTime()) {
    target.setUTCDate(target.getUTCDate() + 1);
  }
  
  return target.getTime() - now.getTime();
}

// ─── Init ──────────────────────────────────────────────────────────────────
function initAccessTokens(db, app, jwt, IS_PROD, JWT_SECRET, SITE_ORIGIN) {
  _db         = db;
  _jwt        = jwt;
  _jwtSecret  = JWT_SECRET;
  _isProd     = IS_PROD;
  _siteOrigin = SITE_ORIGIN;

  runMigration(db);

  const existing = getActiveToken();
  const msUntilRotation = getMsUntilNext1130PMUTC();

  if (existing) {
    const timeUntilExpiry = existing.expires_at - Date.now();
    if (timeUntilExpiry < msUntilRotation) {
      setTimeout(rotateToken, timeUntilExpiry);
    }
    const expiresLocal = new Date(existing.expires_at).toISOString();
    console.log('[AccessTokens] Existing token valid until ' + expiresLocal);
  } else {
    rotateToken();
  }

  console.log('[AccessTokens] Next daily rotation scheduled in ' + (msUntilRotation / 1000 / 60 / 60).toFixed(2) + ' hours (11:30 PM UTC).');
  setTimeout(() => {
    rotateToken();
    setInterval(rotateToken, TWENTY_FOUR_HOURS_MS);
  }, msUntilRotation);

  registerAccessRoute(app);
  registerAdminRoute(app, SITE_ORIGIN);

  console.log('[AccessTokens] Initialised — /access and /admin/current-link routes registered.');
}

module.exports = {
  initAccessTokens,
  requireAccessSession,
  gateStream,
};
