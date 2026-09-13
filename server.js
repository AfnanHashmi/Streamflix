require('dotenv').config();
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
const { initAccessTokens, requireAccessSession, gateStream } = require('./accessTokens');

const app = express();
const server = http.createServer(app);
const io = new Server(server, {
  cors: {
    origin: process.env.SITE_ORIGIN || 'https://biggboss24hrs.com',
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
  origin: process.env.SITE_ORIGIN || 'https://biggboss24hrs.com',
  credentials: true
}));

// ---------- Access-gated HTML routes (must come BEFORE express.static) ----------
// These intercept requests for the homepage and live page and enforce the
// access_session cookie. Static assets (CSS, JS, images) are still served
// ungated by express.static below so no-access.html can load its own assets.
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
app.use(express.static('/var/www/streamflix'));
// Fallback for our own public folder (e.g., no-access.html)
app.use(express.static('public'));

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

// ---------- Access-token system ----------
// Registers /access, /admin/current-link, and starts the 18h rotation.
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

// Default title if none set yet
const existingTitle = db.prepare('SELECT value FROM stream_meta WHERE key = ?').get('stream_title');
if (!existingTitle) {
  db.prepare('INSERT INTO stream_meta (key, value) VALUES (?, ?)').run('stream_title', 'Live Stream');
}

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
      isAdmin
    },
    JWT_SECRET,
    { expiresIn: '30d' }
  );
}

function setAuthCookie(res, token) {
  res.cookie('streamflix_session', token, {
    httpOnly: true,       // JS on the page can never read this — protects against XSS token theft
    secure: IS_PROD,
    path: '/',     // only sent over HTTPS in production
    sameSite: 'lax',
    maxAge: 30 * 24 * 60 * 60 * 1000
  });
}

function requireAuth(req, res, next) {
  let token = req.cookies.streamflix_session;
  if (!token && req.headers.authorization && req.headers.authorization.startsWith('Bearer ')) {
    token = req.headers.authorization.split(' ')[1];
  }
  if (!token) return res.status(401).json({ error: 'Not logged in' });
  try {
    req.user = jwt.verify(token, JWT_SECRET);
    next();
  } catch {
    res.status(401).json({ error: 'Invalid or expired session' });
  }
}

function requireAdmin(req, res, next) {
  const isAdmin = req.user?.role === 'admin' || !!req.user?.isAdmin;
  if (!isAdmin) return res.status(403).json({ error: 'Admin access required' });
  next();
}

// ---------- Socket.IO Middleware & Events ----------
io.use((socket, next) => {
  try {
    const rawCookies = socket.handshake.headers.cookie;
    if (rawCookies) {
      const parsed = parseCookie(rawCookies);
      if (parsed.streamflix_session) {
        socket.user = jwt.verify(parsed.streamflix_session, JWT_SECRET);
      }
    }
  } catch (err) {
    // Ignore invalid token, socket.user remains undefined
  }
  next();
});

// 3. Socket.io Connection & History Logic
let activeViewers = 0;
let pinnedMessage = null;

io.on('connection', (socket) => {
  activeViewers++;
  io.emit('viewer_count', activeViewers);

  // Send current pinned message state to newly connected client
  socket.emit('update_pinned_message', pinnedMessage);

  socket.on('disconnect', () => {
    activeViewers = Math.max(0, activeViewers - 1);
    io.emit('viewer_count', activeViewers);
  });

  const senderUsername = socket.user?.username || 'User';
  const isSenderAdmin = !!(socket.user?.role === 'admin' || socket.user?.isAdmin);

  // Send the past 24 hours of messages with admin flags to the newly connected user
  try {
    const history = db.prepare(`
      SELECT cm.id, cm.username, cm.message, 
             strftime('%H:%M', cm.created_at, 'localtime') as timestamp,
             CASE WHEN u.role = 'admin' OR u.is_admin = 1 THEN 1 ELSE 0 END as isAdmin
      FROM chat_messages cm
      LEFT JOIN users u ON LOWER(cm.username) = LOWER(u.username)
      WHERE cm.created_at >= datetime('now', '-24 hours')
      ORDER BY cm.id ASC
    `).all();

    socket.emit('chat_history', history);
  } catch (err) {
    console.error('Failed to retrieve chat history:', err);
  }

  // Handle incoming live message
  socket.on('send_message', (data) => {
    if (!data.message || !data.message.trim()) return;
    const cleanMsg = data.message.trim();

    try {
      // Save message into SQLite
      const info = db.prepare(`
        INSERT INTO chat_messages (username, message) 
        VALUES (?, ?)
      `).run(senderUsername, cleanMsg);

      const timestamp = new Date().toLocaleTimeString([], { hour: '2-digit', minute: '2-digit' });

      // Broadcast to ALL connected users
      io.emit('receive_message', {
        id: info.lastInsertRowid,
        username: senderUsername,
        message: cleanMsg,
        timestamp: timestamp,
        isAdmin: isSenderAdmin
      });
    } catch (err) {
      console.error('Failed to save chat message:', err);
    }
  });

  // Handle Pin Message (Admin only)
  socket.on('pin_message', (data) => {
    if (!isSenderAdmin) return;
    if (!data || !data.text || !data.text.trim()) return;

    pinnedMessage = {
      id: String(data.id || Date.now()),
      text: data.text.trim(),
      author: data.author || senderUsername,
      timestamp: data.timestamp || new Date().toLocaleTimeString([], { hour: '2-digit', minute: '2-digit' })
    };

    io.emit('update_pinned_message', pinnedMessage);
  });

  // Handle Unpin Message (Admin only)
  socket.on('unpin_message', () => {
    if (!isSenderAdmin) return;

    pinnedMessage = null;
    io.emit('update_pinned_message', null);
  });

});

// ---------- Auth routes ----------
app.post('/api/signup', async (req, res) => {
  try {
    const { username, email, password } = req.body || {};
    if (!username || !username.trim() || !email || !password || password.length < 8) {
      return res.status(400).json({ error: 'Username, valid email, and password of at least 8 characters are required' });
    }

    const cleanUsername = username.trim();
    const cleanEmail = email.toLowerCase().trim();

    // 1. Block Reserved Usernames (403 Error)
    if (RESERVED_USERNAMES.includes(cleanUsername.toLowerCase())) {
      return res.status(403).json({ error: 'This username is reserved and cannot be registered.' });
    }

    // 2. Check if Username is taken (Case-Insensitive 400 Error)
    const existingUsername = db.prepare('SELECT id FROM users WHERE LOWER(username) = LOWER(?)').get(cleanUsername);
    if (existingUsername) {
      return res.status(400).json({ error: 'Username is already taken. Please choose another.' });
    }

    // 3. Check if Email is taken (409 Error)
    const existingEmail = db.prepare('SELECT id FROM users WHERE LOWER(email) = LOWER(?)').get(cleanEmail);
    if (existingEmail) {
      return res.status(409).json({ error: 'An account with this email already exists' });
    }

    // 4. Role Assignment — all new accounts are standard users
    const role = 'user';
    const isAdmin = 0;

    const hash = await bcrypt.hash(password, 12);

    const info = db.prepare(
      'INSERT INTO users (username, email, password_hash, role, is_admin) VALUES (?, ?, ?, ?, ?)'
    ).run(cleanUsername, cleanEmail, hash, role, isAdmin);

    const user = { id: info.lastInsertRowid, username: cleanUsername, email: cleanEmail, role, is_admin: isAdmin };
    const token = signToken(user);
    setAuthCookie(res, token);
    res.json({ token, username: user.username, email: user.email, role: user.role, isAdmin: !!user.is_admin });
  } catch (err) {
    console.error('Signup Error:', err);
    res.status(500).json({ error: 'Server error during signup' });
  }
});

// Login API
app.post('/api/login', async (req, res) => {
  try {
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
  res.clearCookie('streamflix_session');
  res.json({ ok: true });
});

app.get('/api/me', requireAuth, (req, res) => {
  res.json({ username: req.user.username, email: req.user.email, role: req.user.role || (req.user.isAdmin ? 'admin' : 'user'), isAdmin: !!req.user.isAdmin });
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
    db.prepare(`
      INSERT INTO settings (key, value) VALUES ('stream_title', ?)
      ON CONFLICT(key) DO UPDATE SET value = excluded.value
    `).run(cleanTitle);

    // Broadcast new title in real-time to all connected viewers!
    if (typeof io !== 'undefined') {
      io.emit('stream_title_updated', { title: cleanTitle });
    }

    return res.json({ success: true, title: cleanTitle });
  } catch (err) {
    console.error('Failed to save stream title:', err);
    return res.status(500).json({ error: 'Database update failed' });
  }
});

// GET: Fetch current title on page load
app.get('/api/stream-title', (req, res) => {
  try {
    const row = db.prepare(`SELECT value FROM settings WHERE key = 'stream_title'`).get();
    return res.json({ title: row ? row.value : 'Live Stream' });
  } catch (err) {
    return res.json({ title: 'Live Stream' });
  }
});

// ---------- Library Folders & Videos API ----------

// GET /api/library/folders (Public)
app.get('/api/library/folders', (req, res) => {
  try {
    const folders = db.prepare(`
      SELECT f.id, f.title, f.description, f.thumbnail_url, f.created_at,
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

    const videos = db.prepare('SELECT * FROM library_videos WHERE folder_id = ? ORDER BY id DESC').all(folderId);
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

// DELETE /api/library/videos/:id (Admin only)
app.delete('/api/library/videos/:id', requireAuth, requireAdmin, (req, res) => {
  try {
    const videoId = req.params.id;
    const info = db.prepare('DELETE FROM library_videos WHERE id = ?').run(videoId);
    if (info.changes === 0) return res.status(404).json({ error: 'Video not found' });
    res.json({ success: true });
  } catch (err) {
    console.error('Delete video error:', err);
    res.status(500).json({ error: 'Failed to delete video' });
  }
});

// ---------- Live Polls & Predictions ----------
// Poll state lives in the DB (unlike pinnedMessage, which is in-memory and is
// lost on every restart) so polls and votes survive a restart.

const POLL_MAX_OPTIONS = 10;
const POLL_MAX_QUESTION_LEN = 300;
const POLL_MAX_OPTION_LEN = 100;

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
    question: poll.question,
    status: poll.status,
    created_at: poll.created_at,
    closed_at: poll.closed_at,
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
  const emit = () => io.emit('poll_results', buildPollPayload(pollId, null));

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

// GET /api/polls/active — the currently open poll, if any (public)
app.get('/api/polls/active', (req, res) => {
  try {
    const open = db.prepare(`SELECT id FROM polls WHERE status = 'open' ORDER BY id DESC LIMIT 1`).get();
    if (!open) return res.json({ poll: null });
    res.json({ poll: buildPollPayload(open.id, optionalUserId(req)) });
  } catch (err) {
    console.error('Fetch active poll error:', err);
    res.status(500).json({ error: 'Failed to fetch poll' });
  }
});

// GET /api/polls/history — recent closed polls with final results (public)
app.get('/api/polls/history', (req, res) => {
  try {
    const rows = db.prepare(`SELECT id FROM polls WHERE status = 'closed' ORDER BY id DESC LIMIT 10`).all();
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

    const poll = db.prepare('SELECT * FROM polls WHERE id = ?').get(pollId);
    if (!poll) return res.status(404).json({ error: 'Poll not found' });
    if (poll.status !== 'open') return res.status(409).json({ error: 'This poll is closed' });

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

    // Only one poll is open at a time - opening a new one closes the previous.
    const createPoll = db.transaction(() => {
      db.prepare(`UPDATE polls SET status = 'closed', closed_at = CURRENT_TIMESTAMP WHERE status = 'open'`).run();
      const info = db.prepare('INSERT INTO polls (question, created_by) VALUES (?, ?)').run(cleanQuestion, req.user.username);
      const insertOption = db.prepare('INSERT INTO poll_options (poll_id, label, position) VALUES (?, ?, ?)');
      cleanOptions.forEach((label, i) => insertOption.run(info.lastInsertRowid, label, i));
      return info.lastInsertRowid;
    });

    const pollId = createPoll();
    const payload = buildPollPayload(pollId, null);
    io.emit('poll_started', payload);
    res.json({ success: true, poll: payload });
  } catch (err) {
    console.error('Create poll error:', err);
    res.status(500).json({ error: 'Failed to create poll' });
  }
});

// POST /api/polls/:id/close — stop accepting votes (Admin only)
app.post('/api/polls/:id/close', requireAuth, requireAdmin, (req, res) => {
  try {
    const pollId = Number(req.params.id);
    const info = db.prepare(`UPDATE polls SET status = 'closed', closed_at = CURRENT_TIMESTAMP WHERE id = ? AND status = 'open'`).run(pollId);
    if (info.changes === 0) return res.status(404).json({ error: 'No open poll with that id' });

    const payload = buildPollPayload(pollId, null);
    io.emit('poll_closed', payload);
    res.json({ success: true, poll: payload });
  } catch (err) {
    console.error('Close poll error:', err);
    res.status(500).json({ error: 'Failed to close poll' });
  }
});

// DELETE /api/polls/:id (Admin only)
app.delete('/api/polls/:id', requireAuth, requireAdmin, (req, res) => {
  try {
    const pollId = Number(req.params.id);
    // Children removed explicitly - FK cascade isn't relied on here, matching
    // how the library folder delete is written.
    const removePoll = db.transaction(() => {
      db.prepare('DELETE FROM poll_votes WHERE poll_id = ?').run(pollId);
      db.prepare('DELETE FROM poll_options WHERE poll_id = ?').run(pollId);
      return db.prepare('DELETE FROM polls WHERE id = ?').run(pollId);
    });

    const info = removePoll();
    if (info.changes === 0) return res.status(404).json({ error: 'Poll not found' });

    io.emit('poll_closed', { id: pollId, deleted: true });
    res.json({ success: true });
  } catch (err) {
    console.error('Delete poll error:', err);
    res.status(500).json({ error: 'Failed to delete poll' });
  }
});

// ---------- Clips ----------
// Cuts an MP4 straight out of the OME LLHLS DVR window with `-c copy` (no
// re-encode - measured at ~0.15s CPU / ~0.6s wall per 30s clip on this box).
// No watermark, no DB row, no retention: the 2h DVR window is already the
// archive, so keeping a saved copy would just duplicate data we already have.
// The file lives just long enough to stream to the requester, then it's gone.
const CLIP_TMP_DIR = '/tmp/streamflix-clips';
const CLIP_ORIGIN = 'http://127.0.0.1:3333/app';
const CLIP_STREAM_NAME = 'stream';
const CLIP_MAX_DURATION_SEC = 30;
const CLIP_MAX_CONCURRENT = 8;
const CLIP_MAX_QUEUE_DEPTH = 30;
// Clips vary 13x in size (a 360p preview vs a 30s 1080p download), so a
// request-count limit is a poor proxy for cost - it either starves cheap
// previews or, as happened when quality was raised from 720p to 1080p,
// silently becomes far more permissive without anyone changing the number.
// Budgeting by bytes actually served lets a user make many cheap previews OR
// a few full-quality downloads, whichever they need.
const CLIP_BYTE_BUDGET_WINDOW_MS = 15 * 60 * 1000;
const CLIP_BYTE_BUDGET_MAX_BYTES = 150 * 1024 * 1024; // ~10 full 1080p clips, or ~120 preview-quality ones, per 15 min

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
async function getClipSourceChunklists(quality) {
  const masterUrl = `${CLIP_ORIGIN}/${CLIP_STREAM_NAME}/llhls.m3u8`;
  const res = await fetch(masterUrl);
  if (!res.ok) throw new Error(`Master manifest fetch failed: ${res.status}`);
  const text = await res.text();
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
    videoChunklist = renditions.reduce((a, b) =>
      Math.abs(b.height - 720) < Math.abs(a.height - 720) ? b : a
    ).uri;
  } else {
    videoChunklist = renditions.reduce((a, b) => (b.height > a.height ? b : a)).uri;
  }

  if (!videoChunklist || !audioChunklist) {
    throw new Error('Could not locate video/audio chunklists in master manifest');
  }

  return {
    videoChunklistUrl: `${CLIP_ORIGIN}/${CLIP_STREAM_NAME}/${videoChunklist}`,
    audioChunklistUrl: `${CLIP_ORIGIN}/${CLIP_STREAM_NAME}/${audioChunklist}`
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
async function cutAndStreamClip(req, res, { startMs, durationSec, quality, onProduced }) {
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
    const { videoChunklistUrl, audioChunklistUrl } = await getClipSourceChunklists(quality);
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

app.post('/api/clips', requireAuth, async (req, res) => {
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

function clipSignature(startSec, durationSec, quality) {
  return crypto.createHmac('sha256', process.env.CLIP_SIGNING_SECRET)
    .update(`${startSec}|${durationSec}|${quality}`)
    .digest('hex')
    .slice(0, 24);
}

app.post('/api/clips/sign', requireAuth, (req, res) => {
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
  const sig = clipSignature(startSec, durationSec, quality);

  // Charged here at an estimate, not after the fact: whether this URL turns
  // into an origin cut at all depends on cache state we don't control, so
  // there is no "actual bytes produced" moment to hook for a GET request that
  // might be answered entirely from Cloudflare's edge.
  const ESTIMATED_BYTES_PER_SEC = { preview: 40000, '720p': 125000, '1080p': 520000 };
  clipRecordBytes(userId, durationSec * (ESTIMATED_BYTES_PER_SEC[quality] || ESTIMATED_BYTES_PER_SEC['1080p']));

  res.json({ url: `/api/clips/${startSec}/${durationSec}/${quality}/${sig}.mp4` });
});

app.get('/api/clips/:startSec/:durationSec/:quality/:sig.mp4', async (req, res) => {
  const startSec = Number(req.params.startSec);
  const durationSec = Number(req.params.durationSec);
  const quality = req.params.quality;

  if (!Number.isInteger(startSec) || startSec < 0
      || !Number.isInteger(durationSec) || durationSec <= 0 || durationSec > CLIP_MAX_DURATION_SEC
      || !CLIP_ALLOWED_QUALITIES.has(quality)) {
    return res.status(400).json({ error: 'Invalid clip parameters' });
  }

  const expectedSig = clipSignature(startSec, durationSec, quality);
  const providedSig = String(req.params.sig || '');
  const expectedBuf = Buffer.from(expectedSig);
  const providedBuf = Buffer.from(providedSig);
  const validSig = expectedBuf.length === providedBuf.length
    && crypto.timingSafeEqual(expectedBuf, providedBuf);
  if (!validSig) {
    return res.status(403).json({ error: 'Invalid or expired clip link' });
  }

  await cutAndStreamClip(req, res, { startMs: startSec * 1000, durationSec, quality });
});

server.listen(PORT, () => console.log(`Auth server running on port ${PORT}`));