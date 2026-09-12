# Streamflix Auth Server

## Testing locally in VS Code (do this first)

### 1. Open the folder
Open the `auth-server` folder in VS Code (File → Open Folder).

### 2. Install dependencies
In VS Code's built-in terminal (`` Ctrl+` ``):
```
npm install
```

### 3. Create your local .env file
```
cp .env.example .env
```
(On Windows PowerShell, use `copy .env.example .env` instead)

Open `.env` and set:
```
JWT_SECRET=any-random-string-for-now-change-before-real-deploy
NODE_ENV=development
PORT=4000
SITE_ORIGIN=http://localhost:4000
```

You don't need a "real" secure secret for local testing — just something non-empty.
Generate a proper one later before deploying: `openssl rand -base64 48`

### 4. Run the server
```
npm start
```
You should see: `Auth server running on port 4000`

### 5. Open it in your browser
The server also serves your HTML pages directly for local testing, so everything
runs on one origin (avoids CORS/cookie headaches):

- http://localhost:4000/signup.html — create your first account (becomes admin automatically)
- http://localhost:4000/login.html — log in
- http://localhost:4000/live.html — after logging in as admin, refresh this page —
  you should see the pencil/edit icon next to the title now

### 6. What to actually test
- Sign up with a test email/password → should redirect to live.html
- Refresh live.html → edit pencil should be visible (you're admin)
- Click the pencil, change the title, hit Enter → should save and persist on refresh
- Open live.html in an Incognito/Private window (no login) → edit pencil should be
  gone, but the title you set should still show (public read works)
- Try logging in with a wrong password → should show a clean error, not crash
- Try signing up with an email that already exists → should show "already exists" error

### 7. Resetting your local test data
The database is a single file, `streamflix.db`, created automatically in this folder.
Delete it anytime to start fresh (next signup becomes admin again):
```
rm streamflix.db
```
(Windows: `del streamflix.db`)

---

## Deploying to your VPS (do this once local testing looks good)

### 1. Upload this folder to your VPS
```
scp -r auth-server root@5.223.72.33:/root/auth-server
```

### 2. Install dependencies on the VPS
```
cd /root/auth-server
npm install
```

### 3. Set up the real .env
```
cp .env.example .env
nano .env
```
Generate a real secret: `openssl rand -base64 48` — paste into `JWT_SECRET=`.
Set `NODE_ENV=production` and `SITE_ORIGIN=https://biggboss24hrs.com`.

### 4. Run it permanently with PM2
```
npm install -g pm2
pm2 start server.js --name streamflix-auth
pm2 save
pm2 startup
```
(Run whatever command `pm2 startup` prints out.)

### 5. Add an Nginx route for /api/*
Edit your existing Nginx site config:
```
location /api/ {
    proxy_pass http://localhost:4000;
    proxy_http_version 1.1;
    proxy_set_header Host $host;
    proxy_set_header X-Real-IP $remote_addr;
    proxy_cookie_path / /;
}
```
Then:
```
nginx -t
systemctl reload nginx
```

### 6. Copy login.html and signup.html to your real site folder
Copy both from this folder's `public/` directory into wherever your actual site
files live on the VPS (alongside `index.html` and the `live/` folder), so they're
reachable at `/login.html` and `/signup.html` on your real domain.

**Note:** the `live.html` and `index.html` inside this project's `public/` folder
are just local testing copies — don't copy those over your real deployed versions,
since your real site already has its own `live/index.html` in the folder structure
you set up earlier.

### 7. Create your real admin account
Visit `https://biggboss24hrs.com/signup.html` and sign up once for real — that
account becomes admin automatically. To promote a different account later:
```
cd /root/auth-server
sqlite3 streamflix.db "UPDATE users SET is_admin = 1 WHERE email = 'someone@example.com';"
```

## What's still worth doing later
- Move from SQLite to Postgres once you have real user volume
- Add email verification / password reset
- Add rate limiting on /api/login to slow brute-force attempts
