'use strict';
// OmniMind: ОДИН файл = сервер + сайт. Запуск: ADMIN_EMAIL=... ADMIN_PASSWORD=... node server.js  (Node >= 22.5)
const http=require('http'),fs=require('fs'),path=require('path'),crypto=require('crypto'),os=require('os');
const {DatabaseSync}=require('node:sqlite');
const E=process.env;
const PORT=+E.PORT||3000, AI_URL=E.AI_URL||'https://text.pollinations.ai/openai', AI_KEY=E.AI_KEY||'';
const FREE=+E.FREE_LIMIT||10, MAXC=+E.MAX_CONCURRENT||50, MAXQ=+E.MAX_QUEUE||500;
const USER_RPM=+E.USER_RPM||20, REG_RPM=+E.REG_PER_MIN||10, LOGIN_RPM=+E.LOGIN_PER_MIN||20;
const ADMIN=(E.ADMIN_EMAIL||'').trim().toLowerCase(), TRUST=E.TRUST_PROXY==='1';
const PUB=path.join(__dirname,'public');
const db=new DatabaseSync(E.DB_PATH||path.join(__dirname,'omnimind.db'));
db.exec(`PRAGMA journal_mode=WAL;PRAGMA busy_timeout=5000;
CREATE TABLE IF NOT EXISTS users(id INTEGER PRIMARY KEY,email TEXT UNIQUE,salt TEXT,hash TEXT,premium INT DEFAULT 0,blocked INT DEFAULT 0,created INT,seen INT DEFAULT 0);
CREATE TABLE IF NOT EXISTS sessions(t TEXT PRIMARY KEY,uid INT,exp INT);
CREATE TABLE IF NOT EXISTS chats(uid INT PRIMARY KEY,data TEXT,upd INT);
CREATE TABLE IF NOT EXISTS usage(uid INT,day TEXT,n INT,PRIMARY KEY(uid,day));
CREATE TABLE IF NOT EXISTS stats(day TEXT PRIMARY KEY,req INT DEFAULT 0,err INT DEFAULT 0);
CREATE TABLE IF NOT EXISTS errs(ts INT,msg TEXT);`);
const cache=new Map(),q=s=>{let p=cache.get(s);if(!p){p=db.prepare(s);cache.set(s,p)}return p};
const day=()=>new Date().toISOString().slice(0,10), now=()=>Date.now();
const sha=s=>crypto.createHash('sha256').update(s).digest('hex');
const scrypt=(p,s)=>new Promise((r,j)=>crypto.scrypt(p,s,32,(e,k)=>e?j(e):r(k)));
const bump=c=>{q('INSERT INTO stats(day,'+c+')VALUES(?,1)ON CONFLICT(day)DO UPDATE SET '+c+'='+c+'+1').run(day())};
const logErr=m=>{try{q('INSERT INTO errs VALUES(?,?)').run(now(),String(m).slice(0,300));bump('err');q('DELETE FROM errs WHERE ts<?').run(now()-7*864e5)}catch(e){}};

// Admin account is created from env, never via public registration (prevents email squatting).
(async()=>{if(ADMIN&&E.ADMIN_PASSWORD&&!q('SELECT 1 FROM users WHERE email=?').get(ADMIN)){
 const salt=crypto.randomBytes(16).toString('hex');
 q('INSERT INTO users(email,salt,hash,premium,created)VALUES(?,?,?,1,?)').run(ADMIN,salt,(await scrypt(E.ADMIN_PASSWORD,salt)).toString('hex'),now());console.log('admin created')}})();

// fixed-window rate limiter
const buckets=new Map();
const hit=(k,max,ms)=>{const t=now();let b=buckets.get(k);if(!b||b[1]<t){b=[0,t+ms];buckets.set(k,b)}return++b[0]<=max};
setInterval(()=>{const t=now();for(const[k,b]of buckets)if(b[1]<t)buckets.delete(k)},60000).unref();

// global concurrency limiter + bounded queue (overload protection)
let active=0;const waitq=[];
const acquire=()=>new Promise((ok,no)=>{if(active<MAXC){active++;return ok()}if(waitq.length>=MAXQ)return no(new Error('busy'));waitq.push(ok)});
const release=()=>{const n=waitq.shift();if(n)n();else active--};

const json=(res,c,o,h)=>{if(res.headersSent)return;res.writeHead(c,{'content-type':'application/json','cache-control':'no-store',...h});res.end(JSON.stringify(o))};
const readBody=(req,max)=>new Promise((ok,no)=>{let n=0;const a=[];req.on('data',d=>{n+=d.length;if(n>max){no(new Error('big'));req.destroy()}else a.push(d)});req.on('end',()=>ok(Buffer.concat(a).toString()));req.on('error',no)});
const ipOf=req=>TRUST&&req.headers['x-forwarded-for']?req.headers['x-forwarded-for'].split(',')[0].trim():req.socket.remoteAddress;
const cookie=(req,n)=>((req.headers.cookie||'').match(new RegExp('(?:^|; )'+n+'=([^;]+)'))||[])[1];
const secure=req=>E.COOKIE_SECURE==='1'||req.headers['x-forwarded-proto']==='https';
function authUser(req){const t=cookie(req,'sid');if(!t)return null;
 const u=q('SELECT u.*FROM sessions s JOIN users u ON u.id=s.uid WHERE s.t=? AND s.exp>?').get(sha(t),now());
 if(!u||u.blocked)return null;if(u.seen<now()-60000)q('UPDATE users SET seen=? WHERE id=?').run(now(),u.id);return u}
const used=u=>(q('SELECT n FROM usage WHERE uid=? AND day=?').get(u.id,day())||{n:0}).n;
const pub=u=>({email:u.email,premium:!!u.premium,admin:!!ADMIN&&u.email===ADMIN,used:used(u),limit:FREE});
async function session(req,res,u){const t=crypto.randomBytes(32).toString('hex');
 q('INSERT INTO sessions VALUES(?,?,?)').run(sha(t),u.id,now()+30*864e5);
 json(res,200,pub(u),{'set-cookie':`sid=${t}; HttpOnly; SameSite=Lax; Path=/; Max-Age=2592000${secure(req)?'; Secure':''}`})}

async function authRoute(req,res,kind){
 const ip=ipOf(req);if(!hit((kind==='register'?'r':'l')+ip,kind==='register'?REG_RPM:LOGIN_RPM,60000))return json(res,429,{error:'Слишком много попыток, подождите минуту'});
 let b;try{b=JSON.parse(await readBody(req,5000))}catch(e){return json(res,400,{error:'Некорректный запрос'})}
 const email=String(b.email||'').trim().toLowerCase(),pw=String(b.password||'');
 if(!/^\S+@\S+\.\S+$/.test(email)||email.length>120)return json(res,400,{error:'Неверный email'});
 if(pw.length<6||pw.length>200)return json(res,400,{error:'Пароль: от 6 символов'});
 if(kind==='register'){
  if(q('SELECT 1 FROM users WHERE email=?').get(email))return json(res,409,{error:'Такой email уже есть'});
  const salt=crypto.randomBytes(16).toString('hex');
  const r=q('INSERT INTO users(email,salt,hash,created)VALUES(?,?,?,?)').run(email,salt,(await scrypt(pw,salt)).toString('hex'),now());
  return session(req,res,q('SELECT*FROM users WHERE id=?').get(r.lastInsertRowid))}
 const u=q('SELECT*FROM users WHERE email=?').get(email);
 const h=await scrypt(pw,u?u.salt:'0'.repeat(32));
 if(!u||!crypto.timingSafeEqual(h,Buffer.from(u.hash,'hex')))return json(res,401,{error:'Неверный email или пароль'});
 if(u.blocked)return json(res,403,{error:'Аккаунт заблокирован'});
 return session(req,res,u)}

async function chat(req,res,u){
 if(!hit('c'+u.id,USER_RPM,60000))return json(res,429,{error:'Слишком часто. Подождите немного'});
 let b;try{b=JSON.parse(await readBody(req,3e6))}catch(e){return json(res,400,{error:'Некорректный запрос'})}
 const model=String(b.model||'');
 if(!/^[\w.\-]{1,40}$/.test(model)||!Array.isArray(b.messages)||!b.messages.length||b.messages.length>20)return json(res,400,{error:'Некорректный запрос'});
 const messages=b.messages.map(m=>({role:['system','user','assistant'].includes(m.role)?m.role:'user',content:typeof m.content==='string'?m.content.slice(0,20000):Array.isArray(m.content)?m.content.slice(0,4):''}));
 if(!u.premium&&!/^openai/i.test(model))return json(res,403,{error:'Эта модель доступна в Premium'});
 if(!u.premium&&used(u)>=FREE)return json(res,402,{error:'Дневной лимит исчерпан'});
 try{await acquire()}catch(e){return json(res,503,{error:'Сервер перегружен, повторите позже'},{'retry-after':'10'})}
 const ac=new AbortController();let first=false;res.on('close',()=>ac.abort());
 const tm=setTimeout(()=>ac.abort(),25000);
 try{
  bump('req');
  const up=await fetch(AI_URL,{method:'POST',signal:ac.signal,headers:{'content-type':'application/json',...(AI_KEY?{authorization:'Bearer '+AI_KEY}:{})},body:JSON.stringify({model,messages,stream:true})});
  if(!up.ok)throw new Error('upstream '+up.status);
  res.writeHead(200,{'content-type':up.headers.get('content-type')||'text/event-stream','cache-control':'no-store','x-accel-buffering':'no'});
  for await(const ch of up.body){if(!first){first=true;clearTimeout(tm);q('INSERT INTO usage VALUES(?,?,1)ON CONFLICT(uid,day)DO UPDATE SET n=n+1').run(u.id,day())}res.write(ch)}
  res.end();
 }catch(e){if(!res.writableEnded&&!ac.signal.aborted||!first&&ac.signal.aborted&&res.writable)logErr('chat: '+e.message);
  if(!res.headersSent)json(res,502,{error:'ИИ-сервер не ответил'});else res.end()}
 finally{clearTimeout(tm);release()}}

function adminStats(){const d=q('SELECT*FROM stats WHERE day=?').get(day())||{req:0,err:0};
 return{users:q('SELECT COUNT(*)c FROM users').get().c,active15m:q('SELECT COUNT(*)c FROM users WHERE seen>?').get(now()-9e5).c,
 requestsToday:d.req,errorsToday:d.err,requestsTotal:q('SELECT COALESCE(SUM(req),0)c FROM stats').get().c,
 activeStreams:active,queued:waitq.length,maxConcurrent:MAXC,rssMB:Math.round(process.memoryUsage().rss/1048576),load1:os.loadavg()[0],uptimeSec:Math.round(process.uptime()),
 lastErrors:q('SELECT ts,msg FROM errs ORDER BY ts DESC LIMIT 20').all(),
 days:q('SELECT*FROM stats ORDER BY day DESC LIMIT 14').all()}}

// ===== Сайт целиком встроен в этот файл (чат + админ-панель) =====
const PAGES={
index:`<!doctype html>
<html lang="ru">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1,viewport-fit=cover">
<title>OmniMind — бесплатный ИИ-чат с фото: решает задачи, пишет код</title>
<meta name="description" content="OmniMind — бесплатный ИИ-чат без ключей. Решает примеры по фото, пишет код, тексты и переводы. Несколько нейросетей, режим сравнения, Premium.">
<meta name="robots" content="index,follow">
<link rel="canonical" href="https://morozmaxim607-tech.github.io/omnimind/">
<meta property="og:type" content="website">
<meta property="og:title" content="OmniMind — ИИ-чат, который решает задачи по фото">
<meta property="og:description" content="Бесплатный ИИ без ключей: код, математика по фото, тексты, переводы.">
<meta property="og:url" content="https://morozmaxim607-tech.github.io/omnimind/">
<script type="application/ld+json">{"@context":"https://schema.org","@type":"WebApplication","name":"OmniMind","url":"https://morozmaxim607-tech.github.io/omnimind/","applicationCategory":"UtilitiesApplication","operatingSystem":"Any","description":"Бесплатный ИИ-чат: решает задачи по фото, пишет код и тексты.","offers":{"@type":"Offer","price":"0","priceCurrency":"USD"}}</script>
<style>
:root{--pk:#ff7ac6;--cy:#7df3ff;--lv:#b08cff;--tx:#fff;--mut:#c9b8f0;--gl:rgba(255,255,255,.09);--ln:rgba(255,255,255,.18)}
*{box-sizing:border-box;-webkit-tap-highlight-color:transparent}
html,body{height:100%;margin:0}
body{color:var(--tx);font:16px/1.5 system-ui,-apple-system,sans-serif;background:radial-gradient(circle at 15% 10%,#6b2d9c55,transparent 45%),radial-gradient(circle at 90% 90%,#ff7ac644,transparent 40%),linear-gradient(160deg,#1a1033,#261552 60%,#1b1240);overflow:hidden}
button,select,textarea,input{font:inherit;color:var(--tx);background:var(--gl);border:1px solid var(--ln);border-radius:14px;padding:9px 13px}
button{cursor:pointer}option{color:#000}
.p{background:linear-gradient(90deg,var(--pk),var(--lv));border:0;font-weight:700;box-shadow:0 0 16px #ff7ac655}
#app{display:flex;height:100dvh}
#side{width:280px;flex:none;display:flex;flex-direction:column;gap:10px;padding:14px;background:#140b2df0;border-right:1px solid var(--ln)}
.brand{font-weight:800;font-size:22px;background:linear-gradient(90deg,var(--pk),var(--cy));-webkit-background-clip:text;color:transparent}
#list{flex:1;overflow-y:auto;display:flex;flex-direction:column;gap:4px}
.it{display:flex;align-items:center;gap:6px;padding:9px 11px;border-radius:12px;cursor:pointer;color:var(--mut);font-size:15px}
.it span{flex:1;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}.it:hover,.it.on{background:var(--gl);color:#fff}
.it b{opacity:.6;font-weight:400;padding:0 4px}
.foot{display:flex;flex-direction:column;gap:8px;border-top:1px solid var(--ln);padding-top:10px}
#who{font-size:14px;color:var(--mut);overflow:hidden;text-overflow:ellipsis}
#main{flex:1;min-width:0;display:flex;flex-direction:column;height:100dvh}
.top{display:flex;gap:8px;padding:10px 12px;padding-top:max(10px,env(safe-area-inset-top));align-items:center}
.top select{flex:1;min-width:0}#bMenu{display:none}
#chat{flex:1;overflow-y:auto;padding:8px 14px;display:flex;flex-direction:column;gap:14px;max-width:860px;width:100%;margin:0 auto}
.m{max-width:88%;padding:11px 15px;border-radius:18px;white-space:pre-wrap;word-wrap:break-word}
.u{align-self:flex-end;background:linear-gradient(135deg,var(--pk),var(--lv));border-bottom-right-radius:6px}
.a{align-self:flex-start;background:var(--gl);border:1px solid var(--ln);border-bottom-left-radius:6px}
.a small{display:block;color:var(--cy);font-weight:700;margin-bottom:3px}.err{border-color:#ff6b8a}
.m img{max-width:100%;max-height:260px;border-radius:12px;display:block;margin-bottom:6px}
pre{background:#0c0720;padding:10px;border-radius:10px;overflow-x:auto;margin:6px 0}code{background:#0c072099;padding:1px 5px;border-radius:5px}pre code{background:none;padding:0}
.hero{margin:auto;text-align:center;padding:20px;max-width:520px}
.hero .ms{font-size:64px;filter:drop-shadow(0 0 18px var(--pk))}
.hero h1{margin:4px 0;font-size:34px;background:linear-gradient(90deg,var(--pk),var(--cy));-webkit-background-clip:text;color:transparent}
.hero p{color:var(--mut)}.chips{display:flex;flex-wrap:wrap;gap:8px;justify-content:center;margin-top:12px}.chips button{font-size:14px}
#st{text-align:center;color:var(--cy);font-size:14px;min-height:18px}
#pv{max-width:860px;width:100%;margin:0 auto;padding:0 14px}#pv img{height:64px;border-radius:10px;border:2px solid var(--pk)}#pv button{padding:2px 9px;margin-left:6px}
.in{display:flex;gap:8px;max-width:860px;width:100%;margin:0 auto;padding:6px 14px;padding-bottom:max(12px,env(safe-area-inset-bottom));align-items:flex-end}
.in textarea{flex:1;resize:none;height:50px;max-height:140px;border-radius:22px}
.in label,.in button{height:50px;min-width:50px;display:flex;align-items:center;justify-content:center;border-radius:50%;padding:0;cursor:pointer;background:var(--gl);border:1px solid var(--ln)}
.in .p{border:0;background:linear-gradient(135deg,var(--pk),var(--lv))}
dialog{background:#241447;color:#fff;border:1px solid var(--ln);border-radius:20px;max-width:380px;width:92%;box-shadow:0 0 40px #ff7ac655}
dialog::backdrop{background:#000b}dialog input{width:100%;margin:6px 0}dialog h3{margin:0 0 8px}
.row{display:flex;gap:8px;margin:8px 0}.row>*{flex:1}.mut{color:var(--mut);font-size:14px}
#shade{display:none}
@media(max-width:760px){
 #side{position:fixed;z-index:20;left:0;top:0;bottom:0;transform:translateX(-102%);transition:.25s;width:82%;max-width:320px}
 #side.open{transform:none}#side.open+#shade{display:block;position:fixed;inset:0;background:#0009;z-index:15}
 #bMenu{display:block}.m{max-width:94%}}
#srch{width:100%;border-radius:12px;padding:8px 12px;font-size:14px}
.tabs{display:flex;gap:6px}.tabs button{flex:1;padding:6px;font-size:13px;border-radius:10px}.tabs .on{background:linear-gradient(90deg,var(--pk),var(--lv));border:0;font-weight:700}
.gr{font-size:11px;letter-spacing:.06em;text-transform:uppercase;color:var(--mut);opacity:.7;padding:8px 6px 2px}
.it{min-height:40px;transition:background .15s}.it b{cursor:pointer;border-radius:8px;padding:2px 5px;opacity:.55}.it b:hover{opacity:1;background:#fff2}
.prof{display:flex;align-items:center;gap:8px;text-align:left;width:100%}.prof span{overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.foot .row{margin:0}.foot a{text-align:center;color:var(--cy);text-decoration:none;font-size:14px}
#side{transition:transform .28s cubic-bezier(.4,0,.2,1)}
[hidden]{display:none!important}
#side{background:#0f0a1f;padding:10px;gap:4px;border-right:1px solid #ffffff0f}
.sh{display:flex;align-items:center;justify-content:space-between;padding:4px 6px 10px}
.ib{padding:4px 10px;border-radius:10px;background:transparent;border:0;font-size:18px;color:var(--mut)}.ib:hover{background:#ffffff12}
.nav{display:flex;align-items:center;gap:10px;width:100%;text-align:left;background:transparent;border:0;border-radius:10px;padding:9px 10px;color:#e8defc}
.nav:hover,.nav.on{background:#ffffff12}.nav i,.srch i{font-style:normal;width:20px;text-align:center}
#nc{border:1px solid #ff7ac655;background:linear-gradient(90deg,#ff7ac620,#b08cff20);font-weight:600}
.srch{display:flex;align-items:center;gap:10px;padding:0 10px;border-radius:10px;background:#ffffff0d;margin:2px 0}
.srch input{flex:1;border:0;background:transparent;padding:9px 0;border-radius:0;min-width:0;font-size:14px}.srch input:focus{outline:0}
.it{position:relative;border-radius:10px;padding:8px 10px}.it.on{background:#ffffff14;box-shadow:inset 3px 0 0 var(--pk)}
.it .dots{opacity:0;padding:0 6px;font-size:18px;line-height:1}.it:hover .dots,.it.on .dots{opacity:.85}@media(hover:none){.it .dots{opacity:.7}}
.foot{border-top:1px solid #ffffff12;position:relative;padding-top:8px;gap:0}
.prof{display:flex;align-items:center;gap:10px;width:100%;background:transparent;border:0;border-radius:12px;padding:8px;text-align:left}.prof:hover{background:#ffffff12}
.av{width:32px;height:32px;border-radius:50%;background:linear-gradient(135deg,var(--pk),var(--lv));display:flex;align-items:center;justify-content:center;font-weight:700;flex:none}
.prof span{flex:1;font-size:14px;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.pm{position:absolute;z-index:40;min-width:190px;background:#1d1238;border:1px solid var(--ln);border-radius:14px;padding:6px;box-shadow:0 12px 40px #000a}
.foot .pm{left:0;right:0;bottom:58px}#cm{position:fixed}
.pm button,.pm a{display:block;width:100%;text-align:left;background:transparent;border:0;border-radius:9px;padding:9px 10px;color:#fff;text-decoration:none;font-size:14px}.pm button:hover,.pm a:hover{background:#ffffff14}.pm .dng{color:#ff8fa8}
@media(min-width:761px){#side{width:268px;transition:width .25s,padding .25s}.side-c #side{width:0;padding:0;overflow:hidden;border:0}.side-c #bMenu{display:block}}
</style>
</head>
<body>
<div id="app">
 <aside id="side">
  <div class="sh"><div class="brand">🌸 OmniMind</div><button id="bCol" class="ib" title="Свернуть меню">«</button></div>
  <button id="nc" class="nav"><i>＋</i><span>Новый чат</span></button>
  <div class="srch"><i>🔎</i><input id="srch" type="search" placeholder="Поиск по чатам" autocomplete="off"></div>
  <button id="tFav" class="nav"><i>☆</i><span>Избранные чаты</span></button>
  <div id="list"></div>
  <div class="foot">
   <div id="pm" class="pm" hidden><button id="mProf">👤 Профиль</button><button id="bSet">⚙ Настройки</button><button id="bPrem">★ Premium</button><a id="bAdm" href="/admin.html" hidden>🛠 Админ-панель</a><button id="bAuth">Войти</button></div>
   <button id="bProf" class="prof"><b class="av" id="av">?</b><span id="who"></span><i style="font-style:normal">⋯</i></button>
  </div>
 </aside>
 <div id="shade"></div>
 <div id="cm" class="pm" hidden><button data-a="fav">☆ В избранное</button><button data-a="ren">✎ Переименовать</button><button data-a="del" class="dng">🗑 Удалить</button></div>
 <section id="main">
  <div class="top">
   <button id="bMenu">☰</button>
   <select id="model"></select>
   <select id="mode">
    <option value="chat">💬 Чат</option><option value="math">🧮 Решатель задач</option><option value="code">👨‍💻 Программист</option>
    <option value="write">✍️ Писатель</option><option value="tr">🌍 Переводчик</option><option value="cmp">⚖️ Сравнить 3 ИИ ★</option>
   </select>
  </div>
  <div id="chat"></div>
  <div id="st"></div>
  <div id="pv"></div>
  <div class="in">
   <label for="file" title="Добавить фото">📎</label><input type="file" id="file" accept="image/*" hidden>
   <textarea id="q" placeholder="Напишите сообщение или добавьте фото задачи…"></textarea>
   <button id="bSend" class="p">➤</button>
  </div>
 </section>
</div>

<dialog id="dAuth"><h3 id="aT">Вход</h3>
 <input id="em" type="email" placeholder="Email" autocomplete="email" autocapitalize="off" autocorrect="off">
 <input id="pw" type="password" placeholder="Пароль (от 6 символов)" autocomplete="current-password">
 <div class="row"><button class="p" id="aOk">Войти</button><button id="aSw">Регистрация</button></div>
 <p class="mut" id="aE"></p><button onclick="dAuth.close()" style="width:100%">Закрыть</button></dialog>

<dialog id="dPrem"><h3>★ Premium</h3>
 <p class="mut">Все нейросети, сравнение 3 ИИ сразу, без лимита сообщений. Premium включает администратор OmniMind — напишите владельцу сервиса.</p>
 <div id="admBox" hidden><p class="mut">Вы админ. Выдать или снять Premium любому пользователю:</p><input id="pEm" type="email" placeholder="Email пользователя" autocapitalize="off" autocorrect="off"><div class="row"><button class="p" id="pGive">Выдать</button><button id="pTake">Снять</button></div></div>
 <p class="mut" id="pE"></p><button onclick="dPrem.close()" style="width:100%">Закрыть</button></dialog>

<dialog id="dProf"><h3>👤 Профиль</h3>
 <p class="mut">Email: <b id="pfE"></b><br>Тариф: <b id="pfP"></b><br>Использовано сегодня: <b id="pfU"></b><br>Чатов: <b id="pfN"></b></p>
 <button onclick="dProf.close()" style="width:100%">Закрыть</button></dialog>
<dialog id="dSet"><h3>⚙ Настройки</h3>
 <p class="mut">Режим по умолчанию при открытии сайта</p>
 <select id="sMode" style="width:100%"><option value="chat">💬 Чат</option><option value="math">🧮 Решатель задач</option><option value="code">👨‍💻 Программист</option><option value="write">✍️ Писатель</option><option value="tr">🌍 Переводчик</option></select>
 <div class="row"><button id="sClr">🗑 Удалить все чаты</button></div>
 <button onclick="dSet.close()" style="width:100%">Закрыть</button></dialog>
<noscript>OmniMind — бесплатный ИИ-чат: несколько нейросетей, решение задач по фото, код, тексты и переводы. Включите JavaScript.</noscript>

<script>
const FREE_LIMIT=10;
const SYS={chat:"Ты OmniMind — умный, дружелюбный ИИ-ассистент. Отвечай на языке пользователя, чётко и кратко.",
math:"Ты репетитор по математике, физике и другим наукам. Если на фото задача — прочитай её и реши по шагам, в конце напиши ответ. Формулы пиши простым текстом (без LaTeX).",
code:"Ты эксперт-программист уровня senior. Пиши рабочий код в блоках \`\`\`, объясняй кратко, указывай подводные камни.",
write:"Ты талантливый писатель и редактор. Пиши живо, грамотно и красиво.",
tr:"Ты профессиональный переводчик. Переводи точно, сохраняя стиль; если язык не указан — между русским и английским."};
let models=[{n:"GPT",id:"openai"},{n:"Mistral",id:"mistral"},{n:"Llama",id:"llama"},{n:"DeepSeek",id:"deepseek"},{n:"Claude",id:"claude"},{n:"Gemini",id:"gemini"}];
const $=s=>document.querySelector(s);
const L=(k,d)=>{try{return JSON.parse(localStorage.getItem(k))??d}catch(e){return d}};
const S=(k,v)=>{try{localStorage.setItem(k,JSON.stringify(v))}catch(e){}};
const esc=s=>String(s).replace(/[&<>]/g,c=>({"&":"&amp;","<":"&lt;",">":"&gt;"}[c]));
const fmt=t=>esc(t).replace(/\`\`\`\\w*\\n?([\\s\\S]*?)\`\`\`/g,"<pre><code>$1</code></pre>").replace(/\`([^\`\\n]+)\`/g,"<code>$1</code>").replace(/\\*\\*([^*\\n]+)\\*\\*/g,"<b>$1</b>");
const norm=s=>String(s).trim().toLowerCase();
let ME=null;const cur=()=>ME&&ME.email,isPrem=()=>!!(ME&&ME.premium);
const api=(p,o={})=>fetch("/api/"+p,{...o,headers:{"Content-Type":"application/json","X-Requested-With":"om",...(o.headers||{})}});
const day=()=>new Date().toISOString().slice(0,10);
const cnt=()=>ME?ME.used:0;
let authMode="in",chats=[],cid=null,img=null,busy=false;
const cc=()=>chats.find(c=>c.id===cid);
async function load(){try{const r=await api("me");ME=r.ok?await r.json():null;if(ME){const c=await api("chats");chats=c.ok?await c.json():[]}else chats=[]}catch(e){ME=null;chats=[]}cid=chats[0]?chats[0].id:null;ui()}
let svT=0;function save(){if(!cur())return;clearTimeout(svT);svT=setTimeout(()=>api("chats",{method:"PUT",body:JSON.stringify(chats.slice(0,40).map(c=>({...c,msgs:c.msgs.slice(-60).map(m=>m.img?{...m,img:null,hadImg:1}:m)})))}).catch(()=>{}),400)}
function newChat(){const c={id:Date.now(),title:"Новый чат",msgs:[]};chats.unshift(c);cid=c.id;return c}

function ui(){
 const u=cur(),pr=isPrem();
 $("#who").textContent=u?(pr?"★ ":"")+u:"Вы не вошли";$("#av").textContent=u?u[0].toUpperCase():"?";
 $("#bAuth").textContent=u?"Выйти":"Войти";$("#bAdm").hidden=!(ME&&ME.admin);
 $("#bPrem").textContent=pr?"★ Premium активен":"★ Premium";
 const sel=$("#model"),old=sel.value;
 sel.innerHTML=models.map((m,i)=>\`<option value="\${esc(m.id)}">\${esc(m.n)}\${i>0&&!pr?" 🔒":""}</option>\`).join("");
 if(old&&models.some(m=>m.id===old))sel.value=old;
 drawList();draw();
}
let fq="",fFav=false;
function drawList(){
 const q=fq.trim().toLowerCase(),d0=new Date().setHours(0,0,0,0);
 const a=chats.filter(c=>(!fFav||c.fav)&&(!q||c.title.toLowerCase().includes(q)||c.msgs.some(m=>String(m.content).toLowerCase().includes(q))));
 const grp=c=>c.fav&&!fFav?"★ Избранные":c.id>=d0?"Сегодня":c.id>=d0-864e5?"Вчера":c.id>=d0-6*864e5?"Последние 7 дней":"Ранее";
 const order=["★ Избранные","Сегодня","Вчера","Последние 7 дней","Ранее"];let h="";
 for(const g of order){const x=a.filter(c=>grp(c)===g);if(!x.length)continue;h+=\`<div class="gr">\${g}</div>\`+x.map(c=>\`<div class="it\${c.id===cid?" on":""}" data-id="\${c.id}"><span>\${c.fav?"★ ":""}\${esc(c.title)}</span><b class="dots" data-a="menu">⋯</b></div>\`).join("")}
 $("#list").innerHTML=h||\`<p class="mut">\${q?"Ничего не найдено":fFav?"Нет избранных чатов":"Чатов пока нет"}</p>\`;
}
function draw(){
 const c=cc(),ch=$("#chat");
 if(!c||!c.msgs.length){
  ch.innerHTML=\`<div class="hero"><div class="ms">🌸</div><h1>OmniMind</h1><p>Бесплатный ИИ без ключей. Решает примеры и задачи по фото, пишет код, тексты и переводы.</p><div class="chips"><button data-p="Объясни простыми словами, как работает интернет">🌐 Как работает интернет</button><button data-p="Напиши на Python игру «Угадай число»">🐍 Игра на Python</button><button data-p="Придумай 5 идей для стартапа">💡 Идеи</button><button data-m="math">📷 Реши задачу по фото</button></div></div>\`;return}
 ch.innerHTML=c.msgs.map(m=>{
  const im=m.img?\`<img src="\${m.img}" alt="">\`:m.hadImg?"📷 (фото)<br>":"";
  return m.role==="user"?\`<div class="m u">\${im}\${fmt(m.content)}</div>\`:\`<div class="m a\${m.err?" err":""}">\${m.label?\`<small>🌸 \${esc(m.label)}</small>\`:""}\${fmt(m.content)}</div>\`}).join("");
 ch.scrollTop=ch.scrollHeight;
}
$("#chat").onclick=e=>{const b=e.target.closest("button");if(!b)return;if(b.dataset.p){$("#q").value=b.dataset.p;send()}if(b.dataset.m){$("#mode").value=b.dataset.m;$("#file").click()}};
let mid=null;
$("#list").onclick=e=>{const it=e.target.closest(".it");if(!it)return;const id=+it.dataset.id;
 if(e.target.dataset.a==="menu"){e.stopPropagation();mid=id;const c=chats.find(x=>x.id===id),r=e.target.getBoundingClientRect(),m=$("#cm");m.querySelector("[data-a=fav]").textContent=c.fav?"★ Убрать из избранного":"☆ В избранное";m.hidden=false;m.style.left=Math.max(8,Math.min(r.left,innerWidth-200))+"px";m.style.top=Math.min(r.bottom+4,innerHeight-160)+"px";return}
 cid=id;draw();drawList();$("#side").classList.remove("open")};
$("#cm").onclick=e=>{const a=e.target.dataset.a,c=chats.find(x=>x.id===mid);$("#cm").hidden=true;if(!a||!c)return;
 if(a==="fav"){c.fav=!c.fav;save();drawList()}
 if(a==="ren"){const t=prompt("Название чата",c.title);if(t&&t.trim()){c.title=t.trim().slice(0,60);save();drawList()}}
 if(a==="del"&&confirm("Удалить чат «"+c.title+"»?")){chats=chats.filter(x=>x.id!==c.id);if(cid===c.id)cid=chats[0]?chats[0].id:null;save();ui()}};
document.addEventListener("click",e=>{if(!e.target.closest("#cm"))$("#cm").hidden=true;if(!e.target.closest("#bProf"))$("#pm").hidden=true});
$("#srch").oninput=e=>{fq=e.target.value;drawList()};
$("#tFav").onclick=()=>{fFav=!fFav;$("#tFav").classList.toggle("on",fFav);$("#tFav i").textContent=fFav?"★":"☆";drawList()};
$("#bProf").onclick=e=>{e.stopPropagation();$("#cm").hidden=true;$("#pm").hidden=!$("#pm").hidden};
$("#pm").addEventListener("click",()=>setTimeout(()=>{$("#pm").hidden=true}));
$("#mProf").onclick=()=>{if(!cur())return openAuth();$("#pfE").textContent=ME.email;$("#pfP").textContent=ME.premium?"★ Premium":"Free";$("#pfU").textContent=ME.premium?"без лимита":ME.used+" из "+ME.limit;$("#pfN").textContent=chats.length;dProf.showModal();$("#side").classList.remove("open")};
$("#bCol").onclick=()=>{if(innerWidth>760)document.body.classList.add("side-c");else $("#side").classList.remove("open")};
$("#bSet").onclick=()=>{$("#sMode").value=L("om_mode","chat");dSet.showModal();$("#side").classList.remove("open")};
$("#sMode").onchange=e=>{S("om_mode",e.target.value);$("#mode").value=e.target.value};
$("#sClr").onclick=()=>{if(!cur())return;if(confirm("Удалить ВСЕ чаты? Это нельзя отменить.")){chats=[];cid=null;save();ui();dSet.close()}};
let tx=0;$("#side").addEventListener("touchstart",e=>tx=e.touches[0].clientX,{passive:true});$("#side").addEventListener("touchend",e=>{if(tx-e.changedTouches[0].clientX>60)$("#side").classList.remove("open")});
document.addEventListener("keydown",e=>{if(e.key==="Escape")$("#side").classList.remove("open")});
$("#nc").onclick=()=>{if(!cur())return openAuth();newChat();draw();drawList();$("#side").classList.remove("open")};
$("#bMenu").onclick=()=>{if(innerWidth>760)document.body.classList.remove("side-c");else $("#side").classList.toggle("open")};
$("#shade").onclick=()=>$("#side").classList.remove("open");

function openAuth(){authMode="in";authUI();dAuth.showModal()}
function authUI(){$("#aT").textContent=authMode==="in"?"Вход":"Регистрация";$("#aOk").textContent=authMode==="in"?"Войти":"Создать аккаунт";$("#aSw").textContent=authMode==="in"?"Регистрация":"Уже есть аккаунт";$("#aE").textContent=""}
$("#bAuth").onclick=async()=>{if(cur()){await api("logout",{method:"POST"});ME=null;chats=[];cid=null;ui()}else openAuth()};
$("#aSw").onclick=()=>{authMode=authMode==="in"?"up":"in";authUI()};
$("#aOk").onclick=async()=>{
 const e=norm($("#em").value),p=$("#pw").value;
 if(!/^\\S+@\\S+\\.\\S+$/.test(e))return $("#aE").textContent="Неверный email";
 if(p.length<6)return $("#aE").textContent="Пароль слишком короткий";
 $("#aOk").disabled=true;
 try{const r=await api(authMode==="up"?"register":"login",{method:"POST",body:JSON.stringify({email:e,password:p})});const j=await r.json();
  if(!r.ok)return $("#aE").textContent=j.error||"Ошибка";
  $("#pw").value="";dAuth.close();await load()}catch(x){$("#aE").textContent="Нет связи с сервером"}finally{$("#aOk").disabled=false}
};
$("#pw").addEventListener("keydown",e=>{if(e.key==="Enter")$("#aOk").click()});
$("#bPrem").onclick=()=>{if(!cur())return openAuth();$("#pE").textContent=isPrem()?"Premium уже активен ✓":"";$("#admBox").hidden=!(ME&&ME.admin);dPrem.showModal();$("#side").classList.remove("open")};
const grant=async v=>{const em=norm($("#pEm").value);if(!em)return $("#pE").textContent="Введите email";try{const r=await api("admin/user",{method:"POST",body:JSON.stringify({email:em,premium:v})});const j=await r.json();$("#pE").textContent=r.ok?(v?"Premium выдан ✓ ":"Premium снят ✓ ")+em:(j.error||"Ошибка")}catch(e){$("#pE").textContent="Нет связи с сервером"}};
$("#pGive").onclick=()=>grant(1);$("#pTake").onclick=()=>grant(0);
function readImg(f){return new Promise(res=>{const r=new FileReader();r.onerror=()=>res(null);r.onload=()=>{const im=new Image();im.onerror=()=>res(null);im.onload=()=>{const k=Math.min(1,1024/Math.max(im.width,im.height)),c=document.createElement("canvas");c.width=Math.round(im.width*k);c.height=Math.round(im.height*k);c.getContext("2d").drawImage(im,0,0,c.width,c.height);res(c.toDataURL("image/jpeg",.8))};im.src=r.result};r.readAsDataURL(f)})}
$("#file").onchange=async e=>{const f=e.target.files[0];e.target.value="";if(!f)return;img=await readImg(f);if(!img)return alert("Не удалось открыть фото. Попробуйте другой файл (JPG или PNG).");pv()};
function pv(){$("#pv").innerHTML=img?\`<img src="\${img}" alt=""><button id="xi">✕</button>\`:"";if(img)$("#xi").onclick=()=>{img=null;pv()}}

const sleep=ms=>new Promise(o=>setTimeout(o,ms));
async function ask(model,msgs,onTok){
 const ac=new AbortController(),tm=setTimeout(()=>ac.abort(),25000);if(ctl)ctl.signal.addEventListener("abort",()=>ac.abort());
 let r;
 try{r=await fetch("/api/chat",{method:"POST",headers:{"Content-Type":"application/json","X-Requested-With":"om"},body:JSON.stringify({model,messages:msgs}),signal:ac.signal})}
 catch(e){clearTimeout(tm);throw new Error("нет ответа")}
 clearTimeout(tm);
 if(!r.ok){let m="код "+r.status;try{m=(await r.json()).error||m}catch(e){}const er=new Error(m);er.fatal=[401,402,403,429].includes(r.status);throw er}
 const ct=r.headers.get("content-type")||"";
 if(r.body&&ct.includes("event-stream")){
  const rd=r.body.getReader(),dc=new TextDecoder();let buf="",full="";
  try{
   for(;;){
    const {done,value}=await Promise.race([rd.read(),new Promise((_,j)=>setTimeout(()=>j(new Error("завис")),15000))]);
    if(done)break;
    buf+=dc.decode(value,{stream:true});const ls=buf.split("\\n");buf=ls.pop();
    for(const l of ls){if(!l.startsWith("data:"))continue;const d=l.slice(5).trim();if(!d||d==="[DONE]")continue;
     try{const x=JSON.parse(d).choices?.[0]?.delta?.content;if(x){full+=x;if(onTok)onTok(full)}}catch(e){}}
   }
  }catch(e){if(!full)throw e}
  if(full)return full;throw new Error("пусто");
 }
 const tx=await r.text();
 try{const j=JSON.parse(tx);const x=j.choices?.[0]?.message?.content;if(x)return x}catch(e){if(tx.trim())return tx}
 throw new Error("пусто");
}
let busyAt=0,ctl=null;
async function send(){
 if(busy&&Date.now()-busyAt>90000)busy=false;
 if(busy){$("#st").textContent="Подождите, ответ ещё идёт…";return}
 const t=$("#q").value.trim();
 if(!t&&!img){$("#st").textContent="Напишите сообщение";return}
 if(!cur()){$("#st").textContent="Сначала войдите в аккаунт";return openAuth()}
 const pr=isPrem(),mode=$("#mode").value;
 if(mode==="cmp"&&!pr){$("#mode").value="chat";$("#st").textContent="Сравнение 3 ИИ доступно в Premium";return $("#bPrem").click()}
 let sel=models.find(m=>m.id===$("#model").value)||models[0];
 if(!pr&&sel.id!==models[0].id){sel=models[0];$("#model").value=sel.id}
 if(!pr&&cnt()>=FREE_LIMIT){$("#st").textContent="Лимит на сегодня исчерпан — оформите Premium";return $("#bPrem").click()}
 busy=true;busyAt=Date.now();ctl=new AbortController();$("#bSend").textContent="■";
 try{
  const c=cc()||newChat();
  if(!c.msgs.length)c.title=(t||"Фото").slice(0,32);
  const um={role:"user",content:t||"Реши задачу на фото",img};
  c.msgs.push(um);$("#q").value="";$("#q").style.height="50px";img=null;pv();draw();drawList();
  $("#st").textContent="Думаю…";
  const sys={role:"system",content:SYS[mode==="cmp"?"chat":mode]};
  const past=c.msgs.slice(0,-1).filter(m=>!m.err).slice(-6).map(m=>({role:m.role,content:(m.hadImg||m.img?"[фото] ":"")+m.content}));
  const last=um.img?{role:"user",content:[{type:"text",text:um.content},{type:"image_url",image_url:{url:um.img}}]}:{role:"user",content:um.content};
  const msgs=[sys,...past,last];
  const vis=models.filter(x=>["openai","gemini","claude"].includes(x.id));
  const targets=um.img?[models[0]]:mode==="cmp"?models.slice(0,3):[sel];
  let ok=false;
  for(const m of targets){
   const am={role:"assistant",content:"…",label:m.n};c.msgs.push(am);draw();
   const order=um.img?(vis.length?vis:[models[0]]):[m,...models.filter(x=>x.id!==m.id)].slice(0,3);
   let raf=0,done=false;
   for(const x of order){
    am.label=x.n;
    try{am.content=await ask(x.id,msgs,y=>{$("#st").textContent="";am.content=y;if(!raf)raf=requestAnimationFrame(()=>{raf=0;draw()})});done=true;break}
    catch(e){if(ctl.signal.aborted){done=true;if(am.content==="…")am.content="(остановлено)";break}if(e.fatal){am.content="⚠ "+e.message;am.err=1;am.label="";done=true;break}am.content="…";$("#st").textContent="Модель не ответила, пробую другую…";draw()}
   }
   if(done)ok=true;else{am.content="⚠ Все серверы сейчас заняты или нет интернета. Нажмите отправить ещё раз через минуту.";am.err=1;am.label=""}
   $("#st").textContent="";draw();
  }
  if(ok)api("me").then(r=>r.ok&&r.json()).then(j=>{if(j)ME=j}).catch(()=>{});
 }catch(e){$("#st").textContent="Ошибка: "+(e&&e.message||e)}
 finally{busy=false;$("#bSend").textContent="➤";ctl=null;if(!/^Ошибка/.test($("#st").textContent))$("#st").textContent="";try{save();ui()}catch(e){}}
}
$("#bSend").onclick=()=>{if(busy&&ctl)ctl.abort();else send()};
$("#q").addEventListener("keydown",e=>{if(e.key==="Enter"&&!e.shiftKey&&innerWidth>760){e.preventDefault();send()}});
$("#q").addEventListener("input",e=>{e.target.style.height="50px";e.target.style.height=Math.min(140,e.target.scrollHeight)+"px"});

fetch("https://text.pollinations.ai/models").then(r=>r.json()).then(j=>{
 const a=j.filter(m=>m&&m.name&&!/audio|midi|unity|evil|roblox|bidara|rtist|image|tts/i.test(m.name)).map(m=>({n:String(m.description||m.name).split(" - ")[0].slice(0,26),id:m.name}));
 const want=[["GPT","openai",/^openai/i],["Claude","claude",/claude/i],["Gemini","gemini",/gemini/i],["DeepSeek","deepseek",/deepseek/i],["Mistral","mistral",/mistral/i],["Llama","llama",/llama/i]];
 const out=[];
 for(const [n,id,re] of want){const f=a.find(x=>re.test(x.id));out.push({n,id:f?f.id:id})}
 for(const x of a)if(!out.some(o=>o.id===x.id)&&out.length<10)out.push(x);
 models=out;ui()}).catch(()=>{});
window.addEventListener("error",e=>{const st=$("#st");if(st)st.textContent="Ошибка: "+e.message});
{const m=L("om_mode","chat");if([...$("#mode").options].some(o=>o.value===m))$("#mode").value=m}
load();ui();
</script>
</body>
</html>
`,
admin:`<!doctype html><html lang="ru"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>OmniMind — админ</title>
<style>body{font:15px system-ui;margin:0;padding:16px;background:#1a1033;color:#fff}a{color:#7df3ff}.g{display:grid;grid-template-columns:repeat(auto-fit,minmax(150px,1fr));gap:10px}.c{background:#ffffff14;border-radius:12px;padding:12px}.c b{display:block;font-size:24px}table{width:100%;border-collapse:collapse;margin:12px 0}td,th{padding:6px;border-bottom:1px solid #fff3;text-align:left;font-size:13px}.w{overflow-x:auto}button{font:inherit;border-radius:8px;border:1px solid #fff4;background:#ffffff18;color:#fff;padding:3px 8px}pre{white-space:pre-wrap;font-size:12px;color:#ffb3c1}</style>
<p><a href="/">← К чату</a></p><h2>Админ-панель</h2><div id="s" class="g"></div><h3>Пользователи</h3><div class="w"><table id="u"></table></div><h3>Последние ошибки</h3><pre id="e"></pre>
<script>
const api=(p,o={})=>fetch("/api/admin/"+p,{...o,headers:{"Content-Type":"application/json","X-Requested-With":"om"}});
const T=t=>t?new Date(t).toLocaleString():"—",X=s=>String(s).replace(/[&<>"]/g,c=>"&#"+c.charCodeAt(0)+";");
async function go(){const r=await api("stats");if(!r.ok){document.body.insertAdjacentHTML("beforeend","<p>Нет доступа. Войдите аккаунтом администратора.</p>");return}
const s=await r.json(),k={"Пользователей":s.users,"Активны (15 мин)":s.active15m,"Запросов сегодня":s.requestsToday,"Запросов всего":s.requestsTotal,"Ошибок сегодня":s.errorsToday,"Идёт генераций":s.activeStreams+" / "+s.maxConcurrent,"В очереди":s.queued,"Память, МБ":s.rssMB,"Load 1m":s.load1.toFixed(2),"Аптайм, мин":Math.round(s.uptimeSec/60)};
document.getElementById("s").innerHTML=Object.entries(k).map(([a,b])=>\`<div class=c>\${a}<b>\${X(b)}</b></div>\`).join("");
document.getElementById("e").textContent=s.lastErrors.map(e=>T(e.ts)+"  "+e.msg).join("\\n")||"нет";
const us=await(await api("users")).json();
document.getElementById("u").innerHTML="<tr><th>Email<th>Создан<th>Был<th>Premium<th>Блок</tr>"+us.map(u=>\`<tr><td>\${X(u.email)}<td>\${T(u.created)}<td>\${T(u.seen)}<td><button data-i=\${u.id} data-k=premium data-v=\${u.premium?0:1}>\${u.premium?"снять":"выдать"}</button><td><button data-i=\${u.id} data-k=blocked data-v=\${u.blocked?0:1}>\${u.blocked?"разблок.":"блок"}</button>\`).join("")}
document.getElementById("u").onclick=async e=>{const b=e.target.closest("button");if(!b)return;await api("user",{method:"POST",body:JSON.stringify({id:+b.dataset.i,[b.dataset.k]:+b.dataset.v})});go()};
go();setInterval(go,10000);
</script></html>
`};
const MIME={'.html':'text/html;charset=utf-8','.js':'text/javascript','.css':'text/css','.png':'image/png','.svg':'image/svg+xml','.ico':'image/x-icon'};
const SEC={'x-content-type-options':'nosniff','x-frame-options':'DENY','referrer-policy':'same-origin',
 'content-security-policy':"default-src 'self'; img-src 'self' data:; style-src 'self' 'unsafe-inline'; script-src 'self' 'unsafe-inline'; connect-src 'self' https://text.pollinations.ai; frame-ancestors 'none'; base-uri 'none'; form-action 'self'"};

const server=http.createServer(async(req,res)=>{
 for(const k in SEC)res.setHeader(k,SEC[k]);
 try{
  const url=new URL(req.url,'http://x'),p=url.pathname;
  if(p.startsWith('/api/')){
   if(req.method!=='GET'&&req.headers['x-requested-with']!=='om')return json(res,403,{error:'forbidden'});
   if(p==='/api/register'&&req.method==='POST')return await authRoute(req,res,'register');
   if(p==='/api/login'&&req.method==='POST')return await authRoute(req,res,'login');
   const u=authUser(req);
   if(p==='/api/logout'&&req.method==='POST'){const t=cookie(req,'sid');if(t)q('DELETE FROM sessions WHERE t=?').run(sha(t));return json(res,200,{ok:1},{'set-cookie':'sid=; HttpOnly; Path=/; Max-Age=0'})}
   if(!u)return json(res,401,{error:'Войдите в аккаунт'});
   if(p==='/api/me')return json(res,200,pub(u));
   if(p==='/api/chats'&&req.method==='GET'){const r=q('SELECT data FROM chats WHERE uid=?').get(u.id);return json(res,200,r?JSON.parse(r.data):[])}
   if(p==='/api/chats'&&req.method==='PUT'){let a;try{a=JSON.parse(await readBody(req,2e6))}catch(e){return json(res,400,{error:'bad'})}
    if(!Array.isArray(a))return json(res,400,{error:'bad'});
    q('INSERT INTO chats VALUES(?,?,?)ON CONFLICT(uid)DO UPDATE SET data=excluded.data,upd=excluded.upd').run(u.id,JSON.stringify(a.slice(0,100)),now());return json(res,200,{ok:1})}
   if(p==='/api/chat'&&req.method==='POST')return await chat(req,res,u);
   if(p.startsWith('/api/admin/')){
    if(!ADMIN||u.email!==ADMIN)return json(res,403,{error:'forbidden'});
    if(p==='/api/admin/stats')return json(res,200,adminStats());
    if(p==='/api/admin/users')return json(res,200,q('SELECT id,email,premium,blocked,created,seen FROM users ORDER BY id DESC LIMIT 500').all()); // no passwords, no chats
    if(p==='/api/admin/user'&&req.method==='POST'){const b=JSON.parse(await readBody(req,1000));
     const t=b.email?q('SELECT id,email FROM users WHERE email=?').get(String(b.email).trim().toLowerCase()):q('SELECT id,email FROM users WHERE id=?').get(+b.id);
     if(!t)return json(res,404,{error:'Пользователь не найден — он должен сначала зарегистрироваться'});
     if(t.email===ADMIN)return json(res,400,{error:'У админа Premium всегда включён'});
     if('blocked' in b){q('UPDATE users SET blocked=? WHERE id=?').run(b.blocked?1:0,t.id);if(b.blocked)q('DELETE FROM sessions WHERE uid=?').run(t.id)}
     if('premium' in b)q('UPDATE users SET premium=? WHERE id=?').run(b.premium?1:0,t.id);return json(res,200,{ok:1})}}
   return json(res,404,{error:'not found'})}
  if(req.method!=='GET'&&req.method!=='HEAD'){res.writeHead(405);return res.end()}
  const page=p==='/'||p==='/index.html'?PAGES.index:p==='/admin.html'?PAGES.admin:null;
  if(page===null){res.writeHead(404);return res.end('Not found')}
  res.writeHead(200,{'content-type':'text/html;charset=utf-8','cache-control':'no-cache'});res.end(req.method==='HEAD'?'':page);
 }catch(e){logErr(e.stack||e);json(res,500,{error:'Ошибка сервера'})}});
server.requestTimeout=0;server.headersTimeout=15000;server.keepAliveTimeout=30000;
process.on('unhandledRejection',e=>logErr('unhandled '+e));process.on('uncaughtException',e=>logErr('uncaught '+e));
server.listen(PORT,()=>console.log('OmniMind on :'+PORT));
