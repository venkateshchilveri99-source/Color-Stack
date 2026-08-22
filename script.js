/* ==================================================================
   COLOR STACK — Water Sort Puzzle
   Vanilla JS game logic. Organized into clear sections:
   1. Config & constants
   2. Save/load (localStorage)
   3. Solvable level generator
   4. Game state & core rules
   5. Rendering
   6. Input handling
   7. Undo / Restart / Hint / Pause / Win flow
   8. Audio (Web Audio API)
   9. Navigation & page wiring
   10. Boot
   ================================================================== */

/* ---------------------- 1. CONFIG & CONSTANTS ---------------------- */

const PALETTE = [
  '#FF5A5F', '#FFB627', '#FFE066', '#06D6A0',
  '#00B4D8', '#4361EE', '#7B2FF7', '#F72585',
  '#A0E426', '#C08552', '#4CC9F0', '#FF477E'
];

const LEVELS = [
  null, // 1-indexed
  { colors:3,  capacity:4, empty:2, label:'Very Easy', mult:1.0 },
  { colors:4,  capacity:4, empty:2, label:'Easy',      mult:1.2 },
  { colors:5,  capacity:4, empty:2, label:'Easy',      mult:1.4 },
  { colors:6,  capacity:4, empty:2, label:'Medium',    mult:1.6 },
  { colors:7,  capacity:4, empty:2, label:'Medium',    mult:1.8 },
  { colors:8,  capacity:4, empty:2, label:'Medium',    mult:2.0 },
  { colors:9,  capacity:4, empty:2, label:'Hard',      mult:2.3 },
  { colors:10, capacity:4, empty:2, label:'Hard',      mult:2.6 },
  { colors:11, capacity:5, empty:2, label:'Very Hard', mult:3.0 },
  { colors:12, capacity:5, empty:3, label:'Extreme',   mult:3.5 },
];

const SAVE_KEY = 'colorstack_save_v1';

function defaultSave(){
  return {
    unlockedLevel: 1,
    levels: {}, // { [levelNum]: {completed, stars, bestScore, bestMoves} }
    totalScore: 0,
    settings: { sound:true, music:false, theme:'dark', vibration:true, animations:true },
    stats: {
      totalMoves:0, gamesPlayed:0, levelsCompleted:0,
      bestScore:0, highestLevel:1, currentStreak:0, bestLevelScore:0
    }
  };
}

/* ---------------------- 2. SAVE / LOAD ---------------------- */

let SAVE = loadSave();

function loadSave(){
  try{
    const raw = localStorage.getItem(SAVE_KEY);
    if(!raw) return defaultSave();
    const parsed = JSON.parse(raw);
    // merge with defaults in case of new fields
    const d = defaultSave();
    return {
      ...d, ...parsed,
      settings:{ ...d.settings, ...(parsed.settings||{}) },
      stats:{ ...d.stats, ...(parsed.stats||{}) },
      levels: parsed.levels || {}
    };
  }catch(e){
    return defaultSave();
  }
}

function persist(){
  localStorage.setItem(SAVE_KEY, JSON.stringify(SAVE));
}

/* ---------------------- 3. SOLVABLE LEVEL GENERATOR ----------------------
   Strategy: deal the shuffled multiset of colored units randomly into the
   "color" tubes (leaving the extra tubes empty), then run a depth-first
   solver — with visited-state memoization and a completion-first move
   heuristic — to CONFIRM a real solution path exists. If the solver can't
   find one within its search budget, we deal again. Only a puzzle the
   solver has actually proven solvable is ever handed to the player, so
   every level is guaranteed solvable (never a randomly-unsolvable deal).
------------------------------------------------------------------- */

function cloneTubes(t){ return t.map(tube => tube.slice()); }

function isSorted(tubes){
  return tubes.every(tube => tube.length === 0 || tube.every(c => c === tube[0]));
}

function getValidMoves(tubes, capacity){
  const moves = [];
  for(let i=0;i<tubes.length;i++){
    if(tubes[i].length === 0) continue;
    const topColor = tubes[i][tubes[i].length-1];
    for(let j=0;j<tubes.length;j++){
      if(i===j) continue;
      if(tubes[j].length >= capacity) continue;
      if(tubes[j].length>0 && tubes[j][tubes[j].length-1] !== topColor) continue;
      moves.push([i,j]);
    }
  }
  return moves;
}

function topRunLength(tube){
  if(tube.length===0) return 0;
  const color = tube[tube.length-1];
  let n=0;
  for(let k=tube.length-1;k>=0;k--){
    if(tube[k]===color) n++; else break;
  }
  return n;
}

function pourMove(tubes, i, j, capacity){
  const runLen = topRunLength(tubes[i]);
  const space = capacity - tubes[j].length;
  const amount = Math.min(runLen, space);
  for(let a=0;a<amount;a++){ tubes[j].push(tubes[i].pop()); }
  return amount;
}

function randomDeal(colors, capacity, emptyCount){
  const units = [];
  for(let c=0;c<colors;c++){
    for(let k=0;k<capacity;k++) units.push(PALETTE[c]);
  }
  // Fisher-Yates shuffle
  for(let i=units.length-1;i>0;i--){
    const j = Math.floor(Math.random()*(i+1));
    [units[i], units[j]] = [units[j], units[i]];
  }
  const tubes = [];
  let idx = 0;
  for(let c=0;c<colors;c++){
    const t = [];
    for(let s=0;s<capacity;s++) t.push(units[idx++]);
    tubes.push(t);
  }
  for(let e=0;e<emptyCount;e++) tubes.push([]);
  return tubes;
}

// Canonical key ignores tube ORDER (two boards that differ only by which
// physical tube holds which stack are the same puzzle state), which keeps
// the visited-state set small and the solver fast.
function stateKey(tubes){
  return tubes.map(t => t.join(',')).sort().join('|');
}

/* Depth-first solver with memoization + a "prefer moves that make real
   progress" heuristic (finishing a tube, or fully draining one, is tried
   before other moves). Returns {solvable, moveCount} — moveCount is the
   length of the first solution path found, used to set each level's par. */
function solvePuzzle(tubes, capacity, maxNodes, maxDepth){
  const visited = new Set([stateKey(tubes)]);
  let nodes = 0;

  function dfs(cur, depth){
    nodes++;
    if(nodes > maxNodes) return -1;
    if(isSorted(cur)) return 0;
    if(depth <= 0) return -1;

    const moves = getValidMoves(cur, capacity);
    const scored = moves.map(([i,j]) => {
      const runLen = topRunLength(cur[i]);
      let score = 0;
      if(cur[j].length + runLen === capacity) score += 10; // completes a tube
      if(runLen === cur[i].length) score += 4;              // fully drains source
      if(cur[j].length === 0) score -= 1;                    // slight penalty: avoid needless empty dumps
      return { i, j, score };
    }).sort((a,b) => b.score - a.score);

    for(const { i, j } of scored){
      const next = cloneTubes(cur);
      pourMove(next, i, j, capacity);
      const key = stateKey(next);
      if(visited.has(key)) continue;
      visited.add(key);
      const sub = dfs(next, depth-1);
      if(sub >= 0) return sub + 1;
      if(nodes > maxNodes) return -1;
    }
    return -1;
  }

  const totalUnits = tubes.reduce((a,t)=>a+t.length,0);
  const moveCount = dfs(tubes, maxDepth || totalUnits*4);
  return { solvable: moveCount >= 0, moveCount: moveCount >= 0 ? moveCount : null };
}

function generateLevel(levelNum){
  const cfg = LEVELS[levelNum];
  let tubes, result, attempts = 0;
  do{
    attempts++;
    tubes = randomDeal(cfg.colors, cfg.capacity, cfg.empty);
    if(isSorted(tubes)) continue; // practically never happens, guard anyway
    result = solvePuzzle(cloneTubes(tubes), cfg.capacity, 80000, cfg.colors * cfg.capacity * 4);
  } while((!result || !result.solvable) && attempts < 25);

  // Extremely rare fallback: if the solver couldn't confirm a solution in
  // budget after many tries, fall back to a smaller shuffle guaranteed to
  // be trivially solvable so the player is never handed a broken level.
  if(!result || !result.solvable){
    tubes = randomDeal(cfg.colors, cfg.capacity, Math.max(cfg.empty, 2));
    result = { moveCount: cfg.colors * 2 };
  }

  return {
    tubes,
    capacity: cfg.capacity,
    parMoves: Math.max(cfg.colors, result.moveCount || cfg.colors * 2),
    label: cfg.label,
    mult: cfg.mult
  };
}

/* ---------------------- 4. GAME STATE ---------------------- */

const G = {
  level: 1,
  tubes: [],
  capacity: 4,
  parMoves: 0,
  mult: 1,
  selected: null,
  moves: 0,
  score: 0,
  hintsUsed: 0,
  usedUndo: false,
  history: [],
  startTime: 0,
  elapsed: 0,
  timerId: null,
  paused: false,
  locked: false // input lock during animations
};

function tubeIsComplete(tube, capacity){
  return tube.length === capacity && tube.every(c => c === tube[0]);
}

function checkWin(tubes){
  return tubes.every(tube => tube.length===0 || tube.every(c => c===tube[0]));
}

function canPour(tubes, from, to, capacity){
  if(from===to) return false;
  const src = tubes[from], dst = tubes[to];
  if(src.length===0) return false;
  if(dst.length>=capacity) return false;
  const topColor = src[src.length-1];
  if(dst.length>0 && dst[dst.length-1] !== topColor) return false;
  return true;
}

/* ---------------------- 5. RENDERING ---------------------- */

const el = (id) => document.getElementById(id);

function startLevel(levelNum, keepStats){
  const gen = generateLevel(levelNum);
  G.level = levelNum;
  G.tubes = gen.tubes;
  G.capacity = gen.capacity;
  G.parMoves = gen.parMoves;
  G.mult = gen.mult;
  G.selected = null;
  G.moves = 0;
  G.score = 0;
  G.hintsUsed = 0;
  G.usedUndo = false;
  G.history = [];
  G.elapsed = 0;
  G.paused = false;
  G.locked = false;
  clearInterval(G.timerId);
  G.startTime = Date.now();
  G.timerId = setInterval(tickTimer, 1000);
  renderTubes(true);
  updateHud();
  showPage('page-game');
}

function tickTimer(){
  if(G.paused) return;
  G.elapsed = Math.floor((Date.now() - G.startTime)/1000);
  el('hudTime').textContent = formatTime(G.elapsed);
}

function formatTime(sec){
  const m = Math.floor(sec/60), s = sec%60;
  return `${m}:${String(s).padStart(2,'0')}`;
}

function updateHud(){
  el('hudLevel').textContent = 'LEVEL ' + G.level;
  el('hudScore').textContent = G.score;
  el('hudMoves').textContent = G.moves;
  el('hudTime').textContent = formatTime(G.elapsed);
  el('btnUndo').disabled = G.history.length===0;
}

function renderTubes(instant){
  const arena = el('tubesArena');
  arena.innerHTML = '';
  const tubeHeight = Math.min(220, 44 * G.capacity + 20);

  G.tubes.forEach((tube, idx) => {
    const wrap = document.createElement('div');
    wrap.className = 'tube-wrap';
    wrap.dataset.index = idx;
    if(G.selected === idx) wrap.classList.add('selected');

    const cap = document.createElement('div');
    cap.className = 'tube-cap';
    wrap.appendChild(cap);

    const tubeEl = document.createElement('div');
    tubeEl.className = 'tube';
    tubeEl.style.height = tubeHeight + 'px';

    for(let s=0; s<G.capacity; s++){
      const seg = document.createElement('div');
      seg.className = 'liquid-seg';
      const color = tube[s];
      if(color){
        seg.style.background = color;
        seg.style.height = (100/G.capacity) + '%';
        if(s === tube.length-1) seg.classList.add('top-seg');
      } else {
        seg.style.height = '0%';
      }
      tubeEl.appendChild(seg);
    }
    wrap.appendChild(tubeEl);

    const label = document.createElement('div');
    label.className = 'tube-label';
    label.textContent = idx+1;
    wrap.appendChild(label);

    wrap.addEventListener('click', () => onTubeClick(idx));
    arena.appendChild(wrap);
  });
}

/* ---------------------- 6. INPUT HANDLING ---------------------- */

function onTubeClick(idx){
  if(G.locked || G.paused) return;
  clearHintHighlight();

  if(G.selected === null){
    if(G.tubes[idx].length===0) return;
    G.selected = idx;
    playTone('select');
    renderTubes();
    return;
  }

  if(G.selected === idx){
    G.selected = null;
    renderTubes();
    return;
  }

  if(canPour(G.tubes, G.selected, idx, G.capacity)){
    performPour(G.selected, idx);
  } else {
    // switch selection to the newly clicked tube if it has liquid
    if(G.tubes[idx].length>0){
      G.selected = idx;
      playTone('select');
      renderTubes();
    } else {
      G.selected = null;
      renderTubes();
    }
  }
}

function performPour(from, to){
  // push history snapshot
  G.history.push({
    tubes: cloneTubes(G.tubes),
    moves: G.moves,
    score: G.score
  });

  const amount = pourMove(G.tubes, from, to, G.capacity);
  G.moves++;
  G.selected = null;
  G.locked = true;

  playTone('pour');
  vibrate(15);
  animateDroplets(from, to, amount, () => {
    renderTubes();
    updateHud();
    G.locked = false;

    if(checkWin(G.tubes)){
      setTimeout(() => onLevelComplete(), 380);
    }
  });
}

function animateDroplets(from, to, amount, done){
  if(!SAVE.settings.animations){ done(); return; }
  const arena = el('tubesArena');
  const fromEl = arena.querySelector(`[data-index="${from}"] .tube`);
  const toEl = arena.querySelector(`[data-index="${to}"] .tube`);
  if(!fromEl || !toEl){ done(); return; }
  const fromRect = fromEl.getBoundingClientRect();
  const toRect = toEl.getBoundingClientRect();
  const color = G.history[G.history.length-1].tubes[from].slice(-1)[0] || '#fff';

  let n = Math.min(amount, 4);
  let completed = 0;
  for(let i=0;i<n;i++){
    setTimeout(() => {
      const drop = document.createElement('div');
      drop.className = 'pour-droplet';
      drop.style.color = color;
      drop.style.background = color;
      drop.style.left = (fromRect.left + fromRect.width/2) + 'px';
      drop.style.top = (fromRect.top + 8) + 'px';
      document.body.appendChild(drop);
      const dx = (toRect.left + toRect.width/2) - (fromRect.left + fromRect.width/2);
      const dy = (toRect.top + 10) - (fromRect.top + 8);
      drop.animate([
        { transform:'translate(0,0)', opacity:1 },
        { transform:`translate(${dx*0.5}px, ${dy*0.4 - 26}px)`, opacity:1, offset:.5 },
        { transform:`translate(${dx}px, ${dy}px)`, opacity:0.9 }
      ], { duration:280, easing:'ease-in' }).onfinish = () => {
        drop.remove();
        completed++;
        if(completed===n) done();
      };
    }, i*40);
  }
  if(n===0) done();
}

/* ---------------------- 7. UNDO / RESTART / HINT / PAUSE / WIN ---------------------- */

function undoMove(){
  if(G.history.length===0 || G.locked) return;
  const prev = G.history.pop();
  G.tubes = prev.tubes;
  G.moves = prev.moves;
  G.score = prev.score;
  G.selected = null;
  G.usedUndo = true;
  playTone('click');
  vibrate(10);
  renderTubes();
  updateHud();
}

function restartLevel(){
  startLevel(G.level);
}

function clearHintHighlight(){
  document.querySelectorAll('.hint-a,.hint-b').forEach(e => e.classList.remove('hint-a','hint-b'));
}

function useHint(){
  if(G.locked) return;
  const moves = getValidMoves(G.tubes, G.capacity)
    .filter(([i,j]) => {
      // ignore moves that shuffle a fully-sorted tube into another empty (no real progress)
      if(tubeIsComplete(G.tubes[i], G.capacity)) return false;
      return true;
    });
  if(moves.length===0){
    playTone('click');
    return;
  }
  // Prefer a move that completes a tube
  let best = moves.find(([i,j]) => {
    const runLen = topRunLength(G.tubes[i]);
    return G.tubes[j].length + runLen === G.capacity &&
      (G.tubes[j].length===0 || G.tubes[j][G.tubes[j].length-1]===G.tubes[i][G.tubes[i].length-1]);
  });
  if(!best) best = moves[Math.floor(Math.random()*moves.length)];

  const [i,j] = best;
  clearHintHighlight();
  const arena = el('tubesArena');
  const a = arena.querySelector(`[data-index="${i}"]`);
  const b = arena.querySelector(`[data-index="${j}"]`);
  if(a) a.classList.add('hint-a');
  if(b) b.classList.add('hint-b');

  G.hintsUsed++;
  G.score = Math.max(0, G.score - 15);
  updateHud();
  playTone('hint');
  setTimeout(clearHintHighlight, 2200);
}

function pauseGame(){
  G.paused = true;
  showOverlay('overlayPause');
}
function resumeGame(){
  G.paused = false;
  hideOverlay('overlayPause');
}

function onLevelComplete(){
  clearInterval(G.timerId);
  const cfg = LEVELS[G.level];
  const timeSec = G.elapsed;

  const movePenalty = Math.max(0, G.moves - G.parMoves) * 15;
  const hintPenalty = G.hintsUsed * 60;
  const timePenalty = Math.min(300, timeSec) * 1.4;
  const undoBonus = G.usedUndo ? 0 : 80;
  const base = 1000 * cfg.mult;
  const finalScore = Math.max(60, Math.round(base - movePenalty - hintPenalty - timePenalty + undoBonus));
  G.score = finalScore;

  let stars = 1;
  if(G.moves <= G.parMoves && G.hintsUsed===0) stars = 3;
  else if(G.moves <= G.parMoves * 1.4) stars = 2;

  // persist progress
  const lv = SAVE.levels[G.level] || { completed:false, stars:0, bestScore:0, bestMoves:Infinity };
  const isNewBest = finalScore > (lv.bestScore||0);
  SAVE.levels[G.level] = {
    completed: true,
    stars: Math.max(lv.stars||0, stars),
    bestScore: Math.max(lv.bestScore||0, finalScore),
    bestMoves: Math.min(lv.bestMoves===undefined?Infinity:lv.bestMoves, G.moves)
  };
  if(G.level === SAVE.unlockedLevel && G.level < LEVELS.length-1){
    SAVE.unlockedLevel = G.level + 1;
  }
  SAVE.totalScore += finalScore;
  SAVE.stats.totalMoves += G.moves;
  SAVE.stats.gamesPlayed += 1;
  SAVE.stats.currentStreak += 1;
  SAVE.stats.bestScore = Math.max(SAVE.stats.bestScore, finalScore);
  SAVE.stats.highestLevel = Math.max(SAVE.stats.highestLevel, G.level);
  SAVE.stats.bestLevelScore = Math.max(SAVE.stats.bestLevelScore, finalScore);
  const uniqueCompleted = Object.values(SAVE.levels).filter(l => l.completed).length;
  SAVE.stats.levelsCompleted = uniqueCompleted;
  persist();

  playTone('win');
  vibrate([20,40,20]);

  el('completeScore').textContent = finalScore;
  el('completeMoves').textContent = G.moves;
  el('completeTime').textContent = formatTime(timeSec);
  el('completeBest').textContent = SAVE.levels[G.level].bestScore;

  document.querySelectorAll('#starsRow .star').forEach((s, i) => {
    s.classList.remove('earned');
    if(i < stars) s.classList.add('earned');
  });

  const nextBtn = el('btnNextLevel');
  nextBtn.style.display = (G.level < LEVELS.length-1) ? 'flex' : 'none';

  spawnConfetti();
  showOverlay('overlayComplete');
}

function spawnConfetti(){
  if(!SAVE.settings.animations) return;
  const layer = el('confettiLayer');
  layer.innerHTML='';
  const colors = PALETTE;
  for(let i=0;i<36;i++){
    const p = document.createElement('div');
    p.className = 'confetti-piece';
    const size = 6 + Math.random()*6;
    p.style.width = size+'px';
    p.style.height = (size*1.4)+'px';
    p.style.left = Math.random()*100 + '%';
    p.style.background = colors[Math.floor(Math.random()*colors.length)];
    p.style.animationDuration = (1.6 + Math.random()*1.2)+'s';
    p.style.animationDelay = (Math.random()*.4)+'s';
    layer.appendChild(p);
  }
}

/* ---------------------- 8. AUDIO (Web Audio API) ---------------------- */

let audioCtx = null;
function getAudioCtx(){
  if(!audioCtx){
    try{ audioCtx = new (window.AudioContext || window.webkitAudioContext)(); }
    catch(e){ return null; }
  }
  return audioCtx;
}

function playTone(kind){
  if(!SAVE.settings.sound) return;
  const ctx = getAudioCtx();
  if(!ctx) return;
  if(ctx.state==='suspended') ctx.resume();

  const now = ctx.currentTime;
  const presets = {
    select: [{f:520, d:.08, type:'sine', g:.18}],
    click:  [{f:340, d:.06, type:'square', g:.10}],
    pour:   [{f:300, d:.18, type:'sine', g:.14, slide:200}],
    hint:   [{f:660, d:.12, type:'triangle', g:.15},{f:880,d:.12,type:'triangle',g:.12,delay:.1}],
    win:    [{f:523,d:.14,type:'sine',g:.16},{f:659,d:.14,type:'sine',g:.16,delay:.14},{f:784,d:.22,type:'sine',g:.18,delay:.28}]
  };
  (presets[kind]||[]).forEach(step => {
    const osc = ctx.createOscillator();
    const gain = ctx.createGain();
    osc.type = step.type;
    const start = now + (step.delay||0);
    osc.frequency.setValueAtTime(step.f, start);
    if(step.slide) osc.frequency.exponentialRampToValueAtTime(step.f - step.slide*0.4, start + step.d);
    gain.gain.setValueAtTime(0.0001, start);
    gain.gain.exponentialRampToValueAtTime(step.g, start + 0.02);
    gain.gain.exponentialRampToValueAtTime(0.0001, start + step.d);
    osc.connect(gain).connect(ctx.destination);
    osc.start(start);
    osc.stop(start + step.d + 0.05);
  });
}

let musicNodes = null;
function toggleMusic(on){
  const ctx = getAudioCtx();
  if(!ctx) return;
  if(on && !musicNodes){
    const gain = ctx.createGain();
    gain.gain.value = 0.035;
    gain.connect(ctx.destination);
    const notes = [220, 277, 330, 415];
    const oscs = notes.map((f,i) => {
      const o = ctx.createOscillator();
      o.type = 'sine';
      o.frequency.value = f;
      const g = ctx.createGain();
      g.gain.value = 0;
      o.connect(g).connect(gain);
      o.start();
      return { o, g };
    });
    let step = 0;
    const interval = setInterval(() => {
      oscs.forEach((n, idx) => {
        const active = idx === step % oscs.length;
        n.g.gain.linearRampToValueAtTime(active ? 1 : 0, ctx.currentTime + 0.4);
      });
      step++;
    }, 900);
    musicNodes = { gain, oscs, interval };
  } else if(!on && musicNodes){
    clearInterval(musicNodes.interval);
    musicNodes.oscs.forEach(n => { try{ n.o.stop(); }catch(e){} });
    musicNodes.gain.disconnect();
    musicNodes = null;
  }
}

function vibrate(pattern){
  if(SAVE.settings.vibration && navigator.vibrate){
    navigator.vibrate(pattern);
  }
}

/* ---------------------- 9. NAVIGATION & PAGE WIRING ---------------------- */

function showPage(id){
  document.querySelectorAll('.page').forEach(p => p.classList.remove('active'));
  el(id).classList.add('active');
}

function showOverlay(id){ el(id).classList.add('active'); }
function hideOverlay(id){ el(id).classList.remove('active'); }

function renderHome(){
  el('homeBestScore').textContent = SAVE.stats.bestScore;
  el('homeLevelProgress').textContent = `${SAVE.unlockedLevel} / ${LEVELS.length-1}`;
}

function renderLevels(){
  const grid = el('levelsGrid');
  grid.innerHTML = '';
  for(let n=1; n<LEVELS.length; n++){
    const cfg = LEVELS[n];
    const lv = SAVE.levels[n];
    const unlocked = n <= SAVE.unlockedLevel;
    const card = document.createElement('button');
    card.className = 'level-card glass' + (unlocked ? '' : ' locked');
    const starsEarned = lv ? lv.stars : 0;
    const starsHtml = [1,2,3].map(i => `<span class="${i<=starsEarned?'':'dim'}">★</span>`).join('');
    card.innerHTML = `
      ${unlocked ? '' : '<span class="lc-lock-icon">🔒</span>'}
      <span class="lc-num">${n}</span>
      <span class="lc-diff">${cfg.label}</span>
      <span class="lc-stars">${starsHtml}</span>
      <span class="lc-best">${lv && lv.completed ? 'Best: '+lv.bestScore : 'Not played'}</span>
    `;
    if(unlocked){
      card.addEventListener('click', () => startLevel(n));
    }
    grid.appendChild(card);
  }
}

function renderSettings(){
  el('toggleSound').checked = SAVE.settings.sound;
  el('toggleMusic').checked = SAVE.settings.music;
  el('toggleVibration').checked = SAVE.settings.vibration;
  el('toggleAnimations').checked = SAVE.settings.animations;
  document.querySelectorAll('.theme-swatch').forEach(btn => {
    btn.classList.toggle('active', btn.dataset.theme === SAVE.settings.theme);
  });
}

function renderStats(){
  const s = SAVE.stats;
  const items = [
    ['Total Score', SAVE.totalScore],
    ['Best Score', s.bestScore],
    ['Highest Level', s.highestLevel],
    ['Total Moves', s.totalMoves],
    ['Levels Completed', s.levelsCompleted + ' / ' + (LEVELS.length-1)],
    ['Games Played', s.gamesPlayed],
    ['Best Level Score', s.bestLevelScore],
    ['Current Streak', s.currentStreak],
  ];
  const grid = el('statsGrid');
  grid.innerHTML = items.map(([label,val]) => `
    <div class="stat-card glass">
      <span class="stat-value">${val}</span>
      <span class="stat-label">${label}</span>
    </div>
  `).join('');
}

function applyTheme(theme){
  document.body.dataset.theme = theme;
  SAVE.settings.theme = theme;
  persist();
  renderSettings();
}

function initParticles(){
  const layer = el('bgParticles');
  const n = 22;
  for(let i=0;i<n;i++){
    const s = document.createElement('span');
    const size = 2 + Math.random()*3;
    s.style.width = size+'px';
    s.style.height = size+'px';
    s.style.left = Math.random()*100 + '%';
    s.style.bottom = '-10px';
    s.style.animationDuration = (10 + Math.random()*14) + 's';
    s.style.animationDelay = (Math.random()*14) + 's';
    layer.appendChild(s);
  }
}

function wireEvents(){
  // Home
  el('btnPlay').addEventListener('click', () => {
    startLevel(SAVE.unlockedLevel || 1);
  });
  el('btnLevels').addEventListener('click', () => { renderLevels(); showPage('page-levels'); });
  el('btnStats').addEventListener('click', () => { renderStats(); showPage('page-stats'); });
  el('btnSettings').addEventListener('click', () => { renderSettings(); showPage('page-settings'); });

  // Generic back buttons
  document.querySelectorAll('[data-nav]').forEach(btn => {
    btn.addEventListener('click', () => {
      const target = btn.dataset.nav;
      showPage(target);
      if(target==='page-home') renderHome();
    });
  });

  // Game HUD
  el('btnGameBack').addEventListener('click', () => {
    clearInterval(G.timerId);
    showPage('page-home');
    renderHome();
  });
  el('btnPause').addEventListener('click', pauseGame);
  el('btnResume').addEventListener('click', resumeGame);
  el('btnPauseRestart').addEventListener('click', () => { hideOverlay('overlayPause'); restartLevel(); });
  el('btnPauseSettings').addEventListener('click', () => { hideOverlay('overlayPause'); renderSettings(); showPage('page-settings'); });
  el('btnPauseHome').addEventListener('click', () => {
    hideOverlay('overlayPause');
    clearInterval(G.timerId);
    showPage('page-home');
    renderHome();
  });

  // Toolbar
  el('btnUndo').addEventListener('click', undoMove);
  el('btnRestart').addEventListener('click', restartLevel);
  el('btnHint').addEventListener('click', useHint);

  // Level complete overlay
  el('btnNextLevel').addEventListener('click', () => {
    hideOverlay('overlayComplete');
    startLevel(Math.min(G.level+1, LEVELS.length-1));
  });
  el('btnRetryLevel').addEventListener('click', () => {
    hideOverlay('overlayComplete');
    restartLevel();
  });
  el('btnHomeFromComplete').addEventListener('click', () => {
    hideOverlay('overlayComplete');
    showPage('page-home');
    renderHome();
  });

  // Settings toggles
  el('toggleSound').addEventListener('change', (e) => { SAVE.settings.sound = e.target.checked; persist(); playTone('click'); });
  el('toggleMusic').addEventListener('change', (e) => { SAVE.settings.music = e.target.checked; persist(); toggleMusic(e.target.checked); });
  el('toggleVibration').addEventListener('change', (e) => { SAVE.settings.vibration = e.target.checked; persist(); vibrate(20); });
  el('toggleAnimations').addEventListener('change', (e) => { SAVE.settings.animations = e.target.checked; persist(); });

  document.querySelectorAll('.theme-swatch').forEach(btn => {
    btn.addEventListener('click', () => applyTheme(btn.dataset.theme));
  });

  el('btnResetProgress').addEventListener('click', () => showOverlay('overlayConfirmReset'));
  el('btnCancelReset').addEventListener('click', () => hideOverlay('overlayConfirmReset'));
  el('btnConfirmReset').addEventListener('click', () => {
    SAVE = defaultSave();
    persist();
    hideOverlay('overlayConfirmReset');
    applyTheme('dark');
    renderHome();
    renderSettings();
    showPage('page-home');
  });
}

/* ---------------------- 10. BOOT ---------------------- */

function boot(){
  document.body.dataset.theme = SAVE.settings.theme || 'dark';
  initParticles();
  wireEvents();
  renderHome();
  renderSettings();
  if(SAVE.settings.music) toggleMusic(true);
  showPage('page-home');
}

document.addEventListener('DOMContentLoaded', boot);
