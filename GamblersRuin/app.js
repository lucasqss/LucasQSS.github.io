'use strict';

/* =====================================================================
 *  Gambler's Ruin com N apostadores
 *  - A cada rodada: sorteia 2 jogadores vivos, moeda honesta, o vencedor
 *    leva a aposta do perdedor. Quem zera sai do jogo.
 *  - O total de fichas é conservado; o jogo é uma martingale.
 * ===================================================================== */

const $ = (id) => document.getElementById(id);
const fmt = (n) => Math.round(n).toLocaleString('pt-BR');

/* ------------------------------ PRNG ------------------------------ */
function mulberry32(seed) {
  let a = seed | 0;
  return function () {
    a = (a + 0x6D2B79F5) | 0;
    let t = Math.imul(a ^ (a >>> 15), 1 | a);
    t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

/* ------------------------- Riqueza inicial ------------------------- */
// Retorna Int32Array com soma exata n * per (cada jogador com >= 1 ficha).
function initialWealth(n, per, mode, rng) {
  const w = new Int32Array(n);
  if (mode === 'equal') {
    w.fill(per);
    return w;
  }
  const extra = n * (per - 1);
  const weights = new Float64Array(n);
  let sum = 0;
  for (let i = 0; i < n; i++) {
    weights[i] = mode === 'ramp' ? i + 1 : -Math.log(1 - rng()); // Exp(1) => Dirichlet(1,…,1)
    sum += weights[i];
  }
  let given = 0;
  for (let i = 0; i < n; i++) {
    w[i] = 1 + Math.floor((extra * weights[i]) / sum);
    given += w[i] - 1;
  }
  // distribui o resto (arredondamento) para manter a soma exata
  let left = extra - given;
  if (mode === 'ramp') {
    for (let i = n - 1; left > 0; i = (i - 1 + n) % n, left--) w[i]++;
  } else {
    while (left-- > 0) w[Math.floor(rng() * n)]++;
  }
  return w;
}

/* --------------------------- Simulação ---------------------------- */
class Sim {
  constructor(w0, stakeMode, rng) {
    this.w = Int32Array.from(w0);
    this.n = w0.length;
    this.alive = [];
    this.total = 0;
    for (let i = 0; i < this.n; i++) {
      this.total += this.w[i];
      if (this.w[i] > 0) this.alive.push(i);
    }
    this.allin = stakeMode === 'allin';
    this.rng = rng;
    this.steps = 0;
  }

  get done() { return this.alive.length <= 1; }

  // executa até `k` rodadas (ou até o fim do jogo)
  run(k) {
    const { w, alive, rng, allin } = this;
    let steps = 0;
    while (steps < k && alive.length > 1) {
      const m = alive.length;
      const i = (rng() * m) | 0;
      let j = (rng() * (m - 1)) | 0;
      if (j >= i) j++;
      const a = alive[i], b = alive[j];
      const stake = allin ? Math.min(w[a], w[b]) : 1;
      let winner, loser, loserIdx;
      if (rng() < 0.5) { winner = a; loser = b; loserIdx = j; }
      else { winner = b; loser = a; loserIdx = i; }
      w[winner] += stake;
      w[loser] -= stake;
      if (w[loser] === 0) {
        alive[loserIdx] = alive[m - 1];
        alive.pop();
      }
      steps++;
    }
    this.steps += steps;
    return steps;
  }

  // métricas
  metrics() {
    const { w, n, total } = this;
    let max = 0, leader = 0, sq = 0;
    for (let i = 0; i < n; i++) {
      const v = w[i];
      if (v > max) { max = v; leader = i; }
      sq += v * v;
    }
    return { leader, max, share: max / total, neff: (total * total) / sq };
  }
}

/* --------------------------- Utilidades --------------------------- */
const hue = (i) => `hsl(${(i * 137.508) % 360} 72% 62%)`;

function niceTicks(max, count) {
  if (max <= 0) return [0];
  const raw = max / count;
  const mag = Math.pow(10, Math.floor(Math.log10(raw)));
  const norm = raw / mag;
  const step = (norm < 1.5 ? 1 : norm < 3 ? 2 : norm < 7 ? 5 : 10) * mag;
  const out = [];
  for (let v = 0; v <= max + step * 0.001; v += step) out.push(v);
  return out;
}

function compact(n) {
  if (n >= 1e9) return +(n / 1e9).toFixed(2) + ' bi';
  if (n >= 1e6) return +(n / 1e6).toFixed(2) + ' mi';
  if (n >= 1e4) return +(n / 1e3).toFixed(1) + ' mil';
  return String(Math.round(n * 100) / 100);
}

// prepara canvas para DPI/tamanho; devolve contexto em px CSS
function setupCanvas(cv) {
  const dpr = window.devicePixelRatio || 1;
  const w = cv.clientWidth, h = cv.clientHeight;
  if (cv.width !== Math.round(w * dpr) || cv.height !== Math.round(h * dpr)) {
    cv.width = Math.round(w * dpr);
    cv.height = Math.round(h * dpr);
  }
  const ctx = cv.getContext('2d');
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  ctx.clearRect(0, 0, w, h);
  return { ctx, w, h };
}

const CSS = {
  grid: '#262f3f',
  axis: '#8e99ad',
  text: '#c3cad8',
  accent: '#f5b942',
  accent2: '#4cc2ff',
};

/* ----------------------------- Estado ----------------------------- */
const MAX_SNAPS = 1200;

const S = {
  sim: null,
  w0: null,
  // histórico (decimado adaptativamente)
  every: 1,
  hSteps: [],
  hSnaps: [],
  hShare: [],
  maxEver: 1,
  playing: false,
  turbo: false,
  dirty: true,
  raf: 0,
  finished: false,
};

function readConfig() {
  const clamp = (v, lo, hi, d) => {
    v = parseInt(v, 10);
    if (!Number.isFinite(v)) v = d;
    return Math.min(hi, Math.max(lo, v));
  };
  return {
    n: clamp($('inN').value, 2, 100, 8),
    per: clamp($('inW').value, 1, 200, 20),
    init: $('inInit').value,
    stake: $('inStake').value,
    seed: parseInt($('inSeed').value, 10) || 0,
  };
}

function reset() {
  stopPlaying();
  const cfg = readConfig();
  $('inN').value = cfg.n;
  $('inW').value = cfg.per;
  const rngInit = mulberry32(cfg.seed ^ 0x5bd1e995);
  S.w0 = initialWealth(cfg.n, cfg.per, cfg.init, rngInit);
  S.sim = new Sim(S.w0, cfg.stake, mulberry32(cfg.seed));
  S.every = 1;
  S.hSteps = [];
  S.hSnaps = [];
  S.hShare = [];
  S.maxEver = Math.max(...S.w0);
  S.finished = false;
  $('banner').hidden = true;
  record();
  S.dirty = true;
  updateStats();
  requestDraw();
  // a configuração mudou: resultados de Monte Carlo antigos não valem mais
  stopMC();
  mc.counts = null;
  $('mcProgress').textContent = '';
  $('mcSummary').textContent = '';
  drawMC();
}

function record() {
  const sim = S.sim;
  S.hSteps.push(sim.steps);
  S.hSnaps.push(Int32Array.from(sim.w));
  S.hShare.push(sim.metrics().share);
  for (let i = 0; i < sim.n; i++) if (sim.w[i] > S.maxEver) S.maxEver = sim.w[i];
  if (S.hSteps.length >= MAX_SNAPS) { // decima por 2
    S.hSteps = S.hSteps.filter((_, i) => i % 2 === 0);
    S.hSnaps = S.hSnaps.filter((_, i) => i % 2 === 0);
    S.hShare = S.hShare.filter((_, i) => i % 2 === 0);
    S.every *= 2;
  }
}

/* Avança a simulação por até `budget` rodadas, respeitando um orçamento de tempo. */
function advance(budget, ms) {
  const sim = S.sim;
  const t0 = performance.now();
  while (budget > 0 && !sim.done) {
    const k = Math.min(budget, S.every - (sim.steps % S.every));
    const did = sim.run(k);
    budget -= did;
    if (sim.steps % S.every === 0) record();
    if (performance.now() - t0 > ms) break;
  }
  S.dirty = true;
  if (sim.done && !S.finished) finish();
}

function finish() {
  S.finished = true;
  stopPlaying();
  record();
  const sim = S.sim;
  const winner = sim.alive[0];
  const prob = (S.w0[winner] / sim.total) * 100;
  const b = $('banner');
  b.innerHTML =
    `<strong>Fim de jogo.</strong> O jogador <strong style="color:${hue(winner)}">#${winner + 1}</strong> ` +
    `ficou com <strong>${fmt(sim.total)}</strong> fichas (100%) depois de <strong>${fmt(sim.steps)}</strong> rodadas. ` +
    `Os outros ${sim.n - 1} quebraram. Chance inicial dele de ser o vencedor: ${prob.toFixed(1)}%.`;
  b.hidden = false;
  updateStats();
}

/* ------------------------------ Loop ------------------------------ */
function speedToSteps(v) { return Math.max(1, Math.round(Math.pow(10, (v / 100) * 6))); }

function loop() {
  S.raf = 0;
  if (!S.playing) return;
  if (S.turbo) advance(Infinity, 14);
  else advance(speedToSteps(+$('inSpeed').value), 14);
  updateStats();
  draw();
  if (S.playing) S.raf = requestAnimationFrame(loop);
}

function startPlaying() {
  if (S.sim.done) return;
  S.playing = true;
  $('btnPlay').textContent = '⏸ Pausar';
  if (!S.raf) S.raf = requestAnimationFrame(loop);
}

function stopPlaying() {
  S.playing = false;
  S.turbo = false;
  $('btnPlay').textContent = S.sim && S.sim.done ? '▶ Iniciar' : '▶ Continuar';
  if (S.raf) { cancelAnimationFrame(S.raf); S.raf = 0; }
}

let drawQueued = false;
function requestDraw() {
  if (drawQueued) return;
  drawQueued = true;
  requestAnimationFrame(() => { drawQueued = false; draw(); });
}

/* ---------------------------- Estatísticas ---------------------------- */
function updateStats() {
  const sim = S.sim;
  const m = sim.metrics();
  $('sSteps').textContent = fmt(sim.steps);
  $('sAlive').textContent = `${sim.alive.length} / ${sim.n}`;
  $('sLeader').textContent = '#' + (m.leader + 1);
  $('sLeader').style.color = hue(m.leader);
  $('sShare').textContent = (m.share * 100).toFixed(1) + '%';
  $('sNeff').textContent = m.neff.toFixed(2);
  $('sTotal').textContent = fmt(sim.total);
}

/* ------------------------------ Gráficos ------------------------------ */
function currentSeries() {
  // histórico + estado atual (se ele não coincide com o último snapshot)
  const sim = S.sim;
  const steps = S.hSteps.slice(), snaps = S.hSnaps.slice(), share = S.hShare.slice();
  if (steps[steps.length - 1] !== sim.steps) {
    steps.push(sim.steps);
    snaps.push(sim.w);
    share.push(sim.metrics().share);
  }
  return { steps, snaps, share };
}

function xTransform(logScale) {
  return logScale ? (s) => Math.log10(s + 1) : (s) => s;
}

function drawAxes(ctx, box, xmax, ymax, opts) {
  const { l, t, r, b } = box;
  ctx.font = '11px system-ui, sans-serif';
  ctx.lineWidth = 1;
  ctx.strokeStyle = CSS.grid;
  ctx.fillStyle = CSS.axis;
  // y
  ctx.textAlign = 'right';
  ctx.textBaseline = 'middle';
  for (const v of niceTicks(ymax, 5)) {
    const y = b - (v / ymax) * (b - t);
    ctx.beginPath(); ctx.moveTo(l, y + 0.5); ctx.lineTo(r, y + 0.5); ctx.stroke();
    ctx.fillText(opts.yFmt ? opts.yFmt(v) : compact(v), l - 6, y);
  }
  // x
  ctx.textAlign = 'center';
  ctx.textBaseline = 'top';
  if (opts.log) {
    for (let e = 0; e <= Math.floor(xmax); e++) {
      const x = l + (e / xmax) * (r - l);
      ctx.beginPath(); ctx.moveTo(x + 0.5, t); ctx.lineTo(x + 0.5, b); ctx.stroke();
      ctx.fillText(compact(Math.pow(10, e) - 1), x, b + 5);
    }
  } else {
    for (const v of niceTicks(xmax, 6)) {
      const x = l + (v / xmax) * (r - l);
      ctx.beginPath(); ctx.moveTo(x + 0.5, t); ctx.lineTo(x + 0.5, b); ctx.stroke();
      ctx.fillText(compact(v), x, b + 5);
    }
  }
  ctx.fillStyle = CSS.axis;
  ctx.textAlign = 'right';
  ctx.fillText('rodadas', r, b + 18);
}

function drawWealth() {
  const cv = $('cvWealth');
  const { ctx, w, h } = setupCanvas(cv);
  const box = { l: 52, t: 10, r: w - 12, b: h - 34 };
  const sim = S.sim;
  const { steps, snaps } = currentSeries();
  const log = $('inLog').checked;
  const tx = xTransform(log);
  const xmax = Math.max(tx(steps[steps.length - 1]), log ? 1 : 1);
  const ymax = Math.max(S.maxEver, sim.total / sim.n) * 1.05;
  drawAxes(ctx, box, xmax, ymax, { log });

  const X = (s) => box.l + (tx(s) / xmax) * (box.r - box.l);
  const Y = (v) => box.b - (v / ymax) * (box.b - box.t);
  const leader = sim.metrics().leader;
  const multi = sim.n <= 12;
  ctx.lineJoin = 'round';
  for (let pass = 0; pass < 2; pass++) {
    for (let p = 0; p < sim.n; p++) {
      const isLeader = p === leader;
      if ((pass === 0) === isLeader) continue;
      ctx.strokeStyle = hue(p);
      ctx.globalAlpha = isLeader ? 1 : multi ? 0.85 : 0.5;
      ctx.lineWidth = isLeader ? 2.4 : multi ? 1.5 : 1;
      ctx.beginPath();
      for (let k = 0; k < steps.length; k++) {
        const x = X(steps[k]), y = Y(snaps[k][p]);
        if (k === 0) ctx.moveTo(x, y); else ctx.lineTo(x, y);
      }
      ctx.stroke();
    }
  }
  ctx.globalAlpha = 1;
  // linha da média T/N
  const yAvg = Y(sim.total / sim.n);
  ctx.setLineDash([5, 4]);
  ctx.strokeStyle = '#ffffff55';
  ctx.beginPath(); ctx.moveTo(box.l, yAvg); ctx.lineTo(box.r, yAvg); ctx.stroke();
  ctx.setLineDash([]);
  ctx.fillStyle = '#c3cad8';
  ctx.textAlign = 'left';
  ctx.textBaseline = 'bottom';
  ctx.fillText('média T/N (nunca muda)', box.l + 6, yAvg - 3);
}

function drawBars() {
  const cv = $('cvBars');
  const { ctx, w, h } = setupCanvas(cv);
  const sim = S.sim;
  const box = { l: 44, t: 10, r: w - 8, b: h - 26 };
  let max = 1;
  for (let i = 0; i < sim.n; i++) if (sim.w[i] > max) max = sim.w[i];
  const ymax = max * 1.08;
  ctx.font = '11px system-ui, sans-serif';
  ctx.strokeStyle = CSS.grid;
  ctx.fillStyle = CSS.axis;
  ctx.textAlign = 'right';
  ctx.textBaseline = 'middle';
  for (const v of niceTicks(ymax, 4)) {
    const y = box.b - (v / ymax) * (box.b - box.t);
    ctx.beginPath(); ctx.moveTo(box.l, y + 0.5); ctx.lineTo(box.r, y + 0.5); ctx.stroke();
    ctx.fillText(compact(v), box.l - 6, y);
  }
  const slot = (box.r - box.l) / sim.n;
  const bw = Math.max(1, slot * 0.72);
  const showLabels = slot >= 22;
  ctx.textAlign = 'center';
  ctx.textBaseline = 'top';
  for (let i = 0; i < sim.n; i++) {
    const v = sim.w[i];
    const x = box.l + slot * i + (slot - bw) / 2;
    const bh = (v / ymax) * (box.b - box.t);
    ctx.fillStyle = v > 0 ? hue(i) : '#3a4457';
    ctx.fillRect(x, box.b - Math.max(bh, v > 0 ? 1 : 2), bw, Math.max(bh, v > 0 ? 1 : 2));
    if (showLabels) {
      ctx.fillStyle = v > 0 ? CSS.text : '#5b667a';
      ctx.fillText(String(i + 1), x + bw / 2, box.b + 5);
    }
  }
  if (!showLabels) {
    ctx.fillStyle = CSS.axis;
    ctx.fillText(`jogadores 1 … ${sim.n}`, (box.l + box.r) / 2, box.b + 5);
  }
}

function drawShare() {
  const cv = $('cvShare');
  const { ctx, w, h } = setupCanvas(cv);
  const box = { l: 44, t: 10, r: w - 12, b: h - 34 };
  const sim = S.sim;
  const { steps, share } = currentSeries();
  const log = $('inLog').checked;
  const tx = xTransform(log);
  const xmax = Math.max(tx(steps[steps.length - 1]), 1);
  drawAxes(ctx, box, xmax, 1, { log, yFmt: (v) => Math.round(v * 100) + '%' });
  const X = (s) => box.l + (tx(s) / xmax) * (box.r - box.l);
  const Y = (v) => box.b - v * (box.b - box.t);
  // 1/N
  ctx.setLineDash([5, 4]);
  ctx.strokeStyle = '#ffffff55';
  ctx.beginPath(); ctx.moveTo(box.l, Y(1 / sim.n)); ctx.lineTo(box.r, Y(1 / sim.n)); ctx.stroke();
  ctx.setLineDash([]);
  // curva
  ctx.strokeStyle = CSS.accent;
  ctx.lineWidth = 2;
  ctx.lineJoin = 'round';
  ctx.beginPath();
  for (let k = 0; k < steps.length; k++) {
    const x = X(steps[k]), y = Y(share[k]);
    if (k === 0) ctx.moveTo(x, y); else ctx.lineTo(x, y);
  }
  ctx.stroke();
  ctx.lineWidth = 1;
}

function draw() {
  if (!S.sim) return;
  drawWealth();
  drawBars();
  drawShare();
  S.dirty = false;
}

/* ------------------------------ Monte Carlo ------------------------------ */
const mc = { counts: null, done: 0, runs: 0, stepsSum: 0, running: false, raf: 0, cur: null, rng: null, w0: null, stake: 'unit' };

function startMC() {
  stopMC();
  const cfg = readConfig();
  const runs = Math.min(200000, Math.max(10, parseInt($('inRuns').value, 10) || 2000));
  $('inRuns').value = runs;
  mc.w0 = S.w0;
  mc.stake = cfg.stake;
  mc.runs = runs;
  mc.done = 0;
  mc.stepsSum = 0;
  mc.counts = new Float64Array(S.w0.length);
  mc.rng = mulberry32((cfg.seed ^ 0x9e3779b9) | 0);
  mc.cur = null;
  mc.running = true;
  $('btnMC').disabled = true;
  $('btnMCStop').disabled = false;
  mc.raf = requestAnimationFrame(tickMC);
}

function stopMC() {
  mc.running = false;
  if (mc.raf) { cancelAnimationFrame(mc.raf); mc.raf = 0; }
  $('btnMC').disabled = false;
  $('btnMCStop').disabled = true;
}

function tickMC() {
  mc.raf = 0;
  if (!mc.running) return;
  const t0 = performance.now();
  while (mc.done < mc.runs && performance.now() - t0 < 14) {
    if (!mc.cur) mc.cur = new Sim(mc.w0, mc.stake, mc.rng);
    mc.cur.run(100000);
    if (mc.cur.done) {
      mc.counts[mc.cur.alive[0]]++;
      mc.stepsSum += mc.cur.steps;
      mc.done++;
      mc.cur = null;
    }
  }
  drawMC();
  if (mc.done >= mc.runs) {
    stopMC();
  } else {
    mc.raf = requestAnimationFrame(tickMC);
  }
}

function drawMC() {
  const cv = $('cvMC');
  const { ctx, w, h } = setupCanvas(cv);
  const n = S.w0 ? S.w0.length : 0;
  const box = { l: 48, t: 10, r: w - 8, b: h - 26 };
  if (!mc.counts || !mc.done) {
    ctx.fillStyle = CSS.axis;
    ctx.font = '13px system-ui, sans-serif';
    ctx.textAlign = 'center';
    ctx.textBaseline = 'middle';
    ctx.fillText('Clique em "Rodar Monte Carlo" para comparar com a teoria.', w / 2, h / 2);
    if (mc.running) $('mcProgress').textContent = 'iniciando…';
    return;
  }
  const total = S.w0.reduce((a, b) => a + b, 0);
  const theo = Array.from(S.w0, (v) => v / total);
  const obs = Array.from(mc.counts, (c) => c / mc.done);
  let ymax = 0;
  for (let i = 0; i < n; i++) ymax = Math.max(ymax, theo[i], obs[i]);
  ymax *= 1.1;
  ctx.font = '11px system-ui, sans-serif';
  ctx.strokeStyle = CSS.grid;
  ctx.fillStyle = CSS.axis;
  ctx.textAlign = 'right';
  ctx.textBaseline = 'middle';
  for (const v of niceTicks(ymax, 4)) {
    const y = box.b - (v / ymax) * (box.b - box.t);
    ctx.beginPath(); ctx.moveTo(box.l, y + 0.5); ctx.lineTo(box.r, y + 0.5); ctx.stroke();
    ctx.fillText((v * 100).toFixed(v * 100 < 10 ? 1 : 0) + '%', box.l - 6, y);
  }
  const slot = (box.r - box.l) / n;
  const bw = Math.max(1, slot * 0.38);
  const showLabels = slot >= 22;
  ctx.textAlign = 'center';
  ctx.textBaseline = 'top';
  let maxDev = 0;
  for (let i = 0; i < n; i++) {
    const x0 = box.l + slot * i + slot / 2;
    const hObs = (obs[i] / ymax) * (box.b - box.t);
    const hTheo = (theo[i] / ymax) * (box.b - box.t);
    ctx.fillStyle = CSS.accent;
    ctx.fillRect(x0 - bw - 0.5, box.b - hObs, bw, hObs);
    ctx.fillStyle = CSS.accent2;
    ctx.fillRect(x0 + 0.5, box.b - hTheo, bw, hTheo);
    maxDev = Math.max(maxDev, Math.abs(obs[i] - theo[i]));
    if (showLabels) {
      ctx.fillStyle = CSS.text;
      ctx.fillText(String(i + 1), x0, box.b + 5);
    }
  }
  if (!showLabels) {
    ctx.fillStyle = CSS.axis;
    ctx.fillText(`jogadores 1 … ${n}`, (box.l + box.r) / 2, box.b + 5);
  }
  $('mcProgress').textContent = `${fmt(mc.done)} / ${fmt(mc.runs)} jogos`;
  $('mcSummary').textContent =
    `Todos os ${fmt(mc.done)} jogos terminaram com um único vencedor (100%). ` +
    `Maior desvio entre observado e teórico: ${(maxDev * 100).toFixed(2)} p.p. ` +
    `Duração média de um jogo: ${fmt(mc.stepsSum / Math.max(1, mc.done))} rodadas.`;
}

/* ------------------------------- Eventos ------------------------------- */
function bind() {
  ['inN', 'inW', 'inInit', 'inStake', 'inSeed'].forEach((id) => $(id).addEventListener('change', reset));
  $('btnSeed').addEventListener('click', () => {
    $('inSeed').value = Math.floor(Math.random() * 1e6);
    reset();
  });
  $('btnReset').addEventListener('click', reset);
  $('btnPlay').addEventListener('click', () => {
    if (S.playing) { stopPlaying(); return; }
    if (S.sim.done) reset();
    startPlaying();
  });
  $('btnStep').addEventListener('click', () => {
    stopPlaying();
    advance(1, 50);
    updateStats();
    draw();
  });
  $('btnEnd').addEventListener('click', () => {
    if (S.sim.done) return;
    S.turbo = true;
    startPlaying();
  });
  const showSpeed = () => {
    $('outSpeed').textContent = fmt(speedToSteps(+$('inSpeed').value)) + ' rodadas/quadro';
  };
  $('inSpeed').addEventListener('input', showSpeed);
  showSpeed();
  $('inLog').addEventListener('change', requestDraw);
  $('btnMC').addEventListener('click', startMC);
  $('btnMCStop').addEventListener('click', stopMC);
  let rt;
  window.addEventListener('resize', () => {
    clearTimeout(rt);
    rt = setTimeout(() => { draw(); drawMC(); }, 80);
  });
}

bind();
reset();
