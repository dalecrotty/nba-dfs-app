// Lineup building in the browser (the private app). The same rules as the
// Python cruncher (src/dfs/crunch/optimise.py, captain.py), solved as a
// small integer programme by HiGHS (WebAssembly). One lineup per solve:
// the best legal lineup on the given numbers that differs from each
// earlier one by `minDiff`+ players (chalk d=3, the tested default), with
// locks, excludes, max per team and the owner's game stacks (a maximum:
// a lineup drawn from no more than maxGames games, optionally only from
// the games in `games`; nothing is forced from any game). `require`:
// [{ids, k}] = at least k of these players in the lineup (the stud method,
// owner 4 Nov 2026: 2 of the 4 studs and 3 of the 5 best values).
//
// pool: [{i, name, team, game, pos: ["PG","SG"], salary, mean}]
// rules: {cap, slots: {PG:2,...}, maxPerTeam, captain, captainMult, captainSalaryMult}
(function (root, factory) {
  if (typeof module === "object" && module.exports) module.exports = factory();
  else root.Lineup = factory();
})(typeof self !== "undefined" ? self : this, function () {
  const SLOT_ORDER = ["PG", "SG", "SF", "PF", "C"];

  function lp(pool, rules, opts) {
    const { locked = [], banned = new Set(), avoid = [], minDiff = 3, maxGames = null, games = null, maxPerTeam = null, require = [] } = opts || {};
    const lockedBy = new Map(locked.map(([i, s]) => [i, s]));
    const vars = [];                        // {name, i, slot, w}
    const cap = rules.captain;
    for (const p of pool) {
      if (banned.has(p.i) || !(p.mean > 0) && !lockedBy.has(p.i)) continue;
      if (games && games.size && !games.has(p.game) && !lockedBy.has(p.i)) continue;   // only the chosen games
      if (cap) {
        vars.push({ name: `c${p.i}`, i: p.i, slot: "CAP", w: rules.captainMult * p.mean, sal: rules.captainSalaryMult * p.salary });
        vars.push({ name: `f${p.i}`, i: p.i, slot: "FLEX", w: p.mean, sal: p.salary });
      } else {
        for (const s of p.pos) if (rules.slots[s]) vars.push({ name: `x${p.i}_${s}`, i: p.i, slot: s, w: p.mean, sal: p.salary });
      }
    }
    const byPlayer = new Map(), bySlot = new Map(), byTeam = new Map();
    const info = new Map(pool.map((p) => [p.i, p]));
    for (const v of vars) {
      (byPlayer.get(v.i) || byPlayer.set(v.i, []).get(v.i)).push(v);
      (bySlot.get(v.slot) || bySlot.set(v.slot, []).get(v.slot)).push(v);
      const t = info.get(v.i).team;
      (byTeam.get(t) || byTeam.set(t, []).get(t)).push(v);
    }
    const L = [];
    L.push("Maximize", " obj: " + vars.map((v) => `${v.w.toFixed(4)} ${v.name}`).join(" + "), "Subject To");
    let k = 0;
    const row = (expr, op, rhs) => L.push(` r${k++}: ${expr} ${op} ${rhs}`);
    for (const [, vs] of byPlayer) if (vs.length > 1) row(vs.map((v) => v.name).join(" + "), "<=", 1);
    const slots = cap ? { CAP: 1, FLEX: rules.slots.FLEX || 5 } : rules.slots;
    for (const s in slots) {
      const vs = bySlot.get(s) || [];
      if (vs.length < slots[s]) return null;   // not enough eligible players
      row(vs.map((v) => v.name).join(" + "), "=", slots[s]);
    }
    row(vars.map((v) => `${v.sal} ${v.name}`).join(" + "), "<=", rules.cap);
    const perTeam = Math.min(rules.maxPerTeam || 99, maxPerTeam || 99);
    for (const [, vs] of byTeam) row(vs.map((v) => v.name).join(" + "), "<=", perTeam);
    const size = Object.values(slots).reduce((a, b) => a + b, 0);
    for (const lu of avoid) {
      const vs = vars.filter((v) => lu.has(v.i));
      if (vs.length) row(vs.map((v) => v.name).join(" + "), "<=", size - minDiff);
    }
    for (const r of require) {               // at least k of these players
      const ids = r.ids instanceof Set ? r.ids : new Set(r.ids);
      const vs = vars.filter((v) => ids.has(v.i));
      if (r.k > 0 && vs.length === 0) return null;
      if (vs.length) row(vs.map((v) => v.name).join(" + "), ">=", r.k);
    }
    const gameVars = [];                     // y_g = 1 when any player of game g is used
    if (maxGames) {
      const byGame = new Map();
      for (const v of vars) { const g = info.get(v.i).game; (byGame.get(g) || byGame.set(g, []).get(g)).push(v); }
      let n = 0;
      for (const [g, vs] of byGame) {
        const y = `g${n++}`;
        gameVars.push(y);
        for (const [, pv] of Object.entries(Object.groupBy ? Object.groupBy(vs, (v) => v.i) : vs.reduce((m, v) => ((m[v.i] = m[v.i] || []).push(v), m), {})))
          row(pv.map((v) => v.name).join(" + ") + " - " + y, "<=", 0);
      }
      if (gameVars.length > maxGames) row(gameVars.join(" + "), "<=", maxGames);   // no more than maxGames games
    }
    L.push("Bounds");
    for (const y of gameVars) L.push(` 0 <= ${y} <= 1`);
    for (const v of vars) {
      const lk = lockedBy.get(v.i);
      if (lk !== undefined) L.push(` ${v.name} = ${lk === v.slot || (cap && lk === "ANY" && v.slot === "FLEX") ? 1 : 0}`);
      else L.push(` 0 <= ${v.name} <= 1`);
    }
    if (cap) for (const [i, lk] of lockedBy) if (lk === "ANY") {       // locked captain-or-flex: one of the two
      const vs = byPlayer.get(i) || [];
      L.splice(L.indexOf("Bounds"), 0, ` r${k++}: ${vs.map((v) => v.name).join(" + ")} = 1`);
      for (const v of vs) { const j = L.indexOf(` ${v.name} = ${v.slot === "FLEX" ? 1 : 0}`); if (j > 0) L[j] = ` 0 <= ${v.name} <= 1`; }
    }
    L.push("General", " " + vars.map((v) => v.name).concat(gameVars).join(" "), "End");
    return { text: L.join("\n"), vars };
  }

  // one lineup: [{i, slot}] in DraftStars slot order, or null
  function solveOne(highs, pool, rules, opts) {
    const built = lp(pool, rules, opts);
    if (!built) return null;
    let res;
    try { res = highs.solve(built.text, { mip_rel_gap: 0, time_limit: 20 }); } catch (e) { return null; }
    if (res.Status !== "Optimal") return null;
    const picked = built.vars.filter((v) => res.Columns[v.name] && res.Columns[v.name].Primal > 0.5).map((v) => ({ i: v.i, slot: v.slot }));
    const order = rules.captain ? { CAP: 0, FLEX: 1 } : Object.fromEntries(SLOT_ORDER.map((s, n) => [s, n]));
    picked.sort((a, b) => (order[a.slot] - order[b.slot]) || (a.i - b.i));
    return picked;
  }

  // chalk in order: n lineups, each differing from every earlier one by minDiff+
  function build(highs, pool, rules, n, opts) {
    const out = [];
    const o = Object.assign({ minDiff: 3 }, opts || {});
    for (let k = 0; k < n; k++) {
      const avoid = out.map((lu) => new Set(lu.map((x) => x.i)));
      let lu = solveOne(highs, pool, rules, Object.assign({}, o, { avoid }));
      if (!lu && (o.maxGames || o.games)) lu = solveOne(highs, pool, rules, Object.assign({}, o, { avoid, maxGames: null, games: null }));   // the stack can't hold: drop it
      if (!lu) break;
      out.push(lu);
    }
    return out;
  }

  // DraftStars' live swap (FINDINGS F21-F22): one player out, one in, in
  // every lineup holding the first and not the second, while it gains
  // minGain+ per lineup or takes out a player who is out. started: Set of
  // player i whose game has tipped (they stay and cannot come in). The
  // incoming player costs no more than the outgoing one (DraftStars' swap
  // rules, owner 23 Oct 2026).
  function bulkSwaps(pool, rules, lineups, started, outNow, minGain) {
    const info = new Map(pool.map((p) => [p.i, p]));
    const mean = (i) => (outNow.has(i) ? 0 : (info.get(i)?.mean || 0));
    const cur = lineups.map((lu) => lu.map((x) => ({ ...x })));
    const swaps = [];
    const legal = (lu, x, y, slot) => {
      const p = info.get(y);
      if (!p) return false;
      if (!rules.captain && !p.pos.includes(slot)) return false;
      const ids = lu.map((z) => z.i);
      const sal = ids.reduce((a, i) => a + (lu.find((z) => z.i === i).slot === "CAP" ? rules.captainSalaryMult : 1) * info.get(i).salary, 0)
        - (slot === "CAP" ? rules.captainSalaryMult : 1) * (info.get(x).salary - p.salary);
      if (sal > rules.cap) return false;
      const team = ids.filter((i) => i !== x && info.get(i).team === p.team).length + 1;
      return team <= (rules.maxPerTeam || 99);
    };
    for (let round = 0; round < 40; round++) {
      const held = new Set(cur.flatMap((lu) => lu.map((x) => x.i)).filter((i) => !started.has(i)));
      let best = null, bestGain = 1e-9;
      for (const x of held) {
        const hits = cur.map((lu, k) => [lu, k]).filter(([lu]) => lu.some((z) => z.i === x));
        for (const p of pool) {
          const y = p.i;
          if (started.has(y) || outNow.has(y) || y === x) continue;
          if (p.salary > (info.get(x)?.salary ?? 0)) continue;
          const step = mean(y) - mean(x);
          if (step <= 0 || (step < minGain && !outNow.has(x))) continue;
          const touched = [];
          for (const [lu, k] of hits) {
            if (lu.some((z) => z.i === y)) continue;
            const slot = lu.find((z) => z.i === x).slot;
            if (legal(lu, x, y, slot)) touched.push(k);
          }
          if (touched.length && step * touched.length > bestGain) { best = { x, y, touched, step }; bestGain = step * touched.length; }
        }
      }
      if (!best) break;
      for (const k of best.touched) cur[k] = cur[k].map((z) => (z.i === best.x ? { i: best.y, slot: z.slot } : z));
      swaps.push(best);
    }
    return { lineups: cur, swaps };
  }

  // every legal one-for-one replacement for player x across the given lineups
  // (owner, 3 Nov 2026: "this Swap function needs work"): same slot, salary no more
  // than his, game not started, lineup still under the cap and the team limit.
  // [{y, touched: [lineup k], step}] sorted by the incoming player's number.
  function replacements(pool, rules, lineups, x, started, outNow) {
    const info = new Map(pool.map((p) => [p.i, p]));
    const px = info.get(x); if (!px) return [];
    const mean = (i) => (outNow.has(i) ? 0 : (info.get(i)?.mean || 0));
    const out = [];
    for (const p of pool) {
      const y = p.i;
      if (y === x || started.has(y) || outNow.has(y) || p.salary > px.salary) continue;
      const touched = [];
      lineups.forEach((lu, k) => {
        const z = lu.find((q) => q.i === x); if (!z || lu.some((q) => q.i === y)) return;
        if (!rules.captain && !p.pos.includes(z.slot)) return;
        const m = (q) => (q.slot === "CAP" ? rules.captainSalaryMult : 1);
        const sal = lu.reduce((a, q) => a + m(q) * (q.i === x ? p.salary : info.get(q.i).salary), 0);
        if (sal > rules.cap) return;
        if (lu.filter((q) => q.i !== x && info.get(q.i).team === p.team).length + 1 > (rules.maxPerTeam || 99)) return;
        touched.push(k);
      });
      if (touched.length) out.push({ y, touched, step: mean(y) - mean(x) });
    }
    return out.sort((a, b) => mean(b.y) - mean(a.y));
  }

  return { lp, solveOne, build, bulkSwaps, replacements, SLOT_ORDER };
});
