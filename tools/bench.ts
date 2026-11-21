/** Build the raster + nav grid and time line-of-sight and A* (run: node tools/bench.ts). */
import { Raster } from "../src/map/raster.ts"
import { Nav } from "../src/map/nav.ts"

const dir = new URL("../arena", import.meta.url).pathname.replace(/^\/([A-Za-z]:)/, "$1")
let t0 = performance.now()
const r = Raster.fromMapDir(dir)
console.log(`raster: ${(performance.now() - t0).toFixed(0)} ms (${r.nx}x${r.ny})`)
t0 = performance.now()
const nav = new Nav(r, { height: 9, stepUp: 1.2, minClear: 3.0 })
let walk = 0
for (const w of nav.walk) walk += w
console.log(`nav: ${(performance.now() - t0).toFixed(0)} ms, ${nav.nx}x${nav.ny} nodes, walkable ${(100 * walk / nav.walk.length).toFixed(1)}%`)

// deterministic RNG
let s = 12345
const rnd = () => ((s = (s * 1103515245 + 12345) >>> 0) / 4294967296)
const walkable: number[] = []
nav.walk.forEach((w, n) => { if (w) walkable.push(n) })
const pick = () => walkable[Math.floor(rnd() * walkable.length)]

// LOS: eye (z+8) to target centre (z+4.5), random pairs up to 200 m apart
const N = 20000
const pairs: number[][] = []
while (pairs.length < N) {
  const a = pick(), b = pick()
  const ax = nav.nodeX(a), ay = nav.nodeY(a), bx = nav.nodeX(b), by = nav.nodeY(b)
  if (Math.hypot(bx - ax, by - ay) > 200) continue
  pairs.push([ax, ay, r.groundAt(ax, ay) + 8, bx, by, r.groundAt(bx, by) + 4.5])
}
for (let rep = 0; rep < 2; rep++) {
  t0 = performance.now()
  let vis = 0
  for (const p of pairs) if (r.los(p[0], p[1], p[2], p[3], p[4], p[5])) vis++
  const dt = performance.now() - t0
  console.log(`los x${N}: ${dt.toFixed(1)} ms => ${(1000 * dt / N).toFixed(2)} µs/ray, visible ${(100 * vis / N).toFixed(0)}%`)
}

// A*: random pairs 100-500 m apart
const times: number[] = []
let incomplete = 0, totalExp = 0
for (let k = 0; k < 300; k++) {
  const a = pick(), b = pick()
  const d = Math.hypot(nav.nodeX(b) - nav.nodeX(a), nav.nodeY(b) - nav.nodeY(a))
  if (d < 100 || d > 500) { k--; continue }
  const t = performance.now()
  const res = nav.astar(a, b, 20000)!
  times.push(performance.now() - t)
  totalExp += res.expanded
  if (!res.complete) incomplete++
}
times.sort((x, y) => x - y)
const q = (f: number) => times[Math.floor(f * (times.length - 1))].toFixed(2)
console.log(`A* (20k budget) x${times.length}: median ${q(0.5)} ms, p90 ${q(0.9)} ms, max ${q(1)} ms, avg expansions ${(totalExp / times.length).toFixed(0)}, hit budget ${incomplete}`)
