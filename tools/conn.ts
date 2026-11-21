import { Raster } from "../src/map/raster.ts"
import { Nav } from "../src/map/nav.ts"
const r = Raster.fromMapDir("arena")
for (const mc of [3.0, 2.8, 2.6]) {
  const nav = new Nav(r, { height: 9, stepUp: 1.2, minClear: mc })
  const comp = new Int32Array(nav.walk.length).fill(-1); const sizes: number[] = []
  for (let s = 0; s < comp.length; s++) {
    if (!nav.walk[s] || comp[s] >= 0) continue
    const id = sizes.length; let n = 0; const st = [s]; comp[s] = id
    while (st.length) { const u = st.pop()!; n++; const ui = u % nav.nx, uj = (u - ui) / nav.nx
      for (const [di, dj] of [[1,0],[-1,0],[0,1],[0,-1]]) { const vi = ui + di, vj = uj + dj; if (vi < 0 || vj < 0 || vi >= nav.nx || vj >= nav.ny) continue; const v = vj * nav.nx + vi; if (nav.walk[v] && comp[v] < 0) { comp[v] = id; st.push(v) } } }
    sizes.push(n)
  }
  const main = sizes.indexOf(Math.max(...sizes)); const tot = sizes.reduce((a, b) => a + b, 0)
  const stad = nav.nodeAt(-221, 68), stad2 = nav.nodeAt(-280, 150)
  console.log(`minClear ${mc}: walkable ${tot}, main ${(100 * sizes[main] / tot).toFixed(1)}%, stadium(-221,68) ${nav.walk[stad] ? (comp[stad] === main ? "main" : "other") : "blocked"}, field(-280,150) ${nav.walk[stad2] ? (comp[stad2] === main ? "main" : "other") : "blocked"}`)
}
