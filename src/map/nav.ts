/**
 * Ground-level navigation grid (2 m nodes) built from the 1 m raster.
 *
 * - floor: terrain, raised by low decks/curbs (solid touching the ground with top <= step_up above it)
 * - a 1 m cell is blocked if a solid overlaps the mech body (floor .. floor + height), or if a
 *   neighbour's floor differs by more than step_up (cliff/steep slope, treated as a wall both ways)
 * - clearance: approximate Euclidean distance (m) to the nearest blocked cell
 * - a 2 m node is walkable when clearance >= radius + margin
 */
import type { Raster } from "./raster.ts"

export type NavParams = { height: number; stepUp: number; minClear: number }

export class Nav {
  readonly r: Raster
  readonly nx: number // 2 m grid size
  readonly ny: number
  readonly floor: Float32Array // 1 m
  readonly clear: Float32Array // 1 m, metres
  readonly walk: Uint8Array // 2 m
  // A* scratch
  private g: Float32Array
  private parent: Int32Array
  private stamp: Uint32Array
  private closed: Uint32Array
  private gen = 0
  private heap: Int32Array
  private heapF: Float32Array
  private heapN = 0
  /** extra per-node cost multiplier (exposure, threat); 0 = none */
  readonly cost: Float32Array
  /** connected-component id per node (-1 = not walkable) and the id of the largest one */
  readonly comp: Int32Array
  main = 0

  /** Walkable and in the main connected area. */
  isMain(n: number): boolean { return n >= 0 && this.comp[n] === this.main }

  constructor(r: Raster, p: NavParams) {
    this.r = r
    const n1 = r.nx * r.ny
    this.floor = new Float32Array(n1)
    const blocked = new Uint8Array(n1)
    for (let c = 0; c < n1; c++) {
      const g = r.ground[c]
      let f = g
      if (r.s1lo[c] <= g + 0.5 && r.s1hi[c] - g <= p.stepUp && r.s1hi[c] > f) f = r.s1hi[c]
      if (r.s2lo[c] <= g + 0.5 && r.s2hi[c] - g <= p.stepUp && r.s2hi[c] > f) f = r.s2hi[c]
      this.floor[c] = f
      const lo = f + 0.05, hi = f + p.height
      if ((r.s1lo[c] < hi && r.s1hi[c] > lo) || (r.s2lo[c] < hi && r.s2hi[c] > lo)) blocked[c] = 1
    }
    for (let j = 0; j < r.ny; j++) {
      for (let i = 0; i < r.nx; i++) {
        const c = j * r.nx + i
        if (i === 0 || j === 0 || i === r.nx - 1 || j === r.ny - 1) { blocked[c] = 1; continue }
        const f = this.floor[c]
        if (Math.abs(this.floor[c + 1] - f) > p.stepUp || Math.abs(this.floor[c - 1] - f) > p.stepUp ||
            Math.abs(this.floor[c + r.nx] - f) > p.stepUp || Math.abs(this.floor[c - r.nx] - f) > p.stepUp) blocked[c] = 1
      }
    }
    this.clear = chamfer(blocked, r.nx, r.ny)
    this.nx = Math.floor((r.nx - 1) / 2) + 1
    this.ny = Math.floor((r.ny - 1) / 2) + 1
    const n2 = this.nx * this.ny
    this.walk = new Uint8Array(n2)
    for (let J = 0; J < this.ny; J++)
      for (let I = 0; I < this.nx; I++)
        this.walk[J * this.nx + I] = this.clear[2 * J * r.nx + 2 * I] >= p.minClear ? 1 : 0
    // connected components (4-neighbour); `main` is the largest
    this.comp = new Int32Array(n2).fill(-1)
    let bestSize = 0
    for (let s = 0, id = 0; s < n2; s++) {
      if (!this.walk[s] || this.comp[s] >= 0) continue
      let size = 0
      const stack = [s]
      this.comp[s] = id
      while (stack.length) {
        const u = stack.pop()!
        size++
        const ui = u % this.nx, uj = (u - ui) / this.nx
        if (ui > 0 && this.walk[u - 1] && this.comp[u - 1] < 0) { this.comp[u - 1] = id; stack.push(u - 1) }
        if (ui < this.nx - 1 && this.walk[u + 1] && this.comp[u + 1] < 0) { this.comp[u + 1] = id; stack.push(u + 1) }
        if (uj > 0 && this.walk[u - this.nx] && this.comp[u - this.nx] < 0) { this.comp[u - this.nx] = id; stack.push(u - this.nx) }
        if (uj < this.ny - 1 && this.walk[u + this.nx] && this.comp[u + this.nx] < 0) { this.comp[u + this.nx] = id; stack.push(u + this.nx) }
      }
      if (size > bestSize) { bestSize = size; this.main = id }
      id++
    }
    this.g = new Float32Array(n2)
    this.parent = new Int32Array(n2)
    this.stamp = new Uint32Array(n2)
    this.closed = new Uint32Array(n2)
    this.heap = new Int32Array(n2 * 2)
    this.heapF = new Float32Array(n2 * 2)
    this.cost = new Float32Array(n2)
  }

  nodeAt(x: number, y: number): number {
    const I = Math.round((x - this.r.minX) / 2), J = Math.round((y - this.r.minY) / 2)
    if (I < 0 || J < 0 || I >= this.nx || J >= this.ny) return -1
    return J * this.nx + I
  }
  nodeX(n: number): number { return this.r.minX + 2 * (n % this.nx) }
  nodeY(n: number): number { return this.r.minY + 2 * Math.floor(n / this.nx) }

  /** Nearest walkable node within `rad` nodes (spiral search), or -1. */
  nearestWalkable(x: number, y: number, rad = 10, mainOnly = true): number {
    const I0 = Math.round((x - this.r.minX) / 2), J0 = Math.round((y - this.r.minY) / 2)
    let best = -1, bd = Infinity
    for (let dJ = -rad; dJ <= rad; dJ++) for (let dI = -rad; dI <= rad; dI++) {
      const I = I0 + dI, J = J0 + dJ
      if (I < 0 || J < 0 || I >= this.nx || J >= this.ny) continue
      const n = J * this.nx + I
      if (!this.walk[n] || (mainOnly && this.comp[n] !== this.main)) continue
      const d = dI * dI + dJ * dJ
      if (d < bd) { bd = d; best = n }
    }
    return best
  }

  /**
   * A* from node s to node t, at most `budget` expansions. Returns the node path (s..t), or the
   * path to the expanded node closest to t when the budget runs out; null if s is invalid.
   */
  astar(s: number, t: number, budget = 20000): { path: number[]; complete: boolean; expanded: number } | null {
    if (s < 0 || !this.walk[s]) return null
    const gen = ++this.gen
    const nx = this.nx, tx = t % nx, ty = Math.floor(t / nx)
    const g = this.g, par = this.parent, st = this.stamp, cl = this.closed, walk = this.walk, cost = this.cost
    this.heapN = 0
    g[s] = 0; par[s] = -1; st[s] = gen
    const h = (n: number) => {
      const dx = Math.abs((n % nx) - tx), dy = Math.abs(Math.floor(n / nx) - ty)
      return 2 * (Math.max(dx, dy) + 0.41421356 * Math.min(dx, dy))
    }
    this.push(s, h(s))
    let best = s, bestH = h(s), expanded = 0
    while (this.heapN > 0 && expanded < budget) {
      const u = this.pop()
      if (cl[u] === gen) continue
      cl[u] = gen
      expanded++
      if (u === t) return { path: this.trace(u), complete: true, expanded }
      const hu = h(u)
      if (hu < bestH) { bestH = hu; best = u }
      const ui = u % nx, uj = (u - ui) / nx
      for (let k = 0; k < 8; k++) {
        const di = DI[k], dj = DJ[k]
        const vi = ui + di, vj = uj + dj
        if (vi < 0 || vj < 0 || vi >= nx || vj >= this.ny) continue
        const v = vj * nx + vi
        if (!walk[v] || cl[v] === gen) continue
        if (di !== 0 && dj !== 0 && (!walk[uj * nx + vi] || !walk[vj * nx + ui])) continue // no corner cutting
        const ng = g[u] + STEP[k] * (1 + cost[v])
        if (st[v] !== gen || ng < g[v]) {
          st[v] = gen; g[v] = ng; par[v] = u
          this.push(v, ng + h(v))
        }
      }
    }
    return { path: this.trace(best), complete: false, expanded }
  }

  private trace(n: number): number[] {
    const out: number[] = []
    for (let u = n; u !== -1; u = this.parent[u]) out.push(u)
    return out.reverse()
  }

  private push(n: number, f: number): void {
    let i = this.heapN++
    const H = this.heap, F = this.heapF
    while (i > 0) {
      const p = (i - 1) >> 1
      if (F[p] <= f) break
      H[i] = H[p]; F[i] = F[p]; i = p
    }
    H[i] = n; F[i] = f
  }

  private pop(): number {
    const H = this.heap, F = this.heapF
    const top = H[0]
    const n = --this.heapN
    const ln = H[n], lf = F[n]
    let i = 0
    for (;;) {
      let c = 2 * i + 1
      if (c >= n) break
      if (c + 1 < n && F[c + 1] < F[c]) c++
      if (F[c] >= lf) break
      H[i] = H[c]; F[i] = F[c]; i = c
    }
    H[i] = ln; F[i] = lf
    return top
  }
}

const DI = [1, -1, 0, 0, 1, 1, -1, -1]
const DJ = [0, 0, 1, -1, 1, -1, 1, -1]
const STEP = [2, 2, 2, 2, 2.828427, 2.828427, 2.828427, 2.828427]

/** Two-pass 3-4 chamfer distance transform (≈ Euclidean, metres on a 1 m grid). */
function chamfer(blocked: Uint8Array, nx: number, ny: number): Float32Array {
  const d = new Float32Array(nx * ny)
  const BIG = 1e6
  for (let c = 0; c < d.length; c++) d[c] = blocked[c] ? 0 : BIG
  for (let j = 0; j < ny; j++) for (let i = 0; i < nx; i++) {
    const c = j * nx + i
    let v = d[c]
    if (v === 0) continue
    if (i > 0) v = Math.min(v, d[c - 1] + 3)
    if (j > 0) {
      v = Math.min(v, d[c - nx] + 3)
      if (i > 0) v = Math.min(v, d[c - nx - 1] + 4)
      if (i < nx - 1) v = Math.min(v, d[c - nx + 1] + 4)
    }
    d[c] = v
  }
  for (let j = ny - 1; j >= 0; j--) for (let i = nx - 1; i >= 0; i--) {
    const c = j * nx + i
    let v = d[c]
    if (v === 0) continue
    if (i < nx - 1) v = Math.min(v, d[c + 1] + 3)
    if (j < ny - 1) {
      v = Math.min(v, d[c + nx] + 3)
      if (i < nx - 1) v = Math.min(v, d[c + nx + 1] + 4)
      if (i > 0) v = Math.min(v, d[c + nx - 1] + 4)
    }
    d[c] = v
  }
  for (let c = 0; c < d.length; c++) d[c] /= 3
  return d
}
