/**
 * 1 m raster of the static world (protocol §11).
 *
 * Cell (i, j) is centred on the terrain vertex x = minX + i, y = minY + j.
 * Each cell stores terrain height plus up to two solid intervals [lo, hi] from the prisms
 * (buildings, stadium, bridges). Used for line of sight, shot clearance and nav building.
 */
import { readFileSync } from "node:fs"
import { join } from "node:path"

export type Prism = { kind: string; base: number; top: number; ring: number[]; holes: number[][] | number[] }

export class Raster {
  readonly nx: number
  readonly ny: number
  readonly minX: number
  readonly minY: number
  /** terrain height (m) at each vertex */
  readonly ground: Float32Array
  /** solid intervals: lo1, hi1, lo2, hi2 per cell; lo > hi means empty */
  readonly s1lo: Float32Array
  readonly s1hi: Float32Array
  readonly s2lo: Float32Array
  readonly s2hi: Float32Array

  constructor(nx: number, ny: number, minX: number, minY: number, ground: Float32Array) {
    this.nx = nx
    this.ny = ny
    this.minX = minX
    this.minY = minY
    this.ground = ground
    const n = nx * ny
    this.s1lo = new Float32Array(n).fill(1e9)
    this.s1hi = new Float32Array(n).fill(-1e9)
    this.s2lo = new Float32Array(n).fill(1e9)
    this.s2hi = new Float32Array(n).fill(-1e9)
  }

  static fromMapDir(dir: string): Raster {
    const world = JSON.parse(readFileSync(join(dir, "v2", "world.json"), "utf8"))
    const t = world.terrain
    const buf = readFileSync(join(dir, "v2", "terrain.i16"))
    const n = t.nx * t.ny
    const ground = new Float32Array(n)
    for (let k = 0; k < n; k++) ground[k] = buf.readInt16LE(k * 2) * (t.scale ?? 0.01)
    const r = new Raster(t.nx, t.ny, t.minX, t.minY, ground)
    for (const p of world.prisms as Prism[]) r.addPrism(p)
    return r
  }

  /** Rasterize a prism: every cell whose centre is inside ring and outside holes gets [base, top]. */
  addPrism(p: Prism): void {
    const ring = p.ring
    const holes: number[][] = Array.isArray(p.holes?.[0]) ? (p.holes as number[][]) : p.holes && (p.holes as number[]).length ? [p.holes as number[]] : []
    let x0 = Infinity, y0 = Infinity, x1 = -Infinity, y1 = -Infinity
    for (let k = 0; k < ring.length; k += 2) {
      x0 = Math.min(x0, ring[k]); x1 = Math.max(x1, ring[k])
      y0 = Math.min(y0, ring[k + 1]); y1 = Math.max(y1, ring[k + 1])
    }
    const i0 = Math.max(0, Math.ceil(x0 - this.minX)), i1 = Math.min(this.nx - 1, Math.floor(x1 - this.minX))
    const j0 = Math.max(0, Math.ceil(y0 - this.minY)), j1 = Math.min(this.ny - 1, Math.floor(y1 - this.minY))
    for (let j = j0; j <= j1; j++) {
      const y = this.minY + j
      for (let i = i0; i <= i1; i++) {
        const x = this.minX + i
        if (!inPoly(ring, x, y)) continue
        let inHole = false
        for (const h of holes) if (inPoly(h, x, y)) { inHole = true; break }
        if (!inHole) this.addInterval(j * this.nx + i, p.base, p.top)
      }
    }
  }

  private addInterval(c: number, lo: number, hi: number): void {
    if (this.s1lo[c] > this.s1hi[c]) { this.s1lo[c] = lo; this.s1hi[c] = hi; return }
    if (overlaps(this.s1lo[c], this.s1hi[c], lo, hi)) {
      this.s1lo[c] = Math.min(this.s1lo[c], lo); this.s1hi[c] = Math.max(this.s1hi[c], hi); return
    }
    if (this.s2lo[c] > this.s2hi[c]) { this.s2lo[c] = lo; this.s2hi[c] = hi; return }
    // third interval: merge into the nearer one (rare; conservative)
    this.s2lo[c] = Math.min(this.s2lo[c], lo); this.s2hi[c] = Math.max(this.s2hi[c], hi)
  }

  cellOf(x: number, y: number): number {
    const i = Math.round(x - this.minX), j = Math.round(y - this.minY)
    if (i < 0 || j < 0 || i >= this.nx || j >= this.ny) return -1
    return j * this.nx + i
  }

  /** Bilinear terrain height. */
  groundAt(x: number, y: number): number {
    const fx = Math.min(Math.max(x - this.minX, 0), this.nx - 1.001)
    const fy = Math.min(Math.max(y - this.minY, 0), this.ny - 1.001)
    const i = fx | 0, j = fy | 0, u = fx - i, v = fy - j
    const g = this.ground, k = j * this.nx + i
    return (g[k] * (1 - u) + g[k + 1] * u) * (1 - v) + (g[k + this.nx] * (1 - u) + g[k + this.nx + 1] * u) * v
  }

  /** Is the point inside terrain or a solid? */
  solidAt(x: number, y: number, z: number): boolean {
    const c = this.cellOf(x, y)
    if (c < 0) return true
    if (z < this.ground[c]) return true
    return (z >= this.s1lo[c] && z <= this.s1hi[c]) || (z >= this.s2lo[c] && z <= this.s2hi[c])
  }

  /**
   * Line of sight between two points: false if terrain or a solid blocks the segment.
   * Samples every `step` m (default 0.5); endpoints themselves are not tested.
   */
  los(ax: number, ay: number, az: number, bx: number, by: number, bz: number, step = 0.5): boolean {
    const dx = bx - ax, dy = by - ay, dz = bz - az
    const len = Math.sqrt(dx * dx + dy * dy + dz * dz)
    const n = Math.ceil(len / step)
    if (n <= 1) return true
    const nx = this.nx, mx = this.minX, my = this.minY, g = this.ground
    const a1 = this.s1lo, b1 = this.s1hi, a2 = this.s2lo, b2 = this.s2hi
    const inv = 1 / n
    for (let k = 1; k < n; k++) {
      const t = k * inv
      const x = ax + dx * t, y = ay + dy * t, z = az + dz * t
      const i = Math.round(x - mx), j = Math.round(y - my)
      if (i < 0 || j < 0 || i >= nx || j >= this.ny) return false
      const c = j * nx + i
      if (z < g[c]) return false
      if (z >= a1[c] && z <= b1[c]) return false
      if (z >= a2[c] && z <= b2[c]) return false
    }
    return true
  }
}

function overlaps(a0: number, a1: number, b0: number, b1: number): boolean {
  return a0 <= b1 + 0.01 && b0 <= a1 + 0.01
}

/** Even-odd point-in-polygon on a flat [x0, y0, x1, y1, ...] ring. */
export function inPoly(r: number[], x: number, y: number): boolean {
  let inside = false
  const n = r.length
  for (let a = 0, b = n - 2; a < n; b = a, a += 2) {
    const ya = r[a + 1], yb = r[b + 1]
    if (ya > y !== yb > y) {
      const xa = r[a], xb = r[b]
      if (x < ((xb - xa) * (y - ya)) / (yb - ya) + xa) inside = !inside
    }
  }
  return inside
}
