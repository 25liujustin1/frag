export type V2 = [number, number]
export type V3 = [number, number, number]

export const TAU = Math.PI * 2
export const clamp = (v: number, lo: number, hi: number) => (v < lo ? lo : v > hi ? hi : v)
export const hyp2 = (ax: number, ay: number, bx: number, by: number) => Math.hypot(bx - ax, by - ay)
export const dist2 = (a: number[], b: number[]) => Math.hypot(b[0] - a[0], b[1] - a[1])
export const dist3 = (a: number[], b: number[]) => Math.hypot(b[0] - a[0], b[1] - a[1], b[2] - a[2])
/** wrap an angle to (-π, π] */
export const wrap = (a: number) => {
  a = (a + Math.PI) % TAU
  if (a < 0) a += TAU
  return a - Math.PI
}
export const angDiff = (a: number, b: number) => Math.abs(wrap(a - b))
export const yawTo = (from: number[], to: number[]) => Math.atan2(to[1] - from[1], to[0] - from[0])

/** Small deterministic RNG (mulberry32), seeded from hello.seed. */
export class Rng {
  private s: number
  constructor(seed: number) { this.s = (seed >>> 0) || 1 }
  next(): number {
    let t = (this.s = (this.s + 0x6d2b79f5) >>> 0)
    t = Math.imul(t ^ (t >>> 15), t | 1)
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61)
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296
  }
  range(lo: number, hi: number): number { return lo + (hi - lo) * this.next() }
}

export const log = (...a: unknown[]) => { process.stderr.write(a.map(String).join(" ") + "\n") }
