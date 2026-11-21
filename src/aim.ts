/** Firing solutions: gun lead (straight projectile) and mortar arcs (gravity). */
import type { Raster } from "./map/raster.ts"
import type { V3 } from "./util.ts"

/**
 * Where to aim a straight projectile (speed s) so it meets a target at p moving at v.
 * `delay` adds time before the shot leaves (decision latency). If `grav` > 0 the target is
 * airborne and falls; its height is clamped at `floorZ`.
 */
export function lead(m: V3, p: V3, v: V3, s: number, delay: number, grav = 0, floorZ = -1e9): { pt: V3; t: number } {
  let t = 0
  let pt: V3 = [p[0], p[1], p[2]]
  for (let k = 0; k < 4; k++) {
    const tt = t + delay
    let z = p[2] + v[2] * tt - 0.5 * grav * tt * tt
    if (z < floorZ) z = floorZ
    pt = [p[0] + v[0] * tt, p[1] + v[1] * tt, z]
    t = Math.hypot(pt[0] - m[0], pt[1] - m[1], pt[2] - m[2]) / s
  }
  return { pt, t }
}

/** [yaw, pitch] from a to b. */
export function aimAt(a: V3, b: V3): [number, number] {
  const dx = b[0] - a[0], dy = b[1] - a[1], dz = b[2] - a[2]
  return [Math.atan2(dy, dx), Math.atan2(dz, Math.hypot(dx, dy))]
}

/** Mortar pitch for horizontal distance x and height difference dz; null if out of range. */
export function mortarPitch(x: number, dz: number, v: number, g: number, high: boolean): number | null {
  const v2 = v * v
  const disc = v2 * v2 - g * (g * x * x + 2 * dz * v2)
  if (disc < 0) return null
  const r = Math.sqrt(disc)
  return Math.atan((v2 + (high ? r : -r)) / (g * x))
}

/**
 * Mortar solution that leads a moving target. Returns yaw, pitch, flight time, or null.
 * Checks the arc for obstacles against the raster (the shell explodes on the first hit).
 */
export function mortarSolve(r: Raster, m: V3, p: V3, vel: V3, v: number, g: number, high: boolean, minPitch: number, maxPitch: number):
  { yaw: number; pitch: number; t: number } | null {
  let pt: V3 = [p[0], p[1], p[2]]
  let sol: { yaw: number; pitch: number; t: number } | null = null
  for (let k = 0; k < 4; k++) {
    const dx = pt[0] - m[0], dy = pt[1] - m[1]
    const x = Math.hypot(dx, dy)
    const pitch = mortarPitch(x, pt[2] - m[2], v, g, high)
    if (pitch === null || pitch < minPitch || pitch > maxPitch) return null
    const t = x / (v * Math.cos(pitch))
    sol = { yaw: Math.atan2(dy, dx), pitch, t }
    pt = [p[0] + vel[0] * t, p[1] + vel[1] * t, p[2]]
  }
  if (!sol) return null
  // obstacle check along the arc, stop 4 m short of the target
  const cy = Math.cos(sol.yaw), sy = Math.sin(sol.yaw), cp = Math.cos(sol.pitch), sp = Math.sin(sol.pitch)
  const n = 40
  for (let k = 1; k < n; k++) {
    const t = (sol.t * k) / n
    const hx = v * cp * t
    if (sol.t * v * cp - hx < 4) break
    const x = m[0] + cy * hx, y = m[1] + sy * hx, z = m[2] + v * sp * t - 0.5 * g * t * t
    if (r.solidAt(x, y, z)) return null
  }
  return sol
}
