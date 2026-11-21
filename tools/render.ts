/** Render the nav grid to PNG for eyeballing (node tools/render.ts out.png). */
import { writeFileSync } from "node:fs"
import { deflateSync } from "node:zlib"
import { Raster } from "../src/map/raster.ts"
import { Nav } from "../src/map/nav.ts"

const dir = new URL("../arena", import.meta.url).pathname.replace(/^\/([A-Za-z]:)/, "$1")
const r = Raster.fromMapDir(dir)
const nav = new Nav(r, { height: 9, stepUp: 1.2, minClear: 3.0 })

// connected components of walkable nodes
const comp = new Int32Array(nav.walk.length).fill(-1)
const sizes: number[] = []
for (let s = 0; s < comp.length; s++) {
  if (!nav.walk[s] || comp[s] >= 0) continue
  const id = sizes.length
  let n = 0
  const stack = [s]
  comp[s] = id
  while (stack.length) {
    const u = stack.pop()!
    n++
    const ui = u % nav.nx, uj = (u - ui) / nav.nx
    for (const [di, dj] of [[1, 0], [-1, 0], [0, 1], [0, -1]]) {
      const vi = ui + di, vj = uj + dj
      if (vi < 0 || vj < 0 || vi >= nav.nx || vj >= nav.ny) continue
      const v = vj * nav.nx + vi
      if (nav.walk[v] && comp[v] < 0) { comp[v] = id; stack.push(v) }
    }
  }
  sizes.push(n)
}
const main = sizes.indexOf(Math.max(...sizes))
const total = sizes.reduce((a, b) => a + b, 0)
console.log(`components: ${sizes.length}, largest ${(100 * sizes[main] / total).toFixed(1)}% of walkable; next: ${[...sizes].sort((a, b) => b - a).slice(1, 6).join(", ")}`)

// image at 1 px per metre, north up
const W = r.nx, H = r.ny
const px = new Uint8Array(W * H * 3)
for (let j = 0; j < H; j++) for (let i = 0; i < W; i++) {
  const c = j * W + i, o = ((H - 1 - j) * W + i) * 3
  const solid = r.s1hi[c] > r.s1lo[c]
  const n = Math.round(j / 2) * nav.nx + Math.round(i / 2)
  const g = Math.max(0, Math.min(255, 90 + r.ground[c] * 3))
  let rgb: number[]
  if (solid) rgb = r.s1lo[c] > r.ground[c] + 1 ? [200, 120, 40] : [70, 70, 90] // bridge vs building
  else if (nav.clear[c] < 1) rgb = [160, 30, 30] // blocked (cliff/step)
  else if (comp[n] === main) rgb = [g * 0.6, g, g * 0.6]
  else if (comp[n] >= 0) rgb = [220, 200, 0] // walkable but disconnected
  else rgb = [g * 0.8, g * 0.8, g * 0.8] // too tight for the mech
  px.set(rgb, o)
}
const out = process.argv[2] ?? "nav.png"
writeFileSync(out, png(W, H, px))
console.log("wrote", out)

function png(w: number, h: number, rgb: Uint8Array): Buffer {
  const raw = Buffer.alloc((w * 3 + 1) * h)
  for (let y = 0; y < h; y++) { raw[y * (w * 3 + 1)] = 0; Buffer.from(rgb.buffer, y * w * 3, w * 3).copy(raw, y * (w * 3 + 1) + 1) }
  const crcT = new Int32Array(256).map((_, n) => { let c = n; for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1; return c })
  const crc = (b: Buffer) => { let c = -1; for (const x of b) c = crcT[(c ^ x) & 255] ^ (c >>> 8); return (c ^ -1) >>> 0 }
  const chunk = (t: string, d: Buffer) => { const l = Buffer.alloc(4); l.writeUInt32BE(d.length); const td = Buffer.concat([Buffer.from(t), d]); const c = Buffer.alloc(4); c.writeUInt32BE(crc(td)); return Buffer.concat([l, td, c]) }
  const ih = Buffer.alloc(13); ih.writeUInt32BE(w, 0); ih.writeUInt32BE(h, 4); ih[8] = 8; ih[9] = 2
  return Buffer.concat([Buffer.from([137, 80, 78, 71, 13, 10, 26, 10]), chunk("IHDR", ih), chunk("IDAT", deflateSync(raw)), chunk("IEND", Buffer.alloc(0))])
}
