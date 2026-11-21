import { readFileSync } from "node:fs"
import { gunzipSync } from "node:zlib"
import { Bot } from "../src/bot.ts"
const msgs = gunzipSync(readFileSync("test/stream.jsonl.gz")).toString("utf8").split("\n").filter(Boolean).map((l) => JSON.parse(l))
const hello = msgs[0]; hello.map.dir = "x"
const bot: any = new Bot(hello)
const base = msgs[1]
for (const p of [[0, 0], [-40, -170], [150, -60], [300, 100], [-250, 50]]) {
  const obs = structuredClone(base)
  obs.self.pos = [p[0], p[1], bot.r.groundAt(p[0], p[1])]
  obs.zone = { center: p, radius: 400, next_center: p, next_radius: 300, shrink_start: 60, shrink_end: 110, dps: 20 }
  bot.hold = null
  const t0 = performance.now()
  const h = bot.holdSpot(obs, obs.self.pos)
  console.log(p, "->", h && [h.x.toFixed(0), h.y.toFixed(0), "face", h.face.toFixed(2)], `${(performance.now() - t0).toFixed(1)} ms`)
}
