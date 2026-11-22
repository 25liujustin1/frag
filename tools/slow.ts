import { readFileSync } from "node:fs"
import { gunzipSync } from "node:zlib"
import { Bot } from "../src/bot.ts"
const msgs = gunzipSync(readFileSync("test/stream.jsonl.gz")).toString("utf8").split("\n").filter(Boolean).map((l) => JSON.parse(l))
const hello = msgs[0]; hello.map.dir = "x"
const bot: any = new Bot(hello)
for (const m of msgs) {
  if (m.type !== "obs") continue
  const pt0 = bot.pathT
  const t0 = performance.now(); bot.act(m); const dt = performance.now() - t0
  if (dt > 5) console.log(`tick ${m.tick} t ${m.t} ${dt.toFixed(1)} ms mode ${bot.mode} replanned ${bot.pathT !== pt0} partial ${bot.pathPartial} pathLen ${bot.path.length} dynClear ${bot.nav.dynClear.toFixed(2)} cubes ${m.self.cubes}`)
}
