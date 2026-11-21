/** Feed the kit's recorded match through the bot in-process: catches exceptions, times act(). */
import { readFileSync } from "node:fs"
import { gunzipSync } from "node:zlib"
import { Bot } from "../src/bot.ts"

const file = process.argv[2] ?? new URL("../test/stream.jsonl.gz", import.meta.url).pathname.replace(/^\/([A-Za-z]:)/, "$1")
const msgs = gunzipSync(readFileSync(file)).toString("utf8").split("\n").filter(Boolean).map((l) => JSON.parse(l))
const hello = msgs[0]
hello.map.dir = "nonexistent" // force the bundled map
let t0 = performance.now()
const bot = new Bot(hello)
console.log(`init ${(performance.now() - t0).toFixed(0)} ms`)
const times: number[] = []
const modes = new Map<string, number>()
let fired = 0, errors = 0
for (const m of msgs) {
  if (m.type !== "obs") continue
  t0 = performance.now()
  let a: any
  try { a = bot.act(m) } catch (e) { errors++; if (errors < 4) console.error(e); continue }
  times.push(performance.now() - t0)
  const line = JSON.stringify({ ...a, tick: m.tick })
  for (const v of [...(a.move ?? []), ...(a.aim ?? [])]) if (!Number.isFinite(v)) throw new Error("non-finite in " + line)
  if (a.fire?.some(Boolean)) fired++
  const mode = (bot as any).mode
  modes.set(mode, (modes.get(mode) ?? 0) + 1)
  if (m.tick % 100 === 0) console.log(m.t.toFixed(1), line.slice(0, 160))
}
times.sort((a, b) => a - b)
const q = (f: number) => times[Math.floor(f * (times.length - 1))].toFixed(2)
console.log(`act x${times.length}: median ${q(0.5)} ms p99 ${q(0.99)} ms max ${q(1)} ms; errors ${errors}; fired on ${fired}; modes`, Object.fromEntries(modes))
