import { run } from "./mechfight.ts"
import { Bot } from "./bot.ts"

run((hello) => new Bot(hello))
