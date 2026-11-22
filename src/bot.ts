/**
 * M1 bot: zone rotation on a nav grid, loot, lead-aim combat with all four weapons,
 * jinking, range bands by loadout, retreat to cover at low HP, stuck recovery.
 */
import { existsSync, readFileSync } from "node:fs"
import { fileURLToPath } from "node:url"
import { draw, type Action, type ActorObs, type Hello, type Observation, type WeaponObs } from "./mechfight.ts"
import { Raster } from "./map/raster.ts"
import { Nav } from "./map/nav.ts"
import { aimAt, lead, mortarSolve } from "./aim.ts"
import { angDiff, clamp, dist2, dist3, log, Rng, wrap, yawTo, type V2, type V3 } from "./util.ts"

const LOWER_BETTER = new Set(["cooldown", "charge", "boost_drain", "jet_drain", "reload", "hearing", "regen_delay"])
const COUNTERS: Record<string, string> = { laser: "mortar", mortar: "lightning", lightning: "laser" }
const ROOT = fileURLToPath(new URL("..", import.meta.url))
const P = { ...JSON.parse(readFileSync(ROOT + "params.json", "utf8")), ...JSON.parse(process.env.BOT_PARAMS ?? "{}") }

type Track = { id: number; pos: V3; vel: V3; aim: V2; hp: number; maxHp: number; cubes: number; weapons: string[]; charging: boolean; seenT: number; hitUsT: number; weHitT: number; watchT: number }

export class Bot {
  name: string = P.name
  private hello: Hello
  private r: Raster
  private nav: Nav
  private rng: Rng
  private tracks = new Map<number, Track>()
  private pickups = new Map<number, { kind: string; pos: V3 }>()
  // path following
  private path: number[] = []
  private pathIdx = 0
  private pathGoalNode = -1
  private pathT = -99
  private pathPartial = false
  private crates = new Map<number, V3>()
  private cubeMem = new Map<number, V3>()
  private climbId = -1
  private climbT = 0
  private badLoot = new Set<number>()
  private scoutT = -99
  private scoutUntil = -1
  private scoutZ = 0
  private visited = new Map<string, number>()
  private explore: V3 | null = null
  private exploreT = -99
  // state
  private t = 0
  private stuckRef: V2 = [0, 0]
  private stuckRefT = 0
  private jumpUntil = -1
  private jinkSign = 1
  private jinkUntil = 0
  private lastDmgT = -99
  private lastDmgBearing = 0
  private retreating = false
  private escaping = false
  private curTarget = -1
  private pincerUntil = -1
  private flankT = -99
  private flankAim = 0
  private flankUntil = -1
  private islandCheckT = -99
  private offMain = false
  private islandGoal: V2 | null = null
  private islandDir: V2 | null = null
  private islandDirT = -99
  private islandFrom: V2 = [0, 0]
  private islandK = 0
  private islandClearZ = 0
  private islandTried = new Set<number>()
  private hasLight = false
  private fleeReplanT = -99
  private gunOnly = true
  private hitBy = new Map<number, number>()
  private targetSinceT = 0
  private lastShotT = 0
  private ignoreUntil = new Map<number, number>()
  private fleeing = false
  private fleeT = 0
  private fleeDest: V2 | null = null
  private lastHostileT = -99
  private checkNextT = 0
  private checkUntil = -1
  private checkAim = 0
  private unstickUntil = -1
  private unstickDir: V2 = [0, 0]
  private hideUntil = -1
  private otherEyes: V3[] = []
  private reserve = 25
  private threatCostT = -99
  private threatNodes: number[] = []
  private myRad = 2.5
  private jumpZ = 0
  private myKills = 0
  private survNow = false
  private coverAt: V2 | null = null
  private coverT = -99
  private soundContacts: { pos: V3; t: number }[] = []
  private zoneEdgeDist = 999
  private edgeBounds = { minX: -500, maxX: 500, minY: -300, maxY: 300 }
  private edgeDone = false
  private campAnchor: V2 | null = null
  private campT = 0
  ffa = false
  ffaT = -1
  private ambushing = false
  private spotCache: { t: number; tid: number; spot: V2 | null } | null = null
  private resetUntil = -1
  private burstT = 0
  private bursting = false
  private stuckAt: V2 | null = null
  private stuckAtT = -99
  private laserLostT = -1
  private sweep = 0
  private mode = "start"
  private hold: { x: number; y: number; face: number; key: string; t: number } | null = null
  private heardT = -99
  private heardBearing = 0

  constructor(hello: Hello) {
    this.hello = hello
    this.rng = new Rng(hello.seed)
    let dir = hello.map?.dir
    if (!dir || !existsSync(dir + "/v2/world.json")) dir = ROOT + "arena"
    const t0 = performance.now()
    this.r = Raster.fromMapDir(dir)
    this.edgeBounds = { minX: this.r.minX, maxX: this.r.minX + this.r.nx - 1, minY: this.r.minY, maxY: this.r.minY + this.r.ny - 1 }
    const m = hello.config.mech
    this.nav = new Nav(this.r, { height: m.height, stepUp: m.step_up, minClear: m.radius + 0.5 })
    log(`map ${dir} loaded in ${(performance.now() - t0).toFixed(0)} ms`)
    if (P.routeExpW > 0) this.buildExposure()
    this.warmup()
  }

  /** Static route cost: how open each spot is (fraction of 16 directions you can be seen from out to 100 m). */
  private buildExposure(): void {
    const nav = this.nav, r = this.r, t0 = performance.now()
    for (let J = 0; J < nav.ny; J += 2) for (let I = 0; I < nav.nx; I += 2) {
      const n = J * nav.nx + I
      if (!nav.walk[n]) continue
      const x = nav.nodeX(n), y = nav.nodeY(n), z = nav.floor[r.cellOf(x, y)] + 6
      let open = 0
      for (let q = 0; q < 16; q++) {
        const a = (q / 16) * Math.PI * 2
        if (r.los(x, y, z, x + Math.cos(a) * 100, y + Math.sin(a) * 100, z, 2)) open++
      }
      const c = (P.routeExpW * open) / 16
      for (let dj = 0; dj < 2; dj++) for (let di = 0; di < 2; di++) { const m = (J + dj) * nav.nx + I + di; if (I + di < nav.nx && J + dj < nav.ny) nav.expCost[m] = c }
    }
    log(`exposure map ${(performance.now() - t0).toFixed(0)} ms`)
  }

  /** Dynamic route cost: ground that any recently seen enemy can see (within 160 m of us), refreshed each second. */
  /** Bots seen with lightning in the last 10 s (only matters when we don't have lightning ourselves). */
  private lightCarriers(t: number): V3[] {
    if (!P.lightAvoid || this.hasLight) return []
    return [...this.tracks.values()].filter((tr) => tr.id < 100 && t - tr.seenT < 10 && tr.weapons.includes("lightning")).map((tr) => tr.pos)
  }

  private updateThreatCost(obs: Observation): void {
    const nav = this.nav
    if ((P.routeThreatW <= 0 && P.routeNearW <= 0 && !P.lightAvoid) || obs.t - this.threatCostT < 1) return
    this.threatCostT = obs.t
    for (const n of this.threatNodes) nav.threatCost[n] = 0
    this.threatNodes = []
    const eyes = [...this.tracks.values()].filter((tr) => tr.id < 100 && obs.t - tr.seenT < 10 && !this.isPassive(tr.id)).map((tr) => [tr.pos[0], tr.pos[1], tr.pos[2] + 8])
    const lights = this.lightCarriers(obs.t)
    if (!eyes.length && !lights.length) return
    const pos = obs.self.pos, r = this.r
    for (let dy = -160; dy <= 160; dy += 8) for (let dx = -160; dx <= 160; dx += 8) {
      if (dx * dx + dy * dy > 160 * 160) continue
      const x = pos[0] + dx, y = pos[1] + dy, n0 = nav.nodeAt(x, y)
      if (n0 < 0 || !nav.walk[n0]) continue
      const z = nav.floor[r.cellOf(x, y)] + 4.5
      let seen = false, nearest = Infinity
      for (const e of eyes) {
        const de = Math.hypot(e[0] - x, e[1] - y)
        if (de < nearest) nearest = de
        if (!seen && de < 230 && r.los(e[0], e[1], e[2], x, y, z, 1)) seen = true
      }
      // cost: in an enemy's sight line, plus closeness to any known enemy (keep routes away from bots)
      let cost = (seen ? P.routeThreatW : 0) + (nearest < P.routeNearR ? (P.routeNearW * (P.routeNearR - nearest)) / P.routeNearR : 0)
      for (const l of lights) if (Math.hypot(l[0] - x, l[1] - y) < P.lightAvoidR) { cost += P.lightAvoidW; break }
      if (cost <= 0) continue
      const I0 = n0 % nav.nx, J0 = (n0 - I0) / nav.nx
      for (let j = -2; j < 2; j++) for (let i = -2; i < 2; i++) {
        const I = I0 + i, J = J0 + j
        if (I < 0 || J < 0 || I >= nav.nx || J >= nav.ny) continue
        const m = J * nav.nx + I
        nav.threatCost[m] = cost
        this.threatNodes.push(m)
      }
    }
  }

  /** Exercise the hot paths so the JIT has compiled them before the first real decision. */
  private warmup(): void {
    const n = this.nav, r = this.r
    let s = 1
    for (let k = 0; k < 60; k++) {
      const a = n.nearestWalkable(r.minX + 100 + (k * 37) % 800, r.minY + 100 + (k * 53) % 500)
      const b = n.nearestWalkable(r.minX + 100 + (k * 91) % 800, r.minY + 100 + (k * 29) % 500)
      if (a >= 0 && b >= 0) s += n.astar(a, b, 5000)!.expanded
      for (let q = 0; q < 200; q++) if (r.los(n.nodeX(a), n.nodeY(a), 8, n.nodeX(b), n.nodeY(b), 4)) s++
    }
    if (s < 0) log(s)
  }

  act(obs: Observation): Omit<Action, "tick"> {
    const t = (this.t = obs.t)
    const me = obs.self
    const cfg = this.hello.config
    const pos = me.pos as V3
    const act: Omit<Action, "tick"> = {}

    this.updateTracks(obs)
    this.updateThreatCost(obs)
    this.otherEyes = [...this.tracks.values()].filter((tr) => tr.id < 100 && obs.t - tr.seenT < 8 && !this.isPassive(tr.id)).map((tr) => [tr.pos[0], tr.pos[1], tr.pos[2] + 8] as V3)
    {
      // energy reserve for escapes: grows with nearby threats and missing HP; optional boosts only spend above it
      const near = [...this.tracks.values()].filter((tr) => tr.id < 100 && obs.t - tr.seenT < 8 && dist2(tr.pos, obs.self.pos) < 150).length
      const hpGap = 1 - obs.self.hp / Math.max(1, obs.self.max_hp)
      this.reserve = P.dynReserve ? Math.min(85, P.energyReserve + P.reservePerThreat * near + P.reserveLowHp * hpGap) : P.energyReserve
    }
    {
      const cfgc = this.hello.config
      this.myRad = cfgc.mech.radius * (1 + (cfgc.cubes.size_per_cube ?? 0.05) * obs.self.cubes)
      const need = P.sizeAware ? this.myRad + 0.4 : 0
      if (need > this.nav.dynClear + 0.05) this.pathT = -99 // we grew: replan through gaps we still fit
      this.nav.dynClear = need
    }
    for (const e of obs.events) {
      if (e.type === "damaged" && e.weapon !== "zone") {
        this.lastDmgT = t
        if (e.bearing != null) this.lastDmgBearing = e.bearing
        const tr = e.by != null ? this.tracks.get(e.by) : undefined
        if (tr) tr.hitUsT = t
        if (e.by != null) this.hitBy.set(e.by, t) // remember even if we haven't seen the shooter yet
        // flank alarm: shot by a bot we can't see right now -> look toward the shot (once per 2 s)
        if (P.flankLook && e.bearing != null && !obs.mechs.some((m) => m.id === e.by) && t - this.flankT > P.flankEvery && e.weapon !== "npc") {
          this.flankT = t; this.flankAim = e.bearing; this.flankUntil = t + P.flankDur
        }
      } else if (e.type === "hit") {
        const tr = this.tracks.get(e.target)
        if (tr) tr.weHitT = t
      } else if (e.type === "took" || e.type === "dropped") {
        if (e.type === "took") this.pickups.delete(e.id)
      }
    }
    if (obs.offer) act.pick = this.pickUpgrade(obs.offer.choices.map((c) => c.id), me.weapons)
    // ---- which game is this? In practice the house squad never kills itself, so before the zone can kill
    // anyone (~125 s) every death is ours. A mech dying that we didn't kill means a free-for-all (finals).
    for (const e of obs.events) if (e.type === "kill") this.myKills++
    // survivor mode: always (P.survivor), or switch to it late (time) or after enough kills (hybrid)
    this.survNow = !!P.survivor || t >= P.survAfterT || this.myKills >= P.survAfterKills
    if (!this.ffa && P.ffaDetect && t < P.ffaDetectT && obs.alive + this.myKills <= (this.hello.config.match.mechs ?? 16) - P.ffaDeaths) { this.ffa = true; this.ffaT = t }
    // sounds that suggest an approaching or firing mech (most recent, nearest band first)
    for (const s of obs.sounds) {
      if (!SOUND_THREAT.has(s.kind) || s.dist === "far") continue
      if (t - this.heardT > 1 || s.dist === "near") { this.heardT = t - s.age; this.heardBearing = s.bearing }
      // remember where the sound roughly came from (threat picture: flankers we can hear but not see)
      const r = s.dist === "near" ? 35 : 100
      this.soundContacts.push({ pos: [obs.self.pos[0] + Math.cos(s.bearing) * r, obs.self.pos[1] + Math.sin(s.bearing) * r, obs.self.pos[2]], t: t - s.age })
    }
    this.soundContacts = this.soundContacts.filter((s) => t - s.t < 8)
    {
      // distance to the current zone edge, and how long we've been fighting in the same area
      const zc = obs.zone.center, zr = obs.zone.radius
      this.zoneEdgeDist = zr - dist2(zc, obs.self.pos)
      const fighting = this.mode === "fight" || this.mode === "reposition" || this.mode === "retreat"
      if (fighting && this.campAnchor && dist2(this.campAnchor, obs.self.pos) < 30) this.campT += 0.1
      else if (fighting) { this.campAnchor = [obs.self.pos[0], obs.self.pos[1]]; this.campT = 0 }
      else this.campT = 0
    }

    // ---- weapons
    const slots = me.weapons
    const has = (k: string) => slots.findIndex((w) => w?.kind === k)
    const iGun = has("gun"), iLaser = has("laser"), iLight = has("lightning"), iMortar = has("mortar")
    const best = this.bestWeapon(slots)

    // ---- target selection
    // real muzzle (measured from 1,422 laser beams in recordings): radius*size + 0.4 m ahead along the aim, at
    // muzzle_height*size, where size = 1 + 5% per cube. Using a fixed 7 m made every shot fly high once we had cubes.
    let muzzle: V3 = [pos[0], pos[1], pos[2] + me.stats.muzzle_height]
    if (P.muzzleFix) {
      const cm = this.hello.config.mech as any, sz = 1 + ((this.hello.config as any).cubes?.size_per_cube ?? 0.05) * me.cubes
      const fwd = (cm.radius ?? 2.5) * sz + 0.4, cp = Math.cos(me.aim[1])
      muzzle = [pos[0] + Math.cos(me.aim[0]) * cp * fwd, pos[1] + Math.sin(me.aim[0]) * cp * fwd, pos[2] + (cm.muzzle_height ?? 7) * sz + Math.sin(me.aim[1]) * fwd]
    }
    const eye: V3 = [pos[0], pos[1], pos[2] + me.stats.eye_height]
    const enemies = obs.mechs.filter((m) => m.kind === "mech")
    const npcsAttacking = obs.mechs.filter((m) => m.kind === "npc" && (this.tracks.get(m.id)?.hitUsT ?? -99) > t - 4 && dist2(m.pos, pos) < 90)
    // farm drones (2 cubes each) while it's quiet: no enemy mech seen recently, healthy, early in the match
    const quietForFarm = P.farmNpc && t < P.farmStopT && me.hp > me.max_hp * P.farmMinHp && !obs.mechs.some((m) => m.kind === "mech") &&
      ![...this.tracks.values()].some((tr) => tr.id < 100 && t - tr.seenT < P.farmQuiet)
    if (quietForFarm) for (const m of obs.mechs) if (m.kind === "npc" && !npcsAttacking.includes(m) && dist2(m.pos, pos) < P.farmRange) npcsAttacking.push(m)
    let target: ActorObs | null = null
    const anyAttacker = enemies.some((m) => (this.tracks.get(m.id)?.hitUsT ?? -99) > t - P.attackerWindow)
    let bestScore = Infinity
    // mechs already fighting us (they hit us, or we hit them, recently). While any of them is in view,
    // only they are targets: never wake up a fresh enemy mid-fight.
    const engaged = (id: number) => { const tr = this.tracks.get(id); return !!tr && (tr.hitUsT > t - P.engagedMemory || tr.weHitT > t - P.engagedMemory) }
    const hostileNear = enemies.some((m) => !this.isPassive(m.id) && dist2(m.pos, pos) < P.engageRange)
    const fighting = enemies.filter((m) => engaged(m.id) && dist2(m.pos, pos) < P.engageRange)
    let pool = fighting.length ? [...fighting, ...npcsAttacking] : [...enemies, ...npcsAttacking]
    if (hostileNear) pool = pool.filter((m) => m.kind === "npc" || !this.isPassive(m.id))
    // standoff: a target we've held for a while without firing a shot is dropped for a bit (unless it's shooting us)
    if (P.standoffT > 0) pool = pool.filter((m) => !((this.ignoreUntil.get(m.id) ?? -1) > t) || (this.tracks.get(m.id)?.hitUsT ?? -99) > t - 3)
    if (this.ffa && !fighting.length) {
      // free-for-all: don't start fights. Only take free kills (badly hurt targets), defend our space
      // (very close mechs), or fight it out in the endgame.
      pool = pool.filter((m) => m.kind === "npc" || (m.hp ?? 1400) < (m.max_hp ?? 1400) * P.ffaWeakFrac || dist2(m.pos, pos) < P.ffaCloseRange || obs.alive <= P.ffaEndgameAlive)
    } else if (this.survNow && !this.ffa && !fighting.length) {
      // survivor (practice experiment): never start a fight; only fight back, or finish a badly hurt mech
      pool = pool.filter((m) => m.kind === "npc" || (m.hp ?? 1400) < (m.max_hp ?? 1400) * P.survWeakFrac || dist2(m.pos, pos) < P.survCloseRange)
    }
    for (const m of pool) {
      const d = dist2(m.pos, pos)
      if (d > P.engageRange) continue
      const tr = this.tracks.get(m.id)
      const losOk = this.r.los(muzzle[0], muzzle[1], muzzle[2], m.pos[0], m.pos[1], m.pos[2] + centerZ(m))
      let s = d / 60 + (m.hp ?? 1000) / 700
      if (!losOk) s += 3
      if (P.attackerFirst) {
        // whoever is shooting us comes first (weakest attacker first, via the hp term); passive bots wait
        const attacking = !!tr && tr.hitUsT > t - P.attackerWindow
        if (attacking) s -= P.attackerPri
        else if (anyAttacker) s += P.nonAttackerPen
        if (m.id === this.curTarget && (attacking || !anyAttacker)) s -= P.targetStick
      } else {
        if (tr && tr.hitUsT > t - 3) s -= 1.5
        if (m.id === this.curTarget) s -= P.targetStick // finish what we started
      }
      if (m.kind === "npc") s += 2
      if (P.counterW && m.kind === "mech") {
        // weapon triangle: laser > mortar > lightning > laser. Prefer targets we counter, avoid ones that counter us.
        const mine = slots.filter(Boolean).map((w) => w!.kind), theirs = m.weapons ?? []
        const weBeat = mine.some((k) => theirs.includes(COUNTERS[k] ?? "")), theyBeat = theirs.some((k) => mine.includes(COUNTERS[k] ?? ""))
        if (weBeat && !theyBeat) s -= P.counterW
        else if (theyBeat && !weBeat) s += P.counterW
      }
      if (s < bestScore) { bestScore = s; target = m }
    }
    if (target && target.id !== this.curTarget) this.targetSinceT = t
    this.curTarget = target ? target.id : -1
    const tgtDist = target ? dist2(target.pos, pos) : Infinity
    const tgtCenter: V3 | null = target ? [target.pos[0], target.pos[1], target.pos[2] + centerZ(target)] : null
    const tgtLos = !!tgtCenter && this.r.los(muzzle[0], muzzle[1], muzzle[2], tgtCenter[0], tgtCenter[1], tgtCenter[2])
    const underFire = t - this.lastDmgT < 3

    // ---- aim + fire
    const fire: [boolean, boolean] = [false, false]
    let aim: [number, number] | null = null
    const myAim = me.aim as V2
    const turn = me.stats.turn_rate * 0.05, pturn = me.stats.pitch_rate * 0.05
    const aimErr = (want: [number, number]) => Math.max(0, angDiff(want[0], myAim[0]) - turn) + 0.5 * Math.max(0, Math.abs(want[1] - myAim[1]) - pturn)

    this.ambushing = false
    if (target && tgtCenter) {
      const tv = target.vel as V3
      const airborne = Math.abs(tv[2]) > 0.5
      const radius = 2.5 * scaleOf(target)
      const tol = Math.atan2(radius * 0.75, Math.max(tgtDist, 1))
      // gun solution
      let gunAim: [number, number] | null = null
      if (iGun >= 0) {
        const g = slots[iGun]!.stats
        // shoot from where our muzzle will be, and damp the lead for targets that reverse direction:
        // with reversals at rate λ the expected travel over flight time T is v·(1-e^(-2λT))/(2λ)
        const mv = me.vel as V3
        const mz: V3 = [muzzle[0] + mv[0] * P.selfLead, muzzle[1] + mv[1] * P.selfLead, muzzle[2]]
        const first = lead(mz, tgtCenter, tv, g.speed, 0.05, airborne ? cfg.mech.gravity : 0, target.pos[2] + 1)
        const T = first.t + 0.05, lam = P.leadFlipRate
        const k = lam > 0 ? (1 - Math.exp(-2 * lam * T)) / (2 * lam * T) : 1
        const sol = lead(mz, tgtCenter, [tv[0] * k, tv[1] * k, tv[2]], g.speed, 0.05, airborne ? cfg.mech.gravity : 0, target.pos[2] + 1)
        gunAim = aimAt(muzzle, sol.pt)
      }
      const laser = iLaser >= 0 ? slots[iLaser]! : null
      const light = iLight >= 0 ? slots[iLight]! : null
      const mortar = iMortar >= 0 ? slots[iMortar]! : null
      const laserCharging = !!laser && (laser.charge ?? 0) > 0
      const hitscanAim = aimAt(muzzle, [tgtCenter[0] + tv[0] * 0.05, tgtCenter[1] + tv[1] * 0.05, tgtCenter[2]])

      // choose primary aim
      let mortarSol: { yaw: number; pitch: number } | null = null
      if (mortar && mortar.cooldown <= 0.15 && tgtDist > 28 && (!tgtLos || tgtDist > 70)) {
        const ms = mortar.stats
        const mm: V3 = [pos[0], pos[1], pos[2] + me.stats.height + 0.5]
        mortarSol = mortarSolve(this.r, mm, [target.pos[0], target.pos[1], target.pos[2]], tv, ms.speed, ms.gravity, false, me.stats.min_pitch, me.stats.max_pitch)
          ?? mortarSolve(this.r, mm, [target.pos[0], target.pos[1], target.pos[2]], tv, ms.speed, ms.gravity, true, me.stats.min_pitch, me.stats.max_pitch)
      }
      if (laser && (laserCharging || (laser.cooldown <= 0.1 && tgtLos && tgtDist < laser.stats.range))) aim = hitscanAim
      else if (light && tgtDist < light.stats.range + 5 && tgtLos) aim = hitscanAim
      else if (mortarSol && !(tgtLos && tgtDist < 120 && iGun >= 0 && (slots[iGun]!.ammo ?? 0) > 0)) aim = [mortarSol.yaw, mortarSol.pitch]
      else aim = gunAim ?? hitscanAim

      // ambush / surprise: is the target unaware of us (not fighting us, facing away)? Is it coming
      // around a corner toward us while we're hidden?
      const engagedT = this.tracks.get(target.id)
      const aware = !!engagedT && (engagedT.hitUsT > t - P.engagedMemory || engagedT.weHitT > t - P.engagedMemory)
      const facingUs = angDiff(target.aim?.[0] ?? 0, yawTo(target.pos, pos)) < P.unawareAngle
      const unaware = target.kind === "mech" && !aware && !facingUs
      const ux = (pos[0] - target.pos[0]) / Math.max(1, tgtDist), uy = (pos[1] - target.pos[1]) / Math.max(1, tgtDist)
      const closing = tv[0] * ux + tv[1] * uy
      this.ambushing = !!P.ambush && !!laser && target.kind === "mech" && !tgtLos && !underFire && tgtDist < laser.stats.range * 0.9 &&
        me.hp > me.max_hp * 0.5 && (closing > 2 || tgtDist < 90) && !enemies.some((m) => m.id !== target.id && engaged(m.id))
      // surprise opener: hold the gun (its sound warns them) until the laser has fired
      const holdGun = !!P.opener && !!laser && unaware && (laserCharging || (laser.cooldown <= 0.05 && tgtLos))
      // gun
      if (iGun >= 0 && gunAim && !holdGun) {
        const g = slots[iGun]!
        if (tgtLos && tgtDist < g.stats.range && (g.ammo ?? 0) > 0 && (g.reload ?? 0) <= 0 && aimErr(gunAim) < tol) fire[iGun] = true
      }
      // laser: hold to charge, release when full and on target. When ambushing, pre-charge out of
      // sight and keep holding (up to just before the auto-fire limit) until the target steps out.
      if (laser) {
        const full = (laser.charge ?? 0) >= laser.stats.charge - 0.02
        const autoFireSoon = (laser.charge ?? 0) >= laser.stats.charge + laser.stats.hold_s - 0.3
        if (laserCharging) {
          if (tgtLos) this.laserLostT = -1
          else if (this.laserLostT < 0) this.laserLostT = t
          const lostLong = this.laserLostT >= 0 && t - this.laserLostT > 1.2 && !this.ambushing
          if (full && tgtLos && aimErr(hitscanAim) < tol) fire[iLaser] = false // release → fires
          else if (lostLong || autoFireSoon) fire[iLaser] = false
          else fire[iLaser] = true
        } else if (laser.cooldown <= 0.05 && ((tgtLos && tgtDist < laser.stats.range * 0.97) || (this.ambushing && (tgtDist < P.prechargeDist || closing * 0.9 > tgtDist - P.prechargeDist)))) {
          fire[iLaser] = true
          this.laserLostT = -1
        }
      }
      // lightning: only if the intended target is the nearest thing in the cone
      if (light && tgtLos && tgtDist < light.stats.range - 1 && me.energy >= light.stats.energy + 5) {
        const half = (light.stats.cone_deg * Math.PI) / 360
        if (angDiff(myAim[0], yawTo(pos, target.pos)) < half * 0.8 && light.cooldown <= 0.1 && !this.decoyInCone(obs, pos, myAim[0], half, tgtDist, target.id)) fire[iLight] = true
      }
      // mortar
      if (mortar && mortarSol && mortar.cooldown <= 0.05) {
        if (angDiff(myAim[0], mortarSol.yaw) < 0.03 && Math.abs(myAim[1] - mortarSol.pitch) < 0.03) fire[iMortar] = true
      }
    }

    // reload when nothing to shoot
    if (iGun >= 0) {
      const g = slots[iGun]!
      if ((g.reload ?? 0) <= 0 && ((g.ammo ?? 0) === 0 || ((g.ammo ?? 0) <= 4 && !tgtLos))) act.reload = true
    }

    // crate shooting when calm (cubes + loot)
    let crateGoal: V3 | null = null
    const gunOnly = slots.every((w) => !w || w.kind === "gun")
    this.gunOnly = gunOnly
    this.hasLight = iLight >= 0
    const needWeapon = (iLaser < 0 && t < P.searchStopT) || (gunOnly && t < P.gunOnlyStopT)
    if (!target && t < (gunOnly ? Math.max(P.crateStopT, P.gunOnlyStopT) : P.crateStopT) && iGun >= 0 && !underFire) {
      let bd = needWeapon ? P.crateShootRange : P.crateRange
      for (const c of obs.crates) {
        const d = dist2(c.pos, pos)
        if (d < bd && this.reachable(c.pos) && this.r.los(muzzle[0], muzzle[1], muzzle[2], c.pos[0], c.pos[1], c.pos[2] + 1.2)) { bd = d; crateGoal = c.pos as V3 }
      }
      if (crateGoal) {
        const cAim = aimAt(muzzle, [crateGoal[0], crateGoal[1], crateGoal[2] + 1.2])
        aim = cAim
        const g = slots[iGun]!
        if ((g.ammo ?? 0) > 0 && (g.reload ?? 0) <= 0 && aimErr(cAim) < Math.atan2(1.0, Math.max(bd, 1))) fire[iGun] = true
      }
    }

    // ---- movement
    const zoneGoal = this.zoneGoal(obs)
    // edge run (start of match): head for the edge first. Keep shooting whatever we target, but don't close in.
    if (P.edgeMode && !this.edgeDone && (t > P.edgeMaxT || (t > 3 && !zoneGoal))) this.edgeDone = true
    const edgeRun = P.edgeMode && !this.edgeDone
    const odds = target && target.kind === "mech" ? this.fightOdds(me, slots, target, enemies, pos) : 9
    // free-for-all (qualifying/final): survival first. Retreat earlier, come back healthier, flee sooner.
    const ffaSafe = this.ffa && P.ffaSurvive && obs.alive > P.ffaEndgameAlive
    const retreatOdds = ffaSafe ? P.ffaRetreatOdds : P.retreatOdds
    const lowHp = me.hp < me.max_hp * (ffaSafe ? P.ffaRetreatHp : P.retreatHpFrac)
    // push: the target is nearly dead and nobody else is shooting at us → commit to the kill
    const otherShooters = enemies.filter((m) => m.id !== target?.id && engaged(m.id)).length
    const pushing = !!target && target.kind === "mech" && P.push && otherShooters === 0 && me.hp > me.max_hp * P.pushMinSelfHp &&
      ((target.hp ?? 1e9) < (target.max_hp ?? 1400) * P.pushHpFrac || (target.hp ?? 1e9) < P.pushHp)
    if (pushing) this.retreating = false
    // pincer: two hostile bots closing from directions far apart -> back away now (keep firing), whatever the odds
    let pincer = false
    if (P.pincerRetreat && !pushing) {
      const att = [...this.tracks.values()].filter((tr) => tr.id < 100 && !this.isPassive(tr.id) && t - tr.seenT < 3 &&
        dist2(tr.pos, pos) < P.pincerR && (tr.hitUsT > t - 6 || dist2(tr.pos, pos) < P.pincerNear))
      for (let i = 0; i < att.length && !pincer; i++) for (let j = i + 1; j < att.length; j++)
        if (angDiff(yawTo(pos, att[i].pos), yawTo(pos, att[j].pos)) > P.pincerAng) { pincer = true; break }
      if (pincer) this.pincerUntil = t + P.pincerHold
    }
    if (this.retreating && t > this.pincerUntil && me.hp > me.max_hp * (ffaSafe ? P.ffaReengageHp : P.reengageHpFrac) && odds > 1) this.retreating = false
    if (!pushing && (lowHp || odds < retreatOdds) && (underFire || (target && tgtDist < 150))) this.retreating = true
    if (pincer) this.retreating = true
    // reset after a kill: heal up in cover before the next hunter arrives
    if (obs.events.some((e) => e.type === "kill")) {
      this.resetUntil = t + P.resetMax
      const others = [...this.tracks.values()].some((tr) => tr.id < 100 && t - tr.seenT < 10 && dist2(tr.pos, pos) < 200 && tr.hp > 0)
      if (P.postKillHide && me.hp < me.max_hp * P.pkHpFrac && others) this.hideUntil = t + P.pkMaxT
    }
    const healing = P.postKillHide && t < this.hideUntil && me.hp < me.max_hp * P.pkExitHp && !outside

    let move: V2 = [0, 0]
    let boost = false
    let climbJump = false
    const outside = !me.in_zone
    // escape: low HP + any recent threat → get out of sight and stay out until healed. Nothing else.
    const recentTracks = [...this.tracks.values()].filter((tr) => tr.id < 100 && t - tr.seenT < P.escapeMemory)
    const threatRecent = enemies.length > 0 || underFire || recentTracks.length > 0
    if (!this.escaping && me.hp < me.max_hp * (this.ffa ? P.ffaEscapeHp : this.survNow ? P.survEscapeHp : P.escapeHpFrac) && threatRecent) this.escaping = true
    if (this.escaping && me.hp >= me.max_hp * P.escapeExitFrac) this.escaping = false
    const zoneSlack = zoneGoal ? this.zoneSlack(obs, zoneGoal) : Infinity
    // lose-the-tail state: start when low and chased; end when healed (or the timer runs out)
    const hostiles = [...this.tracks.values()].filter((tr) => tr.id < 100 && !this.isPassive(tr.id) && t - tr.seenT < 5)
    if (hostiles.some((tr) => t - tr.seenT < 0.5)) this.lastHostileT = t
    if (P.fleeTail && !this.fleeing && me.hp < me.max_hp * (ffaSafe ? P.ffaFleeHp : P.fleeHp) && hostiles.some((tr) => dist2(tr.pos, pos) < 100)) {
      this.fleeing = true; this.fleeT = t; this.fleeDest = this.fleeDestination(obs, pos, hostiles)
    }
    if (this.fleeing && (me.hp >= me.max_hp * P.fleeExitHp || t - this.fleeT > P.fleeMaxT)) { this.fleeing = false; this.fleeDest = null }
    if (this.fleeing && this.fleeDest && t - this.fleeT > 8 && t - this.lastHostileT < 2) { this.fleeDest = this.fleeDestination(obs, pos, hostiles); this.fleeT = t - 0.01 }
    // re-pick the escape point often, and avoid every known bot (passive ones too) while fleeing
    if (P.fleeAll && this.fleeing && t - this.fleeReplanT > P.fleeReplan) {
      this.fleeReplanT = t
      const all = [...this.tracks.values()].filter((tr) => tr.id < 100 && t - tr.seenT < 10)
      this.fleeDest = this.fleeDestination(obs, pos, all) ?? this.fleeDest
    }
    const flee = this.fleeing
    const grab = P.grab && !outside && !this.escaping && t - this.lastDmgT > P.grabQuiet && me.hp > me.max_hp * P.grabMinHp ? this.grabGoal(obs, slots, pos, enemies) : null
    if (zoneGoal && ((outside && P.zoneOutsideFirst) || zoneSlack < P.zoneSlack)) {
      // the zone wins over everything: get inside (weapons keep firing at whatever we were shooting)
      this.mode = outside ? "zone!" : "rotate!"
      move = this.followTo(zoneGoal, pos, t)
      boost = (outside || zoneSlack < P.zoneSlack / 2) && me.energy > 15
    } else if (flee && !outside) {
      // lose the tail: sprint far away through cover, then heal out of sight
      const quietFor = t - this.lastHostileT
      if (this.fleeDest && dist2(this.fleeDest, pos) > 12 && quietFor < P.fleeQuiet) {
        this.mode = "flee"
        move = this.followTo(this.fleeDest, pos, t)
        boost = me.grounded && me.energy > 8
      } else {
        this.mode = "recover"
        const h = this.holdSpot(obs, pos)
        move = h && Math.hypot(h.x - pos[0], h.y - pos[1]) > 3 ? this.followTo([h.x, h.y], pos, t) : [0, 0]
      }
    } else if (this.escaping && !outside) {
      this.mode = "escape"
      const threats = recentTracks.map((tr) => [tr.pos[0], tr.pos[1], tr.pos[2] + 8] as V3)
      if (underFire) threats.push([pos[0] + Math.cos(this.lastDmgBearing) * 80, pos[1] + Math.sin(this.lastDmgBearing) * 80, pos[2] + 8])
      const seen = threats.some((th) => this.r.los(th[0], th[1], th[2], pos[0], pos[1], pos[2] + 4.5) || this.r.los(th[0], th[1], th[2], pos[0], pos[1], pos[2] + 8.5))
      if (threats.length && (seen || underFire)) {
        const cover = this.findCover(pos, threats, obs)
        if (cover) move = this.followTo(cover, pos, t)
        else move = this.combatDir(pos, threats[0], 9999, 9999, obs)
        boost = me.energy > 10
      } else move = [0, 0] // hidden: stand still and heal
    } else if (grab) {
      // loot the kill site (cubes + dropped weapons) while nobody is shooting at us; keep firing
      this.mode = "grab"
      move = this.followTo(grab.pos, pos, t)
      const gd = dist2(grab.pos, pos)
      if (grab.takeId != null && gd < this.hello.config.loot.pickup_radius - 0.4 && Math.abs(grab.pos[2] - pos[2]) < 3.5) {
        act.take = grab.takeId
        if (grab.drop != null) act.drop = grab.drop
      }
      boost = gd > 25 && me.energy > this.reserve + 20
    } else if (this.retreating && (target || underFire)) {
      this.mode = "retreat"
      // hide from every enemy seen recently, not just the ones in view this tick
      const threats = (P.retreatV2 ? [...this.tracks.values()].filter((tr) => tr.id < 100 && t - tr.seenT < 8).map((tr) => tr.pos) : enemies.filter((m) => !this.isPassive(m.id)).map((m) => m.pos))
        .map((p) => [p[0], p[1], p[2] + 8] as V3)
      if (threats.length === 0 && underFire) threats.push([pos[0] + Math.cos(this.lastDmgBearing) * 80, pos[1] + Math.sin(this.lastDmgBearing) * 80, pos[2] + 8])
      let cover: V2 | null = null
      if (P.retreatV2 && this.coverAt && t - this.coverT < P.coverCommit) {
        // keep the spot we picked unless an enemy can now see it
        const c = this.coverAt, gz = this.r.groundAt(c[0], c[1])
        if (!threats.some((th) => this.r.los(th[0], th[1], th[2], c[0], c[1], gz + 4.5, 1))) cover = c
      }
      if (!cover) { cover = this.findCover(pos, threats, obs); this.coverAt = cover; this.coverT = t }
      if (cover) move = this.followTo(cover, pos, t)
      else if (P.retreatV2 && threats.length >= 2) move = this.gapDir(pos, threats)
      else move = this.combatDir(pos, target ? target.pos as V3 : threats[0], 9999, 9999, obs)
      boost = me.energy > (P.retreatV2 ? 8 : 30)
    } else if (target && (tgtDist < P.engageRange) && target.kind === "mech" && !edgeRun) {
      this.mode = "fight"
      let band: number[] = [...(P.bands[best] ?? P.bands.gun)]
      const tw = target.weapons ?? []
      // stay out of lightning reach unless we have it too; lightning shorts laser users, so close in on them
      if (tw.includes("lightning") && iLight < 0) band = [Math.max(band[0], 55), Math.max(band[1], 100)]
      else if (iLight >= 0 && tw.includes("laser") && !tw.includes("lightning")) band = [...P.bands.lightning]
      // can anything fire soon? (gun loaded, laser off cooldown, lightning in range with energy)
      const ready = slots.some((w) => {
        if (!w) return false
        if (w.kind === "gun") return (w.ammo ?? 0) > 0 && (w.reload ?? 0) <= 0
        if (w.kind === "laser") return w.cooldown <= 0.3
        if (w.kind === "lightning") return tgtDist < w.stats.range && me.energy > 10
        return w.cooldown <= 0.3
      })
      if (pushing) {
        // close in to where our gun can't miss, unless they carry lightning and we don't
        this.mode = "push"
        band = tw.includes("lightning") && iLight < 0 ? [Math.max(band[0], 50), Math.max(band[1], 70)] : [Math.min(band[0], 15), Math.min(band[1], P.pushRange)]
      }
      move = this.combatDir(pos, target.pos as V3, band[0], band[1], obs, ready || pushing)
      if (P.posScore) {
        const threats = [...this.tracks.values()].filter((tr) => tr.id < 100 && t - tr.seenT < 8 && !this.isPassive(tr.id)).map((tr) => [tr.pos[0], tr.pos[1], tr.pos[2] + 8] as V3)
        if (P.threatPic) for (const s of this.soundContacts) if (t - s.t < 6) threats.push([s.pos[0], s.pos[1], s.pos[2] + 8])
        const spot = this.fightSpot(pos, target, threats, band, ready, obs)
        if (spot && Math.hypot(spot[0] - pos[0], spot[1] - pos[1]) > P.spotArrive) {
          // head for the better spot, keeping a little sideways jink so we're not a straight-line target
          const f = this.followTo(spot, pos, t)
          move = [f[0] * 0.85 + move[0] * 0.35, f[1] * 0.85 + move[1] * 0.35]
          this.mode = "reposition"
        }
      }
      if (this.ambushing) { this.mode = "ambush"; move = [0, 0] } // hold still (silent), pre-aimed, laser charging
      if (tgtDist < band[0] * 0.6 && me.energy > this.reserve + 20) boost = true
      if (pushing && tgtDist > band[1] && me.energy > this.reserve) boost = true // chase
      // short boost bursts while dodging, like the house bots (not while charging the laser)
      if (!boost && P.boostBursts && me.energy > this.reserve + 30 && !(laserCharging(slots))) {
        if (t > this.burstT) { this.bursting = this.rng.next() < P.burstChance; this.burstT = t + this.rng.range(0.6, 1.4) }
        boost = this.bursting
      }
    } else if (healing && !(underFire && target && tgtDist < 40)) {
      this.mode = "heal"
      const threats = [...this.tracks.values()].filter((tr) => tr.id < 100 && t - tr.seenT < 10).map((tr) => [tr.pos[0], tr.pos[1], tr.pos[2] + 8] as V3)
      const cover = threats.length ? this.findCover(pos, threats, obs) : null
      if (cover) move = this.followTo(cover, pos, t)
      else if (threats.length >= 2) move = this.gapDir(pos, threats)
      else if (threats.length) move = this.combatDir(pos, threats[0], 9999, 9999, obs, false)
      else move = [0, 0]
      boost = underFire && me.energy > 10
    } else if (t < this.resetUntil && me.hp < me.max_hp * P.resetHpFrac && !outside && enemies.length === 0) {
      // reset: pick up cubes close by, otherwise sit in a sheltered spot and heal
      this.mode = "reset"
      let cube: V3 | null = null, cd = P.resetCubeRange
      if (this.wantCubes(me.cubes)) for (const c of this.cubeMem.values()) { const d = dist2(c, pos); if (d < cd && this.reachable(c)) { cd = d; cube = c } }
      if (cube) move = this.followTo(cube, pos, t)
      else {
        const h = this.holdSpot(obs, pos)
        move = h && Math.hypot(h.x - pos[0], h.y - pos[1]) > 3 ? this.followTo([h.x, h.y], pos, t) : [0, 0]
      }
    } else {
      // loot or rotate
      const loot = this.lootGoal(obs, slots, zoneGoal, needWeapon && !crateGoal)
      const dropAt = this.dropGoal(obs, pos, enemies)
      const seek = this.seekGoal(obs, pos)
      // scout jump: jet straight up and spin to spot loot on roofs and behind buildings
      const knowsWeapon = loot?.takeId != null
      const quiet = ![...this.tracks.values()].some((tr) => tr.id < 100 && t - tr.seenT < P.scoutQuiet)
      if (this.scoutUntil < t && P.scout && quiet && needWeapon && !knowsWeapon && !underFire && !outside && me.grounded && me.energy >= P.scoutEnergy && t > 2 && t - this.scoutT > P.scoutEvery && t < P.searchStopT) {
        this.scoutT = t; this.scoutUntil = t + P.scoutDur; this.scoutZ = pos[2]
      }
      if (t < this.scoutUntil) {
        this.mode = "scout"
        move = [0, 0]
        climbJump = me.grounded && t - this.scoutT < 0.3
        boost = !me.grounded && pos[2] - this.scoutZ < P.scoutHeight && me.energy > 20
        this.sweep = wrap(this.sweep + 0.4)
        aim = [this.sweep, -0.2]
      } else if (dropAt && !edgeRun && !outside && zoneSlack > P.dropZoneSlack && this.zoneEdgeDist > P.dropEdgeMargin) {
        // supply drop: full HP + full energy + 3 cubes for standing in the ring alone for 4 s
        this.mode = "drop"
        const dd = dist2(dropAt, pos)
        move = dd > P.dropStand ? this.followTo(dropAt, pos, t) : [0, 0]
        boost = dd > 40 && me.energy > this.reserve + 20
      } else if (loot && !outside && (!edgeRun || dist2(loot.pos, pos) < P.edgeLootR)) {
        this.mode = loot.takeId != null ? (loot.climb ? "climb" : "loot") : loot.explore ? "explore" : "collect"
        if (loot.climb) {
          // give up on a roof pickup we can't reach in time (never stand at a wall jumping forever)
          if (this.climbId !== loot.takeId) { this.climbId = loot.takeId!; this.climbT = t }
          if (t - this.climbT > P.climbTimeout) this.badLoot.add(loot.takeId!)
          const c = this.climbTo(loot.pos, loot.climb, me, pos, t)
          move = c.move; boost = c.boost; climbJump = c.jump
        } else move = this.followTo(loot.pos, pos, t)
        if (dist2(loot.pos, pos) < this.hello.config.loot.pickup_radius - 0.4 && Math.abs(loot.pos[2] - pos[2]) < 3.5 && loot.takeId != null) {
          act.take = loot.takeId
          if (loot.drop != null) act.drop = loot.drop
        }
      } else if (seek && !outside && (!zoneGoal || zoneSlack > P.seekZoneSlack)) {
        // seek and destroy: go find the next bot (last known position, gunfire, or where the squad gathers)
        this.mode = "seek"
        move = this.followTo(seek, pos, t)
      } else if (zoneGoal) {
        this.mode = outside ? "zone!" : "rotate"
        move = this.followTo(zoneGoal, pos, t)
        boost = outside && me.energy > 15
      } else {
        this.mode = "hold"
        const h = this.holdSpot(obs, pos)
        move = h && Math.hypot(h.x - pos[0], h.y - pos[1]) > 3 ? this.followTo([h.x, h.y], pos, t) : [0, 0]
      }
      if (underFire) {
        // being shot by someone we can't see: keep moving sideways
        const perp = this.lastDmgBearing + Math.PI / 2
        const j = this.jink(t)
        move = [move[0] * 0.6 + Math.cos(perp) * j * 0.8, move[1] * 0.6 + Math.sin(perp) * j * 0.8]
      }
    }
    if (fire[0] || fire[1]) this.lastShotT = t
    if (P.standoffT > 0 && target && target.kind === "mech" && t - this.targetSinceT > P.standoffT && t - this.lastShotT > P.standoffT) {
      this.ignoreUntil.set(target.id, t + P.standoffIgnore); this.targetSinceT = t
    }
    // healing after a kill: hold fire unless shot (dealing damage restarts the 5 s regen delay)
    if (this.mode === "heal" && !underFire) { fire[0] = false; fire[1] = false }
    // never charge the laser while escaping (it halves our speed); the gun keeps firing
    if (this.escaping && iLaser >= 0) fire[iLaser] = false
    // opportunistic take of any useful pickup underfoot
    if (act.take == null) {
      const p = this.pickupUnderfoot(obs, pos, slots)
      if (p) { act.take = p.id; if (p.drop != null) act.drop = p.drop }
    }

    // ---- facing when not aiming at something
    if (!aim) {
      const recent = [...this.tracks.values()].filter((tr) => tr.id < 100 && t - tr.seenT < 12).sort((a, b) => dist2(a.pos, pos) - dist2(b.pos, pos))[0]
      if (underFire) aim = [this.lastDmgBearing, 0]
      else if (t < 1.8) { this.sweep = wrap(this.sweep + 0.4); aim = [this.sweep, 0] } // look around at spawn for loot
      else if (t - this.heardT < 3) aim = [this.heardBearing, 0]
      else if (recent) aim = [yawTo(pos, recent.pos), 0]
      else if (this.mode === "hold" && this.hold && Math.hypot(move[0], move[1]) < 0.1) { if (P.swivel) { this.sweep = wrap(this.sweep + P.swivelHoldRate * 0.1); aim = [this.sweep, 0] } else aim = [this.hold.face + 0.6 * Math.sin(t * 0.7), 0] }
      else if (Math.hypot(move[0], move[1]) > 0.1) aim = [Math.atan2(move[1], move[0]) + (P.swivel ? P.swivelAmp * Math.sin(t * P.swivelRate) : t < P.searchStopT ? P.scanAmp * Math.sin(t * 2.2) : 0), 0]
      else { this.sweep = wrap(this.sweep + 0.12); aim = [this.sweep, 0] }
    } else this.sweep = aim[0]

    // ---- stuck recovery
    const wantMove = Math.hypot(move[0], move[1]) > 0.3
    if (!wantMove || t - this.stuckRefT > 1.0) {
      if (wantMove && dist2(this.stuckRef, pos) < 1.5 && me.grounded && t > 1) {
        this.jumpUntil = t + 0.9
        this.jumpZ = pos[2]
        this.pathT = -99 // force replan
        const n = this.nav.nearestWalkable(pos[0] + move[0] * 4, pos[1] + move[1] * 4, 2)
        if (n >= 0) this.nav.cost[n] += 3
        // stuck at the same place again: wall off the area ahead so the planner routes around it
        if (P.stuckWall && this.stuckAt && dist2(this.stuckAt, pos) < 8 && t - this.stuckAtT < 20) {
          const cx = pos[0] + move[0] * 5, cy = pos[1] + move[1] * 5
          for (let dy = -6; dy <= 6; dy += 2) for (let dx = -6; dx <= 6; dx += 2) {
            const m = this.nav.nodeAt(cx + dx, cy + dy)
            if (m >= 0) this.nav.cost[m] += 25
          }
          this.jumpUntil = t // stop jumping at it; walk around instead
        }
        // stuck in the same place again (often: grown too wide for a gap): back out toward open space
        if (P.unstickOpen && this.stuckAt && dist2(this.stuckAt, pos) < 6 && t - this.stuckAtT < 10) {
          let bestDir: V2 = [0, 0], bc = -1
          for (let k = 0; k < 16; k++) {
            const a = (k / 16) * Math.PI * 2, c = this.r.cellOf(pos[0] + Math.cos(a) * 3, pos[1] + Math.sin(a) * 3)
            if (c >= 0 && this.nav.clear[c] > bc) { bc = this.nav.clear[c]; bestDir = [Math.cos(a), Math.sin(a)] }
          }
          this.unstickDir = bestDir; this.unstickUntil = t + P.unstickT; this.pathT = -99
        }
        this.stuckAt = [pos[0], pos[1]]
        this.stuckAtT = t
      }
      this.stuckRef = [pos[0], pos[1]]
      this.stuckRefT = t
    }
    let jump = climbJump
    if (this.mode === "climb" || this.mode === "scout") this.stuckRefT = t // climbing stalls on purpose; don't trigger stuck recovery
    if (t < this.jumpUntil) {
      jump = me.grounded
      if (!me.grounded && me.energy > 8) boost = true
    }

    if (t < this.unstickUntil) move = this.unstickDir
    // off the main walkable area (sunken bowl, rooftop pocket, ledge the route map doesn't connect):
    // pick the direction with the lowest wall to clear, recharge, jet straight up above it, then go over.
    // If we make no progress, mark that direction as tried and pick another.
    if (P.islandEscape) {
      const nav = this.nav
      if (t - this.islandCheckT > 0.5) {
        this.islandCheckT = t
        const need = nav.dynClear
        nav.dynClear = 0
        this.offMain = me.grounded ? nav.nearestWalkable(pos[0], pos[1], 2) < 0 : this.offMain
        nav.dynClear = need
        if (!this.offMain) { this.islandTried.clear(); this.islandDir = null }
        else if (me.grounded && (!this.islandDir || (t - this.islandDirT > P.islandRetry && dist2(pos, this.islandFrom) < 6))) {
          if (this.islandDir) this.islandTried.add(this.islandK)
          if (this.islandTried.size >= 16) this.islandTried.clear()
          this.islandPick(pos)
          this.islandDirT = t; this.islandFrom = [pos[0], pos[1]]
        }
      }
      if (this.offMain && this.islandDir) {
        this.mode = "island"
        const climbE = Math.min(me.max_energy * 0.95, (this.islandClearZ - pos[2]) * P.climbEnergyPerM + 15)
        if (me.grounded) {
          // wait for enough energy, then take off
          move = me.energy >= climbE ? this.islandDir : [0, 0]
          jump = me.energy >= climbE
          boost = false
        } else {
          // rise straight up until above the wall, then go over it
          move = pos[2] < this.islandClearZ ? [0, 0] : this.islandDir
          boost = me.energy > 2
        }
        this.stuckRefT = t
      }
    }
    if (P.flankLook && t < this.flankUntil) { aim = [this.flankAim, 0]; fire[0] = false; fire[1] = false }
    // safety net: never send NaN/Infinity (a bad setting or edge case must not freeze the mech)
    if (!Number.isFinite(move[0]) || !Number.isFinite(move[1])) move = [0, 0]
    if (!Number.isFinite(aim[0]) || !Number.isFinite(aim[1])) aim = [me.aim[0], 0]
    const len = Math.hypot(move[0], move[1])
    if (len > 1) move = [move[0] / len, move[1] / len]
    act.move = [round3(move[0]), round3(move[1])]
    if (P.airBoostGate && !me.grounded) {
      const meant = this.mode === "climb" || this.mode === "scout" || this.mode === "island" || (t < this.jumpUntil && pos[2] - this.jumpZ < P.unstuckJetH)
      if (!meant) boost = false
    }
    act.boost = boost
    act.jump = jump
    act.aim = [round3(wrap(aim[0])), round3(clamp(aim[1], me.stats.min_pitch, me.stats.max_pitch))]
    act.fire = fire
    draw.label(`${this.ffa ? "FFA " : ""}${this.mode} hp${me.hp.toFixed(0)} ${best}${target ? ` t${target.id}@${tgtDist.toFixed(0)}` : ""}`)
    return act
  }

  // ------------------------------------------------------------------ world model

  private updateTracks(obs: Observation): void {
    for (const m of obs.mechs) {
      let tr = this.tracks.get(m.id)
      if (!tr) {
        tr = { id: m.id, pos: m.pos as V3, vel: m.vel as V3, aim: m.aim as V2, hp: m.hp ?? 0, maxHp: m.max_hp ?? 0, cubes: m.cubes ?? 0, weapons: m.weapons ?? [], charging: !!m.charging, seenT: obs.t, hitUsT: this.hitBy.get(m.id) ?? -99, weHitT: -99, watchT: 0 }
        this.tracks.set(m.id, tr)
      }
      if (m.kind === "mech" && dist2(m.pos, obs.self.pos) < 150) tr.watchT += 0.1 // time we've had it in view nearby
      tr.pos = m.pos as V3; tr.vel = m.vel as V3; tr.aim = m.aim as V2; tr.seenT = obs.t
      tr.hp = m.hp ?? tr.hp; tr.maxHp = m.max_hp ?? tr.maxHp; tr.cubes = m.cubes ?? tr.cubes
      tr.weapons = m.weapons ?? tr.weapons; tr.charging = !!m.charging
    }
    for (const [id, tr] of this.tracks) if (obs.t - tr.seenT > 30) this.tracks.delete(id)
    // pickups: remember what we see; forget ones that should be visible nearby but are not
    const seen = new Set<number>()
    for (const p of obs.pickups) { this.pickups.set(p.id, { kind: p.kind, pos: p.pos as V3 }); seen.add(p.id) }
    for (const [id, p] of this.pickups) if (!seen.has(id) && dist2(p.pos, obs.self.pos) < 35) this.pickups.delete(id)
    const seenK = new Set<number>()
    for (const c of obs.cubes) { this.cubeMem.set(c.id, c.pos as V3); seenK.add(c.id) }
    for (const [id, c] of this.cubeMem) if (!seenK.has(id) && dist2(c, obs.self.pos) < 30) this.cubeMem.delete(id)
    const seenC = new Set<number>()
    for (const c of obs.crates) { this.crates.set(c.id, c.pos as V3); seenC.add(c.id) }
    for (const [id, c] of this.crates) if (!seenC.has(id) && dist2(c, obs.self.pos) < 35) this.crates.delete(id)
  }

  private bestWeapon(slots: (WeaponObs | null)[]): string {
    let best = "gun", bp = -1
    for (const w of slots) if (w && (P.weaponPref[w.kind] ?? 0) > bp) { bp = P.weaponPref[w.kind] ?? 0; best = w.kind }
    return best
  }

  /** Value of an upgrade from its real effects in hello.config.upgrades (survival-weighted, see params.upW). */
  private upgradeValue(id: string, slots: (WeaponObs | null)[]): number | null {
    const def = (this.hello.config.upgrades ?? []).find((u: any) => u.id === id) as any
    if (!def || !Array.isArray(def.effects)) return null
    const held = slots.filter(Boolean).map((w) => w!.kind)
    const main = this.bestWeapon(slots)
    let v = 0
    for (const e of def.effects) {
      const path: string = e.path ?? ""
      const parts = path.split(".")
      const stat = parts[parts.length - 1]
      const lower = LOWER_BETTER.has(stat) || (parts[0] === "weapons" && stat === "energy")
      let base: number | undefined
      if (parts[0] === "mech") base = (this.hello.config.mech as any)?.[stat]
      else if (parts[0] === "weapons") base = (this.hello.config.weapons as any)?.[parts[1]]?.[stat]
      if (stat === "near_range_bonus") base = (this.hello.config.vision as any)?.near_range ?? 45
      if (stat === "vision_bonus") base = (this.hello.config.vision as any)?.range ?? 200
      let rel = 0
      if (typeof e.mul === "number" && e.mul > 0) rel = lower ? 1 / e.mul - 1 : e.mul - 1
      else if (typeof e.add === "number") rel = (lower ? -e.add : e.add) / (base && Math.abs(base) > 1e-9 ? Math.abs(base) : 1)
      const key = parts[0] === "weapons" ? `weapons.${stat}` : path
      let w = P.upW?.[key] ?? P.upW?.default ?? 0.05
      if (parts[0] === "weapons") {
        const kind = parts[1]
        if (!held.includes(kind)) w = 0
        else if (kind !== main) w *= P.upOffMain ?? 0.6
      }
      v += w * rel
    }
    return v
  }

  private pickUpgrade(ids: string[], slots: (WeaponObs | null)[] = []): number {
    if (P.dynUpgrades) {
      let bi = -1, bv = -Infinity
      ids.forEach((id, i) => {
        const v = this.upgradeValue(id, slots)
        if (v != null && v > bv) { bv = v; bi = i }
      })
      if (bi >= 0) return bi
    }
    let bi = 0, br = Infinity
    ids.forEach((id, i) => {
      const r = P.upgrades.indexOf(id)
      const rank = r < 0 ? 999 : r
      if (rank < br) { br = rank; bi = i }
    })
    return bi
  }

  /** Is a crate or NPC (lightning decoy) closer than the target inside the cone? */
  private decoyInCone(obs: Observation, pos: V3, yaw: number, half: number, tgtDist: number, tgtId: number): boolean {
    for (const c of obs.crates) { const d = dist2(c.pos, pos); if (d < tgtDist && angDiff(yawTo(pos, c.pos), yaw) < half) return true }
    for (const m of obs.mechs) {
      if (m.id === tgtId) continue
      const d = dist2(m.pos, pos)
      if (m.kind === "npc" && d < tgtDist && angDiff(yawTo(pos, m.pos), yaw) < half) return true
    }
    return false
  }

  // ------------------------------------------------------------------ goals

  /**
   * Seconds to spare: (time until the shrinking edge reaches where we stand) − (time to walk to the
   * goal inside the next circle, with a detour allowance). Small or negative = start moving now.
   */
  private zoneSlack(obs: Observation, goal: V2): number {
    const z = obs.zone, pos = obs.self.pos, t = obs.t
    const travel = (dist2(pos, goal) * P.zoneDetour) / obs.self.stats.walk_speed
    let tOut = Infinity
    for (let tau = t; tau <= Math.max(z.shrink_end, t) + 0.01; tau += 1) {
      const u = tau <= z.shrink_start ? 0 : clamp((tau - z.shrink_start) / Math.max(1e-6, z.shrink_end - z.shrink_start), 0, 1)
      const cx = z.center[0] + (z.next_center[0] - z.center[0]) * u, cy = z.center[1] + (z.next_center[1] - z.center[1]) * u
      const r = z.radius + (z.next_radius - z.radius) * u
      if (Math.hypot(pos[0] - cx, pos[1] - cy) > r - 3) { tOut = tau - t; break }
    }
    return tOut - travel
  }

  /** A point inside the circle the zone is shrinking to; null if we are already well inside. */
  /** Edge play: a spot on our side near the map edge, kept inside the next safe circle. */
  private edgeGoal(obs: Observation): V2 {
    const z = obs.zone, pos = obs.self.pos
    const c = z.next_center, R = z.next_radius
    let dx = pos[0] - c[0], dy = pos[1] - c[1]
    const d = Math.hypot(dx, dy)
    if (d < 1) { dx = 1; dy = 0 } else { dx /= d; dy /= d }
    // distance along our ray from the zone centre to the map edge (minus a margin)
    const b = this.edgeBounds, m = P.edgeMapMargin
    let tMap = Infinity
    if (dx > 1e-6) tMap = Math.min(tMap, (b.maxX - m - c[0]) / dx)
    if (dx < -1e-6) tMap = Math.min(tMap, (b.minX + m - c[0]) / dx)
    if (dy > 1e-6) tMap = Math.min(tMap, (b.maxY - m - c[1]) / dy)
    if (dy < -1e-6) tMap = Math.min(tMap, (b.minY + m - c[1]) / dy)
    const reach = Math.max(0, Math.min(tMap, R * P.edgeFrac))
    return [c[0] + dx * reach, c[1] + dy * reach]
  }

  private zoneGoal(obs: Observation): V2 | null {
    const z = obs.zone, pos = obs.self.pos
    const c = z.next_center, R = z.next_radius
    // edge play: until the zone gets small, our resting spot is at the edge, not the interior
    if (P.edgeMode && R > P.edgeHoldMinR) {
      const g = this.edgeGoal(obs)
      return dist2(g, pos) > P.edgeArrive ? g : null
    }
    // final phases: stand at the exact centre (the last mech inside the closing circle outlives the rest)
    const inner = R <= P.finalCenterR ? 1.5 : Math.max(R * (this.survNow ? P.survZoneInnerFrac : P.zoneInnerFrac), Math.min(R, 6))
    const d = dist2(c, pos)
    if (d <= inner) return null
    const k = inner / d
    return [c[0] + (pos[0] - c[0]) * k, c[1] + (pos[1] - c[1]) * k]
  }

  /** Far escape point (150-220 m): inside the zone, away from every hostile, not too exposed. */
  private fleeDestination(obs: Observation, pos: V3, hostiles: Track[]): V2 | null {
    const z = obs.zone
    let best: V2 | null = null, bs = -Infinity
    for (const R of [150, 185, 220]) for (let k = 0; k < 16; k++) {
      const a = (k / 16) * Math.PI * 2, x = pos[0] + Math.cos(a) * R, y = pos[1] + Math.sin(a) * R
      const n = this.nav.nodeAt(x, y)
      if (!this.nav.isMain(n) || dist2(z.next_center, [x, y]) > z.next_radius * 0.9) continue
      let minD = Infinity
      for (const h of hostiles) minD = Math.min(minD, dist2(h.pos, [x, y]))
      const s = Math.min(minD, 300) - this.nav.expCost[n] * 60
      if (s > bs) { bs = s; best = [x, y] }
    }
    return best
  }

  /**
   * Seek and destroy: where to look for the next bot. The last known position of the nearest
   * (and least crowded) enemy seen recently; else recent gunfire/footsteps; else the next zone's centre.
   * Positions we reach without finding anyone are dropped so we move on.
   */
  private seekGoal(obs: Observation, pos: V3): V2 | null {
    if (!P.seek || this.ffa || obs.self.hp < obs.self.max_hp * P.seekMinHp) return null
    const t = obs.t
    const cands = [...this.tracks.values()].filter((tr) => tr.id < 100 && t - tr.seenT < P.seekMem && t - tr.seenT > 0.5)
    let best: V2 | null = null, bs = Infinity
    for (const tr of cands) {
      if (!this.inZoneSoon(obs, tr.pos)) continue
      const d = dist2(tr.pos, pos)
      if (d < 15) { this.tracks.delete(tr.id); continue } // looked there, nobody: forget it
      let crowd = 0
      for (const o of cands) if (o !== tr && dist2(o.pos, tr.pos) < 60) crowd++
      const s = d + crowd * P.seekCrowdW
      if (s < bs) { bs = s; best = [tr.pos[0], tr.pos[1]] }
    }
    if (best) return best
    const snd = this.soundContacts.filter((sc) => t - sc.t < 15 && dist2(sc.pos, pos) > 15)
    if (snd.length) { const sc = snd[snd.length - 1]; return [sc.pos[0], sc.pos[1]] }
    const c = obs.zone.next_center
    return dist2(c, pos) > P.seekCenterR ? [c[0], c[1]] : null
  }

  /**
   * A supply drop worth going for: within range, we arrive about when it lands, nobody is about to finish
   * capturing it, no enemy mech is near it, and it's inside the coming zone. Returns its position.
   */
  private dropGoal(obs: Observation, pos: V3, enemies: ActorObs[]): V3 | null {
    if (!P.drops || !obs.drops?.length) return null
    let best: V3 | null = null, bd = Infinity
    for (const d of obs.drops) {
      const dist = dist2(d.pos, pos)
      if (dist > P.dropRange) continue
      const travel = dist / obs.self.stats.walk_speed
      if (d.lands_in > travel + P.dropEarly) continue // no point standing in an empty field for long
      if (d.holder != null && d.holder !== obs.self.id && d.progress > P.dropContestMax) continue
      if (!this.inZoneSoon(obs, d.pos) || !this.reachable(d.pos)) continue
      if (enemies.some((e) => dist2(e.pos, d.pos) < P.dropSafe)) continue
      if (dist < bd) { bd = dist; best = d.pos as V3 }
    }
    return best
  }

  /**
   * Best loot worth grabbing even with enemies around: cube piles (kill sites) and weapons that
   * improve our loadout, within grabRange, where no visible enemy is close to the item or closer to it
   * than we are. Returns null if nothing is worth the trip.
   */
  private grabGoal(obs: Observation, slots: (WeaponObs | null)[], pos: V3, enemies: ActorObs[]): { pos: V3; takeId?: number; drop?: number } | null {
    let best: { pos: V3; takeId?: number; drop?: number } | null = null, bs = 0
    // several enemies closing in: only loot that's right next to us
    const nearUs = enemies.filter((e) => e.kind === "mech" && dist2(e.pos, pos) < P.grabThreatR).length
    const maxD = nearUs > P.grabMaxNear ? P.grabCloseOk : P.grabRange
    const safe = (p: number[], d: number) => {
      if (d > maxD) return false
      for (const e of enemies) {
        const de = dist2(e.pos, p)
        if (de < P.grabSafe || de < d * P.grabRatio) return false
      }
      return true
    }
    if (this.wantCubes(obs.self.cubes)) for (const c of this.cubeMem.values()) {
      const d = dist2(c, pos)
      if (d > P.grabRange || !this.reachable(c) || !this.inZoneSoon(obs, c) || !safe(c, d)) continue
      let n = 0
      for (const o of this.cubeMem.values()) if (dist2(o, c) < 6) n++
      const s = n * P.grabCubeV - d
      if (s > bs) { bs = s; best = { pos: c } }
    }
    for (const [id, p] of this.pickups) {
      if (this.badLoot.has(id)) continue
      const take = this.takeDecision(p.kind, slots)
      if (!take) continue
      const d = dist2(p.pos, pos)
      if (d > P.grabRange || !this.reachable(p.pos) || !this.inZoneSoon(obs, p.pos) || !safe(p.pos, d)) continue
      const s = take.gain * P.grabWeaponV - d
      if (s > bs) { bs = s; best = { pos: p.pos, takeId: id, drop: take.drop } }
    }
    return best
  }

  /**
   * Climb onto a roof for a pickup: walk to the ground spot next to the building, wait for enough
   * energy, jump and jet straight up past the roof edge while pushing toward the pickup, then walk over.
   */
  private climbTo(p: V3, base: V2, me: Observation["self"], pos: V3, t: number): { move: V2; boost: boolean; jump: boolean } {
    const up = p[2] - pos[2]
    if (up < 0.6) return { move: dirTo(pos, p), boost: false, jump: false } // on the roof
    const airborne = !me.grounded
    if (!airborne && dist2(base, pos) > 5) return { move: this.followTo(base, pos, t), boost: false, jump: false }
    const need = up * P.climbEnergyPerM + 10
    if (!airborne && me.energy < Math.min(need, me.max_energy - 2)) return { move: [0, 0], boost: false, jump: false } // wait for energy
    // rise until the feet clear the edge, pushing toward the pickup so we land on the roof
    return { move: dirTo(pos, p), boost: airborne, jump: !airborne }
  }

  /** For a roof pickup: the ground spot to climb from, if the roof is low enough for our energy. */
  private roofBase(p: number[], me: Observation["self"]): V2 | null {
    const c = this.r.cellOf(p[0], p[1])
    if (c < 0) return null
    const n = this.nav.nearestWalkable(p[0], p[1], 14)
    if (n < 0) return null
    const bx = this.nav.nodeX(n), by = this.nav.nodeY(n)
    const bc = this.r.cellOf(bx, by)
    const up = p[2] - this.nav.floor[bc]
    if (up < 2.5 || up > P.maxClimb || up * P.climbEnergyPerM + 10 > me.max_energy) return null
    if (Math.hypot(bx - p[0], by - p[1]) > 26) return null
    return [bx, by]
  }

  private lootGoal(obs: Observation, slots: (WeaponObs | null)[], zoneGoal: V2 | null, search: boolean): { pos: V3; takeId?: number; drop?: number; explore?: boolean; climb?: V2 } | null {
    const pos = obs.self.pos as V3
    const calm = !obs.mechs.some((m) => m.kind === "mech")
    // cubes (from kills, crates): worth a trip when nobody is in sight; clusters first
    if (calm && this.wantCubes(obs.self.cubes) && obs.t < P.cubeStopT && !(zoneGoal && dist2(zoneGoal, pos) / obs.self.stats.walk_speed > (obs.zone.shrink_end - obs.t) * 0.6)) {
      let bc: V3 | null = null, bcs = -Infinity
      for (const c of this.cubeMem.values()) {
        const d = dist2(c, pos)
        if (d > P.cubeRange || !this.inZoneSoon(obs, c) || !this.reachable(c)) continue
        let n = 0
        for (const o of this.cubeMem.values()) if (dist2(o, c) < 6) n++
        const s = n * 40 - d * 0.5
        if (s > bcs) { bcs = s; bc = c }
      }
      if (bc) return { pos: bc }
    }
    if (obs.t > (this.gunOnly ? Math.max(P.lootStopT, P.gunOnlyStopT) : P.lootStopT)) return null
    // don't wander far if the zone needs us
    const z = obs.zone
    const tLeft = z.shrink_end - obs.t
    const zoneTight = zoneGoal && dist2(zoneGoal, pos) / obs.self.stats.walk_speed > tLeft * 0.6
    if (zoneTight) return null
    let best: { pos: V3; takeId?: number; drop?: number; explore?: boolean; climb?: V2 } | null = null
    let bs = -Infinity
    const range = search ? P.lootRangeSearch : P.lootRange
    for (const [id, p] of this.pickups) {
      const take = this.takeDecision(p.kind, slots)
      if (!take) continue
      const d = dist2(p.pos, pos)
      if (d > range || !this.inZoneSoon(obs, p.pos)) continue
      let climb: V2 | undefined
      if (this.badLoot.has(id)) continue
      if (!this.reachable(p.pos)) {
        if (!P.climb || obs.t > (this.gunOnly ? Math.max(P.climbStopT, P.gunOnlyStopT) : P.climbStopT)) continue
        const b = this.roofBase(p.pos, obs.self)
        if (!b) continue
        climb = b
      }
      const s = take.gain * 60 - d - (climb ? (p.kind === "laser" && !slots.some((w) => w?.kind === "laser") ? P.climbPenaltyLaser : P.climbPenalty) : 0)
      if (s > bs) { bs = s; best = { pos: p.pos, takeId: id, drop: take.drop, climb } }
    }
    if (this.wantCubes(obs.self.cubes)) for (const c of obs.cubes) {
      const d = dist2(c.pos, pos)
      if (d > 80 || !this.inZoneSoon(obs, c.pos) || !this.reachable(c.pos)) continue
      const s = 40 - d
      if (s > bs) { bs = s; best = { pos: c.pos as V3 } }
    }
    if (best || !search) return best
    // no known weapon: walk toward a remembered crate (stop at shooting range) ...
    let cd = P.crateSeekRange, crate: V3 | null = null
    for (const c of this.crates.values()) {
      const d = dist2(c, pos)
      if (d < cd && this.reachable(c) && this.inZoneSoon(obs, c)) { cd = d; crate = c }
    }
    if (crate) return { pos: crate }
    // ... or explore unvisited ground inside the coming zone
    return this.exploreGoal(obs, pos)
  }

  /** Pick a point ~70 m away, inside the next zone, in the least-visited 50 m cell. */
  private exploreGoal(obs: Observation, pos: V3): { pos: V3; explore: boolean } | null {
    const cellKey = (x: number, y: number) => `${Math.floor(x / 50)},${Math.floor(y / 50)}`
    this.visited.set(cellKey(pos[0], pos[1]), obs.t)
    if (this.explore && dist2(this.explore, pos) > 12 && obs.t - this.exploreT < 20) return { pos: this.explore, explore: true }
    const z = obs.zone
    let best: V3 | null = null, bs = Infinity
    for (let k = 0; k < 16; k++) {
      const a = (k / 16) * Math.PI * 2 + this.rng.next() * 0.3
      const x = pos[0] + Math.cos(a) * 70, y = pos[1] + Math.sin(a) * 70
      const n = this.nav.nodeAt(x, y)
      if (!this.nav.isMain(n) || dist2(z.next_center, [x, y]) > z.next_radius * 0.9) continue
      const v = this.visited.get(cellKey(x, y))
      const s = (v == null ? 0 : 100 - (obs.t - v)) + dist2(z.next_center, [x, y]) * 0.05
      if (s < bs) { bs = s; best = [x, y, pos[2]] }
    }
    this.explore = best
    this.exploreT = obs.t
    return best ? { pos: best, explore: true } : null
  }

  /** Is a world point on walkable ground (not on a roof or in an enclosed courtyard)? */
  private reachable(p: number[]): boolean {
    const n = this.nav.nearestWalkable(p[0], p[1], 3)
    if (n < 0) return false
    if (Math.hypot(this.nav.nodeX(n) - p[0], this.nav.nodeY(n) - p[1]) > 4.5) return false
    const c = this.r.cellOf(this.nav.nodeX(n), this.nav.nodeY(n))
    return c >= 0 && p[2] - this.nav.floor[c] < 2.5
  }

  /**
   * Fight odds: (time for the enemies that can see us to kill us) / (time for us to kill the target).
   * > 1 means we expect to win the exchange.
   */
  private fightOdds(me: Observation["self"], slots: (WeaponObs | null)[], target: ActorObs, enemies: ActorObs[], pos: V3): number {
    const d = dist2(target.pos, pos)
    const myMult = 1 + 0.04 * Math.min(me.cubes, 10)
    let ours = 0
    for (const w of slots) if (w) ours += weaponDps(w.kind, d, 0.55, w.stats.range)
    ours *= myMult
    let theirs = 0
    const myC: V3 = [pos[0], pos[1], pos[2] + 4.5]
    for (const e of enemies) {
      const de = dist2(e.pos, pos)
      if (de > 280) continue
      if (e.id !== target.id && this.isPassive(e.id)) continue
      if (e.id !== target.id && !this.r.los(e.pos[0], e.pos[1], e.pos[2] + 8, myC[0], myC[1], myC[2])) continue
      let dps = 0
      for (const k of e.weapons ?? ["gun"]) dps += weaponDps(k, de, 0.6, 0)
      theirs += dps * (1 + 0.04 * Math.min(e.cubes ?? 0, 10))
    }
    // threat picture: enemies seen recently (but not in view / not shooting yet) that are close count too
    if (P.threatPic) {
      const visible = new Set(enemies.map((e) => e.id))
      for (const tr of this.tracks.values()) {
        if (tr.id >= 100 || visible.has(tr.id) || this.t - tr.seenT > P.threatMem) continue
        const de = dist2(tr.pos, pos)
        if (de > 150) continue
        let dps = 0
        for (const k of tr.weapons.length ? tr.weapons : ["gun"]) dps += weaponDps(k, Math.max(de, 60), 0.6, 0)
        theirs += dps * P.comingW
      }
      // heard but never seen nearby: footsteps / boosts / gunfire within the near band
      for (const s of this.soundContacts) if (this.t - s.t < 4) theirs += 60 * P.comingW
    }
    const armor = me.stats.armor ?? 0
    if (ours <= 0) return 0
    if (theirs <= 0) return 9
    let odds = (me.hp / (theirs * (1 - armor))) / ((target.hp ?? 1400) / ours)
    // zone closing in behind us: fewer ways out
    if (P.threatPic && this.zoneEdgeDist < 30) odds /= 1 + P.zoneOddsW
    return odds
  }

  /** A sheltered spot near us inside the coming zone, facing the most open direction. */
  private holdSpot(obs: Observation, pos: V3): { x: number; y: number; face: number } | null {
    const z = obs.zone
    const key = `${z.next_center[0]},${z.next_center[1]},${z.next_radius}`
    const h = this.hold
    if (h && h.key === key && obs.t - h.t < 25) return h
    const inner = Math.max(z.next_radius * (this.survNow ? P.survZoneInnerFrac : P.zoneInnerFrac), 6)
    let best: { x: number; y: number; face: number } | null = null, bs = Infinity
    for (const R of [0, 10, 20, 32, 45]) {
      for (let k = 0; k < (R ? 12 : 1); k++) {
        const a = (k / 12) * Math.PI * 2
        const x = pos[0] + Math.cos(a) * R, y = pos[1] + Math.sin(a) * R
        const n = this.nav.nodeAt(x, y)
        if (n < 0 || !this.nav.walk[n]) continue
        if (dist2(z.next_center, [x, y]) > inner && R > 0) continue
        const gz = this.r.groundAt(x, y) + 6
        let open = 0, fx = 0, fy = 0
        for (let q = 0; q < 16; q++) {
          const b = (q / 16) * Math.PI * 2, cx = Math.cos(b), cy = Math.sin(b)
          const o60 = this.r.los(x, y, gz, x + cx * 60, y + cy * 60, gz, 1)
          const o120 = o60 && this.r.los(x, y, gz, x + cx * 120, y + cy * 120, gz, 1)
          open += (o60 ? 1 : 0) + (o120 ? 1 : 0)
          if (o120) { fx += cx; fy += cy }
        }
        if (open < 2) continue // fully boxed in: can't see anyone coming
        const s = open + R * 0.08
        if (s < bs) { bs = s; best = { x, y, face: Math.atan2(fy, fx) } }
      }
    }
    this.hold = best ? { ...best, key, t: obs.t } : null
    return best
  }

  /**
   * Is it safe to go to p? It must be inside the current zone, and we must be able to walk there and
   * then on into the coming circle before the shrink finishes (with a margin).
   */
  private inZoneSoon(obs: Observation, p: number[]): boolean {
    const z = obs.zone, pos = obs.self.pos
    if (dist2(z.center, p) > z.radius - 15) return false
    const inNext = dist2(z.next_center, p) < z.next_radius * 0.95
    if (inNext) return true
    const speed = obs.self.stats.walk_speed * 0.8
    const need = (dist2(pos, p) + Math.max(0, dist2(p, z.next_center) - z.next_radius * 0.8)) / speed + 8
    return need < z.shrink_end - obs.t
  }

  /** Should we take a weapon of this kind? Returns preference gain and which slot to drop. */
  private takeDecision(kind: string, slots: (WeaponObs | null)[]): { gain: number; drop?: number } | null {
    if (kind === "gun" || slots.some((w) => w?.kind === kind)) return null
    const pref = P.weaponPref[kind] ?? 0
    const empty = slots.findIndex((w) => w === null)
    if (empty >= 0) return { gain: pref + 1 }
    // both full: replace the worst non-gun weapon if this one is better
    let worst = -1, wp = Infinity
    slots.forEach((w, i) => { if (!w || (w.kind === "gun" && !P.dropGun)) return; const pr = w.kind === "gun" ? P.gunPref : (P.weaponPref[w.kind] ?? 0); if (pr < wp) { wp = pr; worst = i } })
    if (worst < 0 || pref <= wp) return null
    if (slots[worst]?.kind === "laser" && (slots[worst]!.charge ?? 0) > 0) return null
    return { gain: pref - wp, drop: worst }
  }

  private pickupUnderfoot(obs: Observation, pos: V3, slots: (WeaponObs | null)[]): { id: number; drop?: number } | null {
    for (const p of obs.pickups) {
      if (dist2(p.pos, pos) > this.hello.config.loot.pickup_radius - 0.3 || Math.abs(p.pos[2] - pos[2]) > 3.5) continue
      const d = this.takeDecision(p.kind, slots)
      if (d) return { id: p.id, drop: d.drop }
    }
    return null
  }

  // ------------------------------------------------------------------ movement

  private jink(t: number): number {
    if (t >= this.jinkUntil) {
      this.jinkSign = -this.jinkSign
      this.jinkUntil = t + this.rng.range(P.jinkMin, P.jinkMax)
    }
    return this.jinkSign
  }

  /**
   * Local steering for fights: sample 16 directions, keep the ones with room to move, prefer
   * the range band (closer / away / sideways) plus a jink component, stay inside the zone.
   */
  private combatDir(pos: V3, tp: V3, lo: number, hi: number, obs: Observation, ready = true): V2 {
    const d = dist2(tp, pos)
    const toT = Math.atan2(tp[1] - pos[1], tp[0] - pos[0])
    const radial = d < lo ? -1 : d > hi ? 1 : 0 // -1 away, +1 closer
    const j = this.jink(obs.t)
    const z = obs.zone
    const eyeZ = tp[2] + 8
    let best: V2 = [0, 0], bs = -Infinity
    let maxFree = 0, maxFreeDir: V2 = [0, 0]
    for (let k = 0; k < 16; k++) {
      const a = (k / 16) * Math.PI * 2
      const cx = Math.cos(a), cy = Math.sin(a)
      // room to move this way: up to 9 m; short gaps are allowed (penalised) so a cornered bot still moves
      // normal case: exactly v9.2's room check. The free length is only measured when that fails,
      // so a fully cornered bot can still pick the roomiest way out (fallback below).
      if (!this.roomAlong(pos, cx, cy, 9)) {
        const free = this.freeLen(pos, cx, cy, 9)
        if (free > maxFree) { maxFree = free; maxFreeDir = [cx, cy] }
        continue
      }
      const free = 9
      const along = Math.cos(a - toT) // +1 toward target
      const side = Math.sin(a - toT) // +1 = left of the target line
      let s = radial * along * 2 + side * j * 1.2 - (radial === 0 ? Math.abs(along) * 0.6 : 0)
      // skirmish: where we'd be in ~0.7 s; can the target see that spot?
      if (P.skirmish && d < 260) {
        const px = pos[0] + cx * 8, py = pos[1] + cy * 8, pz = this.r.groundAt(px, py)
        const seen = this.r.los(tp[0], tp[1], eyeZ, px, py, pz + 4.5, 1) || this.r.los(tp[0], tp[1], eyeZ, px, py, pz + 8.5, 1)
        s += ready ? (seen ? P.peekW : -P.peekW) : (seen ? -P.duckW : P.duckW)
        if (P.peekDiscipline && this.otherEyes.length) {
          let others = 0
          for (const e of this.otherEyes) if (Math.hypot(e[0] - tp[0], e[1] - tp[1]) > 8 && (this.r.los(e[0], e[1], e[2], px, py, pz + 4.5, 1) || this.r.los(e[0], e[1], e[2], px, py, pz + 8.5, 1))) others++
          s -= others * P.peekMultiW
        }
        // stay close to cover: prefer spots that have a hidden spot one more step out
        if (seen) {
          const qx = pos[0] + cx * 16, qy = pos[1] + cy * 16, qz = this.r.groundAt(qx, qy)
          if (!this.r.los(tp[0], tp[1], eyeZ, qx, qy, qz + 4.5, 1)) s += P.coverW
        }
      }
      const nx = pos[0] + cx * 10, ny = pos[1] + cy * 10
      const zr = dist2(z.center, [nx, ny])
      if (zr > z.radius - 8) s -= 3
      if (dist2(z.next_center, [nx, ny]) > z.next_radius && dist2(z.next_center, pos) > z.next_radius * 0.9) s -= Math.cos(a - Math.atan2(z.next_center[1] - pos[1], z.next_center[0] - pos[0])) < 0 ? 1.5 : 0
      s -= (9 - free) * P.cornerPenalty
      if (s > bs) { bs = s; best = [cx, cy] }
    }
    // cornered (no direction with 3 m of room): take the roomiest direction, or walk back onto the nav grid
    if (bs === -Infinity) {
      if (maxFree > 0.5) return maxFreeDir
      const n = this.nav.nearestWalkable(pos[0], pos[1], 6)
      if (n >= 0) return dirTo(pos, [this.nav.nodeX(n), this.nav.nodeY(n)])
    }
    return best
  }

  /** Escape direction through the widest angular gap between threats (with room to move). */
  private gapDir(pos: V3, threats: V3[]): V2 {
    const bearings = threats.map((th) => Math.atan2(th[1] - pos[1], th[0] - pos[0]))
    let best: V2 = [0, 0], bs = -Infinity
    for (let k = 0; k < 24; k++) {
      const a = (k / 24) * Math.PI * 2, cx = Math.cos(a), cy = Math.sin(a)
      const free = this.freeLen(pos, cx, cy, 9)
      if (free < 3) continue
      let minGap = Math.PI
      for (const b of bearings) minGap = Math.min(minGap, angDiff(a, b))
      const s = minGap + free * 0.05
      if (s > bs) { bs = s; best = [cx, cy] }
    }
    return best
  }

  /** How far (≤ len m) the mech can move along (cx, cy) with clearance, staying on the connected map. */
  private freeLen(pos: V3, cx: number, cy: number, len: number): number {
    const nav = this.nav, r = this.r
    let ok = 0
    for (let s = 1.5; s <= len + 0.01; s += 1.5) {
      const x = pos[0] + cx * s, y = pos[1] + cy * s
      const c = r.cellOf(x, y)
      if (c < 0 || nav.clear[c] < this.roomClear() || !nav.isMain(nav.nodeAt(x, y))) break
      ok = s
    }
    return ok
  }

  /** A bot we've watched nearby for a while that has never damaged us (house non-hunters seem passive). */
  private isPassive(id: number): boolean {
    if (!P.passiveTrack) return false
    const tr = this.tracks.get(id)
    return !!tr && tr.hitUsT < 0 && tr.watchT >= P.passiveAfter
  }

  /** Highest solid or ground surface at (x, y). */
  private topAt(x: number, y: number): number {
    const r = this.r, c = r.cellOf(x, y)
    if (c < 0) return 1e9
    return Math.max(r.ground[c], r.s1hi[c], r.s2hi[c])
  }

  /** Off the main area: choose the way out with the lowest wall (prefer toward the main area, skip tried ones). */
  private islandPick(pos: V3): void {
    const nav = this.nav
    const n = nav.nearestWalkable(pos[0], pos[1], P.islandSearch)
    const bm = n >= 0 ? Math.atan2(nav.nodeY(n) - pos[1], nav.nodeX(n) - pos[0]) : 0
    let bk = 0, bs = Infinity, bTop = pos[2]
    for (let k = 0; k < 16; k++) {
      const a = (k / 16) * Math.PI * 2, cx = Math.cos(a), cy = Math.sin(a)
      let top = -1e9
      for (let d = 2; d <= 16; d++) top = Math.max(top, this.topAt(pos[0] + cx * d, pos[1] + cy * d))
      const outN = nav.nearestWalkable(pos[0] + cx * 22, pos[1] + cy * 22, 4)
      const s = Math.max(0, top - pos[2]) + (outN >= 0 ? 0 : 10) + angDiff(a, bm) * 4 + (this.islandTried.has(k) ? 50 : 0)
      if (s < bs) { bs = s; bk = k; bTop = top }
    }
    const a = (bk / 16) * Math.PI * 2
    this.islandK = bk
    this.islandDir = [Math.cos(a), Math.sin(a)]
    this.islandClearZ = Math.max(pos[2], bTop) + P.islandMargin
  }

  /** Cubes past 10 only add size; keep taking them only when the next upgrade offer is close. */
  private wantCubes(n: number): boolean {
    if (!P.cubeCap || n < 10) return true
    let th = 10, step = 5
    while (th <= n) { th += step; step++ } // offers at 10, 15, 21, 28, ...
    return th - n <= P.cubeNearUp
  }

  /** clearance needed to move: the starting radius check (2.6) grows with our size */
  private roomClear(): number { return P.sizeAware ? Math.max(2.6, this.myRad + 0.1) : 2.6 }

  /** Is there room for the mech to move `len` m along (cx, cy)? */
  private roomAlong(pos: V3, cx: number, cy: number, len: number): boolean {
    const nav = this.nav, r = this.r
    for (let s = 2; s <= len; s += 1.5) {
      const x = pos[0] + cx * s, y = pos[1] + cy * s
      const c = r.cellOf(x, y)
      if (c < 0 || nav.clear[c] < this.roomClear()) return false
      if (s >= len - 1.5 && !nav.isMain(nav.nodeAt(x, y))) return false // don't step out of the connected map
    }
    return true
  }

  /** Follow an A* path toward a world point; returns a unit move vector. */
  private followTo(goal: number[], pos: V3, t: number): V2 {
    const nav = this.nav
    const need = nav.dynClear
    let gn = nav.nearestWalkable(goal[0], goal[1], 12)
    // grown too big for the map here: plan at normal size and squeeze (walls slide us along)
    if (gn < 0 && need > 3) { nav.dynClear = 0; gn = nav.nearestWalkable(goal[0], goal[1], 12); nav.dynClear = need }
    if (gn < 0) return dirTo(pos, goal)
    if (gn !== this.pathGoalNode || t - this.pathT > 2.5 || this.pathIdx >= this.path.length) {
      let sn = nav.nearestWalkable(pos[0], pos[1], 6)
      let res = sn >= 0 ? nav.astar(sn, gn, this.pathPartial ? 60000 : 20000) : null
      if ((!res || !res.complete) && need > 3 && P.squeezeFallback) {
        nav.dynClear = 0
        sn = nav.nearestWalkable(pos[0], pos[1], 6)
        const r2 = sn >= 0 ? nav.astar(sn, gn, 20000) : null
        nav.dynClear = need
        if (r2 && (r2.complete || !res)) res = r2
      }
      this.path = res ? res.path : []
      this.pathPartial = !res || !res.complete
      this.pathIdx = 0
      this.pathGoalNode = gn
      this.pathT = t
    }
    const path = this.path
    while (this.pathIdx < path.length - 1 && Math.hypot(nav.nodeX(path[this.pathIdx]) - pos[0], nav.nodeY(path[this.pathIdx]) - pos[1]) < 3) this.pathIdx++
    if (path.length === 0) return dirTo(pos, goal)
    // look ahead: furthest node (up to 10 ahead) reachable in a straight line with clearance
    let pick = this.pathIdx
    for (let k = Math.min(path.length - 1, this.pathIdx + 10); k > this.pathIdx; k--) {
      if (this.lineClear(pos[0], pos[1], nav.nodeX(path[k]), nav.nodeY(path[k]))) { pick = k; break }
    }
    const tx = nav.nodeX(path[pick]), ty = nav.nodeY(path[pick])
    if (pick === path.length - 1 && Math.hypot(tx - pos[0], ty - pos[1]) < 2) {
      // end of the path: only stop if it actually reaches the goal; otherwise head straight for the
      // goal (the stuck detector jumps/jets us out) and replan with a bigger budget right away
      if (!this.pathPartial && Math.hypot(tx - goal[0], ty - goal[1]) < 6) return [0, 0]
      this.pathT = -99
      return dirTo(pos, goal)
    }
    for (let k = 0; k < path.length && k < 40; k += 4) draw.point([nav.nodeX(path[k]), nav.nodeY(path[k]), pos[2]], "#40c0ff", 3)
    return dirTo(pos, [tx, ty])
  }

  private lineClear(ax: number, ay: number, bx: number, by: number): boolean {
    const n = Math.ceil(Math.hypot(bx - ax, by - ay))
    for (let k = 1; k <= n; k++) {
      const c = this.r.cellOf(ax + ((bx - ax) * k) / n, ay + ((by - ay) * k) / n)
      if (c < 0 || this.nav.clear[c] < (P.sizeAware ? Math.max(2.7, this.myRad + 0.2) : 2.7)) return false
    }
    return true
  }

  /** Nearest reachable spot (≤ 40 m) hidden from every threat eye, inside the zone. */
  /**
   * Where to fight from. Scores nearby reachable spots on: how many enemies can see it (ideally only
   * the target, and only when we're ready to shoot), a clear shot at the target in our range band,
   * covered ways out (dead ends and corners are penalised), and zone safety (including the edge
   * closing behind us). Re-evaluated every 0.5 s.
   */
  private fightSpot(pos: V3, target: ActorObs, threats: V3[], band: number[], ready: boolean, obs: Observation): V2 | null {
    if (this.spotCache && obs.t - this.spotCache.t < 0.5 && this.spotCache.tid === target.id) return this.spotCache.spot
    const z = obs.zone, t = obs.t
    const tc: V3 = [target.pos[0], target.pos[1], target.pos[2] + 4.5]
    const te: V3 = [target.pos[0], target.pos[1], target.pos[2] + 8]
    // the zone radius ~10 s from now (shrinking or not), used as the safe limit
    const u = t + 10 <= z.shrink_start ? 0 : clamp((t + 10 - z.shrink_start) / Math.max(1e-6, z.shrink_end - z.shrink_start), 0, 1)
    const zc: V2 = [z.center[0] + (z.next_center[0] - z.center[0]) * u, z.center[1] + (z.next_center[1] - z.center[1]) * u]
    const zr = z.radius + (z.next_radius - z.radius) * u
    const sees = (e: V3, x: number, y: number, gz: number) => this.r.los(e[0], e[1], e[2], x, y, gz + 4.5, 1) || this.r.los(e[0], e[1], e[2], x, y, gz + 8.5, 1)
    let best: V2 | null = null, bs = Infinity
    for (const R of [0, 7, 14, 22, 32]) {
      for (let k = 0; k < (R ? 12 : 1); k++) {
        const a = (k / 12) * Math.PI * 2 + R * 0.1
        const x = pos[0] + Math.cos(a) * R, y = pos[1] + Math.sin(a) * R
        if (R > 0 && (!this.nav.isMain(this.nav.nodeAt(x, y)) || !this.lineClear(pos[0], pos[1], x, y))) continue
        const dz = Math.hypot(x - zc[0], y - zc[1])
        if (dz > zr - 6) continue
        const gz = this.r.groundAt(x, y)
        let seenBy = 0
        for (const th of threats) if (sees(th, x, y, gz)) seenBy++
        const shot = this.r.los(x, y, gz + 7, tc[0], tc[1], tc[2], 1)
        const tSees = sees(te, x, y, gz)
        const d = Math.hypot(x - tc[0], y - tc[1])
        let s = 0
        s += P.spotSeenW * Math.max(0, seenBy - (shot ? 1 : 0)) // extra enemies with eyes on us
        if (ready && !shot) s += P.spotNoShotW
        if (!ready && tSees) s += P.spotExposedW
        s += d < band[0] ? (band[0] - d) / 15 : d > band[1] ? (d - band[1]) / 15 : 0
        // covered ways out: points 15 m away, walkable, hidden from every threat
        let exits = 0
        for (let q = 0; q < 8 && exits < 3; q++) {
          const b = (q / 8) * Math.PI * 2, ex = x + Math.cos(b) * 15, ey = y + Math.sin(b) * 15
          if (!this.nav.isMain(this.nav.nodeAt(ex, ey)) || Math.hypot(ex - zc[0], ey - zc[1]) > zr - 6) continue
          const egz = this.r.groundAt(ex, ey)
          let hidden = true
          for (const th of threats) if (sees(th, ex, ey, egz)) { hidden = false; break }
          if (hidden) exits++
        }
        s += exits === 0 ? P.spotDeadEndW : exits === 1 ? P.spotDeadEndW / 3 : 0
        s += Math.max(0, dz - (zr - 25)) * 0.15 // hugging the edge of the zone
        s += R * P.spotTravelW
        // separate the bots: stay away from every enemy except the one we're fighting, so they come one at a time
        if (P.separateW > 0) for (const th of threats) {
          if (Math.hypot(th[0] - tc[0], th[1] - tc[1]) < 8) continue // that's the target
          s += P.separateW * Math.max(0, 120 - Math.hypot(th[0] - x, th[1] - y)) / 120
        }
        if (P.threatPic) {
          // protect our back: open ground behind us (away from the target) lets flankers walk in unseen
          const ba = Math.atan2(y - tc[1], x - tc[0])
          if (this.r.los(x, y, gz + 6, x + Math.cos(ba) * 60, y + Math.sin(ba) * 60, gz + 6, 1)) s += P.spotRearW
          // don't camp: after fighting in one area for a while, prefer moving on
          if (this.campT > P.campAfter && R < 14) s += P.campW
        }
        // never between enemies: the widest angle between any two threat directions (π = sandwiched)
        if (threats.length >= 2) {
          let spread = 0
          const near: { a: number; d: number }[] = []
          for (const th of threats) { const dd = Math.hypot(th[0] - x, th[1] - y); if (dd < 250) near.push({ a: Math.atan2(th[1] - y, th[0] - x), d: dd }) }
          for (let i = 0; i < near.length; i++) for (let j = i + 1; j < near.length; j++) spread = Math.max(spread, angDiff(near[i].a, near[j].a))
          s += P.spotFlankW * Math.max(0, spread - Math.PI / 3) / (Math.PI * 2 / 3) // 0 at ≤60°, full at 180°
          // make them arrive one at a time: reward a gap between the nearest and the next
          if (near.length >= 2) {
            near.sort((p, q) => p.d - q.d)
            s -= P.spotStaggerW * Math.min(near[1].d - near[0].d, 40) / 40
          }
        }
        if (s < bs) { bs = s; best = [x, y] }
      }
    }
    this.spotCache = { t, tid: target.id, spot: best }
    return best
  }

  private findCover(pos: V3, threats: V3[], obs: Observation): V2 | null {
    let best: V2 | null = null, bd = Infinity
    const z = obs.zone
    for (const R of [8, 16, 26, 38]) {
      for (let k = 0; k < 24; k++) {
        const a = (k / 24) * Math.PI * 2
        const x = pos[0] + Math.cos(a) * R, y = pos[1] + Math.sin(a) * R
        const n = this.nav.nodeAt(x, y)
        if (n < 0 || !this.nav.walk[n]) continue
        if (dist2(z.center, [x, y]) > z.radius - 5) continue
        if (this.lightCarriers(obs.t).some((l) => Math.hypot(l[0] - x, l[1] - y) < P.lightAvoidR)) continue
        const gz = this.r.groundAt(x, y)
        let hidden = true
        for (const th of threats) if (this.r.los(th[0], th[1], th[2], x, y, gz + 4.5) || this.r.los(th[0], th[1], th[2], x, y, gz + 8.5)) { hidden = false; break }
        if (!hidden) continue
        // prefer spots away from threats
        let away = 0
        for (const th of threats) away += Math.hypot(x - th[0], y - th[1]) < Math.hypot(pos[0] - th[0], pos[1] - th[1]) ? 15 : 0
        const cost = R + away
        if (cost < bd) { bd = cost; best = [x, y] }
      }
      if (best && bd < R + 10) break
    }
    return best
  }
}

const laserCharging = (slots: (WeaponObs | null)[]) => slots.some((w) => w?.kind === "laser" && (w.charge ?? 0) > 0)

const SOUND_THREAT = new Set(["gun", "laser", "laser_charge", "lightning", "mortar", "step", "boost", "jet", "reload"])

/** Rough expected dps of a weapon kind at distance d (acc = gun hit rate at close range). */
function weaponDps(kind: string, d: number, acc: number, range: number): number {
  switch (kind) {
    case "gun": return d < (range || 230) ? 188 * acc * clamp(1.15 - d / 220, 0.2, 1) : 0
    case "laser": return d < (range || 280) ? 120 : 0
    case "lightning": return d < (range || 45) + 3 ? 200 : 0
    case "mortar": return d > 20 && d < 230 ? 50 : 0
    default: return 0
  }
}

function centerZ(m: ActorObs): number {
  return m.kind === "npc" ? 1.75 : 4.5 * scaleOf(m)
}
function scaleOf(m: ActorObs): number {
  return m.kind === "npc" ? 1 : 1 + 0.05 * (m.cubes ?? 0)
}
function dirTo(a: number[], b: number[]): V2 {
  const dx = b[0] - a[0], dy = b[1] - a[1], l = Math.hypot(dx, dy)
  return l < 1e-6 ? [0, 0] : [dx / l, dy / l]
}
const round3 = (v: number) => Math.round(v * 1000) / 1000
void dist3
