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

const ROOT = fileURLToPath(new URL("..", import.meta.url))
const P = { ...JSON.parse(readFileSync(ROOT + "params.json", "utf8")), ...JSON.parse(process.env.BOT_PARAMS ?? "{}") }

type Track = { id: number; pos: V3; vel: V3; aim: V2; hp: number; maxHp: number; cubes: number; weapons: string[]; charging: boolean; seenT: number; hitUsT: number }

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
    const m = hello.config.mech
    this.nav = new Nav(this.r, { height: m.height, stepUp: m.step_up, minClear: m.radius + 0.5 })
    log(`map ${dir} loaded in ${(performance.now() - t0).toFixed(0)} ms`)
    this.warmup()
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
    for (const e of obs.events) {
      if (e.type === "damaged" && e.weapon !== "zone") {
        this.lastDmgT = t
        if (e.bearing != null) this.lastDmgBearing = e.bearing
        const tr = e.by != null ? this.tracks.get(e.by) : undefined
        if (tr) tr.hitUsT = t
      } else if (e.type === "took" || e.type === "dropped") {
        if (e.type === "took") this.pickups.delete(e.id)
      }
    }
    if (obs.offer) act.pick = this.pickUpgrade(obs.offer.choices.map((c) => c.id))
    // sounds that suggest an approaching or firing mech (most recent, nearest band first)
    for (const s of obs.sounds) {
      if (!SOUND_THREAT.has(s.kind) || s.dist === "far") continue
      if (t - this.heardT > 1 || s.dist === "near") { this.heardT = t - s.age; this.heardBearing = s.bearing }
    }

    // ---- weapons
    const slots = me.weapons
    const has = (k: string) => slots.findIndex((w) => w?.kind === k)
    const iGun = has("gun"), iLaser = has("laser"), iLight = has("lightning"), iMortar = has("mortar")
    const best = this.bestWeapon(slots)

    // ---- target selection
    const muzzle: V3 = [pos[0], pos[1], pos[2] + me.stats.muzzle_height]
    const eye: V3 = [pos[0], pos[1], pos[2] + me.stats.eye_height]
    const enemies = obs.mechs.filter((m) => m.kind === "mech")
    const npcsAttacking = obs.mechs.filter((m) => m.kind === "npc" && (this.tracks.get(m.id)?.hitUsT ?? -99) > t - 4 && dist2(m.pos, pos) < 90)
    let target: ActorObs | null = null
    let bestScore = Infinity
    for (const m of [...enemies, ...npcsAttacking]) {
      const d = dist2(m.pos, pos)
      if (d > P.engageRange) continue
      const tr = this.tracks.get(m.id)
      const losOk = this.r.los(muzzle[0], muzzle[1], muzzle[2], m.pos[0], m.pos[1], m.pos[2] + centerZ(m))
      let s = d / 60 + (m.hp ?? 1000) / 700
      if (!losOk) s += 3
      if (tr && tr.hitUsT > t - 3) s -= 1.5
      if (m.kind === "npc") s += 2
      if (s < bestScore) { bestScore = s; target = m }
    }
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

    if (target && tgtCenter) {
      const tv = target.vel as V3
      const airborne = Math.abs(tv[2]) > 0.5
      const radius = 2.5 * scaleOf(target)
      const tol = Math.atan2(radius * 0.75, Math.max(tgtDist, 1))
      // gun solution
      let gunAim: [number, number] | null = null
      if (iGun >= 0) {
        const g = slots[iGun]!.stats
        const sol = lead(muzzle, tgtCenter, tv, g.speed, 0.05, airborne ? cfg.mech.gravity : 0, target.pos[2] + 1)
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

      // gun
      if (iGun >= 0 && gunAim) {
        const g = slots[iGun]!
        if (tgtLos && tgtDist < g.stats.range && (g.ammo ?? 0) > 0 && (g.reload ?? 0) <= 0 && aimErr(gunAim) < tol) fire[iGun] = true
      }
      // laser: hold to charge, release when full and on target
      if (laser) {
        const full = (laser.charge ?? 0) >= laser.stats.charge - 0.02
        if (laserCharging) {
          if (tgtLos) this.laserLostT = -1
          else if (this.laserLostT < 0) this.laserLostT = t
          const lostLong = this.laserLostT >= 0 && t - this.laserLostT > 1.2
          if (full && tgtLos && aimErr(hitscanAim) < tol) fire[iLaser] = false // release → fires
          else if (lostLong) fire[iLaser] = false
          else fire[iLaser] = true
        } else if (laser.cooldown <= 0.05 && tgtLos && tgtDist < laser.stats.range * 0.97) {
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
    const needWeapon = iLaser < 0 && t < P.searchStopT
    if (!target && t < P.crateStopT && iGun >= 0 && !underFire) {
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
    const odds = target && target.kind === "mech" ? this.fightOdds(me, slots, target, enemies, pos) : 9
    const lowHp = me.hp < me.max_hp * P.retreatHpFrac
    if (this.retreating && me.hp > me.max_hp * P.reengageHpFrac && odds > 1) this.retreating = false
    if ((lowHp || odds < P.retreatOdds) && (underFire || (target && tgtDist < 150))) this.retreating = true

    let move: V2 = [0, 0]
    let boost = false
    const outside = !me.in_zone
    if (this.retreating && (target || underFire)) {
      this.mode = "retreat"
      const threats = enemies.map((m) => [m.pos[0], m.pos[1], m.pos[2] + 8] as V3)
      if (threats.length === 0 && underFire) threats.push([pos[0] + Math.cos(this.lastDmgBearing) * 80, pos[1] + Math.sin(this.lastDmgBearing) * 80, pos[2] + 8])
      const cover = this.findCover(pos, threats, obs)
      if (cover) move = this.followTo(cover, pos, t)
      else move = this.combatDir(pos, target ? target.pos as V3 : threats[0], 9999, 9999, obs)
      boost = me.energy > 30
    } else if (target && (tgtDist < P.engageRange) && target.kind === "mech") {
      this.mode = "fight"
      let band: number[] = [...(P.bands[best] ?? P.bands.gun)]
      const tw = target.weapons ?? []
      // stay out of lightning reach unless we have it too; lightning shorts laser users, so close in on them
      if (tw.includes("lightning") && iLight < 0) band = [Math.max(band[0], 55), Math.max(band[1], 100)]
      else if (iLight >= 0 && tw.includes("laser") && !tw.includes("lightning")) band = [...P.bands.lightning]
      move = this.combatDir(pos, target.pos as V3, band[0], band[1], obs)
      if (tgtDist < band[0] * 0.6 && me.energy > P.energyReserve + 20) boost = true
    } else {
      // loot or rotate
      const loot = this.lootGoal(obs, slots, zoneGoal, needWeapon && !crateGoal)
      if (loot && !outside) {
        this.mode = loot.takeId != null ? "loot" : loot.explore ? "explore" : "collect"
        move = this.followTo(loot.pos, pos, t)
        if (dist2(loot.pos, pos) < this.hello.config.loot.pickup_radius - 0.4 && loot.takeId != null) {
          act.take = loot.takeId
          if (loot.drop != null) act.drop = loot.drop
        }
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
      else if (this.mode === "hold" && this.hold && Math.hypot(move[0], move[1]) < 0.1) aim = [this.hold.face + 0.6 * Math.sin(t * 0.7), 0]
      else if (Math.hypot(move[0], move[1]) > 0.1) aim = [Math.atan2(move[1], move[0]) + (t < P.searchStopT ? P.scanAmp * Math.sin(t * 2.2) : 0), 0]
      else { this.sweep = wrap(this.sweep + 0.12); aim = [this.sweep, 0] }
    } else this.sweep = aim[0]

    // ---- stuck recovery
    const wantMove = Math.hypot(move[0], move[1]) > 0.3
    if (!wantMove || t - this.stuckRefT > 1.0) {
      if (wantMove && dist2(this.stuckRef, pos) < 1.5 && me.grounded && t > 1) {
        this.jumpUntil = t + 0.9
        this.pathT = -99 // force replan
        const n = this.nav.nearestWalkable(pos[0] + move[0] * 4, pos[1] + move[1] * 4, 2)
        if (n >= 0) this.nav.cost[n] += 3
      }
      this.stuckRef = [pos[0], pos[1]]
      this.stuckRefT = t
    }
    let jump = false
    if (t < this.jumpUntil) {
      jump = me.grounded
      if (!me.grounded && me.energy > 8) boost = true
    }

    const len = Math.hypot(move[0], move[1])
    if (len > 1) move = [move[0] / len, move[1] / len]
    act.move = [round3(move[0]), round3(move[1])]
    act.boost = boost
    act.jump = jump
    act.aim = [round3(wrap(aim[0])), round3(clamp(aim[1], me.stats.min_pitch, me.stats.max_pitch))]
    act.fire = fire
    draw.label(`${this.mode} hp${me.hp.toFixed(0)} ${best}${target ? ` t${target.id}@${tgtDist.toFixed(0)}` : ""}`)
    return act
  }

  // ------------------------------------------------------------------ world model

  private updateTracks(obs: Observation): void {
    for (const m of obs.mechs) {
      let tr = this.tracks.get(m.id)
      if (!tr) {
        tr = { id: m.id, pos: m.pos as V3, vel: m.vel as V3, aim: m.aim as V2, hp: m.hp ?? 0, maxHp: m.max_hp ?? 0, cubes: m.cubes ?? 0, weapons: m.weapons ?? [], charging: !!m.charging, seenT: obs.t, hitUsT: -99 }
        this.tracks.set(m.id, tr)
      }
      tr.pos = m.pos as V3; tr.vel = m.vel as V3; tr.aim = m.aim as V2; tr.seenT = obs.t
      tr.hp = m.hp ?? tr.hp; tr.maxHp = m.max_hp ?? tr.maxHp; tr.cubes = m.cubes ?? tr.cubes
      tr.weapons = m.weapons ?? tr.weapons; tr.charging = !!m.charging
    }
    for (const [id, tr] of this.tracks) if (obs.t - tr.seenT > 30) this.tracks.delete(id)
    // pickups: remember what we see; forget ones that should be visible nearby but are not
    const seen = new Set<number>()
    for (const p of obs.pickups) { this.pickups.set(p.id, { kind: p.kind, pos: p.pos as V3 }); seen.add(p.id) }
    for (const [id, p] of this.pickups) if (!seen.has(id) && dist2(p.pos, obs.self.pos) < 35) this.pickups.delete(id)
    const seenC = new Set<number>()
    for (const c of obs.crates) { this.crates.set(c.id, c.pos as V3); seenC.add(c.id) }
    for (const [id, c] of this.crates) if (!seenC.has(id) && dist2(c, obs.self.pos) < 35) this.crates.delete(id)
  }

  private bestWeapon(slots: (WeaponObs | null)[]): string {
    let best = "gun", bp = -1
    for (const w of slots) if (w && (P.weaponPref[w.kind] ?? 0) > bp) { bp = P.weaponPref[w.kind] ?? 0; best = w.kind }
    return best
  }

  private pickUpgrade(ids: string[]): number {
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

  /** A point inside the circle the zone is shrinking to; null if we are already well inside. */
  private zoneGoal(obs: Observation): V2 | null {
    const z = obs.zone, pos = obs.self.pos
    const c = z.next_center, R = z.next_radius
    const inner = Math.max(R * P.zoneInnerFrac, Math.min(R, 6))
    const d = dist2(c, pos)
    if (d <= inner) return null
    const k = inner / d
    return [c[0] + (pos[0] - c[0]) * k, c[1] + (pos[1] - c[1]) * k]
  }

  private lootGoal(obs: Observation, slots: (WeaponObs | null)[], zoneGoal: V2 | null, search: boolean): { pos: V3; takeId?: number; drop?: number; explore?: boolean } | null {
    const pos = obs.self.pos as V3
    if (obs.t > P.lootStopT) return null
    // don't wander far if the zone needs us
    const z = obs.zone
    const tLeft = z.shrink_end - obs.t
    const zoneTight = zoneGoal && dist2(zoneGoal, pos) / obs.self.stats.walk_speed > tLeft * 0.6
    if (zoneTight) return null
    let best: { pos: V3; takeId?: number; drop?: number; explore?: boolean } | null = null
    let bs = -Infinity
    const range = search ? P.lootRangeSearch : P.lootRange
    for (const [id, p] of this.pickups) {
      const take = this.takeDecision(p.kind, slots)
      if (!take) continue
      const d = dist2(p.pos, pos)
      if (d > range || !this.inZoneSoon(obs, p.pos) || !this.reachable(p.pos)) continue
      const s = take.gain * 60 - d
      if (s > bs) { bs = s; best = { pos: p.pos, takeId: id, drop: take.drop } }
    }
    for (const c of obs.cubes) {
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
      if (e.id !== target.id && !this.r.los(e.pos[0], e.pos[1], e.pos[2] + 8, myC[0], myC[1], myC[2])) continue
      let dps = 0
      for (const k of e.weapons ?? ["gun"]) dps += weaponDps(k, de, 0.6, 0)
      theirs += dps * (1 + 0.04 * Math.min(e.cubes ?? 0, 10))
    }
    const armor = me.stats.armor ?? 0
    if (ours <= 0) return 0
    if (theirs <= 0) return 9
    return (me.hp / (theirs * (1 - armor))) / ((target.hp ?? 1400) / ours)
  }

  /** A sheltered spot near us inside the coming zone, facing the most open direction. */
  private holdSpot(obs: Observation, pos: V3): { x: number; y: number; face: number } | null {
    const z = obs.zone
    const key = `${z.next_center[0]},${z.next_center[1]},${z.next_radius}`
    const h = this.hold
    if (h && h.key === key && obs.t - h.t < 25) return h
    const inner = Math.max(z.next_radius * P.zoneInnerFrac, 6)
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

  private inZoneSoon(obs: Observation, p: number[]): boolean {
    return dist2(obs.zone.next_center, p) < obs.zone.next_radius * 0.95
  }

  /** Should we take a weapon of this kind? Returns preference gain and which slot to drop. */
  private takeDecision(kind: string, slots: (WeaponObs | null)[]): { gain: number; drop?: number } | null {
    if (kind === "gun" || slots.some((w) => w?.kind === kind)) return null
    const pref = P.weaponPref[kind] ?? 0
    const empty = slots.findIndex((w) => w === null)
    if (empty >= 0) return { gain: pref + 1 }
    // both full: replace the worst non-gun weapon if this one is better
    let worst = -1, wp = Infinity
    slots.forEach((w, i) => { if (w && w.kind !== "gun" && (P.weaponPref[w.kind] ?? 0) < wp) { wp = P.weaponPref[w.kind] ?? 0; worst = i } })
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
  private combatDir(pos: V3, tp: V3, lo: number, hi: number, obs: Observation): V2 {
    const d = dist2(tp, pos)
    const toT = Math.atan2(tp[1] - pos[1], tp[0] - pos[0])
    const radial = d < lo ? -1 : d > hi ? 1 : 0 // -1 away, +1 closer
    const j = this.jink(obs.t)
    const z = obs.zone
    let best: V2 = [0, 0], bs = -Infinity
    for (let k = 0; k < 16; k++) {
      const a = (k / 16) * Math.PI * 2
      const cx = Math.cos(a), cy = Math.sin(a)
      if (!this.roomAlong(pos, cx, cy, 9)) continue
      const along = Math.cos(a - toT) // +1 toward target
      const side = Math.sin(a - toT) // +1 = left of the target line
      let s = radial * along * 2 + side * j * 1.2 - (radial === 0 ? Math.abs(along) * 0.6 : 0)
      const nx = pos[0] + cx * 10, ny = pos[1] + cy * 10
      const zr = dist2(z.center, [nx, ny])
      if (zr > z.radius - 8) s -= 3
      if (dist2(z.next_center, [nx, ny]) > z.next_radius && dist2(z.next_center, pos) > z.next_radius * 0.9) s -= Math.cos(a - Math.atan2(z.next_center[1] - pos[1], z.next_center[0] - pos[0])) < 0 ? 1.5 : 0
      if (s > bs) { bs = s; best = [cx, cy] }
    }
    return best
  }

  /** Is there room for the mech to move `len` m along (cx, cy)? */
  private roomAlong(pos: V3, cx: number, cy: number, len: number): boolean {
    const nav = this.nav, r = this.r
    for (let s = 2; s <= len; s += 1.5) {
      const x = pos[0] + cx * s, y = pos[1] + cy * s
      const c = r.cellOf(x, y)
      if (c < 0 || nav.clear[c] < 2.6) return false
      if (s >= len - 1.5 && !nav.isMain(nav.nodeAt(x, y))) return false // don't step out of the connected map
    }
    return true
  }

  /** Follow an A* path toward a world point; returns a unit move vector. */
  private followTo(goal: number[], pos: V3, t: number): V2 {
    const nav = this.nav
    const gn = nav.nearestWalkable(goal[0], goal[1], 12)
    if (gn < 0) return dirTo(pos, goal)
    if (gn !== this.pathGoalNode || t - this.pathT > 2.5 || this.pathIdx >= this.path.length) {
      const sn = nav.nearestWalkable(pos[0], pos[1], 6)
      const res = sn >= 0 ? nav.astar(sn, gn, this.pathPartial ? 60000 : 20000) : null
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
      if (c < 0 || this.nav.clear[c] < 2.7) return false
    }
    return true
  }

  /** Nearest reachable spot (≤ 40 m) hidden from every threat eye, inside the zone. */
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
