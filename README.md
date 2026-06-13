# lean-keep

**A system that improves creates new things worth protecting, so its gate
must be able to improve with it — this artifact is the proof that it can,
safely, at every depth.**

**Who gates the gate?** Every reasonable-reflection artifact so far gates the
*object* level: a substrate, a fixed gate, proof-carrying modifications. This
artifact's substrate is the gate stack itself: a tower in which each level's
gate is replaceable at runtime, under a certificate checked by the gate one
level up — and the safety of the whole arrangement is one theorem, with **no
gate's soundness assumed along the way**.

The name: a *keep* is the innermost tower of a castle, and *to keep* is what
the invariant does.

## The point, in one example

A calculator must never break its baseline: `(+ 1 2) = 3`, `(id 3) = 3` —
conservative extension of the baseline is the invariant. Gate 0 protects the
names `{+, id}` and admits any patch elsewhere.

1. **Improve.** A proposer submits `mult` at the fresh name `*`. Gate 0
   admits it, and now `(* 2 3 4) = 24` — strict gain over the baseline, with
   the witness kernel-checked (`demo_improves`).

2. **The improvement creates a problem the invariant cannot see.** `*` now
   matters — and nothing protects it. The same gate that admitted `mult`
   will happily admit a patch that trashes it:
   `t1.gates 0 ⟨"*", junk⟩ = true` (`clobber_was_admissible`). And the
   invariant is no help: `*` is not in the baseline, so clobbering it is
   perfectly conservative. **The system improved; its gate didn't. No
   object-level move can close this gap — only a gate change can.**

   This is the moment existing self-improving systems have no answer for.
   The benchmark-gated ones cannot change the gate at all (it is frozen,
   outside the agent's reach), so every new capability stays forever
   clobberable by whatever the old gate admits. The ungated one would swap
   the gate unchecked and hope.

3. **Improve the gate, through the gate above.** Propose the description
   `{+, id, *}` as a replacement for gate 0. Gate 1 checks it — does it
   still protect the baseline? — and admits. The clobber is now refused:
   `t2.gates 0 ⟨"*", junk⟩ = false` (`clobber_refused` — by `rfl`,
   independent of the payload). Then gate 2 admits hardening gate 1 to
   *demand* `*` stay protected, after which rolling the protection back is
   refused one level up (`rollback_refused`). The improvement locked itself
   in, and the lock locked itself.

4. **And nothing was assumed along the way.** `tower_safe`: at the end of
   the run the invariant holds and every gate in the stack — including the
   two installed mid-flight — is sound, each installed gate's soundness
   derived from the gate that admitted it, not assumed. Meanwhile a corrupt
   gate description (`[]`: protect nothing) cannot enter at any height of
   the tower (`no_sound_gate_admits_nil`).

The moral: **a system that improves creates new things worth protecting, so
its gate must improve with it.** Freezing the gate (sound, dead —
`frozen_sound`) forfeits exactly that; swapping it unchecked is how
self-modifying agents die. Here gate evolution is an ordinary admitted step,
certified one level up, and provably safe at every depth.

## The two facts this answers

Empirical self-improving systems (Darwin Gödel Machine, SICA, STOP,
AlphaEvolve) all keep their evaluation gate frozen and outside the agent's
reach — DGM explicitly, because exposing or unfreezing the gate invites
objective hacking. The one system that lets the agent touch its own
improvement machinery (Gödel Agent) lists self-destruction by editing it as a
characteristic failure mode. On the theory side, the Gödel machine collapses
all meta-levels into a single theorem, and Yudkowsky–Herreshoff's tiling
agents shows a gate cannot certify a successor gate of equal logical strength
*in the abstract* (the Löbian obstacle).

The way through is the LCF discipline lifted one level: a running system
never needs the Löb-blocked quantified self-trust ("all proofs are true") —
it needs to check *this particular* replacement gate against *this
particular* soundness certificate. So: **one fixed checker (the kernel),
unboundedly many swappable gates (policies)**. The empirical systems freeze
the policy because they have nothing else; here only the checker is frozen.

## Core (`Keep/Core.lean`, 131 lines)

A `World` is an object system with an invariant `Inv`, plus a level-indexed
proposal language: a level-0 proposal denotes a state change (`act`), a
level-`n+1` proposal denotes a replacement *gate* for level `n` — a decidable
checker on level-`n` proposals (`den`). Iterated soundness:

```
Sound 0     h  =  everything h admits preserves Inv
Sound (n+1) h  =  every gate description h admits denotes a Sound n gate
```

A configuration is a state plus a gate at every level. A `Step` is either an
admitted object modification or an admitted *gate replacement* at any level.

- **`tower_safe`** — from a safe start (invariant holds, every gate in the
  initial stack sound), every reachable configuration is safe. Each gate
  installed en route has its soundness *derived* from the admitting gate one
  level up; nothing about installed gates is assumed.
- **`sound_antitone`** — a gate admitting less than a sound gate is sound:
  hardening never needs a certificate.
- **`frozen_sound`** — the gate admitting nothing is vacuously sound at every
  level. A frozen tail is sound, and dead: this is the configuration every
  benchmark-gated self-improving system implicitly runs.

Assumptions, stated plainly: the ambient checker (Lean's kernel) is trusted
and fixed; initial-stack soundness is a hypothesis of `tower_safe`; `Step`
admits only gate-approved transitions (admission is the model's definition,
not an enforcement claim about some external runtime).

## Instance (`Keep/Calculator.lean`, 206 lines)

The lean-gate calculator under the tower. Invariant: conservative extension
of the baseline (`+`, `id`). A level-0 proposal installs an arbitrary payload
at a name; gates are *protection lists* and read only the name — conservative
extension is about *where* you write, not *what* you write. A level-`n+1`
proposal is itself a protection list, admitted iff it keeps protecting what
level `n+1` demands.

- **`protect`** — one list generates the whole infinite stack: gate `n` is
  the same description applied at level `n`.
- **`protect_sound`** — a single induction on the level arms every level of
  the infinite tower. No frozen tail; the tower is live all the way up.
- **`nil_unsound` / `no_sound_gate_admits_nil`** — the unprotecting
  description `[]` is unsound at *every* level, so no sound gate at any
  height admits it: the gate that would admit the gate that would admit the
  β-collapse is itself refused, arbitrarily many levels before the harm.
- **The demo trace** (`t0 → t1 → t2 → t3`, theorems `step01`–`step23`,
  `demo_reach`, `demo_safe`): admit `mult` (strict gain, `(* 2 3 4) ⇒ 24`);
  replace gate 0 to protect `*` (the improvement locks itself in); replace
  gate 1 to demand `*` stay protected (the lock is locked).
- **`clobber_was_admissible` / `clobber_refused`** — the same patch, admitted
  before the hardening, refused after; refusal is independent of the payload
  and holds by `rfl`.
- **`rollback_refused`** — un-protecting `*` is refused one level up, also by
  `rfl`: no take-backs without a certificate the tower will not grant.
- **`demo_improves`** — the improvement pair for the whole trace,
  kernel-checked: no regression (conservative extension, from `demo_safe`)
  and strict gain (witness: baseline cannot evaluate `(* 2 3 4)`; the final
  state evaluates it to `24`).

## Run

```
lake build        # library + pinned axiom audit (Keep/Audit.lean)
lake exe smoke    # five scenes: admissions, refusals, the cascade
```

Axiom footprint, CI-pinned: `propext` and `Quot.sound` only — no
`Classical.choice`, no `sorry`, no `native_decide`. The refusal theorems
depend on no axioms at all.

## What is and is not claimed

Claimed: in this abstract setting, gate replacement under
checked-one-level-up certificates preserves both the object invariant and
the soundness of the entire stack, at every reflective depth, including an
infinite live tower — and improvement (no regression + strict gain) survives
the cascade.

Not claimed: this does not discharge lean-sage's open problem (derived
gate-swap soundness *in the Black-faithful tower*, with heaps and closures —
see lean-sage's SCOPE.md); it isolates the principle that problem instantiates.
It does not evade the Löbian obstacle in proof-theoretic strength: all
certificates live in one ambient logic, and replacing the *checker* (rather
than a gate) is exactly where the tiling-agents telomere would begin. The
gates here are checkers over syntax; richer evidence kinds (per-modification
proof terms, as in lean-sage's proof-bearing approvals) compose with the same
tower unchanged.
