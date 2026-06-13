# Tutorial: bring your own tower

`Keep/Core.lean` is fully parametric: instantiate one structure and you get
`tower_safe` — runtime-replaceable gates at every level, with no assumed
gate soundness — for your own system. This tutorial builds the smallest
possible instance from scratch: a dial whose setting must never exceed 100.
The finished file is `Keep/Dial.lean` (~70 lines, compiled and axiom-audited
with the rest of the library), so every snippet below is checked.

The recipe has five steps.

## Step 1 — pick the object system and its invariant

The dial's state is a number; the safety property is a hard limit.

```lean
S := Nat
Inv := fun s => s ≤ 100
```

`Inv` is the thing the whole tower exists to keep. Choose it before anything
else, and choose it *minimal*: in the calculator instance it is conservative
extension of the baseline — pointedly *not* "nothing ever changes."

## Step 2 — choose the proposal language, per level

A level-0 proposal denotes a state change. A level-`n+1` proposal is a
*gate description*: data denoting a checker on level-`n` proposals.

For the dial, every level's proposals are plain numbers:

- level 0: the requested setting;
- level `n+1`: a **cap** — the description of a gate admitting requests
  (or caps) up to it.

```lean
P := fun _ => Nat
act := fun p _ => p                      -- set the dial
den := fun _ c p => decide (p ≤ c)       -- the cap c, as a checker
```

This is the whole `World`:

```lean
def world : Keep.World where
  S := Nat
  Inv := fun s => s ≤ 100
  P := fun _ => Nat
  act := fun p _ => p
  den := fun _ c p => decide (p ≤ c)
```

Design note: gates are *decidable checkers over syntax*, not proof
obligations. That is the amortization move — soundness is proved once per
gate (next step), after which admission at runtime is just running a
`Bool`-valued function. The calculator's gates likewise never read a
patch's payload, only its target name: pick proposal syntax so that the
gate can decide on the part that matters.

## Step 3 — prove your gate descriptions sound, once, by one induction

`Sound` is iterated: a level-0 gate is sound when everything it admits
preserves `Inv`; a level-`n+1` gate is sound when every description it
admits denotes a sound level-`n` gate. When the same description shape
works at every level, one structural induction arms the whole infinite
tower:

```lean
def clamp (c : Nat) : Keep.Gates world := fun n => world.den n c

theorem clamp_sound {c : Nat} (hc : c ≤ 100) :
    ∀ n, Keep.Sound world n (world.den n c)
  | 0 => fun _ _ adm _ => Nat.le_trans (of_decide_eq_true adm) hc
  | n + 1 => fun _ adm =>
      clamp_sound (Nat.le_trans (of_decide_eq_true adm) hc) n
```

Read the successor case aloud: *a cap within the limit only ever admits
caps within the limit.* That sentence is the entire tower.

## Step 4 — find your corrupt description, and refuse it at every level

Every instance has one: the description whose gate is too permissive to be
sound. For the calculator it is the empty protection list; for the dial it
is any cap above the limit. Prove it unsound at level 0, then let the
unsoundness propagate upward — a gate that admits a corrupt description is
itself corrupt:

```lean
theorem overcap_unsound :
    ∀ n, ¬ Keep.Sound world n (world.den n ((1000 : Nat)))
  | 0 => fun h => ...                       -- it admits 1000; 1000 ≰ 100
  | n + 1 => fun h => overcap_unsound n (h (1000 : Nat) rfl)

theorem no_sound_gate_admits_overcap {n : Nat} {h : world.P (n + 1) → Bool}
    (hs : Keep.Sound world (n + 1) h) : h (1000 : Nat) = false := ...
```

This pair is the artifact's signature beat: harm is refused not at the
moment it would strike but at every height of the tower above it.

## Step 5 — run a trace and collect `tower_safe` for free

Configurations, admitted steps, and the safety of the result:

```lean
def d0 : Keep.Config world := ⟨(0 : Nat), clamp 100⟩
def d1 : Keep.Config world :=
  ⟨d0.state, d0.gates.set 0 (world.den 0 (90 : Nat))⟩

theorem tighten : Keep.Step world d0 d1 :=
  Keep.Step.swap (c := d0) 0 (90 : Nat) rfl    -- gate 1 admits the new cap

theorem was_admissible : d0.gates 0 (95 : Nat) = true  := rfl
theorem now_refused    : d1.gates 0 (95 : Nat) = false := rfl

theorem d1_safe : Keep.Safe d1 :=
  Keep.tower_safe d0_safe (.step (.refl d0) tighten)
```

Note what `tighten` is: a *gate replacement at runtime*, admitted by the
gate one level up, after which a previously admissible request is refused —
and `d1_safe` certifies the whole run without assuming anything about the
installed gate. That is the operation every benchmark-gated self-improving
system forbids and every ungated one performs unchecked.

## Mechanical notes (read before writing your own)

Friction you will hit, and the idioms that resolve it — all visible in
`Keep/Dial.lean` and `Keep/Calculator.lean`:

- **Instance search does not see through `World` fields.** `world.P (n+1)`
  and `world.Inv s` are definitionally `Nat` and `s ≤ 100`, but typeclass
  resolution (numerals, `Membership`, `Decidable`) works at reducible
  transparency and will not unfold them. Ascribe literals
  (`(1000 : Nat)`, `([] : List String)`) and state `Prop` side conditions
  with `show` (`show (0 : Nat) ≤ 100 by decide`).
- **Prefer `refine fun ... => ?_` over `intro`** when the goal is `Sound`
  or your invariant applied to projections — elaboration unfolds
  definitions where `intro` may not.
- **Admissions and refusals are often `rfl`.** Gates are computable, so
  `c.gates n p = true/false` frequently closes by reduction — including
  through `Gates.set`. A refusal by `rfl` depends on no axioms.
- **`Step` constructors want the configuration pinned:**
  `Keep.Step.act (c := t0) ...`, `Keep.Step.swap (c := t1) ...`.

## Exercises

1. *Per-level caps.* Generalize `clamp` so level `n` carries cap `c n`,
   sound when `c` is pointwise within limit and monotone. What replaces the
   single induction?
2. *An improvement witness.* The dial has safety but no gain. Add a notion
   of strict improvement to a trace (the calculator's `demo_improves` is
   the model: no regression plus a kernel-checked witness) — e.g. a step
   that raises a too-strict cap back toward the limit, with the witness
   being a request refused before and admitted after.
3. *Two invariants.* Give the dial a second constraint (e.g. even values
   only) by strengthening `Inv`. Which existing proofs survive unchanged?
   (`sound_antitone` says hardened gates are free; what about `clamp`?)
4. *Proof-bearing proposals.* Replace `den`'s decidable check with a
   certificate field on the proposal (as in lean-sage's proof-bearing
   approvals): make `P (n+1)` a structure carrying its own `Sound` proof,
   and let the gate check a shape. Where does the amortization go?
