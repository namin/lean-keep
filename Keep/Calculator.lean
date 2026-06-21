import Keep.Core

/-!
# Keep.Calculator — an infinite live tower over a calculator

The lean-gate calculator placed under the gate tower of `Keep.Core`.

The object system is an apply rule; the invariant is conservative
extension of the baseline. A level-0 proposal is a `Patch` — install an
arbitrary payload at a name. The gates never read the payload: a gate is
a *protection list*, and it admits a patch iff the patched name is
unprotected. Conservativity is about *where* you write, not *what* you
write.

A level-`n+1` proposal is itself a protection list — the description of a
replacement gate for level `n` — and the gate at level `n+1` admits it iff
it keeps protecting what level `n+1` demands. So one list generates the
whole infinite stack (`protect`), and one induction arms every level
(`protect_sound`). The tower has no frozen tail: every level is live.

Highlights:
- `protect_sound` — the standard stack is sound at every level, by a
  single induction on the level.
- `nil_unsound` / `no_sound_gate_admits_nil` — the unprotecting
  description is refused at *every* level: a sound gate cannot admit it,
  two, three, any number of levels above the harm it would eventually
  permit.
- `demo` theorems — a three-level cascade: admit an improvement, harden
  the gate to protect it, watch the clobber and the rollback both get
  refused; conclude safety from `tower_safe` and strict gain from the
  kernel-checked witness pair.
-/

namespace Calc

abbrev Rule := String → List Nat → Option Nat

/-- Baseline: `"+"` sums; `"id" [n]` is the β-redex `(λx. x) n`. -/
def base : Rule := fun op args =>
  if op = "+" then some (args.foldl (· + ·) 0)
  else if op = "id" then args.head?
  else none

/-- The master invariant: conservative extension of the baseline. -/
def CE (r : Rule) : Prop :=
  ∀ op args v, base op args = some v → r op args = some v

/-- A level-0 proposal: install payload `f` at name `op`. -/
structure Patch where
  op : String
  f : List Nat → Option Nat

def install (p : Patch) (r : Rule) : Rule :=
  fun op args => if op = p.op then p.f args else r op args

/-- The calculator world. Level 0 proposals are patches; every higher
level's proposals are protection lists. A gate description `l` at level 1
admits a patch iff its name avoids `l`; at level `n+2` it admits a
protection list iff that list still contains everything in `l`. -/
def world : Keep.World where
  S := Rule
  Inv := CE
  P := fun n => match n with
    | 0 => Patch
    | _ + 1 => List String
  act := install
  den := fun n => match n with
    | 0 => fun l p => !(l.contains p.op)
    | _ + 1 => fun l l' => l.all l'.contains

/-- The standard stack: one protection list, replicated at every level.
Gate 0 protects the names in `l`; gate `n+1` insists that any replacement
for gate `n` still protects them. -/
def protect (l : List String) : Keep.Gates world :=
  fun n => world.den n l

/-- Names outside the baseline's footprint are free: the baseline never
succeeds there. -/
theorem base_none {op : String} (h₁ : op ≠ "+") (h₂ : op ≠ "id")
    (args : List Nat) : base op args = none := by
  simp [base, h₁, h₂]

/-- A protection list covering the baseline footprint denotes a sound
level-0 gate — for *arbitrary payloads*. The gate reads the address, not
the code. -/
theorem den0_sound {l : List String} (hp : "+" ∈ l) (hid : "id" ∈ l) :
    Keep.Sound world 0 (world.den 0 l) := by
  refine fun p s adm hs op args v hv => ?_
  have hop : p.op ∉ l := by
    have h : (!(l.contains p.op)) = true := adm
    simpa using h
  have h₁ : p.op ≠ "+" := fun e => hop (by rw [e]; exact hp)
  have h₂ : p.op ≠ "id" := fun e => hop (by rw [e]; exact hid)
  have hne : op ≠ p.op := by
    rintro rfl
    rw [base_none h₁ h₂] at hv
    simp at hv
  have hs' := hs op args v hv
  show install p s op args = some v
  simpa [install, hne] using hs'

/-- **One induction arms the infinite tower.** The standard stack is
sound at every level. -/
theorem protect_sound {l : List String} (hp : "+" ∈ l) (hid : "id" ∈ l) :
    ∀ n, Keep.Sound world n (world.den n l)
  | 0 => den0_sound hp hid
  | n + 1 => fun l' adm => by
      have adm' : l.all (List.contains l') = true := adm
      refine protect_sound ?_ ?_ n
      · simpa using List.all_eq_true.mp adm' "+" hp
      · simpa using List.all_eq_true.mp adm' "id" hid

theorem protect_allSound {l : List String} (hp : "+" ∈ l)
    (hid : "id" ∈ l) : Keep.AllSound (protect l) :=
  fun n => protect_sound hp hid n

/-! ## Refusal at every level

`[]` is the unprotecting description: as a gate it admits everything
below it. At level 1 it would admit the collapse patch; at level 2 it
would admit the level-1 gate that admits the collapse patch; and so on.
It is unsound at every level — so no sound gate, at any height of the
tower, ever admits it. Corruption is refused arbitrarily many levels
before it could reach the object. -/

/-- The collapse patch: `(id 3) ⇒ 42`, Wand's β-break. -/
def collapse : Patch := ⟨"id", fun _ => some 42⟩

theorem nil_unsound : ∀ n, ¬ Keep.Sound world n (world.den n ([] : List String))
  | 0 => fun h => by
      have hbase : CE base := fun _ _ _ hv => hv
      have hadm : world.den 0 [] collapse = true := rfl
      have hCE : CE (install collapse base) := h collapse base hadm hbase
      have h3 : install collapse base "id" [3] = some 3 :=
        hCE "id" [3] 3 rfl
      simp [install, collapse] at h3
  | n + 1 => fun h =>
      nil_unsound n (h ([] : List String) rfl)

/-- No sound gate at any level admits the unprotecting description. -/
theorem no_sound_gate_admits_nil {n : Nat} {h : world.P (n + 1) → Bool}
    (hs : Keep.Sound world (n + 1) h) : h [] = false := by
  cases e : h ([] : List String) with
  | false => rfl
  | true => exact absurd (hs [] e) (nil_unsound n)

/-! ## The demo trace: improve, protect, refuse

Four configurations. `t0`: baseline under the standard stack protecting
`{+, id}`. `t1`: `mult` admitted at level 0 — `(* 2 3 4) ⇒ 24`, strictly
beyond the baseline. `t2`: gate 0 replaced (via level 1) by one that also
protects `"*"` — the clobber is now refused. `t3`: gate 1 replaced (via
level 2) by one that *demands* `"*"` stay protected — so the rollback is
refused one level up.

Then the refusals: clobbering `"*"` is refused at level 0 (it was
admissible at `t1`!), and rolling back the protection is refused at
level 1. -/

def mult : Patch := ⟨"*", fun args => some (args.foldl (· * ·) 1)⟩

def l₀ : List String := ["+", "id"]
def l₁ : List String := ["+", "id", "*"]

def t0 : Keep.Config world := ⟨base, protect l₀⟩
def t1 : Keep.Config world := ⟨install mult base, protect l₀⟩
def t2 : Keep.Config world := ⟨t1.state, t1.gates.set 0 (world.den 0 l₁)⟩
def t3 : Keep.Config world := ⟨t2.state, t2.gates.set 1 (world.den 1 l₁)⟩

theorem step01 : Keep.Step world t0 t1 := Keep.Step.act (c := t0) mult rfl
theorem step12 : Keep.Step world t1 t2 := Keep.Step.swap (c := t1) 0 l₁ rfl
theorem step23 : Keep.Step world t2 t3 := Keep.Step.swap (c := t2) 1 l₁ rfl

theorem demo_reach : Keep.Reach world t0 t3 :=
  .step (.step (.step (.refl t0) step01) step12) step23

theorem t0_safe : Keep.Safe t0 :=
  ⟨fun _ _ _ hv => hv, protect_allSound (by decide) (by decide)⟩

/-- The whole cascade is safe: invariant intact, every gate in the final
stack sound — including the two gates installed along the way, whose
soundness is derived, not assumed. -/
theorem demo_safe : Keep.Safe t3 := Keep.tower_safe t0_safe demo_reach

/-- Before hardening, the clobber was admissible. -/
theorem clobber_was_admissible (f : List Nat → Option Nat) :
    t1.gates 0 ⟨"*", f⟩ = true := rfl

/-- After hardening, the clobber is refused — whatever its payload. -/
theorem clobber_refused (f : List Nat → Option Nat) :
    t2.gates 0 ⟨"*", f⟩ = false := rfl

/-- After the meta-hardening, unprotecting `"*"` is refused at level 1:
the gate that would re-admit the clobber cannot itself be installed. -/
theorem rollback_refused : t3.gates 1 l₀ = false := rfl

/-- **The improvement pair, kernel-checked.** No regression: the final
state conservatively extends the baseline (from `demo_safe`). Strict
gain: the witness `(* 2 3 4)` — the baseline cannot evaluate it; the
final state evaluates it to `24`. -/
theorem demo_improves :
    CE t3.state
      ∧ base "*" [2, 3, 4] = none
      ∧ t3.state "*" [2, 3, 4] = some 24 :=
  ⟨demo_safe.1, rfl, rfl⟩

end Calc
