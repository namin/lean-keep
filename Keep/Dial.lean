import Keep.Core

/-!
# Keep.Dial — the tutorial instance

The smallest possible `World`, companion to `TUTORIAL.md`. A dial holds a
setting that must never exceed 100. Proposals at every level are plain
numbers: at level 0, the requested setting; at level `n+1`, a *cap* — the
description of a replacement gate for level `n`, admitting requests (or
caps) up to it. One number generates the whole stack (`clamp`), one
induction arms every level (`clamp_sound`), and a cap above the limit is
refused at every height (`no_sound_gate_admits_overcap`).
-/

namespace Dial

def world : Keep.World where
  S := Nat
  Inv := fun s => s ≤ 100
  P := fun _ => Nat
  act := fun p _ => p
  den := fun _ c p => decide (p ≤ c)

/-- One cap, replicated at every level of the stack. -/
def clamp (c : Nat) : Keep.Gates world := fun n => world.den n c

/-- A within-limit cap is sound at every level: a single induction. -/
theorem clamp_sound {c : Nat} (hc : c ≤ 100) :
    ∀ n, Keep.Sound world n (world.den n c)
  | 0 => fun _ _ adm _ => Nat.le_trans (of_decide_eq_true adm) hc
  | n + 1 => fun _ adm =>
      clamp_sound (Nat.le_trans (of_decide_eq_true adm) hc) n

theorem clamp_allSound {c : Nat} (hc : c ≤ 100) :
    Keep.AllSound (clamp c) :=
  fun n => clamp_sound hc n

/-- The over-limit cap is unsound at every level: as a gate it would admit
itself downward until a request above 100 fires. -/
theorem overcap_unsound :
    ∀ n, ¬ Keep.Sound world n (world.den n ((1000 : Nat)))
  | 0 => fun h =>
      absurd (h (1000 : Nat) (0 : Nat) rfl (show (0 : Nat) ≤ 100 by decide))
        (show ¬ (1000 : Nat) ≤ 100 by decide)
  | n + 1 => fun h => overcap_unsound n (h (1000 : Nat) rfl)

/-- So no sound gate, at any height, admits it. -/
theorem no_sound_gate_admits_overcap {n : Nat} {h : world.P (n + 1) → Bool}
    (hs : Keep.Sound world (n + 1) h) : h (1000 : Nat) = false := by
  cases e : h (1000 : Nat) with
  | false => rfl
  | true => exact absurd (hs (1000 : Nat) e) (overcap_unsound n)

/-! The hardening beat, in miniature: tighten the cap from 100 to 90
through gate 1, and a request that was admissible is refused. -/

def d0 : Keep.Config world := ⟨(0 : Nat), clamp 100⟩
def d1 : Keep.Config world :=
  ⟨d0.state, d0.gates.set 0 (world.den 0 (90 : Nat))⟩

theorem tighten : Keep.Step world d0 d1 :=
  Keep.Step.swap (c := d0) 0 (90 : Nat) rfl

theorem was_admissible : d0.gates 0 (95 : Nat) = true := rfl
theorem now_refused : d1.gates 0 (95 : Nat) = false := rfl

theorem d0_safe : Keep.Safe d0 :=
  ⟨show (0 : Nat) ≤ 100 by decide, clamp_allSound (by decide)⟩

theorem d1_safe : Keep.Safe d1 :=
  Keep.tower_safe d0_safe (.step (.refl d0) tighten)

end Dial
