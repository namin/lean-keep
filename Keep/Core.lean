/-!
# Keep.Core — the gate tower, abstractly

Every reasonable-reflection artifact gates the *object* level. This file
gates the *gate*: a tower in which each level's gate is itself replaceable,
under a certificate checked by the gate one level up.

A `World` fixes an object system with an invariant, and a level-indexed
language of proposals. A level-0 proposal denotes a state change. A
level-`n+1` proposal denotes a *gate description*: a decidable checker on
level-`n` proposals. Gates are data; only the kernel is fixed.

`Sound` is iterated soundness: a level-0 gate is sound when everything it
admits preserves the invariant; a level-`n+1` gate is sound when every
gate description it admits denotes a sound level-`n` gate.

The headline is `tower_safe`: along any reachable trace of admitted steps —
object modifications and gate replacements at any level, interleaved — the
invariant and the soundness of the whole stack are preserved. No gate's
soundness is assumed along the trace; each replacement's soundness is
*derived* from the admitting gate one level up.
-/

namespace Keep

/-- An object system with its invariant, and a level-indexed proposal
language. `act` applies a level-0 proposal; `den n` reads a level-`n+1`
proposal as a replacement gate for level `n`. -/
structure World where
  S : Type
  Inv : S → Prop
  P : Nat → Type
  act : P 0 → S → S
  den : (n : Nat) → P (n + 1) → (P n → Bool)

/-- Iterated soundness of a gate, relative to the invariant. -/
def Sound (W : World) : (n : Nat) → (W.P n → Bool) → Prop
  | 0, h => ∀ p s, h p = true → W.Inv s → W.Inv (W.act p s)
  | n + 1, h => ∀ p, h p = true → Sound W n (W.den n p)

/-- The gate stack: one gate per level, all the way up. -/
def Gates (W : World) := (n : Nat) → W.P n → Bool

/-- Replace the gate at level `n`. -/
def Gates.set {W : World} (g : Gates W) (n : Nat) (h : W.P n → Bool) :
    Gates W :=
  fun m => if e : n = m then e ▸ h else g m

theorem Gates.set_self {W : World} (g : Gates W) (n : Nat)
    (h : W.P n → Bool) : g.set n h n = h := by
  simp [Gates.set]

theorem Gates.set_ne {W : World} (g : Gates W) {n m : Nat}
    (h : W.P n → Bool) (e : n ≠ m) : g.set n h m = g m := by
  simp [Gates.set, e]

/-- A running configuration: the object state and the gate stack. -/
structure Config (W : World) where
  state : W.S
  gates : Gates W

/-- One admitted step. `act`: a level-0 proposal passes gate 0 and fires.
`swap`: a level-`n+1` proposal passes gate `n+1` and *replaces gate `n`*. -/
inductive Step (W : World) : Config W → Config W → Prop
  | act {c : Config W} (p : W.P 0)
      (adm : c.gates 0 p = true) :
      Step W c ⟨W.act p c.state, c.gates⟩
  | swap {c : Config W} (n : Nat) (p : W.P (n + 1))
      (adm : c.gates (n + 1) p = true) :
      Step W c ⟨c.state, c.gates.set n (W.den n p)⟩

/-- Reachability by admitted steps. -/
inductive Reach (W : World) : Config W → Config W → Prop
  | refl (c : Config W) : Reach W c c
  | step {a b c : Config W} : Reach W a b → Step W b c → Reach W a c

/-- Every level of the stack is sound. -/
def AllSound {W : World} (g : Gates W) : Prop := ∀ n, Sound W n (g n)

/-- The tower invariant: object invariant holds, gate stack is sound. -/
def Safe {W : World} (c : Config W) : Prop :=
  W.Inv c.state ∧ AllSound c.gates

theorem Step.safe {W : World} {c c' : Config W}
    (hs : Safe c) (st : Step W c c') : Safe c' := by
  obtain ⟨hInv, hAll⟩ := hs
  cases st with
  | act p adm =>
      exact ⟨hAll 0 p c.state adm hInv, hAll⟩
  | swap n p adm =>
      refine ⟨hInv, fun m => ?_⟩
      show Sound W m (c.gates.set n (W.den n p) m)
      by_cases e : n = m
      · subst e
        rw [Gates.set_self]
        exact hAll (n + 1) p adm
      · rw [Gates.set_ne _ _ e]
        exact hAll m

/-- **Trace safety with no assumed gate soundness.** From a safe initial
configuration, every reachable configuration is safe: the invariant holds
and every gate in the stack — including every gate installed *en route*,
at any level — is sound. Each installed gate's soundness is derived from
the admitting gate one level up, recursively grounded in the initial
stack. -/
theorem tower_safe {W : World} {c c' : Config W}
    (hs : Safe c) (r : Reach W c c') : Safe c' := by
  induction r with
  | refl => exact hs
  | step _ st ih => exact st.safe ih

/-- Strictness is free: a gate that admits less than a sound gate is
sound. Hardening never needs a certificate. -/
theorem sound_antitone {W : World} {n : Nat} {h h' : W.P n → Bool}
    (imp : ∀ p, h' p = true → h p = true)
    (snd : Sound W n h) : Sound W n h' := by
  cases n with
  | zero => exact fun p s hp hi => snd p s (imp p hp) hi
  | succ n => exact fun p hp => snd p (imp p hp)

/-- The frozen gate admits nothing. It is vacuously sound at every level:
this is the gate every benchmark-gated self-improving system implicitly
installs above its evaluator. A frozen tail is sound — and dead. -/
def frozen (W : World) (n : Nat) : W.P n → Bool := fun _ => false

theorem frozen_sound (W : World) (n : Nat) : Sound W n (frozen W n) := by
  cases n with
  | zero => exact fun p _ hp => absurd hp (by simp [frozen])
  | succ n => exact fun p hp => absurd hp (by simp [frozen])

end Keep
