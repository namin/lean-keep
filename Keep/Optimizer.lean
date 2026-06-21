import Keep.Core

/-!
# Keep.Optimizer — improving the verifier, not just the gate

The other instances in this development *harden* gates: each reflective step
admits **less**. This one does the opposite, and that is the point.

The object system is a peephole optimizer holding a registry of rewrite rules.
The invariant is that every installed rule is semantics-preserving (`SemEq`).
Gate 0 is a *validator*: it decides which proposed rewrites may be installed.

The story is a **safe relaxation**:

1. A useful rewrite — `x + x ↦ x << 1`, strictly cheaper — is *rejected* by the
   weak validator `basicCheck`, which only knows syntactic identities.
2. Through gate 1 we install a stronger validator, `exhaustiveCheck`, which
   decides semantic equality at all 16 inputs. It admits **strictly more** than
   the old gate (`exhaustive_strictly_better`) while remaining sound
   (`exhaustiveCheck_sound`).
3. The new gate 0 now admits the rewrite, and it is installed.
4. Semantic correctness is *still* guaranteed — read straight off the final
   invariant via `Keep.tower_safe` (`installed_semEq`).

So the gate did not get more cautious; it got more *capable*, without ever
weakening the invariant. The fixed trusted component is still Lean's kernel:
arbitrary checkers may be proposed, but a checker only inhabits
`CertifiedValidator` once the kernel has verified its soundness proof. That is
the LCF discipline lifted to the gate — what changes here is the executable
validation policy, nothing about the trust root.
-/

namespace Opt

/-! ## A tiny finite expression language -/

/-- Expressions over one 4-bit variable. -/
inductive Expr where
  | var
  | zero
  | add : Expr → Expr → Expr
  | shl1 : Expr → Expr
  deriving DecidableEq

/-- Evaluate at a 4-bit input. `shl1 e` doubles `e` modulo 16 — exactly a
one-bit left shift in 4-bit arithmetic. -/
def eval : Expr → Fin 16 → Fin 16
  | .var,     x => x
  | .zero,    _ => 0
  | .add a b, x => eval a x + eval b x
  | .shl1 a,  x => 2 * eval a x

/-- A transparent syntactic cost model. -/
def cost : Expr → Nat
  | .var      => 1
  | .zero     => 1
  | .add a b  => 1 + cost a + cost b
  | .shl1 a   => 1 + cost a

/-- A rewrite rule `lhs ↦ rhs`. -/
structure Rewrite where
  lhs : Expr
  rhs : Expr
  deriving DecidableEq

/-- Semantic equivalence: the two sides agree on every 4-bit input. -/
def SemEq (r : Rewrite) : Prop :=
  ∀ x : Fin 16, eval r.lhs x = eval r.rhs x

/-- The central witness: `x + x ↦ x << 1`. -/
def doubleRule : Rewrite := ⟨.add .var .var, .shl1 .var⟩

/-- The rewrite strictly reduces cost: `x << 1` (size 2) is cheaper than
`x + x` (size 3). -/
theorem double_cheaper : cost doubleRule.rhs < cost doubleRule.lhs := by decide

/-! ## A weak and a strong validator -/

/-- A small decided fact over the finite domain, used in `basicCheck_sound`. -/
theorem fin_add_zero : ∀ v : Fin 16, v + 0 = v := by decide

/-- **The weak validator.** It accepts a rewrite only when the two sides are
syntactically identical, or when the left is literally `e + 0` for the right
`e`. Both are transparently semantics-preserving; it is deliberately myopic
and builds no simplifier. -/
def basicCheck (r : Rewrite) : Bool :=
  decide (r.lhs = r.rhs) || decide (r.lhs = .add r.rhs .zero)

theorem basicCheck_sound : ∀ r, basicCheck r = true → SemEq r := by
  intro r h x
  unfold basicCheck at h
  rw [Bool.or_eq_true] at h
  cases h with
  | inl h => rw [of_decide_eq_true h]
  | inr h =>
      have he : r.lhs = .add r.rhs .zero := of_decide_eq_true h
      rw [he]
      show eval r.rhs x + (0 : Fin 16) = eval r.rhs x
      exact fin_add_zero (eval r.rhs x)

/-- The weak validator cannot see the useful rewrite. -/
theorem basic_rejects_double : basicCheck doubleRule = false := by decide

/-- **The strong validator.** It decides semantic equality at all 16 inputs.
The generic soundness theorem just below is the substance — not that any one
rule happens to pass. -/
def exhaustiveCheck (r : Rewrite) : Bool :=
  decide (∀ x : Fin 16, eval r.lhs x = eval r.rhs x)

/-- **The generic soundness theorem for the stronger validator.** -/
theorem exhaustiveCheck_sound : ∀ r, exhaustiveCheck r = true → SemEq r := by
  intro r h
  exact (of_decide_eq_true h : ∀ x : Fin 16, eval r.lhs x = eval r.rhs x)

/-- The strong validator is also complete on this language: anything
semantically equal is admitted. (Used only to show the relaxation is genuine.) -/
theorem exhaustiveCheck_complete : ∀ r, SemEq r → exhaustiveCheck r = true := by
  intro r h
  exact decide_eq_true (h : ∀ x : Fin 16, eval r.lhs x = eval r.rhs x)

/-- The strong validator admits the useful rewrite. -/
theorem exhaustive_accepts_double : exhaustiveCheck doubleRule = true := by decide

/-! ## The new gate is strictly more permissive -/

def Extends (old new : Rewrite → Bool) : Prop :=
  ∀ r, old r = true → new r = true

def StrictlyBetter (old new : Rewrite → Bool) : Prop :=
  Extends old new ∧ ∃ r, old r = false ∧ new r = true

/-- **The replacement admits strictly more.** Everything `basicCheck` accepts is
semantics-preserving (`basicCheck_sound`), hence accepted by `exhaustiveCheck`
(`exhaustiveCheck_complete`); and `doubleRule` is accepted by the new gate but
not the old. This is *relaxation*, established without appeal to
`Keep.sound_antitone` — that lemma is for hardening and does not apply here. -/
theorem exhaustive_strictly_better : StrictlyBetter basicCheck exhaustiveCheck :=
  ⟨fun r hr => exhaustiveCheck_complete r (basicCheck_sound r hr),
   doubleRule, basic_rejects_double, exhaustive_accepts_double⟩

/-! ## Proof-carrying validators (the LCF boundary) -/

/-- A checker bundled with a kernel-checked soundness proof. Anyone may
*propose* an arbitrary executable checker, but it inhabits `CertifiedValidator`
only after Lean has verified `sound`. -/
structure CertifiedValidator where
  check : Rewrite → Bool
  sound : ∀ r, check r = true → SemEq r

def basicValidator : CertifiedValidator := ⟨basicCheck, basicCheck_sound⟩
def exhaustiveValidator : CertifiedValidator := ⟨exhaustiveCheck, exhaustiveCheck_sound⟩

/-! ## The optimizer as a `Keep.World` -/

/-- The registry invariant: every installed rewrite is semantics-preserving. -/
def Valid (rs : List Rewrite) : Prop := ∀ r ∈ rs, SemEq r

/-- The optimizer world. State is the installed rewrite registry. A level-0
proposal is a `Rewrite`; a level-`n+1` proposal is a `CertifiedValidator`,
which `den n` reads as a replacement gate for level `n`. Only one reflective
validator upgrade is needed, so `den` above level 0 is the frozen
(admit-nothing) gate description. -/
def world : Keep.World where
  S := List Rewrite
  Inv := Valid
  P := fun n => match n with
    | 0     => Rewrite
    | _ + 1 => CertifiedValidator
  act := fun r rs => r :: rs
  den := fun n => match n with
    | 0     => fun v => v.check
    | _ + 1 => fun _ _ => false

/-- **Any sound checker is a sound level-0 gate.** When it admits a rewrite,
consing that rewrite onto a valid registry keeps the registry valid: the new
rule's soundness comes from the checker, the rest from the old registry. -/
theorem check_sound_gate (chk : Rewrite → Bool)
    (hchk : ∀ r, chk r = true → SemEq r) :
    Keep.Sound world 0 chk := by
  intro r rs adm hValid
  show Valid (r :: rs)
  intro r' hr'
  rcases List.mem_cons.mp hr' with e | e
  · rw [e]; exact hchk r adm
  · exact hValid r' e

/-- A certified validator's checker is a sound level-0 gate — the level-1
proposal's `sound` field is exactly what discharges the obligation. -/
theorem certified_gate0_sound (v : CertifiedValidator) :
    Keep.Sound world 0 (world.den 0 v) :=
  check_sound_gate v.check v.sound

/-- The initial stack: gate 0 is the weak `basicCheck`; gate 1 admits *every*
certified validator; gates ≥ 2 are frozen (one upgrade suffices). -/
def initGates : Keep.Gates world
  | 0       => basicCheck
  | 1       => fun _ => true
  | (n + 2) => Keep.frozen world (n + 2)

/-- **The whole initial stack is sound.** Gate 1 is where the LCF boundary pays
off: its Boolean answer is unconditionally `true`, yet its soundness obligation
is discharged *entirely* by the proposal's own `sound` field (via
`certified_gate0_sound`), never by re-examining the proposed checker. Admission
is easy only because constructing the proposal was already kernel-checked. -/
theorem initGates_sound : Keep.AllSound initGates
  | 0       => check_sound_gate basicCheck basicCheck_sound
  | 1       => fun (v : CertifiedValidator) _ => certified_gate0_sound v
  | (n + 2) => Keep.frozen_sound world (n + 2)

/-! ## The demonstration trace -/

/-- `c0`: empty registry, gate 0 = `basicCheck`. -/
def c0 : Keep.Config world := ⟨[], initGates⟩

/-- `c1`: gate 0 replaced by `exhaustiveCheck`, by admitting
`exhaustiveValidator` at gate 1. -/
def c1 : Keep.Config world :=
  ⟨c0.state, c0.gates.set 0 (world.den 0 exhaustiveValidator)⟩

/-- `c2`: `doubleRule` admitted by the new gate 0 and installed. -/
def c2 : Keep.Config world :=
  ⟨world.act doubleRule c1.state, c1.gates⟩

/-- After the swap, gate 0 *is* `exhaustiveCheck`. -/
theorem c1_gate0 : c1.gates 0 = exhaustiveCheck :=
  Keep.Gates.set_self c0.gates 0 (world.den 0 exhaustiveValidator)

/-- The weak initial gate 0 rejects the useful rewrite. -/
theorem c0_rejects_double : c0.gates 0 doubleRule = false := basic_rejects_double

/-- The swapped-in gate 0 admits the useful rewrite. -/
theorem c1_admits_double : c1.gates 0 doubleRule = true := by
  rw [c1_gate0]; exact exhaustive_accepts_double

theorem step01 : Keep.Step world c0 c1 :=
  Keep.Step.swap (c := c0) 0 exhaustiveValidator rfl

theorem step12 : Keep.Step world c1 c2 :=
  Keep.Step.act (c := c1) doubleRule c1_admits_double

theorem demo_reach : Keep.Reach world c0 c2 :=
  .step (.step (.refl c0) step01) step12

theorem nil_valid : Valid [] := by intro r hr; cases hr

theorem c0_safe : Keep.Safe c0 := ⟨nil_valid, initGates_sound⟩

/-- The whole trace is safe: invariant intact, every gate in the final stack
sound — including the validator installed mid-flight, whose soundness is
*derived* from gate 1, not assumed. Obtained from `Keep.tower_safe`. -/
theorem demo_safe : Keep.Safe c2 := Keep.tower_safe c0_safe demo_reach

/-- The installed rule really is in the final registry. (`show … from` pins the
state's type to `List Rewrite`, which is defeq to the opaque `world.S`.) -/
theorem installed_mem : doubleRule ∈ show List Rewrite from c2.state := by decide

/-- **The payoff, read off the final invariant.** `SemEq doubleRule` is not
re-proved here: it is extracted from `demo_safe.1` — the registry invariant at
the end of the certified trace — so the example visibly exercises
`Keep.tower_safe`. -/
theorem installed_semEq : SemEq doubleRule :=
  demo_safe.1 doubleRule installed_mem

/-- **The headline.** A useful rewrite the current verifier rejects becomes
installable through a strictly-more-permissive, still-sound verifier, with
correctness preserved end to end. -/
theorem demo_improves_validator :
    StrictlyBetter basicCheck exhaustiveCheck
      ∧ c0.gates 0 doubleRule = false
      ∧ c1.gates 0 doubleRule = true
      ∧ (doubleRule ∈ show List Rewrite from c2.state)
      ∧ SemEq doubleRule
      ∧ cost doubleRule.rhs < cost doubleRule.lhs :=
  ⟨exhaustive_strictly_better, c0_rejects_double, c1_admits_double,
   installed_mem, installed_semEq, double_cheaper⟩

end Opt
