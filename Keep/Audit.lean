import Keep.Core
import Keep.Calculator
import Keep.Dial
import Keep.Optimizer

/-!
# Keep.Audit — pinned axiom footprint

Build fails if any theorem's axiom dependencies change. Standard axioms
only (`propext`, `Quot.sound`); no `Classical.choice`, no `sorry`, no
`native_decide` anywhere in the development. The refusal theorems are
`rfl`: they depend on no axioms at all.
-/

/-- info: 'Keep.tower_safe' depends on axioms: [propext] -/
#guard_msgs in #print axioms Keep.tower_safe

/-- info: 'Keep.sound_antitone' does not depend on any axioms -/
#guard_msgs in #print axioms Keep.sound_antitone

/-- info: 'Keep.frozen_sound' depends on axioms: [propext] -/
#guard_msgs in #print axioms Keep.frozen_sound

/-- info: 'Calc.protect_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Calc.protect_sound

/-- info: 'Calc.nil_unsound' depends on axioms: [propext] -/
#guard_msgs in #print axioms Calc.nil_unsound

/-- info: 'Calc.no_sound_gate_admits_nil' depends on axioms: [propext] -/
#guard_msgs in #print axioms Calc.no_sound_gate_admits_nil

/-- info: 'Calc.demo_safe' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Calc.demo_safe

/-- info: 'Calc.demo_improves' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Calc.demo_improves

/-- info: 'Calc.clobber_refused' does not depend on any axioms -/
#guard_msgs in #print axioms Calc.clobber_refused

/-- info: 'Calc.rollback_refused' does not depend on any axioms -/
#guard_msgs in #print axioms Calc.rollback_refused

/-- info: 'Dial.clamp_sound' does not depend on any axioms -/
#guard_msgs in #print axioms Dial.clamp_sound

/-- info: 'Dial.overcap_unsound' does not depend on any axioms -/
#guard_msgs in #print axioms Dial.overcap_unsound

/-- info: 'Dial.no_sound_gate_admits_overcap' does not depend on any axioms -/
#guard_msgs in #print axioms Dial.no_sound_gate_admits_overcap

/-- info: 'Dial.d1_safe' depends on axioms: [propext] -/
#guard_msgs in #print axioms Dial.d1_safe

/-! ## Optimizer (safe relaxation)

The registry is a plain `List`, so these never touch `Quot.sound`: the
footprint is `propext` only, lighter than the Calculator's. The rejection fact
is `by decide` and depends on no axioms. -/

/-- info: 'Opt.exhaustiveCheck_sound' depends on axioms: [propext] -/
#guard_msgs in #print axioms Opt.exhaustiveCheck_sound

/-- info: 'Opt.basicCheck_sound' depends on axioms: [propext] -/
#guard_msgs in #print axioms Opt.basicCheck_sound

/-- info: 'Opt.exhaustive_strictly_more_permissive' depends on axioms: [propext] -/
#guard_msgs in #print axioms Opt.exhaustive_strictly_more_permissive

/-- info: 'Opt.initGates_sound' depends on axioms: [propext] -/
#guard_msgs in #print axioms Opt.initGates_sound

/-- info: 'Opt.demo_safe' depends on axioms: [propext] -/
#guard_msgs in #print axioms Opt.demo_safe

/-- info: 'Opt.installed_semEq' depends on axioms: [propext] -/
#guard_msgs in #print axioms Opt.installed_semEq

/-- info: 'Opt.demo_improves_validator' depends on axioms: [propext] -/
#guard_msgs in #print axioms Opt.demo_improves_validator

/-- info: 'Opt.basic_rejects_double' does not depend on any axioms -/
#guard_msgs in #print axioms Opt.basic_rejects_double
