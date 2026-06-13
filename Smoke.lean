import Keep
open Keep Calc

def check (label : String) (actual expected : Option Nat) : IO Unit := do
  if actual = expected then
    IO.println s!"OK  {label}: {actual}"
  else
    IO.println s!"XX  {label}: got {actual}, expected {expected}"

def gate (label : String) (actual expected : Bool) : IO Unit := do
  let verdict := if actual then "ADMIT" else "REFUSE"
  if actual = expected then
    IO.println s!"OK  {label}: {verdict}"
  else
    IO.println s!"XX  {label}: {verdict} (expected otherwise)"

def main : IO Unit := do
  IO.println "=== Scene 1: baseline under the standard stack ==="
  check "(+ 1 2)"   (t0.state "+"  [1, 2])    (some 3)
  check "(id 3)"    (t0.state "id" [3])       (some 3)
  check "(* 2 3 4)" (t0.state "*"  [2, 3, 4]) none

  IO.println ""
  IO.println "=== Scene 2: level 0 — admit mult, refuse collapse ==="
  gate "propose mult (fresh name *)" (t0.gates 0 mult) true
  check "(* 2 3 4) after admission" (t1.state "*" [2, 3, 4]) (some 24)
  check "(id 3) preserved"          (t1.state "id" [3])      (some 3)
  gate "propose collapse (writes id)" (t0.gates 0 collapse) false
  IO.println "    ungated, for contrast:"
  check "  collapse (id 3) — β COLLAPSED"
    (install collapse base "id" [3]) (some 42)

  IO.println ""
  IO.println "=== Scene 3: level 1 — replace gate 0, locking mult in ==="
  gate "swap gate 0 to protect {+,id,*}" (t1.gates 1 l₁) true
  gate "clobber * — admissible BEFORE"  (t1.gates 0 ⟨"*", fun _ => some 0⟩) true
  gate "clobber * — refused AFTER"      (t2.gates 0 ⟨"*", fun _ => some 0⟩) false

  IO.println ""
  IO.println "=== Scene 4: level 2 — harden gate 1, refuse the rollback ==="
  gate "swap gate 1 to demand * protected" (t2.gates 2 l₁) true
  gate "roll gate 0 back to {+,id}"        (t3.gates 1 l₀) false

  IO.println ""
  IO.println "=== Scene 5: the unprotecting description, refused at every level ==="
  gate "[] at level 1" (t3.gates 1 ([] : List String)) false
  gate "[] at level 2" (t3.gates 2 ([] : List String)) false
  gate "[] at level 3" (t3.gates 3 ([] : List String)) false
  IO.println "    `no_sound_gate_admits_nil`: at *every* level n, any sound"
  IO.println "    gate refuses it — the gate that would admit the gate that"
  IO.println "    would admit the collapse is itself inadmissible, all the"
  IO.println "    way up. Corruption is refused before it is even near."

  IO.println ""
  IO.println "=== Verdict (kernel-checked, see Keep/Calculator.lean) ==="
  IO.println "    tower_safe:     invariant + stack soundness along the trace,"
  IO.println "                    installed gates' soundness derived, not assumed."
  IO.println "    demo_improves:  no regression (CE) ∧ strict gain:"
  check "      witness before" (base "*" [2, 3, 4])     none
  check "      witness after " (t3.state "*" [2, 3, 4]) (some 24)
