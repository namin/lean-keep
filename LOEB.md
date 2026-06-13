# Löb and the gate one level up

Why gate replacement in a running system is not blocked by the Löbian
obstacle — and where the obstacle genuinely still stands. Companion note to
[README.md](README.md); the relevant code is `Sound` and `tower_safe` in
[Keep/Core.lean](Keep/Core.lean).

References: Yudkowsky & Herreshoff, [*Tiling Agents for Self-Modifying AI,
and the Löbian Obstacle*](https://intelligence.org/files/TilingAgentsDraft.pdf)
(2013); Schmidhuber, [*Gödel Machines*](https://arxiv.org/abs/cs/0309048);
Feferman, *Transfinite recursive progressions of axiomatic theories* (JSL
1962); Beklemishev, *Reflection principles and provability algebras in
formal arithmetic* (Russian Math. Surveys 2005).

## 1. The theorem, and the asymmetry inside it

Löb's theorem: for any consistent theory T strong enough to talk about its
own proofs (□φ = "φ is provable in T"),

> if T ⊢ □φ → φ, then T ⊢ φ.

Contrapositive: T can never prove "if φ is provable in me, then φ" for any
φ it cannot already prove outright. So the **soundness schema**

> ∀φ : □_T⌈φ⌉ → φ   ("my proofs can be trusted")

is unprovable in T. Gödel II is the instance φ = ⊥.

The asymmetry that everything below turns on (Tiling Agents, p. 7 and
fn. 31):

- T **cannot** trust its own proofs *in the abstract*: "I don't know if φ
  is true, but if any proof of φ exists from my axioms, φ is true" — never.
- T **can** trust any *particular* proof: handed a concrete derivation of
  φ, it checks it and thereby concludes φ. No schema needed.

Schema-trust: blocked. One-at-a-time trust: free.

## 2. The obstacle: why self-modifying agents need the blocked kind

The tiling setup. Agent A¹ reasons in T and constructs a successor A⁰ that
also reasons in T. The successor is autonomous — A¹ cannot simulate its
future actions ("Vingean reflection": the offspring's actions appear only
inside quantifiers). All A¹ knows is the design fact:

> A⁰ acts only after producing a T-proof that the action is safe.

To conclude "therefore A⁰'s actions *are* safe," A¹ must pass from *A⁰
proved it* to *it is true* — for proofs A¹ will never see, of statements
not yet formulated. That is exactly □_T → truth, quantified over the
successor's entire unseen future. Löb forbids it. Consequence: A¹ must
reason in a *strictly stronger* theory than A⁰, and proof strength descends
with every generation — the paper's "telomere" that shortens on each
self-modification. Its partial escapes (the T-n descent, Fallenstein's
T_κ) each give up something real (a standard model; an interpretable
constant).

The structural signature of the obstacle: **the trust decision is made
once, up front, over an open-ended future of proofs the certifier will
never inspect.** Call it compile-time trust, or delegation.

(The Gödel machine has the same shape — its "meta-level collapse" (§4.3)
puts all future self-modifications under one theorem proven before the
switch — and never mentions Löb; consistency of its axiom system 𝒜 is
assumed from outside.)

## 3. The escape: mediation instead of delegation

A runtime-gated tower — this artifact, or any LCF descendant — never
certifies the future. The kernel stays in the loop: every modification,
*including every replacement gate*, arrives as a particular concrete
certificate and is checked at admission time by the same fixed kernel.
That is the permitted side of the asymmetry: particular proofs, one at a
time, forever.

The crux is what a gate-swap certificate quantifies over. This artifact's

> `Sound n h` = "everything the policy `h` accepts preserves the invariant"

*looks* like a soundness schema, but it is a statement about a **program**
— a Bool-valued filter on syntax — proved by ordinary case analysis in the
ambient logic. It is *not* a statement about **provability in the ambient
logic**. No □ occurs anywhere inside the system; no level ever asserts
"proofs checked below me are true." Concretely: the certificate for the
calculator's gate `fun p => !(l.contains p.op)` is a lemma that a
list-membership test implies conservative extension
(`Calc.protect_sound`) — induction on a list, not reflection on a proof
predicate.

So the two towers are different objects:

- The **tiling tower stacks theories.** Each level must out-prove the one
  below; Löb makes the descent mandatory; logical strength is the currency
  being spent.
- The **gate tower stacks policies.** Each level governs the filter below;
  every proof at every level lives in one ambient logic, checked by one
  kernel; logical strength is constant. Löb has nothing to grab.

The observation: *for governing a running system, the policy tower
suffices.* Depth in authority was needed; depth in strength never was.
This is the LCF move (`thm`: don't certify the proof search, check each
proof) applied one level up, to the gates themselves.

## 4. The price, and where Löb still stands

Two honest costs:

1. **Perpetual mediation.** The kernel can never hand off and walk away.
   The tiling agent wants to *delegate* — build the successor, then exit —
   and that ambition is precisely what forces the quantified schema.
   Giving it up is what dissolves the obstacle.
2. **The kernel is the one frozen thing.** If the system replaced its own
   *checker* and internally certified "the new checker's proofs are
   trustworthy," that is □ → truth for a same-strength system; Löb applies
   in full, and the strength descent starts exactly there.

Boundary, stated crisply: **one immutable kernel, unboundedly many mutable
gates.** Contemporary self-improving systems freeze the *gate* because
they cannot certify gate changes; only the *checker* ever needed freezing.

## 5. Growing strength lawfully

To genuinely trust a *stronger* system, logic has known the lawful route
for sixty years: iterated reflection — T, T+Con(T), T+reflection, …,
transfinitely, externally indexed by ordinal notations (Feferman's
progressions; Beklemishev's analysis). Same fork, proof-theoretic
statement: depth in policy space is free (this artifact); depth in
proof-theoretic strength is priced in ordinals (that literature). The
tiling-agents paper builds Turing–Feferman progressions without citing
Feferman — it rediscovers them from the descending side.

## 6. Three positions

| | trust decision | Löb status | strength over time |
|---|---|---|---|
| **Gödel machine** | collapse: one theorem up front covers all future self-mods | unmentioned; consistency of 𝒜 assumed | constant by assumption |
| **Tiling agents** | delegate: quantified trust in the successor's unseen proofs | blocked; partial escapes sacrifice a desideratum | descends (telomere) |
| **This artifact** | mediate: particular certificates, checked at admission, forever | immune — no □ inside the system | constant by construction |

In one paragraph: Löb's theorem says you cannot trust your own proofs in
the abstract, only one at a time. Self-modifying agents that certify
successors up front need the abstract kind and are blocked; a system whose
kernel checks every certificate at admission only ever needs the
particular kind. So gate modification is not a trust problem at all —
provided the thing that changes is the policy and not the logic. The
apparent systems trick (keep the checker in the loop) is the operational
shadow of a provability-logic theorem about which trust statements are
derivable.
