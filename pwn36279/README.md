# Checks against Benzmüller, "Proofs Without Nominals" (arXiv:2609.36279)

Run on 2 Oct 2026 (ET) on Isabelle2025-2 and Lean 4.33.1 (elan), against the arXiv
ancillary files of 2609.36279 v2 (anc/OpenQuestions). His files are not vendored here;
the ROOT below imports his sessions by name.

## Isabelle2025-2

    isabelle build -d <anc>/OpenQuestions/alternatives -d pwn36279/isabelle <session>

| Session | Imports (his) | What it checks | Outcome |
|---|---|---|---|
| PwnCheckTwo | Ax1GenAlternativesTwo (E) | our empty-at-home instance is not an Ax1GenTwo instance; symmetry / Th3 under Ax1GenTwo only via his nominal OneWorld | builds |
| PwnCheckRigid | Ax1GenAlternativesB (B) | `L_R_derived`: Ax1GenR ⊢ P G (his "L: derivability open"); `Ax1GenTwoR`; `L_TwoR` | builds |
| PwnCheckRigidNitpick (in PwnCheckRigid) | B | genuine countermodels: G_ex, Th3-S4 under Ax1GenR; G_ex, MC (K), Th3 (S4) under Ax1GenTwoR; `Ax1Gen_of_TwoR` (Ax1GenTwoR does not imply Ax1Gen) | builds (expect = genuine) |
| PwnCheckReqII | Th4FromConjunction (I) | requirement (ii) for Ax1GenTwoR: Th4, P(λx.⊤) refuted from Ax1GenTwoR + Ax2a | builds |
| PwnCheckReqIIR | I | Th4 refuted from Ax1GenR + Ax2a | builds |
| PwnCheckReqIIbB | I | Th4 refuted from Ax1GenTwoR + Ax2a + Ax2b | builds |
| PwnCheckReqIIbA | I | Th4 from Ax1GenR + Ax2a + Ax2b: Nitpick "unknown" | FAILS by design (likely a theorem; not proved) |
| PwnSanity | I | a valid formula under `expect = genuine` | FAILS by design (shows `expect` is enforced) |

Our original session `Ax1Gen_EmptyAtHome_Check` (isabelle/) was re-run the same evening
against the AFP checkout of 2026-09-24 and still finishes; see reports/.

A countermodel certified `expect = genuine` refutes its statement whatever the card size; the small cards (i ≤ 2, e ≤ 2) limit only the searches that returned `none`/`unknown`.

## Lean 4.33.1

`lean/apply.sh <anc>/OpenQuestions/lean` splices our additions into copies of his modules.
`#print axioms L_R_derived` = Ax2a, Ax2b, P, R, e, existsAt, i, propext, Classical.choice,
Quot.sound (no sorry). His `#hybrid_audit` output: reports/audit-*.txt. Our
`fig7_implies_symmetric_EAH` is flagged `[NOMINAL RIGID]` on both witnesses (hybrid).
`L_R_derived` is unflagged, but its witness `fun ψ => P ψ w` has type (e → σ) → Prop, outside
the detector's stated scope; its hybrid-free status is not settled.
