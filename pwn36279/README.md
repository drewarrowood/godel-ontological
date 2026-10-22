# Checks against Benzmüller, "Proofs Without Nominals" (arXiv:2609.36279)

Run on 2 Oct 2026 (ET) on Isabelle2025-2 and Lean 4.33.1 (elan), against the arXiv
ancillary files of 2609.36279 v2 (anc/OpenQuestions). His files are not vendored here;
the ROOT below imports his sessions by name.

Added 15 Oct 2026: v3 of 2609.36279 (13 Oct 2026) was read but these checks were not re-run
against its ancillary files. v3's session B now proves `L_R` (L under Ax1GenR, with the snapshot
`{ψ. P ψ w}`), the same witness as `L_R_derived` here; see the paper, §1 and §6.

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
| PwnCheckReqIIbA | I | Th4 from Ax1GenR + Ax2a + Ax2b: Nitpick "unknown" | FAILS by design; superseded by PwnTh4R (kept as a record of the search) |
| PwnTh4R | I | Added 22 Oct 2026: `Th4_R`: Ax1GenR + Ax2b (hypothesis) ⊢ ⌊◇∃ᴱx. G x⌋, via `L_R` (snapshot) and the rigid sets ∅, {G}. Embedding theorem; hybrid-free only if L_R is | builds |
| PwnUF | B | Added 22 Oct 2026: `UF_base`: ⌊UFilter P⌋ (Notes' Filter/UFilter, oneFile l.206–207) from session B's axioms alone; the three Ax1GenTwoR countermodels re-found with UFilter P assumed (expect = genuine) | builds |
| PwnSanity | I | a valid formula under `expect = genuine` | FAILS by design (shows `expect` is enforced) |
| PwnCheckEvil | Ax1GenAlternativesV3Two (F, v4 ancillary) | Added 18 Oct 2026: AFP ThereIsNoEvil2's `NecNoEvil` from Ax2a and Ax4 alone (no conjunction axiom), given two individuals | builds |

Added 18 Oct 2026: `PwnCheckEvil` was written against session F of the v4 ancillary files
(`alternatives/F` in v4's ancillary files) and builds on Isabelle2025-2 against it (18 Oct 2026;
`isabelle build -d <anc-v4>/OpenQuestions/alternatives -d pwn36279/isabelle PwnCheckEvil`). With
one individual, Nitpick under Ax1GenTwo returned `none` for (i,e) = (1,1) and (2,1); that
case is not proved.

Our original session `Ax1Gen_EmptyAtHome_Check` (isabelle/) was re-run the same evening
against the AFP checkout of 2026-09-24 and still finishes; see reports/.

A countermodel certified `expect = genuine` refutes its statement whatever the card size; the small cards (i ≤ 2, e ≤ 2) limit only the searches that returned `none`/`unknown`.

Added 22 Oct 2026: `PwnTh4R` and `PwnUF` built on Isabelle2025-2 against the same `alternatives/` sessions I and B
(`isabelle build -d <anc>/OpenQuestions/alternatives -d pwn36279/isabelle PwnTh4R PwnUF`, exit 0). The
Mühlenbeck–Benzmüller (LLP 2026) definition of ultrafilter was not read; UF_base uses the Notes' definition.

## Lean 4.33.1

`lean/apply.sh <anc>/OpenQuestions/lean` splices our additions into copies of his modules.
`#print axioms L_R_derived` = Ax2a, Ax2b, P, R, e, existsAt, i, propext, Classical.choice,
Quot.sound (no sorry). His `#hybrid_audit` output: reports/audit-*.txt. Our
`fig7_implies_symmetric_EAH` is flagged `[NOMINAL RIGID]` on both witnesses (hybrid).
`L_R_derived` is unflagged, but its witness `fun ψ => P ψ w` has type (e → σ) → Prop, outside
the detector's stated scope; its hybrid-free status is not settled.
