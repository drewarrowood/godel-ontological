# S4 / Theorem Th3 — Monatshefte Fig. 7 stays open

Desk note. Not a priority claim. This file does not settle the open.

Date: 2026-09-24 (America/New_York). Toolchain: Lean 4.34.0.

---

## Literature cut (the open, before any Lean claim)

Christoph Benzmüller and Dana Scott, “Notes on Gödel’s and Scott’s variants of
the ontological argument”, *Monatshefte für Mathematik*,
DOI 10.1007/s00605-025-02078-x. Dataset: AFP entry
`Notes_On_Goedels_Ontological_Argument`.

**Named open (§4.4, Fig. 7).** After essence is repaired by adding the
conjunct “the essential property actually holds of the individual” (Scott’s
addition to Gödel’s 1970 definition), can **Theorem Th3** be proved in **S4**?

- **Th3:** if a God-like being possibly exists, then a God-like being
  necessarily exists.
- Quantifiers in their statement of Th3 are **actualist** (an existence
  predicate; an individual need not exist at every world).
- The modal strength in question is reflexivity and transitivity (axiom
  schemes M, D, or 4), **instead of** symmetry (B / `Rsymm`).
- Only Th3 uses symmetry. The other steps do not.
- For the **inconsistent** manuscript variant they report a proof of Th3 from
  reflexivity alone, and a Nitpick countermodel in an appendix for that
  inconsistent context. For **Fig. 7** they report neither an S4 proof nor an
  S4 countermodel. That is the open.
- `P(God-like)` is **not** an axiom in Fig. 7. It is lemma L, obtained from
  Gödel’s generalized conjunction axiom **Ax1Gen** (arbitrary, including
  infinite, conjunctions of positive properties). Scott’s later variant
  postulates that lemma as axiom A3. The paper treats those as different.

**Same open, second packaging (§4.5, Fig. 8).** If inconsistency is avoided by
changing necessary property implication instead of essence, Th3 in S4 is again
left open.

**Nearby, not the same question (§5.3).** Nitpick found S4 counterexamples to
Scott’s T3 in some of their Scott figures. Those counterexamples were **not**
reproduced when Scott’s A3 was replaced by Ax1Gen, and no proof was found
either. The paper calls that inconclusive and asks for further study.

---

## Why it does not transfer to this Lean package

| Their Fig. 7 | This package |
| --- | --- |
| HOML; `P` on intensions (`e ⇒ σ`, `σ = i ⇒ bool`); axioms under validity | Thin `Prop` encoding. WRP (`PosW`) is only an analogue of world-relative `P` |
| Actualist `∃^E` / `∀^E` | Constant domain. No existence predicate. Every `Unit` value is “there” at every world |
| Necessary implication uses actualist quantification inside the box | `necessaryR` quantifies over all individuals |
| `P(G)` derived from **Ax1Gen** | `A3` / `A3W` is an **axiom** |
| S4 question: refl+trans in place of symmetry, for that axiom set | `chain_S4_local_T3_fails` drops symmetry while **keeping postulated A3W** |

A countermodel that assumes `P(GodLike)` does not answer a question whose whole
point, in §5.3, is that the S4 counterexamples disappeared when that postulate
was replaced by Ax1Gen. The Kripke picture in their base-logic counterexample
(an individual God-like in one world and **non-existent** in another) is also
not expressible here.

Rigid Countermodel B (`Countermodel.lean`) is the same mismatch, plus rigid
Positive rather than their intensional `P`.

---

## What was checked instead

`GodelOntological/S4Open.lean`, theorem `scott_style_S4_local_T3_fails`:
alias of `WRPFrameResidue.chain_S4_local_T3_fails`.

On the two-world S4 chain (reflexive, transitive, not symmetric), with
world-relative `PosPivot true` and **A3W postulated**, God is possible at
`false` and not necessary there. Constant `Unit` domain.

`#print axioms scott_style_S4_local_T3_fails`: `propext` (same proof as the
chain theorem). No `sorry`.

That is a **desk** Scott-style S4 failure in this encoding. It is not a
reproduction of their Nitpick model and not a countermodel to Fig. 7.

---

## Status

**Still open.** Fig. 7 (and Fig. 8) Th3 in S4, with Ax1Gen and actualist
quantifiers, is not proved or refuted here. Encoding mismatch, recorded above.
Not a priority claim.
