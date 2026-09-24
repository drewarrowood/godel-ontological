# Gödel’s ontological argument (Scott emendation) in Lean 4

A **small, didactic** Lean 4 formalization of Dana Scott’s consistent reading of
Kurt Gödel’s ontological-proof notes. The goal is clarity: a thin S5 worlds
encoding, named axioms A1–A5 (with A4 absorbed — see below), and a checked proof
that **from those axioms** one obtains

> necessarily, there exists a God-like being  
> (`□ ∃ x, GodLike x`).

## What this is — and is not

| This project **does** | This project **does not** |
| --- | --- |
| Check that Scott’s axiom set entails `□∃x G(x)` in a universal-frame S5 encoding | Prove that God exists in metaphysics, theology, or the physical world |
| Use ordinary Lean 4 (no Mathlib, no Isabelle port) | Claim the unrepaired Gödel notes are consistent |
| Label axioms A1, A2, A3, A5 explicitly as assumptions | Hide modal structure behind classical non-modal fakes |

Lean verifies an implication: `A1 ∧ A2 ∧ A3 ∧ A5 ⊢ □∃x G(x)` (under the encoding).
Whether the axioms are *true* is a separate philosophical question.

## Build

```bash
source "$HOME/.elan/env"
cd /workspace/godel-ontological
lake build
```

Requires Lean **4.34.0** (see `lean-toolchain`).PATH must include `$HOME/.elan/bin`.

## Modal encoding

- `World` / `Individual` are ordinary types (parameters of the theorems).
- Accessibility is **universal**: every world sees every world (a valid S5 frame).
- `□ φ` ≜ `∀ w, φ w`,  `◇ φ` ≜ `∃ w, φ w`.
- A **property** is an intension `World → Individual → Prop`.
- **Positivity** is a *rigid* meta-predicate `Positive : Property → Prop` (not indexed by worlds).

Because positivity is rigid, Scott’s **A4** (`P(φ) → □ P(φ)`) holds automatically and
is not listed as a separate hypothesis. NOTES.md records this design choice.

## Axioms (Scott)

| Id | Statement (informal) | Lean name |
| --- | --- | --- |
| **A1** | A property is positive iff its negation is not | `A1` |
| **A2** | What a positive property necessarily entails is positive | `A2` |
| **A3** | Being God-like is positive | `A3` |
| **A4** | Positive properties are necessarily positive | *absorbed by rigid `Positive`* |
| **A5** | Necessary existence is positive | `A5` |

Scott’s A5 (positivity of necessary existence) is the famous repair that avoids the
inconsistency of Gödel’s unrepaired axiom set (see Benzmüller & Paleo; NOTES.md).

## Definitions

- **D1 `GodLike`**: has every positive property (at that world).
- **D2 `Essence`**: φ is an essence of x when x has φ and φ necessarily entails every property of x.
- **D3 `NE`**: every essence of x is necessarily exemplified.

## What is proved (no `sorry`)

| Theorem | Content |
| --- | --- |
| `T1_positive_possibly_exemplified` | Positive properties are possibly exemplified |
| `C_possibly_God` | Possibly, a God-like being exists |
| `T2_godlike_essence` | God-likeness is an essence of any God-like being |
| `exists_God_implies_necessary` | `∃x G(x)` at a world ⇒ `□∃x G(x)` |
| **`T3_necessarily_God`** | **`□ ∃x GodLike(x)`** from A1, A2, A3, A5 |
| `exists_God_at_every_world` | At every world, some God-like individual exists |

## Layout

```
GodelOntological/Modal.lean        — □, ◇, Property, entailment helpers (universal)
GodelOntological/Scott.lean        — definitions, axioms-as-Props, proofs (universal)
GodelOntological/ScottCuts.lean    — Russell / P042 dependency cuts (drop A5 or A3)
GodelOntological/Frames.lean       — Access, necessaryR/possibleR, named frame props
GodelOntological/WeakScott.lean    — R-relative Scott; local T3 under Symmetric/TB/S5; global under Universal
GodelOntological/Countermodel.lean — countermodels A/B + TB strictness C (path / swap)
GodelOntological/Collapse.lean     — modal collapse + ContingentR (rigid Positive; rediscovery)
GodelOntological/CountermodelA_WRP.lean — world-relative Positive; Countermodel A dies
GodelOntological/CollapseWRP.lean  — WRP collapse along R (rediscovery; see COLLAPSE_WRP.md)
GodelOntological/WRPFrameResidue.lean — what fails if Symmetric is dropped (WRP)
GodelOntological/Anderson.lean     — Anderson 1990 fragment; ContingentR survives
COUNTERMODEL_A.md                  — rigid vs WRP desk note
COLLAPSE_WRP.md                    — WRP collapse / ContingentR
WRP_FRAMES.md                      — frame residue table under WRP
ANDERSON.md                        — Anderson repair (not Fitting)
NOTES.md                           — design notebook + references
```


## Russell cuts / P042

Dependency ledger (checked in `GodelOntological/ScottCuts.lean`). A3 and A5 stay
hypotheses — **not** restored as ambient axioms or “proved” lemmas.

| Cut | Keep | Drop | Still holds | Dies / unavailable |
| --- | --- | --- | --- | --- |
| **1** | A1–A3 | A5 | `cut1_T1_without_A5`, `cut1_C_without_A5` (◇∃ GodLike) | T3 / `exists_God_implies_necessary` (need A5 in the type) |
| **2** | A1–A2+A5 | A3 | `cut2_T1_without_A3`; `cut2_reflection_without_A3` *if* a local God-like is assumed | `C_possibly_God`, T3 (no possibly-/necessarily-God without A3) |

**What stood without A5:** possibility of a God-like being (C) from A1–A3.
**What stood without A3:** T1 for arbitrary positive φ, and reflection from a
*given* local God-like + A5.
**Foundation not restored:** neither cut yields `□∃x GodLike` from a strictly
smaller axiom set than Scott’s A1∧A2∧A3∧A5.


## Weak-frame conjecture / residual cut

**Status (2026-09-24 ET):** local T3 settled under **`Symmetric R`** (Brouwerian),
strictly weaker than `S5Frame`; countermodels A/B stand; frame hyps stay **in the type**.

The universal encoding (`□ ≜ ∀w`) is stronger than “S5”. Named accessibility
conditions live in `Frames.lean`; R-relative Scott in `WeakScott.lean`.

| Claim | Frame hyp in type | Result |
| --- | --- | --- |
| Local reflection (God at `w` ⇒ □_R ∃G at `w`) | none | proved (A1+A5) |
| Local T3 (`◇_R ∃G w → □_R ∃G w`) | **`Symmetric R`** / Brouwerian / TB | **proved** (`local_T3_of_Symmetric`) |
| Local T3 under S5Frame | `S5Frame R` | corollary of Symmetric |
| Global T3 (`∀w ∃x GodLike`) | **`Universal R`** | proved (recovers `Scott.T3`) |
| Global T3 from S5Frame alone (**rigid** Positive) | — | **false** — Countermodel A; see `COUNTERMODEL_A.md` §F (dies under WRP) |
| Local T3 from refl+trans (S4) alone | — | **false** — Countermodel B |
| Symmetric/TB strictly weaker than S5Frame | — | **yes** — Strictness C (`R_path`) |

**Countermodel A (rigid Positive):** `W = Bool`, `R =` identity (S5 but not universal), Positive = “true at `false`”; A1–A5 hold; God only in one cluster. Under world-relative Positive the shape dies — `COUNTERMODEL_A.md`.
**Countermodel B:** S4 chain; A1–A5 hold; at the source `◇∃G` but not `□∃G`.
**Strictness C:** 3-world undirected path is TB/Brouwerian but not euclidean/S5Frame.

Do **not** read this as “proved necessity in S5” without the frame hypotheses.
Residual cut closed: Symmetric alone suffices for local T3; S4 does not. Details in `NOTES.md`.


## Modal collapse / free will as contingency

**Status (2026-09-24 ET):** rediscovery in this encoding of a known Scott-side effect
(Sobel; Benzmüller et al.) — **not** a priority claim. Details in `NOTES.md`.

| Claim | Assumptions in type | Result |
| --- | --- | --- |
| `ModalCollapse` (`φ → □φ`) | A1–A5 (universal Scott) | **proved** (`ModalCollapse_of_Scott`) |
| `ModalCollapseR` everywhere | **`Universal R`** + A1–A5 | **proved** |
| Collapse at a God-world | A1+A5 (any R) | **proved** (`ModalCollapseAt_of_God`) |
| `ContingentR` / `ContingentAct` impossible under Universal + A1–A5 | same | **proved** |
| ContingentR survives under S5Frame alone (**rigid** Positive) | — | **yes** — Countermodel D (non-God cluster) |
| Collapse at every world along `R` (**WRP**) | **Symmetric** + valid A1W–A5W | **proved** (`CollapseWRP.ModalCollapseR_of_Symmetric`); rediscovery |
| ContingentR impossible everywhere (**WRP**) | same | **proved** (`ContingentR_impossible_of_Symmetric`) |
| Sobel `ModalCollapse` from Symmetric alone (**WRP**) | — | **false** — `wrp_idRel_R_collapse_not_sobel` |

**Free-will reading:** contingency = true here, false at some accessible world.
Under Universal Scott, collapse kills all ContingentR/ContingentAct. Under
**rigid** Positive, ContingentR can survive off the God-cluster
(`countermodel_D_ContingentR_survives`). Under **WRP**, Symmetric + valid
A1W–A5W already kills ContingentR at every world; Sobel collapse across
inaccessible worlds still needs `Universal R`. Details in `COLLAPSE_WRP.md`.
ScottCuts / Countermodels A,B left intact.

## Anderson (not Fitting)

**Status (2026-09-24 ET):** repair formalization of Anderson 1990 (half of A1;
God-like iff necessarily has exactly the positive properties). `T3A_necessarily_God`
is `□∃ GodLikeA` from that fragment. On a two-world universal frame the same
fragment holds and `ContingentR` survives (`anderson_fragment_ContingentR_survives`).
Rediscovery of a known repair; desk witness in this encoding. Fitting’s
extensional block is not formalized. Details in `ANDERSON.md`.

## Historical pointers

- Gödel’s ontological-proof manuscripts (c. 1941 / early 1970s notes).
- Dana Scott’s emendation (circulated notes; positivity of necessary existence).
- Benzmüller & Paleo — mechanized HOML work showing inconsistency of the unrepaired set and consistency-oriented Scott variants (Isabelle/HOL; not required here).

See `NOTES.md` for a fuller notebook.
