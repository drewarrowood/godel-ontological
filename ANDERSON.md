# Anderson’s emendation (thin check)

Desk formalization of **Anderson 1990**, not Fitting. Not a priority claim.

Date: 2026-09-24 (America/New_York). Toolchain: Lean 4.34.0.
Module: `GodelOntological/Anderson.lean`.

---

## Literature cut

Anderson, “Some Emendations of Gödel’s Ontological Proof”, *Faith and
Philosophy* 7(3), 1990. Kanckos & Woltzenlogel Paleo, *Studia Logica* 105(3),
2017, DOI 10.1007/s11225-016-9700-1, §7, record the emendation as:

| Piece | Anderson | Scott, in this package |
| --- | --- | --- |
| A1 | only `P(¬φ) → ¬P(φ)` | biconditional `A1` |
| God-like | `∀φ (P(φ) ↔ □ φ(x))` | has every positive property |
| A2, A3 | as in Scott (`P(G)`) | `A2`, `A3` |
| A4, A5, essence, NE | not required for T3 (Hájek; confirmed §7.1) | used for Scott’s T3 |

§7.2: the extra box in Anderson’s essence turns the Scott collapse derivation
into the tautology `□A → □A`. Benzmüller & Fuenmayor (arXiv:1910.08955; BSL
49(2), 2020, DOI 10.18778/0138-0680.2020.08) show both Anderson and Fitting
avoid collapse. Fitting’s block is **extensional** positivity. **This module
does not formalize Fitting.**

Signature here: rigid `Positive : Property → Prop` and universal-frame `□`
(`Scott.lean`). **Not WRP.**

---

## Fragment proved (0 `sorry`)

| Theorem | From | Result |
| --- | --- | --- |
| `T1A_positive_possibly_exemplified` | half-A1 + A2 | positive ⇒ possibly exemplified |
| `CA_possibly_God` | half-A1 + A2 + A3 | possibly God-like |
| `box_GodLikeA_of_God` | A3 + D1 | a God-like individual is God-like at every world |
| `exists_God_implies_necessaryA` | A3 + D1 | local God ⇒ `□∃ GodLikeA` |
| `T3A_necessarily_God` | half-A1 + A2 + A3 | **`□ ∃ GodLikeA`** |

A4, A5, and essence are not hypotheses of `T3A_necessarily_God`.

---

## Collapse does not follow

`anderson_fragment_ContingentR_survives` on `Bool`, `R = universalRel`,
`P_all φ ↔ ∀ w, φ w ()`:

- half-A1, A2, and A3 hold;
- `□ ∃ GodLikeA` holds (both worlds);
- `(· = false)` is `ContingentR` at `false`;
- `ModalCollapseAt` and Sobel `ModalCollapse` fail;
- Scott’s full `A1` fails (`P_all_not_Scott_A1`): a world-dependent property and
  its negation are both non-positive.

---

## `#print axioms` (2026-09-24)

| Theorems | Axioms |
| --- | --- |
| `T1A_positive_possibly_exemplified`, `CA_possibly_God`, `T3A_necessarily_God`, `anderson_fragment_ContingentR_survives` | `propext`, `Classical.choice`, `Quot.sound` |
| `box_GodLikeA_of_God`, `exists_God_implies_necessaryA`, `P_all_A1A` | none |
| `P_all_not_Scott_A1` | `propext` |

---

## Status

**Rediscovery** of Anderson’s known repair (collapse avoided; T3 kept from the
weaker package). The Bool table is **desk packaging** in this thin universal-frame
encoding. Not a priority claim. Not Fitting. Does not refute the HOML developments.
