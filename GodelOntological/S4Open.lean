import GodelOntological.WRPFrameResidue

/-
# Monatshefte Fig. 7 / Th3 in S4 — not settled here

## Literature cut

Benzmüller & Scott, “Notes on Gödel’s and Scott’s variants of the ontological
argument”, *Monatshefte für Mathematik*, DOI 10.1007/s00605-025-02078-x;
AFP `Notes_On_Goedels_Ontological_Argument`.

The named open (§4.4, Fig. 7; again §4.5, Fig. 8) is whether **Theorem Th3**

> if a God-like being possibly exists, then one necessarily exists,

with **actualist** quantifiers, is provable from the **essence-adapted**
Gödel axioms in **S4** (reflexivity and transitivity in place of symmetry).
`P(G)` is not an axiom there: it is lemma L, from the generalized conjunction
axiom Ax1Gen. Neither a proof nor a countermodel in S4 is reported.
§5.3 is a different, inconclusive Scott-side experiment (Nitpick S4
counterexamples when A3 is postulated; not reproduced when A3 is replaced by
Ax1Gen).

## Why the Lean development does not transfer

This package has constant domains, no existence predicate, no Ax1Gen, and a
thin `Prop` encoding. `A3` / `A3W` (**P(GodLike)**) is postulated. The theorem
below is that Scott-style WRP fact on an S4 chain. It is **not** a countermodel
to Fig. 7. The Fig. 7 question stays **open**. See `S4_OPEN.md`.
-/

namespace GodelOntological
namespace S4Open

open WRPFrameResidue
open CountermodelA_WRP

/-- **Not Fig. 7.** On the S4 chain, with WRP and **postulated** `A3W`
(constant `Unit` domain), possibility of God at the source does not yield
necessity. Alias of `WRPFrameResidue.chain_S4_local_T3_fails`. -/
theorem scott_style_S4_local_T3_fails :
    possibleR Countermodel.R_chain
      (fun v => ∃ x : Unit, GodLikeW (PosPivot true) v x) false ∧
    ¬ necessaryR Countermodel.R_chain
      (fun v => ∃ x : Unit, GodLikeW (PosPivot true) v x) false :=
  chain_S4_local_T3_fails

end S4Open
end GodelOntological
