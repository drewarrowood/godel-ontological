# Empty-at-home check of AFP Figure 7 in S4

This directory is a probe. It does not vendor the Archive of Formal Proofs.

The theory `Ax1Gen_EmptyAtHome.thy` imports

`Notes_On_Goedels_Ontological_Argument.GoedelVariantHOML2inS4`

from the AFP entry dated 7 January 2025 on isa-afp.org, release AFP 2025-2, which matches Isabelle2025-2.

## What the session proves

`fig7_implies_symmetric`: `∀w v. w r v ⟶ v r w`.

Ax1Gen is instantiated at

- φ = `(λ_::e. λu::i. u = w)` (“world is w”)
- Φ = `(λψ. λu. (u ≠ w) ∧ (∀x. ¬ ψ x u))` (empty at home)

Then Ax2b, `φ ⊃N ~φ`, and Ax4 contradict Ax2a. The sketch matches the Lean lemma `fig7_implies_symmetric`.

`Th3_via_empty_at_home`: the same goal as Th3 in `GoedelVariantHOML2inS4`, the goal that file leaves as `oops` (“Open problem”). The proof uses AFP Th2 and the symmetry just derived. It assumes no extra `Rsymm` axiom.

`R_is_identity` and `MC` are Lean theorems in `GodelOntological/Audit.lean`, from the symmetry those axioms derive. They are not lemmas of this session. `Th3_via_empty_at_home` uses `fig7_implies_symmetric`, not that Lean path. `#print axioms` is a Lean report and does not apply here.

## Recorded run

Isabelle2025-2. The AFP 2025-2 session `Notes_On_Goedels_Ontological_Argument` built cleanly. Session `Ax1Gen_EmptyAtHome_Check` then finished (exit 0): `Finished Ax1Gen_EmptyAtHome_Check`.

SHA256 of the Isabelle2025-2 Linux tarball, from the Cambridge mirror `https://www.cl.cam.ac.uk/research/hvg/Isabelle/dist/Isabelle2025-2_linux.tar.gz`:

`a20a507bc7c1270d8be96a9f3fbec06345387789d2dc2c4d3df6260d47bfb33c`

On that run the TUM dist URL returned an empty file.

Register the AFP component, then build this session from this directory:

```
isabelle build -v -d . Ax1Gen_EmptyAtHome_Check
```

## Already in the AFP entry

These are not results of the probe. In `GoedelVariantHOML2`, lemma MC uses `Rsymm` from `HOMLinHOL`, not from `HOMLinHOLonlyS4`. In the unrepaired Figure 6 theory, `EmptyEssL` and `Inconsistency` are already formalized. Figure 7 essence includes Scott’s conjunct `φ x`. The 1970 hand manuscript is not this theory.
