# Actualist Fig. 7 — Th3 in S4

Desk note for `GodelOntological/Actualist.lean`. Not a priority claim.

Date: 2026-09-24 (America/New_York). Toolchain: Lean 4.34.0. No Mathlib.
No `sorry`. No `native_decide`. No Lean `axiom` declarations (hypotheses are `Prop`s).

---

## Literature cut (before the Lean claim)

Christoph Benzmüller and Dana Scott, “Notes on Gödel’s and Scott’s variants of
the ontological argument”, *Monatshefte für Mathematik*,
DOI 10.1007/s00605-025-02078-x. Dataset: AFP
`Notes_On_Goedels_Ontological_Argument` (7 January 2025).

Theories read directly:

- `HOMLinHOL.thy` / `HOMLinHOLonlyS4.thy` — shallow HOML. S5 has `Rrefl`,
  `Rsymm`, `Rtrans`. S4 has only `Rrefl` and `Rtrans`.
- `GoedelVariantHOML2.thy` — **Figure 7**. Th3 is proved from Th2 and `Rsymm`.
- `GoedelVariantHOML2inS4.thy` — the same axioms in S4. Th3 is
  `oops ―‹Open problem›`.
- `GoedelVariantHOML3.thy` / `GoedelVariantHOML3inS4.thy` — **Figure 8**.
  Th3 in S4 is again `oops`.

The paper (§4.4): no S4 proof and no S4 countermodel for Fig. 7. §4.5 says the
same for Fig. 8. §5.3 (Scott’s A3 replaced by Ax1Gen) is a different question.

Also checked, and not a settlement of this question:

- Sobel 1987; *Logic and Theism* 2004 (collapse).
- Benzmüller & Fuenmayor, arXiv:1910.08955; BSL 49(2) 2020 (Scott collapse;
  Anderson and Fitting avoid it).
- Kanckos & Woltzenlogel Paleo, *Studia Logica* 105 (2017): Scott’s argument
  in KB.
- Anderson 1990; Fitting’s extensional positivity.
- Benzmüller, arXiv:2608.07578 (2026): necessary existence in **K** for a
  simplified ultrafilter package (U1, A2, A3, `df.G`). Not Fig. 7’s axiom list.

No published proof or countermodel of Fig. 7’s Th3 in S4 was found.

---

## Encoding

**World-relative `P`**, not rigid Positive. **Actualist** individual
quantifiers via an existence predicate `ex : Ind → W → Prop` (AFP `existsAt`).
The outer type `Ind` is fixed; who exists can vary by world. That is how the
AFP file represents varying domains, not a further departure.

Property order is `Ind → W → Prop` (`τ = e ⇒ σ`, `σ = i ⇒ bool`). Older modules
in this repo use `W → Ind → Prop`. This file does not.

---

## Axiom list encoded (Fig. 7, quoted from `GoedelVariantHOML2.thy`)

```
consts PositiveProperty::"(e⇒σ)⇒σ" ("P")
Ax1:    ⌊P φ ∧ P ψ ⊃ P (φ . ψ)⌋
Ax2a:   ⌊P φ ∨^e P (~φ)⌋
G x ≡ ∀φ. P φ ⊃ φ x
φ ⊃_N ψ ≡ □(∀^E y. φ y ⊃ ψ y)
φ Ess. x ≡ φ x ∧ (∀ψ. ψ x ⊃ (φ ⊃_N ψ))
Ax2b:   ⌊P φ ⊃ □ P φ⌋
E x ≡ ∀φ. φ Ess. x ⊃ □(∃^E x. φ x)     -- inner binder shadows x
Ax3:    ⌊P E⌋
Ax4:    ⌊P φ ∧ (φ ⊃_N ψ) ⊃ P ψ⌋
PosProps Φ ≡ ∀φ. Φ φ ⊃ P φ
ConjOfPropsFrom φ Φ ≡ □(∀^E z. φ z ↔ (∀ψ. Φ ψ ⊃ ψ z))
Ax1Gen: ⌊(PosProps Φ ∧ ConjOfPropsFrom φ Φ) ⊃ P φ⌋
L:      ⌊P G⌋                             -- lemma, not an axiom
Th3:    ⌊◇(∃^E x. G x) ⊃ □(∃^E y. G y)⌋
```

Lean names: `Ax1`, `Ax2a`, `Ax2b`, `Ax3`, `Ax4`, `Ax1Gen`, `god`, `necImpl`,
`essence`, `necExist`, `posProps`, `conjOfPropsFrom`, `lemma_L`, `Th3`.

`Ax1` is encoded and holds in the one-world model. Th3 does not use it.
The AFP proof of Th3 does not use it either.

---

## Departures

| AFP | This file |
| --- | --- |
| Isabelle/HOL `bool` | Lean `Prop`, classical where noted below |
| `⌊ψ⌋ ≡ ∀w. ψ w` | `valid` |
| `existsAt : e ⇒ σ` | `ex : Ind → W → Prop` |
| Property quantifiers are HOL `∀` over all functions `e ⇒ σ` | Lean `∀` over all functions `Ind → W → Prop` (full comprehension, as in their impredicative Ax1Gen) |
| Fig. 8 `φ ≠ (λx. ⊥)` is HOL extensional equality | `neBot`: `¬ ∀ x w, φ x w ↔ False`. The symmetry proof uses a pointwise witness, which is extensional inequality |
| Deep HOML surface syntax, Leibniz equality, Nitpick | Not present. No custom axioms |

Not departures: world-relative `P`; actualist `∀^E` / `∃^E`; possibilist quantifiers over properties; Fig. 7 essence **with** `φ x`; `P(G)` derived.

**World-shift used on purpose.** In the AFP abbreviation, `PosProps Φ` is
evaluated at the world where Ax1Gen is applied, while `ConjOfPropsFrom` puts
`Φ` under a box, so `Φ` is read at accessible worlds. `fig7_implies_symmetric`
uses that shift: `Φ` is empty at the source (so `PosProps` is vacuous) and
non-empty at other worlds (so the biconditional can define a property that is
true only at the source). That is the literal abbreviation, not a repaired
Ax1Gen. A variant that required `PosProps` at every accessible world is not
what was proved.

---

## What was proved

No `Reflexive` or `Transitive` hypothesis anywhere in the Th3 theorems.
S4 is the special case in which those two hold and symmetry is not assumed.
Symmetry is derived from the non-logical axioms, so the AFP step that cites
`Rsymm` is available inside S4, and in K.

| Theorem | Content | Class |
| --- | --- | --- |
| `lemma_L` | `⌊P G⌋` from Ax1Gen | rediscovery |
| `ax2b'` | negative positivity spreads forward | rediscovery |
| `th1_fig7` | `⌊G x ⊃ G Ess. x⌋` | rediscovery |
| `th2_fig7` | `⌊G x ⊃ □∃^E G⌋` | rediscovery |
| `th3_of_symmetric` | Th3 from Th2 + `Symmetric` (AFP’s three `have`s) | rediscovery |
| `fig7_implies_symmetric` | Ax1Gen + Ax2a + Ax2b + Ax4 ⇒ `Symmetric R` | answers the open |
| **`th3_fig7`** | **Th3 from Ax1Gen, Ax2a, Ax2b, Ax3, Ax4. No frame hypothesis** | **answers the open** |
| `th4_fig7` | `⌊◇∃^E G⌋` | rediscovery |
| `th5_fig7` | `⌊□∃^E G⌋` | rediscovery |
| `fig7_unsat_on_S4_chain` | those axioms are unsatisfiable on the two-world S4 chain | not a countermodel |
| `unit_ax1` … `unit_fig7_th3` | one world, one individual, principal `P φ := φ () ()`, `idRel` | desk consistency check (Nitpick card = 1) |

Fig. 8 (relevant because §4.5 repeats the open, and `⊃_N` adds `φ ≠ ⊥`):

| Theorem | Content |
| --- | --- |
| `th1_fig8`, `th2_fig8`, `th3_fig8_of_symmetric` | same chain, Fig. 8 essence and inclusion |
| `fig8_implies_symmetric` | same symmetry argument; the witness `x0 : Ind` shows `neBot` |
| **`th3_fig8`** | **Th3 from the Fig. 8 package, no frame hypothesis** |
| `fig8_unsat_on_S4_chain` | unsatisfiable on the S4 chain once an individual is given |

Fig. 8 **Th4 / Th5 are not claimed.** The Fig. 7 proof of Th4 uses
`⊥ ⊃_N ¬⊥`, which is vacuous for Fig. 7 inclusion. Fig. 8’s inclusion requires
`φ ≠ ⊥`, so that step does not transfer. In `GoedelVariantHOML3.thy` the Th4
script is `oops` and Th4 is then re-introduced by `axiomatization`.

### Where the old countermodel attempt breaks

On the S4 chain (`false` sees both worlds, `true` sees only `true`: reflexive,
transitive, not symmetric), `fig7_implies_symmetric` already yields `False`.
There is no `P` and no `existsAt` satisfying Ax1Gen, Ax2a, Ax2b, and Ax4.
A fortiori there is no model in which `◇∃^E G` holds at `false` and `□∃^E G`
fails there. The same obstruction is every non-symmetric frame, not a special
feature of two worlds.

The symmetry proof does not need Ax3. Th3 needs Ax3, through Th2.

### What would be a different theorem

Requiring `PosProps` inside the box, dropping Ax2b, using rigid `P`, using
possibilist individual quantifiers, or using Fig. 6’s inconsistent essence,
would be a different package. Those were not proved or refuted here.
`GoedelVariantHOML2possInS4` (possibilist twin) also leaves Th3 open; it is
not encoded.

---

## `#print axioms`

| Theorem | Axioms |
| --- | --- |
| `lemma_L`, `ax2b'`, `th1_fig7`, `th2_fig7`, `th3_of_symmetric` | none |
| `th1_fig8`, `th2_fig8`, `th3_fig8_of_symmetric` | none |
| `R_chain_reflexive`, `unit_ax1`, `unit_ax2b`, `unit_ax4`, `unit_ax1Gen`, `unit_ax3` | none |
| `R_chain_transitive`, `R_chain_not_symmetric` | `propext` |
| `fig7_implies_symmetric`, `th3_fig7`, `th4_fig7`, `th5_fig7`, `fig7_unsat_on_S4_chain` | `propext`, `Classical.choice`, `Quot.sound` |
| `fig8_implies_symmetric`, `th3_fig8`, `fig8_unsat_on_S4_chain` | `propext`, `Classical.choice`, `Quot.sound` |
| `unit_ax2a`, `unit_fig7_th3` | `propext`, `Classical.choice`, `Quot.sound` (`Classical.em` / the symmetry derivation) |

`Classical.choice` is `Classical.byContradiction` in the symmetry argument and
in Th4, and `Classical.em` in the one-world check of Ax2a. Isabelle/HOL is
classical, so that matches the host logic. No `sorry`. No `native_decide`.

---

## Status

**Answers the stated open question** for the encoded Fig. 7 axioms, and the
same way for Fig. 8’s Th3: Th3 is provable in S4. The proof does not use
reflexivity or transitivity. It derives symmetry from Ax1Gen, Ax2a, Ax2b, and
Ax4, then repeats the AFP proof of Th3 from Th2.

There is no S4 countermodel in this encoding. Any model of those axioms has
symmetric accessibility, and Th3 holds on symmetric frames. The one-world
principal interpretation shows the axioms are satisfiable.

`th3_of_symmetric` and the symmetry-free AFP lemmas are rediscoveries.
`fig7_implies_symmetric` is the step the S4 file left open; it was not found
in the sources listed above. Not a priority claim.

---

## Hunt 6 — Ax1Gen without the source/successor split

Date: 2026-09-24 (America/New_York). Module: `GodelOntological/Actualist_Repaired.lean`.
The literal Fig. 7 development above is unchanged.

### Literature, again

The AFP S4 files (`GoedelVariantHOML2inS4`, and the possibilist and Fig. 8
twins) still state literal Ax1Gen — `PosProps` outside the box — and leave
Th3 as `oops`. Benzmüller & Fuenmayor (BSL 2020), Kirchner’s modal-collapse
work, Fitting’s extensional positivity, and the simplified-argument AFP entry
`SimplifiedOntologicalArgument` do not study these two repairs. No published
S4 countermodel for a boxed or rigid Ax1Gen was found. Hunt 5’s positive
answer is for the literal axiom only.

### Why R1 is the closer repair

Gödel’s 1970 footnote extends axiom 1 to any number of summands: the
conjunction of a collection of **positive** properties is positive. In the AFP
abbreviation the identity “`φ` is that conjunction” sits under a box
(`ConjOfPropsFrom`), while “the conjuncts are positive” (`PosProps`) is read
only at the source. The closer repair judges both at the same accessible
worlds:

`⌊□(PosProps Φ ∧ ∀^E z. φ z ↔ (∀ψ. Φ ψ ⊃ ψ z)) ⊃ P φ⌋`

(`Ax1GenInBox`). In K, `□A ∧ □B` is `□(A ∧ B)` and `ConjOfPropsFrom` is already
a box, so this is equivalent to

`⌊(□ PosProps Φ ∧ ConjOfPropsFrom φ Φ) ⊃ P φ⌋`

(`Ax1GenBox`). `ax1GenBox_iff_inBox` is axiom-free. The two forms do not
differ. One countermodel covers both. R2 is a different restriction, not a
rival spelling of R1: `Φ` must be world-invariant (`Rigid`), and `PosProps`
and `ConjOfPropsFrom` stay literal.

### Per reading

| | R1 (boxed / in-box) | R2 (rigid `Φ`) |
| --- | --- | --- |
| Lemma L | `lemma_L_box`, `lemma_L_inBox`. From the repaired Ax1Gen alone. `Φ := P` is positive at every world, so the box adds nothing | `lemma_L_rigid`. Needs Ax2a and Ax2b as well: the rigid snapshot `Φ ψ _ := P ψ w` matches `G` at successors only because positivity agrees along `R` |
| Symmetry | Not forced. The Hunt 5 `Φ` is empty at the source, so source `PosProps` holds, but at the sink it contains `⊥`, so `□ PosProps` asks for `P(⊥)` | Not forced. That same `Φ` is not rigid, so `Ax1GenRigid` does not apply to it |
| Th3 in S4 | Fails. `r1_s4_countermodel` | Fails. `r2_s4_countermodel` |

### Witness (both readings)

`R_chain` on `Bool`: `false` sees both worlds, `true` sees only `true`
(`R_chain_reflexive`, `R_chain_transitive`, `R_chain_not_symmetric`).
One individual, `chainEx` true at both worlds.
`chainP φ _ := φ () true`.

God-like at `true` only (`chain_god_sink`, `chain_not_god_source`).
At `false`, `◇∃^E G` holds and `□∃^E G` fails (`chain_th3_fails_at_source`).
Ax1, Ax2b, Ax3, Ax4, `Ax1GenBox`, `Ax1GenInBox`, and `Ax1GenRigid` hold.
`chain_not_literal_Ax1Gen`: this `P` is not a model of literal Ax1Gen, by
Hunt 5’s unsatisfiability theorem. The repairs are strictly weaker on this frame.

### `#print axioms`

| Theorem | Axioms |
| --- | --- |
| `ax1GenBox_iff_inBox`, `lemma_L_box`, `lemma_L_inBox`, `lemma_L_rigid`, `pos_agree` | none |
| `chain_ax1`, `chain_ax2b`, `chain_ax3`, `chain_ax4`, `chain_ax1GenBox`, `chain_ax1GenInBox`, `chain_ax1GenRigid` | none |
| `chain_th3_fails_at_source`, `chain_not_Th3`, `chain_god_sink`, `chain_not_god_source` | none |
| `chain_ax2a` | `propext`, `Classical.choice`, `Quot.sound` (`Classical.em`) |
| `chain_not_literal_Ax1Gen` | `propext`, `Classical.choice`, `Quot.sound` (from `fig7_implies_symmetric`) |
| `r1_s4_countermodel`, `r2_s4_countermodel` | `propext`, `Classical.choice`, `Quot.sound` (Ax2a, and `propext` on the chain’s transitivity / non-symmetry) |

No `sorry`. No `native_decide`. No custom axioms.

### Classification

For the **literal** AFP axiom, Hunt 5 stands: Th3 is proved, and this chain is
unsatisfiable.

For **readings R1 and R2**, Th3 is not a theorem of S4. The finite chain is a
countermodel. That answers the open question **negatively for those named
readings**. It is not a rediscovery of an AFP or Monatshefte countermodel, and
it is not a countermodel of literal Fig. 7. Not a priority claim.
