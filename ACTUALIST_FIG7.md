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

Literal Ax1Gen with Ax2a, Ax2b, and Ax4 forces reflexivity (`Audit.refl_of_gen`)
and the B schema (`Audit.B_schema`). Adding Ax3 forces `R w v ↔ v = w`
(`Audit.R_is_identity`) and modal collapse (`Audit.MC`), with no symmetry
hypothesis. The AFP lemma `MC` in `GoedelVariantHOML2` is the same schema,
proved there from Ax2a, Ax2b, Th5, the definition of `G`, and `Rsymm`. What is
new is the collapse without `Rsymm`. The only S4 models of the literal axioms
are discrete, and Th3 holds there trivially.

| Theorem | Content | Class |
| --- | --- | --- |
| `lemma_L` | `⌊P G⌋` from Ax1Gen | rediscovery |
| `ax2b'` | negative positivity spreads forward | rediscovery |
| `th1_fig7` | `⌊G x ⊃ G Ess. x⌋` | rediscovery |
| `th2_fig7` | `⌊G x ⊃ □∃^E G⌋` | rediscovery |
| `th3_of_symmetric` | Th3 from Th2 + `Symmetric` (AFP’s three `have`s) | rediscovery |
| `fig7_implies_symmetric` | Ax1Gen + Ax2a + Ax2b + Ax4 ⇒ `Symmetric R` | the B schema for “the world is `w`” |
| **`th3_fig7`** | **Th3 from Ax1Gen, Ax2a, Ax2b, Ax3, Ax4** | **holds because `R` is the identity** |
| `Audit.pos_of_home` | Ax1Gen alone: a property true of all existents at `w` is positive at `w` | audit |
| `Audit.refl_of_gen` | Ax1Gen + Ax2a ⇒ `Reflexive R` | audit |
| `Audit.B_schema` | `q → □◇q` for every world-proposition | audit |
| **`Audit.R_is_identity`** | **literal Fig. 7 ⇒ `R` is the identity. No symmetry hypothesis** | **headline** |
| **`Audit.MC`** | **collapse `q → □q`. No symmetry hypothesis** | **headline** |
| `th4_fig7` | `⌊◇∃^E G⌋` | rediscovery |
| `th5_fig7` | `⌊□∃^E G⌋` | rediscovery |
| `fig7_unsat_on_S4_chain` | those axioms are unsatisfiable on the two-world S4 chain | not a countermodel |
| `unit_ax1` … `unit_fig7_th3` | one world, one individual, principal `P φ := φ () ()`, `idRel` | desk consistency check (Nitpick card = 1) |

Fig. 8 (relevant because §4.5 repeats the open, and `⊃_N` adds `φ ≠ ⊥`):

| Theorem | Content |
| --- | --- |
| `th1_fig8`, `th2_fig8`, `th3_fig8_of_symmetric` | same chain, Fig. 8 essence and inclusion |
| `fig8_implies_symmetric` | same symmetry argument; the witness `x0 : Ind` shows `neBot` |
| **`th3_fig8`** | **Th3 from the Fig. 8 package. Not a claim that Fig. 8 forces the identity** |
| `fig8_unsat_on_S4_chain` | unsatisfiable on the S4 chain once an individual is given |

Fig. 8 **Th4 is `Audit.th4_fig8`:** possible existence from literal Ax1Gen and
Ax2a, via `pos_of_home` and reflexivity. It does not use Fig. 8’s side
condition on inclusion. In `GoedelVariantHOML3.thy` the Th4 script is `oops`,
with a comment that sledgehammer found a proof from Ax2a, L, and Ax1Gen, and
Th4 is then re-introduced by `axiomatization`. A Fig. 8 Th5 is not claimed.
Fig. 8 was not varied in the comparison of the three readings of Ax1Gen.

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

**Literal Fig. 7 forces a discrete frame.** `Audit.R_is_identity` and
`Audit.MC` do not assume symmetry. Th3 holds in S4 only because every model
is a cluster of isolated reflexive worlds, so the diamond and the box are the
same quantifier. There is no non-discrete S4 model. The one-world principal
interpretation shows the axioms are satisfiable, and it is the shape Nitpick
reported at cardinality one.

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

### Two reconstructions

Neither replacement is dictated by the footnote. Both are reconstructions.
What both remove is `Φ` being read at two different worlds. The Lean name
`Rigid` means world-invariant `Φ`, not Ax2b. An earlier note called R1 the
closer repair. That ranking is dropped.

Gödel’s 1970 footnote extends axiom 1 to any number of summands: the
conjunction of a collection of **positive** properties is positive. In the AFP
abbreviation the identity “`φ` is that conjunction” sits under a box
(`ConjOfPropsFrom`), while “the conjuncts are positive” (`PosProps`) is read
only at the source. `Audit.pos_of_home` is the consequence: positivity at `w`
tracks the existents at `w`, against Gödel’s gloss that positive is
independent of the accidental structure of the world. R1 judges both halves
at the same accessible worlds:

`⌊□(PosProps Φ ∧ ∀^E z. φ z ↔ (∀ψ. Φ ψ ⊃ ψ z)) ⊃ P φ⌋`

(`Ax1GenInBox`). In K, `□A ∧ □B` is `□(A ∧ B)` and `ConjOfPropsFrom` is already
a box, so this is equivalent to

`⌊(□ PosProps Φ ∧ ConjOfPropsFrom φ Φ) ⊃ P φ⌋`

(`Ax1GenBox`). `ax1GenBox_iff_inBox` is axiom-free. The two forms do not
differ. One countermodel covers both. R2 freezes `Φ`: it must be
world-invariant, and `PosProps` and `ConjOfPropsFrom` stay literal. R2 moves
no box.

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
`chain_not_literal_Ax1Gen`: this `P` is not a model of literal Ax1Gen.
`Audit.literal_to_R1`: literal implies R1 on reflexive frames.
`Audit.literal_to_R2`: literal implies R2 on every frame.
`Audit.readings_coincide_on_unit`: on a one-world identity frame the three
readings coincide. The converses are not proved in general. The chain
separates them: both reconstructions have a model, and the literal axiom has
none (`Audit.literal_unsat_on_R_chain`). The domain has one element and
`chainEx` is always true, so the actualist machinery is not exercised.
Non-symmetry is this chain (`R_chain_not_symmetric` inside
`r1_s4_countermodel` and `r2_s4_countermodel`), not the failure of one
derivation to instantiate.

### `#print axioms`

| Theorem | Axioms |
| --- | --- |
| `ax1GenBox_iff_inBox`, `lemma_L_box`, `lemma_L_inBox`, `lemma_L_rigid`, `pos_agree` | none |
| `chain_ax1`, `chain_ax2b`, `chain_ax3`, `chain_ax4`, `chain_ax1GenBox`, `chain_ax1GenInBox`, `chain_ax1GenRigid` | none |
| `chain_th3_fails_at_source`, `chain_not_Th3`, `chain_god_sink`, `chain_not_god_source` | none |
| `chain_ax2a` | `propext`, `Classical.choice`, `Quot.sound` (`Classical.em`) |
| `chain_not_literal_Ax1Gen` | `propext`, `Classical.choice`, `Quot.sound` (from `fig7_implies_symmetric`) |
| `r1_s4_countermodel`, `r2_s4_countermodel` | `propext`, `Classical.choice`, `Quot.sound` (Ax2a, and `propext` on the chain’s transitivity / non-symmetry) |
| `Audit.pos_of_home`, `refl_of_gen`, `B_schema`, `R_is_identity`, `MC`, `th4_fig8` | `propext`, `Classical.choice`, `Quot.sound` |
| `Audit.literal_to_R1`, `literal_to_R2`, `R1_to_literal_of_identity`, `literal_iff_R1_of_identity`, `R2_to_literal_of_one_world`, `readings_coincide_on_unit` | none |
| `Audit.literal_unsat_on_R_chain` | `propext`, `Classical.choice`, `Quot.sound` |
| `Audit.chain_not_necessary_existence` | none |

No `sorry`. No `native_decide`. No custom axioms.

### Classification

For the **literal** AFP axiom, `R` is the identity and the chain is
unsatisfiable. Th3 holds only on discrete frames.

For **readings R1 and R2**, Th3 is not a theorem of S4. The finite chain is a
countermodel. That is a negative answer for those two reconstructions. It is
not a rediscovery of an AFP or Monatshefte countermodel, and it is not a
countermodel of literal Fig. 7. Not a priority claim. The probe
`isabelle/Ax1Gen_EmptyAtHome.thy` (session `Ax1Gen_EmptyAtHome_Check`,
Isabelle2025-2, AFP 2025-2) imports `GoedelVariantHOML2inS4` and proves
`fig7_implies_symmetric` and `Th3_via_empty_at_home` from the empty-at-home
instantiation, with no extra `Rsymm` axiom. The session finished. It does not
prove that `R` is the identity. That remains `Audit.lean`. It is not a
`#print axioms` report.
