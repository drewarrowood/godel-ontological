# Countermodel A — print hypotheses and WRP stress test

Desk note for the finite S5 non-universal countermodel to *global* T3 under
**rigid** Positive, and the checked outcome when the same frame shape is
re-read under Benzmüller–Scott-style **world-relative** Positive (WRP).

Date: 2026-09-24 (America/New_York). Toolchain: Lean 4.34.0. Package:
`/workspace/godel-ontological/`. No published-novelty claim.

---

## A. Signature (rigid Countermodel A)

| Component | Lean | Meaning |
| --- | --- | --- |
| Worlds | `W2 := Bool` | two worlds: `false`, `true` |
| Individuals | `Ind1 := Unit` | single individual `()` |
| Accessibility | `R_id := idRel W2` | `R w v ↔ w = v` (two isolated reflexive points) |
| Frame class | `S5Frame R_id` | refl + euclidean (hence sym + trans); **not** `Universal` |
| Positive | `PosA := PositiveAt false` | `PosA φ ↔ φ false ()` — **rigid** `Property → Prop` |

Related files: `GodelOntological/Countermodel.lean`, `Frames.lean`, `WeakScott.lean`,
`Modal.lean`, `Scott.lean`.

---

## B. What is rigid vs world-relative vs global

### Rigid (Countermodel A as proved)

- **`Positive : Property W Ind → Prop`** does **not** depend on an evaluation
  world. Whether φ is positive is a single meta-fact.
- Scott’s **A4** (`P(φ) → □P(φ)`) is absorbed by rigidity (see `Scott.lean` /
  `NOTES.md`).
- Axioms `A1R`–`A3R`, `A5R` are **global Prop hypotheses** on that one
  `Positive` — not indexed by worlds.
- Modal operators in the weak-frame development are **`R`-relative**
  (`necessaryR` / `possibleR`). “Global T3” means `∀ w, ∃ x, GodLike PosA w x`.

### What “global validity” means in Benzmüller–Scott HOML (literature)

- Positivity is **world-relative / intensional**: `P :: (e⇒σ)⇒σ` with
  `σ = i⇒bool`.
- Validity `⌊φ⌋ ≡ ∀ w. φ w` — axioms are required **at every world**.
- **A4** rigidifies positivity **along `R`** inside a cluster:
  `P(φ) → □P(φ)` relative to accessibility.
- Under that packaging, equivalence-S5 + symmetry yields global T3; they do
  **not** exhibit Countermodel A (Monatshefte 2025 DOI
  10.1007/s00605-025-02078-x; AFP `Notes_On_Goedels_Ontological_Argument`).

### Desk claim is encoding-relative

Countermodel A uses **rigid Positive + named cut of Universal**. The HOML
embedding’s world-relative `P` plus per-world validity of A3 is a different
hypothesis package; see §E–F.

---

## C. Exact statement of Countermodel A (conjunction proved)

Lean name: `Countermodel.countermodel_A_global_T3_fails`.

```
S5Frame R_id
∧ A1R PosA ∧ A2R PosA ∧ A3R PosA ∧ A5R R_id PosA
∧ (∃ w, ∃ x, GodLike PosA w x)
∧ ¬ (∀ w, ∃ x, GodLike PosA w x)
```

Supporting facts in the same file:

| Theorem | Content |
| --- | --- |
| `GodLike_PosA` | `GodLike PosA w x ↔ w = false` |
| `PosA_no_God_at_true` | no God at `true` |
| `countermodel_A_box_fails_at_true` | `¬ necessaryR R_id (∃ GodLike) true` |
| `countermodel_A_local_T3_at_false` | local □∃G at the God-world `false` |
| `R_id_not_universal` | `¬ Universal R_id` |

`#print axioms countermodel_A_global_T3_fails`: **no axioms** (definitional /
constructive on this finite model).

**Informal restatement:** On a two-point identity S5 frame that is not
universal, with Unit individuals and positivity “true of `()` at `false`,”
Scott A1–A5 hold, God exists at `false`, and God fails at `true`. So
**S5Frame alone does not yield global T3** under rigid Positive.

---

## D. What Universal restores

`WeakScott.T3R_necessarily_God_of_universal`:

```
Universal R → A1R → A2R → A3R → A5R R → ∀ w, ∃ x, GodLike w x
```

Under `R = universalRel`, this recovers `Scott.T3_necessarily_God` (the
`□ = ∀w` encoding). Local reflection
(`exists_God_implies_necessaryR`) only pushes God to **`R`-successors** of a
witness world (`obstruction_reflection_only_reaches_successors`); Universal
makes every world a successor.

Local T3 (`possibleR (∃G) w → necessaryR (∃G) w`) needs only **`Symmetric R`**
(`local_T3_of_Symmetric`) — strictly weaker than `S5Frame` (see Strictness C).

---

## E. Encoding caveat vs Benzmüller–Scott HOML

Why their embedding may block this model:

1. **Rigid vs world-relative Positive.** Countermodel A’s `PosA` is one global
   classifier. HOML `P` is evaluated at worlds; A3 as `⌊P(G)⌋` demands
   positivity of Godlikeness **at every world**, not once.
2. **Single global A3 bit vs per-world A3.** Rigid A3 + T1 gives God
   *somewhere* once; WRP A3 at each world gives a local ◇∃G in each cluster.
3. **A4 along `R`.** Inside a cluster, positivity is shared; with symmetry,
   local reflection fills the cluster. Multiple S5 clusters each get God from
   their own A3 — Universal is not required for global T3.
4. **Validity.** Their theorems are about valid formulas (`∀w`). The desk’s
   rigid A1–A5 are not the same as `⌊A1⌋…⌊A5⌋` under WRP.

So Countermodel A is a fact about **this** Lean encoding (rigid Positive +
explicit Universal cut). It is not a countermodel inside their HOML packaging.

---

## F. WRP stress test — checked Lean outcome

**Module:** `GodelOntological/CountermodelA_WRP.lean`  
**Verdict: Countermodel A dies under WRP.**

### Signature (WRP)

| Component | Definition |
| --- | --- |
| `PosW W Ind` | `W → Property W Ind → Prop` |
| `GodLikeW P w x` | `∀ φ, P w φ → φ w x` |
| `A1W`–`A5W` | axioms **at a world** (A2 uses `necessaryR`-entailment; A4 rigidifies along `R`) |
| `validW Ax` | `∀ w, Ax w` (global validity) |

### Theorems (0 `sorry`)

| Name | Content |
| --- | --- |
| `global_T3W_of_Symmetric` | `Symmetric R` + valid A1–A5 (with A4) ⇒ `∀ w ∃ GodLikeW` — **no Universal** |
| `global_T3W_of_S5` | same under `S5Frame` |
| `countermodel_A_shape_dies_under_WRP` | on Bool/`idRel`, any `PosW` with valid WRP hyps has global T3 |
| `PosLocal` / `PosLocal_is_not_a_countermodel` | natural localisation `P w φ ↔ φ w ()` satisfies WRP hyps **and** God everywhere |
| `rigid_gap_A3_at_true_forces_God` | A3 at `true` on `idRel` already forces God at `true` |

### `#print axioms` (2026-09-24, America/New_York)

| Theorem | Axioms |
| --- | --- |
| `countermodel_A_global_T3_fails` (rigid) | *none* |
| `PosLocal_is_not_a_countermodel` | *none* |
| `global_T3W_of_Symmetric` / `_of_S5` / `countermodel_A_shape_dies_under_WRP` / `PosLocal_global_T3_by_obstruction` / `rigid_gap_A3_at_true_forces_God` | `propext`, `Classical.choice`, `Quot.sound` (from `Classical.byContradiction` in T1) |

No `sorry`. `lake build` succeeds.

### What survives / dies

| Claim | Rigid Positive | WRP (this module) |
| --- | --- | --- |
| S5Frame ⇏ global T3 | **survives** (Countermodel A) | **dies** — Symmetric + valid A1–A5 ⇒ global T3 |
| Bool/`idRel` + Unit as countermodel shape | works with `PosA` | natural `PosLocal` is **not** a countermodel |
| Universal load-bearing for global T3 | **yes** | **no** (per-world A3 fills every cluster) |
| Local T3 under Symmetric | survives (WeakScott) | survives (`local_T3W_of_Symmetric`) |

---

## G. Status (honest) — phrase “possibly novel” deleted (Feynman P015)

What is checkable and kept:

- Finite tables: `W = Bool`, `R = idRel`, `PosA = PositiveAt false`.
- Named theorem: `countermodel_A_global_T3_fails` (S5Frame + A1R–A5R + ∃G somewhere + ¬∀w∃G).
- `#print axioms`: none on that theorem; WRP obstruction theorems use only
  `propext`, `Classical.choice`, `Quot.sound` (Franklin independent pass).
- Documented encoding miss: Monatshefte 2025 / AFP Notes use WRP + global
  validity and get global T3 from Rsymm; they do not exhibit this rigid cut.
  Negative search supports a *packaging fact*, never proof of priority.

What is not claimed:

- Not a countermodel to local T3, nor to Benzmüller–Scott HOML “S5/KB suffices.”
- Not published novelty / not priority. Local desk only.
- Under WRP the T3-fail shape **dies** (§F); there is no WRP novelty candidate
  for “global T3 fails.”

Fair fail of even the rigid packaging claim (Feynman): equivalent rigid model
already published; isomorphic tables elsewhere; artifact Positive; or claim text
that says “T3 fails in S5” without naming rigid Positive and *global* ∀w.

---

## I. Philosopher cuts (2026-09-24, Drew asked)

### Wittgenstein (keep-sentence)

Under *rigid* Positive, Scott A1–A5 on a two-world identity S5 frame (hence S5, not Universal) do not entail global T3: GodLike can hold at one world and fail at the other.

That sentence fails if Positive is world-relative with their global axioms, or if “S5” is silently read as Universal. Not incompleteness, limits of reason, or mind vs machine — named-hypothesis countermodel only.

### Heidegger (subject vs frame dial)

World-relative Positive changes what the axiom package is about, not only the frame engineering. Rigidity says the measure (perfection as such) is not world-indexed. WRP makes positivity a world-local inventory. Softening Positive is ontological change (absolute positiveness → contingent local lists), not a technical patch that “enlarges frames.” Frame engineering = vary `R` while Positive stays the same predicate.

### How this sits with §F

The WRP stress test matches Wittgenstein’s fail-condition and Heidegger’s distinction: under valid world-local A1–A5, Countermodel A’s shape dies (`countermodel_A_shape_dies_under_WRP`). The rigid packaging fact remains about a *different* package.

### Russell (three claims; Principia-style conjuncts)

Reject the slogan “Scott needs only KB/S5”; keep the theorem. Split:

| Label | Claim | Countermodel A? |
| --- | --- | --- |
| A | local T3 under Symmetric / S5-ish | **No** — holds at `false`; `local_T3_of_Symmetric` already |
| B | global T3 from S5Frame + rigid A1–A5 alone | **Yes** — Universal load-bearing in this packaging |
| C | Benzmüller–Scott HOML (WRP + ⌊Axioms⌋) | **No** — WRP module kills the shape; encoding mismatch |

Name before any status talk: (1) scope of Positive rigid vs WRP; (2) one global A3 vs ⌊A3⌋; (3) necessaryR vs Universal; (4) local T3 ≠ global T3; (5) frame hypothesis in the theorem type. Novelty cut he would sign: under *named* rigid Positive + global A3, S5Frame ⇏ global T3, with explicit finite model — and WRP stress test in the same paragraph.

### Feynman P015 PASS (2026-09-24)

Formal mark on the *rigid packaging* claim (desk, not priority): **PASS**.
Nothing else required. Will re-mark if README/keep-sentence drops rigid / global /
Universal cut, or if a novelty claim is reintroduced.

Optional polish done: README “Global T3 from S5Frame alone” row now names
**rigid** Positive and points at §F.

### Feynman (P015 bar)

Delete “possibly novel.” Candidate/packaging PASS needs: clean `lake build`, `#print axioms` listed (not hidden), hand-checkable Pos tables, claim sentence with costs in the open (encoding, frame, holds, fails), documented negative search. Will not mark priority. Fair fail = WRP twin in literature showing global T3 fail under equivalent encoding, isomorphic published model, artifact, or costume claim text. **Note:** after §F there is no WRP T3-fail candidate; his bar applies to the *rigid* packaging fact only.

### Franklin (independent verify)

`lake build` exit 0 (23 jobs). WRP dies via `countermodel_A_shape_dies_under_WRP`. Axiom lists as in §F; rigid control axiom-free; `PosLocal_is_not_a_countermodel` axiom-free.


---

## H. Build

```bash
source "$HOME/.elan/env"
cd /workspace/godel-ontological
lake build
```

Lean 4.34.0; 0 `sorry` in claimed theorems.
