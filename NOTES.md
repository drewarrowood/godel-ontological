# NOTES — Gödel/Scott ontological formalization

Permanent notebook for design choices, dead ends, and references.

## Intent

Start simple: a Lean 4 beginner can read `Modal.lean` + `Scott.lean` and see the
Scott chain without HOML infrastructure. Prefer a complete small fragment over an
incomplete large port of Benzmüller’s Isabelle development.

## Definitions chosen

1. **Universal-frame S5** rather than an explicit accessibility relation.
   - Pro: `□`/`◇` are literally `∀`/`∃` over worlds; S5 laws hold.
   - Con: cannot study weaker frames (K, T, B alone) without refactoring.
   - The classical Scott proof of T3 needs (at least) symmetry/B in general
     Kripke frames; universal accessibility supplies full S5, so B is free.

2. **Rigid positivity** (`Positive : Property → Prop`).
   - Makes A4 (`P(φ) → □P(φ)`) true by construction.
   - Matches the didactic aim; a world-relative `Positive : World → Property → Prop`
     would reintroduce A4 as a real hypothesis (closer to HOML embeddings).
   - Failed approach considered: world-relative positivity in v0 — deferred to keep
     the first version small.

3. **Axioms as `Prop`-valued definitions** (`A1 Positive`, …) passed as hypotheses,
   not global `axiom` commands.
   - Makes the dependence `A1∧A2∧A3∧A5 ⊢ T3` explicit at every theorem.
   - Avoids polluting the environment with unconditioned axioms.

4. **No Mathlib.**
   - Proofs use `Classical.byContradiction`, `refine`, `obtain` only.
   - Keeps `lake build` instant and dependency-free.

## Proof sketch (Scott chain)

1. **T1** from A1+A2: if φ is positive but nowhere exemplified, then φ entails
   `propFalse`, so `propFalse` is positive; but `propFalse = propNeg propTrue`, so
   A1 yields ¬Positive(`propTrue`); yet any positive φ entails `propTrue`, contradiction.
2. **C** from A3+T1: God-like is positive ⇒ possibly exemplified.
3. **T2** from A1 (+ rigidity): if G(x) and ψ(x), then ψ is positive (else ¬ψ would be
   positive and G(x) would give ¬ψ(x)); hence every God-like being has ψ at every world.
4. **Reflection** from T2+A5: G(x) ⇒ NE(x) ⇒ □∃y G(y).
5. **T3** from C + reflection under universal S5: ◇∃G and (∃G → □∃G) ⇒ □∃G.

## Failed / deferred approaches

- Full Benzmüller-style HOML with explicit `σ` (world→Prop) embedding and
  quantified accessibility: too heavy for “start simple.”
- Single-world collapse (purely classical): rejected; we want a real (thin) modal
  encoding even if the frame is the coarsest S5 frame.
- Porting Isabelle AFP `GoedelGod` proofs verbatim: not attempted; this is an
  independent Lean sketch of the same informal argument.

## Inconsistency warning (unrepaired Gödel)

Gödel’s notes, taken without Scott’s repairs, admit inconsistent readings
(notably around the interaction of positivity, essence, and necessary existence).
Benzmüller & Paleo showed mechanized inconsistency results for the unrepaired
axiom set and studied Scott/Anderson-style repairs. This package formalizes the
**Scott** side (A5: positivity of NE; A3 naming P(G); essence with the φ(x)
conjunct). We do **not** claim to re-check the inconsistency result in Lean.

## References

- Gödel, K. — ontological proof manuscripts / notes (often cited via Sobel).
- Scott, D. — notes on Gödel’s ontological argument (emendation; A5).
- Sobel, J. H. — *Logic and Theism* (discussion of Gödel/Scott).
- Benzmüller, C. & Paleo, B. W. — “Formalization, Mechanization and Automation of
  Gödel’s Proof of God’s Existence” (arXiv:1308.4526); AFP entries `GoedelGod`,
  related HOML notes.
- Fitting, M. — *Types, Tableaus, and Gödel’s God*.

## Build log (first successful check)

- Lean 4.34.0 via elan
- `lake build` → success, **0 `sorry`**
- Date: 2026-09-24 (America/New_York)

## Russell cuts / P042 (2026-09-24, America/New_York)

Implemented `GodelOntological/ScottCuts.lean` at Bertrand Russell’s request:
explicit dependency split without treating A3/A5 as secure.

- **Cut 1 (drop A5):** `cut1_T1_without_A5`, `cut1_C_without_A5` — T1/C stand
  from A1–A3; no theorem of type `A1→A2→A3→□∃ GodLike`.
- **Cut 2 (drop A3):** `cut2_T1_without_A3`, optional
  `cut2_reflection_without_A3` — T1 and (conditional) reflection stand;
  C and T3 unavailable without A3.
- Existing `T3_necessarily_God` in `Scott.lean` left intact; A3/A5 remain
  hypotheses only. `lake build` expected 0 sorry.

## Weak-frame conjecture (2026-09-24, America/New_York)

**Conjecture (weak-frame Scott).** In Scott A1–A5 with rigid positivity, the step
from ◇∃x GodLike to □∃x GodLike may depend on the **universal-frame** encoding
(`□ ≜ ∀w`). Task: name the weakest accessibility conditions under which T3 still
goes through, and/or exhibit a countermodel where axioms hold but □∃ GodLike fails.

### What was built

| File | Role |
| --- | --- |
| `GodelOntological/Frames.lean` | `Access`, `necessaryR` / `possibleR`, named props incl. Brouwerian, TBFrame, S5Frame, EquivalenceFrame; `universalRel`, `idRel` |
| `GodelOntological/WeakScott.lean` | R-relative Essence/NE/A5; local reflection; local T3 under Symmetric/TB/S5; global under Universal; obstruction |
| `GodelOntological/Countermodel.lean` | Countermodels A/B + TB strictness C (0 sorry) |

### What was proved (0 sorry)

1. **Local reflection** (`exists_God_implies_necessaryR`): God at `w` ⇒
   `necessaryR (∃G) w`. Needs A1+A5 only — **no** frame hypothesis.
2. **Local T3** (`local_T3_of_Symmetric` / `_Brouwerian` / `_TB` / `_S5`): under
   **`Symmetric R`** alone (hence also TB / S5Frame) in the theorem type,
   `possibleR (∃G) w → necessaryR (∃G) w`. S5 packaging is now a corollary.
3. **Global T3** (`T3R_necessarily_God_of_universal`): under **`Universal R`** in
   the theorem type, `∀w ∃x GodLike w x` from A1–A3+A5. Recovers the
   `Scott.lean` reading when `R = universalRel`.
4. **Obstruction lemma**: global C + local reflection only force God on
   `R`-successors of the witness world — not at arbitrary worlds.

Frame hypotheses appear **in the theorem type** (same honesty style as A1–A5).
We do **not** claim “T3 in S5” without those hypotheses.

### Countermodels found (priority deliverable)

**Countermodel A — universality load-bearing for global T3.**
- Frame: `W = Bool`, `R = idRel` (identity). This is an **S5Frame**
  (refl+eucl+sym+trans) but **not Universal** (two clusters).
- `Ind = Unit`, `Positive φ ↔ φ false ()`.
- A1–A5 hold; GodLike only at `false`.
- Local T3 holds at `false`; `□∃G` / existence fails at `true`.
- So **S5 frame conditions alone do not yield global `∀w ∃G`**. The old
  universal encoding (`□ = ∀w`) was stronger than “S5”.

**Countermodel B — euclidean/symmetry load-bearing for local T3.**
- Frame: chain `false → {false,true}`, `true → {true}` (refl+trans, **not**
  sym / **not** euclidean — an S4 frame).
- `Positive φ ↔ φ true ()`; GodLike only at sink `true`.
- A1–A5 hold; at source: `◇∃G` true, `□∃G` false.
- So **local T3 needs something beyond S4**. Residual cut later proves
  **Symmetric / Brouwerian alone** suffices (and is strictly weaker than
  S5Frame; see strictness witness C).

### What remains open (pre–residual cut)

- ~~Exact weakest frame for local T3~~ — **settled** by residual cut below.
- World-relative (non-rigid) Positive / explicit A4: see `COUNTERMODEL_A.md` / `CountermodelA_WRP.lean` (Countermodel A dies under WRP).
- No metaphysical claim: these are facts about the Lean encoding.

### Build

- `lake build` → success, **0 `sorry`** (weak-frame + countermodels).
- Date: 2026-09-24 (America/New_York).

## Residual cut — local T3 under Symmetric (2026-09-24, America/New_York)

**Order followed (Feynman):** attempted a small sym-only / refl+sym finite frame
as a prospective countermodel *before* claiming Brouwerian sufficiency. On the
3-world undirected path (TB, not euclidean), placing God only at an endpoint
**cannot** yield ◇∃G ∧ ¬□∃G under A1+A5: reflection at a God-world plus symmetry
forces God back along every edge. So no countermodel on TB; the proof goes through.

### Delivered (weaker theorem, 0 sorry)

| Theorem | Frame hyp **in the type** | Notes |
| --- | --- | --- |
| `local_T3_of_Symmetric` | `Symmetric R` | Main residual result |
| `local_T3_of_Brouwerian` | `Brouwerian R` (= Symmetric) | Alias |
| `local_T3_of_TB` | `TBFrame R` (= refl ∧ sym) | Refl unused for this direction |
| `local_exists_God_of_Symmetric` | `Symmetric R` | ◇∃G ⇒ God at `w` via back-edge |
| `local_T3_of_S5` | `S5Frame R` | Now a **corollary** via `S5Frame.symmetric` |

**Proof idea.** ◇∃G at `w` ⇒ God at some `v` with `R w v`; reflection (A1+A5)
⇒ □∃G at `v`; symmetry ⇒ `R v w` ⇒ God at `w`; reflection at `w` ⇒ □∃G at `w`.
No reflexivity, transitivity, or euclidean needed.

### Strictness / negative results (unchanged + new witness)

- **Countermodel B** still shows **S4 (refl+trans) is insufficient** for local T3.
- **Countermodel A** still shows **S5Frame is insufficient** for *global* T3
  (need `Universal R`).
- **Strictness C** (`strictness_C_TB_not_S5`): 3-world path `R_path` is
  `TBFrame` / Brouwerian but **not** transitive, **not** euclidean, **not**
  `S5Frame`. So the Symmetric/TB hypothesis is strictly weaker than S5Frame.
- **Feynman sym-only check** (`R_swap`): pure 2-cycle `w ≠ v` is Brouwerian
  and **not** reflexive (hence not TB); still covered by `local_T3_of_Symmetric`.

### Status summary

| Claim | Status |
| --- | --- |
| Local T3 from Symmetric / Brouwerian / TB | **proved** (weaker than S5Frame) |
| Local T3 from S4 (refl+trans) alone | **false** — Countermodel B |
| Local T3 from S5Frame | proved (corollary) |
| Global T3 from S5Frame alone (**rigid** Positive) | **false** — Countermodel A; WRP kills the shape (`COUNTERMODEL_A.md`) |
| Global T3 from Universal | proved |

Nothing material remains open on the residual cut itself. Deferred: non-rigid
Positive / explicit A4 — **done 2026-09-24**: see `COUNTERMODEL_A.md` and
`GodelOntological/CountermodelA_WRP.lean`. Verdict: under world-relative Positive
with global validity of A1–A5 (incl. A4), `Symmetric R` already forces global T3
(no Universal); Countermodel A dies. Status: rigid packaging fact only (P015 PASS desk; not priority);
not claimed vs Monatshefte 2025 / AFP Notes.

### Build (residual)

- `lake build` → success, **0 `sorry`**.
- Date: 2026-09-24 (America/New_York).

## Modal collapse / free will as contingency (2026-09-24, America/New_York)

**Literature (no priority).** Sobel noted that Gödel/Scott premises imply modal
collapse `φ → □φ` (Sobel 1987; *Logic and Theism* 2004). Benzmüller & Fuenmayor
(and earlier Benzmüller–Paleo HOML work) re-verified collapse for Scott’s variant
in Isabelle/HOL and studied Anderson/Fitting emendations that avoid it
(arXiv:1910.08955; BSL 2020). One philosophical reading is that collapse
eliminates contingency and thus “free will” in the sense of could-have-been-
otherwise. This package **re-checks collapse in the thin Lean encoding** —
rediscovery only.

### Definitions (`GodelOntological/Collapse.lean`)

- `ContingentR R φ w` := `φ w ∧ possibleR R (¬φ) w`
- `ContingentAct R α w x` := ContingentR on `fun v => α v x`
- `Contingent φ w` := universal-frame version (`◇ = ∃`)
- `ModalCollapseAt R w` / `ModalCollapseR R` / `ModalCollapse` (Sobel `φ → □φ`)

### What was proved (0 sorry)

1. **Local collapse at God-worlds** (`ModalCollapseAt_of_God` / `local_collapse_of_God`):
   A1+A5 + ∃ GodLike at `w` ⇒ every true `φ` is `necessaryR` at `w`.
   Sobel step: lift `φ` to `constProp`, use EssenceR + NER.
2. **Universal R + A1–A5 ⇒ `ModalCollapseR`** (`ModalCollapseR_of_universal`);
   hence **`ContingentR` / `ContingentAct` impossible everywhere**.
3. **Scott universal encoding ⇒ `ModalCollapse`** (`ModalCollapse_of_Scott` from
   A1–A5); **`Contingent` impossible** (`Contingent_impossible_of_Scott`).
4. Symmetry packaging: `ModalCollapseAt_of_Symmetric_diamond` (◇∃G ⇒ collapse).
5. Bridge `NER_universalRel_eq_NE` / `A5R_of_A5_universalRel` ties Scott A5 to A5R.

### Countermodel D — ContingentR survives without Universal

- Frame: `WD = {a,b,c}`, `R_clusters` = equivalence `{a,b}` | `{c}` (**S5Frame**,
  not Universal).
- `Positive φ ↔ φ c ()`; GodLike only at `c`; A1–A5 hold.
- At `a`: `φ_a := (· = a)` is ContingentR; `ModalCollapseAt` fails at `a`.
- At `c`: collapse holds; ContingentR impossible (God-world).
- So **Scott A1–A5 + S5Frame do not rule out free-will-as-contingency globally**;
  Universality (God in every cluster) was load-bearing for that stronger claim.

### Relation to prior cuts

- ScottCuts / Countermodels A,B / Strictness C **left intact**.
- Countermodel A already showed S5 ⇏ global T3; D shows S5 ⇏ “no ContingentR
  anywhere,” even when A1–A5 and local God-collapse hold.

### Build

- `lake build` → success, **0 `sorry`**.
- Date: 2026-09-24 (America/New_York).

## WRP collapse / ContingentR (2026-09-24, America/New_York)

**Literature cut.** Sobel: Scott-style premises yield `φ → □φ` (1987; *Logic and
Theism* 2004). Benzmüller & Fuenmayor: Scott’s HOML variant (intensional /
world-relative positivity) entails modal collapse; Anderson and Fitting avoid it
(arXiv:1910.08955; BSL 49(2) 2020, DOI 10.18778/0138-0680.2020.08).

**Status: rediscovery** in `GodelOntological/CollapseWRP.lean` (thin `PosW`, not
rigid Positive). Write-up: `COLLAPSE_WRP.md`. Not a priority claim.

| Claim | Hypotheses in the type | Result |
| --- | --- | --- |
| Collapse at a God-world | A1W+A4W+A5W at `w` and `∃ GodLikeW` (no Symmetric) | `ModalCollapseAt_of_GodW` |
| Collapse at every world along `R` | **Symmetric** + `validW` A1W–A5W | `ModalCollapseR_of_Symmetric` |
| ContingentR impossible everywhere | same | `ContingentR_impossible_of_Symmetric` |
| Sobel `φ → □φ` | **Universal** + valid A1W–A5W | `ModalCollapse_of_Universal_WRP` |
| Sobel form from Symmetric alone | — | **false** on `idRel` (`wrp_idRel_R_collapse_not_sobel`) |

`#print axioms` on those theorems: `propext`, `Classical.choice`, `Quot.sound`.
0 `sorry`. Rigid Countermodel D (ContingentR off a non-God cluster) does not
transfer: under WRP, valid A3 puts God in every cluster. That comparison is
desk packaging; the collapse itself is the literature result above.
