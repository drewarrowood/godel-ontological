import GodelOntological.WeakScott
import GodelOntological.Countermodel

/-
# Modal collapse and free will as contingency

Sobel observed that Scott-style Gödel premises yield **modal collapse**
(`φ → □φ`); Benzmüller et al. re-verified this in HOML encodings. This file
re-checks the phenomenon **in this thin Lean package** — a rediscovery, not a
priority claim. See NOTES.md / README.

**Free will as contingency:** `ContingentR R φ w` means `φ` holds at `w` but
fails at some `R`-accessible world. Modal collapse rules that out wherever it
applies. Optional `ContingentAct` packages the same idea for individual-relative
“acts.”

| Setting | Collapse? | ContingentR? |
| --- | --- | --- |
| Universal R + A1–A5 | yes, everywhere | impossible everywhere |
| Scott universal encoding A1–A5 | yes (`ModalCollapse`) | impossible (`Contingent`) |
| God at `w` + A1+A5 (any R) | at `w` | impossible at `w` |
| S5Frame, non-universal (Countermodel D) | fails off God-cluster | **can survive** off God-cluster |
-/

namespace GodelOntological

/-! ## Contingency (free-will-as-contingency reading) -/

/-- A world-proposition `φ` is **contingent** at `w` relative to `R`:
true here, and false at some `R`-accessible world. -/
def ContingentR {W : Type} (R : Access W) (φ : W → Prop) (w : W) : Prop :=
  φ w ∧ possibleR R (fun v => ¬ φ v) w

/-- An individual `x` has a contingent “act” `α` at `w` when
`fun v => α v x` is contingent at `w`. -/
def ContingentAct {W Ind : Type} (R : Access W)
    (α : Property W Ind) (w : W) (x : Ind) : Prop :=
  ContingentR R (fun v => α v x) w

/-- Universal-frame contingency (`◇` = ∃ world): true here, false somewhere. -/
def Contingent {W : Type} (φ : W → Prop) (w : W) : Prop :=
  φ w ∧ ◇ (fun v => ¬ φ v)

/-! ## Modal collapse -/

/-- **R-relative modal collapse at `w`:** everything true at `w` is `R`-necessary. -/
def ModalCollapseAt {W : Type} (R : Access W) (w : W) : Prop :=
  ∀ φ : W → Prop, φ w → necessaryR R φ w

/-- **R-relative modal collapse (all worlds).** -/
def ModalCollapseR {W : Type} (R : Access W) : Prop :=
  ∀ w : W, ModalCollapseAt R w

/-- **Universal-frame modal collapse (Sobel):** `φ w → □ φ`. -/
def ModalCollapse {W : Type} : Prop :=
  ∀ φ : W → Prop, ∀ w : W, φ w → □ φ

/-! ## Collapse ⇒ no contingency -/

theorem ContingentR_impossible_of_collapseAt {W : Type} (R : Access W)
    {w : W} (hMC : ModalCollapseAt R w) (φ : W → Prop) :
    ¬ ContingentR R φ w := by
  intro ⟨hφ, ⟨v, hRv, hnφ⟩⟩
  exact hnφ (hMC φ hφ v hRv)

theorem ContingentAct_impossible_of_collapseAt {W Ind : Type} (R : Access W)
    {w : W} (hMC : ModalCollapseAt R w) (α : Property W Ind) (x : Ind) :
    ¬ ContingentAct R α w x :=
  ContingentR_impossible_of_collapseAt R hMC (fun v => α v x)

theorem Contingent_impossible_of_ModalCollapse {W : Type}
    (hMC : ModalCollapse (W := W)) (φ : W → Prop) (w : W) :
    ¬ Contingent φ w := by
  intro ⟨hφ, ⟨v, hnφ⟩⟩
  exact hnφ (hMC φ w hφ v)

/-! ## Local collapse at God-worlds (A1+A5 — Sobel/essence step)

Lift a world-proposition `φ` to the constant property `fun v _ => φ v`.
Essence of GodLike + reflection (NE) force `φ` on every `R`-successor.
-/

/-- Constant (individual-insensitive) property from a world-proposition. -/
def constProp {W Ind : Type} (φ : W → Prop) : Property W Ind :=
  fun v _ => φ v

theorem local_collapse_of_God {W Ind : Type} (R : Access W)
    (Positive : Property W Ind → Prop)
    (hA1 : A1R Positive) (hA5 : A5R R Positive)
    {w : W} (hEx : ∃ x : Ind, GodLike Positive w x)
    (φ : W → Prop) (hφ : φ w) :
    necessaryR R φ w := by
  obtain ⟨x, hx⟩ := hEx
  have hEss : EssenceR R (GodLike Positive) w x :=
    T2R_godlike_essence R Positive hA1 hx
  have hNE : NER R w x := godlike_has_NER R Positive hA5 hx
  have hBoxG :
      necessaryR R (fun v => ∃ y : Ind, GodLike Positive v y) w :=
    hNE (GodLike Positive) hEss
  have hψ : constProp (Ind := Ind) φ w x := hφ
  have hTrans :
      necessaryR R
        (fun v => ∀ y : Ind,
          GodLike Positive v y → constProp (Ind := Ind) φ v y) w :=
    hEss.2 (constProp (Ind := Ind) φ) hψ
  intro v hv
  obtain ⟨y, hy⟩ := hBoxG v hv
  exact hTrans v hv y hy

theorem ModalCollapseAt_of_God {W Ind : Type} (R : Access W)
    (Positive : Property W Ind → Prop)
    (hA1 : A1R Positive) (hA5 : A5R R Positive)
    {w : W} (hEx : ∃ x : Ind, GodLike Positive w x) :
    ModalCollapseAt R w :=
  fun φ hφ => local_collapse_of_God R Positive hA1 hA5 hEx φ hφ

/-- Under symmetry: local ◇∃G ⇒ collapse at `w`. -/
theorem ModalCollapseAt_of_Symmetric_diamond {W Ind : Type} (R : Access W)
    (hSym : Symmetric R)
    (Positive : Property W Ind → Prop)
    (hA1 : A1R Positive) (hA5 : A5R R Positive)
    {w : W}
    (hPos : possibleR R (fun v => ∃ x : Ind, GodLike Positive v x) w) :
    ModalCollapseAt R w := by
  have hEx : ∃ x : Ind, GodLike Positive w x :=
    local_exists_God_of_Symmetric R hSym Positive hA1 hA5 hPos
  exact ModalCollapseAt_of_God R Positive hA1 hA5 hEx

/-- ContingentR impossible at any God-world (A1+A5). -/
theorem ContingentR_impossible_at_God {W Ind : Type} (R : Access W)
    (Positive : Property W Ind → Prop)
    (hA1 : A1R Positive) (hA5 : A5R R Positive)
    {w : W} (hEx : ∃ x : Ind, GodLike Positive w x)
    (φ : W → Prop) :
    ¬ ContingentR R φ w :=
  ContingentR_impossible_of_collapseAt R
    (ModalCollapseAt_of_God R Positive hA1 hA5 hEx) φ

/-! ## Full collapse under Universal R + A1–A5 -/

/-- Under **Universal R** + A1–A5: modal collapse at every world.
Costs: `Universal R`, A1, A2, A3, A5 — all in the type. -/
theorem ModalCollapseR_of_universal {W Ind : Type} (R : Access W)
    (hU : Universal R)
    (Positive : Property W Ind → Prop)
    (hA1 : A1R Positive) (hA2 : A2R Positive)
    (hA3 : A3R Positive) (hA5 : A5R R Positive) :
    ModalCollapseR R := by
  intro w
  have hEx : ∃ x : Ind, GodLike Positive w x :=
    T3R_necessarily_God_of_universal R hU Positive hA1 hA2 hA3 hA5 w
  exact ModalCollapseAt_of_God R Positive hA1 hA5 hEx

/-- ContingentR impossible everywhere under Universal + A1–A5. -/
theorem ContingentR_impossible_of_universal {W Ind : Type} (R : Access W)
    (hU : Universal R)
    (Positive : Property W Ind → Prop)
    (hA1 : A1R Positive) (hA2 : A2R Positive)
    (hA3 : A3R Positive) (hA5 : A5R R Positive)
    (φ : W → Prop) (w : W) :
    ¬ ContingentR R φ w :=
  ContingentR_impossible_of_collapseAt R
    (ModalCollapseR_of_universal R hU Positive hA1 hA2 hA3 hA5 w) φ

theorem ContingentAct_impossible_of_universal {W Ind : Type} (R : Access W)
    (hU : Universal R)
    (Positive : Property W Ind → Prop)
    (hA1 : A1R Positive) (hA2 : A2R Positive)
    (hA3 : A3R Positive) (hA5 : A5R R Positive)
    (α : Property W Ind) (w : W) (x : Ind) :
    ¬ ContingentAct R α w x :=
  ContingentR_impossible_of_universal R hU Positive hA1 hA2 hA3 hA5
    (fun v => α v x) w

/-! ## Universal-frame Scott (`Scott.lean`) ⇒ ModalCollapse -/

/-- Sobel collapse in the universal encoding: A1–A5 ⊢ `φ → □φ`.
Rediscovery in this package (Sobel 1987/2004; Benzmüller et al.). -/
theorem ModalCollapse_of_Scott {W Ind : Type}
    (Positive : Property W Ind → Prop)
    (hA1 : A1 Positive) (hA2 : A2 Positive)
    (hA3 : A3 Positive) (hA5 : A5 Positive) :
    ModalCollapse (W := W) := by
  intro φ w hφ v
  obtain ⟨x, hx⟩ := exists_God_at_every_world Positive hA1 hA2 hA3 hA5 w
  have hEss : Essence (GodLike Positive) w x :=
    T2_godlike_essence Positive hA1 hx
  have hTrans : □ (fun u => ∀ y : Ind,
      GodLike Positive u y → constProp (Ind := Ind) φ u y) :=
    hEss.2 (constProp (Ind := Ind) φ) hφ
  obtain ⟨y, hy⟩ := exists_God_at_every_world Positive hA1 hA2 hA3 hA5 v
  exact hTrans v y hy

/-- Contingency impossible under Scott A1–A5 (universal encoding). -/
theorem Contingent_impossible_of_Scott {W Ind : Type}
    (Positive : Property W Ind → Prop)
    (hA1 : A1 Positive) (hA2 : A2 Positive)
    (hA3 : A3 Positive) (hA5 : A5 Positive)
    (φ : W → Prop) (w : W) :
    ¬ Contingent φ w :=
  Contingent_impossible_of_ModalCollapse
    (ModalCollapse_of_Scott Positive hA1 hA2 hA3 hA5) φ w

/-- Bridge: under `universalRel`, `NER` coincides with `NE`, so A5 ⇒ A5R. -/
theorem NER_universalRel_eq_NE {W Ind : Type} :
    NER (universalRel W) = (NE : Property W Ind) := by
  funext w x
  apply propext
  constructor
  · intro hNER φ hEss
    have hEssR : EssenceR (universalRel W) φ w x := by
      refine ⟨hEss.1, ?_⟩
      intro ψ hψ v _hv y hy
      exact hEss.2 ψ hψ v y hy
    intro v
    exact hNER φ hEssR v trivial
  · intro hNE φ hEssR
    have hEss : Essence φ w x := by
      refine ⟨hEssR.1, ?_⟩
      intro ψ hψ v y hy
      exact hEssR.2 ψ hψ v trivial y hy
    intro v _hv
    exact hNE φ hEss v

theorem A5R_of_A5_universalRel {W Ind : Type}
    (Positive : Property W Ind → Prop) (hA5 : A5 Positive) :
    A5R (universalRel W) Positive := by
  simpa [A5R, A5, NER_universalRel_eq_NE] using hA5

/-- Recover R-collapse from Scott via the universal relation. -/
theorem ModalCollapseR_recover_universalRel {W Ind : Type}
    (Positive : Property W Ind → Prop)
    (hA1 : A1 Positive) (hA2 : A2 Positive)
    (hA3 : A3 Positive) (hA5 : A5 Positive) :
    ModalCollapseR (universalRel W) :=
  ModalCollapseR_of_universal (universalRel W)
    (universalRel_is_universal W) Positive hA1 hA2 hA3
    (A5R_of_A5_universalRel Positive hA5)

/-! ## Countermodel D — ContingentR survives off the God-cluster

**S5Frame** + A1–A5 need **not** kill ContingentR globally: when `R` is not
universal, a non-God equivalence cluster can still vary a proposition across
accessible worlds. Universality (or God in every cluster) was load-bearing for
“no free-will-as-contingency anywhere.”

Concrete model:
* `W = {a,b,c}`, `R` = equivalence with clusters `{a,b}` and `{c}` (S5, not universal)
* `Ind = Unit`, `Positive φ ↔ φ c ()`
* GodLike only at `c`; ContingentR at `a` for `φ := (· = a)`
-/

namespace CollapseCountermodel

inductive WD where
  | a | b | c
  deriving DecidableEq, Repr

/-- Two S5 clusters: `{a,b}` and `{c}`. -/
def R_clusters : Access WD := fun w v =>
  match w, v with
  | .a, .a | .b, .b | .c, .c => True
  | .a, .b | .b, .a => True
  | _, _ => False

theorem R_clusters_reflexive : Reflexive R_clusters := by
  intro w; cases w <;> simp [R_clusters]

theorem R_clusters_symmetric : Symmetric R_clusters := by
  intro w v hwv
  cases w <;> cases v <;> simp_all [R_clusters]

theorem R_clusters_transitive : Transitive R_clusters := by
  intro w v u hwv hvu
  cases w <;> cases v <;> cases u <;> simp_all [R_clusters]

theorem R_clusters_euclidean : Euclidean R_clusters := by
  intro w v u hwv hwu
  cases w <;> cases v <;> cases u <;> simp_all [R_clusters]

theorem R_clusters_s5 : S5Frame R_clusters :=
  ⟨R_clusters_reflexive, R_clusters_euclidean⟩

theorem R_clusters_not_universal : ¬ Universal R_clusters := by
  intro hU
  have : R_clusters .a .c := hU .a .c
  simp [R_clusters] at this

abbrev Ind1 : Type := Unit

def PosD : Property WD Ind1 → Prop := Countermodel.PositiveAt (pivot := WD.c)

theorem PosD_A1 : A1R PosD := Countermodel.A1_PositiveAt WD.c
theorem PosD_A2 : A2R PosD := Countermodel.A2_PositiveAt WD.c

theorem GodLike_PosD (w : WD) (x : Ind1) :
    GodLike PosD w x ↔ w = WD.c := by
  constructor
  · intro hg
    let φ : Property WD Ind1 := fun v _ => v = WD.c
    have hP : PosD φ := rfl
    exact hg φ hP
  · intro hw φ hP
    cases x
    rw [hw]; exact hP

theorem PosD_A3 : A3R PosD :=
  (GodLike_PosD WD.c ()).mpr rfl

/-- NER at the singleton God-cluster `{c}`. -/
theorem NER_clusters_at_c (x : Ind1) : NER R_clusters WD.c x := by
  intro φ hEss
  intro v hv
  cases x
  -- hv : R c v ⇒ v = c
  have hv' : v = WD.c := by
    cases v <;> simp_all [R_clusters]
  refine ⟨(), ?_⟩
  have hφ : φ WD.c () := hEss.1
  simpa [hv'] using hφ

theorem PosD_A5 : A5R R_clusters PosD :=
  NER_clusters_at_c ()

theorem PosD_God_only_at_c :
    (∃ x : Ind1, GodLike PosD WD.c x) ∧
    ¬ (∃ x : Ind1, GodLike PosD WD.a x) ∧
    ¬ (∃ x : Ind1, GodLike PosD WD.b x) := by
  refine ⟨⟨(), (GodLike_PosD WD.c ()).mpr rfl⟩, ?_, ?_⟩
  · intro ⟨x, hx⟩
    have : WD.a = WD.c := (GodLike_PosD WD.a x).mp hx
    cases this
  · intro ⟨x, hx⟩
    have : WD.b = WD.c := (GodLike_PosD WD.b x).mp hx
    cases this

/-- Witness proposition: true only at `a`. -/
def φ_a : WD → Prop := fun w => w = WD.a

theorem ContingentR_at_a :
    ContingentR R_clusters φ_a WD.a := by
  refine ⟨rfl, ⟨WD.b, ?_, ?_⟩⟩
  · simp [R_clusters]
  · simp [φ_a]

theorem ModalCollapseAt_fails_at_a :
    ¬ ModalCollapseAt R_clusters WD.a := by
  intro hMC
  have hNec : necessaryR R_clusters φ_a WD.a := hMC φ_a rfl
  have : WD.b = WD.a := hNec WD.b (by simp [R_clusters])
  cases this

/-- Collapse still holds at the God-world. -/
theorem ModalCollapseAt_holds_at_c :
    ModalCollapseAt R_clusters WD.c :=
  ModalCollapseAt_of_God R_clusters PosD PosD_A1 PosD_A5
    ⟨(), (GodLike_PosD WD.c ()).mpr rfl⟩

/-- ContingentR impossible at the God-world (sanity). -/
theorem ContingentR_impossible_at_c (φ : WD → Prop) :
    ¬ ContingentR R_clusters φ WD.c :=
  ContingentR_impossible_of_collapseAt R_clusters ModalCollapseAt_holds_at_c φ

/-- **Countermodel D.** S5Frame + A1–A5, yet ContingentR survives at `a`
(non-God cluster). Free-will-as-contingency is not ruled out by Scott axioms
alone without universality / God in every cluster. -/
theorem countermodel_D_ContingentR_survives :
    S5Frame R_clusters ∧
    ¬ Universal R_clusters ∧
    A1R PosD ∧ A2R PosD ∧ A3R PosD ∧ A5R R_clusters PosD ∧
    (∃ x : Ind1, GodLike PosD WD.c x) ∧
    ¬ (∃ x : Ind1, GodLike PosD WD.a x) ∧
    ContingentR R_clusters φ_a WD.a ∧
    ¬ ModalCollapseAt R_clusters WD.a ∧
    ModalCollapseAt R_clusters WD.c :=
  ⟨R_clusters_s5, R_clusters_not_universal,
    PosD_A1, PosD_A2, PosD_A3, PosD_A5,
    PosD_God_only_at_c.1, PosD_God_only_at_c.2.1,
    ContingentR_at_a, ModalCollapseAt_fails_at_a,
    ModalCollapseAt_holds_at_c⟩

end CollapseCountermodel

end GodelOntological
