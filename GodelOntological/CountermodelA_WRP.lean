import GodelOntological.WeakScott
import GodelOntological.Countermodel

/-
# Countermodel A under world-relative Positive (WRP stress test)

Benzmüller–Scott HOML takes positivity as intensional / world-relative
(`P :: (e⇒σ)⇒σ`, `σ = i⇒bool`) with validity `⌊φ⌋ ≡ ∀w. φ w`, and A4
rigidifies positivity along `R` inside a cluster. Under that packaging,
equivalence-S5 yields global T3; they do not exhibit Countermodel A.

This module mirrors that idea in the thin Prop embedding (no full HOML):
* `PosW : W → Property W Ind → Prop` — positivity at an evaluation world
* A1–A5 stated *at each world*; global validity = `∀ w, …`
* A4: `PosW w φ → necessaryR R (fun v => PosW v φ) w`

## Verdict

**Countermodel A dies under WRP.** Global validity of A1–A5 (with A4) plus
`Symmetric R` already forces `∀ w, ∃ x, GodLikeW PosW w x` — no `Universal R`
required. The Bool/`idRel` shape with the natural localisation of `PositiveAt`
satisfies the WRP hypotheses *and* global T3, so it is not a countermodel.

The rigid-Positive Countermodel A exploited a single global `A3` bit that
places God in one cluster only. WRP reinstates A3 at every world, so every
cluster gets its own local C + reflection.
-/

namespace GodelOntological
namespace CountermodelA_WRP

/-! ## Signature: world-relative Positive -/

/-- World-relative positivity: evaluated at a world. -/
abbrev PosW (W Ind : Type) := W → Property W Ind → Prop

/-- **D1 (WRP).** God-like at `w`: has every property positive *at `w`*. -/
def GodLikeW {W Ind : Type} (P : PosW W Ind) : Property W Ind :=
  fun w x => ∀ φ : Property W Ind, P w φ → φ w x

/-- **D2 (WRP).** Essence relative to `R` (same shape as `EssenceR`). -/
def EssenceW {W Ind : Type} (R : Access W) (φ : Property W Ind)
    (w : W) (x : Ind) : Prop :=
  φ w x ∧
    ∀ ψ : Property W Ind, ψ w x →
      necessaryR R (fun v => ∀ y : Ind, φ v y → ψ v y) w

/-- **D3 (WRP).** Necessary existence relative to `R`. -/
def NEW {W Ind : Type} (R : Access W) : Property W Ind :=
  fun w x =>
    ∀ φ : Property W Ind, EssenceW R φ w x →
      necessaryR R (fun v => ∃ y : Ind, φ v y) w

/-! ## Axioms at a world (Benzmüller–Scott style, thin Prop) -/

/-- **A1 at `w`.** Exclusive/exhaustive positivity for complements. -/
def A1W {W Ind : Type} (P : PosW W Ind) (w : W) : Prop :=
  ∀ φ : Property W Ind, P w (propNeg φ) ↔ ¬ P w φ

/-- **A2 at `w`.** `R`-necessary entailment preserves positivity at `w`. -/
def A2W {W Ind : Type} (R : Access W) (P : PosW W Ind) (w : W) : Prop :=
  ∀ φ ψ : Property W Ind,
    P w φ → necessaryR R (fun v => ∀ y : Ind, φ v y → ψ v y) w → P w ψ

/-- **A3 at `w`.** Being God-like is positive at `w`. -/
def A3W {W Ind : Type} (P : PosW W Ind) (w : W) : Prop :=
  P w (GodLikeW P)

/-- **A4 at `w`.** Positivity rigidifies along `R`-successors (Scott A4). -/
def A4W {W Ind : Type} (R : Access W) (P : PosW W Ind) (w : W) : Prop :=
  ∀ φ : Property W Ind, P w φ → necessaryR R (fun v => P v φ) w

/-- **A5 at `w`.** Necessary existence is positive at `w`. -/
def A5W {W Ind : Type} (R : Access W) (P : PosW W Ind) (w : W) : Prop :=
  P w (NEW R)

/-- Global validity: the axiom holds at every world. -/
def validW {W : Type} (Ax : W → Prop) : Prop := ∀ w : W, Ax w

/-! ## Local chain under WRP -/

theorem positive_propTrue_W {W Ind : Type} (R : Access W) (P : PosW W Ind)
    {w : W} (hA2 : A2W R P w) {φ : Property W Ind} (hφ : P w φ) :
    P w (propTrue : Property W Ind) :=
  hA2 φ propTrue hφ (fun _ _ _ _ => trivial)

/-- **T1 (local, WRP).** Positive at `w` ⇒ `possibleR (∃ φ) w`. -/
theorem T1W {W Ind : Type} (R : Access W) (P : PosW W Ind)
    {w : W} (hA1 : A1W P w) (hA2 : A2W R P w)
    (φ : Property W Ind) (hP : P w φ) :
    possibleR R (fun v => ∃ x : Ind, φ v x) w := by
  apply Classical.byContradiction
  intro h
  have nowhere : necessaryR R (fun v => ∀ y : Ind, ¬ φ v y) w := by
    intro v hv y hy
    exact h ⟨v, hv, y, hy⟩
  have hEntFalse :
      necessaryR R (fun v => ∀ y : Ind, φ v y → (propFalse : Property W Ind) v y) w := by
    intro v hv y hy
    exact (nowhere v hv y) hy
  have hFalse : P w (propFalse : Property W Ind) := hA2 φ propFalse hP hEntFalse
  have hNegTrue : P w (propNeg (propTrue : Property W Ind)) := by
    -- propNeg propTrue = propFalse definitionally after simp
    simpa [propNeg, propTrue, propFalse] using hFalse
  have hNotTrue : ¬ P w (propTrue : Property W Ind) := (hA1 propTrue).mp hNegTrue
  have hTrue : P w (propTrue : Property W Ind) :=
    positive_propTrue_W R P hA2 hP
  exact hNotTrue hTrue

/-- **C (local, WRP).** A3 at `w` ⇒ `possibleR (∃ GodLikeW) w`. -/
theorem CW {W Ind : Type} (R : Access W) (P : PosW W Ind)
    {w : W} (hA1 : A1W P w) (hA2 : A2W R P w) (hA3 : A3W P w) :
    possibleR R (fun v => ∃ x : Ind, GodLikeW P v x) w :=
  T1W R P hA1 hA2 (GodLikeW P) hA3

theorem godlike_has_only_positive_W {W Ind : Type} (P : PosW W Ind)
    {w : W} (hA1 : A1W P w) {x : Ind} {ψ : Property W Ind}
    (hg : GodLikeW P w x) (hψ : ψ w x) :
    P w ψ := by
  apply Classical.byContradiction
  intro hNot
  have hNeg : P w (propNeg ψ) := (hA1 ψ).mpr hNot
  exact (hg (propNeg ψ) hNeg) hψ

/-- **T2 (WRP).** God-like ⇒ EssenceW of GodLikeW. Needs A1 at `w` and A4 at `w`
so positivity of witnessed properties transfers to `R`-successors. -/
theorem T2W {W Ind : Type} (R : Access W) (P : PosW W Ind)
    {w : W} (hA1 : A1W P w) (hA4 : A4W R P w)
    {x : Ind} (hg : GodLikeW P w x) :
    EssenceW R (GodLikeW P) w x := by
  refine ⟨hg, ?_⟩
  intro ψ hψ
  have hPos : P w ψ := godlike_has_only_positive_W P hA1 hg hψ
  have hPosBox : necessaryR R (fun v => P v ψ) w := hA4 ψ hPos
  intro v hv y hy
  -- hy : GodLikeW P v y, and P v ψ, so ψ v y
  exact hy ψ (hPosBox v hv)

theorem godlike_has_NEW {W Ind : Type} (R : Access W) (P : PosW W Ind)
    {w : W} (hA5 : A5W R P w) {x : Ind} (hg : GodLikeW P w x) :
    NEW R w x :=
  hg (NEW R) hA5

/-- Local reflection: God at `w` ⇒ `necessaryR (∃ GodLikeW) w`. -/
theorem exists_God_implies_necessaryW {W Ind : Type} (R : Access W)
    (P : PosW W Ind) {w : W}
    (hA1 : A1W P w) (hA4 : A4W R P w) (hA5 : A5W R P w)
    (hEx : ∃ x : Ind, GodLikeW P w x) :
    necessaryR R (fun v => ∃ y : Ind, GodLikeW P v y) w := by
  obtain ⟨x, hx⟩ := hEx
  have hEss : EssenceW R (GodLikeW P) w x := T2W R P hA1 hA4 hx
  have hNE : NEW R w x := godlike_has_NEW R P hA5 hx
  exact hNE (GodLikeW P) hEss

/-- Local T3 under **Symmetric** alone (same residual cut as rigid WeakScott). -/
theorem local_T3W_of_Symmetric {W Ind : Type} (R : Access W)
    (hSym : Symmetric R) (P : PosW W Ind) {w : W}
    (hA1 : A1W P w) (hA4 : A4W R P w) (hA5 : A5W R P w)
    -- Need A1/A4/A5 also at the witness successor `v`; package as valid on all worlds
    (hA1all : validW (A1W P)) (hA4all : validW (A4W R P)) (hA5all : validW (A5W R P))
    (hPos : possibleR R (fun v => ∃ x : Ind, GodLikeW P v x) w) :
    necessaryR R (fun v => ∃ y : Ind, GodLikeW P v y) w := by
  obtain ⟨v, hRv, hEx⟩ := hPos
  have hNecAtV :
      necessaryR R (fun u => ∃ y : Ind, GodLikeW P u y) v :=
    exists_God_implies_necessaryW R P (hA1all v) (hA4all v) (hA5all v) hEx
  have hExAtW : ∃ x : Ind, GodLikeW P w x :=
    hNecAtV w (hSym w v hRv)
  exact exists_God_implies_necessaryW R P hA1 hA4 hA5 hExAtW

/-! ## Global T3 without Universal — Countermodel A dies -/

/-- **Obstruction (WRP kills Countermodel A).**
If A1–A5 (with A4) are *valid at every world* and `R` is symmetric, then
`∀ w, ∃ x, GodLikeW P w x`. No `Universal R` hypothesis.

Contrast with rigid `WeakScott.T3R_necessarily_God_of_universal`, which needs
`Universal R` because rigid A3 is a single global bit (God somewhere once). -/
theorem global_T3W_of_Symmetric {W Ind : Type} (R : Access W)
    (hSym : Symmetric R) (P : PosW W Ind)
    (hA1 : validW (A1W P))
    (hA2 : validW (A2W R P))
    (hA3 : validW (A3W P))
    (hA4 : validW (A4W R P))
    (hA5 : validW (A5W R P)) :
    ∀ w : W, ∃ x : Ind, GodLikeW P w x := by
  intro w
  have hDiamond : possibleR R (fun v => ∃ x : Ind, GodLikeW P v x) w :=
    CW R P (hA1 w) (hA2 w) (hA3 w)
  -- Symmetric alone need not be reflexive: read God at `w` via the diamond
  -- witness + back-edge (same pattern as `local_exists_God_of_Symmetric`).
  obtain ⟨v, hRv, hEx⟩ := hDiamond
  have hNecAtV :
      necessaryR R (fun u => ∃ y : Ind, GodLikeW P u y) v :=
    exists_God_implies_necessaryW R P (hA1 v) (hA4 v) (hA5 v) hEx
  exact hNecAtV w (hSym w v hRv)

/-- Same conclusion under `S5Frame` (via `S5Frame.symmetric`). -/
theorem global_T3W_of_S5 {W Ind : Type} (R : Access W)
    (hS5 : S5Frame R) (P : PosW W Ind)
    (hA1 : validW (A1W P))
    (hA2 : validW (A2W R P))
    (hA3 : validW (A3W P))
    (hA4 : validW (A4W R P))
    (hA5 : validW (A5W R P)) :
    ∀ w : W, ∃ x : Ind, GodLikeW P w x :=
  global_T3W_of_Symmetric R hS5.symmetric P hA1 hA2 hA3 hA4 hA5

/-- Packaged: the Bool/`idRel` shape **cannot** be a WRP countermodel to global T3. -/
theorem countermodel_A_shape_dies_under_WRP
    (P : PosW Countermodel.W2 Countermodel.Ind1)
    (hA1 : validW (A1W P))
    (hA2 : validW (A2W Countermodel.R_id P))
    (hA3 : validW (A3W P))
    (hA4 : validW (A4W Countermodel.R_id P))
    (hA5 : validW (A5W Countermodel.R_id P)) :
    ∀ w : Countermodel.W2, ∃ x : Countermodel.Ind1, GodLikeW P w x :=
  global_T3W_of_S5 Countermodel.R_id Countermodel.R_id_s5 P hA1 hA2 hA3 hA4 hA5

/-! ## Natural localisation of `PositiveAt` — axioms hold, global T3 holds -/

/-- Localise rigid `PositiveAt`: at evaluation world `w`, φ is positive iff
φ holds of `()` at `w`. This is the direct WRP analogue of Countermodel A's
`PosA = PositiveAt false`. -/
def PosLocal : PosW Countermodel.W2 Countermodel.Ind1 :=
  fun w φ => φ w ()

theorem PosLocal_A1 : validW (A1W PosLocal) := by
  intro w φ
  constructor
  · intro hNeg hPos
    exact hNeg hPos
  · intro hNot
    exact hNot

theorem PosLocal_A2 : validW (A2W Countermodel.R_id PosLocal) := by
  intro w φ ψ hP hEnt
  -- under idRel, hEnt only constrains world w
  exact hEnt w rfl () hP

theorem PosLocal_GodLike (w : Countermodel.W2) (x : Countermodel.Ind1) :
    GodLikeW PosLocal w x := by
  cases x
  intro φ hP
  exact hP

theorem PosLocal_A3 : validW (A3W PosLocal) := by
  intro w
  -- A3W: PosLocal w (GodLikeW PosLocal) = GodLikeW PosLocal w ()
  exact PosLocal_GodLike w ()

theorem PosLocal_A4 : validW (A4W Countermodel.R_id PosLocal) := by
  intro w φ hP v hv
  -- hv : w = v
  cases hv
  exact hP

theorem NER_id_Unit (w : Countermodel.W2) (x : Countermodel.Ind1) :
    NEW Countermodel.R_id w x := by
  intro φ hEss v hv
  cases x
  refine ⟨(), ?_⟩
  have hφ : φ w () := hEss.1
  cases hv
  exact hφ

theorem PosLocal_A5 : validW (A5W Countermodel.R_id PosLocal) := by
  intro w
  exact NER_id_Unit w ()

/-- The natural WRP reading of Countermodel A's frame+Ind satisfies all global
WRP Scott hypotheses **and** has God at every world — so global T3 holds. -/
theorem PosLocal_is_not_a_countermodel :
    S5Frame Countermodel.R_id ∧
    validW (A1W PosLocal) ∧
    validW (A2W Countermodel.R_id PosLocal) ∧
    validW (A3W PosLocal) ∧
    validW (A4W Countermodel.R_id PosLocal) ∧
    validW (A5W Countermodel.R_id PosLocal) ∧
    (∀ w : Countermodel.W2, ∃ x : Countermodel.Ind1, GodLikeW PosLocal w x) ∧
    ¬ Universal Countermodel.R_id := by
  refine ⟨Countermodel.R_id_s5, PosLocal_A1, PosLocal_A2, PosLocal_A3,
    PosLocal_A4, PosLocal_A5, ?_, Countermodel.R_id_not_universal⟩
  intro w
  exact ⟨(), PosLocal_GodLike w ()⟩

/-- Direct instance of the obstruction on this concrete PosW. -/
theorem PosLocal_global_T3_by_obstruction :
    ∀ w : Countermodel.W2, ∃ x : Countermodel.Ind1, GodLikeW PosLocal w x :=
  countermodel_A_shape_dies_under_WRP PosLocal
    PosLocal_A1 PosLocal_A2 PosLocal_A3 PosLocal_A4 PosLocal_A5

/-! ## Encoding gap vs rigid Countermodel A -/

/-- Rigid `PosA` makes GodLike fail at `true`. Under WRP global A3, that failure
mode is unavailable: A3 at `true` forces `possibleR (∃G) true`, and on `idRel`
that is exactly God at `true`. -/
theorem rigid_gap_A3_at_true_forces_God
    (P : PosW Countermodel.W2 Countermodel.Ind1)
    (hA1 : A1W P true) (hA2 : A2W Countermodel.R_id P true) (hA3 : A3W P true) :
    ∃ x : Countermodel.Ind1, GodLikeW P true x := by
  have hD := CW Countermodel.R_id P hA1 hA2 hA3
  obtain ⟨v, hv, hEx⟩ := hD
  -- hv : true = v
  cases hv
  exact hEx

end CountermodelA_WRP
end GodelOntological
