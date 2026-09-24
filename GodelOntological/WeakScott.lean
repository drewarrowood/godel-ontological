import GodelOntological.Scott
import GodelOntological.Frames

/-
# Scott axioms relative to an accessibility relation

Parallel to `Scott.lean`, but □ / ◇ / Essence / NE are `R`-relative.
`Positive` stays rigid. Axioms A1–A5 remain Prop-valued hypotheses.

Key results:
* Local reflection needs only A1+A5 (no frame hypothesis).
* Local T3 (`possibleR (∃G) w → necessaryR (∃G) w`) needs only **Symmetric R**
  (Brouwerian / axiom B) in the theorem type — strictly weaker than `S5Frame`.
* Global `∀w, ∃x GodLike w x` needs **Universal R** (stronger than S5Frame).
-/

namespace GodelOntological

/-! ## R-relative definitions -/

/-- Necessary entailment as a *validity*: □∀x(φ→ψ) at every world. -/
def necEntailsR {W Ind : Type} (R : Access W) (φ ψ : Property W Ind) : Prop :=
  ∀ w : W, necessaryR R (fun v => ∀ y : Ind, φ v y → ψ v y) w

/-- Global (frame-independent) entailment — same as `Modal.necEntails`. -/
def necEntailsGlobal {W Ind : Type} (φ ψ : Property W Ind) : Prop :=
  ∀ w : W, ∀ x : Ind, φ w x → ψ w x

/-- **D1.** God-like (unchanged: rigid Positive). -/
def GodLikeR {W Ind : Type} (Positive : Property W Ind → Prop) : Property W Ind :=
  GodLike Positive

/-- **D2.** Essence relative to `R`. -/
def EssenceR {W Ind : Type} (R : Access W) (φ : Property W Ind)
    (w : W) (x : Ind) : Prop :=
  φ w x ∧
    ∀ ψ : Property W Ind, ψ w x →
      necessaryR R (fun v => ∀ y : Ind, φ v y → ψ v y) w

/-- **D3.** Necessary existence relative to `R`. -/
def NER {W Ind : Type} (R : Access W) : Property W Ind :=
  fun w x =>
    ∀ φ : Property W Ind, EssenceR R φ w x →
      necessaryR R (fun v => ∃ y : Ind, φ v y) w

/-! ## Axioms (A2 uses global entailment, matching `Scott.lean`) -/

def A1R {W Ind : Type} (Positive : Property W Ind → Prop) : Prop :=
  A1 Positive

def A2R {W Ind : Type} (Positive : Property W Ind → Prop) : Prop :=
  A2 Positive

def A3R {W Ind : Type} (Positive : Property W Ind → Prop) : Prop :=
  A3 Positive

def A5R {W Ind : Type} (R : Access W) (Positive : Property W Ind → Prop) : Prop :=
  Positive (NER R)

/-! ## Fragments that do not need frame conditions -/

theorem positive_propTrue_R {W Ind : Type} (Positive : Property W Ind → Prop)
    (hA2 : A2R Positive) {φ : Property W Ind} (hφ : Positive φ) :
    Positive (propTrue : Property W Ind) :=
  positive_propTrue Positive hA2 hφ

/-- **T1** (global reading): positive ⇒ exemplified somewhere in `W`.
Uses A1+A2 only; accessibility unused (same proof as `Scott.T1`). -/
theorem T1R_positive_possibly_exemplified {W Ind : Type}
    (Positive : Property W Ind → Prop)
    (hA1 : A1R Positive) (hA2 : A2R Positive)
    (φ : Property W Ind) (hP : Positive φ) :
    ∃ w : W, ∃ x : Ind, φ w x :=
  T1_positive_possibly_exemplified Positive hA1 hA2 φ hP

/-- **C** (global): some world has a God-like being. -/
theorem CR_possibly_God {W Ind : Type} (Positive : Property W Ind → Prop)
    (hA1 : A1R Positive) (hA2 : A2R Positive) (hA3 : A3R Positive) :
    ∃ w : W, ∃ x : Ind, GodLike Positive w x :=
  C_possibly_God Positive hA1 hA2 hA3

theorem godlike_has_only_positive_R {W Ind : Type}
    (Positive : Property W Ind → Prop) (hA1 : A1R Positive)
    {w : W} {x : Ind} {ψ : Property W Ind}
    (hg : GodLike Positive w x) (hψ : ψ w x) :
    Positive ψ :=
  godlike_has_only_positive Positive hA1 hg hψ

/-- **T2** relative to `R`: God-like ⇒ EssenceR (needs A1 only). -/
theorem T2R_godlike_essence {W Ind : Type} (R : Access W)
    (Positive : Property W Ind → Prop) (hA1 : A1R Positive)
    {w : W} {x : Ind} (hg : GodLike Positive w x) :
    EssenceR R (GodLike Positive) w x := by
  refine ⟨hg, ?_⟩
  intro ψ hψ
  have hPos : Positive ψ := godlike_has_only_positive_R Positive hA1 hg hψ
  intro v _hv y hy
  exact hy ψ hPos

theorem godlike_has_NER {W Ind : Type} (R : Access W)
    (Positive : Property W Ind → Prop) (hA5 : A5R R Positive)
    {w : W} {x : Ind} (hg : GodLike Positive w x) :
    NER R w x :=
  hg (NER R) hA5

/-- Local reflection: God at `w` ⇒ `necessaryR (∃ GodLike) w`.
Needs A1+A5 only — **no** frame hypothesis. -/
theorem exists_God_implies_necessaryR {W Ind : Type} (R : Access W)
    (Positive : Property W Ind → Prop)
    (hA1 : A1R Positive) (hA5 : A5R R Positive)
    {w : W} (hEx : ∃ x : Ind, GodLike Positive w x) :
    necessaryR R (fun v => ∃ y : Ind, GodLike Positive v y) w := by
  obtain ⟨x, hx⟩ := hEx
  have hEss : EssenceR R (GodLike Positive) w x :=
    T2R_godlike_essence R Positive hA1 hx
  have hNE : NER R w x := godlike_has_NER R Positive hA5 hx
  exact hNE (GodLike Positive) hEss

/-! ## Local T3 under symmetry alone (strictly weaker than S5Frame) -/

/-- Under **symmetry** alone, possibility of God at `w` lifts to necessity of
God at `w`. Proof: ◇∃G at `w` gives an `R`-successor `v` with God; reflection
at `v` + `R v w` (symmetry) yields God at `w`; reflection at `w` yields □∃G.
No reflexivity, transitivity, or euclidean hypothesis. -/
theorem local_T3_of_Symmetric {W Ind : Type} (R : Access W)
    (hSym : Symmetric R)
    (Positive : Property W Ind → Prop)
    (hA1 : A1R Positive) (hA5 : A5R R Positive)
    {w : W}
    (hPos : possibleR R (fun v => ∃ x : Ind, GodLike Positive v x) w) :
    necessaryR R (fun v => ∃ y : Ind, GodLike Positive v y) w := by
  obtain ⟨v, hRv, hEx⟩ := hPos
  have hNecAtV :
      necessaryR R (fun u => ∃ y : Ind, GodLike Positive u y) v :=
    exists_God_implies_necessaryR R Positive hA1 hA5 hEx
  have hExAtW : ∃ x : Ind, GodLike Positive w x :=
    hNecAtV w (hSym w v hRv)
  exact exists_God_implies_necessaryR R Positive hA1 hA5 hExAtW

/-- Same as `local_T3_of_Symmetric`, packaged under the `Brouwerian` name. -/
theorem local_T3_of_Brouwerian {W Ind : Type} (R : Access W)
    (hB : Brouwerian R)
    (Positive : Property W Ind → Prop)
    (hA1 : A1R Positive) (hA5 : A5R R Positive)
    {w : W}
    (hPos : possibleR R (fun v => ∃ x : Ind, GodLike Positive v x) w) :
    necessaryR R (fun v => ∃ y : Ind, GodLike Positive v y) w :=
  local_T3_of_Symmetric R hB Positive hA1 hA5 hPos

/-- Under **TB** (refl + sym), same local T3. Reflexivity is unused for this
direction; it is recorded for the standard T+B packaging. -/
theorem local_T3_of_TB {W Ind : Type} (R : Access W)
    (hTB : TBFrame R)
    (Positive : Property W Ind → Prop)
    (hA1 : A1R Positive) (hA5 : A5R R Positive)
    {w : W}
    (hPos : possibleR R (fun v => ∃ x : Ind, GodLike Positive v x) w) :
    necessaryR R (fun v => ∃ y : Ind, GodLike Positive v y) w :=
  local_T3_of_Symmetric R hTB.symmetric Positive hA1 hA5 hPos

/-- Under symmetry alone: local possibility of God ⇒ God at `w`
(back-edge from the witness, no reflexivity required). -/
theorem local_exists_God_of_Symmetric {W Ind : Type} (R : Access W)
    (hSym : Symmetric R)
    (Positive : Property W Ind → Prop)
    (hA1 : A1R Positive) (hA5 : A5R R Positive)
    {w : W}
    (hPos : possibleR R (fun v => ∃ x : Ind, GodLike Positive v x) w) :
    ∃ x : Ind, GodLike Positive w x := by
  obtain ⟨v, hRv, hEx⟩ := hPos
  have hNecAtV :
      necessaryR R (fun u => ∃ y : Ind, GodLike Positive u y) v :=
    exists_God_implies_necessaryR R Positive hA1 hA5 hEx
  exact hNecAtV w (hSym w v hRv)

/-- Under **S5Frame**, local T3 — recovered as a corollary of symmetry
(`S5Frame.symmetric`). The older euclidean/cluster proof is subsumed. -/
theorem local_T3_of_S5 {W Ind : Type} (R : Access W)
    (hS5 : S5Frame R)
    (Positive : Property W Ind → Prop)
    (hA1 : A1R Positive) (hA5 : A5R R Positive)
    {w : W}
    (hPos : possibleR R (fun v => ∃ x : Ind, GodLike Positive v x) w) :
    necessaryR R (fun v => ∃ y : Ind, GodLike Positive v y) w :=
  local_T3_of_Symmetric R hS5.symmetric Positive hA1 hA5 hPos

/-- Corollary: under S5, local possibility of God ⇒ God at `w`. -/
theorem local_exists_God_of_S5 {W Ind : Type} (R : Access W)
    (hS5 : S5Frame R)
    (Positive : Property W Ind → Prop)
    (hA1 : A1R Positive) (hA5 : A5R R Positive)
    {w : W}
    (hPos : possibleR R (fun v => ∃ x : Ind, GodLike Positive v x) w) :
    ∃ x : Ind, GodLike Positive w x :=
  local_exists_God_of_Symmetric R hS5.symmetric Positive hA1 hA5 hPos

/-! ## Global T3 requires Universal R (stronger than S5Frame) -/

/-- Under **Universal R**, recover global T3 (`∀w ∃x GodLike`).
`Universal R` is in the theorem type — not smuggled via encoding. -/
theorem T3R_necessarily_God_of_universal {W Ind : Type} (R : Access W)
    (hU : Universal R)
    (Positive : Property W Ind → Prop)
    (hA1 : A1R Positive) (hA2 : A2R Positive)
    (hA3 : A3R Positive) (hA5 : A5R R Positive) :
    ∀ w : W, ∃ x : Ind, GodLike Positive w x := by
  obtain ⟨w0, hEx⟩ := CR_possibly_God Positive hA1 hA2 hA3
  have hNec :
      necessaryR R (fun v => ∃ y : Ind, GodLike Positive v y) w0 :=
    exists_God_implies_necessaryR R Positive hA1 hA5 hEx
  intro w
  exact hNec w (hU w0 w)

/-- Same conclusion packaged as `necessaryR` at an arbitrary world. -/
theorem T3R_box_exists_God_of_universal {W Ind : Type} (R : Access W)
    (hU : Universal R)
    (Positive : Property W Ind → Prop)
    (hA1 : A1R Positive) (hA2 : A2R Positive)
    (hA3 : A3R Positive) (hA5 : A5R R Positive)
    (w : W) :
    necessaryR R (fun v => ∃ x : Ind, GodLike Positive v x) w := by
  intro v hv
  exact T3R_necessarily_God_of_universal R hU Positive hA1 hA2 hA3 hA5 v

/-- Specialization: universal relation recovers the `Scott.lean` reading. -/
theorem T3_recover_universalRel {W Ind : Type}
    (Positive : Property W Ind → Prop)
    (hA1 : A1R Positive) (hA2 : A2R Positive)
    (hA3 : A3R Positive) (hA5 : A5R (universalRel W) Positive) :
    □ (fun w : W => ∃ x : Ind, GodLike Positive w x) :=
  T3R_necessarily_God_of_universal (universalRel W)
    (universalRel_is_universal W) Positive hA1 hA2 hA3 hA5

/-! ## Obstruction: S5Frame alone does not give global T3

See `Countermodel.lean` for a concrete finite frame where `S5Frame R` holds,
A1–A5 hold, local T3 holds in the God-cluster, but `∀w ∃x GodLike w x` fails.
The lemma below records the proof-theoretic gap: global C + local reflection
only force God on the `R`-successors of the witness world.
-/

/-- **Obstruction lemma.** From global C and local reflection one obtains God
only on successors of the witness — not at arbitrary worlds — unless those
worlds are `R`-reachable from the witness (e.g. by `Universal R`). -/
theorem obstruction_reflection_only_reaches_successors
    {W Ind : Type} (R : Access W)
    (Positive : Property W Ind → Prop)
    (hA1 : A1R Positive) (hA5 : A5R R Positive)
    {w0 : W} (hEx : ∃ x : Ind, GodLike Positive w0 x) :
    ∀ v : W, R w0 v → ∃ y : Ind, GodLike Positive v y :=
  exists_God_implies_necessaryR R Positive hA1 hA5 hEx

end GodelOntological
