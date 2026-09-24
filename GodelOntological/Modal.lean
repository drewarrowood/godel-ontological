/-
# Lightweight S5 modal encoding

Possible worlds with **universal accessibility** (every world sees every world).
That is a valid S5 frame: □ is `∀ w, …` and ◇ is `∃ w, …`.

This is intentionally thin — enough to state Gödel/Scott modal claims in ordinary
Lean 4, without a full HOML embedding.
-/

namespace GodelOntological

/-- Necessity on a world-proposition: true at every world. -/
def necessary {W : Type} (φ : W → Prop) : Prop :=
  ∀ w : W, φ w

/-- Possibility on a world-proposition: true at some world. -/
def possible {W : Type} (φ : W → Prop) : Prop :=
  ∃ w : W, φ w

/-- Box notation for necessity. -/
prefix:max "□" => necessary

/-- Diamond notation for possibility. -/
prefix:max "◇" => possible

/-- A property of individuals, evaluated relative to a world (intension). -/
abbrev Property (W Ind : Type) := W → Ind → Prop

/-- Negation of a property (pointwise). -/
def propNeg {W Ind : Type} (φ : Property W Ind) : Property W Ind :=
  fun w x => ¬ φ w x

/-- The unsatisfiable property. -/
def propFalse {W Ind : Type} : Property W Ind :=
  fun _ _ => False

/-- The universal (always-true) property. -/
def propTrue {W Ind : Type} : Property W Ind :=
  fun _ _ => True

/-- Necessary entailment: □∀x (φ(x) → ψ(x)), under universal accessibility. -/
def necEntails {W Ind : Type} (φ ψ : Property W Ind) : Prop :=
  ∀ w : W, ∀ x : Ind, φ w x → ψ w x

theorem necEntails_false_of_nowhere {W Ind : Type} (φ : Property W Ind)
    (h : ∀ w : W, ∀ x : Ind, ¬ φ w x) :
    necEntails φ (propFalse : Property W Ind) := by
  intro w x hφ
  exact (h w x) hφ

theorem necEntails_true {W Ind : Type} (φ : Property W Ind) :
    necEntails φ (propTrue : Property W Ind) := by
  intro _ _ _; trivial

@[simp] theorem propNeg_true {W Ind : Type} :
    propNeg (propTrue : Property W Ind) = propFalse := by
  funext w x; simp [propNeg, propTrue, propFalse]

end GodelOntological
