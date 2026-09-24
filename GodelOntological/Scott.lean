import GodelOntological.Modal

/-
# Scott’s emendation of Gödel’s ontological argument (thin Lean 4 encoding)

We formalize the **Scott-consistent** axiom set and prove the standard chain
through `□ ∃x G(x)` under a universal-frame S5 reading.

Honesty clause: Lean checks that the conclusion follows from the named axioms
in this encoding. That is not a metaphysical demonstration that God exists; it
is a formal implication.
-/

namespace GodelOntological

/-! ## Definitions (Scott / Gödel notes) -/

/-- **D1.** God-like: possesses every positive property (at that world).

`Positive` is treated as **rigid** (not world-relative). Under that reading,
Scott’s A4 (`P(φ) → □P(φ)`) holds definitionally and is omitted as a separate
hypothesis — see README / NOTES. -/
def GodLike {W Ind : Type} (Positive : Property W Ind → Prop) : Property W Ind :=
  fun w x => ∀ φ : Property W Ind, Positive φ → φ w x

/-- **D2.** Essence: φ is an essence of x at w when x has φ at w and φ
necessarily entails every property that x has at w. -/
def Essence {W Ind : Type} (φ : Property W Ind) (w : W) (x : Ind) : Prop :=
  φ w x ∧ ∀ ψ : Property W Ind, ψ w x → □ (fun v => ∀ y : Ind, φ v y → ψ v y)

/-- **D3.** Necessary existence: every essence of x is necessarily exemplified. -/
def NE {W Ind : Type} : Property W Ind :=
  fun w x => ∀ φ : Property W Ind, Essence φ w x → □ (fun v => ∃ y : Ind, φ v y)

/-! ## Scott axioms as propositions (assumptions, not ambient `axiom`s) -/

/-- **A1.** A property is positive iff its negation is not.
(Scott’s exclusive/exhaustive positivity for complements.) -/
def A1 {W Ind : Type} (Positive : Property W Ind → Prop) : Prop :=
  ∀ φ : Property W Ind, Positive (propNeg φ) ↔ ¬ Positive φ

/-- **A2.** Whatever is necessarily entailed by a positive property is positive. -/
def A2 {W Ind : Type} (Positive : Property W Ind → Prop) : Prop :=
  ∀ φ ψ : Property W Ind, Positive φ → necEntails φ ψ → Positive ψ

/-- **A3.** Being God-like is positive. (Scott’s repair / naming of Gödel’s idea.) -/
def A3 {W Ind : Type} (Positive : Property W Ind → Prop) : Prop :=
  Positive (GodLike Positive)

/-- **A5.** Necessary existence is positive. (Scott’s key consistency repair.) -/
def A5 {W Ind : Type} (Positive : Property W Ind → Prop) : Prop :=
  Positive (NE : Property W Ind)

/-! ## Derived facts and the theorem chain -/

/-- From A2: the universal property is positive whenever anything is. -/
theorem positive_propTrue {W Ind : Type} (Positive : Property W Ind → Prop)
    (hA2 : A2 Positive) {φ : Property W Ind} (hφ : Positive φ) :
    Positive (propTrue : Property W Ind) :=
  hA2 φ propTrue hφ (necEntails_true φ)

/-- **T1.** Positive properties are possibly exemplified. -/
theorem T1_positive_possibly_exemplified {W Ind : Type}
    (Positive : Property W Ind → Prop)
    (hA1 : A1 Positive) (hA2 : A2 Positive)
    (φ : Property W Ind) (hP : Positive φ) :
    ◇ (fun w : W => ∃ x : Ind, φ w x) := by
  apply Classical.byContradiction
  intro h
  have nowhere : ∀ (w : W) (x : Ind), ¬ φ w x := by
    intro w x hx
    exact h ⟨w, x, hx⟩
  have hFalse : Positive (propFalse : Property W Ind) :=
    hA2 φ propFalse hP (necEntails_false_of_nowhere φ nowhere)
  have hNegTrue : Positive (propNeg (propTrue : Property W Ind)) := by
    rw [propNeg_true]; exact hFalse
  have hNotTrue : ¬ Positive (propTrue : Property W Ind) :=
    (hA1 propTrue).mp hNegTrue
  have hTrue : Positive (propTrue : Property W Ind) :=
    positive_propTrue Positive hA2 hP
  exact hNotTrue hTrue

/-- **Corollary (C).** Possibly, a God-like being exists. -/
theorem C_possibly_God {W Ind : Type} (Positive : Property W Ind → Prop)
    (hA1 : A1 Positive) (hA2 : A2 Positive) (hA3 : A3 Positive) :
    ◇ (fun w : W => ∃ x : Ind, GodLike Positive w x) :=
  T1_positive_possibly_exemplified Positive hA1 hA2 (GodLike Positive) hA3

/-- Auxiliary: if x is God-like at w and has ψ at w, then ψ is positive. -/
theorem godlike_has_only_positive {W Ind : Type}
    (Positive : Property W Ind → Prop) (hA1 : A1 Positive)
    {w : W} {x : Ind} {ψ : Property W Ind}
    (hg : GodLike Positive w x) (hψ : ψ w x) :
    Positive ψ := by
  apply Classical.byContradiction
  intro hNot
  have hNeg : Positive (propNeg ψ) := (hA1 ψ).mpr hNot
  have : propNeg ψ w x := hg (propNeg ψ) hNeg
  exact this hψ

/-- **T2.** Being God-like is an essence of any God-like being.

Uses A1. (A4 is absorbed by rigidity of `Positive`.) -/
theorem T2_godlike_essence {W Ind : Type}
    (Positive : Property W Ind → Prop) (hA1 : A1 Positive)
    {w : W} {x : Ind} (hg : GodLike Positive w x) :
    Essence (GodLike Positive) w x := by
  refine ⟨hg, ?_⟩
  intro ψ hψ
  have hPos : Positive ψ := godlike_has_only_positive Positive hA1 hg hψ
  intro v y hy
  exact hy ψ hPos

/-- From God-likeness + A5: a God-like being has necessary existence. -/
theorem godlike_has_NE {W Ind : Type}
    (Positive : Property W Ind → Prop) (hA5 : A5 Positive)
    {w : W} {x : Ind} (hg : GodLike Positive w x) :
    NE w x :=
  hg NE hA5

/-- Local reflection: existence of a God-like being at `w` implies necessary
existence of a God-like being (under A1+A5). -/
theorem exists_God_implies_necessary {W Ind : Type}
    (Positive : Property W Ind → Prop)
    (hA1 : A1 Positive) (hA5 : A5 Positive)
    {w : W} (hEx : ∃ x : Ind, GodLike Positive w x) :
    □ (fun v : W => ∃ y : Ind, GodLike Positive v y) := by
  obtain ⟨x, hx⟩ := hEx
  have hEss : Essence (GodLike Positive) w x := T2_godlike_essence Positive hA1 hx
  have hNE : NE w x := godlike_has_NE Positive hA5 hx
  exact hNE (GodLike Positive) hEss

/-- **T3.** Necessarily, there exists a God-like being.

Assumes A1–A3 and A5 (A4 absorbed by rigid positivity). Under universal-frame
S5, possibility of God plus the reflection lemma yields necessity. -/
theorem T3_necessarily_God {W Ind : Type}
    (Positive : Property W Ind → Prop)
    (hA1 : A1 Positive) (hA2 : A2 Positive) (hA3 : A3 Positive) (hA5 : A5 Positive) :
    □ (fun w : W => ∃ x : Ind, GodLike Positive w x) := by
  obtain ⟨w0, hEx⟩ := C_possibly_God Positive hA1 hA2 hA3
  exact exists_God_implies_necessary Positive hA1 hA5 hEx

/-- Weaker non-modal corollary at an arbitrary world (from T3). -/
theorem exists_God_at_every_world {W Ind : Type}
    (Positive : Property W Ind → Prop)
    (hA1 : A1 Positive) (hA2 : A2 Positive) (hA3 : A3 Positive) (hA5 : A5 Positive)
    (w : W) :
    ∃ x : Ind, GodLike Positive w x :=
  T3_necessarily_God Positive hA1 hA2 hA3 hA5 w

end GodelOntological
