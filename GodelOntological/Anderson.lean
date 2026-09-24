import GodelOntological.Scott
import GodelOntological.Collapse

/-
# Anderson’s emendation (thin universal-frame check)

## Literature cut (before the Lean claim)

Anderson, “Some Emendations of Gödel’s Ontological Proof”, *Faith and
Philosophy* 7(3), 1990, pp. 291–303. As recorded by Kanckos & Woltzenlogel Paleo
(*Studia Logica* 105(3), 2017, DOI 10.1007/s11225-016-9700-1, §7):

* **A1, one direction only:** `P(¬φ) → ¬P(φ)`.
* **D1:** `G(x) ↔ ∀φ (P(φ) ↔ □ φ(x))` — necessarily possesses exactly the
  positive properties.
* **A2, A3** as in Scott (`P(G)`).
* Hájek: A4, A5, and the emended essence / necessary-existence definitions are
  not needed for Theorem 3. §7.1 confirms that; §7.2 explains why the Scott
  collapse derivation becomes `□A → □A` after the extra box in essence.

Benzmüller & Fuenmayor (arXiv:1910.08955; BSL 49(2), 2020,
DOI 10.18778/0138-0680.2020.08): Anderson’s variant avoids modal collapse;
Fitting’s does too, by taking positivity of **extensions**. This file
formalizes **Anderson 1990**, not Fitting.

## What is checked here

Rigid `Positive : Property → Prop` on the universal frame (`□` = `∀` worlds),
same modal layer as `Scott.lean`. Not WRP.

* Fragment: half-A1 + A2 + A3 + Anderson D1 ⇒ `□ ∃ GodLikeA`
  (`T3A_necessarily_God`). Essence and A5 are not hypotheses.
* Desk witness that this fragment does **not** entail Sobel collapse:
  on `Bool` with `universalRel`, `P φ ↔ φ` holds at every world, the fragment
  holds, God exists at both worlds, and `(· = false)` is `ContingentR`
  (`anderson_fragment_ContingentR_survives`). Scott’s full A1 fails on that
  same `P`.

**Status:** the avoidance of collapse is a **rediscovery** of Anderson’s
emendation. The finite Bool table is **desk packaging** in this thin encoding.
Not a priority claim. Not a Fitting formalization.
-/

namespace GodelOntological
namespace Anderson

/-- **Anderson A1 (half).** If the negation is positive, the property is not. -/
def A1A {W Ind : Type} (Positive : Property W Ind → Prop) : Prop :=
  ∀ φ : Property W Ind, Positive (propNeg φ) → ¬ Positive φ

/-- **Anderson D1.** God-like: the positive properties are exactly those the
individual has necessarily (`□` = every world). -/
def GodLikeA {W Ind : Type} (Positive : Property W Ind → Prop) : Property W Ind :=
  fun _w x => ∀ φ : Property W Ind, Positive φ ↔ □ (fun v => φ v x)

/-- **A3 for Anderson D1.** Being God-like (in Anderson’s sense) is positive. -/
def A3A {W Ind : Type} (Positive : Property W Ind → Prop) : Prop :=
  Positive (GodLikeA Positive)

/-! ## Fragment: half-A1 + A2 + A3 ⇒ □∃ GodLikeA -/

theorem positive_propTrue_A {W Ind : Type} (Positive : Property W Ind → Prop)
    (hA2 : A2 Positive) {φ : Property W Ind} (hφ : Positive φ) :
    Positive (propTrue : Property W Ind) :=
  hA2 φ propTrue hφ (necEntails_true φ)

/-- **T1 (Anderson).** Uses only `P(¬φ) → ¬P(φ)`, not Scott’s converse. -/
theorem T1A_positive_possibly_exemplified {W Ind : Type}
    (Positive : Property W Ind → Prop)
    (hA1 : A1A Positive) (hA2 : A2 Positive)
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
    hA1 propTrue hNegTrue
  exact hNotTrue (positive_propTrue_A Positive hA2 hP)

/-- **C (Anderson).** Possibly a God-like being, from half-A1, A2, and A3. -/
theorem CA_possibly_God {W Ind : Type} (Positive : Property W Ind → Prop)
    (hA1 : A1A Positive) (hA2 : A2 Positive) (hA3 : A3A Positive) :
    ◇ (fun w : W => ∃ x : Ind, GodLikeA Positive w x) :=
  T1A_positive_possibly_exemplified Positive hA1 hA2 (GodLikeA Positive) hA3

/-- From Anderson D1 + A3: a God-like individual is God-like at every world.
Essence and A5 are not used. -/
theorem box_GodLikeA_of_God {W Ind : Type} (Positive : Property W Ind → Prop)
    (hA3 : A3A Positive) {w : W} {x : Ind}
    (hg : GodLikeA Positive w x) :
    □ (fun v : W => GodLikeA Positive v x) :=
  (hg (GodLikeA Positive)).mp hA3

theorem exists_God_implies_necessaryA {W Ind : Type}
    (Positive : Property W Ind → Prop) (hA3 : A3A Positive)
    {w : W} (hEx : ∃ x : Ind, GodLikeA Positive w x) :
    □ (fun v : W => ∃ y : Ind, GodLikeA Positive v y) := by
  obtain ⟨x, hx⟩ := hEx
  intro v
  exact ⟨x, box_GodLikeA_of_God Positive hA3 hx v⟩

/-- **T3 (Anderson fragment).** `□ ∃ GodLikeA` from half-A1, A2, and A3.
Hájek’s redundancy of A4/A5, checked in this universal-frame encoding. -/
theorem T3A_necessarily_God {W Ind : Type} (Positive : Property W Ind → Prop)
    (hA1 : A1A Positive) (hA2 : A2 Positive) (hA3 : A3A Positive) :
    □ (fun w : W => ∃ x : Ind, GodLikeA Positive w x) := by
  obtain ⟨w, hEx⟩ := CA_possibly_God Positive hA1 hA2 hA3
  exact exists_God_implies_necessaryA Positive hA3 hEx

/-! ## Bool witness: fragment holds, ContingentR survives -/

/-- Positive iff true of `()` at every world. -/
def P_all : Property Bool Unit → Prop :=
  fun φ => ∀ w : Bool, φ w ()

theorem P_all_A1A : A1A P_all := by
  intro φ hNeg hPos
  exact hNeg false (hPos false)

theorem P_all_A2 : A2 P_all := by
  intro φ ψ hP hEnt w
  exact hEnt w () (hP w)

theorem P_all_GodLike (w : Bool) (x : Unit) : GodLikeA P_all w x := by
  cases x
  intro φ
  constructor
  · intro hAll v
    exact hAll v
  · intro hBox v
    exact hBox v

theorem P_all_A3 : A3A P_all := by
  intro w
  exact P_all_GodLike w ()

/-- Scott’s biconditional A1 fails: a world-dependent property and its
negation are both non-positive. -/
theorem P_all_not_Scott_A1 : ¬ A1 P_all := by
  intro hA1
  let φ : Property Bool Unit := fun w _ => w = false
  have hNot : ¬ P_all φ := by
    intro hAll
    have : true = false := hAll true
    exact Bool.noConfusion this
  have hNeg : P_all (propNeg φ) := (hA1 φ).mpr hNot
  have : ¬ (false = false) := by
    simpa [propNeg, φ] using hNeg false
  exact this rfl

theorem P_all_Contingent_at_false :
    ContingentR (universalRel Bool) (fun w => w = false) false := by
  refine ⟨rfl, ⟨true, ?_, ?_⟩⟩
  · simp [universalRel]
  · intro h
    exact Bool.noConfusion h

theorem P_all_not_collapse_at_false :
    ¬ ModalCollapseAt (universalRel Bool) false := by
  intro hMC
  exact ContingentR_impossible_of_collapseAt (universalRel Bool) hMC
    (fun w => w = false) P_all_Contingent_at_false

/-- **Desk witness.** Anderson’s fragment (half-A1, A2, A3, D1) holds on a
two-world universal frame, `□∃ GodLikeA` holds, and `(· = false)` is contingent.
Sobel collapse does not follow. Scott’s full A1 does not hold of this `P`. -/
theorem anderson_fragment_ContingentR_survives :
    A1A P_all ∧ A2 P_all ∧ A3A P_all ∧
    □ (fun w : Bool => ∃ x : Unit, GodLikeA P_all w x) ∧
    ContingentR (universalRel Bool) (fun w => w = false) false ∧
    ¬ ModalCollapseAt (universalRel Bool) false ∧
    ¬ ModalCollapse (W := Bool) ∧
    ¬ A1 P_all := by
  refine ⟨P_all_A1A, P_all_A2, P_all_A3,
    T3A_necessarily_God P_all P_all_A1A P_all_A2 P_all_A3,
    P_all_Contingent_at_false, P_all_not_collapse_at_false, ?_, P_all_not_Scott_A1⟩
  intro hMC
  have : true = false := hMC (fun w => w = false) false rfl true
  exact Bool.noConfusion this

end Anderson
end GodelOntological
