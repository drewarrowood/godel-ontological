import GodelOntological.Actualist

/-
# Hunt 6 — Ax1Gen without the source/successor split

The literal axiom is `⌊(PosProps Φ ∧ ConjOfPropsFrom φ Φ) ⊃ P φ⌋`.
`PosProps` is read at the source; `ConjOfPropsFrom` reads `Φ` under a box.
`fig7_implies_symmetric` uses a `Φ` that is empty at the source and non-empty
at other worlds. This file keeps every other Fig. 7 ingredient and replaces
only that axiom, in two ways:

* **R1.** Positivity of the conjuncts is required at the same worlds as the
  conjunction identity. `□(PosProps ∧ biconditional)` and
  `(□ PosProps ∧ ConjOfPropsFrom)` are equivalent in K; both are stated.
* **R2.** `Φ` is restricted to world-invariant collections. `PosProps` and
  `ConjOfPropsFrom` stay literal.

See `ACTUALIST_FIG7.md`, Hunt 6.
-/

namespace GodelOntological.Actualist.Repaired

open GodelOntological.Actualist

/-! ## R1: positivity under the same box as the conjunction -/

/-- The actualist biconditional inside `ConjOfPropsFrom`, without the box. -/
def bicondAt {W Ind : Type} (ex : Ind → W → Prop) (φ : MProp W Ind)
    (Φ : MPred W Ind) : WorldProp W :=
  allAct ex (fun z u => φ z u ↔ ∀ ψ, Φ ψ u → ψ z u)

/-- **R1, split form.** `⌊(□ PosProps Φ ∧ ConjOfPropsFrom φ Φ) ⊃ P φ⌋`. -/
def Ax1GenBox {W Ind : Type} (R : Access W) (ex : Ind → W → Prop)
    (P : MPred W Ind) : Prop :=
  ∀ (Φ : MPred W Ind) (φ : MProp W Ind),
    valid (fun w => box R (posProps P Φ) w → conjOfPropsFrom R ex φ Φ w → P φ w)

/-- **R1, joint form.** `⌊□(PosProps Φ ∧ ∀^E z. φ z ↔ (∀ψ. Φ ψ ⊃ ψ z)) ⊃ P φ⌋`.
This is the reading closer to Gödel’s footnote: at each accessible world the
properties `Φ` marks are positive there, and `φ` is their conjunction there. -/
def Ax1GenInBox {W Ind : Type} (R : Access W) (ex : Ind → W → Prop)
    (P : MPred W Ind) : Prop :=
  ∀ (Φ : MPred W Ind) (φ : MProp W Ind),
    valid (fun w =>
      box R (fun v => posProps P Φ v ∧ bicondAt ex φ Φ v) w → P φ w)

/-- In K, `□A ∧ □B` is `□(A ∧ B)`, and `ConjOfPropsFrom` is already a box.
The two R1 statements do not differ. -/
theorem ax1GenBox_iff_inBox {W Ind : Type} (R : Access W) (ex : Ind → W → Prop)
    (P : MPred W Ind) :
    Ax1GenBox R ex P ↔ Ax1GenInBox R ex P := by
  constructor
  · intro h Φ φ w hBoth
    exact h Φ φ w (fun v hv => (hBoth v hv).1) (fun v hv => (hBoth v hv).2)
  · intro h Φ φ w hPos hConj
    exact h Φ φ w (fun v hv => ⟨hPos v hv, hConj v hv⟩)

/-- **Lemma L** from boxed Ax1Gen alone. `Φ := P` is positive at every world,
so the extra box is vacuous. -/
theorem lemma_L_box {W Ind : Type} {R : Access W} {ex : Ind → W → Prop}
    {P : MPred W Ind} (hGen : Ax1GenBox R ex P) :
    valid (P (god P)) := by
  intro w
  refine hGen (fun φ => P φ) (god P) w ?_ ?_
  · intro _v _hv φ hP
    exact hP
  · intro _v _hv _z _hz
    constructor
    · intro hG ψ hP
      exact hG ψ hP
    · intro hAll ψ hP
      exact hAll ψ hP

theorem lemma_L_inBox {W Ind : Type} {R : Access W} {ex : Ind → W → Prop}
    {P : MPred W Ind} (hGen : Ax1GenInBox R ex P) :
    valid (P (god P)) :=
  lemma_L_box ((ax1GenBox_iff_inBox R ex P).mpr hGen)

/-! ## R2: rigid collections of properties -/

/-- `Φ` does not depend on the world. -/
def Rigid {W Ind : Type} (Φ : MPred W Ind) : Prop :=
  ∀ ψ w v, Φ ψ w ↔ Φ ψ v

/-- **R2.** Literal `PosProps` and `ConjOfPropsFrom`, but `Φ` is rigid. -/
def Ax1GenRigid {W Ind : Type} (R : Access W) (ex : Ind → W → Prop)
    (P : MPred W Ind) : Prop :=
  ∀ (Φ : MPred W Ind), Rigid Φ → ∀ φ,
    valid (fun w => posProps P Φ w → conjOfPropsFrom R ex φ Φ w → P φ w)

/-- Along an edge, Ax2a and Ax2b make positivity agree in both directions. -/
theorem pos_agree {W Ind : Type} {R : Access W} {P : MPred W Ind}
    (h2a : Ax2a P) (h2b : Ax2b R P) {w v : W} (hwv : R w v) (ψ : MProp W Ind) :
    P ψ w ↔ P ψ v := by
  constructor
  · intro h
    exact h2b ψ w h v hwv
  · intro hPv
    cases (h2a ψ w).1 with
    | inl hPw => exact hPw
    | inr hNegW =>
      exact False.elim ((h2a ψ v).2 ⟨hPv, h2b (negPred ψ) w hNegW v hwv⟩)

/-- **Lemma L** for rigid `Φ`. The snapshot `Φ ψ _ := P ψ w` is rigid.
Ax2a and Ax2b make that snapshot agree with `P` at successors, so the
conjunction is still `G`. Literal `lemma_L` did not need Ax2a or Ax2b. -/
theorem lemma_L_rigid {W Ind : Type} {R : Access W} {ex : Ind → W → Prop}
    {P : MPred W Ind}
    (hGen : Ax1GenRigid R ex P) (h2a : Ax2a P) (h2b : Ax2b R P) :
    valid (P (god P)) := by
  intro w
  let Φ : MPred W Ind := fun ψ _ => P ψ w
  have hRigid : Rigid Φ := fun _ψ _u _v => Iff.rfl
  refine hGen Φ hRigid (god P) w ?_ ?_
  · intro _φ hP
    exact hP
  · intro v hv z _hz
    constructor
    · intro hG ψ hΦ
      exact hG ψ ((pos_agree h2a h2b hv ψ).mp hΦ)
    · intro hAll ψ hPv
      exact hAll ψ ((pos_agree h2a h2b hv ψ).mpr hPv)

/-! ## S4 chain countermodel for both repairs

Worlds `false` (source) and `true` (sink). `R_chain` is reflexive and
transitive, not symmetric. One individual, existing at both worlds.
`P φ` holds at either world iff `φ` holds of that individual at the sink.
God-like at the sink only, so `◇∃^E G` holds at the source and `□∃^E G` fails.
-/

def chainEx : Unit → Bool → Prop := fun _ _ => True

/-- Principal at the sink: positive iff true of `()` at `true`. -/
def chainP : MPred Bool Unit := fun φ _ => φ () true

theorem chain_god_sink : god chainP () true :=
  fun _ hP => hP

theorem chain_not_god_source : ¬ god chainP () false := by
  intro hG
  let φ : MProp Bool Unit := fun _ u => u = true
  have hP : chainP φ false := rfl
  exact Bool.false_ne_true (hG φ hP)

theorem chain_ax1 : Ax1 chainP := by
  intro φ ψ _ hφ hψ
  exact ⟨hφ, hψ⟩

theorem chain_ax2a : Ax2a chainP := by
  intro φ w
  cases w <;>
    exact ⟨Classical.em (φ () true), fun h => h.2 h.1⟩

theorem chain_ax2b : Ax2b R_chain chainP := by
  intro _φ _w hφ _v _hv
  exact hφ

theorem chain_ax4 : Ax4 R_chain chainEx chainP := by
  intro φ ψ w hφ hN
  cases w
  · exact hN true trivial () trivial hφ
  · exact hN true rfl () trivial hφ

theorem chain_ax3 : Ax3 R_chain chainEx chainP := by
  -- `chainP` reads extensions only at the sink, so Ax3 is `necExist` at `true`.
  intro _w φ hEss v hv
  subst hv
  exact ⟨(), trivial, hEss.1⟩

theorem chain_ax1GenBox : Ax1GenBox R_chain chainEx chainP := by
  intro Φ φ w _hPos hConj
  cases w
  · exact (hConj true trivial () trivial).mpr (fun ψ hΦ => _hPos true trivial ψ hΦ)
  · exact (hConj true rfl () trivial).mpr (fun ψ hΦ => _hPos true rfl ψ hΦ)

theorem chain_ax1GenInBox : Ax1GenInBox R_chain chainEx chainP :=
  (ax1GenBox_iff_inBox R_chain chainEx chainP).mp chain_ax1GenBox

theorem chain_ax1GenRigid : Ax1GenRigid R_chain chainEx chainP := by
  intro Φ hRigid φ w hPos hConj
  have hIff :=
    hConj true (by cases w <;> trivial) () trivial
  exact hIff.mpr (fun ψ hΦt => hPos ψ ((hRigid ψ true w).mp hΦt))

/-- At the source: an existent God is possible, and not necessary. -/
theorem chain_th3_fails_at_source :
    dia R_chain (exAct chainEx (god chainP)) false ∧
      ¬ box R_chain (exAct chainEx (god chainP)) false := by
  refine ⟨⟨true, trivial, (), trivial, chain_god_sink⟩, ?_⟩
  intro hBox
  rcases hBox false trivial with ⟨_, _, hG⟩
  exact chain_not_god_source hG

theorem chain_not_Th3 : ¬ Th3 R_chain chainEx chainP := by
  intro hTh
  exact chain_th3_fails_at_source.2 (hTh false chain_th3_fails_at_source.1)

/-- This `P` is not a model of literal Ax1Gen. The repairs are strictly weaker
on this frame: Hunt 5 already rules the literal axiom out on `R_chain`. -/
theorem chain_not_literal_Ax1Gen : ¬ Ax1Gen R_chain chainEx chainP := by
  intro hGen
  exact fig7_unsat_on_S4_chain chainEx chainP hGen chain_ax2a chain_ax2b chain_ax4

/-- **R1 countermodel.** S4 chain, all Fig. 7 axioms with boxed Ax1Gen
(split form; the joint form is `chain_ax1GenInBox`), Th3 false at `false`. -/
theorem r1_s4_countermodel :
    Reflexive R_chain ∧ Transitive R_chain ∧ ¬ Symmetric R_chain ∧
      Ax1 chainP ∧ Ax2a chainP ∧ Ax2b R_chain chainP ∧
      Ax3 R_chain chainEx chainP ∧ Ax4 R_chain chainEx chainP ∧
      Ax1GenBox R_chain chainEx chainP ∧ Ax1GenInBox R_chain chainEx chainP ∧
      ¬ Th3 R_chain chainEx chainP :=
  ⟨R_chain_reflexive, R_chain_transitive, R_chain_not_symmetric,
    chain_ax1, chain_ax2a, chain_ax2b, chain_ax3, chain_ax4,
    chain_ax1GenBox, chain_ax1GenInBox, chain_not_Th3⟩

/-- **R2 countermodel.** Same frame and the same `P`. Literal `PosProps` /
`ConjOfPropsFrom`, with `Φ` restricted to rigid collections. -/
theorem r2_s4_countermodel :
    Reflexive R_chain ∧ Transitive R_chain ∧ ¬ Symmetric R_chain ∧
      Ax1 chainP ∧ Ax2a chainP ∧ Ax2b R_chain chainP ∧
      Ax3 R_chain chainEx chainP ∧ Ax4 R_chain chainEx chainP ∧
      Ax1GenRigid R_chain chainEx chainP ∧
      ¬ Th3 R_chain chainEx chainP :=
  ⟨R_chain_reflexive, R_chain_transitive, R_chain_not_symmetric,
    chain_ax1, chain_ax2a, chain_ax2b, chain_ax3, chain_ax4,
    chain_ax1GenRigid, chain_not_Th3⟩

end GodelOntological.Actualist.Repaired
