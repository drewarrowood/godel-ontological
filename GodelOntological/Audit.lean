import GodelOntological.Actualist_Repaired

/-
# Audit of literal Fig. 7

The literal AFP Ax1Gen, with Ax2a, Ax2b, and Ax4, derives symmetry, and also
reflexivity and the B schema. Adding Ax3 forces `R` to be the identity, and
modal collapse follows from that derived symmetry. `Rsymm` is not a hypothesis.
Full comprehension here is unrestricted quantification over properties.

`GoedelVariantHOML2` already proves `lemma MC` from Ax2a, Ax2b, Th5, and an
assumed `Rsymm`. These lemmas do not assume `Rsymm`.

The two repairs in `Actualist_Repaired.lean` are not restated here.
`literal_to_R1` and `literal_to_R2` record the one direction that was proved:
literal Ax1Gen implies the boxed reading on reflexive frames, and implies the
world-invariant reading on every frame.
-/

open GodelOntological GodelOntological.Actualist GodelOntological.Actualist.Repaired

namespace GodelOntological.Audit

variable {W Ind : Type} {R : Access W} {ex : Ind → W → Prop} {P : MPred W Ind}

/-- Literal Ax1Gen alone: any property true of every existent at `w`
    (only required when `R w w`) is positive at `w`. Empty-at-home trick, generalized. -/
theorem pos_of_home (hGen : Ax1Gen R ex P) (φ : MProp W Ind) (w : W)
    (h : R w w → allAct ex φ w) : P φ w := by
  refine hGen (fun ψ u => u ≠ w ∧ ψ = φ) φ w ?_ ?_
  · intro ψ hΦ; exact absurd rfl hΦ.1
  · intro u hu z hz
    by_cases huw : u = w
    · subst huw
      exact ⟨fun _ ψ hΦ => absurd rfl hΦ.1, fun _ => h hu z hz⟩
    · refine ⟨fun hφ ψ hΦ => hΦ.2 ▸ hφ, fun hR => hR φ ⟨huw, rfl⟩⟩

/-- Literal Ax1Gen + Ax2a force reflexivity. -/
theorem refl_of_gen (hGen : Ax1Gen R ex P) (h2a : Ax2a P) : Reflexive R := by
  intro w
  apply Classical.byContradiction; intro hn
  have h1 := pos_of_home hGen botP w (fun h => absurd h hn)
  have h2 := pos_of_home hGen (negPred botP) w (fun h => absurd h hn)
  exact (h2a botP w).2 ⟨h1, h2⟩

/-- Literal Ax1Gen + Ax2a + Ax2b + Ax4 validate the B schema `q → □◇q`
    for every world-proposition `q` (full comprehension). -/
theorem B_schema (hGen : Ax1Gen R ex P) (h2a : Ax2a P) (h2b : Ax2b R P)
    (h4 : Ax4 R ex P) (q : W → Prop) (w : W) (hq : q w) : box R (dia R q) w := by
  intro v hv
  apply Classical.byContradiction; intro hnd
  let φ : MProp W Ind := fun _ u => q u
  have hPw : P φ w := pos_of_home hGen φ w (fun _ _ _ => hq)
  have hPv : P φ v := h2b φ w hPw v hv
  have hI : necImpl R ex φ botP v := fun u hu _ _ hqu => hnd ⟨u, hu, hqu⟩
  have hb : P botP v := h4 φ botP v hPv hI
  have hn : P (negPred botP) v := h4 botP _ v hb (fun _ _ _ _ h => False.elim h)
  exact (h2a botP v).2 ⟨hb, hn⟩

/-- The full literal Fig. 7 package forces `R` to be the identity relation.
Symmetry is not a hypothesis. -/
theorem R_is_identity (hGen : Ax1Gen R ex P) (h2a : Ax2a P) (h2b : Ax2b R P)
    (h3 : Ax3 R ex P) (h4 : Ax4 R ex P) : ∀ w v, R w v ↔ v = w := by
  intro w v
  constructor
  · intro hv
    let φ : MProp W Ind := fun _ u => u = w
    have hPw : P φ w := pos_of_home hGen φ w (fun _ _ _ => rfl)
    have hPv : P φ v := h2b φ w hPw v hv
    obtain ⟨g, _, hg⟩ := th5_fig7 hGen h2a h2b h3 h4 v v (refl_of_gen hGen h2a v)
    exact hg φ hPv
  · intro h; subst h; exact refl_of_gen hGen h2a v

/-- Modal collapse for every world-proposition.
The AFP lemma `MC` in `GoedelVariantHOML2` is the same schema, proved there
from `Rsymm`. This proof does not assume symmetry. -/
theorem MC (hGen : Ax1Gen R ex P) (h2a : Ax2a P) (h2b : Ax2b R P)
    (h3 : Ax3 R ex P) (h4 : Ax4 R ex P) (q : W → Prop) : valid (fun w => q w → box R q w) := by
  intro w hq v hv
  rw [(R_is_identity hGen h2a h2b h3 h4 w v).mp hv]; exact hq

/-- Fig. 8 Th4 (possible existence) from literal Ax1Gen, Ax2a, and lemma L.
The AFP comment on the corresponding script is
`sledgehammer(Ax2a L Ax1Gen) ... Proof found`. -/
theorem th4_fig8 (hGen : Ax1Gen R ex P) (h2a : Ax2a P) :
    valid (dia R (exAct ex (god P))) := by
  intro w
  apply Classical.byContradiction; intro hn
  have hr := refl_of_gen hGen h2a w
  have hneg : P (negPred (god P)) w :=
    pos_of_home hGen _ w (fun _ x hx hg => hn ⟨w, hr, x, hx, hg⟩)
  exact (h2a (god P) w).2 ⟨lemma_L hGen w, hneg⟩

/-- Literal Ax1Gen implies the boxed reading on every reflexive frame. -/
theorem literal_to_R1 (hR : Reflexive R) (hGen : Ax1Gen R ex P) : Ax1GenBox R ex P :=
  fun Φ φ w hB hC => hGen Φ φ w (hB w (hR w)) hC

/-- Literal Ax1Gen implies the world-invariant reading on every frame. -/
theorem literal_to_R2 (hGen : Ax1Gen R ex P) : Ax1GenRigid R ex P :=
  fun Φ _ φ => hGen Φ φ

/-- On a frame whose accessibility is the identity, the boxed reading implies
the literal axiom. -/
theorem R1_to_literal_of_identity (hId : ∀ w v, R w v ↔ v = w)
    (hBox : Ax1GenBox R ex P) : Ax1Gen R ex P :=
  fun Φ φ w hPos hConj =>
    hBox Φ φ w (fun v hv => by
      have hvw : v = w := (hId w v).mp hv
      subst hvw
      exact hPos) hConj

/-- On an identity frame, literal Ax1Gen and the boxed reading are equivalent. -/
theorem literal_iff_R1_of_identity (hId : ∀ w v, R w v ↔ v = w) :
    Ax1Gen R ex P ↔ Ax1GenBox R ex P :=
  ⟨fun hGen => literal_to_R1 (fun w => (hId w w).mpr rfl) hGen,
   R1_to_literal_of_identity hId⟩

/-- If there is only one world, the world-invariant reading implies the literal axiom:
every collection is world-invariant. -/
theorem R2_to_literal_of_one_world (hOne : ∀ w v : W, w = v)
    (hRigid : Ax1GenRigid R ex P) : Ax1Gen R ex P :=
  fun Φ φ =>
    hRigid Φ (fun _ψ w v => by
      cases hOne w v
      exact Iff.rfl) φ

/-- On the one-world identity frame the literal axiom, the boxed reading, and the
world-invariant reading coincide. -/
theorem readings_coincide_on_unit {Ind : Type} {ex : Ind → Unit → Prop}
    {P : MPred Unit Ind} :
    (Ax1Gen (idRel Unit) ex P ↔ Ax1GenBox (idRel Unit) ex P) ∧
      (Ax1Gen (idRel Unit) ex P ↔ Ax1GenRigid (idRel Unit) ex P) := by
  refine ⟨literal_iff_R1_of_identity ?_, ?_⟩
  · intro w v
    cases w
    cases v
    exact Iff.rfl
  · constructor
    · exact literal_to_R2
    · exact R2_to_literal_of_one_world (fun w v => by cases w; cases v; rfl)

/-- Literal Ax1Gen, Ax2a, Ax2b, and Ax4 have no model on `R_chain`
(reflexive, transitive, not symmetric). -/
theorem literal_unsat_on_R_chain {Ind : Type} (ex : Ind → Bool → Prop)
    (P : MPred Bool Ind) (hGen : Ax1Gen R_chain ex P) (h2a : Ax2a P)
    (h2b : Ax2b R_chain P) (h4 : Ax4 R_chain ex P) : False :=
  fig7_unsat_on_S4_chain ex P hGen h2a h2b h4

/-- On the repair model of the chain, necessary existence of a God-like being
is not valid. That model is not a model of literal Ax1Gen. -/
theorem chain_not_necessary_existence :
    ¬ valid (box R_chain (exAct chainEx (god chainP))) :=
  fun h => chain_th3_fails_at_source.2 (h false)

end GodelOntological.Audit
