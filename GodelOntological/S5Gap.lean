import GodelOntological.Actualist
import GodelOntological.Actualist_Repaired
import GodelOntological.Actualist_Two
import GodelOntological.Dagger

/-
# An S5 frame the chain proof does not cross

`chain_fig8_no_gap` pushes a positive property from the source to the sink.
That step needs a forward edge. The two-point discrete frame is S5 and has
no such edge. The chain proof does not run there.

It is not a countermodel to the Fig. 8 + Ax1GenTwo package: the same
predicate that witnesses the gap fails Ax1GenTwo, because Meaning now looks
only at the source and the conjunction can fail at the sink. Symmetry is
not what saves the axiom. The missing edge is what breaks the proof, and
what also lets the roster misalign.
-/

namespace GodelOntological.Actualist.S5Gap

open GodelOntological.Actualist
open GodelOntological.Actualist.Repaired
open GodelOntological.Actualist.TwoConjuncts

def R_disc (w v : Bool) : Prop := w = v

theorem R_disc_s5 : Reflexive R_disc ∧ Symmetric R_disc ∧ Transitive R_disc := by
  refine ⟨?_, ?_, ?_⟩
  · intro w; rfl
  · intro w v h; exact h.symm
  · intro w v u hwv hvu; exact hwv.trans hvu

theorem disc_no_cross : ¬ R_disc false true := by
  intro h
  cases h

/-- The chain predicate still puts a God-like being at the sink only. -/
theorem disc_gap :
    exAct chainEx (god chainP) true ∧ ¬ exAct chainEx (god chainP) false := by
  refine ⟨⟨(), trivial, chain_god_sink⟩, ?_⟩
  intro h
  rcases h with ⟨_, _, hG⟩
  exact chain_not_god_source hG

theorem disc_th4_fails :
    ¬ dia R_disc (exAct chainEx (god chainP)) false := by
  intro h
  rcases h with ⟨v, hv, _, _, hG⟩
  cases hv
  exact chain_not_god_source hG

/-- Ax1GenTwo fails. Meaning no longer sees the sink, so the conjunction
pinned at the source need not hold there. -/
theorem disc_not_Ax1GenTwo : ¬ Ax1GenTwo R_disc chainEx chainP := by
  intro h
  let Φ : MPred Bool Unit := fun φ u => u = false ∧ (φ = topP ∨ φ = sinkMark)
  let χ : MProp Bool Unit := fun _ _ => False
  have hTwo : atLeastTwo Φ false := by
    refine ⟨topP, sinkMark, ?_, ?_, Ne.symm sinkMark_ne_top⟩
    · exact ⟨rfl, Or.inl rfl⟩
    · exact ⟨rfl, Or.inr rfl⟩
  have hPos : posProps chainP Φ false := by
    intro φ hΦ
    rcases hΦ.2 with hT | hS
    · subst hT
      trivial
    · subst hS
      rfl
  have hConj : conjOfPropsFrom R_disc chainEx χ Φ false := by
    intro v hv z hz
    cases hv
    constructor
    · intro hχ
      exact False.elim hχ
    · intro hAll
      have hS : Φ sinkMark false := ⟨rfl, Or.inr rfl⟩
      exact False.elim (by
        have hMark : sinkMark z false := hAll sinkMark hS
        simp [sinkMark] at hMark)
  have hP : chainP χ false := h Φ χ false hTwo hPos hConj
  exact hP

/-- The push in `chain_fig8_no_gap` needs `R false true`. This frame has no such edge. -/
theorem disc_breaks_the_push : ¬ R_disc false true :=
  disc_no_cross

end GodelOntological.Actualist.S5Gap
