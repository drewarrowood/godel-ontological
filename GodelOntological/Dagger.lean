import GodelOntological.Actualist
import GodelOntological.Actualist_Two

/-
# Whether (†) can be dropped

Benzmüller, arXiv:2609.36279v2, after Theorem 15, leaves open whether the
hybrid-free derivation of an actual God-like being under Fig. 8 inclusion
and Ax1GenTwo needs

  (†)  at some world where a God-like being exists, some individual is not.

Two facts settle the shape of that question. They do not close it in general.
-/

namespace GodelOntological.Actualist.Dagger

open GodelOntological.Actualist
open GodelOntological.Actualist.TwoConjuncts

/-- If two individuals differ at a God-world, Ax2a forces (†).
Full comprehension supplies the separating property. The side condition is
then not an extra assumption: it is exclusivity. -/
theorem dagger_of_distinct {W Ind : Type} {P : MPred W Ind} {w : W} {a b : Ind}
    (h2a : Ax2a P) (hG : god P a w)
    (φ : MProp W Ind) (hφ : φ a w) (hNot : ¬ φ b w) :
    ¬ god P b w := by
  intro hGb
  cases (h2a φ w).1 with
  | inl hP => exact hNot (hGb φ hP)
  | inr hNeg => exact hG (negPred φ) hNeg hφ

/-- On a one-individual domain, (†) fails at every world where that
individual is God-like. The open case is this one, not the two-individual one. -/
theorem dagger_fails_on_unit {W : Type} {P : MPred W Unit} {w : W}
    (hG : god P () w) :
    ¬ ∃ x, god P x w ∧ ∃ y, ¬ god P y w := by
  intro h
  rcases h with ⟨_, _, y, hNot⟩
  cases y
  exact hNot hG

/-! ## Fig. 8 + Ax1GenTwo on the chain, one actual individual

Assume Th4, so the sink is God-like, and assume the source is not. (†) fails.
The Fig. 7 prank still fires once the universal property is positive, and
Fig. 8's non-emptiness clause does not block it: `necExist` is not empty. -/

def ex1 : Unit → Bool → Prop := fun _ _ => True

theorem top_positive_fig8 (P : MPred Bool Unit)
    (h3 : Ax3_8 R_chain ex1 P) (h4 : Ax4_8 R_chain ex1 P)
    (hNe : neBot (necExist8 R_chain ex1)) :
    P topP false := by
  refine h4 (necExist8 R_chain ex1) topP false (h3 false) ?_
  intro v _hv
  refine ⟨hNe, ?_⟩
  intro _y _hy _hE
  trivial

theorem necExist_not_bot (P : MPred Bool Unit)
    (_h2a : Ax2a P) (_h2b : Ax2b R_chain P) (h3 : Ax3_8 R_chain ex1 P)
    (hGod : god P () true) :
    neBot (necExist8 R_chain ex1) := by
  intro hEq
  have hHold : necExist8 R_chain ex1 () true := hGod _ (h3 true)
  exact (hEq () true).mp hHold

/-- No positivity predicate satisfies Fig. 8's Ax2a, Ax2b, Ax3, Ax4 and
Ax1GenTwo on the chain if the source has no actual God-like being and the
sink does. Th4 at the source is that second assumption. (†) is not used:
on this domain it is false. -/
theorem chain_fig8_no_gap
    (P : MPred Bool Unit)
    (hTwo : Ax1GenTwo R_chain ex1 P)
    (h2a : Ax2a P) (h2b : Ax2b R_chain P)
    (h3 : Ax3_8 R_chain ex1 P) (h4 : Ax4_8 R_chain ex1 P)
    (hNo : ¬ exAct ex1 (god P) false)
    (hYes : exAct ex1 (god P) true) : False := by
  rcases hYes with ⟨_, _, hG⟩
  have hYes' : exAct ex1 (god P) true := ⟨(), trivial, hG⟩
  have hNotGod : ¬ god P () false := by
    intro h
    exact hNo ⟨(), trivial, h⟩
  have ⟨ψ, hPψ, hψFail⟩ : ∃ ψ, P ψ false ∧ ¬ ψ () false := by
    apply Classical.byContradiction
    intro hAll
    apply hNotGod
    intro φ hP
    apply Classical.byContradiction
    intro hFail
    exact hAll ⟨φ, hP, hFail⟩
  have hNe : neBot (necExist8 R_chain ex1) :=
    necExist_not_bot P h2a h2b h3 hG
  have hTop : P topP false := top_positive_fig8 P h3 h4 hNe
  have hψNe : ψ ≠ topP := by
    intro h
    have : ψ () false := by
      rw [h]
      trivial
    exact hψFail this
  let χ : MProp Bool Unit := fun z u => ¬ exAct ex1 (god P) u ∧ ψ z u
  let Φ : MPred Bool Unit := fun φ u =>
    (¬ exAct ex1 (god P) u ∧ (φ = topP ∨ φ = ψ)) ∨
      (exAct ex1 (god P) u ∧ φ = botP)
  have hTwoMem : atLeastTwo Φ false := by
    refine ⟨topP, ψ, ?_, ?_, Ne.symm hψNe⟩
    · left
      exact ⟨hNo, Or.inl rfl⟩
    · left
      exact ⟨hNo, Or.inr rfl⟩
  have hPos : posProps P Φ false := by
    intro φ hΦ
    rcases hΦ with hNone | hSome
    · rcases hNone.2 with hT | hψ
      · subst hT
        exact hTop
      · subst hψ
        exact hPψ
    · exact False.elim (hNo hSome.1)
  have hConj : conjOfPropsFrom R_chain ex1 χ Φ false := by
    intro v _hv z _hz
    cases v
    · constructor
      · intro hχ
        exact False.elim (hψFail hχ.2)
      · intro hAll
        have hψΦ : Φ ψ false := by
          left
          exact ⟨hNo, Or.inr rfl⟩
        exact False.elim (hψFail (hAll ψ hψΦ))
    · constructor
      · intro hχ
        exact False.elim (hχ.1 hYes')
      · intro hAll
        have hBot : Φ botP true := by
          right
          exact ⟨hYes', rfl⟩
        exact False.elim (hAll botP hBot)
  have hPχ : P χ false := hTwo Φ χ false hTwoMem hPos hConj
  have hχs : χ () true := hG χ (h2b χ false hPχ true trivial)
  exact hχs.1 hYes'

end GodelOntological.Actualist.Dagger
