import GodelOntological.Actualist
import GodelOntological.Actualist_Repaired

/-
# Hunt 7 — two conjuncts, roster still read twice

Benzmüller, “Proofs Without Nominals” (arXiv:2609.36279v2, 1 Oct 2026),
restricts Ax1Gen to collections with at least two distinct members at the
world of evaluation (`Ax1GenTwo`). That paper also isolates `Ax1GenBox`,
which is R1 of `Actualist_Repaired.lean`.

`Ax1GenTwo` is a weakening of literal Ax1Gen. The cardinality guard sits
beside Membership, not under the box, so Meaning still re-reads `Φ` at
successors. The R1/R2 chain is therefore not automatically a countermodel.
This file checks that it is not one: the same `chainP` satisfies R1 and
fails `Ax1GenTwo`, by the two-member roster of that paper’s Theorem 11.

Lemma L under the restriction is that paper’s Lemma 10. It is not re-proved
here.
-/

namespace GodelOntological.Actualist.TwoConjuncts

open GodelOntological.Actualist
open GodelOntological.Actualist.Repaired

def topP {W Ind : Type} : MProp W Ind := fun _ _ => True

/-- At least two distinct members of `Φ` at the world of evaluation. -/
def atLeastTwo {W Ind : Type} (Φ : MPred W Ind) : WorldProp W :=
  fun w => ∃ ψ1 ψ2, Φ ψ1 w ∧ Φ ψ2 w ∧ ψ1 ≠ ψ2

/-- **Ax1GenTwo.** Literal Membership and Meaning, refused for empty and
singleton rosters at the source. Not a same-world repair. -/
def Ax1GenTwo {W Ind : Type} (R : Access W) (ex : Ind → W → Prop)
    (P : MPred W Ind) : Prop :=
  ∀ (Φ : MPred W Ind) (φ : MProp W Ind),
    valid (fun w =>
      atLeastTwo Φ w → posProps P Φ w → conjOfPropsFrom R ex φ Φ w → P φ w)

theorem ax1Gen_implies_two {W Ind : Type} (R : Access W) (ex : Ind → W → Prop)
    (P : MPred W Ind) (hGen : Ax1Gen R ex P) : Ax1GenTwo R ex P :=
  fun Φ φ w _hTwo hPos hConj => hGen Φ φ w hPos hConj

/-- “This world is the sink.” Positive on the chain, not universal. -/
def sinkMark : MProp Bool Unit := fun _ u => u = true

theorem sinkMark_ne_top : sinkMark ≠ topP := by
  intro h
  have := congrFun (congrFun h ()) false
  simp [sinkMark, topP] at this

/-- Theorem 11’s roster, specialised to the chain: `{⊤, sinkMark}` where no
God-like being exists, `{⊥}` where one does. -/
def chainΦ : MPred Bool Unit :=
  fun ψ u =>
    (¬ exAct chainEx (god chainP) u ∧ (ψ = topP ∨ ψ = sinkMark)) ∨
      (exAct chainEx (god chainP) u ∧ ψ = botP)

def chainχ : MProp Bool Unit :=
  fun z u => ¬ exAct chainEx (god chainP) u ∧ sinkMark z u

theorem chain_no_god_source : ¬ exAct chainEx (god chainP) false := by
  intro h
  rcases h with ⟨_, _, hG⟩
  exact chain_not_god_source hG

theorem chain_god_at_sink : exAct chainEx (god chainP) true :=
  ⟨(), trivial, chain_god_sink⟩

theorem chainΦ_two_at_source : atLeastTwo chainΦ false := by
  refine ⟨topP, sinkMark, ?_, ?_, Ne.symm sinkMark_ne_top⟩
  · left
    exact ⟨chain_no_god_source, Or.inl rfl⟩
  · left
    exact ⟨chain_no_god_source, Or.inr rfl⟩

theorem chain_pos_at_source : posProps chainP chainΦ false := by
  intro ψ hΦ
  rcases hΦ with hNone | hSome
  · rcases hNone.2 with hTop | hSink
    · subst hTop
      trivial
    · subst hSink
      rfl
  · exact False.elim (chain_no_god_source hSome.1)

theorem chain_conj : conjOfPropsFrom R_chain chainEx chainχ chainΦ false := by
  intro v _hv z _hz
  cases v
  · constructor
    · intro hχ
      simp [chainχ, sinkMark] at hχ
    · intro hAll
      have hSink : chainΦ sinkMark false := by
        left
        exact ⟨chain_no_god_source, Or.inr rfl⟩
      have := hAll sinkMark hSink
      simp [sinkMark] at this
  · constructor
    · intro hχ
      simp [chainχ, sinkMark, chain_god_at_sink] at hχ
    · intro hAll
      have hBot : chainΦ botP true := by
        right
        exact ⟨chain_god_at_sink, rfl⟩
      exact False.elim (hAll botP hBot)

theorem chain_not_P_chi : ¬ chainP chainχ false := by
  intro h
  simp [chainP, chainχ, sinkMark, chain_god_at_sink] at h

theorem chain_not_Ax1GenTwo : ¬ Ax1GenTwo R_chain chainEx chainP := by
  intro h
  exact chain_not_P_chi
    (h chainΦ chainχ false chainΦ_two_at_source chain_pos_at_source chain_conj)

/-- R1 holds on this frame and Ax1GenTwo does not. The cardinality guard is
not a same-world repair: the chain that kills Th3 for R1 is not a model of
the October restriction. -/
theorem r1_not_two_on_chain :
    Ax1GenBox R_chain chainEx chainP ∧ ¬ Ax1GenTwo R_chain chainEx chainP :=
  ⟨chain_ax1GenBox, chain_not_Ax1GenTwo⟩

end GodelOntological.Actualist.TwoConjuncts
