
/-! ## Arrowood, "One World or Two": the empty-at-home instance of Ax1Gen
(`isabelle/Ax1Gen_EmptyAtHome.thy`, `fig7_implies_symmetric`), replayed in this module so that
Benzmüller's detector can classify its witnesses. -/
theorem fig7_implies_symmetric_EAH : ∀ w v, w 𝗿 v → v 𝗿 w := by
  intro w v hwv
  apply Classical.byContradiction
  intro hnot
  let φ : e → σ := fun _ u => u = w
  let Φ : (e → σ) → σ := fun ψ u => u ≠ w ∧ ∀ x, ¬ ψ x u
  have hpos : PosProps Φ w := fun ψ h => absurd rfl h.1
  have hconj : ConjOfPropsFrom φ Φ w := by
    intro u _ z _
    show (u = w ↔ ∀ ψ, Φ ψ u → ψ z u)
    constructor
    · intro h ψ hψ; exact absurd h hψ.1
    · intro hall
      apply Classical.byContradiction
      intro hn
      exact hall (fun _ => ⊥ᵐ) ⟨hn, fun _ h => h⟩
  have hP : P φ w := Ax1Gen Φ φ w ⟨hpos, hconj⟩
  have hPv : P φ v := Ax2b φ w hP v hwv
  have hincl : (φ ⊃ᴺ ~ᵐφ) v := by
    intro u huv y _ hy
    have hy' : u = w := hy
    rw [hy'] at huv
    exact absurd huv hnot
  have hneg : P (~ᵐφ) v := Ax4 φ (~ᵐφ) v ⟨hPv, hincl⟩
  exact (Ax2a φ v).2 ⟨hPv, hneg⟩

#print axioms fig7_implies_symmetric_EAH
