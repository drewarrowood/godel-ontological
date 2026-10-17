-- (was: Does `L` follow?  Neither a countermodel nor a proof was found.)
/-- Arrowood (godel-ontological, `lemma_L_rigid` / `pos_agree`, commit 27524f7, 2026-09-24),
replayed against Benzmüller's own module: the open `L` for rigid `Φ` holds, from `Ax1GenR`,
`Ax2a`, `Ax2b` (logic K). The witness is the snapshot `fun ψ => P ψ w`. -/
theorem pos_agree_R {w v : i} (hwv : w 𝗿 v) (ψ : e → σ) : P ψ w ↔ P ψ v := by
  constructor
  · intro h; exact Ax2b ψ w h v hwv
  · intro hv
    apply Classical.byContradiction
    intro hn
    have hneg : P (~ᵐψ) w := (Ax2a' ψ w).1 hn
    have hneg' : P (~ᵐψ) v := Ax2b (~ᵐψ) w hneg v hwv
    exact (Ax2a ψ v).2 ⟨hv, hneg'⟩

theorem L_R_derived (hR : Ax1GenR) : ⌊P G⌋ := by
  intro w
  refine hR (fun ψ => P ψ w) G w ⟨fun ψ h => h, ?_⟩
  show ∀ v, w 𝗿 v → ∀ z, z @ᵐ v → (G z v ↔ ∀ ψ, P ψ w → ψ z v)
  intro v hv z _hz
  constructor
  · intro hG ψ hψ; exact hG ψ ((pos_agree_R hv ψ).mp hψ)
  · intro hAll
    show ∀ ψ, P ψ v → ψ z v
    intro ψ hψv; exact hAll ψ ((pos_agree_R hv ψ).mpr hψv)

#print axioms L_R_derived
