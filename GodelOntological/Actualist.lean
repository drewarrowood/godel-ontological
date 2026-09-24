import GodelOntological.Frames

/-
# Actualist Fig. 7 (and the Fig. 8 inclusion) — Benzmüller & Scott

Shallow Lean reading of AFP `GoedelVariantHOML2` (Monatshefte Fig. 7,
DOI 10.1007/s00605-025-02078-x) and, where the inclusion differs, Fig. 8
(`GoedelVariantHOML3`). Positivity is world-relative. Individual quantifiers
in the argument are actualist (`existsAt`). Property quantifiers are
possibilist. `P(G)` is lemma L from Ax1Gen, not an axiom.

The S4 file `GoedelVariantHOML2inS4` leaves Theorem Th3 as `oops`
("Open problem"). This module proves Th3 from the Fig. 7 axioms with no
reflexivity, transitivity, or symmetry hypothesis: those axioms imply
`Symmetric R`, and the AFP proof of Th3 from Th2 plus symmetry then applies.
See `ACTUALIST_FIG7.md` for the quoted axiom list, departures, and status.
-/

namespace GodelOntological.Actualist

/-! ## HOML fragment (AFP `HOMLinHOL`, property order `e ⇒ i ⇒ bool`) -/

/-- World-lifted proposition (`σ = i ⇒ bool`). -/
abbrev WorldProp (W : Type) := W → Prop

/-- Modal property (`τ = e ⇒ σ`). Argument order is individual, then world. -/
abbrev MProp (W Ind : Type) := Ind → WorldProp W

/-- Higher-order modal predicate, e.g. positivity (`(e ⇒ σ) ⇒ σ`). -/
abbrev MPred (W Ind : Type) := MProp W Ind → WorldProp W

def box {W : Type} (R : Access W) (φ : WorldProp W) : WorldProp W :=
  fun w => ∀ v, R w v → φ v

def dia {W : Type} (R : Access W) (φ : WorldProp W) : WorldProp W :=
  fun w => ∃ v, R w v ∧ φ v

def valid {W : Type} (φ : WorldProp W) : Prop :=
  ∀ w, φ w

def negPred {W Ind : Type} (φ : MProp W Ind) : MProp W Ind :=
  fun x w => ¬ φ x w

def conjPred {W Ind : Type} (φ ψ : MProp W Ind) : MProp W Ind :=
  fun x w => φ x w ∧ ψ x w

/-- Exclusive or on world-propositions (`∨^e`). -/
def xorW {W : Type} (φ ψ : WorldProp W) : WorldProp W :=
  fun w => (φ w ∨ ψ w) ∧ ¬ (φ w ∧ ψ w)

def botP {W Ind : Type} : MProp W Ind :=
  fun _ _ => False

/-- Actualist universal, restricted to individuals that exist at the world. -/
def allAct {W Ind : Type} (ex : Ind → W → Prop) (φ : MProp W Ind) : WorldProp W :=
  fun w => ∀ x, ex x w → φ x w

/-- Actualist existential. -/
def exAct {W Ind : Type} (ex : Ind → W → Prop) (φ : MProp W Ind) : WorldProp W :=
  fun w => ∃ x, ex x w ∧ φ x w

/-! ## Fig. 7 definitions (`GoedelVariantHOML2`) -/

/-- Fig. 7 necessary property inclusion: `φ ⊃_N ψ ≡ □(∀^E y. φ y ⊃ ψ y)`. -/
def necImpl {W Ind : Type} (R : Access W) (ex : Ind → W → Prop)
    (φ ψ : MProp W Ind) : WorldProp W :=
  box R (allAct ex (fun y u => φ y u → ψ y u))

/-- `G x ≡ ∀φ. P φ ⊃ φ x` (possibilist quantifier over properties). -/
def god {W Ind : Type} (P : MPred W Ind) : MProp W Ind :=
  fun x w => ∀ φ, P φ w → φ x w

/-- Fig. 7 essence, with Scott’s conjunct `φ x`:
`φ Ess. x ≡ φ x ∧ (∀ψ. ψ x ⊃ (φ ⊃_N ψ))`. -/
def essence {W Ind : Type} (R : Access W) (ex : Ind → W → Prop)
    (φ : MProp W Ind) (x : Ind) : WorldProp W :=
  fun w => φ x w ∧ ∀ ψ, ψ x w → necImpl R ex φ ψ w

/-- Necessary existence. The AFP binder `∃^E x. φ x` shadows `x`;
this is `∀φ. φ Ess. x ⊃ □(∃^E z. φ z)`. -/
def necExist {W Ind : Type} (R : Access W) (ex : Ind → W → Prop) : MProp W Ind :=
  fun x w => ∀ φ, essence R ex φ x w → box R (exAct ex φ) w

/-- `PosProps Φ ≡ ∀φ. Φ φ ⊃ P φ`. -/
def posProps {W Ind : Type} (P : MPred W Ind) (Φ : MPred W Ind) : WorldProp W :=
  fun w => ∀ φ, Φ φ w → P φ w

/-- `ConjOfPropsFrom φ Φ ≡ □(∀^E z. φ z ↔ (∀ψ. Φ ψ ⊃ ψ z))`.
`Φ` on the right is read at the accessible world, not at the world of `P φ`. -/
def conjOfPropsFrom {W Ind : Type} (R : Access W) (ex : Ind → W → Prop)
    (φ : MProp W Ind) (Φ : MPred W Ind) : WorldProp W :=
  box R (allAct ex (fun z u => φ z u ↔ ∀ ψ, Φ ψ u → ψ z u))

/-! ## Fig. 7 axioms (hypotheses, not Lean `axiom`s) -/

/-- **Ax1.** `⌊P φ ∧ P ψ ⊃ P (φ . ψ)⌋`. Not used for Th3. -/
def Ax1 {W Ind : Type} (P : MPred W Ind) : Prop :=
  ∀ φ ψ, valid (fun w => P φ w → P ψ w → P (conjPred φ ψ) w)

/-- **Ax2a.** `⌊P φ ∨^e P (~φ)⌋`. -/
def Ax2a {W Ind : Type} (P : MPred W Ind) : Prop :=
  ∀ φ, valid (xorW (P φ) (P (negPred φ)))

/-- **Ax2b.** `⌊P φ ⊃ □ P φ⌋`. -/
def Ax2b {W Ind : Type} (R : Access W) (P : MPred W Ind) : Prop :=
  ∀ φ, valid (fun w => P φ w → box R (P φ) w)

/-- **Ax3.** `⌊P E⌋`. -/
def Ax3 {W Ind : Type} (R : Access W) (ex : Ind → W → Prop) (P : MPred W Ind) : Prop :=
  valid (P (necExist R ex))

/-- **Ax4.** `⌊P φ ∧ (φ ⊃_N ψ) ⊃ P ψ⌋`, with Fig. 7 `⊃_N`. -/
def Ax4 {W Ind : Type} (R : Access W) (ex : Ind → W → Prop) (P : MPred W Ind) : Prop :=
  ∀ φ ψ, valid (fun w => P φ w → necImpl R ex φ ψ w → P ψ w)

/-- **Ax1Gen.** `⌊(PosProps Φ ∧ ConjOfPropsFrom φ Φ) ⊃ P φ⌋`. -/
def Ax1Gen {W Ind : Type} (R : Access W) (ex : Ind → W → Prop) (P : MPred W Ind) : Prop :=
  ∀ (Φ : MPred W Ind) (φ : MProp W Ind),
    valid (fun w => posProps P Φ w → conjOfPropsFrom R ex φ Φ w → P φ w)

/-- **Th3.** `⌊◇(∃^E x. G x) ⊃ □(∃^E y. G y)⌋`. -/
def Th3 {W Ind : Type} (R : Access W) (ex : Ind → W → Prop) (P : MPred W Ind) : Prop :=
  valid (fun w => dia R (exAct ex (god P)) w → box R (exAct ex (god P)) w)

/-! ## Symmetry-free AFP lemmas, then symmetry from Ax1Gen -/

/-- **Lemma L.** `⌊P G⌋` from Ax1Gen and the definition of `G`. -/
theorem lemma_L {W Ind : Type} {R : Access W} {ex : Ind → W → Prop} {P : MPred W Ind}
    (hGen : Ax1Gen R ex P) : valid (P (god P)) := by
  intro w
  refine hGen (fun φ => P φ) (god P) w ?_ ?_
  · intro φ hP
    exact hP
  · intro _v _hv _z _hz
    constructor
    · intro hG ψ hP
      exact hG ψ hP
    · intro hAll ψ hP
      exact hAll ψ hP

/-- **Ax2b'.** `⌊¬P φ ⊃ □(¬P φ)⌋` from Ax2a and Ax2b. -/
theorem ax2b' {W Ind : Type} {R : Access W} {P : MPred W Ind}
    (h2a : Ax2a P) (h2b : Ax2b R P) (φ : MProp W Ind) :
    valid (fun w => ¬ P φ w → box R (fun v => ¬ P φ v) w) := by
  intro w hNot v hv hPv
  have hNegW : P (negPred φ) w := by
    cases (h2a φ w).1 with
    | inl hP => exact absurd hP hNot
    | inr hN => exact hN
  exact (h2a φ v).2 ⟨hPv, h2b (negPred φ) w hNegW v hv⟩

/-- **Th1 (Fig. 7).** `⌊G x ⊃ G Ess. x⌋` from Ax2a, Ax2b, and the definitions. -/
theorem th1_fig7 {W Ind : Type} {R : Access W} {ex : Ind → W → Prop} {P : MPred W Ind}
    (h2a : Ax2a P) (h2b : Ax2b R P) {x : Ind} {w : W} (hG : god P x w) :
    essence R ex (god P) x w := by
  refine ⟨hG, ?_⟩
  intro ψ hψ
  have hNotNeg : ¬ P (negPred ψ) w := by
    intro hNeg
    exact hG (negPred ψ) hNeg hψ
  have hPos : P ψ w := by
    cases (h2a ψ w).1 with
    | inl h => exact h
    | inr h => exact absurd h hNotNeg
  intro v hv y _hy hGy
  exact hGy ψ (h2b ψ w hPos v hv)

/-- **Th2 (Fig. 7).** `⌊G x ⊃ □(∃^E y. G y)⌋`. No symmetry. -/
theorem th2_fig7 {W Ind : Type} {R : Access W} {ex : Ind → W → Prop} {P : MPred W Ind}
    (h2a : Ax2a P) (h2b : Ax2b R P) (h3 : Ax3 R ex P)
    {x : Ind} {w : W} (hG : god P x w) :
    box R (exAct ex (god P)) w := by
  have hE : necExist R ex x w := hG (necExist R ex) (h3 w)
  exact hE (god P) (th1_fig7 h2a h2b hG)

/-- **Th3 from symmetry.** AFP’s three-step proof (`Th2`, then `Rsymm`).
Rediscovery of `GoedelVariantHOML2.Th3`. Reflexivity is not used. -/
theorem th3_of_symmetric {W Ind : Type} {R : Access W} {ex : Ind → W → Prop}
    {P : MPred W Ind}
    (h2a : Ax2a P) (h2b : Ax2b R P) (h3 : Ax3 R ex P) (hSym : Symmetric R) :
    Th3 R ex P := by
  intro w hDia
  rcases hDia with ⟨v, hwv, hvA⟩
  rcases hvA with ⟨x, _, hG⟩
  have hAtW : exAct ex (god P) w :=
    th2_fig7 h2a h2b h3 hG w (hSym w v hwv)
  rcases hAtW with ⟨y, _, hGy⟩
  exact th2_fig7 h2a h2b h3 hGy

/-- **Fig. 7 axioms imply symmetry of `R`.**
Instantiates Ax1Gen at `w` with `φ = (λ _ u => u = w)` and with `Φ` empty at `w`
and, elsewhere, the property of being universally false. Ax2b pushes positivity
to a successor `v` that does not see `w`; Fig. 7 inclusion of `φ` in `~φ` is then
vacuous, and Ax4 contradicts Ax2a. -/
theorem fig7_implies_symmetric {W Ind : Type} {R : Access W} {ex : Ind → W → Prop}
    {P : MPred W Ind}
    (hGen : Ax1Gen R ex P) (h2a : Ax2a P) (h2b : Ax2b R P) (h4 : Ax4 R ex P) :
    Symmetric R := by
  intro w v hwv
  apply Classical.byContradiction
  intro hnot
  let φ : MProp W Ind := fun _ u => u = w
  let Φ : MPred W Ind := fun ψ u => u ≠ w ∧ ∀ x, ¬ ψ x u
  have hPφ : P φ w := by
    refine hGen Φ φ w ?_ ?_
    · intro ψ hΦ
      exact absurd rfl hΦ.1
    · intro u _hu z _hz
      constructor
      · intro hzu ψ hΦ
        exact absurd hzu hΦ.1
      · intro hRHS
        apply Classical.byContradiction
        intro hne
        have hΦbot : Φ botP u := ⟨hne, fun _ h => h⟩
        exact hRHS botP hΦbot
  have hPφv : P φ v := h2b φ w hPφ v hwv
  have hIncl : necImpl R ex φ (negPred φ) v := by
    intro u hu z _hz hφ
    cases hφ
    intro hw
    exact hnot hu
  have hPneg : P (negPred φ) v := h4 φ (negPred φ) v hPφv hIncl
  exact (h2a φ v).2 ⟨hPφv, hPneg⟩

/-- **Th3 (Fig. 7), no frame hypothesis.**
Ax1Gen, Ax2a, Ax2b, Ax3, Ax4. Symmetry is derived, then the AFP proof runs.
Reflexivity and transitivity are not hypotheses, so the result holds in S4. -/
theorem th3_fig7 {W Ind : Type} {R : Access W} {ex : Ind → W → Prop} {P : MPred W Ind}
    (hGen : Ax1Gen R ex P) (h2a : Ax2a P) (h2b : Ax2b R P)
    (h3 : Ax3 R ex P) (h4 : Ax4 R ex P) :
    Th3 R ex P :=
  th3_of_symmetric h2a h2b h3 (fig7_implies_symmetric hGen h2a h2b h4)

/-- **Th4.** `⌊◇(∃^E x. G x)⌋` from Ax2a, Ax4, and L. -/
theorem th4_fig7 {W Ind : Type} {R : Access W} {ex : Ind → W → Prop} {P : MPred W Ind}
    (h2a : Ax2a P) (h4 : Ax4 R ex P) (hL : valid (P (god P))) :
    valid (dia R (exAct ex (god P))) := by
  intro w
  apply Classical.byContradiction
  intro hNot
  have hIncl : necImpl R ex (god P) botP w := by
    intro v hv x hx hG
    exact hNot ⟨v, hv, x, hx, hG⟩
  have hPbot : P botP w := h4 (god P) botP w (hL w) hIncl
  have hInclNeg : necImpl R ex botP (negPred botP) w := by
    intro _v _hv _x _hx hbot
    exact False.elim hbot
  have hPneg : P (negPred botP) w := h4 botP (negPred botP) w hPbot hInclNeg
  exact (h2a botP w).2 ⟨hPbot, hPneg⟩

/-- **Th5.** `⌊□(∃^E x. G x)⌋` from Th3 and Th4. -/
theorem th5_fig7 {W Ind : Type} {R : Access W} {ex : Ind → W → Prop} {P : MPred W Ind}
    (hGen : Ax1Gen R ex P) (h2a : Ax2a P) (h2b : Ax2b R P)
    (h3 : Ax3 R ex P) (h4 : Ax4 R ex P) :
    valid (box R (exAct ex (god P))) := by
  intro w
  exact th3_fig7 hGen h2a h2b h3 h4 w
    (th4_fig7 h2a h4 (lemma_L hGen) w)

/-! ## S4 chain: not a Fig. 7 countermodel -/

/-- Two-world S4 chain: `false` sees both worlds, `true` sees only itself. -/
def R_chain (w v : Bool) : Prop :=
  match w with
  | false => True
  | true => v = true

theorem R_chain_reflexive : Reflexive R_chain := by
  intro w
  cases w <;> trivial

theorem R_chain_transitive : Transitive R_chain := by
  intro w v u hwv hvu
  cases w <;> cases v <;> cases u <;> simp_all [R_chain]

theorem R_chain_not_symmetric : ¬ Symmetric R_chain := by
  intro hSym
  have : R_chain true false := hSym false true trivial
  simp [R_chain] at this

/-- The Fig. 7 axioms used for symmetry are unsatisfiable on this S4 chain.
So the chain is not a countermodel to Th3: there is no `P` and `existsAt`
making the axioms true while Th3 fails. -/
theorem fig7_unsat_on_S4_chain {Ind : Type} (ex : Ind → Bool → Prop)
    (P : MPred Bool Ind)
    (hGen : Ax1Gen R_chain ex P) (h2a : Ax2a P) (h2b : Ax2b R_chain P)
    (h4 : Ax4 R_chain ex P) : False :=
  R_chain_not_symmetric (fig7_implies_symmetric hGen h2a h2b h4)

/-! ## One-world control (Nitpick’s cardinality-one shape)

Principal positivity on a single reflexive world. Shows the Fig. 7 axioms
are not jointly absurd once `R` may be symmetric. -/

def unitEx : Unit → Unit → Prop := fun _ _ => True

def unitP : MPred Unit Unit := fun φ _ => φ () ()

theorem unit_ax1 : Ax1 unitP := by
  intro φ ψ w hφ hψ
  cases w
  exact ⟨hφ, hψ⟩

theorem unit_ax2a : Ax2a unitP := by
  intro φ w
  cases w
  refine ⟨Classical.em (φ () ()), ?_⟩
  intro h
  exact h.2 h.1

theorem unit_ax2b : Ax2b (idRel Unit) unitP := by
  intro φ w hφ v hv
  cases w
  cases v
  exact hφ

theorem unit_ax4 : Ax4 (idRel Unit) unitEx unitP := by
  intro φ ψ w hφ hIncl
  cases w
  exact hIncl () rfl () trivial hφ

theorem unit_ax1Gen : Ax1Gen (idRel Unit) unitEx unitP := by
  intro Φ φ w hPos hConj
  cases w
  exact (hConj () rfl () trivial).mpr (fun ψ hΦ => hPos ψ hΦ)

theorem unit_ax3 : Ax3 (idRel Unit) unitEx unitP := by
  intro w
  cases w
  intro φ hEss v hv
  cases v
  exact ⟨(), trivial, hEss.1⟩

theorem unit_fig7_th3 :
    Th3 (idRel Unit) unitEx unitP :=
  th3_fig7 unit_ax1Gen unit_ax2a unit_ax2b unit_ax3 unit_ax4

/-! ## Fig. 8 inclusion (`GoedelVariantHOML3`)

`φ ⊃_N ψ ≡ □(φ ≠ (λx. ⊥) ∧ ∀^E y. φ y ⊃ ψ y)`.
Essence drops the conjunct `φ x`. The S4 file likewise leaves Th3 open.
The symmetry argument still applies when an individual is on hand to witness
`φ ≠ ⊥` (Fig. 7 did not need that witness). -/

/-- Extensional disagreement with `λx w. False`.
Isabelle/HOL identifies functions extensionally, so `φ ≠ (λx. ⊥)` is this fact,
not Lean’s intensional `φ ≠ botP`. -/
def neBot {W Ind : Type} (φ : MProp W Ind) : Prop :=
  ¬ ∀ x w, φ x w ↔ False

/-- Fig. 8 necessary inclusion. The inequality is world-independent. -/
def necImpl8 {W Ind : Type} (R : Access W) (ex : Ind → W → Prop)
    (φ ψ : MProp W Ind) : WorldProp W :=
  box R (fun u => neBot φ ∧ allAct ex (fun y u' => φ y u' → ψ y u') u)

/-- Fig. 8 essence, without the conjunct `φ x`. -/
def essence8 {W Ind : Type} (R : Access W) (ex : Ind → W → Prop)
    (φ : MProp W Ind) (x : Ind) : WorldProp W :=
  fun w => ∀ ψ, ψ x w → necImpl8 R ex φ ψ w

def necExist8 {W Ind : Type} (R : Access W) (ex : Ind → W → Prop) : MProp W Ind :=
  fun x w => ∀ φ, essence8 R ex φ x w → box R (exAct ex φ) w

def Ax3_8 {W Ind : Type} (R : Access W) (ex : Ind → W → Prop) (P : MPred W Ind) : Prop :=
  valid (P (necExist8 R ex))

def Ax4_8 {W Ind : Type} (R : Access W) (ex : Ind → W → Prop) (P : MPred W Ind) : Prop :=
  ∀ φ ψ, valid (fun w => P φ w → necImpl8 R ex φ ψ w → P ψ w)

/-- **Th1 (Fig. 8).** -/
theorem th1_fig8 {W Ind : Type} {R : Access W} {ex : Ind → W → Prop} {P : MPred W Ind}
    (h2a : Ax2a P) (h2b : Ax2b R P) {x : Ind} {w : W} (hG : god P x w) :
    essence8 R ex (god P) x w := by
  intro ψ hψ
  have hNotNeg : ¬ P (negPred ψ) w := by
    intro hNeg
    exact hG (negPred ψ) hNeg hψ
  have hPos : P ψ w := by
    cases (h2a ψ w).1 with
    | inl h => exact h
    | inr h => exact absurd h hNotNeg
  intro v hv
  refine ⟨?_, ?_⟩
  · intro hEq
    exact (hEq x w).mp hG
  · intro y _hy hGy
    exact hGy ψ (h2b ψ w hPos v hv)

/-- **Th2 (Fig. 8).** No symmetry. -/
theorem th2_fig8 {W Ind : Type} {R : Access W} {ex : Ind → W → Prop} {P : MPred W Ind}
    (h2a : Ax2a P) (h2b : Ax2b R P) (h3 : Ax3_8 R ex P)
    {x : Ind} {w : W} (hG : god P x w) :
    box R (exAct ex (god P)) w := by
  have hE : necExist8 R ex x w := hG (necExist8 R ex) (h3 w)
  exact hE (god P) (th1_fig8 h2a h2b hG)

theorem th3_fig8_of_symmetric {W Ind : Type} {R : Access W} {ex : Ind → W → Prop}
    {P : MPred W Ind}
    (h2a : Ax2a P) (h2b : Ax2b R P) (h3 : Ax3_8 R ex P) (hSym : Symmetric R) :
    Th3 R ex P := by
  intro w hDia
  rcases hDia with ⟨v, hwv, hvA⟩
  rcases hvA with ⟨x, _, hG⟩
  have hAtW : exAct ex (god P) w :=
    th2_fig8 h2a h2b h3 hG w (hSym w v hwv)
  rcases hAtW with ⟨y, _, hGy⟩
  exact th2_fig8 h2a h2b h3 hGy

/-- Fig. 8 axioms imply symmetry. `x0` witnesses `φ ≠ (λ_. ⊥)`. -/
theorem fig8_implies_symmetric {W Ind : Type} {R : Access W} {ex : Ind → W → Prop}
    {P : MPred W Ind} (x0 : Ind)
    (hGen : Ax1Gen R ex P) (h2a : Ax2a P) (h2b : Ax2b R P) (h4 : Ax4_8 R ex P) :
    Symmetric R := by
  intro w v hwv
  apply Classical.byContradiction
  intro hnot
  let φ : MProp W Ind := fun _ u => u = w
  let Φ : MPred W Ind := fun ψ u => u ≠ w ∧ ∀ x, ¬ ψ x u
  have hPφ : P φ w := by
    refine hGen Φ φ w ?_ ?_
    · intro ψ hΦ
      exact absurd rfl hΦ.1
    · intro u _hu z _hz
      constructor
      · intro hzu ψ hΦ
        exact absurd hzu hΦ.1
      · intro hRHS
        apply Classical.byContradiction
        intro hne
        exact hRHS botP ⟨hne, fun _ h => h⟩
  have hPφv : P φ v := h2b φ w hPφ v hwv
  have hNeq : neBot φ := by
    intro hEq
    exact (hEq x0 w).mp rfl
  have hIncl : necImpl8 R ex φ (negPred φ) v := by
    intro u hu
    refine ⟨hNeq, ?_⟩
    intro z _hz hφ
    cases hφ
    intro _hw
    exact hnot hu
  have hPneg : P (negPred φ) v := h4 φ (negPred φ) v hPφv hIncl
  exact (h2a φ v).2 ⟨hPφv, hPneg⟩

/-- **Th3 (Fig. 8), no frame hypothesis.** If `◇∃^E G` holds at `w`, the witness
individual feeds `fig8_implies_symmetric`, and the AFP back-edge is available. -/
theorem th3_fig8 {W Ind : Type} {R : Access W} {ex : Ind → W → Prop} {P : MPred W Ind}
    (hGen : Ax1Gen R ex P) (h2a : Ax2a P) (h2b : Ax2b R P)
    (h3 : Ax3_8 R ex P) (h4 : Ax4_8 R ex P) :
    Th3 R ex P := by
  intro w hDia
  have hSym : Symmetric R := by
    rcases hDia with ⟨_, _, x0, _, _⟩
    exact fig8_implies_symmetric x0 hGen h2a h2b h4
  exact th3_fig8_of_symmetric h2a h2b h3 hSym w hDia

theorem fig8_unsat_on_S4_chain {Ind : Type} (x0 : Ind) (ex : Ind → Bool → Prop)
    (P : MPred Bool Ind)
    (hGen : Ax1Gen R_chain ex P) (h2a : Ax2a P) (h2b : Ax2b R_chain P)
    (h4 : Ax4_8 R_chain ex P) : False :=
  R_chain_not_symmetric (fig8_implies_symmetric x0 hGen h2a h2b h4)

end GodelOntological.Actualist
