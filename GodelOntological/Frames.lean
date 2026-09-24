/-
# Accessibility frames (weak-frame Scott)

Named frame conditions and R-relative □ / ◇. The universal encoding in
`Modal.lean` is the special case `R = fun _ _ => True`.
-/

namespace GodelOntological

/-- Accessibility relation on worlds. -/
abbrev Access (W : Type) := W → W → Prop

/-- Necessity at `w` relative to `R`: true at all `R`-successors of `w`. -/
def necessaryR {W : Type} (R : Access W) (φ : W → Prop) (w : W) : Prop :=
  ∀ v : W, R w v → φ v

/-- Possibility at `w` relative to `R`: true at some `R`-successor of `w`. -/
def possibleR {W : Type} (R : Access W) (φ : W → Prop) (w : W) : Prop :=
  ∃ v : W, R w v ∧ φ v

/-! ## Standard frame properties -/

def Reflexive {W : Type} (R : Access W) : Prop :=
  ∀ w : W, R w w

def Symmetric {W : Type} (R : Access W) : Prop :=
  ∀ w v : W, R w v → R v w

def Transitive {W : Type} (R : Access W) : Prop :=
  ∀ w v u : W, R w v → R v u → R w u

/-- Euclidean: `R w v → R w u → R v u`. With reflexivity, yields S5. -/
def Euclidean {W : Type} (R : Access W) : Prop :=
  ∀ w v u : W, R w v → R w u → R v u

def Serial {W : Type} (R : Access W) : Prop :=
  ∀ w : W, ∃ v : W, R w v

/-- Universal (total) accessibility: every world sees every world. -/
def Universal {W : Type} (R : Access W) : Prop :=
  ∀ w v : W, R w v

/-- Brouwerian frame condition: symmetry of `R` (modal axiom B: `φ → □◇φ`). -/
def Brouwerian {W : Type} (R : Access W) : Prop :=
  Symmetric R

/-- S5 frame conditions: reflexive + Euclidean (implies symmetric + transitive). -/
def S5Frame {W : Type} (R : Access W) : Prop :=
  Reflexive R ∧ Euclidean R

/-- Equivalence-relation frame (alternative S5 packaging). -/
def EquivalenceFrame {W : Type} (R : Access W) : Prop :=
  Reflexive R ∧ Symmetric R ∧ Transitive R

/-- TB / Brouwerian-T frame: reflexive + symmetric (modal T + B).
Strictly weaker than `S5Frame` / `EquivalenceFrame` (no transitivity / euclidean). -/
def TBFrame {W : Type} (R : Access W) : Prop :=
  Reflexive R ∧ Symmetric R

/-! ## Elementary consequences -/

theorem Universal.reflexive {W : Type} {R : Access W} (h : Universal R) :
    Reflexive R := fun w => h w w

theorem Universal.symmetric {W : Type} {R : Access W} (h : Universal R) :
    Symmetric R := fun w v _ => h v w

theorem Universal.transitive {W : Type} {R : Access W} (h : Universal R) :
    Transitive R := fun w _v u _ _ => h w u

theorem Universal.euclidean {W : Type} {R : Access W} (h : Universal R) :
    Euclidean R := fun _w v u _ _ => h v u

theorem Universal.s5 {W : Type} {R : Access W} (h : Universal R) :
    S5Frame R :=
  ⟨h.reflexive, h.euclidean⟩

/-- Reflexive + Euclidean ⇒ Symmetric. -/
theorem S5Frame.symmetric {W : Type} {R : Access W}
    (h : S5Frame R) : Symmetric R := by
  intro w v hwv
  exact h.2 w v w hwv (h.1 w)

/-- Reflexive + Euclidean ⇒ Transitive. -/
theorem S5Frame.transitive {W : Type} {R : Access W}
    (h : S5Frame R) : Transitive R := by
  intro w v u hwv hvu
  have hsym : Symmetric R := h.symmetric
  exact h.2 v w u (hsym w v hwv) hvu

theorem S5Frame.equivalence {W : Type} {R : Access W}
    (h : S5Frame R) : EquivalenceFrame R :=
  ⟨h.1, h.symmetric, h.transitive⟩

/-- Under S5: if `R w v`, then `w` and `v` see the same worlds. -/
theorem S5Frame.same_cluster {W : Type} {R : Access W}
    (h : S5Frame R) {w v u : W} (hwv : R w v) :
    R w u ↔ R v u := by
  constructor
  · intro hwu
    exact h.2 w v u hwv hwu
  · intro hvu
    exact h.transitive w v u hwv hvu

theorem TBFrame.reflexive {W : Type} {R : Access W} (h : TBFrame R) :
    Reflexive R := h.1

theorem TBFrame.symmetric {W : Type} {R : Access W} (h : TBFrame R) :
    Symmetric R := h.2

theorem TBFrame.brouwerian {W : Type} {R : Access W} (h : TBFrame R) :
    Brouwerian R := h.2

/-- S5Frame ⇒ TBFrame (strictly stronger: also euclidean / transitive). -/
theorem S5Frame.tb {W : Type} {R : Access W} (h : S5Frame R) : TBFrame R :=
  ⟨h.1, h.symmetric⟩

/-- The constantly-true relation is universal. -/
def universalRel (W : Type) : Access W := fun _ _ => True

theorem universalRel_is_universal (W : Type) :
    Universal (universalRel W) := fun _ _ => trivial

/-- Identity accessibility: each world sees only itself (S5, not universal if `|W|>1`). -/
def idRel (W : Type) : Access W := fun w v => w = v

theorem idRel_reflexive (W : Type) : Reflexive (idRel W) := fun _ => rfl

theorem idRel_symmetric (W : Type) : Symmetric (idRel W) := fun _ _ h => h.symm

theorem idRel_transitive (W : Type) : Transitive (idRel W) :=
  fun _ _ _ hwv hvu => hwv.trans hvu

theorem idRel_euclidean (W : Type) : Euclidean (idRel W) :=
  fun _ _ _ hwv hwu => hwv.symm.trans hwu

theorem idRel_s5 (W : Type) : S5Frame (idRel W) :=
  ⟨idRel_reflexive W, idRel_euclidean W⟩

end GodelOntological
