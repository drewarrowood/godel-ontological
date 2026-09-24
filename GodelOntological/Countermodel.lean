import GodelOntological.WeakScott

/-
# Finite countermodels for weak-frame Scott

## Result A — universality is load-bearing for global T3

Even under full **S5Frame** (refl + euclidean), if `R` is not universal,
`A1–A5` can hold while `∀w ∃x GodLike w x` fails.

Concrete model:
* `W = Bool`, `R = idRel` (two isolated reflexive worlds — an S5 frame)
* `Ind = Unit`
* `Positive φ ↔ φ false unit` (positive = true at the `false` world)

Then GodLike holds only at `false`; A1–A5 hold; local T3 holds at `false`;
global T3 and `□∃G` at `true` fail.

## Result B — S4 (refl+trans) is insufficient for local T3

On an S4 chain `w₀ → w₁` (refl + trans, not sym), A1–A5 can hold with God
only at the sink, so at the source `◇∃G` holds but `□∃G` fails.

## Result C — TB is strictly weaker than S5Frame (strictness witness)

A 3-world undirected path is **TBFrame** (refl+sym) but **not** Euclidean /
not transitive / not S5Frame. Local T3 is nevertheless available on every TB
frame via `local_T3_of_Symmetric` / `local_T3_of_TB` (proved in `WeakScott`).
This is not a T3-countermodel — it shows the named weakening is real.
-/

namespace GodelOntological
namespace Countermodel

/-! ## Shared Positive for “true at a designated world” (Ind = Unit) -/

/-- Positive properties = those exemplified by `()` at world `pivot`. -/
def PositiveAt {W : Type} (pivot : W) : Property W Unit → Prop :=
  fun φ => φ pivot ()

theorem A1_PositiveAt {W : Type} (pivot : W) :
    A1R (PositiveAt (W := W) pivot) := by
  intro φ
  constructor
  · intro hNeg hPos
    exact hNeg hPos
  · intro hNot
    exact hNot

theorem A2_PositiveAt {W : Type} (pivot : W) :
    A2R (PositiveAt (W := W) pivot) := by
  intro φ ψ hP hEnt
  exact hEnt pivot () hP

/-! ## Result A: discrete 2-world S5 frame -/

abbrev W2 : Type := Bool
abbrev Ind1 : Type := Unit

def R_id : Access W2 := idRel W2

theorem R_id_s5 : S5Frame R_id := idRel_s5 W2

def PosA : Property W2 Ind1 → Prop := PositiveAt (pivot := false)

theorem PosA_A1 : A1R PosA := A1_PositiveAt false
theorem PosA_A2 : A2R PosA := A2_PositiveAt false

/-- GodLike holds at `w` iff `w = false`. -/
theorem GodLike_PosA (w : W2) (x : Ind1) :
    GodLike PosA w x ↔ w = false := by
  constructor
  · intro hg
    let φ : Property W2 Ind1 := fun v _ => v = false
    have hP : PosA φ := rfl
    exact hg φ hP
  · intro hw φ hP
    cases x
    -- hP : φ false (); rewrite along w = false
    rw [hw]; exact hP

theorem PosA_A3 : A3R PosA := by
  -- Positive(GodLike) ↔ GodLike false () ↔ true
  change GodLike PosA false ()
  exact (GodLike_PosA false ()).mpr rfl

/-- Under identity accessibility + Unit, NER is always true. -/
theorem NER_id_always (w : W2) (x : Ind1) : NER R_id w x := by
  intro φ hEss
  intro v hv
  -- hv : w = v
  cases x
  refine ⟨(), ?_⟩
  -- Essence gives φ w (); transport along hv
  have hφ : φ w () := hEss.1
  simpa [R_id, idRel, hv.symm] using hφ

theorem PosA_A5 : A5R R_id PosA := by
  -- Positive(NER) ↔ NER false () ↔ true
  exact NER_id_always false ()

/-- Global C holds: God at `false`. -/
theorem PosA_global_C : ∃ w : W2, ∃ x : Ind1, GodLike PosA w x :=
  ⟨false, (), (GodLike_PosA false ()).mpr rfl⟩

/-- God fails at `true`. -/
theorem PosA_no_God_at_true : ¬ ∃ x : Ind1, GodLike PosA true x := by
  intro ⟨x, hx⟩
  have : true = false := (GodLike_PosA true x).mp hx
  exact Bool.noConfusion this

/-- **Countermodel A (global T3 fails).** S5Frame + A1–A5, yet not every
world has a God-like being. Universality was load-bearing. -/
theorem countermodel_A_global_T3_fails :
    S5Frame R_id ∧
    A1R PosA ∧ A2R PosA ∧ A3R PosA ∧ A5R R_id PosA ∧
    (∃ w : W2, ∃ x : Ind1, GodLike PosA w x) ∧
    ¬ (∀ w : W2, ∃ x : Ind1, GodLike PosA w x) := by
  refine ⟨R_id_s5, PosA_A1, PosA_A2, PosA_A3, PosA_A5, PosA_global_C, ?_⟩
  intro hAll
  exact PosA_no_God_at_true (hAll true)

/-- At `true`, even local □∃G fails (identity cluster has no God). -/
theorem countermodel_A_box_fails_at_true :
    ¬ necessaryR R_id (fun v => ∃ x : Ind1, GodLike PosA v x) true := by
  intro hNec
  exact PosA_no_God_at_true (hNec true rfl)

/-- Local T3 still holds at the God-world under S5. -/
theorem countermodel_A_local_T3_at_false :
    necessaryR R_id (fun v => ∃ x : Ind1, GodLike PosA v x) false := by
  exact exists_God_implies_necessaryR R_id PosA PosA_A1 PosA_A5
    ⟨(), (GodLike_PosA false ()).mpr rfl⟩

/-- `R_id` is not universal. -/
theorem R_id_not_universal : ¬ Universal R_id := by
  intro hU
  have : false = true := hU false true
  exact Bool.noConfusion this

/-! ## Result B: S4 chain — local T3 fails without euclidean/symmetry -/

/-- Two-point chain: `false` sees both; `true` sees only itself. -/
def R_chain : Access W2 := fun w v =>
  match w with
  | false => True          -- source sees everyone
  | true  => v = true      -- sink sees only itself

theorem R_chain_reflexive : Reflexive R_chain := by
  intro w
  cases w <;> simp [R_chain]

theorem R_chain_transitive : Transitive R_chain := by
  intro w v u hwv hvu
  cases w <;> cases v <;> cases u <;> simp_all [R_chain]

theorem R_chain_not_symmetric : ¬ Symmetric R_chain := by
  intro hSym
  -- false R true, but not true R false
  have hft : R_chain false true := trivial
  have : R_chain true false := hSym false true hft
  simp [R_chain] at this

theorem R_chain_not_euclidean : ¬ Euclidean R_chain := by
  intro hEu
  -- false R false and false R true ⇒ should get false R ... wait
  -- Euclidean: R w v → R w u → R v u
  -- Take w=false, v=true, u=false: R false true, R false false ⇒ R true false
  have : R_chain true false :=
    hEu false true false trivial (R_chain_reflexive false)
  simp [R_chain] at this

def PosB : Property W2 Ind1 → Prop := PositiveAt (pivot := true)

theorem PosB_A1 : A1R PosB := A1_PositiveAt true
theorem PosB_A2 : A2R PosB := A2_PositiveAt true

theorem GodLike_PosB (w : W2) (x : Ind1) :
    GodLike PosB w x ↔ w = true := by
  constructor
  · intro hg
    let φ : Property W2 Ind1 := fun v _ => v = true
    have hP : PosB φ := rfl
    exact hg φ hP
  · intro hw φ hP
    cases x
    rw [hw]; exact hP

theorem PosB_A3 : A3R PosB :=
  (GodLike_PosB true ()).mpr rfl

/-- NER at the sink (`true`) under the chain: only sees itself, so like id. -/
theorem NER_chain_at_sink (x : Ind1) : NER R_chain true x := by
  intro φ hEss
  intro v hv
  cases x
  refine ⟨(), ?_⟩
  have hφ : φ true () := hEss.1
  simpa [R_chain, hv.symm] using hφ

/-- At the source, NER may fail — but A5 only requires Positive(NER), i.e.
NER at the pivot `true`. -/
theorem PosB_A5 : A5R R_chain PosB :=
  NER_chain_at_sink ()

theorem PosB_God_only_at_true :
    (∃ x : Ind1, GodLike PosB true x) ∧
    ¬ (∃ x : Ind1, GodLike PosB false x) := by
  constructor
  · exact ⟨(), (GodLike_PosB true ()).mpr rfl⟩
  · intro ⟨x, hx⟩
    have : false = true := (GodLike_PosB false x).mp hx
    exact Bool.noConfusion this

/-- At the source: ◇∃G holds (sees the sink). -/
theorem PosB_diamond_at_source :
    possibleR R_chain (fun v => ∃ x : Ind1, GodLike PosB v x) false :=
  ⟨true, trivial, ⟨(), (GodLike_PosB true ()).mpr rfl⟩⟩

/-- At the source: □∃G fails (no God at source). -/
theorem PosB_box_fails_at_source :
    ¬ necessaryR R_chain (fun v => ∃ x : Ind1, GodLike PosB v x) false := by
  intro hNec
  have hAtFalse := hNec false (R_chain_reflexive false)
  exact PosB_God_only_at_true.2 hAtFalse

/-- **Countermodel B (local T3 fails).** Refl+trans chain, A1–A5, ◇∃G at
source but not □∃G — euclidean/symmetry was load-bearing for local T3. -/
theorem countermodel_B_local_T3_fails :
    Reflexive R_chain ∧ Transitive R_chain ∧
    ¬ Symmetric R_chain ∧ ¬ Euclidean R_chain ∧
    A1R PosB ∧ A2R PosB ∧ A3R PosB ∧ A5R R_chain PosB ∧
    possibleR R_chain (fun v => ∃ x : Ind1, GodLike PosB v x) false ∧
    ¬ necessaryR R_chain (fun v => ∃ x : Ind1, GodLike PosB v x) false :=
  ⟨R_chain_reflexive, R_chain_transitive, R_chain_not_symmetric,
    R_chain_not_euclidean, PosB_A1, PosB_A2, PosB_A3, PosB_A5,
    PosB_diamond_at_source, PosB_box_fails_at_source⟩

/-! ## Result C: TB path — strict weakening of S5Frame (not a T3 countermodel) -/

/-- Three worlds arranged as an undirected path `a—b—c`. -/
inductive W3 where
  | a | b | c
  deriving DecidableEq, Repr

/-- Reflexive symmetric closure of the path edges `{a—b, b—c}`. -/
def R_path : Access W3 := fun w v =>
  match w, v with
  | .a, .a | .b, .b | .c, .c => True
  | .a, .b | .b, .a => True
  | .b, .c | .c, .b => True
  | _, _ => False

theorem R_path_reflexive : Reflexive R_path := by
  intro w
  cases w <;> simp [R_path]

theorem R_path_symmetric : Symmetric R_path := by
  intro w v hwv
  cases w <;> cases v <;> simp_all [R_path]

theorem R_path_tb : TBFrame R_path :=
  ⟨R_path_reflexive, R_path_symmetric⟩

theorem R_path_not_transitive : ¬ Transitive R_path := by
  intro hTrans
  -- a R b and b R c, but not a R c
  have : R_path .a .c :=
    hTrans .a .b .c (by simp [R_path]) (by simp [R_path])
  simp [R_path] at this

theorem R_path_not_euclidean : ¬ Euclidean R_path := by
  intro hEu
  -- b R a and b R c ⇒ should get a R c
  have : R_path .a .c :=
    hEu .b .a .c (by simp [R_path]) (by simp [R_path])
  simp [R_path] at this

theorem R_path_not_s5 : ¬ S5Frame R_path := by
  intro hS5
  exact R_path_not_euclidean hS5.2

/-- **Strictness witness C.** `R_path` is TB (hence Brouwerian) but not
S5Frame. Local T3 still follows from `local_T3_of_Symmetric` on any such
frame; S5Frame was a stronger-than-needed packaging. -/
theorem strictness_C_TB_not_S5 :
    TBFrame R_path ∧
    Symmetric R_path ∧
    Brouwerian R_path ∧
    ¬ Transitive R_path ∧
    ¬ Euclidean R_path ∧
    ¬ S5Frame R_path :=
  ⟨R_path_tb, R_path_symmetric, R_path_symmetric,
    R_path_not_transitive, R_path_not_euclidean, R_path_not_s5⟩

/-- Feynman check: a pure-symmetric (not necessarily reflexive) 2-cycle is
Brouwerian and not reflexive — still enough for `local_T3_of_Symmetric`. -/
def R_swap : Access W2 := fun w v => w ≠ v

theorem R_swap_symmetric : Symmetric R_swap := by
  intro w v hwv
  -- hwv : w ≠ v; need v ≠ w
  simp [R_swap] at hwv ⊢
  exact Ne.symm hwv

theorem R_swap_not_reflexive : ¬ Reflexive R_swap := by
  intro hRefl
  have : false ≠ false := hRefl false
  exact this rfl

theorem R_swap_brouwerian_not_TB :
    Brouwerian R_swap ∧ ¬ Reflexive R_swap ∧ ¬ TBFrame R_swap := by
  refine ⟨R_swap_symmetric, R_swap_not_reflexive, ?_⟩
  intro hTB
  exact R_swap_not_reflexive hTB.1

end Countermodel
end GodelOntological
