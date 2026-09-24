import GodelOntological.CollapseWRP

/-
# Frame residue under world-relative Positive

## Literature cut (before the Lean claim)

Kanckos & Woltzenlogel Paleo show that Scott’s ontological argument can be
carried in **KB** (symmetry), and that S5 is not required
(*Studia Logica* 105(3), 2017, DOI 10.1007/s11225-016-9700-1).
Benzmüller & Scott likewise note that their Theorem Th3 uses symmetry of
accessibility (`Rsymm`), not the rest of S5
(*Monatshefte für Mathematik*, 2025, DOI 10.1007/s00605-025-02078-x).

Their separate question — whether **S4** proves Th3 for Gödel’s variant with
the **adapted** essence (their Fig. 7) — is not this file. These tables use
Scott-style `EssenceW` / `A1W`–`A5W` in the thin `PosW` encoding.

## What this file checks

Positive direction (already proved, restated as one package): **Symmetric**
+ valid A1W–A5W ⇒ global T3, local T3, `ModalCollapseR`, and ContingentR
impossible at every world. That direction is a **rediscovery** of the KB fact
above, inside this encoding (`symmetric_WRP_package`).

Negative direction: finite frames where dropping Symmetric makes global T3,
local T3, or collapse fail, while the WRP axioms still hold — or where the
axiom package cannot hold at all. Those tables are **desk packaging** in this
encoding. Not a priority claim. Not an answer to the Monatshefte Fig. 7 open.
-/

namespace GodelOntological
namespace WRPFrameResidue

open CountermodelA_WRP
open CollapseWRP

/-! ## What survives under Symmetric -/

/-- **WRP residue, positive direction.** Symmetric + valid A1W–A5W. -/
theorem symmetric_WRP_package {W Ind : Type} (R : Access W)
    (hSym : Symmetric R) (P : PosW W Ind)
    (hA1 : validW (A1W P))
    (hA2 : validW (A2W R P))
    (hA3 : validW (A3W P))
    (hA4 : validW (A4W R P))
    (hA5 : validW (A5W R P)) :
    (∀ w : W, ∃ x : Ind, GodLikeW P w x) ∧
    (∀ w : W, necessaryR R (fun v => ∃ x : Ind, GodLikeW P v x) w) ∧
    ModalCollapseR R ∧
    (∀ (φ : W → Prop) (w : W), ¬ ContingentR R φ w) := by
  refine ⟨
    global_T3W_of_Symmetric R hSym P hA1 hA2 hA3 hA4 hA5,
    ?_,
    ModalCollapseR_of_Symmetric R hSym P hA1 hA2 hA3 hA4 hA5,
    fun φ w =>
      ContingentR_impossible_of_Symmetric R hSym P hA1 hA2 hA3 hA4 hA5 φ w⟩
  intro w
  exact exists_God_implies_necessaryW R P (hA1 w) (hA4 w) (hA5 w)
    (global_T3W_of_Symmetric R hSym P hA1 hA2 hA3 hA4 hA5 w)

/-! ## Dead-end: A1–A3 already require a successor -/

/-- A1+A2+A3 at `w` produce `possibleR (∃ GodLikeW)`, hence a successor. -/
theorem A123_implies_serial {W Ind : Type} (R : Access W) (P : PosW W Ind)
    {w : W} (hA1 : A1W P w) (hA2 : A2W R P w) (hA3 : A3W P w) :
    ∃ v : W, R w v := by
  obtain ⟨v, hv, _⟩ := CW R P hA1 hA2 hA3
  exact ⟨v, hv⟩

/-- Empty accessibility on a point: no `PosW` satisfies A1–A3. -/
def R_empty : Access Unit := fun _ _ => False

theorem no_A123_on_empty (P : PosW Unit Unit) :
    ¬ (A1W P () ∧ A2W R_empty P () ∧ A3W P ()) := by
  intro ⟨hA1, hA2, hA3⟩
  obtain ⟨v, hv⟩ := A123_implies_serial R_empty P hA1 hA2 hA3
  cases v
  exact hv

/-! ## Irreflexive 2-cycle: Symmetric, but A1–A4 have no model -/

/-- On `Bool` with `R w v ↔ w ≠ v` (symmetric, not reflexive), valid A1W–A4W
is impossible for every individual type. The conditional Symmetric theorems
remain true; this frame supplies no witness. -/
theorem R_swap_no_valid_A1234 {Ind : Type}
    (P : PosW Countermodel.W2 Ind) :
    ¬ (validW (A1W P) ∧ validW (A2W Countermodel.R_swap P) ∧
       validW (A3W P) ∧ validW (A4W Countermodel.R_swap P)) := by
  intro ⟨hA1, hA2, hA3, hA4⟩
  have hGodTrue : ∃ x : Ind, GodLikeW P true x := by
    obtain ⟨v, hv, hEx⟩ :=
      CW Countermodel.R_swap P (hA1 false) (hA2 false) (hA3 false)
    cases v
    · exact absurd rfl hv
    · exact hEx
  have hGodFalse : ∃ x : Ind, GodLikeW P false x := by
    obtain ⟨v, hv, hEx⟩ :=
      CW Countermodel.R_swap P (hA1 true) (hA2 true) (hA3 true)
    cases v
    · exact hEx
    · exact absurd rfl hv
  obtain ⟨xt, hxt⟩ := hGodTrue
  obtain ⟨xf, hxf⟩ := hGodFalse
  let φ : Property Countermodel.W2 Ind := fun w _ => w = false
  have hNotPtrue : ¬ P true φ := by
    intro hP
    have : true = false := hxt φ hP
    exact Bool.noConfusion this
  have hNotPfalseNeg : ¬ P false (propNeg φ) := by
    intro hP
    have hneg : propNeg φ false xf := hxf (propNeg φ) hP
    simp [propNeg, φ] at hneg
  have hPfalse : P false φ := by
    apply Classical.byContradiction
    intro h
    exact hNotPfalseNeg ((hA1 false φ).mpr h)
  have hPtrue : P true φ :=
    hA4 false φ hPfalse true (by
      intro hEq
      exact Bool.noConfusion hEq)
  exact hNotPtrue hPtrue

/-! ## Principal positivity at a seen singleton sink -/

/-- `PosPivot s φ` iff `φ` holds of `()` at the pivot `s` (world-independent). -/
def PosPivot {W : Type} (s : W) : PosW W Unit :=
  fun _ φ => φ s ()

theorem PosPivot_GodLike {W : Type} (s w : W) (x : Unit) :
    GodLikeW (PosPivot s) w x ↔ w = s := by
  cases x
  constructor
  · intro hg
    let φ : Property W Unit := fun v _ => v = s
    have hP : PosPivot s w φ := rfl
    exact hg φ hP
  · intro hw φ hP
    rw [hw]
    exact hP

theorem PosPivot_A1 {W : Type} (s : W) : validW (A1W (PosPivot s)) := by
  intro w φ
  constructor
  · intro hNeg hPos
    exact hNeg hPos
  · intro hNot
    exact hNot

theorem PosPivot_A2 {W : Type} (R : Access W) (s : W)
    (hSee : ∀ w : W, R w s) : validW (A2W R (PosPivot s)) := by
  intro w φ ψ hP hEnt
  exact hEnt s (hSee w) () hP

theorem PosPivot_A3 {W : Type} (s : W) : validW (A3W (PosPivot s)) := by
  intro w
  exact (PosPivot_GodLike s s ()).mpr rfl

theorem PosPivot_A4 {W : Type} (R : Access W) (s : W) :
    validW (A4W R (PosPivot s)) := by
  intro _ φ hP _ _
  exact hP

theorem PosPivot_NEW_sink {W : Type} (R : Access W) (s : W)
    (hSink : ∀ v : W, R s v → v = s) : NEW R s () := by
  intro φ hEss v hv
  have hv' : v = s := hSink v hv
  refine ⟨(), ?_⟩
  have hφ : φ s () := hEss.1
  simpa [hv'] using hφ

theorem PosPivot_A5 {W : Type} (R : Access W) (s : W)
    (hSink : ∀ v : W, R s v → v = s) : validW (A5W R (PosPivot s)) := by
  intro _
  exact PosPivot_NEW_sink R s hSink

theorem PosPivot_not_global {W : Type} (s w : W) (hw : w ≠ s) :
    ¬ (∀ u : W, ∃ x : Unit, GodLikeW (PosPivot s) u x) := by
  intro hAll
  obtain ⟨x, hx⟩ := hAll w
  exact hw ((PosPivot_GodLike s w x).mp hx)

theorem PosPivot_local_gap {W : Type} (R : Access W) (s w u : W)
    (hS : R w s) (hU : R w u) (hu : u ≠ s) :
    possibleR R (fun v => ∃ x : Unit, GodLikeW (PosPivot s) v x) w ∧
    ¬ necessaryR R (fun v => ∃ x : Unit, GodLikeW (PosPivot s) v x) w := by
  refine ⟨⟨s, hS, (), (PosPivot_GodLike s s ()).mpr rfl⟩, ?_⟩
  intro hNec
  obtain ⟨x, hx⟩ := hNec u hU
  exact hu ((PosPivot_GodLike s u x).mp hx)

theorem PosPivot_Contingent_at {W : Type} (R : Access W) (w u : W)
    (hR : R w u) (hu : u ≠ w) :
    ContingentR R (fun v => v = w) w := by
  refine ⟨rfl, ⟨u, hR, ?_⟩⟩
  intro hEq
  exact hu hEq

theorem PosPivot_collapse_fails {W : Type} (R : Access W) (w u : W)
    (hR : R w u) (hu : u ≠ w) :
    ¬ ModalCollapseAt R w := by
  intro hMC
  exact ContingentR_impossible_of_collapseAt R hMC (fun v => v = w)
    (PosPivot_Contingent_at R w u hR hu)

theorem PosPivot_collapse_at_sink {W : Type} (R : Access W) (s : W)
    (hSink : ∀ v : W, R s v → v = s) :
    ModalCollapseAt R s :=
  ModalCollapseAt_of_GodW R (PosPivot s)
    (PosPivot_A1 s s) (PosPivot_A4 R s s) (PosPivot_A5 R s hSink s)
    ⟨(), (PosPivot_GodLike s s ()).mpr rfl⟩

/-! ## S4 chain: reflexive + transitive, not symmetric

`Countermodel.R_chain`: `false` sees both worlds; `true` sees only itself.
-/

theorem R_chain_sees_sink (w : Countermodel.W2) :
    Countermodel.R_chain w true := by
  cases w <;> simp [Countermodel.R_chain]

theorem R_chain_sink (v : Countermodel.W2) :
    Countermodel.R_chain true v → v = true := by
  cases v <;> simp [Countermodel.R_chain]

/-- **S4 (refl+trans), not symmetric.** Valid WRP A1–A5, God only at `true`.
Global T3 fails. -/
theorem chain_S4_global_T3_fails :
    Reflexive Countermodel.R_chain ∧
    Transitive Countermodel.R_chain ∧
    ¬ Symmetric Countermodel.R_chain ∧
    ¬ Euclidean Countermodel.R_chain ∧
    validW (A1W (PosPivot true)) ∧
    validW (A2W Countermodel.R_chain (PosPivot true)) ∧
    validW (A3W (PosPivot true)) ∧
    validW (A4W Countermodel.R_chain (PosPivot true)) ∧
    validW (A5W Countermodel.R_chain (PosPivot true)) ∧
    ¬ (∀ w : Countermodel.W2, ∃ x : Unit, GodLikeW (PosPivot true) w x) :=
  ⟨Countermodel.R_chain_reflexive, Countermodel.R_chain_transitive,
    Countermodel.R_chain_not_symmetric, Countermodel.R_chain_not_euclidean,
    PosPivot_A1 true, PosPivot_A2 Countermodel.R_chain true R_chain_sees_sink,
    PosPivot_A3 true, PosPivot_A4 Countermodel.R_chain true,
    PosPivot_A5 Countermodel.R_chain true R_chain_sink,
    PosPivot_not_global true false Bool.false_ne_true⟩

/-- Local T3 fails at the source: `◇∃G` via the sink, not `□∃G`. -/
theorem chain_S4_local_T3_fails :
    possibleR Countermodel.R_chain
      (fun v => ∃ x : Unit, GodLikeW (PosPivot true) v x) false ∧
    ¬ necessaryR Countermodel.R_chain
      (fun v => ∃ x : Unit, GodLikeW (PosPivot true) v x) false :=
  PosPivot_local_gap Countermodel.R_chain true false false
    (R_chain_sees_sink false) (Countermodel.R_chain_reflexive false)
    Bool.false_ne_true

theorem chain_S4_ContingentR_survives :
    ContingentR Countermodel.R_chain (fun v => v = false) false :=
  PosPivot_Contingent_at Countermodel.R_chain false true
    (R_chain_sees_sink false) Bool.false_ne_true.symm

theorem chain_S4_collapse_fails_at_source :
    ¬ ModalCollapseAt Countermodel.R_chain false :=
  PosPivot_collapse_fails Countermodel.R_chain false true
    (R_chain_sees_sink false) Bool.false_ne_true.symm

theorem chain_S4_collapse_at_sink :
    ModalCollapseAt Countermodel.R_chain true :=
  PosPivot_collapse_at_sink Countermodel.R_chain true R_chain_sink

/-! ## Reflexive, not transitive / not symmetric / not Euclidean -/

inductive W4 where
  | a | b | c | s
  deriving DecidableEq, Repr

/-- `a → b → c`, and every world sees the singleton sink `s` and itself.
Not transitive (`a` does not see `c`), not symmetric, not Euclidean. -/
def R_fork : Access W4 := fun w v =>
  match w, v with
  | _, .s => True
  | .a, .a | .b, .b | .c, .c => True
  | .a, .b => True
  | .b, .c => True
  | _, _ => False

theorem R_fork_reflexive : Reflexive R_fork := by
  intro w
  cases w <;> simp [R_fork]

theorem R_fork_sees_sink (w : W4) : R_fork w .s := by
  cases w <;> simp [R_fork]

theorem R_fork_sink (v : W4) : R_fork .s v → v = .s := by
  cases v <;> simp [R_fork]

theorem R_fork_not_symmetric : ¬ Symmetric R_fork := by
  intro hS
  have : R_fork .b .a := hS .a .b (by simp [R_fork])
  simp [R_fork] at this

theorem R_fork_not_transitive : ¬ Transitive R_fork := by
  intro hT
  have : R_fork .a .c :=
    hT .a .b .c (by simp [R_fork]) (by simp [R_fork])
  simp [R_fork] at this

theorem R_fork_not_euclidean : ¬ Euclidean R_fork := by
  intro hE
  have : R_fork .s .b :=
    hE .a .s .b (by simp [R_fork]) (by simp [R_fork])
  simp [R_fork] at this

theorem fork_global_T3_fails :
    Reflexive R_fork ∧
    ¬ Symmetric R_fork ∧
    ¬ Transitive R_fork ∧
    ¬ Euclidean R_fork ∧
    validW (A1W (PosPivot W4.s)) ∧
    validW (A2W R_fork (PosPivot W4.s)) ∧
    validW (A3W (PosPivot W4.s)) ∧
    validW (A4W R_fork (PosPivot W4.s)) ∧
    validW (A5W R_fork (PosPivot W4.s)) ∧
    ¬ (∀ w : W4, ∃ x : Unit, GodLikeW (PosPivot W4.s) w x) := by
  refine ⟨R_fork_reflexive, R_fork_not_symmetric, R_fork_not_transitive,
    R_fork_not_euclidean, PosPivot_A1 W4.s,
    PosPivot_A2 R_fork W4.s R_fork_sees_sink, PosPivot_A3 W4.s,
    PosPivot_A4 R_fork W4.s, PosPivot_A5 R_fork W4.s R_fork_sink, ?_⟩
  exact PosPivot_not_global W4.s W4.a (by intro h; cases h)

theorem fork_local_T3_fails :
    possibleR R_fork (fun v => ∃ x : Unit, GodLikeW (PosPivot W4.s) v x) .a ∧
    ¬ necessaryR R_fork (fun v => ∃ x : Unit, GodLikeW (PosPivot W4.s) v x) .a :=
  PosPivot_local_gap R_fork W4.s .a .a
    (R_fork_sees_sink .a) (R_fork_reflexive .a) (by intro h; cases h)

theorem fork_ContingentR_survives :
    ContingentR R_fork (fun v => v = W4.a) .a :=
  PosPivot_Contingent_at R_fork .a .b (by simp [R_fork]) (by intro h; cases h)

theorem fork_collapse_fails_at_a :
    ¬ ModalCollapseAt R_fork .a :=
  PosPivot_collapse_fails R_fork .a .b (by simp [R_fork]) (by intro h; cases h)

/-! ## Euclidean + serial + transitive, not reflexive, not symmetric

Everyone sees only `true`. Local T3 holds; global T3 fails.
-/

def R_to_true : Access Bool := fun _ v => v = true

theorem R_to_true_serial : Serial R_to_true := fun _ => ⟨true, rfl⟩

theorem R_to_true_transitive : Transitive R_to_true := by
  intro _ _ u _ hvu
  simpa [R_to_true] using hvu

theorem R_to_true_euclidean : Euclidean R_to_true := by
  intro _ _ u _ hu
  simpa [R_to_true] using hu

theorem R_to_true_not_reflexive : ¬ Reflexive R_to_true := by
  intro h
  have : false = true := by simpa [R_to_true] using h false
  exact Bool.noConfusion this

theorem R_to_true_not_symmetric : ¬ Symmetric R_to_true := by
  intro h
  have : false = true := by
    simpa [R_to_true] using h false true rfl
  exact Bool.noConfusion this

theorem R_to_true_sees (w : Bool) : R_to_true w true := rfl

theorem R_to_true_sink (v : Bool) : R_to_true true v → v = true :=
  fun h => h

theorem to_true_global_T3_fails :
    Serial R_to_true ∧
    Transitive R_to_true ∧
    Euclidean R_to_true ∧
    ¬ Reflexive R_to_true ∧
    ¬ Symmetric R_to_true ∧
    validW (A1W (PosPivot true)) ∧
    validW (A2W R_to_true (PosPivot true)) ∧
    validW (A3W (PosPivot true)) ∧
    validW (A4W R_to_true (PosPivot true)) ∧
    validW (A5W R_to_true (PosPivot true)) ∧
    ¬ (∀ w : Bool, ∃ x : Unit, GodLikeW (PosPivot true) w x) :=
  ⟨R_to_true_serial, R_to_true_transitive, R_to_true_euclidean,
    R_to_true_not_reflexive, R_to_true_not_symmetric,
    PosPivot_A1 true, PosPivot_A2 R_to_true true R_to_true_sees,
    PosPivot_A3 true, PosPivot_A4 R_to_true true,
    PosPivot_A5 R_to_true true R_to_true_sink,
    PosPivot_not_global true false Bool.false_ne_true⟩

/-- On this frame every successor is the sink, so local T3 holds at every world
even though the frame is not symmetric and global T3 fails. -/
theorem to_true_local_T3_holds (w : Bool) :
    possibleR R_to_true (fun v => ∃ x : Unit, GodLikeW (PosPivot true) v x) w →
    necessaryR R_to_true (fun v => ∃ x : Unit, GodLikeW (PosPivot true) v x) w := by
  intro _ v hv
  have hv' : v = true := by simpa [R_to_true] using hv
  exact ⟨(), (PosPivot_GodLike true v ()).mpr hv'⟩

theorem to_true_ContingentR_survives :
    ContingentR R_to_true (fun v => v = false) false :=
  PosPivot_Contingent_at R_to_true false true rfl Bool.false_ne_true.symm

theorem to_true_collapse_fails_at_false :
    ¬ ModalCollapseAt R_to_true false :=
  PosPivot_collapse_fails R_to_true false true rfl Bool.false_ne_true.symm

theorem to_true_collapse_at_sink :
    ModalCollapseAt R_to_true true :=
  PosPivot_collapse_at_sink R_to_true true R_to_true_sink

end WRPFrameResidue
end GodelOntological
