import GodelOntological.CountermodelA_WRP
import GodelOntological.Collapse

/-
# WRP modal collapse and ContingentR

## Literature cut (before the Lean claim)

Sobel showed that Scott-style Gödel premises yield modal collapse `φ → □φ`
(Sobel 1987; *Logic and Theism* 2004). Benzmüller & Fuenmayor re-checked this
for Scott’s variant in Isabelle/HOL HOML, where positivity is intensional
(world-relative type), and showed that Anderson’s and Fitting’s emendations
avoid it (arXiv:1910.08955; BSL 49(2) 2020, DOI 10.18778/0138-0680.2020.08).

That Scott-side collapse is already in the literature. The theorems below are a
**rediscovery**: the same consequence, checked in this thin world-relative
(`PosW`) encoding. They are not a priority claim.

## What is proved here (WRP, not rigid Positive)

`ModalCollapseAt` / `ContingentR` are the R-relative notions from `Collapse.lean`.

* **Local, at a God-world.** `A1W` + `A4W` + `A5W` at `w` and `∃ GodLikeW` at `w`
  give `ModalCollapseAt R w`. Symmetry is not required. (Rigid `Collapse.lean`
  needs only A1+A5 here, because rigid Positive absorbs A4.)
* **At every world, along `R`.** `Symmetric R` + `validW` of A1W–A5W give
  `ModalCollapseR R`, hence `ContingentR` is impossible at every world.
  `A2W` and `A3W` are used only to obtain God at every world
  (`global_T3W_of_Symmetric`); the collapse step itself is A1W+A4W+A5W.
* **Sobel form `φ → □φ`.** That is `ModalCollapse` (`□` = truth at every world).
  It follows when `R` is `Universal`. Symmetry alone does not give it:
  on `idRel`, R-collapse and “no ContingentR” hold, and a proposition may still
  differ at an inaccessible world (`wrp_idRel_R_collapse_not_sobel`).

So the named claim is: under **WRP**, Symmetric + valid A1–A5 ⇒ collapse
**at every world along `R`**, and ContingentR is **impossible everywhere**.
It is not the cross-cluster Sobel form unless `R` is universal.
-/

namespace GodelOntological
namespace CollapseWRP

open CountermodelA_WRP

/-! ## Local collapse at a WRP God-world -/

/-- At a world where some individual is `GodLikeW`, every truth is `R`-necessary.
Needs A1, A4, and A5 **at that world**. No frame hypothesis. -/
theorem local_collapse_of_GodW {W Ind : Type} (R : Access W) (P : PosW W Ind)
    {w : W} (hA1 : A1W P w) (hA4 : A4W R P w) (hA5 : A5W R P w)
    (hEx : ∃ x : Ind, GodLikeW P w x)
    (φ : W → Prop) (hφ : φ w) :
    necessaryR R φ w := by
  obtain ⟨x, hx⟩ := hEx
  have hEss : EssenceW R (GodLikeW P) w x := T2W R P hA1 hA4 hx
  have hNE : NEW R w x := godlike_has_NEW R P hA5 hx
  have hBoxG :
      necessaryR R (fun v => ∃ y : Ind, GodLikeW P v y) w :=
    hNE (GodLikeW P) hEss
  have hψ : constProp (Ind := Ind) φ w x := hφ
  have hTrans :
      necessaryR R
        (fun v => ∀ y : Ind,
          GodLikeW P v y → constProp (Ind := Ind) φ v y) w :=
    hEss.2 (constProp (Ind := Ind) φ) hψ
  intro v hv
  obtain ⟨y, hy⟩ := hBoxG v hv
  exact hTrans v hv y hy

/-- **Local (WRP).** Collapse at a God-world. -/
theorem ModalCollapseAt_of_GodW {W Ind : Type} (R : Access W) (P : PosW W Ind)
    {w : W} (hA1 : A1W P w) (hA4 : A4W R P w) (hA5 : A5W R P w)
    (hEx : ∃ x : Ind, GodLikeW P w x) :
    ModalCollapseAt R w :=
  fun φ hφ => local_collapse_of_GodW R P hA1 hA4 hA5 hEx φ hφ

/-- ContingentR is impossible at a WRP God-world. -/
theorem ContingentR_impossible_at_GodW {W Ind : Type} (R : Access W)
    (P : PosW W Ind) {w : W}
    (hA1 : A1W P w) (hA4 : A4W R P w) (hA5 : A5W R P w)
    (hEx : ∃ x : Ind, GodLikeW P w x) (φ : W → Prop) :
    ¬ ContingentR R φ w :=
  ContingentR_impossible_of_collapseAt R
    (ModalCollapseAt_of_GodW R P hA1 hA4 hA5 hEx) φ

/-! ## Symmetric + valid A1W–A5W ⇒ collapse at every world -/

/-- **Global along `R` (WRP).** Symmetric + globally valid A1–A5
⇒ `ModalCollapseAt` at every world. God exists everywhere by
`global_T3W_of_Symmetric`; each such world collapses. -/
theorem ModalCollapseR_of_Symmetric {W Ind : Type} (R : Access W)
    (hSym : Symmetric R) (P : PosW W Ind)
    (hA1 : validW (A1W P))
    (hA2 : validW (A2W R P))
    (hA3 : validW (A3W P))
    (hA4 : validW (A4W R P))
    (hA5 : validW (A5W R P)) :
    ModalCollapseR R := by
  intro w
  exact ModalCollapseAt_of_GodW R P (hA1 w) (hA4 w) (hA5 w)
    (global_T3W_of_Symmetric R hSym P hA1 hA2 hA3 hA4 hA5 w)

/-- **ContingentR is impossible at every world** under Symmetric + valid WRP A1–A5.
This is the global (all-worlds) reading of “no free-will-as-contingency along `R`”.
It does not by itself identify truths across disconnected clusters. -/
theorem ContingentR_impossible_of_Symmetric {W Ind : Type} (R : Access W)
    (hSym : Symmetric R) (P : PosW W Ind)
    (hA1 : validW (A1W P))
    (hA2 : validW (A2W R P))
    (hA3 : validW (A3W P))
    (hA4 : validW (A4W R P))
    (hA5 : validW (A5W R P))
    (φ : W → Prop) (w : W) :
    ¬ ContingentR R φ w :=
  ContingentR_impossible_of_collapseAt R
    (ModalCollapseR_of_Symmetric R hSym P hA1 hA2 hA3 hA4 hA5 w) φ

theorem ContingentAct_impossible_of_Symmetric {W Ind : Type} (R : Access W)
    (hSym : Symmetric R) (P : PosW W Ind)
    (hA1 : validW (A1W P))
    (hA2 : validW (A2W R P))
    (hA3 : validW (A3W P))
    (hA4 : validW (A4W R P))
    (hA5 : validW (A5W R P))
    (α : Property W Ind) (w : W) (x : Ind) :
    ¬ ContingentAct R α w x :=
  ContingentR_impossible_of_Symmetric R hSym P hA1 hA2 hA3 hA4 hA5
    (fun v => α v x) w

/-- Same R-collapse under `S5Frame` (via symmetry). -/
theorem ModalCollapseR_of_S5 {W Ind : Type} (R : Access W)
    (hS5 : S5Frame R) (P : PosW W Ind)
    (hA1 : validW (A1W P))
    (hA2 : validW (A2W R P))
    (hA3 : validW (A3W P))
    (hA4 : validW (A4W R P))
    (hA5 : validW (A5W R P)) :
    ModalCollapseR R :=
  ModalCollapseR_of_Symmetric R hS5.symmetric P hA1 hA2 hA3 hA4 hA5

/-! ## Sobel form needs Universal, not merely Symmetric -/

/-- When `R` is universal, WRP collapse is Sobel’s `φ → □φ`
(`ModalCollapse`, `□` = truth at every world). -/
theorem ModalCollapse_of_Universal_WRP {W Ind : Type} (R : Access W)
    (hU : Universal R) (P : PosW W Ind)
    (hA1 : validW (A1W P))
    (hA2 : validW (A2W R P))
    (hA3 : validW (A3W P))
    (hA4 : validW (A4W R P))
    (hA5 : validW (A5W R P)) :
    ModalCollapse (W := W) := by
  intro φ w hφ v
  exact ModalCollapseR_of_Symmetric R hU.symmetric P hA1 hA2 hA3 hA4 hA5
    w φ hφ v (hU w v)

/-- Packaging witness (WRP, `PosLocal` on `idRel`).
Symmetric + valid A1–A5 give R-collapse and kill ContingentR, but not Sobel
collapse across the two isolated worlds: `(· = false)` holds at `false` and
fails at `true`, which is not `R`-accessible. -/
theorem wrp_idRel_R_collapse_not_sobel :
    ModalCollapseR Countermodel.R_id ∧
    (∀ (φ : Countermodel.W2 → Prop) (w : Countermodel.W2),
      ¬ ContingentR Countermodel.R_id φ w) ∧
    ¬ ModalCollapse (W := Countermodel.W2) := by
  have hMC : ModalCollapseR Countermodel.R_id :=
    ModalCollapseR_of_S5 Countermodel.R_id Countermodel.R_id_s5 PosLocal
      PosLocal_A1 PosLocal_A2 PosLocal_A3 PosLocal_A4 PosLocal_A5
  refine ⟨hMC, ?_, ?_⟩
  · intro φ w
    exact ContingentR_impossible_of_collapseAt Countermodel.R_id (hMC w) φ
  · intro hSobel
    have : (true : Countermodel.W2) = false :=
      hSobel (fun w => w = false) false rfl true
    exact Bool.noConfusion this

end CollapseWRP
end GodelOntological
