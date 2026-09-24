import GodelOntological.Scott

/-
# Russell cuts / P042 — dependency split for Gödel–Scott

Bertrand Russell asked which fragments of the Scott chain survive when A3 or A5
is dropped. This file **documents and typechecks** that split. It does **not**
restore A3 or A5 as ambient axioms, proved lemmas, or “secure” foundations.

| Cut | Keep | Drop | What still holds | What dies |
| --- | --- | --- | --- | --- |
| **1** | A1, A2, A3 | A5 | T1, C (possibly God) | T3, `exists_God_implies_necessary` |
| **2** | A1, A2, A5 | A3 | T1 (arbitrary positive φ); reflection *if* a local God-like is assumed | C, T3 (no possibly-God or necessarily-God without A3) |

Foundation is **not** restored: necessity of God-likeness still requires A5 in
the type; possibility of God-likeness still requires A3 in the type.
-/

namespace GodelOntological

/-! ## Cut 1 — drop A5, keep A1–A3

T1 and C already depend only on A1–A3 (resp. A1–A2 for T1) in `Scott.lean`.
The theorems below re-export that fact under unmistakable names.

**Ledger note.** No theorem in this cut has type
`A1 → A2 → A3 → □∃x GodLike`. Necessity of God-likeness requires A5 in the
type (see `exists_God_implies_necessary` / `T3_necessarily_God` in Scott.lean).
We deliberately do **not** prove T3 or `exists_God_implies_necessary` here
without A5.
-/

/-- **Cut 1 / T1.** Positive properties are possibly exemplified — from A1+A2 only
(A5 unused). Same statement as `T1_positive_possibly_exemplified`. -/
theorem cut1_T1_without_A5 {W Ind : Type}
    (Positive : Property W Ind → Prop)
    (hA1 : A1 Positive) (hA2 : A2 Positive)
    (φ : Property W Ind) (hP : Positive φ) :
    ◇ (fun w : W => ∃ x : Ind, φ w x) :=
  T1_positive_possibly_exemplified Positive hA1 hA2 φ hP

/-- **Cut 1 / C.** Possibly a God-like being exists — from A1+A2+A3 only
(A5 unused). Same statement as `C_possibly_God`. -/
theorem cut1_C_without_A5 {W Ind : Type}
    (Positive : Property W Ind → Prop)
    (hA1 : A1 Positive) (hA2 : A2 Positive) (hA3 : A3 Positive) :
    ◇ (fun w : W => ∃ x : Ind, GodLike Positive w x) :=
  C_possibly_God Positive hA1 hA2 hA3

/-! ## Cut 2 — drop A3, keep A1–A2+A5

Without A3, God-likeness is not known to be positive, so `C_possibly_God` and
`T3_necessarily_God` are unavailable (their types mention A3). A5 alone does
not yield possibly-God or necessarily-God.

T1 for an *arbitrary* positive φ still follows from A1+A2. Separately, the
reflection step (`exists_God_implies_necessary`) needs only A1+A5 once a local
God-like is assumed — that shows A5 fuels reflection while A3 fuels possibility.
-/

/-- **Cut 2 / T1.** T1 still from A1+A2 for an arbitrary positive φ (A3 unused). -/
theorem cut2_T1_without_A3 {W Ind : Type}
    (Positive : Property W Ind → Prop)
    (hA1 : A1 Positive) (hA2 : A2 Positive)
    (φ : Property W Ind) (hP : Positive φ) :
    ◇ (fun w : W => ∃ x : Ind, φ w x) :=
  T1_positive_possibly_exemplified Positive hA1 hA2 φ hP

/-- **Cut 2 / reflection.** Local God-likeness + A1+A5 still yields □∃ GodLike
(A3 unused). Shows A5 fuels the reflection step; A3 is what would fuel
possibility of God-likeness (`C_possibly_God`), which is **not** proved here. -/
theorem cut2_reflection_without_A3 {W Ind : Type}
    (Positive : Property W Ind → Prop)
    (hA1 : A1 Positive) (hA5 : A5 Positive)
    {w : W} (hEx : ∃ x : Ind, GodLike Positive w x) :
    □ (fun v : W => ∃ y : Ind, GodLike Positive v y) :=
  exists_God_implies_necessary Positive hA1 hA5 hEx

end GodelOntological
