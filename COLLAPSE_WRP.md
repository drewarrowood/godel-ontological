# WRP collapse / ContingentR

Desk check of modal collapse under **world-relative** Positive (`PosW`), in the thin
encoding of `GodelOntological/CollapseWRP.lean`. Not a priority claim.

Date: 2026-09-24 (America/New_York). Toolchain: Lean 4.34.0.

---

## Literature cut (before the Lean claim)

Sobel showed that Scott-style Gödel premises yield modal collapse `φ → □φ`
(Sobel 1987; *Logic and Theism*, 2004). Benzmüller & Fuenmayor encoded Scott’s,
Anderson’s, and Fitting’s variants in Isabelle/HOL. Scott’s variant entails
collapse; Anderson’s and Fitting’s do not (arXiv:1910.08955; *Bulletin of the
Section of Logic* 49(2), 2020, DOI 10.18778/0138-0680.2020.08). Their Scott
`P` is intensional (a predicate on properties in HOML), i.e. the world-relative
reading, not this package’s rigid `Positive : Property → Prop`.

The statements below are a **rediscovery** of that Scott-side collapse, checked
here under `PosW` and `validW` of A1W–A5W. Anderson / Fitting repairs are not
in this note.

---

## Signature

WRP as in `GodelOntological/CountermodelA_WRP.lean`: `PosW`, `GodLikeW`,
`A1W`–`A5W`, `validW`. Collapse vocabulary as in `Collapse.lean`:

| Name | Meaning |
| --- | --- |
| `ModalCollapseAt R w` | every truth at `w` is `necessaryR` at `w` |
| `ModalCollapseR R` | `ModalCollapseAt` at every world |
| `ModalCollapse` | Sobel form: `φ w → □ φ` with `□` = truth at **every** world |
| `ContingentR R φ w` | `φ` true at `w` and false at some `R`-successor |

---

## What was proved (0 `sorry`)

| Theorem | Frame / axioms | Result |
| --- | --- | --- |
| `local_collapse_of_GodW` / `ModalCollapseAt_of_GodW` | A1W+A4W+A5W at `w`, plus `∃ GodLikeW` at `w`. **No** Symmetric | collapse **at that God-world** |
| `ContingentR_impossible_at_GodW` | same | ContingentR impossible **at that world** |
| `ModalCollapseR_of_Symmetric` | **`Symmetric R`** + `validW` A1W–A5W | collapse **at every world, along `R`** |
| `ModalCollapseR_of_S5` | `S5Frame` (via symmetry) + valid A1W–A5W | same |
| `ContingentR_impossible_of_Symmetric` | Symmetric + valid A1W–A5W | ContingentR impossible **at every world** |
| `ContingentAct_impossible_of_Symmetric` | same | same for `ContingentAct` |
| `ModalCollapse_of_Universal_WRP` | **`Universal R`** + valid A1W–A5W | Sobel `ModalCollapse` |
| `wrp_idRel_R_collapse_not_sobel` | `idRel` on `Bool`, `PosLocal` | R-collapse and no ContingentR, but **not** Sobel collapse |

`A2W` and `A3W` are used only to get God at every world
(`global_T3W_of_Symmetric`). The collapse step at a God-world is A1W+A4W+A5W.
Rigid `ModalCollapseAt_of_God` does not list A4 because rigid Positive absorbs it.

### Which “global”?

Under **WRP** (not rigid Positive): Symmetric + valid A1–A5 ⇒

- `ModalCollapseR`: collapse at every world, along accessible worlds;
- ContingentR impossible at every world.

That is stronger than rigid Countermodel D, where S5Frame + rigid A1–A5 leave
ContingentR alive off the single God-cluster. WRP A3 is required at every
world, so every symmetric cluster gets a God-world and then collapses.
Comparison with Countermodel D is **desk packaging** of that encoding gap.
The collapse theorem itself is **rediscovery**.

Symmetry does **not** yield Sobel `ModalCollapse`. On two isolated reflexive
worlds, `(· = false)` is true at `false` and false at `true`
(`wrp_idRel_R_collapse_not_sobel`). Those worlds are not `R`-related, so this
is not `ContingentR`.

---

## `#print axioms` (2026-09-24)

All of the theorems in the table above depend only on:

`propext`, `Classical.choice`, `Quot.sound`

(from `Classical.byContradiction` in the WRP T1 / T2 chain). No `sorry`.
`lake build` succeeds.

---

## Status

**Rediscovery** of Sobel / Benzmüller–Fuenmayor Scott collapse, in this thin
WRP encoding. The `idRel` split between `ModalCollapseR` and Sobel
`ModalCollapse` is desk packaging of what `□` means when `R` is not universal.
Not a priority claim. Does not refute the HOML development; it re-checks the
Scott-side consequence they already record.
