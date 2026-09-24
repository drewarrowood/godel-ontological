# Frame residue under world-relative Positive

Desk check of what happens in `GodelOntological/WRPFrameResidue.lean` when
**Symmetric** is dropped. Not a priority claim. Not an answer to the
Monatshefte Fig. 7 question (S4 for Gödel’s adapted-essence Th3), which these
Scott-style tables do not settle.

Date: 2026-09-24 (America/New_York). Toolchain: Lean 4.34.0. Signature: **WRP**
(`PosW`, A1W–A5W, `validW`), not rigid Positive.

---

## Literature cut

Kanckos & Woltzenlogel Paleo: Scott’s argument goes through in **KB**
(symmetry); S5 is not required (*Studia Logica* 105(3), 2017,
DOI 10.1007/s11225-016-9700-1). Benzmüller & Scott: their Theorem Th3 uses
symmetry of accessibility (`Rsymm`), not the rest of S5 (*Monatshefte für
Mathematik*, 2025, DOI 10.1007/s00605-025-02078-x).

The same paper leaves **open** whether S4 proves Th3 for Gödel’s variant with
the **adapted** essence (Fig. 7). The countermodels below use Scott-style
`EssenceW` in this thin encoding. They do not answer that open.

---

## Table

| Frame | WRP A1–A5 | Global T3 | Local T3 | Collapse at every world | ContingentR |
| --- | --- | --- | --- | --- | --- |
| **Symmetric** + valid A1W–A5W | assumed | holds | holds (`□∃G` at every world) | holds (`ModalCollapseR`) | impossible everywhere |
| `idRel` + `PosLocal` (sym. and refl.) | satisfiable (earlier module) | holds | holds | R-collapse holds | impossible |
| `R_swap` (`w ≠ v` on `Bool`), any `Ind` | **A1–A4 impossible** | conditional theorems have no witness on this frame | same | same | same |
| Empty `R` on `Unit` | **A1–A3 impossible** | — | — | — | — |
| `R_chain` (refl + trans, not sym, not eucl.) | satisfiable (`PosPivot true`) | **fails** | **fails** at `false` | fails at `false`; holds at the sink | **survives** at `false` |
| `R_fork` (refl.; not trans / sym / eucl.) | satisfiable (`PosPivot s`) | **fails** | **fails** at `a` | fails at `a` | **survives** at `a` |
| `R_to_true` (serial + trans + eucl.; not refl / sym) | satisfiable (`PosPivot true`) | **fails** | **holds** at every world | fails at `false`; holds at the sink | **survives** at `false` |

`PosPivot s` says `φ` is positive iff `φ` holds of `()` at the sink `s`.
It validates A1W–A5W when every world sees `s` and `s` sees only itself.

---

## Theorem names

Survives: `symmetric_WRP_package`.

Dead-end: `A123_implies_serial`, `no_A123_on_empty`.

No Unit-or-larger witness for the irreflexive 2-cycle: `R_swap_no_valid_A1234`.

S4 chain: `chain_S4_global_T3_fails`, `chain_S4_local_T3_fails`,
`chain_S4_ContingentR_survives`, `chain_S4_collapse_fails_at_source`,
`chain_S4_collapse_at_sink`.

Fork: `fork_global_T3_fails`, `fork_local_T3_fails`, `fork_ContingentR_survives`,
`fork_collapse_fails_at_a`.

See-only-sink: `to_true_global_T3_fails`, `to_true_local_T3_holds`,
`to_true_ContingentR_survives`, `to_true_collapse_fails_at_false`,
`to_true_collapse_at_sink`.

---

## `#print axioms` (2026-09-24)

| Theorems | Axioms |
| --- | --- |
| `symmetric_WRP_package`, `A123_implies_serial`, `no_A123_on_empty`, `R_swap_no_valid_A1234`, `chain_S4_collapse_at_sink`, `to_true_collapse_at_sink` | `propext`, `Classical.choice`, `Quot.sound` |
| `chain_S4_*` failure/Contingent theorems, `fork_global_T3_fails`, `fork_local_T3_fails`, `fork_ContingentR_survives`, `to_true_global_T3_fails` | `propext` |
| `PosPivot_A1`, `PosPivot_A5`, `to_true_local_T3_holds`, `to_true_ContingentR_survives`, `to_true_collapse_fails_at_false` | none |

No `sorry`. `lake build` succeeds.

---

## Status

**Rediscovery** of the positive KB/symmetry direction (`symmetric_WRP_package`
packages theorems already checked against Kanckos & Woltzenlogel Paleo and
Benzmüller–Scott).

**Desk packaging** of the negative rows: finite tables in this WRP signature.
Euclidean + serial + transitive does not substitute for Symmetric (global T3
fails on `R_to_true` while local T3 holds). Reflexive + transitive does not
either (`R_chain`).

Not a priority claim. Does not settle the Monatshefte Fig. 7 S4 question.
