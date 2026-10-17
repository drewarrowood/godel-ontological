#!/usr/bin/env bash
# Rebuild the two Lean check modules inside Benzmüller's own lake package
# (arXiv:2609.36279 ancillary files, anc/OpenQuestions/lean, lean-toolchain 4.33.1).
# His files are not vendored here (no licence statement in the ancillary files);
# this script copies his module and splices in our additions.
#   usage: lean/apply.sh /path/to/anc/OpenQuestions/lean
set -euo pipefail
PKG="$1"; HERE="$(cd "$(dirname "$0")" && pwd)"
OQ="$PKG/OpenQuestions"
# PwnRigidL: his Ax1GenRigidVariant2 with lines 149-150 (the `openproblem` for L) replaced.
{ head -n 148 "$OQ/Ax1GenRigidVariant2.lean"; cat "$HERE/PwnRigidL.additions.lean"; tail -n +151 "$OQ/Ax1GenRigidVariant2.lean"; } > "$OQ/PwnRigidL.lean"
# PwnEmptyAtHome: his GoedelVariantHOML2inS4oneFile with our theorem appended.
{ cat "$OQ/GoedelVariantHOML2inS4oneFile.lean"; cat "$HERE/PwnEmptyAtHome.additions.lean"; } > "$OQ/PwnEmptyAtHome.lean"
cd "$PKG"
lake build OpenQuestions.PwnRigidL OpenQuestions.PwnEmptyAtHome
echo "Now run his detector (#hybrid_audit, HybridAudit.lean) on both modules as in his audit README."
