# DRAFT — not sent

**From:** Drew Arrowood
**To:** Christoph Benzmüller
**Subject:** Thanks for "Proofs Without Nominals" (arXiv:2609.36279), and a note on Candidate B
**Status:** DRAFT. Not sent. For Drew's review.

---

Dear Professor Benzmüller,

Thank you for *Proofs Without Nominals* (arXiv:2609.36279). It settles the questions my note *One World or Two* was circling, and it does so more cleanly than my note did.

One small item may be useful to you. Your session-B Candidate B, Ax1GenR (rigid Φ), is listed as open in `alternatives/README.md` line 87: "derivability **open** (the article's derivation, Φ := P, is unavailable since P is not rigid)". In `Ax1GenRigidVariant2.lean`, line 150 is `example (_ : Ax1GenR) : ⌊P G⌋ := by openproblem`. Independently, my repository derives L for this reading, as `lemma_L_rigid` in commit 27524f7. GitHub merged that commit into master with PR #1 on 24 September 2026 at 20:51:39 UTC, before your v1. The proof takes a snapshot of positivity at w and uses Ax2a and Ax2b.

I have re-proved it in your encoding. In Isabelle2025-2 it is session `PwnCheckRigid`, theorem `L_R_derived`. In Lean 4.33.1 it is `PwnRigidL.lean`, where `#print axioms` lists Ax2a, Ax2b, the signature constants, and the classical triple, with no sorry. I also checked a rigid two-conjunct reading, Ax1GenTwoR, with genuine Nitpick countermodels. One question is open: whether the snapshot witness counts as hybrid-free. It lies outside your detector's stated scope.

My PR #13 (https://github.com/drewarrowood/godel-ontological/pull/13) marks my earlier results as superseded by your paper. It also flags my Ax1Gen instance as the degenerate empty case. I would be grateful for any corrections.

With thanks and best regards,
Drew Arrowood
