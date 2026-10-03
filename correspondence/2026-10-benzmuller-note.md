# DRAFT — not sent

**From:** Drew Arrowood
**To:** Christoph Benzmüller
**Subject:** Thanks for "Proofs Without Nominals" (arXiv:2609.36279), and a note on Candidate B
**Status:** DRAFT. Not sent. For Drew's review.

---

Dear Professor Benzmüller,

Thank you for *Proofs Without Nominals* (arXiv:2609.36279). It settles the questions my note *One World or Two* was circling, and it does so more cleanly than my note did.

One small item may be useful to you. Your session-B Candidate B, Ax1GenR (rigid Φ), is listed as open in `alternatives/README.md` line 87, and `Ax1GenRigidVariant2.lean` line 150 leaves it as `openproblem`. My `lemma_L_rigid` builds on your AFP entry `GoedelVariantHOML2inS4`, and its snapshot-and-agreement step uses the same move as `Th4_finite` in your arXiv:2608.07578; my commit `b23cc28` cited arXiv:2608.07578, for a different result, 31 minutes before `27524f7`, and my records do not show whether `Th4_finite` was read. It proves L for the rigid-Φ variant you later list as Candidate B (Ax1GenR), in commit `27524f7`, merged 24 Sep 2026 (20:51 UTC), four days before arXiv:2609.36279 v1 (28 Sep). I checked arXiv:2609.26806 v1, the Monatshefte paper, the AFP entries, and your public repositories as of that date and found no statement of Candidate B or of L as open under it. I mention this only so that the record is clear.

I have re-proved it in your encoding. In Isabelle2025-2 it is session `PwnCheckRigid`, theorem `L_R_derived`. In Lean 4.33.1 it is `PwnRigidL.lean`, where `#print axioms` lists Ax2a, Ax2b, the signature constants, and the classical triple, with no sorry. I also checked a rigid two-conjunct reading, Ax1GenTwoR, with genuine Nitpick countermodels. One question is open: whether the snapshot witness counts as hybrid-free. It lies outside your detector's stated scope.

My PR #13 (https://github.com/drewarrowood/godel-ontological/pull/13) marks my earlier results as superseded by your paper. It also flags my Ax1Gen instance as the degenerate empty case. I would be grateful for any corrections.

With thanks and best regards,
Drew Arrowood
