# DRAFT — not sent

**From:** Drew Arrowood
**To:** Christoph Benzmüller
**Subject:** Thanks for "Proofs Without Nominals" (arXiv:2609.36279), and a note on Candidate B
**Status:** DRAFT. Not sent. For Drew's review. Revised 15 Oct 2026 after arXiv:2609.36279v3 (13 Oct 2026).

---

Dear Professor Benzmüller,

Thank you for *Proofs Without Nominals* (arXiv:2609.36279; I have now read v3 of 13 October). It settles the questions my note *One World or Two* was circling, and it does so more cleanly than my note did.

One small item may be useful to you. In v2, your session-B Candidate B, Ax1GenR (rigid Φ), was listed as open in `alternatives/README.md` line 87, and `Ax1GenRigidVariant2.lean` line 150 left it as `openproblem`. My `lemma_L_rigid` builds on the theory `GoedelVariantHOML2inS4` in your and Dana Scott's AFP entry `Notes_On_Goedels_Ontological_Argument`, and its snapshot-and-agreement step uses the same move as `Th4_finite` in your arXiv:2608.07578; my commit `b23cc28` cited arXiv:2608.07578, for a different result, 31 minutes before `27524f7`, and my records do not show whether `Th4_finite` was read. It proves L for the rigid-Φ variant you later list as Candidate B (Ax1GenR), in commit `27524f7`, merged 24 Sep 2026 (20:51 UTC), four days before arXiv:2609.36279 v1 (28 Sep). I checked arXiv:2609.26806 v1, the Monatshefte paper, the AFP entries, and your public repositories as of that date and found no statement of Candidate B or of L as open under it. Your v3 now states L under Ax1GenR as derived in K from Ax2a and Ax2b, with the same snapshot of positivity, {ψ | P ψ w}, read as the satisfaction operator @_w P (`L_R`, §6.4.3), and footnote 6 says it was pointed out in a pre-submission review. I mention all this only so that the record is clear.

I have re-proved it in your encoding. In Isabelle2025-2 it is session `PwnCheckRigid`, theorem `L_R_derived`. In Lean 4.33.1 it is `PwnRigidL.lean`, where `#print axioms` lists Ax2a, Ax2b, the signature constants, and the classical triple, with no sorry. I also checked a rigid two-conjunct reading, Ax1GenTwoR, with genuine Nitpick countermodels. In v2 I left open whether the snapshot witness counts as hybrid-free, since it lay outside the detector's stated scope; your v3 Definition 1 now covers sets of properties simpliciter, and §6.4.3 says the detector flags that witness. One small thing you may want to align: the v3 ancillary comments still say the opposite (`Ax1GenRigidVariant2.lean` line 156, "The detector does not flag it, and cannot"; `alternatives/README.md` line 97, "which the criterion of the article cannot even see here"; and the session-B theory comment before `P_succ`).

My PR #13 (https://github.com/drewarrowood/godel-ontological/pull/13) marks my earlier results as superseded by your paper. It also flags my Ax1Gen instance as the degenerate empty case. I would be grateful for any corrections.

With thanks and best regards,
Drew Arrowood
