theory PwnTh4RPNitpick imports PwnTh4RP.PwnTh4RP
begin
text \<open>Is RigidPos extra?  Countermodels (expect = genuine) in K, S4, S5 (equivalence relation).\<close>
lemma RP_K:  assumes Ax2bH Ax1GenR shows RigidPos
  nitpick[card i=2, card e=1, timeout=120, expect=genuine, max_genuine=1] oops
lemma RP_S4: assumes Ax2bH Ax1GenR FrRefl FrTrans shows RigidPos
  nitpick[card i=2, card e=1, timeout=120, expect=genuine, max_genuine=1] oops
lemma RP_S5: assumes Ax2bH Ax1GenR FrRefl FrTrans FrSym shows RigidPos
  nitpick[card i=2, card e=1, timeout=120, expect=genuine, max_genuine=1] oops
end
