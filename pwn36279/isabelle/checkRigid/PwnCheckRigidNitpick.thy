theory PwnCheckRigidNitpick imports PwnCheckRigid
begin
text \<open>Countermodels (Nitpick, expect=genuine certified by the build).\<close>
lemma G_ex_R_noL: assumes "Ax1GenR" shows "\<lfloor>\<^bold>\<exists>\<^sup>Ex. G x\<rfloor>"
  nitpick[card i=1-2, card e=1, timeout=120, expect=genuine] oops
lemma Th3_R_S4_noL: assumes "Ax1GenR" and FrRefl and FrTrans
  shows "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>Ex. G x) \<^bold>\<supset> \<^bold>\<box>(\<^bold>\<exists>\<^sup>Ey. G y)\<rfloor>"
  nitpick[card i=1-2, card e=1, timeout=120, expect=genuine] oops
lemma G_ex_TwoR: assumes "Ax1GenTwoR" shows "\<lfloor>\<^bold>\<exists>\<^sup>Ex. G x\<rfloor>"
  nitpick[card i=1-2, card e=1, timeout=120, expect=genuine] oops
lemma MC_TwoR_K: assumes "Ax1GenTwoR" shows "\<lfloor>\<phi> \<^bold>\<supset> \<^bold>\<box>\<phi>\<rfloor>"
  nitpick[card i=1-2, card e=1, timeout=120, expect=genuine] oops
lemma Th3_TwoR_S4: assumes "Ax1GenTwoR" and FrRefl and FrTrans
  shows "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>Ex. G x) \<^bold>\<supset> \<^bold>\<box>(\<^bold>\<exists>\<^sup>Ey. G y)\<rfloor>"
  nitpick[card i=1-2, card e=1, timeout=120, expect=genuine] oops
text \<open>Ax1GenTwoR does not give back Ax1Gen (contrast session E, Two_equivalent, which goes through
  Theorem 11's world-dependent set and the nominal argument R_Id).\<close>
lemma Ax1Gen_of_TwoR: assumes "Ax1GenTwoR" shows "Ax1GenS"
  nitpick[card i=1-2, card e=1, timeout=120, expect=genuine] oops
end
