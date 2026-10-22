theory PwnUF imports Ax1GenAlternativesB.Ax1GenAlternativesB
begin
  abbreviation "TwoMembersR (\<Phi>::(e\<Rightarrow>\<sigma>)\<Rightarrow>bool) \<equiv> \<exists>\<psi>\<^sub>1 \<psi>\<^sub>2. \<Phi> \<psi>\<^sub>1 \<and> \<Phi> \<psi>\<^sub>2 \<and> \<psi>\<^sub>1 \<noteq> \<psi>\<^sub>2"
  abbreviation "Ax1GenTwoR \<equiv> \<forall>(\<Phi>::(e\<Rightarrow>\<sigma>)\<Rightarrow>bool) \<phi>. \<lfloor>((\<lambda>w. TwoMembersR \<Phi>) \<^bold>\<and> PosPropsR \<Phi> \<^bold>\<and> ConjR \<phi> \<Phi>) \<^bold>\<supset> P \<phi>\<rfloor>"
text \<open>Filter/UFilter copied verbatim from the Notes' GoedelVariantHOML3inS4oneFile.thy l.206-207 (2609.36279 ancillary),
  with property inclusion as session B defines it.\<close>
  abbreviation "Filter \<Phi> \<equiv> \<Phi> (\<lambda>x. \<^bold>\<top>) \<^bold>\<and> \<^bold>\<not>(\<Phi> (\<lambda>x. \<^bold>\<bottom>)) \<^bold>\<and> (\<^bold>\<forall>\<phi> \<psi>. (\<Phi> \<phi> \<^bold>\<and> (\<phi> \<^bold>\<supset>\<^sub>N \<psi>)) \<^bold>\<supset> \<Phi> \<psi>) \<^bold>\<and> (\<^bold>\<forall>\<phi> \<psi>. (\<Phi> \<phi> \<^bold>\<and> \<Phi> \<psi>) \<^bold>\<supset> \<Phi> (\<phi> \<^bold>. \<psi>))"
  abbreviation "UFilter \<Phi> \<equiv> Filter \<Phi> \<^bold>\<and> (\<^bold>\<forall>\<phi>. \<Phi> \<phi> \<^bold>\<or> \<Phi> (\<^bold>~\<phi>))"

theorem UF_base: "\<lfloor>UFilter P\<rfloor>"
proof
  fix w
  have top: "P (\<lambda>x. \<^bold>\<top>) w" using Ax3 Ax4[of E "\<lambda>x. \<^bold>\<top>"] by blast
  have nbot: "\<not> P (\<lambda>x. \<^bold>\<bottom>) w" using top Ax2a[of "\<lambda>x. \<^bold>\<top>", rule_format, of w] by simp
  show "UFilter P w" using top nbot Ax4 Ax1 Ax2a by blast
qed
text \<open>So UFilter P holds at every world of every model of session B's axioms (Ax1, Ax2a, Ax2b, Ax3, Ax4), with no
  conjunction-axiom reading at all; in particular in every model of Ax1GenTwoR there.\<close>
corollary UF_TwoR: assumes "Ax1GenTwoR" shows "\<lfloor>UFilter P\<rfloor>" using UF_base .
text \<open>TwoR(c) countermodels, now additionally requiring UFilter P at every world.\<close>
lemma G_ex_TwoR_UF: assumes "Ax1GenTwoR" "\<lfloor>UFilter P\<rfloor>" shows "\<lfloor>\<^bold>\<exists>\<^sup>Ex. G x\<rfloor>"
  nitpick[card i=1-2, card e=1, timeout=120, expect=genuine] oops
lemma MC_TwoR_K_UF: assumes "Ax1GenTwoR" "\<lfloor>UFilter P\<rfloor>" shows "\<lfloor>\<phi> \<^bold>\<supset> \<^bold>\<box>\<phi>\<rfloor>"
  nitpick[card i=1-2, card e=1, timeout=120, expect=genuine] oops
lemma Th3_TwoR_S4_UF: assumes "Ax1GenTwoR" "\<lfloor>UFilter P\<rfloor>" FrRefl FrTrans
  shows "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>Ex. G x) \<^bold>\<supset> \<^bold>\<box>(\<^bold>\<exists>\<^sup>Ey. G y)\<rfloor>"
  nitpick[card i=1-2, card e=1, timeout=120, expect=genuine] oops
end
