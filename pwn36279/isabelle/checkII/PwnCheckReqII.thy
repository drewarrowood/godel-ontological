theory PwnCheckReqII imports Th4FromConjunction.Th4FromConjunction
begin
text \<open>Requirement (ii) of 2609.36279 Sect. 6 for the rigid two-conjunct reading: Ax2a is the only axiom.\<close>
  abbreviation "PosPropsR (\<Phi>::(e\<Rightarrow>\<sigma>)\<Rightarrow>bool) \<equiv> \<lambda>w. \<forall>\<psi>. \<Phi> \<psi> \<longrightarrow> P \<psi> w"
  abbreviation "ConjR \<phi> (\<Phi>::(e\<Rightarrow>\<sigma>)\<Rightarrow>bool) \<equiv> \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ez. \<phi> z \<^bold>\<leftrightarrow> (\<lambda>w. \<forall>\<psi>. \<Phi> \<psi> \<longrightarrow> \<psi> z w))"
  abbreviation "Ax1GenR \<equiv> \<forall>(\<Phi>::(e\<Rightarrow>\<sigma>)\<Rightarrow>bool) \<phi>. \<lfloor>(PosPropsR \<Phi> \<^bold>\<and> ConjR \<phi> \<Phi>) \<^bold>\<supset> P \<phi>\<rfloor>"
  abbreviation "TwoMembersR (\<Phi>::(e\<Rightarrow>\<sigma>)\<Rightarrow>bool) \<equiv> \<exists>\<psi>\<^sub>1 \<psi>\<^sub>2. \<Phi> \<psi>\<^sub>1 \<and> \<Phi> \<psi>\<^sub>2 \<and> \<psi>\<^sub>1 \<noteq> \<psi>\<^sub>2"
  abbreviation "Ax1GenTwoR \<equiv> \<forall>(\<Phi>::(e\<Rightarrow>\<sigma>)\<Rightarrow>bool) \<phi>. \<lfloor>((\<lambda>w. TwoMembersR \<Phi>) \<^bold>\<and> PosPropsR \<Phi> \<^bold>\<and> ConjR \<phi> \<Phi>) \<^bold>\<supset> P \<phi>\<rfloor>"
  lemma Th4_TwoR_alone: assumes Ax1GenTwoR shows "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>Ex. G x)\<rfloor>" nitpick[card i=1-2, card e=1-2, timeout=120, expect=genuine] oops
  lemma PTop_TwoR_alone: assumes Ax1GenTwoR shows "\<lfloor>P (\<lambda>x. \<^bold>\<top>)\<rfloor>" nitpick[card i=1-2, card e=1-2, timeout=120, expect=genuine] oops
end
