theory PwnCheckRigid imports Ax1GenAlternativesB.Ax1GenAlternativesB
begin
text \<open>Benzmueller, arXiv:2609.36279v2 ancillary, session B (variant 2 = AFP Fig. 7, logic K):
  "Candidate B -- Ax1GenR: Phi a rigid (world-independent) set of properties"; README:
  "L: derivability open (the article's derivation, Phi := P, is unavailable since P is not rigid)";
  Lean Ax1GenRigidVariant2: example (_ : Ax1GenR) : P G := by openproblem.
  Arrowood's repository (GodelOntological/Actualist_Repaired.lean, lemma_L_rigid, commit 27524f7,
  2026-09-24) derives L for the rigid reading using Ax2a and Ax2b (pos_agree).  Replayed here.\<close>

lemma pos_agree: assumes r: "w\<^bold>r v" shows "P \<psi> w \<longleftrightarrow> P \<psi> v"
proof
  assume "P \<psi> w" thus "P \<psi> v" using Ax2b r by blast
next
  assume pv: "P \<psi> v"
  show "P \<psi> w"
  proof (rule ccontr)
    assume "\<not> P \<psi> w"
    hence "P (\<^bold>~\<psi>) w" using Ax2a[of \<psi>] by blast
    hence "P (\<^bold>~\<psi>) v" using Ax2b r by blast
    thus False using pv Ax2a[of \<psi>] by blast
  qed
qed

lemma Gagree: assumes rv: "w\<^bold>r v" shows "G z v \<longleftrightarrow> (\<forall>\<psi>. P \<psi> w \<longrightarrow> \<psi> z v)"
proof
  assume "G z v" hence g: "\<forall>\<psi>. P \<psi> v \<longrightarrow> \<psi> z v" unfolding God_def by simp
  show "\<forall>\<psi>. P \<psi> w \<longrightarrow> \<psi> z v"
  proof (intro allI impI)
    fix \<psi> assume "P \<psi> w" hence "P \<psi> v" using pos_agree[OF rv] by simp
    thus "\<psi> z v" using g by blast
  qed
next
  assume h: "\<forall>\<psi>. P \<psi> w \<longrightarrow> \<psi> z v"
  { fix \<psi> assume "P \<psi> v" hence "P \<psi> w" using pos_agree[OF rv] by simp
    hence "\<psi> z v" using h by blast }
  thus "G z v" unfolding God_def by blast
qed

theorem L_R_derived: assumes A: "Ax1GenR" shows "\<lfloor>P G\<rfloor>"
proof -
  { fix w
    have inst: "((PosPropsR (\<lambda>\<psi>. P \<psi> w) \<^bold>\<and> ConjR G (\<lambda>\<psi>. P \<psi> w)) \<^bold>\<supset> P G) w"
      by (rule A[THEN spec, THEN spec, THEN spec])
    have pos: "PosPropsR (\<lambda>\<psi>. P \<psi> w) w" by simp
    have conj: "ConjR G (\<lambda>\<psi>. P \<psi> w) w"
    proof -
      { fix v z assume rv: "w\<^bold>r v"
        have "G z v \<longleftrightarrow> (\<forall>\<psi>. P \<psi> w \<longrightarrow> \<psi> z v)" by (rule Gagree[OF rv]) }
      thus ?thesis by simp
    qed
    have "P G w" using inst pos conj by blast }
  thus ?thesis by blast
qed

text \<open>Hence session B's countermodels "with L added" are countermodels of Ax1GenR alone.\<close>

text \<open>A combined reading not in 2609.36279: rigid Phi AND at least two different conjuncts.\<close>
abbreviation "TwoMembersR (\<Phi>::(e\<Rightarrow>\<sigma>)\<Rightarrow>bool) \<equiv> \<exists>\<psi>\<^sub>1 \<psi>\<^sub>2. \<Phi> \<psi>\<^sub>1 \<and> \<Phi> \<psi>\<^sub>2 \<and> \<psi>\<^sub>1 \<noteq> \<psi>\<^sub>2"
abbreviation "Ax1GenTwoR \<equiv> \<forall>(\<Phi>::(e\<Rightarrow>\<sigma>)\<Rightarrow>bool) \<phi>.
   \<lfloor>((\<lambda>w. TwoMembersR \<Phi>) \<^bold>\<and> PosPropsR \<Phi> \<^bold>\<and> ConjR \<phi> \<Phi>) \<^bold>\<supset> P \<phi>\<rfloor>"
abbreviation "TwoMembers \<Phi> \<equiv> \<lambda>w. \<exists>\<psi>\<^sub>1 \<psi>\<^sub>2. \<Phi> \<psi>\<^sub>1 w \<and> \<Phi> \<psi>\<^sub>2 w \<and> \<psi>\<^sub>1 \<noteq> \<psi>\<^sub>2"
abbreviation "Ax1GenTwo \<equiv> \<forall>\<Phi> \<phi>. \<lfloor>(TwoMembers \<Phi> \<^bold>\<and> PosProps \<Phi> \<^bold>\<and> ConjOfPropsFrom \<phi> \<Phi>) \<^bold>\<supset> P \<phi>\<rfloor>"

lemma TwoR_weaker_than_R: assumes "Ax1GenR" shows "Ax1GenTwoR" using assms by blast
lemma TwoR_weaker_than_Two: assumes A: "Ax1GenTwo" shows "Ax1GenTwoR"
proof -
  { fix \<Phi> :: "(e\<Rightarrow>\<sigma>)\<Rightarrow>bool" and \<phi> :: "e\<Rightarrow>\<sigma>" and w :: i
    have h: "(TwoMembers (\<lambda>\<psi> u. \<Phi> \<psi>) \<^bold>\<and> PosProps (\<lambda>\<psi> u. \<Phi> \<psi>) \<^bold>\<and> ConjOfPropsFrom \<phi> (\<lambda>\<psi> u. \<Phi> \<psi>)) w \<longrightarrow> P \<phi> w"
      by (rule A[THEN spec[of _ "\<lambda>\<psi> u. \<Phi> \<psi>"], THEN spec[of _ \<phi>], THEN spec[of _ w]])
    hence "(((\<lambda>w. TwoMembersR \<Phi>) \<^bold>\<and> PosPropsR \<Phi> \<^bold>\<and> ConjR \<phi> \<Phi>) \<^bold>\<supset> P \<phi>) w" by simp }
  thus ?thesis by blast
qed

lemma PTop: "\<lfloor>P (\<lambda>x. \<^bold>\<top>)\<rfloor>"
proof -
  { fix w have "P (\<lambda>x. \<^bold>\<top>) w" using Ax4[of E "\<lambda>x. \<^bold>\<top>", rule_format, of w] Ax3[rule_format, of w] by simp }
  thus ?thesis by blast
qed

theorem L_TwoR: assumes A: "Ax1GenTwoR" shows "\<lfloor>P G\<rfloor>"
proof -
  { fix w
    have PT: "P (\<lambda>x. \<^bold>\<top>) w" using PTop by blast
    have "P G w"
    proof (cases "\<exists>\<psi>\<^sub>1 \<psi>\<^sub>2. P \<psi>\<^sub>1 w \<and> P \<psi>\<^sub>2 w \<and> \<psi>\<^sub>1 \<noteq> \<psi>\<^sub>2")
      case True
      have inst: "(((\<lambda>u. TwoMembersR (\<lambda>\<psi>. P \<psi> w)) \<^bold>\<and> PosPropsR (\<lambda>\<psi>. P \<psi> w) \<^bold>\<and> ConjR G (\<lambda>\<psi>. P \<psi> w)) \<^bold>\<supset> P G) w"
        by (rule A[THEN spec, THEN spec, THEN spec])
      have conj: "ConjR G (\<lambda>\<psi>. P \<psi> w) w"
      proof -
        { fix v z assume rv: "w\<^bold>r v"
          have "G z v \<longleftrightarrow> (\<forall>\<psi>. P \<psi> w \<longrightarrow> \<psi> z v)" by (rule Gagree[OF rv]) }
        thus ?thesis by simp
      qed
      show ?thesis using inst True conj by simp
    next
      case False
      have one: "\<And>\<phi>. P \<phi> w \<Longrightarrow> \<phi> = (\<lambda>x. \<^bold>\<top>)" using False PT by blast
      have Gw: "G x w" for x
      proof -
        { fix \<phi> assume "P \<phi> w" hence "\<phi> = (\<lambda>x. \<^bold>\<top>)" by (rule one) hence "\<phi> x w" by simp }
        thus ?thesis unfolding God_def by blast
      qed
      have "P G w \<or> P (\<^bold>~G) w" using Ax2a[of G, rule_format, of w] by auto
      moreover
      { assume h: "P (\<^bold>~G) w"
        have one': "\<And>\<phi> x v. P \<phi> w \<Longrightarrow> \<phi> x v"
        proof -
          fix \<phi> x v assume "P \<phi> w"
          hence "\<phi> = (\<lambda>x. \<^bold>\<top>)" by (rule one)
          thus "\<phi> x v" by simp
        qed
        have "(\<^bold>~G) undefined w" by (rule one'[OF h])
        hence False using Gw[of undefined] by simp }
      ultimately show ?thesis by blast
    qed }
  thus ?thesis by blast
qed

text \<open>Collapse under the combined reading: expected refuted (it is weaker than Ax1GenR).\<close>
end
