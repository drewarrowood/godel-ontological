theory PwnTh4R imports Th4FromConjunction.Th4FromConjunction
begin
  abbreviation "PosPropsR (\<Phi>::(e\<Rightarrow>\<sigma>)\<Rightarrow>bool) \<equiv> \<lambda>w. \<forall>\<psi>. \<Phi> \<psi> \<longrightarrow> P \<psi> w"
  abbreviation "ConjR \<phi> (\<Phi>::(e\<Rightarrow>\<sigma>)\<Rightarrow>bool) \<equiv> \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ez. \<phi> z \<^bold>\<leftrightarrow> (\<lambda>w. \<forall>\<psi>. \<Phi> \<psi> \<longrightarrow> \<psi> z w))"
  abbreviation "Ax1GenR \<equiv> \<forall>(\<Phi>::(e\<Rightarrow>\<sigma>)\<Rightarrow>bool) \<phi>. \<lfloor>(PosPropsR \<Phi> \<^bold>\<and> ConjR \<phi> \<Phi>) \<^bold>\<supset> P \<phi>\<rfloor>"
  abbreviation "Ax2bH \<equiv> \<forall>\<phi>. \<lfloor>P \<phi> \<^bold>\<supset> \<^bold>\<box> P \<phi>\<rfloor>"

lemma pos_agree: assumes B: Ax2bH and r: "w\<^bold>r v" shows "P \<psi> w \<longleftrightarrow> P \<psi> v"
proof
  assume "P \<psi> w" thus "P \<psi> v" using B r by blast
next
  assume pv: "P \<psi> v"
  show "P \<psi> w"
  proof (rule ccontr)
    assume "\<not> P \<psi> w"
    hence "P (\<^bold>~\<psi>) w" using Ax2a[of \<psi>] by blast
    hence "P (\<^bold>~\<psi>) v" using B r by blast
    thus False using pv Ax2a[of \<psi>] by blast
  qed
qed

text \<open>L via the snapshot \<Phi> = {\<psi>. P \<psi> w}: world-invariant as a function, but it names w (hybrid-flagged in v3).\<close>
lemma L_R: assumes A: Ax1GenR and B: Ax2bH shows "\<lfloor>P G\<rfloor>"
proof
  fix w
  have c: "ConjR G (\<lambda>\<psi>. P \<psi> w) w"
  proof (intro allI impI)
    fix v z assume rv: "w\<^bold>r v" and "z\<^bold>@v"
    show "G z v \<longleftrightarrow> (\<forall>\<psi>. P \<psi> w \<longrightarrow> \<psi> z v)"
      unfolding God_def using pos_agree[OF B rv] by blast
  qed
  show "P G w" using A[THEN spec[where x="\<lambda>\<psi>. P \<psi> w"], THEN spec[where x=G], THEN spec[where x=w]] c by simp
qed

text \<open>Th4_R: only rigid, world-free collections {} and {G} are used after L.\<close>
theorem Th4_R: assumes A: Ax1GenR and B: Ax2bH shows "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>Ex. G x)\<rfloor>"
proof
  fix w
  have L: "\<And>v. P G v" using L_R[OF A B] by blast
  have top: "P (\<lambda>x. \<^bold>\<top>) w" using A[THEN spec[where x="\<lambda>\<psi>. False"], THEN spec[where x="\<lambda>x. \<^bold>\<top>"], THEN spec[where x=w]] by simp
  show "(\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>Ex. G x)) w"
  proof (rule ccontr)
    assume h: "\<not>(\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>Ex. G x)) w"
    have "P (\<lambda>x. \<^bold>\<bottom>) w" using A[THEN spec[where x="\<lambda>\<psi>. \<psi> = G"], THEN spec[where x="\<lambda>x. \<^bold>\<bottom>"], THEN spec[where x=w]] L h by simp
    thus False using top Ax2a[of "\<lambda>x. \<^bold>\<top>", rule_format, of w] by simp
  qed
qed

end
