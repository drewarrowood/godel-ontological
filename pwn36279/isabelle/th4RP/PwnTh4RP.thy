theory PwnTh4RP imports Th4FromConjunction.Th4FromConjunction
begin
  abbreviation "PosPropsR (\<Phi>::(e\<Rightarrow>\<sigma>)\<Rightarrow>bool) \<equiv> \<lambda>w. \<forall>\<psi>. \<Phi> \<psi> \<longrightarrow> P \<psi> w"
  abbreviation "ConjR \<phi> (\<Phi>::(e\<Rightarrow>\<sigma>)\<Rightarrow>bool) \<equiv> \<^bold>\<box>(\<^bold>\<forall>\<^sup>Ez. \<phi> z \<^bold>\<leftrightarrow> (\<lambda>w. \<forall>\<psi>. \<Phi> \<psi> \<longrightarrow> \<psi> z w))"
  abbreviation "Ax1GenR \<equiv> \<forall>(\<Phi>::(e\<Rightarrow>\<sigma>)\<Rightarrow>bool) \<phi>. \<lfloor>(PosPropsR \<Phi> \<^bold>\<and> ConjR \<phi> \<Phi>) \<^bold>\<supset> P \<phi>\<rfloor>"
  abbreviation "Ax2bH \<equiv> \<forall>\<phi>. \<lfloor>P \<phi> \<^bold>\<supset> \<^bold>\<box> P \<phi>\<rfloor>"
  abbreviation "RigidPos \<equiv> \<forall>\<psi> u v. P \<psi> u \<longrightarrow> P \<psi> v"   \<comment>\<open>Benzmueller v4, session B\<close>
  abbreviation "PosGlobal \<equiv> \<lambda>\<psi>. \<forall>v. P \<psi> v"           \<comment>\<open>A(P psi): names no world\<close>
  abbreviation "FrRefl \<equiv> \<forall>x. x\<^bold>r x"
  abbreviation "FrTrans \<equiv> \<forall>x y z. x\<^bold>r y \<and> y\<^bold>r z \<longrightarrow> x\<^bold>r z"
  abbreviation "FrSym \<equiv> \<forall>x y. x\<^bold>r y \<longrightarrow> y\<^bold>r x"
  abbreviation "FrUniv \<equiv> \<forall>x y. x\<^bold>r y"

text \<open>L with the world-free witness PosGlobal (Benzmueller's L_R_rigidpos, v4 session B, restated here).\<close>
lemma L_RP: assumes R: RigidPos and A: Ax1GenR shows "\<lfloor>P G\<rfloor>"
proof
  fix w
  have c: "ConjR G PosGlobal w"
  proof (intro allI impI)
    fix v z assume "w\<^bold>r v" "z\<^bold>@v"
    show "G z v \<longleftrightarrow> (\<forall>\<psi>. PosGlobal \<psi> \<longrightarrow> \<psi> z v)"
    proof
      assume "G z v" thus "\<forall>\<psi>. PosGlobal \<psi> \<longrightarrow> \<psi> z v" unfolding God_def by blast
    next
      assume h: "\<forall>\<psi>. PosGlobal \<psi> \<longrightarrow> \<psi> z v"
      { fix \<phi> assume pv: "P \<phi> v"
        have "PosGlobal \<phi>" using R pv by blast
        hence "\<phi> z v" using h by blast }
      thus "G z v" unfolding God_def by blast
    qed
  qed
  show "P G w" using A[THEN spec[where x=PosGlobal], THEN spec[where x=G], THEN spec[where x=w]] c by blast
qed

text \<open>Th4 with witnesses PosGlobal, the empty set, and {G}; no term names a world.\<close>
theorem Th4_RP: assumes R: RigidPos and A: Ax1GenR shows "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>Ex. G x)\<rfloor>"
proof
  fix w
  have L: "\<And>v. P G v" using L_RP[OF R A] by blast
  have top: "P (\<lambda>x. \<^bold>\<top>) w" using A[THEN spec[where x="\<lambda>\<psi>. False"], THEN spec[where x="\<lambda>x. \<^bold>\<top>"], THEN spec[where x=w]] by simp
  show "(\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>Ex. G x)) w"
  proof (rule ccontr)
    assume h: "\<not>(\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>Ex. G x)) w"
    have "P (\<lambda>x. \<^bold>\<bottom>) w" using A[THEN spec[where x="\<lambda>\<psi>. \<psi> = G"], THEN spec[where x="\<lambda>x. \<^bold>\<bottom>"], THEN spec[where x=w]] L h by simp
    thus False using top Ax2a[of "\<lambda>x. \<^bold>\<top>", rule_format, of w] by simp
  qed
qed

text \<open>With a universal relation (S5 read as one cluster) it is derivable, by Ax2b alone.\<close>
lemma RP_univ: assumes B: Ax2bH and U: FrUniv shows RigidPos
proof (intro allI impI)
  fix \<psi> u v assume "P \<psi> u"
  thus "P \<psi> v" using B[THEN spec[where x=\<psi>], THEN spec[where x=u]] U by blast
qed
end
