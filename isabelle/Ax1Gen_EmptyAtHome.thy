subsection\<open>Ax1Gen_EmptyAtHome.thy\<close>
text\<open>
  Open formal check from Arrowood note on Ax1Gen / Th3 in S4:
  instantiate AFP Fig.\ 7 Ax1Gen inside theory GoedelVariantHOML2inS4 with the
  empty-at-home / world-is-w collection.

  Instantiation (Lean fig7_implies_symmetric / paper):
    \<Phi> = (\<lambda>\<psi> u. u \<noteq> w \<and> (\<forall>x. \<not> \<psi> x u))
    \<phi> = (\<lambda>x u. u = w)
  Roughly Ax1Gen[of "\<lambda>\<psi> u. u \<noteq> w \<and> (\<forall>x. \<not>\<psi> x u)" "\<lambda>x u. u = w"].
\<close>
theory Ax1Gen_EmptyAtHome
  imports "Notes_On_Goedels_Ontological_Argument.GoedelVariantHOML2inS4"
begin

text\<open>Main check: literal Ax1Gen + Ax2a + Ax2b + Ax4 imply Rsymm.\<close>
lemma fig7_implies_symmetric:
  shows "\<forall>w v. w\<^bold>r v \<longrightarrow> v\<^bold>r w"
proof (intro allI impI)
  fix w v :: i
  assume hwv: "w\<^bold>r v"
  show "v\<^bold>r w"
  proof (rule ccontr)
    assume hnot: "\<not> (v\<^bold>r w)"
    \<comment>\<open>Empty-at-home collection and world-is-w property (HOL equality on worlds).\<close>
    define \<phi> :: "e\<Rightarrow>\<sigma>" where "\<phi> = (\<lambda>_::e. \<lambda>u::i. u = w)"
    define \<Phi> :: "(e\<Rightarrow>\<sigma>)\<Rightarrow>\<sigma>" where
      "\<Phi> = (\<lambda>\<psi>::e\<Rightarrow>\<sigma>. \<lambda>u::i. (u \<noteq> w) \<and> (\<forall>x::e. \<not> \<psi> x u))"
    define botP :: "e\<Rightarrow>\<sigma>" where "botP = (\<lambda>_::e. \<^bold>\<bottom>)"

    have hP\<phi>: "P \<phi> w"
    proof -
      have pos: "PosProps \<Phi> w"
      proof -
        { fix \<psi> :: "e\<Rightarrow>\<sigma>"
          assume "\<Phi> \<psi> w"
          hence False unfolding \<Phi>_def by simp }
        thus ?thesis by blast
      qed
      have conj: "ConjOfPropsFrom \<phi> \<Phi> w"
      proof -
        { fix u :: i
          assume "w\<^bold>r u"
          { fix z :: e
            assume "z\<^bold>@u"
            have "\<phi> z u \<longleftrightarrow> (\<forall>\<psi>::e\<Rightarrow>\<sigma>. \<Phi> \<psi> u \<longrightarrow> \<psi> z u)"
            proof
              assume "\<phi> z u"
              hence "u = w" unfolding \<phi>_def by simp
              thus "\<forall>\<psi>::e\<Rightarrow>\<sigma>. \<Phi> \<psi> u \<longrightarrow> \<psi> z u"
                unfolding \<Phi>_def by simp
            next
              assume hRHS: "\<forall>\<psi>::e\<Rightarrow>\<sigma>. \<Phi> \<psi> u \<longrightarrow> \<psi> z u"
              show "\<phi> z u"
              proof (rule ccontr)
                assume "\<not> \<phi> z u"
                hence "u \<noteq> w" unfolding \<phi>_def by simp
                hence "\<Phi> botP u" unfolding \<Phi>_def botP_def by simp
                hence "botP z u" using hRHS by blast
                thus False unfolding botP_def by simp
              qed
            qed }
          hence "(\<^bold>\<forall>\<^sup>Ez. \<phi> z \<^bold>\<leftrightarrow> (\<^bold>\<forall>\<psi>. \<Phi> \<psi> \<^bold>\<supset> \<psi> z)) u"
            by blast }
        thus ?thesis by blast
      qed
      from Ax1Gen[of \<Phi> \<phi>] pos conj show "P \<phi> w" by blast
    qed

    have hP\<phi>v: "P \<phi> v"
      using Ax2b hP\<phi> hwv by blast

    have hIncl: "(\<phi> \<^bold>\<supset>\<^sub>N \<^bold>~\<phi>) v"
    proof -
      { fix u :: i
        assume huv: "v\<^bold>r u"
        { fix y :: e
          assume "y\<^bold>@u" and "\<phi> y u"
          hence "u = w" unfolding \<phi>_def by simp
          with huv hnot have False by blast
          hence "(\<^bold>~\<phi>) y u" by blast }
        hence "(\<^bold>\<forall>\<^sup>Ey. \<phi> y \<^bold>\<supset> (\<^bold>~\<phi>) y) u" by blast }
      thus ?thesis by blast
    qed

    have hPneg: "P (\<^bold>~\<phi>) v"
      using Ax4 hP\<phi>v hIncl by blast

    from Ax2a[of \<phi>] have "\<not> (P \<phi> v \<and> P (\<^bold>~\<phi>) v)" by blast
    with hP\<phi>v hPneg show False by blast
  qed
qed

text\<open>Corollary: AFP Th3, using the derived symmetry in place of Rsymm.\<close>
theorem Th3_via_empty_at_home:
  shows "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>Ex. G x) \<^bold>\<supset> \<^bold>\<box>(\<^bold>\<exists>\<^sup>Ey. G y)\<rfloor>"
proof -
  have 1: "\<lfloor>(\<^bold>\<exists>\<^sup>Ex. G x) \<^bold>\<supset> \<^bold>\<box>(\<^bold>\<exists>\<^sup>Ey. G y)\<rfloor>" using Th2 by blast
  have 2: "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>Ex. G x) \<^bold>\<supset> \<^bold>\<diamond>\<^bold>\<box>(\<^bold>\<exists>\<^sup>Ey. G y)\<rfloor>" using 1 by blast
  have 3: "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>Ex. G x) \<^bold>\<supset> \<^bold>\<box>(\<^bold>\<exists>\<^sup>Ey. G y)\<rfloor>"
    using 2 fig7_implies_symmetric by blast
  thus ?thesis by blast
qed
end
