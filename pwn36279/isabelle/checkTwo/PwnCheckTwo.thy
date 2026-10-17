theory PwnCheckTwo imports Ax1GenAlternativesTwo.Ax1GenAlternativesTwo
begin
text \<open>Arrowood, "One World or Two": the Ax1Gen instance of isabelle/Ax1Gen_EmptyAtHome.thy
  (session Ax1Gen_EmptyAtHome_Check) re-examined in Benzmueller's session E
  (arXiv:2609.36279v2 ancillary, variant 2 = AFP Fig. 7, logic K, Ax1GenTwo as hypothesis).\<close>

text \<open>1. Our collection is EMPTY at the world of evaluation, so it is not an Ax1GenTwo instance.\<close>
lemma empty_at_home_not_TwoMembers:
  "\<not> TwoMembers (\<lambda>\<psi> u. u \<noteq> w \<and> (\<forall>x. \<not> \<psi> x u)) w" by simp


text \<open>2. Symmetry (indeed R = identity) still follows from Ax1GenTwo -- but only through
  Benzmueller's nominal argument (ae_Two / R_Id use OneWorld at the nominal \<lambda>x t. t = u).\<close>
theorem symm_Two_hybrid: assumes A: "Ax1GenTwo" shows "FrSymm"
proof (intro allI impI)
  fix x y assume r: "x\<^bold>r y"
  have "y = x" by (rule R_Id[OF A r])
  thus "y\<^bold>r x" using ReflR[OF A] by simp
qed

text \<open>3. Our own empty-at-home route, replayed under Ax1GenTwo: it needs the full Ax1Gen back,
  which Ax1GenTwo yields only via Ax1Gen_of_Two (hybrid).\<close>
theorem symm_Two_via_empty_at_home: assumes A: "Ax1GenTwo"
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
      have G: "Ax1GenS" by (rule Ax1Gen_of_Two[OF A])
      from G[THEN spec[of _ \<Phi>], THEN spec[of _ \<phi>], THEN spec[of _ w]] pos conj show "P \<phi> w" by blast
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


text \<open>4. Th3 (the Monatshefte Fig. 7 S4 question) under Ax1GenTwo: hybrid-free given an actual
  individual at every world (Th3_Two), unconditional only with the nominal (ae_Two).\<close>
theorem Th3_Two_unconditional: assumes A: "Ax1GenTwo"
  shows "\<lfloor>\<^bold>\<diamond>(\<^bold>\<exists>\<^sup>Ex. G x) \<^bold>\<supset> \<^bold>\<box>(\<^bold>\<exists>\<^sup>Ey. G y)\<rfloor>"
  using G_ex_Two_unconditional[OF A] by blast
end
