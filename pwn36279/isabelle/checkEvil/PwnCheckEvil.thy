theory PwnCheckEvil imports Ax1GenAlternativesV3Two.Ax1GenAlternativesV3Two
begin
(* Added 18 Oct 2026. AFP ThereIsNoEvil2 (Monatshefte Fig. 11) definition of Evil, in Benzmueller's
   session F of arXiv:2609.36279v4 (variant 3, Fig. 8 inclusion with the non-emptiness clause).
   NecNoEvil is derived from Ax2a and Ax4 alone, with no conjunction axiom (Ax1, Ax1Gen, Ax1GenTwo
   are not used), provided the type of individuals has two members. *)
definition Evil ("Evil") where "Evil x \<equiv> \<^bold>\<forall>\<phi>. \<^bold>\<not> P \<phi> \<^bold>\<supset> \<phi> x"
(* No conjunction axiom at all: with at least two individuals, Ax2a and Ax4 suffice. *)
lemma NecNoEvil_two_individuals: assumes D: "\<exists>a b::e. a \<noteq> b" shows "\<lfloor>\<^bold>\<box>(\<^bold>\<not>(\<^bold>\<exists>\<^sup>Ex. Evil x))\<rfloor>"
proof (intro allI impI notI)
  fix w v assume "w \<^bold>r v" and ex: "(\<^bold>\<exists>\<^sup>Ex. Evil x) v"
  from ex obtain x where Ev: "Evil x v" by auto
  have ev: "\<And>\<phi>. \<not> P \<phi> v \<Longrightarrow> \<phi> x v" using Ev unfolding Evil_def by blast
  have x2: "\<And>\<phi>. P \<phi> v \<longleftrightarrow> \<not> P (\<^bold>~\<phi>) v"
  proof -
    fix \<phi> show "P \<phi> v \<longleftrightarrow> \<not> P (\<^bold>~\<phi>) v" using Ax2a[of \<phi>] by meson
  qed
  have notEq: "\<not> P (\<lambda>y. y \<^bold>= x) v"
  proof
    assume "P (\<lambda>y. y \<^bold>= x) v"
    hence "\<not> P (\<^bold>~(\<lambda>y. y \<^bold>= x)) v" using x2[of "\<lambda>y. y \<^bold>= x"] by blast
    hence "(\<^bold>~(\<lambda>y. y \<^bold>= x)) x v" by (rule ev)
    thus False by simp
  qed
  have same: "(\<^bold>~(\<lambda>y. y \<^bold>\<noteq> x)) = (\<lambda>y. y \<^bold>= x)" by (rule ext, rule ext, simp)
  have "\<not> P (\<^bold>~(\<lambda>y. y \<^bold>\<noteq> x)) v" using notEq same by simp
  hence Pne: "P (\<lambda>y. y \<^bold>\<noteq> x) v" using x2[of "\<lambda>y. y \<^bold>\<noteq> x"] by blast
  from D obtain a b::e where ab: "a \<noteq> b" by auto
  have "\<exists>c. c \<noteq> x" using ab by metis
  then obtain c where cx: "c \<noteq> x" by auto
  have ne: "(\<lambda>y. y \<^bold>\<noteq> x) \<noteq> (\<lambda>x. \<^bold>\<bottom>)"
  proof
    assume h: "(\<lambda>y. y \<^bold>\<noteq> x) = (\<lambda>x. \<^bold>\<bottom>)"
    show False using arg_cong[where f="\<lambda>F. F c v", OF h] cx by simp
  qed
  have incl: "((\<lambda>y. y \<^bold>\<noteq> x) \<^bold>\<supset>\<^sub>N (\<lambda>y. \<^bold>\<top>)) v" using ne by simp
  have ax4: "(P (\<lambda>y. y \<^bold>\<noteq> x) \<^bold>\<and> ((\<lambda>y. y \<^bold>\<noteq> x) \<^bold>\<supset>\<^sub>N (\<lambda>y. \<^bold>\<top>)) \<^bold>\<supset> P (\<lambda>y. \<^bold>\<top>)) v"
    by (rule Ax4[THEN spec])
  have PT: "P (\<lambda>y. \<^bold>\<top>) v" using ax4 Pne incl by simp
  hence "\<not> P (\<^bold>~(\<lambda>y. \<^bold>\<top>)) v" using x2[of "\<lambda>y. \<^bold>\<top>"] by blast
  hence "(\<^bold>~(\<lambda>y. \<^bold>\<top>)) x v" by (rule ev)
  thus False by simp
qed
end
