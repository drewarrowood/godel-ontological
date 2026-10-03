theory PwnSanity imports Th4FromConjunction.Th4FromConjunction
begin
  lemma true_thing: "\<lfloor>P (\<lambda>x. \<^bold>\<top>) \<^bold>\<supset> P (\<lambda>x. \<^bold>\<top>)\<rfloor>" nitpick[card i=1-2, card e=1-2, timeout=60, expect=genuine] oops
end
