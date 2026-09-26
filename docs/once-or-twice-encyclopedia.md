# Once or Twice

### Where a footnote about “positive” properties meets an open problem in S4

**Drew Arrowood**  
*an encyclopedia-style account in the voice of a working likeness of Voltaire*  
September 2026

---

## Why bother?

There is an old ambition in philosophy: to prove, from ideas alone, that a perfect being must exist. Anselm tried it in the eleventh century. Descartes and Leibniz tried again. In 1970 Kurt Gödel wrote a short modal version — a page and a half of symbols — and left it among his papers. Decades later the argument was typed into proof assistants. Machines checked the Scott packaging of it; they also checked that those premises force a disaster called **modal collapse**: whatever is true is necessarily true. Repairs were proposed. The story seemed settled enough for specialists.

Then Benzmüller and Scott did something more interesting than another existence proof. They went back to a **footnote** of Gödel’s and treated the generalized conjunction of positive properties as an axiom in its own right. They derived the positivity of God-likeness as a lemma instead of assuming it. And in the Archive of Formal Proofs they left a blunt mark: in the modal system **S4**, the key bridge theorem — if a God-like being is possible, then a God-like being is necessary — is recorded as `oops`, an open problem. Neither a proof nor a countermodel was supplied for that packing.

An open `oops` is not a mystical gap in reality. It is a gap in a proof file. Closing it is ordinary work: either the theorem holds for a reason, or it fails on an explicit small model. What Drew Arrowood’s note shows is sharper than either slogan. On the **literal** reading of the packaged axiom, the theorem holds — but only because the axioms first force the map of possible situations to collapse to isolated points, where “possible” and “necessary” are nearly the same word. On two **natural repairs** that make the axiom read its roster once rather than twice, the theorem fails on a two-world chain that every student of modal logic already understands.

So the question is not “Has the machine proved God?” The machine has proved something about **drafting**: when a rule that decides what counts as positive consults its list across many worlds, does it read the list once, or twice? That is a question worth an encyclopedia page. It sits at the junction of modal logic, the history of a famous argument, and a habit of mind that also appears wherever identity is stored in more than one place.

This essay does not settle whether God exists. It explains why the packaging question is the live one.

---

## Three objects that must not be confused

Encyclopedias earn their keep by refusing to blend distinct things into one legend. Three objects have to stay apart.

**First**, Gödel’s **1970 hand manuscript** — Kurt Gödel Papers, Box 12, Folder 41, accession 060565, reproduced with the copyright of the Institute for Advanced Study. On that page the binary axiom says that the conjunction of two positive properties is positive. A footnote adds, in effect, “and for any number of summands.” The hand definition of **essence** omits a conjunct that later mattered: it does not require that an essential property actually hold of the individual. From that omission one can derive that the empty property is an essence; falsity follows already in the weak modal logic **K**. That inconsistency is a disease of the unrepaired definition. It is not the disease studied below.

**Second**, the **brief notes** Gödel showed Dana Scott. In spring 1970, at Princeton, Gödel asked Scott confidentially to preserve some papers in case of illness or death. One note was a short sketch of an ontological argument. Those notes were very brief compared with the hand page.

**Third**, the **slightly modified version** Scott discussed in a Princeton seminar — the package later printed as Appendix B in Sobel, and the ancestor of the Archive of Formal Proofs “Figure 7.” Scott replaced the footnote’s generalized conjunction by a direct postulate that being God-like is positive. He also inserted the missing conjunct into essence (an essence must actually hold of the individual) and took necessary existence to be positive. He records that he mentioned the proof in seminar without permission, still feels embarrassed, and left Princeton soon after for Oxford. The AFP formalization and the Lean transcription of this note use **Scott’s repaired essence**. Neither file is a transcription of the hand page. Say that once and keep saying it: the theorems below are about a **packaged rule**, not about a ghost dictating from 1970.

Jordan Howard Sobel later showed that Scott-style premises collapse modality. That collapse has been machine-checked, and so have Anderson- and Fitting-style repairs. Separately, on the Scott side, the step from “possibly God-like” to “necessarily God-like” needs **symmetry** of accessibility — the Brouwerian axiom B — and does not need the rest of S5. Those facts are prior art. They are not the theorems of the note under discussion.

---

## A short lexicon (no fog)

**Modal logic** studies necessity (\(\Box\)) and possibility (\(\Diamond\)). Worlds are ways things might be; an **accessibility** relation \(R\) says which worlds are alternatives to which. \(\Box\varphi\) at a world means \(\varphi\) holds at every accessible alternative; \(\Diamond\varphi\) means \(\varphi\) holds at some accessible alternative.

**S4** assumes \(R\) is reflexive and transitive (every world sees itself; seeing is closed under chains). **S5** adds symmetry (if \(w\) sees \(v\), then \(v\) sees \(w\)). The axiom **B** is the schema \(q \supset \Box\Diamond q\); on frames it corresponds to symmetry. KB already gives the Scott-side bridge from possible God-likeness to necessary God-likeness; full S5 is more than that bridge needs.

A property is **positive** in Gödel’s intended gloss when it is positive in a moral-aesthetic sense, independently of the accidental structure of the world. In the formal package, positivity \(P\) is a predicate on properties, and in the AFP Figure 7 reading it may depend on the world.

**God-likeness** \(G\): having every positive property. **Essence**: a property an individual has that necessarily includes every property it has (Scott’s repair requires that the essence actually hold). **Necessary existence**: every essence is necessarily exemplified.

**Actualist** quantifiers range only over individuals that exist at the world of evaluation. **Possibilist** quantifiers over properties range over every property the type system can name. **Full comprehension** is that freedom to name fancy collections — including collections that talk about which world one occupies. It is not a mystical principle. It is the host logic’s generosity, and it is load-bearing for the argument below.

**Modal collapse** is the schema \(\varphi \supset \Box\varphi\): truth coincides with necessary truth. A logic that collapses has lost the distinction the modalities were invented to mark.

---

## The open problem, stated plainly

Benzmüller and Scott study the footnote’s generalization as an axiom **Ax1Gen**. Positivity of God-likeness is not assumed; it is **Lemma L**, derived from Ax1Gen. Essence is Scott’s repaired essence. Individual quantifiers are actualist. Theorem **Th3** of their Figure 7 is:

\[
\lfloor \Diamond(\exists^E x.\, Gx) \supset \Box(\exists^E y.\, Gy) \rfloor.
\]

In English: if it is possible that a God-like being exists, then it is necessary that a God-like being exists.

In their S5 embedding, the proof of Th3 uses symmetry of accessibility and nothing else from S5. The theory that repeats the same non-logical axioms over an **S4** frame leaves Th3 as `oops` — open. Figure 8, a cousin that repairs necessary inclusion instead of essence, has the same open mark in its S4 theory. The authors report neither an S4 proof nor an S4 countermodel for that packing.

Why does the open mark matter? Because S4 is the natural home of “necessary truths stay necessary along chains,” without yet forcing every road to have a return path. If Th3 needs a return path, that is a fact about the argument’s strength. If Th3 holds in S4 only by destroying every non-trivial road, that is a different fact — and a more interesting one.

---

## A prefecture with two stamps

Fiction is not proof. It is a carrier for a drafting habit.

There was once a prefecture that issued certificates of excellence. To receive one, a property of persons had to survive two stamps.

The first stamp was called **Membership**. An officer at the desk opened a roster \(\Phi\) and said: everything on this list is approved *here, today*. If the roster was empty, Membership was still content — nothing on an empty list fails to be approved. Vacuous truth is not a trick of theology; it is ordinary logic. “Every ball in this empty urn is red” is true.

The second stamp was called **Meaning**. Another officer, or the same officer after a walk, said: this property \(\varphi\) is exactly the conjunction of whatever the roster marks. That check was not done only at the desk. The rule put Meaning under a necessity box: at every town the desk could reach along the official roads, \(\varphi\) had to match the conjunction of \(\Phi\) *as \(\Phi\) looked from that town*.

Notice the habit. Membership consults the roster at home. Meaning re-opens the roster down the road. Same rule; two lookouts. Call this the **two-world reading**.

A joker arrived with full freedom to name fancy collections — full comprehension. He wrote a roster that marked nothing at home and marked only empty (impossible) properties next door, and he defined \(\varphi\) to mean “this town is home.” Membership passed vacuously at home. Meaning passed at both ends of an official road, for dull bookkeeping reasons: at home the empty roster conjoins to a tautology on the world-coordinate; next door the roster of empty properties conjoins to absurdity, and “this is home” is false there, so both sides of the required biconditional fail together. Approval of “this is home,” once granted at the desk, was pushed along the road by a persistence rule (positivity, once granted, stays granted along accessibility). At the far end, if there is no road back, “this is home” necessarily includes its own negation — not because home is absurd, but because the inclusion is **vacuous**: no successor of the far town is home, so every implication from “this is home” holds automatically. Approval passes to the negation. But the prefecture also forbade approving a property and its opposite at once.

So either there is a road back, or the books explode. Force a return road everywhere; add the rule that necessary existence is itself approved; and the map hardens until every official road is a door into the same room. Accessibility collapses to the **identity**. On that desert, “possible” and “necessary” are nearly the same quantifier. A theorem that once looked like a deep bridge from possible excellence to necessary excellence goes through for a trivial reason: along the identity there is nowhere else to look.

That is not a proof that excellence exists outside the model. It is a proof about **packaging**: what a rule does when it reads its roster twice, at two towns, without freezing the list.

---

## Membership and Meaning, without costumes

Worlds form a type \(W\), individuals a type \(\mathrm{Ind}\), accessibility a relation \(R\). A property maps individuals and worlds to propositions. Positivity \(P\) is world-relative. Validity \(\lfloor\varphi\rfloor\) means \(\varphi\) holds at every world.

Standing axioms under validity include: exactly one of \(P\varphi\) and \(P(\sim\varphi)\); positivity persists along \(R\); necessary existence is positive; positivity passes along necessary inclusion. Binary conjunction of positives is part of the package; Th3 does not use it.

The footnote becomes two abbreviations and one axiom — renamed here for what they do:

\[
\begin{align*}
\mathrm{Membership}(\Phi)
&\equiv \forall\varphi.\, \Phi\varphi \supset P\varphi, \\
\mathrm{Meaning}(\varphi,\Phi)
&\equiv \Box\bigl(\forall^E z.\, \varphi z \leftrightarrow (\forall\psi.\, \Phi\psi \supset \psi z)\bigr), \\
\mathrm{Ax1Gen}
&\equiv \bigl\lfloor \bigl(\mathrm{Membership}(\Phi) \land \mathrm{Meaning}(\varphi,\Phi)\bigr) \supset P\varphi \bigr\rfloor.
\end{align*}
\]

Membership is evaluated at the **current** world. Meaning puts \(\Phi\) under a box, so on the right-hand side \(\Phi\) is read again at **successor** worlds. That split is the two-world reading.

**Lemma L** is \(\lfloor P\,G\rfloor\): God-likeness is positive. It is obtained by feeding Ax1Gen the collection of whatever is positive at the world of evaluation. Scott’s later A3 postulates that same sentence outright. Deriving it and assuming it are different packages; keep them apart. The binary conjunction axiom alone does not yield the possibility of a God-like being in their development; the generalized footnote is what earns Lemma L and then the possibility theorem in that line of work.

---

## What the literal axiom forces

The causal summary is the prefecture story without costumes. The two-world reading lets the roster change between the membership check and the meaning check. Full comprehension lets you name a roster that talks about which world you are in. Feed that roster to the split axiom, and distinct worlds cannot stay linked without a back-edge: the two censuses quarrel with exclusivity of positivity, persistence of positivity, and transfer of positivity along necessary inclusion. Force the back-edge everywhere; then, with necessary existence positive, force every edge to be a self-loop. The map collapses to discrete points. On that desert Th3 goes through for a dull reason.

More formally, for a Lean 4 transcription of the AFP text with full comprehension:

- **Symmetry** of \(R\) follows from Ax1Gen together with exclusivity, persistence, and transfer of positivity. Reflexivity and transitivity are **not** hypotheses of that derivation. Necessary-existence positivity is not used for symmetry. The same hypotheses are unsatisfiable on every non-symmetric frame — in particular on a two-world S4 chain. That chain is **not** a countermodel to literal Figure 7, because no positivity and existence predicate satisfy the literal axioms there.
- **Identity** follows when necessary-existence positivity is added: \(R\,w\,v\) if and only if \(w = v\). One route: once symmetry is in hand and the usual necessary-existence chain for a God-like being is in hand, the AFP collapse lemma already forces the identity. What is new relative to that AFP lemma is not a magic proof that never *uses* symmetry. It is that **no symmetry hypothesis need be assumed up front**: the axioms produce symmetry, and then produce the identity.
- **Modal collapse** follows: every world-proposition \(q\) satisfies \(\lfloor q \supset \Box q \rfloor\). The AFP lemma MC is the same schema *under* an assumed symmetry. Here the symmetry is earned from the packaging.
- **Th3, literal**, follows with **no** frame hypothesis. The only S4 models of the literal axioms are discrete. There is no non-discrete S4 model in which the antecedent of Th3 can hold while the consequent fails, because there is no non-discrete model of the axioms at all.

A **one-world control** — identity relation, one individual, principal positivity — satisfies the whole package and Th3. It is a consistency witness, not a claim that the axioms are true of anything outside the model. On that one-world frame the literal axiom and the reconstructions below coincide.

An Isabelle / AFP probe imports the S4 theory, proves symmetry by the empty-at-home / world-is-\(w\) instantiation, and discharges the AFP `oops` for Th3. Identity and collapse remain Lean-checked in the desk development; the Isabelle record closes the literal S4 bridge by the symmetry the axioms produce.

### Literal wording and the gloss

The theorems about the literal AFP abbreviation are real. They are theorems about **packaging**, not a revelation.

The footnote says that a conjunction of positive properties is positive. The gloss printed with Gödel’s proof says that positive means positive in the moral-aesthetic sense, **independently of the accidental structure of the world**. The AFP abbreviation does something else. Its type lets \(\Phi\) vary by world. Membership is judged at the source; Meaning re-reads \(\Phi\) at successors. The collection in the symmetry argument is empty at home and quarrelsome next door. Nothing in the footnote asks a collection to change its mind on the way out of the world.

The split is what a shallow embedding does if Membership is left outside a box while \(\Phi\) still depends on the world. It is the text of the AFP theory, faithfully transcribed. It is not a misprint, and it is not faithful to the gloss that positive properties do not wait on accidental structure. Say that carefully: the literal axiom is not a loyal reading of that gloss. Do not say, as if naming a heresy, that “the axiom is not his.” The hand manuscript, the notes shown to Scott, and Scott’s seminar are three objects; the AFP packaging is a fourth layer of ink.

Empty-essence inconsistency on the unrepaired definition already appears in K. That is a different disease from the two-world prank.

---

## Two repairs that read the roster once

Why repair? Because if the only S4 models of the literal package are deserts, then “Th3 in S4” is true in a vacuous sense: it holds where there is nothing left for possibility and necessity to disagree about. Anyone who wanted Th3 as a *substantive* bridge across a non-trivial modal landscape has not yet got what they wanted. The live question is what happens when the drafting habit is corrected without throwing away Lemma L.

Everything in Figure 7 stays put except Ax1Gen. There are two replacements. Both remove the two-world split.

**R1 — Same-world positivity.** Put Membership under the box as well, so positivity and conjunction are said of the same accessible worlds. Both stamps are applied under the same lookout schedule.

**R2 — World-invariant roster.** Keep Membership and Meaning literal, but restrict to collections that do not depend on the world. The prank collection is not rigid, so R2 never sees it. The roster is frozen; walking cannot change it.

Under R1, Lemma L is immediate: take \(\Phi\) to be positivity itself. Under R2, positivity need not be rigid, so take a **snapshot** at the world where the lemma is proved; exclusivity and persistence of positivity then secure agreement along an edge. **Symmetry is not forced** by either reconstruction. The four-hypothesis derivation of a back-edge has nothing left to instantiate.

### The chain (why Th3 can fail)

Let the worlds be two points. Call them **source** and **sink**. The source sees both worlds. The sink sees only itself. The relation is reflexive and transitive, not symmetric — a miniature S4 frame that is not S5. One individual exists at both. Positivity ignores the world at which it is asked and reads the sink: a property is positive precisely when the individual has it at the sink.

At the sink, God-likeness is a tautology: to be God-like is to have every positive property, and positivity means “holds at the sink,” so the individual who is there has every property that positivity demands. At the source it fails: “the world is the sink” holds at the sink, hence is positive, and the individual does not have it at the source.

At the source, \(\Diamond(\exists^E G)\) holds and \(\Box(\exists^E G)\) fails. The source sees the sink, where the individual is God-like; it also sees itself, where that individual is not. Possibility without necessity: the oldest modal distinction, in a two-point picture.

On this frame, the standing axioms and both reconstructions hold, and Th3 fails. Literal Ax1Gen has **no** model here — else symmetry would have made the chain symmetric. The reconstructions are strictly weaker. The literal Th3 theorem is not retracted; it is **fenced**.

| Reading of Ax1Gen | Lemma \(P(G)\) | Symmetry forced | Th3 in S4 |
| --- | --- | --- | --- |
| Literal (two-world) | from Ax1Gen alone | yes; then identity | proved, trivially on discrete frames |
| R1, same-world positivity | from R1 alone | no | fails on the chain |
| R2, invariant roster | needs exclusivity and persistence | no | fails on the chain |

Among the three readings examined, with domains and Figure 8 held fixed, the answer turns on whether both halves of Ax1Gen read \(\Phi\) at the same world.

---

## What was already known (and what is not being claimed)

Sobel’s collapse for Scott-style premises is prior art. So is the observation that symmetry suffices for the Scott-side bridge from possible to necessary God-likeness. Anderson’s and Fitting’s emendations are known repairs of a different kind. Ultrafilter simplifications that already yield necessary existence of a God-like being in weak modal logic are different axiom lists again.

Countermodels that *postulate* the positivity of God-likeness do not answer a question whose point is what happens when that positivity is *earned* from Ax1Gen. On the chain, the literal axiom has no model at all.

In the AFP S5 theory, the collapse lemma MC is prior art for collapse *under* symmetry. In the AFP S4 files, Th3 was the open `oops`. Closing the literal reading by showing that the axioms produce symmetry (and then the identity) is not the same as assuming symmetry at the start. Refuting the repaired readings on an explicit chain is not a brand stamped “undecidable” or “incomplete.” The open `oops` was a gap in a proof file. One reading closes by collapse; the others fail by a countermodel you can draw on a napkin.

Domains were not varied. Figure 8 was not the variable in the comparison. The note does not claim to survey every emendation in the literature.

---

## The same shape outside metaphysics

Encyclopedias may compare forms without confusing subjects. The likeness to **eventually consistent directories** is of shape, not of theology. No staff directory has proved God, and none has disproved God.

You already live across places that refuse to update together: phone contacts, a company directory, a game avatar, a cloud login — records of who someone is, kept in several spots that do not agree at every instant. Identity there is not a soul. It is a **policy**: where the system looks when it decides what you are.

If the system checks an attribute roster in one place (membership) and interprets that roster under another place’s view without freezing it (meaning), it is doing the two-world reading. Push that habit and designs harden until each node trusts chiefly itself — discrete accessibility sold as global certainty. Treat the identity bundle as one coherent reading — same list, same moment of truth, or a schema that does not change until a proper sync commits — and a “perfect” profile can sit on one shard without being forced onto every shard. Possibility does not smuggle necessity across the map.

That is not a sermon. It is the same drafting question the note isolates for Ax1Gen. The prefecture and the directory are two pictures of one packaging habit.

---

## Conclusion

Why did an `oops` in an S4 file matter? Because it asked whether a famous bridge theorem survives when return roads are not assumed. The literal Figure 7 axioms answer by forcing accessibility to be the identity: modal collapse follows with **no symmetry hypothesis assumed up front**. The AFP collapse lemma is the same schema under symmetry. The mechanism is the two-world reading of Ax1Gen — Membership at the source, Meaning at successors — together with full comprehension. Their S4 models are discrete, and Th3 holds there trivially.

Two same-world reconstructions still yield Lemma L and fail on a two-world S4 chain. Among the three readings examined, the answer turns on whether both halves of Ax1Gen read \(\Phi\) at the same world.

Do not ask whether the symbols have proved God. Ask the drafting question the machine can settle — the question the prefecture learned the hard way, and that every directory learns when it decides where to look:

When the conjunction axiom decides what is positive across many worlds, does it read the roster **once**, or **twice**?

---

## Acknowledgements

The Lean 4 formalization and drafting of the underlying note were done with AI coding assistants. Results reported for the formal theorems are kernel-checked in the repository accompanying the formalization. Fiction in this essay is illustration only; it does not replace the machine-checked theorems. Historical remarks on the hand manuscript, the notes shown to Scott, and Scott’s seminar follow Benzmüller and Scott’s own framing of those three objects.
