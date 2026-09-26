# Once or Twice

**Drew Arrowood**  
*rewritten in the voice of a working likeness of Voltaire — with a short fiction to carry the machinery*  
September 2026

---

## A prefecture with two stamps

There was once a prefecture that issued certificates of excellence. To receive one, a property of persons had to survive two stamps.

The first stamp was called **Membership**. An officer at the desk opened a roster \(\Phi\) and said: everything on this list is approved here, today. If the roster was empty, Membership was still happy — nothing on an empty list fails to be approved.

The second stamp was called **Meaning**. Another officer, or the same officer after a walk, said: this property \(\varphi\) is exactly the conjunction of whatever the roster marks. That check was not done only at the desk. The rule put Meaning under a necessity box: at every town the desk could reach along the official roads, \(\varphi\) had to match the conjunction of \(\Phi\) *as \(\Phi\) looked from that town*.

Notice the drafting habit. Membership consults the roster at home. Meaning re-opens the roster down the road. Same rule; two lookouts. Call this the **two-world reading**.

A joker arrived with full freedom to name fancy collections — what the logicians call **full comprehension**. He wrote a roster that marked nothing at home and marked a contradiction next door, and he defined \(\varphi\) to mean “this town is home.” Membership passed vacuously. Meaning passed at both ends of an official road, for dull bookkeeping reasons. Approval of “this is home,” once granted at the desk, was pushed along the road by a persistence rule. At the far end, “this is home” necessarily included its own negation whenever there was no road back — the inclusion was vacuous, because no successor of the far town was home. Approval passed to the negation. But the prefecture also forbade approving a property and its opposite at once.

So either there is a road back, or the books explode. Force a return road everywhere, add the rule that necessary existence is itself approved, and the map hardens until every official road is a door into the same room. The accessibility relation collapses to the **identity**. On that desert, “possible” and “necessary” are nearly the same quantifier. A theorem that once looked like a deep bridge from possible excellence to necessary excellence goes through for a trivial reason: along the identity there is nowhere else to look.

That is not a proof that excellence exists outside the model. It is a proof about **packaging**: what a rule does when it reads its roster twice, at two towns, without freezing the list.

---

## What the note is about

Around 1970 Kurt Gödel wrote a short modal version of the ontological argument. The first axiom says that the conjunction of two positive properties is positive. A footnote extends the claim from two summands to any collection: the conjunction of positive properties is itself positive.

Three objects must stay apart, or the story turns into superstition dressed as scholarship:

1. the **1970 hand manuscript** (Nachlass Box 12 / Folder 41 / accession 060565);
2. the **notes Gödel allowed Scott to copy**;
3. **Scott’s seminar packaging**, later recorded in the Archive of Formal Proofs as actualist Figure 7 — including Scott’s repair of essence with the conjunct \(\varphi x\), and necessary existence taken as positive.

Dana Scott rearranged the package. In his notes the generalized conjunction is often replaced by a direct postulate that being God-like is positive. Sobel showed that Scott-style premises collapse modality: whatever is true is necessarily true. That collapse has been machine-checked, and so have Anderson- and Fitting-style repairs. Separately, the step from “possibly God-like” to “necessarily God-like” on the Scott side needs **symmetry** of accessibility (the Brouwerian axiom B), and does not need the rest of S5.

Benzmüller and Scott return to the footnote. They study Gödel’s generalized conjunction as an axiom they call **Ax1Gen**. Positivity of God-likeness is not assumed; it is **Lemma L**, derived from Ax1Gen. Essence keeps Scott’s extra conjunct. Individual quantifiers are **actualist**. In their Figure 7, Theorem **Th3** is:

\[
\lfloor \Diamond(\exists^E x.\, Gx) \supset \Box(\exists^E y.\, Gy) \rfloor.
\]

In the S5 embedding, Th3 uses symmetry and nothing else from S5. The theory `GoedelVariantHOML2inS4` repeats the non-logical axioms over an S4 frame — reflexive and transitive; symmetry *not* assumed — and leaves Th3 as `oops`, marked open. Neither an S4 proof nor an S4 countermodel is reported there for that packing.

**What the note shows**, for a Lean 4 transcription of that AFP text, with full comprehension:

1. The **literal** reading of Ax1Gen proves Th3 — but by forcing accessibility to be the identity. The only S4 models are discrete; Th3 holds there trivially.
2. Two **same-world reconstructions** of Ax1Gen still yield Lemma L, do not force symmetry, and **refute** Th3 on a two-world S4 chain.

Among the three readings examined, with domains and Figure 8 held fixed, the answer turns on whether both halves of Ax1Gen read \(\Phi\) at the same world.

This paper does not settle whether God exists. It settles where a packaged rule looks when it decides what “positive” means.

---

## Membership and Meaning

Worlds form a type \(W\), individuals a type \(\mathrm{Ind}\), accessibility a relation \(R\). A property is a map from individuals and worlds to propositions. **Positivity** \(P\) is world-relative. Necessity and possibility quantify along \(R\). Validity \(\lfloor\varphi\rfloor\) means \(\varphi\) holds at every world. An existence predicate says who is present; **actualist** quantifiers restrict to existents. Quantifiers over properties stay **possibilist**: full comprehension — the freedom to name collections that talk about which world one occupies. That freedom is load-bearing. It is the joker’s license in the prefecture story.

God-likeness \(G\): having every positive property. Essence: a property the individual has that necessarily includes every property it has (Scott’s repair includes the conjunct that the essence actually holds). Necessary existence \(E\): every essence is necessarily exemplified.

Standing axioms under validity: binary conjunction of positives (Ax1); exactly one of \(P\varphi\) and \(P(\sim\varphi)\) (Ax2a); positivity persists along \(R\) (Ax2b); necessary existence is positive (Ax3); positivity passes along necessary inclusion (Ax4).

The footnote becomes two abbreviations and one axiom:

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

Membership is evaluated at the **current** world. Meaning puts \(\Phi\) under a box, so on the right-hand side \(\Phi\) is read again at **successor** worlds. That is the two-world reading — the two stamps.

Lemma L is \(\lfloor P\,G\rfloor\), obtained by feeding Ax1Gen the collection of properties positive at the world of evaluation. Scott’s later A3 postulates that same sentence outright. The packages differ; keep them apart.

---

## The literal axiom forces the desert

The causal summary is the prefecture story without the costumes. The two-world reading lets the roster change between the membership check and the meaning check. Full comprehension lets you name a roster that talks about which world you are in. Feed that roster to the split axiom, and distinct worlds cannot stay linked without a back-edge: the two censuses quarrel with Ax2a, Ax2b, and Ax4. Force the back-edge everywhere, then (with Ax3) force every edge to be a self-loop. The map collapses to discrete points. On that desert Th3 goes through for a dull reason.

**Symmetry** follows from Ax1Gen, Ax2a, Ax2b, and Ax4. Reflexivity and transitivity are **not** hypotheses of that derivation. Ax3 is not used for symmetry. The same four hypotheses are unsatisfiable on every non-symmetric frame — in particular on a two-world S4 chain. That chain is **not** a countermodel to literal Figure 7, because no positivity and existence predicate satisfy the literal axioms there.

**Identity** follows when Ax3 is added: \(R\,w\,v\) if and only if \(w = v\). One route: once symmetry is in hand and the usual necessary-existence chain for a God-like being is in hand, the AFP collapse lemma already forces the identity. What is new relative to that AFP lemma is not a magic “symmetry-free proof” in the sense of never *using* symmetry. It is that **no symmetry hypothesis need be assumed up front**: the axioms produce symmetry, and then produce the identity.

**Modal collapse** follows: every world-proposition \(q\) satisfies \(\lfloor q \supset \Box q \rfloor\). The AFP lemma MC is the same schema *under* an assumed \(R\)-symmetry. Here the symmetry is earned from the packaging.

**Th3, literal**, follows with **no** frame hypothesis. The only S4 models of the literal axioms are discrete. There is no non-discrete S4 model in which the antecedent of Th3 can hold while the consequent fails, because there is no non-discrete model of the axioms at all.

A **one-world control** — identity relation, one individual, principal positivity — satisfies the whole package and Th3. It is a consistency witness. It is not a claim that the axioms are true of anything outside the model. On that one-world frame the literal axiom and the reconstructions below coincide.

An Isabelle2025-2 / AFP 2025-2 probe imports the S4 theory, proves symmetry by the empty-at-home / world-is-\(w\) instantiation, then discharges the AFP `oops` for Th3. Identity and collapse remain Lean-only in the desk development.

### The literal wording and the gloss

The theorems about the literal AFP abbreviation are real. They are theorems about **packaging**, not a revelation.

The footnote says that a conjunction of positive properties is positive. The gloss printed with the proof says that positive means positive in the moral-aesthetic sense, **independently of the accidental structure of the world**. The AFP abbreviation does something else. Its type lets \(\Phi\) vary by world. Membership is judged at the source; Meaning re-reads \(\Phi\) at successors. The collection in the symmetry argument is empty at home and full of contradictions next door. Nothing in the footnote asks a collection to change its mind on the way out of the world.

The split is what a shallow embedding does if Membership is left outside a box while \(\Phi\) still depends on the world. It is the text of `GoedelVariantHOML2`, faithfully transcribed. It is not a misprint, and it is not faithful to the gloss that positive properties do not wait on the accidental structure of the world. Say that carefully: the literal axiom is not a loyal reading of that gloss. Do not say, as if naming a heresy, that “the axiom is not his” — the hand manuscript, the notes shown to Scott, and Scott’s seminar are three objects; the AFP packaging is a fourth layer of ink.

Empty-essence inconsistency on the unrepaired definition already appears in K. That is a different disease from the two-world prank.

---

## Two repairs that read the roster once

Everything in Figure 7 stays put except Ax1Gen. There are two replacements. Both remove the two-world split. In the prefecture: either both stamps are applied under the same box (same towns of evaluation), or the roster is frozen so that walking cannot change it.

**R1 — Same-world positivity.** Put Membership under the box as well, so positivity and conjunction are said of the same accessible worlds. Call the spellings Ax1GenInBox / Ax1GenBox; one countermodel covers both.

**R2 — World-invariant roster.** Keep Membership and Meaning literal, but restrict to collections that do not depend on the world. The prank collection of the desert argument is not rigid, so R2 never sees it.

Under R1, Lemma L is immediate: take \(\Phi\) to be \(P\) itself. Under R2, \(P\) need not be rigid, so take a **snapshot** at the world where the lemma is proved; Ax2a and Ax2b then secure agreement along an edge. **Symmetry is not forced** by either reconstruction. The four-hypothesis derivation of a back-edge has nothing left to instantiate.

### The chain

Let the worlds be two Booleans. The **source** sees both worlds. The **sink** sees only itself. The relation is reflexive and transitive, not symmetric. One individual exists at both. Positivity ignores the world at which it is asked and reads the sink: a property is positive precisely when the individual has it at the sink.

At the sink, God-likeness is a tautology. At the source it fails: “the world is the sink” holds at the sink, hence is positive, and the individual does not have it at the source.

At the source, \(\Diamond(\exists^E G)\) holds and \(\Box(\exists^E G)\) fails. The source sees the sink, where the individual is God-like; it also sees itself, where that individual is not. On this frame, Ax1–Ax4 and both reconstructions hold, and Th3 fails. Literal Ax1Gen has **no** model here — else symmetry would have made the chain symmetric. The reconstructions are strictly weaker. The literal Th3 theorem is not retracted; it is **fenced**.

| Reading of Ax1Gen | Lemma \(P(G)\) | Symmetry forced | Th3 in S4 |
| --- | --- | --- | --- |
| Literal (two-world) | from Ax1Gen alone | yes; then identity | proved, trivially on discrete frames |
| R1, same-world positivity | from R1 alone | no | fails on the chain |
| R2, invariant roster | needs Ax2a, Ax2b | no | fails on the chain |

So “Th3 in S4” under the literal axioms is vacuous in the interesting sense: it holds only where the map has already become a desert. The live question sits with the repairs.

---

## What was already known (and what is not being claimed)

Sobel’s collapse for Scott-style premises is prior art. So is the observation that symmetry suffices for the Scott-side bridge from possible to necessary God-likeness. Anderson’s and Fitting’s emendations are known repairs of a different kind. Ultrafilter simplifications that already yield \(\Box\exists^E G\) in K are different axiom lists again.

Countermodels that *postulate* \(P(G)\) do not answer a question whose point is what happens when \(P(G)\) is *earned* from Ax1Gen. On the chain, the literal axiom has no model at all.

In the AFP S5 theory, lemma MC is prior art for collapse *under* symmetry. In the AFP S4 files, Th3 is the open `oops`. No proof of the identity — or of collapse — for literal Figure 7 **without** a symmetry hypothesis assumed up front, and no countermodel of the two reconstructions, turned up in those sources in the desk search. That is a statement about where the search went. It is not a priority claim about the wider literature, and it is not a brand stamped “undecidable” or “incomplete.” The open `oops` was a gap in a proof file. The desk closed one reading by collapse and the other by an explicit chain.

---

## The same shape outside metaphysics

The likeness to eventually consistent directories is of **shape**, not of theology. No staff directory has proved God, and none has disproved God.

You already live across places that refuse to update together: phone contacts, a company directory, a game avatar, a cloud login — records of who someone is, kept in several spots that do not agree at every instant. Identity there is not a soul. It is a **policy**: where the system looks when it decides what you are.

If the system checks an attribute roster in one place (membership) and interprets that roster under another place’s view without freezing it (meaning), it is doing the two-world reading. Push that habit and designs harden until each node trusts chiefly itself — discrete accessibility sold as global certainty. Treat the identity bundle as one coherent reading — same list, same moment of truth, or a schema that does not change until a proper sync commits — and a “perfect” profile can sit on one shard without being forced onto every shard. Possibility does not smuggle necessity across the map.

That is not a sermon. It is the same drafting question this note isolates for Ax1Gen.

---

## Conclusion

The literal Figure 7 axioms force accessibility to be the identity, and modal collapse follows with **no symmetry hypothesis assumed up front**. The AFP lemma MC is the same schema under symmetry. The mechanism is the two-world reading of Ax1Gen: Membership consults \(\Phi\) at the source; Meaning re-reads \(\Phi\) at successors. Full comprehension turns that split into a force toward discrete frames. Their S4 models are discrete, and Th3 holds there trivially.

Two same-world reconstructions still yield Lemma L and fail on a two-world S4 chain. Among the three readings examined, with full comprehension, the answer turns on whether both halves of Ax1Gen read \(\Phi\) at the same world. Domains and Figure 8 were not varied.

Do not ask whether the symbols have proved God. Ask the drafting question the machine can settle — the question the prefecture learned the hard way:

When the conjunction axiom decides what is positive across many worlds, does it read the roster **once**, or **twice**?

---

## Acknowledgements

The Lean 4 formalization and drafting of the underlying note were done with AI coding assistants. All results reported are kernel-checked in the repository accompanying the formalization. Fiction in this rewrite is illustration only; it does not replace the machine-checked theorems.
