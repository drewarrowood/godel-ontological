# One World or Two:
# Where AFP Figure 7 Reads Φ

**Drew Arrowood**  
September 2026

The canonical note is [`paper/main.tex`](../paper/main.tex), with HTML at [index.html](index.html) and PDF at [main.pdf](main.pdf). This file is not a second HTML build.

---

## Abstract

Benzmüller and Scott leave open whether Theorem Th3 of their actualist Figure 7 — possible existence of a God-like being implies necessary existence, with positivity of God-likeness derived from Ax1Gen, the AFP abbreviation of the footnote’s generalization — is provable in S4. For a Lean 4 transcription of that AFP text, property quantifiers are unrestricted. That is full comprehension. The literal abbreviation derives symmetry: Ax1Gen, Ax2a, Ax2b, and Ax4 yield symmetry of \(R\), and also reflexivity and the B schema \(q \supset \Box\Diamond q\). Adding Ax3 yields Th3. In Lean the same list yields \(R\) equal to the identity, and modal collapse. \(R_{\mathrm{symm}}\) is not an extra hypothesis. On that literal package the only S4 models are discrete frames, including the unit model, and Th3 holds there trivially. The live question sits with the repairs.

Two **reconstructions** — not dictated by Gödel’s footnote — make both halves of Ax1Gen read the collection \(\Phi\) at the **same** world: (R1) positivity judged inside the box, or (R2) a world-invariant collection. Both still yield \(P(G)\). Neither forces symmetry. Both fail on a two-world S4 chain. Among the three readings examined, the answer turns on a single drafting question: does the conjunction axiom consult its roster of positive properties at one world, or at two?

This paper does not settle whether God exists. It settles where a packaged rule looks when it decides what “positive” means.

---

## 1. The open problem, in plain and in symbols

Around 1970 Kurt Gödel wrote a short modal version of the ontological argument [11]. The first axiom says that the conjunction of two positive properties is positive. A footnote extends that claim from two summands to any number: the conjunction of a *collection* of positive properties is itself positive.

Three objects have to be kept apart, as Benzmüller and Scott set them out [8]. The first is Gödel’s own 1970 hand manuscript (their Figure 1; Kurt Gödel Papers, Box 12, Folder 41, item accession 060565, printed there under the copyright of the Institute for Advanced Study). The second is the brief notes Gödel showed Scott. The third is the slightly modified seminar version printed as Appendix B of Sobel [14, 16]. In spring 1970 Gödel asked Scott confidentially to preserve some notes in case of illness or death; Scott later mentioned a slightly modified version in a seminar without permission, and he records his embarrassment [8]. The hand definition of essence omits the conjunct φ x. Benzmüller and Scott show that the empty-essence inconsistency is already derivable in modal logic K, and that Scott’s addition of φ x restores consistency. The AFP entry of 7 January 2025 and the Lean desk use that repaired essence, not the hand page. Scott’s seminar notes also replace the footnote’s generalized conjunction by a direct postulate that being God-like is positive.

Sobel later showed that Scott’s premises collapse modality: whatever is true is necessarily true [15, 16]. That collapse has been machine-checked, and so have Anderson- and Fitting-style repairs [1, 10, 5]. Separately, the step from “possibly God-like” to “necessarily God-like” on the Scott side needs **symmetry** of accessibility (the Brouwerian axiom B), and does not need the rest of S5 [12]. Those facts are recorded again in Section 6 so they are not mistaken for the theorems below.

The question of this note comes from a return to the footnote. Benzmüller and Scott [7, 8] study Gödel’s generalized conjunction as an axiom they call **Ax1Gen**. Positivity of being God-like is not assumed; it is **Lemma L**, derived from Ax1Gen. The essence there is Scott’s repaired clause. Individual quantifiers are **actualist**: an existence predicate says who is present at a world. In their Figure 7, Theorem **Th3** is

\[
\lfloor \Diamond(\exists^E x.\, Gx) \supset \Box(\exists^E y.\, Gy) \rfloor.
\]

In the S5 embedding, the proof of Th3 uses symmetry of accessibility, the schema B, and nothing else from S5, so KB already suffices [8]. The published theory `GoedelVariantHOML2inS4` leaves Th3 as `oops`. That goal is the literal Ax1Gen of the file. Session `Ax1Gen_EmptyAtHome_Check`, on Isabelle2025-2 and AFP 2025-2, proves symmetry from the empty-at-home instantiation and then that goal, with no extra `Rsymm` axiom. Identity and collapse are Lean theorems, not lemmas of that session. Under the same-world reconstructions, Th3 still fails on a two-world chain. Figure 8 still leaves Th3 as `oops`; that goal is not the probe. Binary Ax1 does not yield their possibility theorem Th4; Ax1Gen does, via Lemma L, Ax2a, and Ax4. A 2026 comment supplies an infinite non-principal ultrafilter countermodel for binary Ax1, and locates collapse primarily in the rigidity of positivity (Scott’s A4, Gödel’s Ax2b) rather than in the ultrafilter alone [4]. Neither fact is the identity theorem below. The published S4 file still writes that `oops`. The probe is what discharges the Figure 7 goal.

**What this note shows.** For a Lean 4 transcription of that AFP text, with full comprehension:

1. The **literal** reading of Ax1Gen proves Th3 — but by forcing accessibility to be the identity. The only S4 models are discrete; Th3 holds there trivially.
2. Two **same-world reconstructions** of Ax1Gen still yield Lemma L, do not force symmetry, and **refute** Th3 on a two-world S4 chain.

Among the three readings, with domains and Figure 8 held fixed, the answer turns on whether both halves of Ax1Gen read \(\Phi\) at the same world.

---

## 2. Setup, with names that say what they do

Worlds form a type \(W\), individuals a type \(\mathrm{Ind}\), and accessibility a relation \(R\) on \(W\). A world-proposition is a map \(W \to \mathrm{Prop}\). A **property** is a map \(\mathrm{Ind} \to W \to \mathrm{Prop}\) (individual first, world second), matching the AFP type \(e \Rightarrow i \Rightarrow \mathrm{bool}\). **Positivity** \(P\) is a world-relative predicate on properties.

Necessity and possibility are the usual quantifications along \(R\):

\[
(\Box\varphi)\,w \equiv \forall v.\, R\,w\,v \to \varphi\,v,
\qquad
(\Diamond\varphi)\,w \equiv \exists v.\, R\,w\,v \land \varphi\,v.
\]

**Validity** \(\lfloor\varphi\rfloor\) means \(\varphi\) holds at every world.

An existence predicate \(\mathrm{ex} : \mathrm{Ind} \to W \to \mathrm{Prop}\) plays the role of AFP `existsAt`. The outer type of individuals is fixed; who exists may vary. **Actualist** quantifiers restrict to existents:

\[
(\forall^E y.\,\varphi y)\,w \equiv \forall y.\, \mathrm{ex}\,y\,w \to \varphi y\,w,
\qquad
(\exists^E y.\,\varphi y)\,w \equiv \exists y.\, \mathrm{ex}\,y\,w \land \varphi y\,w.
\]

Quantifiers over properties stay **possibilist**: they range over every map \(\mathrm{Ind} \to W \to \mathrm{Prop}\). That is **full comprehension** — the freedom to name fancy collections, including collections that talk about which world one occupies. That freedom is load-bearing below.

### 2.1 God-likeness and the other Figure 7 clauses

Writing \(\varphi\cdot\psi\) for pointwise conjunction and \(\sim\varphi\) for pointwise negation:

\begin{align*}
G x &\equiv \forall\varphi.\, P\varphi \supset \varphi x, \\
\varphi \supset_N \psi &\equiv \Box(\forall^E y.\, \varphi y \supset \psi y), \\
\varphi\ \mathrm{Ess.}\ x &\equiv \varphi x \land (\forall\psi.\, \psi x \supset (\varphi \supset_N \psi)), \\
E x &\equiv \forall\varphi.\, (\varphi\ \mathrm{Ess.}\ x) \supset \Box(\exists^E z.\, \varphi z).
\end{align*}

**God-likeness** \(G\): having every positive property.  
**Necessary inclusion** \(\supset_N\): inclusion that holds at every accessible world (for existents).  
**Essence**: a property the individual has that necessarily includes every property it has.  
**Necessary existence** \(E\): every essence of the individual is necessarily exemplified.

### 2.2 The standing axioms (all under validity)

| Name | Informal content |
| --- | --- |
| **Ax1** | Binary conjunction of positives is positive |
| **Ax2a** | Exactly one of \(P\varphi\) and \(P(\sim\varphi)\) |
| **Ax2b** | \(P\varphi \supset \Box P\varphi\) (positivity persists along \(R\)) |
| **Ax3** | Necessary existence is positive: \(P\,E\) |
| **Ax4** | Positivity passes along necessary inclusion |

Ax1 is part of the package and holds in the one-world model of Section 4. Th3 does not use it; neither does the AFP proof of Th3.

### 2.3 The conjunction axiom: membership half and meaning half

The footnote becomes two abbreviations and one axiom. Rename them for what they do:

\[
\begin{align*}
\mathrm{Membership}(\Phi)
&\equiv \forall\varphi.\, \Phi\varphi \supset P\varphi
&&\text{(“everything on the roster is positive”)} \\[0.4em]
\mathrm{Meaning}(\varphi,\Phi)
&\equiv \Box\bigl(\forall^E z.\, \varphi z \leftrightarrow (\forall\psi.\, \Phi\psi \supset \psi z)\bigr)
&&\text{(“\(\varphi\) is the conjunction of the roster”)} \\[0.4em]
\mathrm{Ax1Gen}
&\equiv \bigl\lfloor \bigl(\mathrm{Membership}(\Phi) \land \mathrm{Meaning}(\varphi,\Phi)\bigr) \supset P\varphi \bigr\rfloor.
\end{align*}
\]

Both \(\Phi\) and \(\varphi\) are universally quantified. This is the text of `GoedelVariantHOML2` and of `GoedelVariantHOML2inS4`.

**The split.** \(\mathrm{Membership}(\Phi)\) is evaluated at the **current** world — the world where the axiom is applied. \(\mathrm{Meaning}(\varphi,\Phi)\) puts \(\Phi\) under a box, so on the right-hand side \(\Phi\) is read again at **successor** worlds. Same axiom; two lookouts. Call this the **two-world reading** of Ax1Gen.

**Lemma L** is \(\lfloor P\,G\rfloor\), obtained by feeding Ax1Gen the collection of properties that are positive at the world of evaluation. It is a lemma, not an axiom. Scott’s later A3 postulates that same sentence outright. The two packages are different; Section 6 keeps them apart.

In the S5 theory, Th3 is proved from Th2 by three steps: existence of a God-like being implies necessary existence; the diamond of the antecedent is therefore a diamond of a box; symmetry turns that diamond-box back into a box. Reflexivity is not used in that argument.

---

## 3. What the encoding is (and is not)

The development is a shallow embedding in Lean 4, with no Mathlib. Hypotheses are propositions passed as arguments; there is no Lean `axiom` declaration in the repository. The host logic is the ordinary Lean kernel. Where a proof uses classical reasoning, `#print axioms` says so (Section 7). Isabelle/HOL is classical, so that use matches the AFP host; it is still a different host.

World-relative \(P\), actualist individual quantifiers, possibilist quantifiers over properties, Figure 7 essence with the conjunct \(\varphi x\), and the derivation of \(P(G)\) are the AFP reading. They are not extra deviations.

One consequence of Lean’s `Prop` is worth saying before the proofs. A proof of a negation may be a classical contradiction rather than a construction of a counter-witness. The symmetry argument is of that kind. The chain countermodel of Section 5 is not: failure of Th3 at the source is an explicit world, an explicit individual, and a computation.

---

## 4. The literal axiom forces the identity

### 4.1 The trick, before the symbols

Ax1Gen invites you to define a property by saying which collection it conjoins. The abbreviation does **not** require the collection to be the same at every world. Membership is judged at the source. Meaning re-reads the roster under the box.

At the current world \(w\), let \(\Phi\) mark **nothing**. Membership is then vacuously true, and the axiom will still conclude that the defined property \(\varphi\) is positive at \(w\). At a successor \(u \neq w\), let \(\Phi\) mark the empty property \(\bot\), and define \(\varphi\) to be “this world is \(w\)” (the source). The boxed biconditional holds in both places:

- at home, an empty collection conjoins to a tautology on the world-coordinate;
- next door, a collection that contains a contradiction conjoins to a contradiction, and “this is home” is false next door.

Positivity, once granted at home, is pushed along the edge by Ax2b. At the far end, “this world is home” *necessarily includes* its own negation, because the far world cannot see home — that is the missing back-edge we are trying to forbid — so the inclusion is vacuous. Ax4 passes positivity to the negation. Ax2a refuses to let a property and its negation both be positive.

**Causal summary.** The two-world reading lets the roster change between the membership check and the meaning check. Full comprehension lets you name a roster that *talks about* which world you are in. Feed that roster to the split axiom, and distinct worlds cannot stay linked without a back-edge: the two censuses quarrel with Ax2a, Ax2b, and Ax4. Force the back-edge everywhere, then (with Ax3) force every edge to be a self-loop. The map of possible situations collapses to discrete points. On that desert, “possible” and “necessary” nearly coincide — and Th3 goes through for a dull reason.

### 4.2 From home-positivity to the identity

**Lemma 1** (*home positivity*). From Ax1Gen alone: if \(\varphi\) holds of every individual that exists at \(w\), then \(P\varphi\) at \(w\) whenever \(w\) sees itself — and, more strongly, Ax1Gen alone already yields a form of “whatever holds of all existents here is positive here” once reflexivity is in play. (The formal development isolates the home-collection \(\Phi\,\psi\,u :\equiv (u \neq w \land \psi = \varphi)\); at \(w\) that collection marks nothing useful for Membership, while Meaning pins \(\varphi\) as the conjunction of what was marked.)

**Theorem 2** (*reflexivity*). From Ax1Gen and Ax2a, \(R\) is reflexive.

**Theorem 3** (*B schema*). From Ax1Gen, Ax2a, Ax2b, and Ax4, every world-proposition \(q\) satisfies \(\lfloor q \supset \Box\Diamond q \rfloor\).

**Theorem 4** (*symmetry*). From Ax1Gen, Ax2a, Ax2b, and Ax4, \(R\) is symmetric. Reflexivity and transitivity are **not** hypotheses.

*Sketch of Theorem 4.* Fix \(R\,w\,v\) and suppose \(\neg R\,v\,w\). Define

\[
\varphi :\equiv \lambda \_\, u.\, (u = w),
\qquad
\Phi :\equiv \lambda\psi\, u.\, \bigl(u \neq w \land \forall x.\, \neg\psi\,x\,u\bigr).
\]

At \(w\), the clause \(u \neq w\) fails, so \(\Phi\) marks no property and Membership holds outright. The boxed Meaning holds at every successor of \(w\) (empty roster at home; \(\bot\) next door, with both sides of the biconditional failing together). Ax1Gen yields \(P\varphi\) at \(w\). Ax2b pushes it to \(v\). At \(v\), necessary inclusion of \(\varphi\) in \(\sim\varphi\) is vacuous (a successor of \(v\) cannot be \(w\)). Ax4 yields \(P(\sim\varphi)\) at \(v\). Ax2a says \(P\varphi\) and \(P(\sim\varphi)\) are exclusive. Contradiction. Hence \(R\,v\,w\).

Ax3 is not used for symmetry. The same four hypotheses are therefore unsatisfiable on every non-symmetric frame — in particular on the two-world S4 chain of Figure 2 (`fig7_unsat_on_S4_chain`). That chain is **not** a countermodel to literal Figure 7, because no positivity and existence predicate satisfy the literal axioms there.

**Theorem 5** (*identity*). From Ax1Gen, Ax2a, Ax2b, Ax3, and Ax4,
\[
R\,w\,v \iff w = v.
\]

*Sketch.* Reflexivity (Theorem 2) gives the right-to-left direction. For the other direction: with Ax3 one obtains necessary existence of a God-like being (the AFP Th5 route, via Lemma L and the usual essence/NE chain). Applied to the world-proposition “the world is \(w\)”, collapse confines every accessible world to \(w\). Equivalently: once symmetry is in hand (Theorem 4) and Th5 is in hand, the AFP collapse lemma MC already forces the identity. The axioms derive that symmetry, and then the identity.

**Theorem 6** (*modal collapse*). From the same five axioms, every world-proposition \(q\) satisfies \(\lfloor q \supset \Box q \rfloor\).

*Sketch.* If \(q\) holds at \(w\) and \(R\,w\,v\), Theorem 5 forces \(v = w\), so \(q\) holds at \(v\).

This is the schema of the AFP lemma MC. The AFP proof assumes \(R\)-symmetry. Theorem 6 does not. What the literal S4 problem was missing is that symmetry does not have to be hypothesized: the axioms produce it, and they produce the identity relation.

**Theorem 7** (*Th3, literal*). From Ax1Gen, Ax2a, Ax2b, Ax3, and Ax4,
\[
\lfloor \Diamond(\exists^E x.\, Gx) \supset \Box(\exists^E y.\, Gy) \rfloor,
\]
with **no** frame hypothesis.

The literal axioms force \(R\) to be the identity. Their S4 models are discrete, and Th3 holds there **trivially**: a diamond and a box along the identity are the same quantifier. There is no non-discrete S4 model in which the antecedent can hold while the consequent fails, because there is no non-discrete model of the axioms at all.

**Proposition 8** (*one-world control*). On a single world, with the identity relation, one individual existing there, and principal positivity \(P\varphi :\equiv \varphi()()\), axioms Ax1, Ax2a, Ax2b, Ax3, Ax4, and Ax1Gen hold, and Th3 holds.

This is the shape Nitpick reported at cardinality one, checked directly. It is a consistency witness for the literal package. It is not a claim that the axioms are true of anything outside the model. On that one-world frame the literal axiom and the two reconstructions of Section 5 coincide.

### 4.3 Figure 8 (held fixed)

Figure 8 changes necessary inclusion (adds a non-bottom side condition) and drops the \(\varphi x\) conjunct from essence. Figure 8 was **not** varied as part of the comparison in Section 5. For completeness: with *literal* Ax1Gen, Th3 still holds for the Figure 8 package (symmetry as in Theorem 4, with an inhabitant taken from the diamond); and possible existence of a God-like being (Th4) follows from literal Ax1Gen and Ax2a once reflexivity is in hand — the proof the AFP S4 file left as `oops` and then re-axiomatized.

### 4.4 The literal axiom is not the footnote

Theorem 7 is a theorem of the literal AFP abbreviation Ax1Gen. The 1970 hand manuscript states binary Ax1 and a footnote. It does not state that abbreviation.

The footnote says that a conjunction of positive properties is positive [11, 4]. The gloss printed with the proof says that positive means positive in the moral-aesthetic sense, **independently of the accidental structure of the world** [11]. The AFP abbreviation does something else. Its type lets \(\Phi\) vary by world. Membership is judged at the source; Meaning re-reads \(\Phi\) at successors. The collection in the symmetry argument is empty at home and full of contradictions next door. The footnote does not mention worlds. The hand page is not the AFP text.

The split is what a shallow embedding does if Membership is left outside a box while \(\Phi\) still depends on the world. It is the text of `GoedelVariantHOML2`, faithfully transcribed. It is not a misprint, and it is not a reading of the footnote. The theorems about the literal wording are real. They are theorems about **packaging**, not a revelation.

---

## 5. Two same-world reconstructions

Everything in Figure 7 stays put except Ax1Gen. There are two replacements. They are not rivals for a single idea; both remove the two-world split.

### R1 — Same-world positivity (positivity in the box)

Both halves are judged at the same accessible worlds:

\[
\lfloor \Box\,\mathrm{Membership}(\Phi) \land \forall^E z.\, \varphi z \leftrightarrow (\forall\psi.\, \Phi\psi \supset \psi z) \supset P\varphi \rfloor.
\]

Call this **Ax1GenInBox**. In K, a box of a conjunction is a conjunction of boxes, and Meaning is already a box, so this is equivalent to

\[
\lfloor \bigl(\Box(\mathrm{Membership}(\Phi)) \land \mathrm{Meaning}(\varphi,\Phi)\bigr) \supset P\varphi \rfloor
\]

(**Ax1GenBox**). One countermodel covers both spellings. This is the reading on which “positive” and “conjunction” are said of the **same** world.

### R2 — World-invariant roster

Restrict Ax1Gen to collections that do not depend on the world: \(\Phi\,\psi\,w \leftrightarrow \Phi\,\psi\,v\) for every property and every pair of worlds. Membership and Meaning stay literal. Call this **Ax1GenRigid**. R2 moves no box; it freezes \(\Phi\). The empty-at-home collection of Section 4 is not world-invariant, so R2 never sees it.

### 5.1 Lemma L still derives

Under R1, Lemma L is immediate from the repaired axiom alone. Take \(\Phi\) to be \(P\) itself. At every world, every property that \(\Phi\) marks is positive there, by identity, so the extra box is free. The conjunction of whatever is positive at a world is \(G\) at that world, by definition of \(G\).

Under R2 the same \(\Phi\) may be refused, because \(P\) itself need not be rigid. Take a **snapshot** at the world \(w\) where the lemma is being proved: \(\Phi\,\psi\,\_ :\equiv P\,\psi\,w\). That collection ignores its world argument, so it is rigid. At a successor \(v\), the conjunction it defines is \(G\) only if positivity at \(w\) and positivity at \(v\) agree. Ax2a and Ax2b give exactly that agreement along an edge: a positive property stays positive by Ax2b, and a property positive at \(v\) cannot have a positive negation at \(w\), or Ax2b would carry the negation forward and break Ax2a at \(v\). So Lemma L under R2 needs Ax2a and Ax2b; literal Lemma L needed neither.

**Symmetry is not forced** by either reconstruction. The collection used for Theorem 4 is empty at the source (so source Membership holds) but marks \(\bot\) at a successor. R1’s boxed Membership demands \(P(\bot)\) there. R2 does not apply, because the collection varies. The four-hypothesis derivation of a back-edge has nothing left to instantiate.

### 5.2 The chain (Figure 2)

Let the worlds be the two Booleans. The **source** \(s = \mathsf{false}\) sees both worlds. The **sink** \(t = \mathsf{true}\) sees only itself. The relation is reflexive and transitive. It is not symmetric. One individual exists at both worlds. Positivity ignores the world at which it is asked and reads the sink:

\[
P\varphi \equiv \varphi()\,\mathsf{true}.
\]

A property is positive precisely when the individual has it at \(t\).

At the sink, God-likeness is a tautology: \(G\) says every positive property holds there, and positivity means the property holds there. At the source it fails: the property “the world is the sink” holds at the sink, hence is positive, and the individual does not have it at the source.

**Theorem 11** (*Th3 fails at the source*). At the source, \(\Diamond(\exists^E G)\) holds and \(\Box(\exists^E G)\) fails.

*Sketch.* The source sees the sink, where the individual exists and is God-like. The source also sees itself, where that same individual exists and is not God-like. The diamond is the first fact; the failure of the box is the second. No kernel axiom is used.

**Theorem 12** (*same-world countermodels*). On this frame: \(R\) is an S4 frame and not symmetric; Ax1, Ax2a, Ax2b, Ax3, Ax4, and both spellings of R1 hold, and Th3 fails. The same frame, positivity, and existence predicate satisfy R2, and Th3 fails.

| Reading of Ax1Gen | Lemma \(P(G)\) | Symmetry forced | Th3 in S4 |
| --- | --- | --- | --- |
| Literal (two-world) | from Ax1Gen alone | yes (Thm. 4); identity (Thm. 5) | proved, trivially on discrete frames (Thm. 7) |
| R1, same-world positivity | from R1 alone | no | fails (Thm. 12) |
| R2, invariant roster | needs Ax2a, Ax2b | no | fails (Thm. 12) |

**Table 1.** The S4 question, by scope. The witness for both negative cells is the chain of Figure 2.

Literal Ax1Gen has **no** model on this frame (else Theorem 4 would make the chain symmetric). The reconstructions are strictly weaker than the literal axiom here. Theorem 7 is not retracted; it is **fenced**. A model of R1 or of R2 need not be a model of the abbreviation that proved Th3.

---

## 6. What was already known (and what is not being claimed)

Sobel showed that Scott-style premises yield \(\varphi \supset \Box\varphi\) [15, 16]. Benzmüller and Fuenmayor checked that Scott’s intensional positivity collapses modality, while Anderson’s emendation and Fitting’s extensional positivity do not [5, 1, 10]. The repository’s collapse modules rediscover the Scott-side collapse. That is a rediscovery; it is not Theorem 6 or Theorem 12.

Kanckos and Woltzenlogel Paleo showed that Scott’s argument goes through in KB: symmetry suffices [12]. Benzmüller and Scott make the same point for their Th3 [7, 8]. Countermodels that *postulate* \(P(G)\) do not answer a question whose point is what happens when \(P(G)\) is *earned* from Ax1Gen. On the chain of Figure 2, the literal axiom has no model at all.

Anderson’s and Fitting’s emendations are known repairs of a different kind. Ultrafilter simplifications that already yield \(\Box\exists^E G\) in K are different axiom lists again [4, 3]. They do not use the AFP scoping of Ax1Gen.

What was checked, for the claim that the identity proof and the two reconstructions were not found already in the AFP S4 theories named above, is recorded in the repository notes. In the AFP S5 theory, lemma MC is prior art for collapse *under* symmetry. In the AFP S4 files, Th3 is the open `oops`. No proof that the literal Figure 7 axioms derive symmetry, and with Ax3 the identity and collapse, and no countermodel of the two reconstructions, turned up in those sources. That is a statement about where the search went. It is not a priority claim about the wider literature.

---

## 7. Remark: the same shape outside metaphysics

The likeness to eventually consistent directories is of **shape**, not of theology. No staff directory has proved God, and none has disproved God.

You already live across places that refuse to update together: phone contacts, a company directory, a game avatar, a cloud login — records of who someone is, kept in several spots that do not agree at every instant. Identity there is not a soul. It is a **policy**: where the system looks when it decides what you are.

If the system checks an attribute roster in one place (membership) and interprets that roster under another place’s view without freezing it (meaning), it is doing the two-world reading. Push that habit and designs harden until each node trusts chiefly itself — discrete accessibility sold as global certainty. Treat the identity bundle as one coherent reading — same list, same moment of truth, or a schema that does not change until a proper sync commits — and a “perfect” profile can sit on one shard without being forced onto every shard. Possibility does not smuggle necessity across the map.

That is not a sermon. It is the same drafting question this note isolates for Ax1Gen: when a rule decides what something *is* across many worlds, does it read the list once, or twice?

---

## 8. What the kernel accepts

The development builds with `lake build` on Lean 4.34.0, with no Mathlib. A search of the Lean sources finds no `sorry`, no `native_decide`, and no `axiom` command (strings that look like those words sit in comments). Hypotheses of the ontological argument are parameters of type `Prop`.

`#print axioms` on the headline theorems reports either no kernel axioms, or the standard classical package `propext`, `Classical.choice`, `Quot.sound`. No custom axiom appears. Classical choice enters through contradiction arguments in reflexivity, the B schema, symmetry, the identity, and collapse; excluded middle enters Ax2a on the chain. The failure of Th3 at the source, taken by itself, depends on none of them.

---

## 9. Conclusion

The literal Figure 7 axioms force accessibility to be the identity (Theorem 5), and modal collapse follows (Theorem 6), from the symmetry that Ax1Gen, Ax2a, Ax2b, and Ax4 have already derived. \(R_{\mathrm{symm}}\) is not an extra hypothesis. The AFP lemma MC is the same schema from an assumed symmetry. The mechanism is the two-world reading of Ax1Gen: Membership consults \(\Phi\) at the source; Meaning re-reads \(\Phi\) at successors. Full comprehension, unrestricted quantification over properties, turns that split into a force toward discrete frames. Their S4 models are discrete, including the unit model, and Th3 holds there trivially (Theorem 7). The live question sits with the repairs.

Two same-world reconstructions still yield Lemma L and fail on a two-world S4 chain (Theorem 12). Among the three readings examined, with full comprehension, the answer turns on whether both halves of Ax1Gen read \(\Phi\) at the same world. Domains and Figure 8 were not varied.

Do not ask whether the symbols have proved God. Ask the drafting question the machine can settle: when the conjunction axiom decides what is positive across many worlds, does it read the roster once, or twice?

---

## Acknowledgements

The Lean 4 formalization and drafting of the underlying note were done with AI coding assistants. All results reported are kernel-checked in the repository accompanying the formalization.

---

## References

[1] C. Anthony Anderson. Some emendations of Gödel’s ontological proof. *Faith and Philosophy*, 7(3):291–303, 1990.

[2] C. Anthony Anderson and Michael Gettings. Gödel’s ontological proof revisited. In Hájek (ed.), *Gödel ’96*, LNL 6, 167–172. ASL / CUP, 1996/2017.

[3] Christoph Benzmüller. Exploring simplified variants of Gödel’s ontological argument in Isabelle/HOL. *Archive of Formal Proofs*, November 2021.

[4] Christoph Benzmüller. A comment on modal collapse and ultrafilters in Gödel’s ontological argument, 2026. arXiv:2608.07578.

[5] Christoph Benzmüller and David Fuenmayor. Computer-supported analysis of positive properties, ultrafilters and modal collapse in variants of Gödel’s ontological argument. *Bulletin of the Section of Logic*, 49(2), 2020.

[6] Christoph Benzmüller and Bruno Woltzenlogel Paleo. Automating Gödel’s ontological proof of God’s existence with higher-order automated theorem provers. In *ECAI 2014*, 93–98. IOS Press, 2014.

[7] Christoph Benzmüller and Dana Scott. Notes on Gödel’s and Scott’s variants of the ontological argument. *Archive of Formal Proofs*, 7 January 2025.

[8] Christoph Benzmüller and Dana Scott. Notes on Gödel’s and Scott’s variants of the ontological argument. *Monatshefte für Mathematik*, 208(4):569–611, 2025. Published online 21 April 2025. https://doi.org/10.1007/s00605-025-02078-x.

[9] Leonardo de Moura and Sebastian Ullrich. The Lean 4 theorem prover and programming language. In *CADE 28*, LNCS 12699, 625–635. Springer, 2021.

[10] Melvin Fitting. *Types, Tableaus, and Gödel’s God*. Kluwer, 2002.

[11] Kurt Gödel. Ontological proof. In *Collected Works*, Vol. III, 403–404. Oxford University Press, 1995.

[12] Annika Kanckos and Bruno Woltzenlogel Paleo. Variants of Gödel’s ontological proof in a natural deduction calculus. *Studia Logica*, 105(3):553–586, 2017.

[13] Tobias Nipkow, Lawrence C. Paulson, and Markus Wenzel (eds.). *Isabelle/HOL*. LNCS 2283. Springer, 2002.

[14] Dana Scott. Appendix B: Notes in Dana Scott’s hand. In Sobel, *Logic and Theism*, 145–146. Cambridge University Press, 2004.

[15] Jordan Howard Sobel. Gödel’s ontological proof. In Thomson (ed.), *On Being and Saying*, 241–261. MIT Press, 1987.

[16] Jordan Howard Sobel. *Logic and Theism*. Cambridge University Press, 2004.
