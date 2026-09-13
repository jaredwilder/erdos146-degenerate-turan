/-
# Erdős #146 — ATTACK 03.  MIN-DEGREE SUBGRAPH EXTRACTION.

Frozen spec: `oracle/evidence/formalizer-sources/erdos/erdos-146.lean`.
Named targets: `ConjectureAt`, `Conjecture`, `Conjecture_r_two`.
Predecessors: `Attack01.lean` (26 sealed lemmas), `Attack02.lean` (11 sealed lemmas).

⛔ NOTHING HERE CLOSES THE TARGET. No `sorry`. The conjecture is still a `def ... : Prop` and is
not asserted anywhere in this file.

## What this file is

`Attack01`'s TERMINAL named exactly two missing lemmas on the road to `ConjectureAt 1`:

  (a) MIN-DEGREE EXTRACTION — a graph with more than `k·n` edges has a nonempty vertex set on
      which every vertex has more than `k` neighbours;
  (b) GREEDY EMBEDDING — place an `r`-degenerate `H` into a graph of large minimum degree, along
      the degeneracy order produced by `Attack01.exists_degeneracyList`.

(b) is a multi-hundred-line development. **This file is (a), and only (a).** It is the cheaper
half, and — unlike (b) — it is reusable verbatim across every degenerate-Turán target, because
it mentions neither bipartiteness nor `H`.

## The statement, and why it is stated this way

The extraction is proved by DELETION: while some vertex of `S` has at most `k` neighbours inside
`S`, delete it. Each deletion removes one vertex and at most `k` edges, so the invariant
`e(S) > k·|S|` survives; and `e(∅) > k·0` is false, so the process cannot empty the set. What
it stops at is a nonempty set of minimum degree `> k`.

Three shapes of the conclusion are proved, deliberately:

  * `exists_minDegree_aux` / `exists_minDegree_subset` — `Finset`-relative, the workhorse. This
    is the form a greedy embedding consumes: it hands back a CONCRETE `T ⊆ S` together with the
    degree guarantee for every one of its vertices.
  * `exists_minDegree_of_card_edgeFinset` — the classical global statement, in Mathlib's own
    edge-count vocabulary (`G.edgeFinset.card`), bridged by Mathlib's handshake lemma.
  * `exists_subgraph_minDegree` — the same witness packaged as an honest `SimpleGraph.Subgraph`
    (`(⊤ : G.Subgraph).induce ↑T`), for a consumer that wants a subgraph object rather than a
    vertex set.

The degree guarantee itself is always stated as `k < (G.neighborSet v ∩ ↑T).ncard`, which is
VERBATIM the shape the frozen spec's `IsDegenerate` uses. That is not decoration: it makes the
conclusion of the extraction the exact negation of the spec's degeneracy witness, so the two
compose with no glue at all. `IsDegenerate.card_edgeFinset_le` below is that composition.

## What it buys, immediately

`IsDegenerate r H → H.edgeFinset.card ≤ r * Fintype.card V`. Every `r`-degenerate graph is
sparse — at most `r·n` edges — machine-checked, from the spec's own definition of `IsDegenerate`
and nothing else. This is the standard sparsity fact for degenerate graphs, and it is the first
statement in this campaign that turns the degeneracy HYPOTHESIS into a quantitative bound rather
than a structural one. Together with `Attack01.exists_degeneracyList` it is the whole non-embedding
half of the `r = 1` argument.

## What is still missing

The greedy embedding, (b) above. Untouched here, as intended: it needs a `SimpleGraph.Copy`
built by induction along a list, which is not a budget-8 job and does not belong in the same
file as the extraction.
-/

import Mathlib

open Finset SimpleGraph

namespace Erdos146Attack3

universe u

variable {V : Type u}

/-! ## §0. Copied VERBATIM from the frozen spec `erdos-146.lean`. Do not edit. -/

/-- `IsDegenerate r H`: every induced subgraph of `H` has minimum degree `≤ r`.
Spec convention (3). -/
def IsDegenerate (r : ℕ) (H : SimpleGraph V) : Prop :=
  ∀ S : Set V, S.Nonempty → ∃ v ∈ S, (H.neighborSet v ∩ S).ncard ≤ r

/-! ## §1. Degree inside a finite vertex set, and the bridge to the spec's shape. NEW. -/

/-- `degIn G S v` : the number of neighbours of `v` lying inside the finite set `S`. The
`Finset` counterpart of the spec's `(G.neighborSet v ∩ S).ncard`. -/
def degIn (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (v : V) : ℕ :=
  (S.filter (G.Adj v)).card

/-- **The bridge.** `degIn` is the spec's own quantity. Every theorem below can therefore be
read in either vocabulary, and the extraction's conclusion is literally the negation of the
witness `IsDegenerate` demands. -/
theorem ncard_neighborSet_inter (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (v : V) :
    (G.neighborSet v ∩ (↑S : Set V)).ncard = degIn G S v := by
  have h : G.neighborSet v ∩ (↑S : Set V) = ↑(S.filter (G.Adj v)) := by
    ext w
    simp [and_comm]
  show (G.neighborSet v ∩ (↑S : Set V)).ncard = (S.filter (G.Adj v)).card
  rw [h, Set.ncard_coe_finset]

/-- On the whole vertex type, `degIn` is Mathlib's `degree`. This is what lets the handshake
lemma `SimpleGraph.sum_degrees_eq_twice_card_edges` be used unchanged. -/
theorem degIn_univ [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    degIn G Finset.univ v = G.degree v := by
  have h : Finset.univ.filter (G.Adj v) = G.neighborFinset v := by
    ext w
    simp [SimpleGraph.mem_neighborFinset]
  calc degIn G Finset.univ v = (Finset.univ.filter (G.Adj v)).card := rfl
    _ = (G.neighborFinset v).card := by rw [h]
    _ = G.degree v := rfl

/-! ## §2. Two pieces of bookkeeping, isolated so the induction below stays readable. NEW. -/

/-- Deleting one member of `S` from a filtered count removes exactly the indicator of that
member. Stated additively: no `ℕ`-subtraction anywhere in this file. -/
theorem card_filter_erase [DecidableEq V] (p : V → Prop) [DecidablePred p] {S : Finset V} {v : V}
    (hv : v ∈ S) :
    (S.filter p).card = (if p v then 1 else 0) + ((S.erase v).filter p).card := by
  simp only [Finset.card_filter]
  exact (Finset.add_sum_erase S (fun a => if p a then 1 else 0) hv).symm

/-- The arithmetic of one deletion step, with the nonlinear product `2 * k * |S|` abstracted to
an opaque `X` so that `omega` sees a purely linear problem. -/
theorem nat_descent {X A d k : ℕ} (h1 : X + 2 * k < A + 2 * d) (h2 : d ≤ k) : X < A := by omega

/-- Multiplying a strict inequality by the literal `2`. Kept as its own lemma for the same
reason as `nat_descent`: it keeps every arithmetic step linear. -/
theorem two_mul_lt {a b : ℕ} (h : a < b) : 2 * a < 2 * b := by omega

/-! ## §3. ⭐ THE DELETION IDENTITY. NEW.

Deleting `v` from `S` removes exactly `2 * degIn G S v` from the degree sum: once for the
neighbours of `v`, which each lose `v`, and once for `v` itself, which leaves the sum. This is
the handshake lemma, localised to `S`, and it is the entire content of the induction step. -/

theorem sum_degIn_erase [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {S : Finset V}
    {v : V} (hv : v ∈ S) :
    (∑ w ∈ S.erase v, degIn G (S.erase v) w) + 2 * degIn G S v = ∑ w ∈ S, degIn G S w := by
  have h1 : ∀ w : V, degIn G S w = (if G.Adj w v then 1 else 0) + degIn G (S.erase v) w :=
    fun w => card_filter_erase (G.Adj w) hv
  have h2 : ∑ w ∈ S.erase v, degIn G S w
      = (∑ w ∈ S.erase v, (if G.Adj w v then 1 else 0))
        + ∑ w ∈ S.erase v, degIn G (S.erase v) w := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun w _ => h1 w)
  have hfilter : (S.erase v).filter (fun w => G.Adj w v) = S.filter (G.Adj v) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨-, huS⟩, hadj⟩
      exact ⟨huS, hadj.symm⟩
    · rintro ⟨huS, hadj⟩
      exact ⟨⟨(G.ne_of_adj hadj).symm, huS⟩, hadj.symm⟩
  have h3 : (∑ w ∈ S.erase v, (if G.Adj w v then 1 else 0)) = degIn G S v := by
    show (∑ w ∈ S.erase v, (if G.Adj w v then 1 else 0)) = (S.filter (G.Adj v)).card
    rw [← hfilter, Finset.card_filter]
  have h4 : degIn G S v + ∑ w ∈ S.erase v, degIn G S w = ∑ w ∈ S, degIn G S w :=
    Finset.add_sum_erase S (fun w => degIn G S w) hv
  omega

/-! ## §4. ⭐ THE EXTRACTION. NEW. This is the target of this file. -/

/-- **The workhorse, by strong induction on `|S|`.**

If the degree sum inside `S` exceeds `2k|S|` — equivalently, if `S` spans more than `k|S|` edges
— then `S` has a NONEMPTY subset `T` on which every vertex has more than `k` neighbours inside
`T`.

The induction is the classical deletion argument: if some `v ∈ S` already has `degIn ≤ k`,
delete it. By `sum_degIn_erase` the degree sum drops by exactly `2 * degIn G S v ≤ 2k` while
`|S|` drops by exactly one, so the hypothesis `2k|S| < ∑ degIn` is restored on `S.erase v`
(`nat_descent`). Otherwise `S` itself is the answer, and it is nonempty because `2k·0 < 0` is
false. -/
theorem exists_minDegree_aux [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ) :
    ∀ (m : ℕ) (S : Finset V), S.card = m → 2 * k * S.card < ∑ v ∈ S, degIn G S v →
      ∃ T ⊆ S, T.Nonempty ∧ (∀ v ∈ T, k < degIn G T v) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro S hSm hbig
    have hSne : S.Nonempty := by
      rcases S.eq_empty_or_nonempty with rfl | hS
      · simp at hbig
      · exact hS
    by_cases hmin : ∀ v ∈ S, k < degIn G S v
    · exact ⟨S, Finset.Subset.refl S, hSne, hmin⟩
    · obtain ⟨v, hvS, hdv⟩ : ∃ v ∈ S, degIn G S v ≤ k := by
        by_contra hcon
        refine hmin fun v hv => ?_
        by_contra hlt
        exact hcon ⟨v, hv, by omega⟩
      have hcard : (S.erase v).card + 1 = S.card := Finset.card_erase_add_one hvS
      have hsplit := sum_degIn_erase G hvS
      have hexp : 2 * k * (S.erase v).card + 2 * k = 2 * k * S.card := by
        rw [← hcard]; ring
      have hstep : 2 * k * (S.erase v).card < ∑ w ∈ S.erase v, degIn G (S.erase v) w := by
        refine nat_descent (d := degIn G S v) ?_ hdv
        rw [hexp, hsplit]
        exact hbig
      obtain ⟨T, hTsub, hTne, hTmin⟩ :=
        ih (S.erase v).card (by rw [← hSm]; exact Finset.card_erase_lt_of_mem hvS)
          (S.erase v) rfl hstep
      exact ⟨T, hTsub.trans (Finset.erase_subset v S), hTne, hTmin⟩

/-- **⭐ THE EXTRACTION, RELATIVE FORM, IN THE SPEC'S VOCABULARY.**

`2k|S| < ∑_{v ∈ S} deg_S(v)` gives a nonempty `T ⊆ S` with `(G.neighborSet v ∩ ↑T).ncard > k`
for every `v ∈ T`. That conclusion is exactly the failure of the witness `IsDegenerate k`
demands at the set `↑T`, so this composes with the frozen spec with no glue. It is also the
form a greedy embedding consumes: a concrete vertex set, and a degree floor on it. -/
theorem exists_minDegree_subset [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    {S : Finset V} (hbig : 2 * k * S.card < ∑ v ∈ S, degIn G S v) :
    ∃ T ⊆ S, T.Nonempty ∧ ∀ v ∈ T, k < (G.neighborSet v ∩ (↑T : Set V)).ncard := by
  obtain ⟨T, hTS, hTne, hTmin⟩ := exists_minDegree_aux G k S.card S rfl hbig
  refine ⟨T, hTS, hTne, fun v hv => ?_⟩
  rw [ncard_neighborSet_inter]
  exact hTmin v hv

/-- **⭐ THE CLASSICAL STATEMENT.** *Every finite graph with more than `k·n` edges contains a
(nonempty, induced) subgraph of minimum degree `> k`.*

Stated in Mathlib's own edge vocabulary: the hypothesis is on `G.edgeFinset.card`, and the
translation to the degree sum is Mathlib's handshake lemma
`SimpleGraph.sum_degrees_eq_twice_card_edges`, not a re-derivation. -/
theorem exists_minDegree_of_card_edgeFinset [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {k : ℕ} (h : k * Fintype.card V < G.edgeFinset.card) :
    ∃ T : Finset V, T.Nonempty ∧ ∀ v ∈ T, k < (G.neighborSet v ∩ (↑T : Set V)).ncard := by
  have hdeg : ∀ v : V, degIn G Finset.univ v = G.degree v := degIn_univ G
  have hsum : ∑ v ∈ (Finset.univ : Finset V), degIn G Finset.univ v = 2 * G.edgeFinset.card := by
    simp only [hdeg]
    exact G.sum_degrees_eq_twice_card_edges
  have hbig : 2 * k * (Finset.univ : Finset V).card
      < ∑ v ∈ (Finset.univ : Finset V), degIn G Finset.univ v := by
    rw [hsum, Finset.card_univ]
    calc 2 * k * Fintype.card V = 2 * (k * Fintype.card V) := by ring
      _ < 2 * G.edgeFinset.card := two_mul_lt h
  obtain ⟨T, -, hTne, hTmin⟩ := exists_minDegree_subset G hbig
  exact ⟨T, hTne, hTmin⟩

/-! ## §5. ⭐ WHAT THE EXTRACTION BUYS AGAINST THE SPEC'S HYPOTHESIS. NEW. -/

/-- **⭐ `r`-DEGENERATE GRAPHS ARE SPARSE: `e(H) ≤ r·n`.**

Proved by contraposition against the extraction: more than `r·n` edges would produce a nonempty
`T` all of whose vertices have more than `r` neighbours inside `↑T`, and `IsDegenerate r`
applied to the set `↑T` demands a vertex with at most `r`. The two cannot both hold.

This is the first quantitative consequence in this campaign of the spec's `IsDegenerate`. Every
earlier result about the hypothesis (`Attack02.degeneracy_hierarchy_strict` and friends) was
structural; this one is a bound, and it is the non-embedding half of the `r = 1` argument. -/
theorem IsDegenerate.card_edgeFinset_le [Fintype V] [DecidableEq V] {r : ℕ} {H : SimpleGraph V}
    [DecidableRel H.Adj] (hd : IsDegenerate r H) :
    H.edgeFinset.card ≤ r * Fintype.card V := by
  by_contra hcon
  obtain ⟨T, hTne, hTmin⟩ := exists_minDegree_of_card_edgeFinset H (Nat.not_le.mp hcon)
  obtain ⟨v, hvT, hvle⟩ := hd (↑T : Set V) (Finset.coe_nonempty.mpr hTne)
  have h1 := hTmin v (Finset.mem_coe.mp hvT)
  omega

/-- The same bound on every vertex subset at once: an `r`-degenerate graph spans at most `r|S|`
edges inside any `S`, stated as `∑_{v ∈ S} deg_S(v) ≤ 2r|S|`. The relative form is what an
induction over a degeneracy order needs; the global form above is the special case `S = univ`. -/
theorem IsDegenerate.sum_degIn_le [DecidableEq V] {r : ℕ} {H : SimpleGraph V}
    [DecidableRel H.Adj] (hd : IsDegenerate r H) (S : Finset V) :
    ∑ v ∈ S, degIn H S v ≤ 2 * r * S.card := by
  by_contra hcon
  obtain ⟨T, -, hTne, hTmin⟩ := exists_minDegree_subset H (Nat.not_le.mp hcon)
  obtain ⟨v, hvT, hvle⟩ := hd (↑T : Set V) (Finset.coe_nonempty.mpr hTne)
  have h1 := hTmin v (Finset.mem_coe.mp hvT)
  omega

/-- The contrapositive, stated in the direction an attack actually uses: an edge count above
`r·n` REFUTES `r`-degeneracy. -/
theorem not_isDegenerate_of_card_edgeFinset [Fintype V] [DecidableEq V] {r : ℕ}
    {H : SimpleGraph V} [DecidableRel H.Adj] (h : r * Fintype.card V < H.edgeFinset.card) :
    ¬ IsDegenerate r H := by
  intro hd
  have := hd.card_edgeFinset_le
  omega

/-! ## §6. The witness as an honest `SimpleGraph.Subgraph`. NEW.

§4 hands back a vertex set. A consumer that wants a subgraph OBJECT — one that can be fed to a
lemma about `SimpleGraph.Subgraph` — gets it here, with the degree floor transported. -/

/-- Inside the induced subgraph `(⊤ : G.Subgraph).induce T`, the neighbourhood of a vertex of
`T` is precisely `G.neighborSet v ∩ T`. -/
theorem neighborSet_induce_top (G : SimpleGraph V) {T : Set V} {v : V} (hv : v ∈ T) :
    ((⊤ : G.Subgraph).induce T).neighborSet v = G.neighborSet v ∩ T := by
  ext w
  simp only [Subgraph.mem_neighborSet, Subgraph.induce_adj, Subgraph.top_adj, Set.mem_inter_iff,
    SimpleGraph.mem_neighborSet]
  exact ⟨fun h => ⟨h.2.2, h.2.1⟩, fun h => ⟨hv, h.2, h.1⟩⟩

/-- **⭐ THE EXTRACTION, AS A SUBGRAPH.** More than `k·n` edges yields a nonempty `T` whose
induced subgraph `(⊤ : G.Subgraph).induce ↑T` has vertex set `↑T` and minimum degree `> k`. -/
theorem exists_subgraph_minDegree [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {k : ℕ} (h : k * Fintype.card V < G.edgeFinset.card) :
    ∃ T : Finset V, T.Nonempty ∧
      ((⊤ : G.Subgraph).induce (↑T : Set V)).verts = (↑T : Set V) ∧
      ∀ v ∈ T, k < (((⊤ : G.Subgraph).induce (↑T : Set V)).neighborSet v).ncard := by
  obtain ⟨T, hTne, hTmin⟩ := exists_minDegree_of_card_edgeFinset G h
  refine ⟨T, hTne, rfl, fun v hv => ?_⟩
  rw [neighborSet_induce_top G (Finset.mem_coe.mpr hv)]
  exact hTmin v hv

end Erdos146Attack3

-- ⛔ FOOTPRINTS. Clean is [propext, Classical.choice, Quot.sound]. No `sorryAx` may appear.
#print axioms Erdos146Attack3.ncard_neighborSet_inter
#print axioms Erdos146Attack3.degIn_univ
#print axioms Erdos146Attack3.card_filter_erase
#print axioms Erdos146Attack3.nat_descent
#print axioms Erdos146Attack3.two_mul_lt
#print axioms Erdos146Attack3.sum_degIn_erase
#print axioms Erdos146Attack3.exists_minDegree_aux
#print axioms Erdos146Attack3.exists_minDegree_subset
#print axioms Erdos146Attack3.exists_minDegree_of_card_edgeFinset
#print axioms Erdos146Attack3.IsDegenerate.card_edgeFinset_le
#print axioms Erdos146Attack3.IsDegenerate.sum_degIn_le
#print axioms Erdos146Attack3.not_isDegenerate_of_card_edgeFinset
#print axioms Erdos146Attack3.neighborSet_induce_top
#print axioms Erdos146Attack3.exists_subgraph_minDegree
