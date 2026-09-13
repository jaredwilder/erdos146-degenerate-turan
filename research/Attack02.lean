/-
# Erdős #146 — ATTACK 02.  The OTHER axis of the obstruction map: the hypothesis class.

Companion to `Attack01.lean`. `Attack01` §3–§4 showed the CONCLUSION axis of `ConjectureAt r`
moves strictly: `scale s` is never `≪ scale r` for `r < s`, so the cited AKS bound at
`2 - 1/(4r)` cannot yield the conjectured `2 - 1/r`.

This file does the HYPOTHESIS axis. `IsDegenerate r` grows with `r` (spec `IsDegenerate.mono`,
re-proved here so the file stands alone). The question the obstruction map needs answered is
whether it grows STRICTLY, and strictly *inside the bipartite class the conjecture quantifies
over* — because a hierarchy that collapsed on bipartite graphs would make `ConjectureAt 2` a
corollary of `ConjectureAt 1`, and the source's "open even for r=2" would be strange.

It does. `K_{r,r}` is bipartite, is `r`-degenerate, and is NOT `k`-degenerate for any `k < r`.

⛔ NOTHING HERE CLOSES THE TARGET. No `sorry`; the conjecture is not stated as a theorem.

TAKEN TOGETHER WITH Attack01: as `r` increases, `ConjectureAt r` speaks about a STRICTLY LARGER
class of graphs and demands a STRICTLY WEAKER bound. Neither direction of the pair collapses, so
no `ConjectureAt k` implies any other, and `r = 2` is genuinely its own problem.
-/

import Mathlib

open SimpleGraph Finset

namespace Erdos146Attack2

universe u

variable {W : Type u}

/-! ## §0. Copied VERBATIM from the frozen spec `erdos-146.lean`. -/

/-- `IsDegenerate r H`: every induced subgraph of `H` has minimum degree `≤ r`.
Spec convention (3). -/
def IsDegenerate (r : ℕ) (H : SimpleGraph W) : Prop :=
  ∀ S : Set W, S.Nonempty → ∃ v ∈ S, (H.neighborSet v ∩ S).ncard ≤ r

/-- Spec control, copied verbatim: degeneracy is monotone in `r`. -/
theorem IsDegenerate.mono {r s : ℕ} {H : SimpleGraph W} (h : r ≤ s) (hd : IsDegenerate r H) :
    IsDegenerate s H := by
  intro S hS
  obtain ⟨v, hv, hle⟩ := hd S hS
  exact ⟨v, hv, hle.trans h⟩

/-! ## §1. `K_{r,r}` is `r`-regular. NEW. -/

theorem neighborSet_inl {r : ℕ} (a : Fin r) :
    (completeBipartiteGraph (Fin r) (Fin r)).neighborSet (Sum.inl a) = Set.range Sum.inr := by
  ext w
  simp [completeBipartiteGraph]
  cases w <;> simp

theorem neighborSet_inr {r : ℕ} (b : Fin r) :
    (completeBipartiteGraph (Fin r) (Fin r)).neighborSet (Sum.inr b) = Set.range Sum.inl := by
  ext w
  simp [completeBipartiteGraph]
  cases w <;> simp

theorem ncard_range_inr (r : ℕ) : (Set.range (Sum.inr : Fin r → Fin r ⊕ Fin r)).ncard = r := by
  rw [← Set.image_univ, Set.ncard_image_of_injective _ Sum.inr_injective]
  simp

theorem ncard_range_inl (r : ℕ) : (Set.range (Sum.inl : Fin r → Fin r ⊕ Fin r)).ncard = r := by
  rw [← Set.image_univ, Set.ncard_image_of_injective _ Sum.inl_injective]
  simp

/-- **`K_{r,r}` is `r`-regular.** Every vertex, on either side, has exactly `r` neighbours. -/
theorem ncard_neighborSet (r : ℕ) (v : Fin r ⊕ Fin r) :
    ((completeBipartiteGraph (Fin r) (Fin r)).neighborSet v).ncard = r := by
  cases v with
  | inl a => rw [neighborSet_inl a]; exact ncard_range_inr r
  | inr b => rw [neighborSet_inr b]; exact ncard_range_inl r

/-! ## §2. `K_{r,r}` is in the conjecture's hypothesis class, at level `r` and no lower. NEW. -/

/-- `K_{r,r}` is bipartite — so it is a LIVE instance of `ConjectureAt r`, not a graph outside
the quantifier. -/
theorem completeBipartite_isBipartite (r : ℕ) :
    (completeBipartiteGraph (Fin r) (Fin r)).IsBipartite := by
  refine ⟨SimpleGraph.Coloring.mk (fun v => if v.isLeft then (0 : Fin 2) else 1) ?_⟩
  intro v w hadj
  cases v <;> cases w <;> simp_all [completeBipartiteGraph]

/-- `K_{r,r}` is `r`-degenerate: bound the degree inside any `S` by the full degree, which is
`r` by `ncard_neighborSet`. -/
theorem completeBipartite_isDegenerate (r : ℕ) :
    IsDegenerate r (completeBipartiteGraph (Fin r) (Fin r)) := by
  rintro S ⟨v, hv⟩
  refine ⟨v, hv, ?_⟩
  calc ((completeBipartiteGraph (Fin r) (Fin r)).neighborSet v ∩ S).ncard
      ≤ ((completeBipartiteGraph (Fin r) (Fin r)).neighborSet v).ncard :=
        Set.ncard_le_ncard Set.inter_subset_left (Set.toFinite _)
    _ = r := ncard_neighborSet r v

/-- **`K_{r,r}` is NOT `k`-degenerate for any `k < r`.** Test the definition on `S = univ`: no
vertex has fewer than `r` neighbours there, so the witness the definition demands cannot exist.
This is where the `S.Nonempty` guard of spec convention (3) earns its keep — the whole vertex
set is the `S` that refutes. -/
theorem completeBipartite_not_isDegenerate {k r : ℕ} (hkr : k < r) :
    ¬ IsDegenerate k (completeBipartiteGraph (Fin r) (Fin r)) := by
  intro hd
  haveI : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl ⟨0, by omega⟩⟩
  obtain ⟨v, -, hv⟩ := hd Set.univ Set.univ_nonempty
  rw [Set.inter_univ, ncard_neighborSet r v] at hv
  omega

/-! ## §3. ⭐ THE HYPOTHESIS AXIS OF THE OBSTRUCTION MAP. NEW. -/

/-- **⭐ The degeneracy hierarchy is strict, inside the conjecture's own bipartite class.**

For every `k < r`, the concrete graph `K_{r,r}` is bipartite, is `r`-degenerate, and is not
`k`-degenerate. Hence the class of graphs `ConjectureAt r` quantifies over strictly contains the
class `ConjectureAt k` quantifies over, and settling the conjecture at any `k` leaves `K_{r,r}`
— a live, bipartite, `r`-degenerate instance — entirely untouched.

Combined with `Attack01.scale_not_vinogradov` (the conclusion axis), the two axes of
`ConjectureAt` both move strictly and in OPPOSITE directions: more graphs, weaker bound. That is
the structural reason no instance of the conjecture implies another. -/
theorem degeneracy_hierarchy_strict {k r : ℕ} (hkr : k < r) :
    (completeBipartiteGraph (Fin r) (Fin r)).IsBipartite ∧
      IsDegenerate r (completeBipartiteGraph (Fin r) (Fin r)) ∧
      ¬ IsDegenerate k (completeBipartiteGraph (Fin r) (Fin r)) :=
  ⟨completeBipartite_isBipartite r, completeBipartite_isDegenerate r,
    completeBipartite_not_isDegenerate hkr⟩

/-- The chain `IsDegenerate 0 ⊊ IsDegenerate 1 ⊊ IsDegenerate 2 ⊊ ⋯` restated: monotone by
`IsDegenerate.mono`, and never an equality, witnessed on bipartite graphs. -/
theorem degeneracy_chain_strict {k r : ℕ} (hkr : k < r) :
    (∀ (V : Type) (H : SimpleGraph V), IsDegenerate k H → IsDegenerate r H) ∧
      ¬ (∀ (V : Type) (H : SimpleGraph V), IsDegenerate r H → IsDegenerate k H) := by
  refine ⟨fun _ _ hd => hd.mono hkr.le, ?_⟩
  intro h
  exact completeBipartite_not_isDegenerate hkr
    (h (Fin r ⊕ Fin r) _ (completeBipartite_isDegenerate r))

end Erdos146Attack2

-- ⛔ FOOTPRINTS. Clean is [propext, Classical.choice, Quot.sound]. No `sorryAx` may appear.
#print axioms Erdos146Attack2.IsDegenerate.mono
#print axioms Erdos146Attack2.neighborSet_inl
#print axioms Erdos146Attack2.neighborSet_inr
#print axioms Erdos146Attack2.ncard_range_inr
#print axioms Erdos146Attack2.ncard_range_inl
#print axioms Erdos146Attack2.ncard_neighborSet
#print axioms Erdos146Attack2.completeBipartite_isBipartite
#print axioms Erdos146Attack2.completeBipartite_isDegenerate
#print axioms Erdos146Attack2.completeBipartite_not_isDegenerate
#print axioms Erdos146Attack2.degeneracy_hierarchy_strict
#print axioms Erdos146Attack2.degeneracy_chain_strict
