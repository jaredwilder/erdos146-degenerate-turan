import Mathlib

open SimpleGraph Finset

-- PROBE ONLY. Not an artifact. Discovers simp normal forms; every goal ends in `sorry`
-- deliberately, and nothing here is ever cited.

example (r : ℕ) (a : Fin r) : True := by
  have h1 : ((completeBipartiteGraph (Fin r) (Fin r)).neighborSet (Sum.inl a))
      = Set.range Sum.inr := by
    ext w
    simp [completeBipartiteGraph]
    trace_state
    sorry
  trivial

example (r : ℕ) (b : Fin r) : True := by
  have h2 : ((completeBipartiteGraph (Fin r) (Fin r)).neighborSet (Sum.inr b))
      = Set.range Sum.inl := by
    ext w
    simp [completeBipartiteGraph]
    trace_state
    sorry
  trivial

example (r : ℕ) : True := by
  have h3 : (Set.range (Sum.inr : Fin r → Fin r ⊕ Fin r)).ncard = r := by
    rw [← Set.image_univ, Set.ncard_image_of_injective _ Sum.inr_injective]
    simp
    trace_state
    sorry
  trivial

-- does `Set.ncard_le_ncard` + inter_subset_left give the easy upper bound shape?
example (r : ℕ) (S : Set (Fin r ⊕ Fin r)) (a : Fin r) : True := by
  have h4 : ((completeBipartiteGraph (Fin r) (Fin r)).neighborSet (Sum.inl a) ∩ S).ncard
      ≤ ((completeBipartiteGraph (Fin r) (Fin r)).neighborSet (Sum.inl a)).ncard :=
    Set.ncard_le_ncard Set.inter_subset_left (Set.toFinite _)
  trivial

-- univ nonempty as a Set, for the negative direction
example (r : ℕ) (hr : 1 ≤ r) : True := by
  haveI : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have h5 : (Set.univ : Set (Fin r ⊕ Fin r)).Nonempty := Set.univ_nonempty
  trivial
