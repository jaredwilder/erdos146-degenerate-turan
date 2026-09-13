/-
# Erdős #146 — ATTACK 01.  Erdős–Simonovits degenerate Turán conjecture ($500, OPEN).

Frozen spec: `oracle/evidence/formalizer-sources/erdos/erdos-146.lean`.
Named targets: `ConjectureAt`, `Conjecture`, `Conjecture_r_two`.

⛔ NOTHING HERE CLOSES THE TARGET. This file contains no `sorry`; every declaration below is
either a definition copied VERBATIM from the frozen spec (§0) or a NEW theorem proved outright.
The conjecture is untouched: it is still a `def ... : Prop`.

WHAT THIS FILE ADDS, in three registers:

  (A) THE EXPONENT AXIS, TOTALLY ORDERED AND STRICTLY SEPARATED (§2–§3).
      `scale r n = n^(2-1/r)` is monotone in `r` under `≪`, and the monotonicity is STRICT:
      `¬ VinogradovLE (scale s) (scale r)` for `r < s`. This is the machine-checked form of the
      spec's prose claim that "the gap between the two exponents IS the open problem".

  (B) A TYPED OBSTRUCTION MAP (§4–§5). The cited AKS bound `n^{2-1/(4r)}` does NOT imply the
      conjectured `n^{2-1/r}`: there is an explicit `f` satisfying the first and refuting the
      second. Hence no argument that consumes `alon_krivelevich_sudakov` as a BLACK BOX can
      prove `ConjectureAt r`. Same for the free trivial bound `ex(n;H) ≤ n²`, which is proved
      here unconditionally and then shown to be strictly insufficient.

  (C) STRUCTURE OF THE HYPOTHESIS (§6–§8). `IsDegenerate 0` is exactly the edgeless graph;
      degeneracy is inherited by subgraphs; `ex` is monotone under `⊑`; and — the one piece of
      genuine machinery toward `r = 1` — every finite `r`-degenerate graph admits a DEGENERACY
      ORDER (`exists_degeneracyList`), the list in which each vertex has at most `r` neighbours
      among those still to come. That list is the input a greedy embedding argument consumes.

WHAT IS STILL MISSING (the honest gap; see TERMINAL.json):
  the min-degree subgraph extraction lemma, and the greedy embedding of an `r`-degenerate `H`
  into a graph of large minimum degree. Those two together would give `ConjectureAt 1`; neither
  is proved here.
-/

import Mathlib

open Filter SimpleGraph Finset

namespace Erdos146Attack

universe u v

variable {W : Type u}

/-! ## §0. Copied VERBATIM from the frozen spec. Do not edit; the spec is the authority. -/

/-- `VinogradovLE f g` is the source's `f \ll g`. Spec convention (5). -/
def VinogradovLE (f g : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, f n ≤ C * g n

/-- The right-hand scale `n^{2 - 1/r}`. Spec convention (7). -/
noncomputable def scale (r : ℕ) (n : ℕ) : ℝ := (n : ℝ) ^ (2 - 1 / (r : ℝ))

/-- `ex n H` is the Turán number. Spec convention (1)–(2). -/
noncomputable def ex (n : ℕ) (H : SimpleGraph W) : ℕ := SimpleGraph.extremalNumber n H

/-- `ex` as a real-valued function of `n`. -/
noncomputable def exR (H : SimpleGraph W) (n : ℕ) : ℝ := (ex n H : ℝ)

/-- `IsDegenerate r H`: every induced subgraph of `H` has minimum degree `≤ r`.
Spec convention (3). -/
def IsDegenerate (r : ℕ) (H : SimpleGraph W) : Prop :=
  ∀ S : Set W, S.Nonempty → ∃ v ∈ S, (H.neighborSet v ∩ S).ncard ≤ r

/-- ⛔ THE CONJECTURE AT A FIXED `r`. A `Prop`, not a theorem. -/
def ConjectureAt (r : ℕ) : Prop :=
  1 ≤ r → ∀ (W : Type u) [Fintype W] (H : SimpleGraph W),
    H.IsBipartite → IsDegenerate r H → VinogradovLE (exR H) (scale r)

/-- ⛔ THE CONJECTURE. A `Prop`, not a theorem. -/
def Conjecture : Prop := ∀ r : ℕ, ConjectureAt.{u} r

/-- ⛔ The `r = 2` instance, itself open. A `Prop`, not a theorem. -/
def Conjecture_r_two : Prop := ConjectureAt.{u} 2

/-- Spec control, copied verbatim (proved there, re-proved here so this file stands alone). -/
theorem ex_le_choose_two (n : ℕ) (H : SimpleGraph W) : ex n H ≤ n.choose 2 := by
  have h : SimpleGraph.extremalNumber (Fintype.card (Fin n)) H ≤ n.choose 2 := by
    rw [SimpleGraph.extremalNumber_le_iff]
    intro G _ _
    simpa using G.card_edgeFinset_le_card_choose_two
  simpa [ex] using h

/-! ## §1. `≪` is a preorder. NEW. -/

theorem VinogradovLE.refl (f : ℕ → ℝ) : VinogradovLE f f :=
  ⟨1, one_pos, by filter_upwards with n; simp⟩

theorem VinogradovLE.trans {f g h : ℕ → ℝ} (hfg : VinogradovLE f g) (hgh : VinogradovLE g h) :
    VinogradovLE f h := by
  obtain ⟨C₁, hC₁, h₁⟩ := hfg
  obtain ⟨C₂, hC₂, h₂⟩ := hgh
  refine ⟨C₁ * C₂, mul_pos hC₁ hC₂, ?_⟩
  filter_upwards [h₁, h₂] with n hn₁ hn₂
  calc f n ≤ C₁ * g n := hn₁
    _ ≤ C₁ * (C₂ * h n) := mul_le_mul_of_nonneg_left hn₂ hC₁.le
    _ = C₁ * C₂ * h n := by ring

/-! ## §2. The scale family is monotone in `r`. NEW. -/

theorem scale_eq (r : ℕ) : scale r = fun n : ℕ => (n : ℝ) ^ (2 - 1 / (r : ℝ)) := rfl

/-- Pointwise: a larger degeneracy index is a larger scale, on every `n ≥ 1`. -/
theorem scale_le_scale {r s : ℕ} (hr : 1 ≤ r) (hrs : r ≤ s) {n : ℕ} (hn : 1 ≤ n) :
    scale r n ≤ scale s n := by
  have hrN : 0 < r := by omega
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hrN
  have hrs' : (r : ℝ) ≤ (s : ℝ) := by exact_mod_cast hrs
  have hx : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1 : (1 : ℝ) / (s : ℝ) ≤ 1 / (r : ℝ) := one_div_le_one_div_of_le hr0 hrs'
  exact Real.rpow_le_rpow_of_exponent_le hx (by linarith)

/-- Consequently the conjectured conclusion WEAKENS as `r` grows. -/
theorem vinogradovLE_scale_mono {f : ℕ → ℝ} {r s : ℕ} (hr : 1 ≤ r) (hrs : r ≤ s)
    (h : VinogradovLE f (scale r)) : VinogradovLE f (scale s) := by
  obtain ⟨C, hC, hev⟩ := h
  refine ⟨C, hC, ?_⟩
  filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
  exact hn.trans (mul_le_mul_of_nonneg_left (scale_le_scale hr hrs hn1) hC.le)

/-! ## §3. ⭐ THE SEPARATION. The monotonicity of §2 is STRICT. NEW — this is the crux. -/

/-- **The engine.** A strictly larger real power is never `≪` a smaller one. -/
theorem rpow_not_vinogradov {a b : ℝ} (hab : b < a) :
    ¬ VinogradovLE (fun n : ℕ => (n : ℝ) ^ a) (fun n : ℕ => (n : ℝ) ^ b) := by
  rintro ⟨C, hC, hev⟩
  have hd : 0 < a - b := sub_pos.mpr hab
  have htend : Tendsto (fun n : ℕ => (n : ℝ) ^ (a - b)) atTop atTop :=
    (_root_.tendsto_rpow_atTop hd).comp tendsto_natCast_atTop_atTop
  have hfalse : ∀ᶠ n : ℕ in atTop, False := by
    filter_upwards [eventually_ge_atTop 1, htend.eventually_gt_atTop C, hev] with n hn1 hnC hnle
    have hx1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hxpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one hx1
    have hsum : a - b + b = a := by ring
    have hsplit : (n : ℝ) ^ a = (n : ℝ) ^ (a - b) * (n : ℝ) ^ b := by
      rw [← Real.rpow_add hxpos, hsum]
    have hbpos : (0 : ℝ) < (n : ℝ) ^ b := Real.rpow_pos_of_pos hxpos b
    have hnle' : (n : ℝ) ^ a ≤ C * (n : ℝ) ^ b := hnle
    rw [hsplit] at hnle'
    have h2 : (n : ℝ) ^ (a - b) ≤ C := le_of_mul_le_mul_right hnle' hbpos
    linarith
  obtain ⟨n, hn⟩ := hfalse.exists
  exact hn

/-- **The scales are strictly separated.** For `1 ≤ r < s`, `scale s` is NOT `≪ scale r`. -/
theorem scale_not_vinogradov {r s : ℕ} (hr : 1 ≤ r) (hrs : r < s) :
    ¬ VinogradovLE (scale s) (scale r) := by
  have hrN : 0 < r := by omega
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hrN
  have hrs' : (r : ℝ) < (s : ℝ) := by exact_mod_cast hrs
  have h1 : (1 : ℝ) / (s : ℝ) < 1 / (r : ℝ) := one_div_lt_one_div_of_lt hr0 hrs'
  rw [scale_eq s, scale_eq r]
  exact rpow_not_vinogradov (by linarith)

/-- The free quadratic bound is NOT `≪ n^{2-1/r}` for any `r ≥ 1`. -/
theorem trivial_bound_not_vinogradov {r : ℕ} (hr : 1 ≤ r) :
    ¬ VinogradovLE (fun n : ℕ => (n : ℝ) ^ (2 : ℝ)) (scale r) := by
  have hrN : 0 < r := by omega
  have hr0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hrN
  have h1 : (0 : ℝ) < 1 / (r : ℝ) := by positivity
  rw [scale_eq r]
  exact rpow_not_vinogradov (by linarith)

/-! ## §4. ⭐ THE TYPED OBSTRUCTION MAP. NEW. -/

/-- **No weaker scale suffices.** For `1 ≤ r < s` there is a function obeying the `s`-bound and
refuting the `r`-bound. So an upper bound at exponent `2 - 1/s` carries NO information about the
conjectured exponent `2 - 1/r`. -/
theorem no_weaker_scale_suffices {r s : ℕ} (hr : 1 ≤ r) (hrs : r < s) :
    ∃ f : ℕ → ℝ, VinogradovLE f (scale s) ∧ ¬ VinogradovLE f (scale r) :=
  ⟨scale s, VinogradovLE.refl _, scale_not_vinogradov hr hrs⟩

/-- **⭐ The AKS bound is insufficient, machine-checked.** The cited theorem
`alon_krivelevich_sudakov` concludes `VinogradovLE (exR H) (scale (4*r))`. There is an explicit
`f` satisfying exactly that conclusion and violating `VinogradovLE f (scale r)`. Hence NO
derivation that uses the AKS conclusion as a black box can prove `ConjectureAt r`: the gap
between `2 - 1/(4r)` and `2 - 1/r` is not bridgeable by any argument about the bound alone. -/
theorem aks_bound_insufficient {r : ℕ} (hr : 1 ≤ r) :
    ∃ f : ℕ → ℝ, VinogradovLE f (scale (4 * r)) ∧ ¬ VinogradovLE f (scale r) :=
  no_weaker_scale_suffices hr (by omega)

/-- The conclusion of `ConjectureAt` genuinely strengthens as `r` decreases: implications run
one way only. -/
theorem conjectureAt_conclusion_strictly_decreasing {r s : ℕ} (hr : 1 ≤ r) (hrs : r < s) :
    (∀ f : ℕ → ℝ, VinogradovLE f (scale r) → VinogradovLE f (scale s)) ∧
      ¬ (∀ f : ℕ → ℝ, VinogradovLE f (scale s) → VinogradovLE f (scale r)) := by
  refine ⟨fun f hf => vinogradovLE_scale_mono hr hrs.le hf, ?_⟩
  intro h
  exact scale_not_vinogradov hr hrs (h (scale s) (VinogradovLE.refl _))

/-! ## §5. The free baseline, and the exact distance from it to the target. NEW. -/

theorem exR_le_sq (H : SimpleGraph W) (n : ℕ) : exR H n ≤ (n : ℝ) ^ (2 : ℝ) := by
  have h1 : ex n H ≤ n ^ 2 := by
    refine le_trans (ex_le_choose_two n H) ?_
    rw [Nat.choose_two_right]
    calc n * (n - 1) / 2 ≤ n * (n - 1) := Nat.div_le_self _ _
      _ ≤ n * n := Nat.mul_le_mul le_rfl (Nat.sub_le _ _)
      _ = n ^ 2 := (pow_two n).symm
  have h3 : ((n : ℝ)) ^ (2 : ℝ) = ((n : ℝ)) ^ (2 : ℕ) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  show ((ex n H : ℕ) : ℝ) ≤ (n : ℝ) ^ (2 : ℝ)
  rw [h3]
  exact_mod_cast h1

/-- **Unconditional, for every `H` whatsoever.** The trivial bound needs no hypothesis at all. -/
theorem exR_vinogradov_sq (H : SimpleGraph W) :
    VinogradovLE (exR H) (fun n : ℕ => (n : ℝ) ^ (2 : ℝ)) :=
  ⟨1, one_pos, by filter_upwards with n; simpa using exR_le_sq H n⟩

/-- **The distance to the target, typed.** Left: the trivial bound holds for free, for every
graph, with no bipartiteness and no degeneracy hypothesis. Right: it is strictly weaker than the
conjectured scale. So the entire content of `ConjectureAt r` lies in the strict gap. -/
theorem distance_to_target {r : ℕ} (hr : 1 ≤ r) :
    (∀ (V : Type u) (H : SimpleGraph V), VinogradovLE (exR H) (fun n : ℕ => (n : ℝ) ^ (2 : ℝ))) ∧
      ¬ VinogradovLE (fun n : ℕ => (n : ℝ) ^ (2 : ℝ)) (scale r) :=
  ⟨fun _ H => exR_vinogradov_sq H, trivial_bound_not_vinogradov hr⟩

/-! ## §6. The degeneracy hypothesis: extreme cases and the junk instance. NEW. -/

/-- On a nonempty finite vertex type, `r`-degeneracy gives a vertex of degree `≤ r` outright. -/
theorem exists_lowDegree_vertex [Fintype W] [Nonempty W] {r : ℕ} {H : SimpleGraph W}
    (hd : IsDegenerate r H) : ∃ v : W, (H.neighborSet v).ncard ≤ r := by
  obtain ⟨v, -, hv⟩ := hd Set.univ Set.univ_nonempty
  exact ⟨v, by simpa using hv⟩

/-- **`0`-degenerate is exactly edgeless.** One end of the hierarchy pinned down. -/
theorem isDegenerate_zero_iff [Fintype W] {H : SimpleGraph W} :
    IsDegenerate 0 H ↔ H = ⊥ := by
  constructor
  · intro h
    ext u v
    simp only [SimpleGraph.bot_adj, iff_false]
    intro huv
    obtain ⟨w, hw, hcard⟩ := h {u, v} ⟨u, Set.mem_insert _ _⟩
    have hpos : 0 < (H.neighborSet w ∩ ({u, v} : Set W)).ncard := by
      rw [Set.ncard_pos (Set.toFinite _)]
      rcases Set.mem_insert_iff.mp hw with rfl | hw'
      · exact ⟨v, by simpa using huv, by simp⟩
      · rw [Set.mem_singleton_iff] at hw'
        subst hw'
        exact ⟨u, by simpa using huv.symm, by simp⟩
    omega
  · rintro rfl S ⟨v, hv⟩
    refine ⟨v, hv, ?_⟩
    have hn : ((⊥ : SimpleGraph W).neighborSet v ∩ S) = ∅ := by
      ext x; simp [SimpleGraph.neighborSet]
    simp [hn]

/-- **The junk instance carries no content, machine-checked.** `ConjectureAt 0` is TRUE, and
trivially so: the `1 ≤ r` guard of spec convention (6) is what makes it vacuous. Anyone reading
`Conjecture = ∀ r, ConjectureAt r` must know that the `r = 0` conjunct is free. -/
theorem conjectureAt_zero : ConjectureAt.{u} 0 := by
  intro h
  exact absurd h (by omega)

/-! ## §7. Degeneracy and containment: the hypothesis is monotone downwards. NEW. -/

/-- **Degeneracy passes to subgraphs.** If `H' ⊑ H` (an injective homomorphism, spec convention
(1)) and `H` is `r`-degenerate, so is `H'`. -/
theorem IsDegenerate.of_isContained {W' : Type v} [Fintype W] {r : ℕ}
    {H : SimpleGraph W} {H' : SimpleGraph W'} (hsub : H' ⊑ H) (hd : IsDegenerate r H) :
    IsDegenerate r H' := by
  obtain ⟨f⟩ := hsub
  intro S' hS'
  obtain ⟨x, hx⟩ := hS'
  obtain ⟨v, hv, hcard⟩ := hd ((fun w => f.toHom w) '' S') ⟨f.toHom x, x, hx, rfl⟩
  obtain ⟨u, huS', rfl⟩ := hv
  refine ⟨u, huS', ?_⟩
  refine le_trans (Set.ncard_le_ncard_of_injOn (fun w => f.toHom w) ?_ ?_ (Set.toFinite _)) hcard
  · rintro w ⟨hw1, hw2⟩
    exact ⟨f.toHom.map_rel hw1, w, hw2, rfl⟩
  · intro a _ b _ hab
    exact f.injective hab

/-- Degeneracy is an isomorphism invariant, as it must be. -/
theorem IsDegenerate.congr_iso {W' : Type v} [Fintype W] {r : ℕ}
    {H : SimpleGraph W} {H' : SimpleGraph W'} (e : H ≃g H') (hd : IsDegenerate r H) :
    IsDegenerate r H' :=
  IsDegenerate.of_isContained ⟨e.symm.toCopy⟩ hd

/-- `ex` is monotone under containment of the forbidden graph. -/
theorem ex_mono_of_isContained {W' : Type v} {n : ℕ} {H : SimpleGraph W} {H' : SimpleGraph W'}
    (h : H' ⊑ H) : ex n H' ≤ ex n H :=
  SimpleGraph.IsContained.extremalNumber_le h

/-- **A usable reduction.** Proving the conjectured bound for `H` gives it for every subgraph of
`H` for free — and by `IsDegenerate.of_isContained` the hypothesis is inherited too. So
`ConjectureAt r` may be attacked on edge-maximal `H` only. -/
theorem vinogradov_of_isContained {W' : Type v} {r : ℕ} {H : SimpleGraph W} {H' : SimpleGraph W'}
    (hsub : H' ⊑ H) (hH : VinogradovLE (exR H) (scale r)) : VinogradovLE (exR H') (scale r) := by
  obtain ⟨C, hC, hev⟩ := hH
  refine ⟨C, hC, ?_⟩
  filter_upwards [hev] with n hn
  have hmono : ex n H' ≤ ex n H := ex_mono_of_isContained hsub
  have h2 : exR H' n ≤ exR H n := by
    show ((ex n H' : ℕ) : ℝ) ≤ ((ex n H : ℕ) : ℝ)
    exact_mod_cast hmono
  linarith

/-! ## §8. ⭐ THE DEGENERACY ORDER. NEW. The one piece of real machinery toward `r = 1`. -/

/-- `L` is a degeneracy list at level `r`: at every suffix `v :: T` of `L`, the head `v` has at
most `r` neighbours among the vertices `T` still to come. Read backwards, `L` is an order in
which each newly-added vertex attaches to at most `r` already-placed vertices — exactly the
input a greedy embedding argument consumes. -/
def IsDegeneracyList (r : ℕ) (H : SimpleGraph W) (L : List W) : Prop :=
  ∀ (v : W) (T : List W), (v :: T) <:+ L → (H.neighborSet v ∩ {w | w ∈ T}).ncard ≤ r

/-- Relative form, over an arbitrary finite vertex set. Strong induction on the cardinality:
peel off the low-degree vertex the degeneracy hypothesis hands you, recurse on the rest. -/
theorem exists_degeneracyList_aux [DecidableEq W] {r : ℕ} {H : SimpleGraph W}
    (hd : IsDegenerate r H) : ∀ (m : ℕ) (S : Finset W), S.card = m →
      ∃ L : List W, L.Nodup ∧ (∀ v : W, v ∈ L ↔ v ∈ S) ∧ IsDegeneracyList r H L := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro S hSm
    rcases S.eq_empty_or_nonempty with rfl | hS
    · refine ⟨[], List.nodup_nil, by simp, ?_⟩
      intro v T hsuf
      simp at hsuf
    · obtain ⟨v, hvS, hv⟩ := hd (↑S : Set W) (Finset.coe_nonempty.mpr hS)
      have hvS' : v ∈ S := Finset.mem_coe.mp hvS
      obtain ⟨L, hLnd, hLmem, hLdeg⟩ :=
        ih (S.erase v).card (by rw [← hSm]; exact Finset.card_erase_lt_of_mem hvS')
          (S.erase v) rfl
      have hvL : v ∉ L := fun hmem => (Finset.notMem_erase v S) ((hLmem v).mp hmem)
      have hsub : {w : W | w ∈ L} ⊆ (↑S : Set W) := by
        intro w hw
        exact Finset.mem_coe.mpr (Finset.mem_of_mem_erase ((hLmem w).mp hw))
      have hfin : (H.neighborSet v ∩ (↑S : Set W)).Finite :=
        S.finite_toSet.subset Set.inter_subset_right
      have hcard : (H.neighborSet v ∩ {w : W | w ∈ L}).ncard ≤ r :=
        le_trans (Set.ncard_le_ncard (Set.inter_subset_inter (subset_refl _) hsub) hfin) hv
      refine ⟨v :: L, List.nodup_cons.mpr ⟨hvL, hLnd⟩, ?_, ?_⟩
      · intro w
        constructor
        · intro hw
          rcases List.mem_cons.mp hw with rfl | hw'
          · exact hvS'
          · exact Finset.mem_of_mem_erase ((hLmem w).mp hw')
        · intro hw
          by_cases hwv : w = v
          · exact List.mem_cons.mpr (Or.inl hwv)
          · exact List.mem_cons.mpr (Or.inr ((hLmem w).mpr (Finset.mem_erase.mpr ⟨hwv, hw⟩)))
      · intro w T hsuf
        rcases List.suffix_cons_iff.mp hsuf with heq | hsuf'
        · simp only [List.cons.injEq] at heq
          obtain ⟨rfl, rfl⟩ := heq
          exact hcard
        · exact hLdeg w T hsuf'

/-- **⭐ Every finite `r`-degenerate graph admits a degeneracy order.** -/
theorem exists_degeneracyList [Fintype W] [DecidableEq W] {r : ℕ} {H : SimpleGraph W}
    (hd : IsDegenerate r H) :
    ∃ L : List W, L.Nodup ∧ (∀ v : W, v ∈ L) ∧ IsDegeneracyList r H L := by
  obtain ⟨L, h1, h2, h3⟩ :=
    exists_degeneracyList_aux hd (Finset.univ : Finset W).card Finset.univ rfl
  exact ⟨L, h1, fun v => (h2 v).mpr (Finset.mem_univ v), h3⟩

/-! ## §9. ⭐ THE UNIVERSE IS NOT PART OF THE PROBLEM. NEW.

`ConjectureAt r` quantifies over every type `W : Type u` carrying a `Fintype`. That binder is
noise: the statement is really about graphs on `Fin m`, one `m` per size. Proving it there
proves it in EVERY universe. -/

/-- **⭐ Reduction to `Fin`.** If the conjectured bound holds for every bipartite `r`-degenerate
graph on `Fin m`, for every `m`, then `ConjectureAt.{u} r` holds — in every universe `u`. So a
mechanised attack may work entirely with `Fin`-indexed graphs, where induction on `m` and
enumeration are available. -/
theorem conjectureAt_of_fin {r : ℕ}
    (h : ∀ (m : ℕ) (H : SimpleGraph (Fin m)), H.IsBipartite → IsDegenerate r H →
      VinogradovLE (exR H) (scale r)) : ConjectureAt.{u} r := by
  intro _hr V inst H hb hdg
  haveI : Fintype V := inst
  obtain ⟨C, hC, hev⟩ :=
    h (Fintype.card V) (H.map (Fintype.equivFin V).toEmbedding)
      (SimpleGraph.Colorable.map _ hb)
      (IsDegenerate.congr_iso (SimpleGraph.Iso.map (Fintype.equivFin V) H) hdg)
  refine ⟨C, hC, ?_⟩
  filter_upwards [hev] with n hn
  have hex : ex n H = ex n (H.map (Fintype.equivFin V).toEmbedding) :=
    SimpleGraph.extremalNumber_congr_right (SimpleGraph.Iso.map (Fintype.equivFin V) H)
  show ((ex n H : ℕ) : ℝ) ≤ C * scale r n
  rw [hex]
  exact hn

/-- The converse, in the base universe: `Fin m` lives in `Type 0`, so `ConjectureAt.{0} r`
specialises to it directly. Together with `conjectureAt_of_fin` this makes the `Fin` form an
EQUIVALENT restatement of the target, not merely a sufficient condition.

(For `u ≠ 0` the converse needs a `ULift`, since `Fin m : Type 0` is not a `Type u`; the useful
direction `conjectureAt_of_fin` is universe-free and is proved above.) -/
theorem conjectureAt_fin_iff {r : ℕ} (hr : 1 ≤ r) :
    ConjectureAt.{0} r ↔ ∀ (m : ℕ) (H : SimpleGraph (Fin m)), H.IsBipartite → IsDegenerate r H →
      VinogradovLE (exR H) (scale r) := by
  constructor
  · intro hc m H hb hdg
    exact hc hr (Fin m) H hb hdg
  · exact conjectureAt_of_fin

/-- **The `r = 0` conjunct of `Conjecture` is free**, so the whole conjecture is exactly the
family `{ConjectureAt r : r ≥ 1}`. -/
theorem conjecture_iff_ge_one : Conjecture.{u} ↔ ∀ r : ℕ, 1 ≤ r → ConjectureAt.{u} r := by
  constructor
  · intro h r _
    exact h r
  · intro h r
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · exact conjectureAt_zero
    · exact h r hr

end Erdos146Attack

-- ⛔ FOOTPRINTS. Clean is [propext, Classical.choice, Quot.sound]. No `sorryAx` may appear.
#print axioms Erdos146Attack.ex_le_choose_two
#print axioms Erdos146Attack.VinogradovLE.refl
#print axioms Erdos146Attack.VinogradovLE.trans
#print axioms Erdos146Attack.scale_le_scale
#print axioms Erdos146Attack.vinogradovLE_scale_mono
#print axioms Erdos146Attack.rpow_not_vinogradov
#print axioms Erdos146Attack.scale_not_vinogradov
#print axioms Erdos146Attack.trivial_bound_not_vinogradov
#print axioms Erdos146Attack.no_weaker_scale_suffices
#print axioms Erdos146Attack.aks_bound_insufficient
#print axioms Erdos146Attack.conjectureAt_conclusion_strictly_decreasing
#print axioms Erdos146Attack.exR_le_sq
#print axioms Erdos146Attack.exR_vinogradov_sq
#print axioms Erdos146Attack.distance_to_target
#print axioms Erdos146Attack.exists_lowDegree_vertex
#print axioms Erdos146Attack.isDegenerate_zero_iff
#print axioms Erdos146Attack.conjectureAt_zero
#print axioms Erdos146Attack.IsDegenerate.of_isContained
#print axioms Erdos146Attack.IsDegenerate.congr_iso
#print axioms Erdos146Attack.ex_mono_of_isContained
#print axioms Erdos146Attack.vinogradov_of_isContained
#print axioms Erdos146Attack.exists_degeneracyList_aux
#print axioms Erdos146Attack.exists_degeneracyList
#print axioms Erdos146Attack.conjectureAt_of_fin
#print axioms Erdos146Attack.conjectureAt_fin_iff
#print axioms Erdos146Attack.conjecture_iff_ge_one
