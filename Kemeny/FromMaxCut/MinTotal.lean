import Kemeny.FromMaxCut.Margins
import Mathlib.Algebra.BigOperators.Intervals

/-!
# The closed form of the minority total

The Kemeny budget of the produced instance is `minTotal + marginBudget`, and
the certificate must compute the number `minTotal` from the graph. This file
gives its closed form.

The minority total counts, over each unordered pair of candidates, the voters
on the pair's minority side (`min (againstCount a b) (againstCount b a)`). By
the margin facts, that minority is `0` on a pair inside one supercandidate
(unanimity) and `1` on every other pair (a `2`–`1` split). So `minTotal` is
simply the number of *non-supercandidate* pairs:

  `minTotal = C(N, 2) − 6n · C(M, 2)`,

where `N` is the number of candidates, `6n` the number of supercandidates, and
`M` their common size. Both binomials are written in the division-free Gauss
form `T(x) = ∑_{i < x} i` — exactly what the certificate computes with
`listSum ∘ range`, and what `Finset.sum_range_id_mul_two` bridges to `x(x−1)`.

The counting is two applications of one lemma
(`two_mul_card_filter_rankedPairs`): a symmetric predicate holds on twice as
many ordered distinct pairs as ranked pairs, because the ranked pairs and their
swaps partition the off-diagonal. This turns each count into an off-diagonal
cardinality, computed by `Finset.offDiag_card`.
-/

namespace Hardness

open Finset

/-! ## Counting ranked pairs under a symmetric predicate -/

section General

variable {A : Type*} [Fintype A]

/-- A symmetric predicate holds on twice as many ordered distinct pairs as
ranked pairs: the ranked pairs and their componentwise swaps partition the
off-diagonal, and both carry the predicate by symmetry. -/
theorem two_mul_card_filter_rankedPairs (r : LinearOrder A) (P : A → A → Prop)
    [DecidableRel P] (hsymm : ∀ a b, P a b → P b a) :
    2 * ((rankedPairs r).filter (fun p => P p.1 p.2)).card
      = (univ.offDiag.filter (fun p => P p.1 p.2)).card := by
  classical
  set S := (rankedPairs r).filter (fun p => P p.1 p.2) with hS
  have hswapcard : (S.image Prod.swap).card = S.card :=
    Finset.card_image_of_injective _ Prod.swap_injective
  have hdisj : Disjoint S (S.image Prod.swap) := by
    rw [Finset.disjoint_left]
    rintro p hp hp'
    rw [hS, mem_filter, mem_rankedPairs] at hp
    rw [mem_image] at hp'
    obtain ⟨q, hq, rfl⟩ := hp'
    rw [hS, mem_filter, mem_rankedPairs] at hq
    exact ranks_asymm hq.1 (by simpa using hp.1)
  have hunion : univ.offDiag.filter (fun p => P p.1 p.2) = S ∪ S.image Prod.swap := by
    ext p
    simp only [hS, mem_filter, mem_offDiag, mem_union, mem_image, mem_rankedPairs,
      mem_univ, true_and, Prod.exists, Prod.swap_prod_mk]
    constructor
    · rintro ⟨hne, hP⟩
      by_cases h : r.lt p.1 p.2
      · exact Or.inl ⟨h, hP⟩
      · exact Or.inr ⟨p.2, p.1, ⟨ranks_of_not_ranks hne h, hsymm _ _ hP⟩, by simp⟩
    · rintro (⟨h, hP⟩ | ⟨a, b, ⟨hab, hP⟩, heq⟩)
      · exact ⟨ranks_ne h, hP⟩
      · obtain ⟨rfl, rfl⟩ : p.1 = b ∧ p.2 = a := by rw [← heq]; exact ⟨rfl, rfl⟩
        exact ⟨(ranks_ne hab).symm, hsymm _ _ hP⟩
  rw [hunion, Finset.card_union_of_disjoint hdisj, hswapcard]
  omega

/-- **The count of ranked pairs**: `C(N, 2)` written in the division-free Gauss
form `∑_{i < N} i`. -/
theorem card_rankedPairs (r : LinearOrder A) :
    (rankedPairs r).card = ∑ i ∈ Finset.range (Fintype.card A), i := by
  have h := two_mul_card_filter_rankedPairs r (fun _ _ => True) (fun _ _ _ => trivial)
  rw [Finset.filter_true_of_mem (s := rankedPairs r) (fun _ _ => trivial),
      Finset.filter_true_of_mem (s := univ.offDiag) (fun _ _ => trivial),
      Finset.offDiag_card, Finset.card_univ] at h
  have hg := Finset.sum_range_id_mul_two (Fintype.card A)
  have hbridge : Fintype.card A * (Fintype.card A - 1)
      = Fintype.card A * Fintype.card A - Fintype.card A := by
    rw [Nat.mul_sub_one, Nat.mul_comm]
  omega

end General

/-! ## Counting supercandidate pairs -/

section Cand

variable {n M : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

open Classical in
/-- **The count of within-supercandidate ranked pairs**: each of the `6n`
supercandidates contributes `C(M, 2)` pairs among its `M` members. -/
theorem card_super_rankedPairs (r : LinearOrder (Cand n M G)) :
    ((rankedPairs r).filter (fun p : Cand n M G × Cand n M G => SameSuper p.1 p.2)).card
      = 6 * n * ∑ i ∈ Finset.range M, i := by
  classical
  have h := two_mul_card_filter_rankedPairs (A := Cand n M G) r
      (fun c c' => SameSuper c c') (fun _ _ hh => hh.symm)
  have hinj : Function.Injective (fun t : (Fin n × Letter) × (Fin M × Fin M) =>
      ((Sum.inl (t.1.1, t.1.2, t.2.1), Sum.inl (t.1.1, t.1.2, t.2.2))
        : Cand n M G × Cand n M G)) := by
    rintro ⟨⟨i, x⟩, ⟨m, m'⟩⟩ ⟨⟨j, y⟩, ⟨p, p'⟩⟩ heq
    simp only [Prod.mk.injEq, Sum.inl.injEq] at heq
    obtain ⟨⟨rfl, rfl, rfl⟩, -, -, rfl⟩ := heq
    rfl
  have himg : (univ.offDiag.filter (fun p : Cand n M G × Cand n M G => SameSuper p.1 p.2))
      = ((univ : Finset (Fin n × Letter)) ×ˢ (univ : Finset (Fin M)).offDiag).image
          (fun t : (Fin n × Letter) × (Fin M × Fin M) =>
            ((Sum.inl (t.1.1, t.1.2, t.2.1), Sum.inl (t.1.1, t.1.2, t.2.2))
              : Cand n M G × Cand n M G)) := by
    ext ⟨a, b⟩
    simp only [mem_filter, mem_offDiag, mem_univ, true_and, mem_image, Finset.mem_product,
      Finset.mem_offDiag, SameSuper, Prod.mk.injEq, Prod.exists]
    constructor
    · rintro ⟨hne, i, x, m, m', rfl, rfl⟩
      exact ⟨i, x, m, m', fun hmm => hne (by rw [hmm]), rfl, rfl⟩
    · rintro ⟨i, x, m, m', hmm, rfl, rfl⟩
      exact ⟨fun hab => hmm (by simpa using hab), i, x, m, m', rfl, rfl⟩
  have hcard : (univ.offDiag.filter (fun p : Cand n M G × Cand n M G => SameSuper p.1 p.2)).card
      = 6 * n * (M * M - M) := by
    rw [himg, Finset.card_image_of_injective _ hinj, Finset.card_product, Finset.offDiag_card]
    have hL : Fintype.card Letter = 6 := by decide
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, hL]
    rw [Nat.mul_comm n 6]
  rw [hcard] at h
  have hMM : M * M - M = 2 * ∑ i ∈ Finset.range M, i := by
    have hg := Finset.sum_range_id_mul_two M
    have hbridge : M * (M - 1) = M * M - M := by rw [Nat.mul_sub_one, Nat.mul_comm]
    omega
  have hfac : 6 * n * (2 * ∑ i ∈ Finset.range M, i)
      = 2 * (6 * n * ∑ i ∈ Finset.range M, i) :=
    mul_left_comm (6 * n) 2 (∑ i ∈ Finset.range M, i)
  rw [hMM, hfac] at h
  omega

/-! ## The closed form -/

/-- **The minority total of the produced profile**, in closed form: the number
of candidate pairs that do not lie inside one supercandidate,

  `minTotal = C(N, 2) − 6n · C(M, 2)`,

with both binomials in division-free Gauss form. The per-pair minority is `0`
inside a supercandidate (unanimity, `againstCount ∈ {0, 3}`) and `1` on every
other pair (a `2`–`1` split, `againstCount ∈ {1, 2}`); so the total counts the
non-supercandidate pairs. The reference ranking is immaterial
(`minTotal_congr`); any `r₀` works. -/
theorem minTotal_kemenyProfile (hsp : SpreadEdges n G) (r₀ : LinearOrder (Cand n M G)) :
    minTotal (kemenyProfile n G M) r₀
      = (∑ i ∈ Finset.range (Fintype.card (Cand n M G)), i)
        - 6 * n * ∑ i ∈ Finset.range M, i := by
  classical
  -- Each ranked pair's minority is `0` inside a supercandidate, else `1`.
  have hmin : ∀ p ∈ rankedPairs r₀,
      min (againstCount (kemenyProfile n G M) p.1 p.2)
          (againstCount (kemenyProfile n G M) p.2 p.1)
        = if SameSuper p.1 p.2 then 0 else 1 := by
    rintro ⟨a, b⟩ hp
    dsimp only
    rw [mem_rankedPairs] at hp
    have hne : a ≠ b := ranks_ne hp
    by_cases hs : SameSuper a b
    · rw [if_pos hs]
      obtain ⟨i, x, m, m', rfl, rfl⟩ := hs
      have hmm : m ≠ m' := fun h => hne (by rw [h])
      rcases lt_or_gt_of_ne hmm with hlt | hlt
      · have hz : againstCount (kemenyProfile n G M) (Sum.inl (i, x, m)) (Sum.inl (i, x, m')) = 0 :=
          againstCount_profile_same_super hlt
        omega
      · have hz : againstCount (kemenyProfile n G M) (Sum.inl (i, x, m')) (Sum.inl (i, x, m)) = 0 :=
          againstCount_profile_same_super hlt
        omega
    · rw [if_neg hs]
      have h1 : 1 ≤ againstCount (kemenyProfile n G M) a b :=
        one_le_againstCount_profile hsp hne hs
      have h2 : 1 ≤ againstCount (kemenyProfile n G M) b a :=
        one_le_againstCount_profile hsp hne.symm (fun h => hs h.symm)
      have h3 : againstCount (kemenyProfile n G M) a b
              + againstCount (kemenyProfile n G M) b a = 3 := by
        have h := againstCount_add_againstCount (kemenyProfile n G M) hne
        rwa [kemenyProfile_length] at h
      omega
  -- So `minTotal` counts the non-supercandidate ranked pairs.
  rw [minTotal, Finset.sum_congr rfl hmin]
  have hswap : ∀ p : Cand n M G × Cand n M G,
      (if SameSuper p.1 p.2 then (0 : ℕ) else 1)
        = if ¬ SameSuper p.1 p.2 then 1 else 0 := by
    intro p; by_cases h : SameSuper p.1 p.2 <;> simp [h]
  rw [Finset.sum_congr rfl (fun p _ => hswap p), ← Finset.card_filter]
  -- non-super = all ranked pairs minus super ranked pairs
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := rankedPairs r₀) (p := fun p : Cand n M G × Cand n M G => SameSuper p.1 p.2)
  rw [card_super_rankedPairs] at hsplit
  rw [card_rankedPairs] at hsplit
  omega

end Cand

end Hardness
