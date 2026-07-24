import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.Prod
import HardnessReductions.Core

/-!
# Rankings, the Kendall tau distance, and the Kemeny objective

The preliminaries of the Kemeny project: rankings are bundled `LinearOrder`
values — the representation of SocialChoiceLean, whose `Prefers` is `.lt`, so
`r.lt a b` reads "`r` ranks `a` above `b`" (smaller is better; the top of the
ranking is the bottom of the order). A profile is a `List (LinearOrder A)`:
the number of voters is the length of an explicit list, per the library's
size discipline, and the three-voter restriction of the target problem is
`voters.length = 3`.

`kendallTau r s` counts the ordered pairs `(a, b)` that `r` ranks `a` above
`b` and `s` ranks `b` above `a` — each disagreeing unordered pair is counted
exactly once, in the orientation `r` ranks it. `kemenyCost voters r` is the
total Kendall tau distance from `r` to the profile.

The engine of everything downstream is the **pairwise decomposition**
(`kemenyCost_eq_sum_against`): the Kemeny cost of `r` is, summed over the
ordered pairs `(a, b)` that `r` ranks `a` above `b`, the number of voters who
rank `b` above `a`. Both directions of the hardness reduction are sums over
pair categories through this lemma.

## Decidability of bundled orders

`LinearOrder.toDecidableLT` is instance-registered and its projection chain
unifies with any bundled value — but only while a *single* bundled
`LinearOrder` is in scope; with two or more, instance search fails. The
working rules, observed throughout this file:

* a definition or proof that filters on a bundled order installs the specific
  instance with `letI := r.toDecidableLT`;
* statements never carry an `if` over a bundled order when more than one is
  in scope — the per-voter pair cost is spelled `againstCount [v] a b`, whose
  decidability is internal to `againstCount`, rather than
  `if v.lt b a then 1 else 0`.
-/

namespace Hardness

open Finset

variable {A : Type*}

/-! ## Bundled-order helpers

Order-theoretic facts about a bundled `r : LinearOrder A`, packaged so that
call sites need no `letI`: each helper installs its own instance. These are
used constantly — every case split on how a ranking orders a pair goes
through them. -/

/-- A ranking never ranks an alternative above itself, so ranked pairs are
pairs of distinct alternatives. -/
theorem ranks_ne {r : LinearOrder A} {a b : A} (h : r.lt a b) : a ≠ b := by
  letI := r
  exact ne_of_lt h

/-- A ranking ranks each pair one way only. -/
theorem ranks_asymm {r : LinearOrder A} {a b : A} (h : r.lt a b) : ¬r.lt b a := by
  letI := r
  exact lt_asymm h

/-- Rankings are transitive, in bundled form. -/
theorem ranks_trans {r : LinearOrder A} {a b c : A} (h1 : r.lt a b) (h2 : r.lt b c) :
    r.lt a c := by
  letI := r
  exact lt_trans h1 h2

/-- A ranking ranks every pair of distinct alternatives one way or the other:
totality, in the form the case splits consume. -/
theorem ranks_of_not_ranks {r : LinearOrder A} {a b : A} (hne : a ≠ b) (h : ¬r.lt a b) :
    r.lt b a := by
  letI := r
  rcases lt_trichotomy a b with h1 | h1 | h1
  · exact absurd h1 h
  · exact absurd h1 hne
  · exact h1

/-- On a pair of distinct alternatives, ranking one way is refusing the other:
the two-sided form of asymmetry-plus-totality. -/
theorem ranks_iff_not_ranks {r : LinearOrder A} {a b : A} (hne : a ≠ b) :
    r.lt a b ↔ ¬r.lt b a :=
  ⟨ranks_asymm, ranks_of_not_ranks hne.symm⟩

/-! ## Counting disagreeing voters (no finiteness needed) -/

/-- How many voters rank `b` above `a` — the cost that the pairwise
decomposition charges for ranking `a` above `b`, and the `n_{ba}` of the
paper. -/
def againstCount (voters : List (LinearOrder A)) (a b : A) : ℕ :=
  voters.countP fun v ↦ decide (v.lt b a)

@[simp] theorem againstCount_nil (a b : A) : againstCount [] a b = 0 := rfl

/-- A single voter's verdict on the pair: cost `1` exactly if `v` ranks `b`
above `a`. The atom of the pairwise decomposition — pair-cost computations
against a concrete voter go through this. -/
theorem againstCount_singleton (v : LinearOrder A) (a b : A) :
    againstCount [v] a b = if v.lt b a then 1 else 0 := by
  rw [againstCount, List.countP_cons, List.countP_nil]
  by_cases h : v.lt b a <;> simp [h]

/-- A voter ranking `a` above `b` is not against that order. -/
theorem againstCount_singleton_of_lt {v : LinearOrder A} {a b : A} (h : v.lt a b) :
    againstCount [v] a b = 0 := by
  rw [againstCount_singleton, if_neg (ranks_asymm h)]

/-- A voter ranking `b` above `a` is against ranking `a` above `b`. -/
theorem againstCount_singleton_of_gt {v : LinearOrder A} {a b : A} (h : v.lt b a) :
    againstCount [v] a b = 1 := by
  rw [againstCount_singleton, if_pos h]

theorem againstCount_cons (v : LinearOrder A) (voters : List (LinearOrder A)) (a b : A) :
    againstCount (v :: voters) a b = againstCount [v] a b + againstCount voters a b := by
  rw [againstCount, againstCount, againstCount, List.countP_cons, List.countP_cons,
    List.countP_nil]
  omega

/-- The number of voters who disagree with putting `a` above `b` never exceeds
the number of voters. -/
theorem againstCount_le_length (voters : List (LinearOrder A)) (a b : A) :
    againstCount voters a b ≤ voters.length :=
  List.countP_le_length ..

/-- A single witness puts the count at one: some voter ranks `b` above `a`. -/
theorem one_le_againstCount {voters : List (LinearOrder A)} {a b : A}
    {v : LinearOrder A} (hv : v ∈ voters) (h : v.lt b a) :
    1 ≤ againstCount voters a b := by
  rw [againstCount]
  exact List.countP_pos_iff.mpr ⟨v, hv, decide_eq_true h⟩

/-- No voter against means count zero — the `againstCount` form of
unanimity. -/
theorem againstCount_eq_zero {voters : List (LinearOrder A)} {a b : A}
    (h : ∀ v ∈ voters, ¬v.lt b a) : againstCount voters a b = 0 := by
  rw [againstCount, List.countP_eq_zero]
  intro v hv
  simpa using h v hv

/-- Every voter against means full count — unanimity in the other
orientation. -/
theorem againstCount_eq_length {voters : List (LinearOrder A)} {a b : A}
    (h : ∀ v ∈ voters, v.lt b a) : againstCount voters a b = voters.length := by
  rw [againstCount, List.countP_eq_length]
  intro v hv
  simpa using h v hv

/-- **Every voter takes a side**: on a pair of distinct alternatives, the
voters against one orientation and the voters against the other partition the
electorate. What makes `min (againstCount a b) (againstCount b a)` and its
complement read as "minority" and "majority". -/
theorem againstCount_add_againstCount {a b : A} (voters : List (LinearOrder A))
    (h : a ≠ b) :
    againstCount voters a b + againstCount voters b a = voters.length := by
  induction voters with
  | nil => rfl
  | cons v vs ih =>
    rw [againstCount_cons v vs a b, againstCount_cons v vs b a, againstCount_singleton,
      againstCount_singleton, List.length_cons]
    have h1 : ((if v.lt b a then 1 else 0) + (if v.lt a b then 1 else 0) : ℕ) = 1 := by
      by_cases hab : v.lt a b
      · rw [if_neg (ranks_asymm hab), if_pos hab]
      · rw [if_pos (ranks_of_not_ranks h hab), if_neg hab]
    omega

/-! ## The Kendall tau distance -/

variable [Fintype A]

/-- The ordered pairs `(a, b)` that `r` ranks above (`r.lt a b`) and `s` ranks
below (`s.lt b a`). Each unordered pair of disagreement appears exactly once,
oriented as `r` ranks it. -/
def discordantPairs (r s : LinearOrder A) : Finset (A × A) :=
  letI := r.toDecidableLT
  letI := s.toDecidableLT
  univ.filter fun p : A × A ↦ r.lt p.1 p.2 ∧ s.lt p.2 p.1

@[simp] theorem mem_discordantPairs {r s : LinearOrder A} {p : A × A} :
    p ∈ discordantPairs r s ↔ r.lt p.1 p.2 ∧ s.lt p.2 p.1 := by
  letI := r.toDecidableLT
  letI := s.toDecidableLT
  simp only [discordantPairs, mem_filter_univ]

/-- The Kendall tau distance between two rankings: on how many pairs of
alternatives do they disagree? -/
def kendallTau (r s : LinearOrder A) : ℕ :=
  (discordantPairs r s).card

/-- Componentwise swap matches the discordant pairs of `r, s` with those of
`s, r`. -/
theorem discordantPairs_swap (r s : LinearOrder A) :
    (discordantPairs r s).image Prod.swap = discordantPairs s r := by
  ext p
  rw [mem_image]
  constructor
  · rintro ⟨q, hq, rfl⟩
    rw [mem_discordantPairs] at hq
    rw [mem_discordantPairs]
    exact ⟨hq.2, hq.1⟩
  · intro hp
    rw [mem_discordantPairs] at hp
    exact ⟨p.swap, by rw [mem_discordantPairs]; exact ⟨hp.2, hp.1⟩, Prod.swap_swap p⟩

/-- The distance is symmetric. -/
theorem kendallTau_comm (r s : LinearOrder A) : kendallTau r s = kendallTau s r := by
  rw [kendallTau, kendallTau, ← discordantPairs_swap r s,
    card_image_of_injective _ Prod.swap_injective]

/-- A ranking is at distance `0` from itself. -/
@[simp] theorem kendallTau_self (r : LinearOrder A) : kendallTau r r = 0 := by
  letI := r
  rw [kendallTau, card_eq_zero, discordantPairs, filter_eq_empty_iff]
  rintro p - ⟨h1, h2⟩
  exact absurd h2 (lt_asymm h1)

/-! ## The Kemeny objective -/

/-- The Kemeny cost of an output ranking `r` against a profile: the total
Kendall tau distance to the voters. -/
def kemenyCost (voters : List (LinearOrder A)) (r : LinearOrder A) : ℕ :=
  (voters.map fun v ↦ kendallTau v r).sum

@[simp] theorem kemenyCost_nil (r : LinearOrder A) : kemenyCost [] r = 0 := rfl

theorem kemenyCost_cons (v : LinearOrder A) (voters : List (LinearOrder A))
    (r : LinearOrder A) :
    kemenyCost (v :: voters) r = kendallTau v r + kemenyCost voters r := by
  rw [kemenyCost, List.map_cons, List.sum_cons, kemenyCost]

/-! ## The pairwise decomposition -/

/-- The ordered pairs `(a, b)` that `r` ranks `a` above `b` — the index set of
the pairwise decomposition. Exactly one of `(a, b)`, `(b, a)` appears for each
pair of distinct alternatives. -/
def rankedPairs (r : LinearOrder A) : Finset (A × A) :=
  letI := r.toDecidableLT
  univ.filter fun p : A × A ↦ r.lt p.1 p.2

@[simp] theorem mem_rankedPairs {r : LinearOrder A} {p : A × A} :
    p ∈ rankedPairs r ↔ r.lt p.1 p.2 := by
  letI := r.toDecidableLT
  simp only [rankedPairs, mem_filter_univ]

/-- A single voter's distance to `r`, indexed by the pairs `r` ranks: the
one-voter case of the decomposition, and the inductive step of its proof. -/
theorem kendallTau_eq_sum_rankedPairs (v r : LinearOrder A) :
    kendallTau v r = ∑ p ∈ rankedPairs r, againstCount [v] p.1 p.2 := by
  letI := v.toDecidableLT
  rw [Finset.sum_congr rfl fun (p : A × A) _ ↦ againstCount_singleton v p.1 p.2,
    ← card_filter, kendallTau]
  have himg : (rankedPairs r).filter (fun p ↦ v.lt p.2 p.1)
      = (discordantPairs v r).image Prod.swap := by
    ext p
    rw [mem_filter, mem_rankedPairs, mem_image]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨p.swap, by rw [mem_discordantPairs]; exact ⟨h2, h1⟩, Prod.swap_swap p⟩
    · rintro ⟨q, hq, rfl⟩
      rw [mem_discordantPairs] at hq
      exact ⟨hq.2, hq.1⟩
  rw [himg, card_image_of_injective _ Prod.swap_injective]

/-- **The pairwise decomposition of the Kemeny objective**: the cost of `r` is,
over the pairs `(a, b)` that `r` ranks `a` above `b`, the number of voters
ranking `b` above `a`. Everything downstream — both directions of the hardness
reduction — is a sum over pair categories through this identity. -/
theorem kemenyCost_eq_sum_against (voters : List (LinearOrder A)) (r : LinearOrder A) :
    kemenyCost voters r = ∑ p ∈ rankedPairs r, againstCount voters p.1 p.2 := by
  induction voters with
  | nil => simp
  | cons v vs ih =>
    rw [kemenyCost_cons, ih, kendallTau_eq_sum_rankedPairs v r, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ ↦ (againstCount_cons v vs p.1 p.2).symm

end Hardness
