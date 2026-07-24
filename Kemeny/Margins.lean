import Mathlib.Data.Fintype.BigOperators
import Kemeny.Rankings

/-!
# The margin objective, and the affine bridge

The paper's two Kemeny objectives, and the identity connecting them. For a
pair of distinct alternatives, `min (againstCount a b) (againstCount b a)`
voters disagree with *any* ranking — the minority side of the pair is a cost
no output can avoid. `minTotal` sums these unavoidable costs; `marginCost`
(the paper's `Kemeny₂`) charges a ranking only the *excess*: for each pair it
orders against a strict majority, the majority margin. The affine bridge is

  `kemenyCost voters r = minTotal voters + marginCost voters r`,

so the two objectives have the same minimizers, and a budget for one is a
budget for the other shifted by a constant. The hardness reduction computes
everything in margin units and converts once, through
`exists_kemenyCost_le_iff`.

Formally `minTotal` is indexed by the ranked pairs of an arbitrary reference
ranking, since the pairs of a `min` are unordered; that the choice does not
matter is `minTotal_congr`, an instance of `sum_rankedPairs_congr` — the sum
of any symmetric pair function over `rankedPairs r` is independent of `r`,
because reorienting a pair fixes a symmetric value. Downstream this freedom
matters: the closed form of the constant is computed against whichever
ranking makes the counting easiest.
-/

namespace Hardness

open Finset

variable {A : Type*} [Fintype A]

/-! ## Sums over ranked pairs of symmetric functions -/

/-- **Reorientation invariance**: summing a symmetric pair function over the
ranked pairs of `r` does not depend on `r`. The bijection sends each pair to
its `r'`-orientation; symmetry of `f` makes the values match. -/
theorem sum_rankedPairs_congr {M : Type*} [AddCommMonoid M] (r r' : LinearOrder A)
    (f : A → A → M) (hf : ∀ a b, f a b = f b a) :
    ∑ p ∈ rankedPairs r, f p.1 p.2 = ∑ p ∈ rankedPairs r', f p.1 p.2 := by
  letI := r.toDecidableLT
  letI := r'.toDecidableLT
  refine Finset.sum_nbij' (i := fun p ↦ if r'.lt p.1 p.2 then p else p.swap)
    (j := fun p ↦ if r.lt p.1 p.2 then p else p.swap) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    rw [mem_rankedPairs] at hp
    by_cases h' : r'.lt p.1 p.2
    · rw [if_pos h', mem_rankedPairs]
      exact h'
    · rw [if_neg h', mem_rankedPairs, Prod.fst_swap, Prod.snd_swap]
      exact ranks_of_not_ranks (ranks_ne hp) h'
  · intro p hp
    rw [mem_rankedPairs] at hp
    by_cases h : r.lt p.1 p.2
    · rw [if_pos h, mem_rankedPairs]
      exact h
    · rw [if_neg h, mem_rankedPairs, Prod.fst_swap, Prod.snd_swap]
      exact ranks_of_not_ranks (ranks_ne hp) h
  · intro p hp
    rw [mem_rankedPairs] at hp
    by_cases h' : r'.lt p.1 p.2
    · rw [if_pos h', if_pos hp]
    · rw [if_neg h', Prod.fst_swap, Prod.snd_swap, if_neg (ranks_asymm hp), Prod.swap_swap]
  · intro p hp
    rw [mem_rankedPairs] at hp
    by_cases h : r.lt p.1 p.2
    · rw [if_pos h, if_pos hp]
    · rw [if_neg h, Prod.fst_swap, Prod.snd_swap, if_neg (ranks_asymm hp), Prod.swap_swap]
  · intro p hp
    by_cases h' : r'.lt p.1 p.2
    · rw [if_pos h']
    · rw [if_neg h', Prod.fst_swap, Prod.snd_swap]
      exact hf p.1 p.2

/-! ## The two objectives -/

/-- The unavoidable part of the Kemeny cost: over each pair of alternatives,
the voters on the pair's minority side. Indexed by the ranked pairs of an
arbitrary reference ranking `r`, which does not matter (`minTotal_congr`) —
`min` is symmetric in the orientation. -/
def minTotal (voters : List (LinearOrder A)) (r : LinearOrder A) : ℕ :=
  ∑ p ∈ rankedPairs r, min (againstCount voters p.1 p.2) (againstCount voters p.2 p.1)

/-- The reference ranking indexing `minTotal` is immaterial. -/
theorem minTotal_congr (voters : List (LinearOrder A)) (r r' : LinearOrder A) :
    minTotal voters r = minTotal voters r' :=
  sum_rankedPairs_congr r r'
    (fun a b ↦ min (againstCount voters a b) (againstCount voters b a))
    (fun _ _ ↦ min_comm ..)

/-- **The margin objective** — the paper's `Kemeny₂`: for each pair the output
ranks against a strict majority of voters, the majority margin. In `ℕ` the
truncated subtraction is exactly "the margin when positive, else zero". -/
def marginCost (voters : List (LinearOrder A)) (r : LinearOrder A) : ℕ :=
  ∑ p ∈ rankedPairs r, (againstCount voters p.1 p.2 - againstCount voters p.2 p.1)

/-! ## The margin cost as a sum over the ordered square

The index form consumed by cost computations: summing over *all* ordered
pairs, with the unranked orientation contributing `0`, lets a structured
alternative type split the sum along its sums and products — explicit block
decompositions instead of pair-set cardinalities. -/

/-- The margin cost of one ordered pair: the (truncated) margin paid if `r`
ranks `a` above `b`, else `0`. -/
def orientedMargin (voters : List (LinearOrder A)) (r : LinearOrder A) (a b : A) : ℕ :=
  letI := r.toDecidableLT
  if r.lt a b then againstCount voters a b - againstCount voters b a else 0

omit [Fintype A] in
theorem orientedMargin_of_lt {r : LinearOrder A} {a b : A}
    (voters : List (LinearOrder A)) (h : r.lt a b) :
    orientedMargin voters r a b
      = againstCount voters a b - againstCount voters b a := by
  letI := r.toDecidableLT
  rw [orientedMargin, if_pos h]

omit [Fintype A] in
theorem orientedMargin_of_not_lt {r : LinearOrder A} {a b : A}
    (voters : List (LinearOrder A)) (h : ¬r.lt a b) :
    orientedMargin voters r a b = 0 := by
  letI := r.toDecidableLT
  rw [orientedMargin, if_neg h]

/-- `marginCost` as a double sum over the full ordered square. -/
theorem marginCost_eq_sum_orientedMargin (voters : List (LinearOrder A))
    (r : LinearOrder A) :
    marginCost voters r = ∑ a, ∑ b, orientedMargin voters r a b := by
  letI := r.toDecidableLT
  rw [marginCost]
  simp only [rankedPairs]
  rw [sum_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ ↦ Finset.sum_congr rfl fun b _ ↦ ?_
  dsimp only
  by_cases h : r.lt a b
  · rw [if_pos h, orientedMargin_of_lt voters h]
  · rw [if_neg h, orientedMargin_of_not_lt voters h]

/-! ## The affine bridge -/

/-- **The affine bridge** — the paper's `Kemeny₁ = Σ min + Kemeny₂`: the
Kemeny cost of any ranking is the unavoidable minority total plus its margin
cost. Pointwise this is `x = min x y + (x - y)` in `ℕ`. -/
theorem kemenyCost_eq_minTotal_add_marginCost (voters : List (LinearOrder A))
    (r : LinearOrder A) :
    kemenyCost voters r = minTotal voters r + marginCost voters r := by
  rw [kemenyCost_eq_sum_against, minTotal, marginCost, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun p _ ↦ by omega

/-- **The budget conversion**: a Kemeny budget of `minTotal + c` is met exactly
when a margin budget of `c` is — the form in which the hardness reduction
states its target instance, with `minTotal` computed against any convenient
reference ranking `r₀`. -/
theorem exists_kemenyCost_le_iff (voters : List (LinearOrder A)) (r₀ : LinearOrder A)
    (c : ℕ) :
    (∃ r, kemenyCost voters r ≤ minTotal voters r₀ + c) ↔
      ∃ r, marginCost voters r ≤ c := by
  constructor
  · rintro ⟨r, hr⟩
    rw [kemenyCost_eq_minTotal_add_marginCost, minTotal_congr voters r r₀] at hr
    exact ⟨r, by omega⟩
  · rintro ⟨r, hr⟩
    refine ⟨r, ?_⟩
    rw [kemenyCost_eq_minTotal_add_marginCost, minTotal_congr voters r r₀]
    omega

end Hardness
