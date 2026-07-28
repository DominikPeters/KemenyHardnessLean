import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Max
import KemenyHardness.Margins

/-!
# Clone contraction

Conitzer's block lemma (Theorem 1 of "Computing Slater rankings using
similarities among candidates", 2006), in the constructive, cost-monotone form
the Kemeny reduction consumes. A set `S` of *clones* — candidates every voter
compares uniformly against each outsider, and orders internally in a common
way `ω` — can be contracted in any output ranking: move every member of `S`
to the position of a cheapest member `rep`, ordered internally by `ω`, without
increasing the Kemeny cost. Iterating over the supercandidates of the
reduction turns an arbitrary low-cost ranking into a *block* ranking, which is
where the whole reverse-direction analysis happens.

## No list surgery

`contractClones` is not defined by cutting and splicing positions. The
contracted ranking is `LinearOrder.lift'` along the key
`x ↦ if x ∈ S then (rep, x) else (x, x)` into `A ×ₗ A`, lexicographic with
the first component ordered by the original ranking `r` and the second by
`ω`: members of `S` travel to `rep`'s position and settle internally by `ω`,
outsiders keep their `r`-order. The key is injective outright — a collision
across the `S`-boundary already forces its two second components equal — so
the order exists with no side conditions, and its four comparison laws
(`contractClones_lt_*`) are the complete downstream interface.

## No pair bijections

The cost comparison never reorients pairs. `kemenyCost_eq_sum_orientedCost`
rewrites the Kemeny cost as a double sum over *ordered* pairs of the one-sided
cost `orientedCost` (zero in the unranked orientation), and `sum_sum_split`
cuts the square into the `S×S` block (cost `0` after contraction, by
unanimity), the mixed block (each member's row becomes `rep`'s row, and `rep`
minimizes `sideCost`), and the outside block (untouched). Summing the three
comparisons is the theorem (`kemenyCost_contractClones_le`); choosing `rep`
by `Finset.exists_min_image` gives the existence form (`exists_contract_le`).
-/

namespace Hardness

open Finset

variable {A : Type*}

/-! ## The oriented-cost decomposition -/

/-- The cost a ranking pays on the *ordered* pair `(a, b)`: the disagreeing
voters if it ranks `a` above `b`, nothing otherwise. Summing over both
orientations of a pair gives the pair's cost, so summing over the full square
gives the Kemeny cost (`kemenyCost_eq_sum_orientedCost`) — the index shape
that makes membership splits painless. -/
def orientedCost (voters : List (LinearOrder A)) (r : LinearOrder A) (a b : A) : ℕ :=
  orient r (againstCount voters) a b

theorem orientedCost_of_lt {r : LinearOrder A} {a b : A} (voters : List (LinearOrder A))
    (h : r.lt a b) : orientedCost voters r a b = againstCount voters a b :=
  orient_of_lt _ h

theorem orientedCost_of_not_lt {r : LinearOrder A} {a b : A} (voters : List (LinearOrder A))
    (h : ¬r.lt a b) : orientedCost voters r a b = 0 :=
  orient_of_not_lt _ h

/-- Two rankings agreeing on an ordered pair pay the same oriented cost on
it. -/
theorem orientedCost_congr {r r' : LinearOrder A} {a b : A} (voters : List (LinearOrder A))
    (h : r.lt a b ↔ r'.lt a b) :
    orientedCost voters r a b = orientedCost voters r' a b :=
  orient_congr _ h

section ContractedRanking

variable [DecidableEq A]

/-! ## The contracted ranking -/

/-- The contraction key: members of `S` travel to the representative's
position (first component) and are separated by their own identity (second
component); outsiders stay where they are. Read into `A ×ₗ A` with the first
component ordered by the original ranking and the second by the internal
order of the clones. -/
def cloneKey (S : Finset A) (rep : A) (x : A) : A ×ₗ A :=
  if x ∈ S then toLex (rep, x) else toLex (x, x)

/-- The key is injective — with no hypothesis at all: any collision forces the
two second components, hence the two candidates, to be equal. -/
theorem cloneKey_injective (S : Finset A) (rep : A) :
    Function.Injective (cloneKey S rep) := by
  intro x y h
  simp only [cloneKey] at h
  by_cases hx : x ∈ S <;> by_cases hy : y ∈ S
  · rw [if_pos hx, if_pos hy, toLex_inj] at h
    injection h
  · rw [if_pos hx, if_neg hy, toLex_inj] at h
    injection h
  · rw [if_neg hx, if_pos hy, toLex_inj] at h
    injection h
  · rw [if_neg hx, if_neg hy, toLex_inj] at h
    injection h

/-- **The contracted ranking**: members of `S` move to `rep`'s position,
internally ordered by `ω`; outsiders are untouched. Defined by lifting the
clone key along the lexicographic order — no positions, no list surgery. -/
@[implicit_reducible]
def contractClones (r ω : LinearOrder A) (S : Finset A) (rep : A) : LinearOrder A :=
  letI : LinearOrder (A ×ₗ A) := @Prod.Lex.instLinearOrder A A r ω
  LinearOrder.lift' (cloneKey S rep) (cloneKey_injective S rep)

section ComparisonLaws

variable {r ω : LinearOrder A} {S : Finset A} {rep : A}

/-- The raw comparison law of the lifted order, before membership analysis. -/
private theorem contractClones_lt_iff {x y : A} :
    (contractClones r ω S rep).lt x y ↔
      r.lt (ofLex (cloneKey S rep x)).1 (ofLex (cloneKey S rep y)).1
        ∨ (ofLex (cloneKey S rep x)).1 = (ofLex (cloneKey S rep y)).1
            ∧ ω.lt (ofLex (cloneKey S rep x)).2 (ofLex (cloneKey S rep y)).2 := by
  exact @Prod.Lex.lt_iff A A r.toLT ω.toLT (cloneKey S rep x) (cloneKey S rep y)

/-- Outsiders are compared as before. -/
theorem contractClones_lt_outside {x y : A} (hx : x ∉ S) (hy : y ∉ S) :
    (contractClones r ω S rep).lt x y ↔ r.lt x y := by
  rw [contractClones_lt_iff]
  simp only [cloneKey, if_neg hx, if_neg hy, ofLex_toLex]
  constructor
  · rintro (h | ⟨rfl, h⟩)
    · exact h
    · exact absurd h (fun h' ↦ ranks_ne h' rfl)
  · exact Or.inl

/-- A member is compared to an outsider as the representative was. Needs the
representative to be a member: were `rep` itself the outsider, the first lex
component of the two keys would tie. -/
theorem contractClones_lt_left {s x : A} (hrep : rep ∈ S) (hs : s ∈ S) (hx : x ∉ S) :
    (contractClones r ω S rep).lt s x ↔ r.lt rep x := by
  rw [contractClones_lt_iff]
  simp only [cloneKey, if_pos hs, if_neg hx, ofLex_toLex]
  constructor
  · rintro (h | ⟨rfl, h⟩)
    · exact h
    · exact absurd hrep hx
  · exact Or.inl

/-- An outsider is compared to a member as it was to the representative. Needs
the representative to be a member, as `contractClones_lt_left` does. -/
theorem contractClones_lt_right {s x : A} (hrep : rep ∈ S) (hs : s ∈ S) (hx : x ∉ S) :
    (contractClones r ω S rep).lt x s ↔ r.lt x rep := by
  rw [contractClones_lt_iff]
  simp only [cloneKey, if_pos hs, if_neg hx, ofLex_toLex]
  constructor
  · rintro (h | ⟨rfl, h⟩)
    · exact h
    · exact absurd hrep hx
  · exact Or.inl

/-- Members are compared by the internal order `ω`. -/
theorem contractClones_lt_inside {s s' : A} (hs : s ∈ S) (hs' : s' ∈ S) :
    (contractClones r ω S rep).lt s s' ↔ ω.lt s s' := by
  rw [contractClones_lt_iff]
  simp only [cloneKey, if_pos hs, if_pos hs', ofLex_toLex]
  constructor
  · rintro (h | ⟨-, h⟩)
    · exact absurd rfl (ranks_ne h)
    · exact h
  · exact fun h ↦ Or.inr ⟨trivial, h⟩

end ComparisonLaws

end ContractedRanking

variable [Fintype A]

/-- The Kemeny cost as a double sum of oriented costs over the full square of
ordered pairs — the unranked orientation contributes zero, so nothing is
double-counted. -/
theorem kemenyCost_eq_sum_orientedCost (voters : List (LinearOrder A)) (r : LinearOrder A) :
    kemenyCost voters r = ∑ a, ∑ b, orientedCost voters r a b := by
  rw [kemenyCost_eq_sum_against, sum_rankedPairs_eq_sum_orient]
  rfl

variable [DecidableEq A]

/-- Splitting the square: a double sum over all ordered pairs is the `S×S`
block, plus the mixed block with both orientations folded together, plus the
block outside `S`. -/
theorem sum_sum_split (S : Finset A) (F : A → A → ℕ) :
    ∑ a, ∑ b, F a b
      = ((∑ a ∈ S, ∑ b ∈ S, F a b) + ∑ s ∈ S, ∑ x ∈ Sᶜ, (F s x + F x s))
        + ∑ a ∈ Sᶜ, ∑ b ∈ Sᶜ, F a b := by
  have h1 : (∑ a, ∑ b, F a b) = (∑ a ∈ S, ∑ b, F a b) + ∑ a ∈ Sᶜ, ∑ b, F a b :=
    (Finset.sum_add_sum_compl S _).symm
  have h2 : (∑ a ∈ S, ∑ b, F a b)
      = (∑ a ∈ S, ∑ b ∈ S, F a b) + ∑ a ∈ S, ∑ b ∈ Sᶜ, F a b := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ ↦ (Finset.sum_add_sum_compl S _).symm
  have h3 : (∑ a ∈ Sᶜ, ∑ b, F a b)
      = (∑ a ∈ Sᶜ, ∑ b ∈ S, F a b) + ∑ a ∈ Sᶜ, ∑ b ∈ Sᶜ, F a b := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ ↦ (Finset.sum_add_sum_compl S _).symm
  have h4 : (∑ a ∈ Sᶜ, ∑ b ∈ S, F a b) = ∑ s ∈ S, ∑ x ∈ Sᶜ, F x s := Finset.sum_comm
  have h5 : (∑ s ∈ S, ∑ x ∈ Sᶜ, (F s x + F x s))
      = (∑ s ∈ S, ∑ x ∈ Sᶜ, F s x) + ∑ s ∈ S, ∑ x ∈ Sᶜ, F x s := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ ↦ Finset.sum_add_distrib
  omega

/-- The cost a candidate `s` pays against the outside of `S`, in ranking `r`:
both orientations of every pair `{s, x}` with `x ∉ S`. The quantity the
contraction representative minimizes. -/
def sideCost (voters : List (LinearOrder A)) (r : LinearOrder A) (S : Finset A) (s : A) : ℕ :=
  ∑ x ∈ Sᶜ, (orientedCost voters r s x + orientedCost voters r x s)

/-! ## The cost theorem -/

section CostTheorem

variable {voters : List (LinearOrder A)} {r ω : LinearOrder A} {S : Finset A} {rep : A}

/-- **Contraction does not increase the Kemeny cost**, provided the
representative is a cheapest member — Conitzer's Theorem 1 in cost-monotone
form. Hypotheses: every voter compares every member of `S` with every
outsider as it compares `rep` (the clone condition), every voter orders `S`
internally by `ω` (unanimity), and `rep` minimizes the outside cost among
members. -/
theorem kemenyCost_contractClones_le (hrep : rep ∈ S)
    (hclone : ∀ v ∈ voters, ∀ s ∈ S, ∀ x, x ∉ S → (v.lt s x ↔ v.lt rep x))
    (hunan : ∀ v ∈ voters, ∀ s ∈ S, ∀ s' ∈ S, (v.lt s s' ↔ ω.lt s s'))
    (hmin : ∀ s ∈ S, sideCost voters r S rep ≤ sideCost voters r S s) :
    kemenyCost voters (contractClones r ω S rep) ≤ kemenyCost voters r := by
  -- voters see members and the representative identically, in both orientations
  have hagainst₁ : ∀ s ∈ S, ∀ x ∉ S,
      againstCount voters s x = againstCount voters rep x := by
    intro s hs x hx
    have hxs : x ≠ s := fun h ↦ hx (h ▸ hs)
    have hxrep : x ≠ rep := fun h ↦ hx (h ▸ hrep)
    rw [againstCount, againstCount]
    refine List.countP_congr fun v hv ↦ ?_
    simp only [decide_eq_true_eq]
    rw [ranks_iff_not_ranks hxs, ranks_iff_not_ranks hxrep]
    exact not_congr (hclone v hv s hs x hx)
  have hagainst₂ : ∀ s ∈ S, ∀ x ∉ S,
      againstCount voters x s = againstCount voters x rep := by
    intro s hs x hx
    rw [againstCount, againstCount]
    refine List.countP_congr fun v hv ↦ ?_
    simp only [decide_eq_true_eq]
    exact hclone v hv s hs x hx
  -- the S×S block collapses to zero: the contracted ranking agrees with every voter on S
  have hSS : ∑ a ∈ S, ∑ b ∈ S, orientedCost voters (contractClones r ω S rep) a b = 0 := by
    refine Finset.sum_eq_zero fun s hs ↦ Finset.sum_eq_zero fun s' hs' ↦ ?_
    by_cases h : (contractClones r ω S rep).lt s s'
    · rw [orientedCost_of_lt voters h]
      have hω : ω.lt s s' := (contractClones_lt_inside hs hs').mp h
      rw [againstCount, List.countP_eq_zero]
      intro v hv
      simp only [decide_eq_true_eq]
      intro hvs
      exact ranks_asymm hω ((hunan v hv s' hs' s hs).mp hvs)
    · rw [orientedCost_of_not_lt voters h]
  -- the outside block is untouched
  have hOO : ∑ a ∈ Sᶜ, ∑ b ∈ Sᶜ, orientedCost voters (contractClones r ω S rep) a b
      = ∑ a ∈ Sᶜ, ∑ b ∈ Sᶜ, orientedCost voters r a b := by
    refine Finset.sum_congr rfl fun a ha ↦ Finset.sum_congr rfl fun b hb ↦ ?_
    rw [Finset.mem_compl] at ha hb
    exact orientedCost_congr voters (contractClones_lt_outside ha hb)
  -- each member's mixed row becomes the representative's row
  have hM : ∑ s ∈ S, ∑ x ∈ Sᶜ,
        (orientedCost voters (contractClones r ω S rep) s x
          + orientedCost voters (contractClones r ω S rep) x s)
      = ∑ s ∈ S, ∑ x ∈ Sᶜ,
        (orientedCost voters r rep x + orientedCost voters r x rep) := by
    refine Finset.sum_congr rfl fun s hs ↦ Finset.sum_congr rfl fun x hx ↦ ?_
    rw [Finset.mem_compl] at hx
    by_cases h : r.lt rep x
    · have h1 : (contractClones r ω S rep).lt s x := (contractClones_lt_left hrep hs hx).mpr h
      have h2 : ¬(contractClones r ω S rep).lt x s :=
        fun hcon ↦ ranks_asymm h ((contractClones_lt_right hrep hs hx).mp hcon)
      have h3 : ¬r.lt x rep := ranks_asymm h
      rw [orientedCost_of_lt voters h1, orientedCost_of_not_lt voters h2,
        orientedCost_of_lt voters h, orientedCost_of_not_lt voters h3,
        hagainst₁ s hs x hx]
    · have hrx : r.lt x rep := ranks_of_not_ranks (fun he ↦ hx (he ▸ hrep)) h
      have h1 : (contractClones r ω S rep).lt x s := (contractClones_lt_right hrep hs hx).mpr hrx
      have h2 : ¬(contractClones r ω S rep).lt s x :=
        fun hcon ↦ ranks_asymm hrx ((contractClones_lt_left hrep hs hx).mp hcon)
      rw [orientedCost_of_not_lt voters h2, orientedCost_of_lt voters h1,
        orientedCost_of_not_lt voters h, orientedCost_of_lt voters hrx,
        hagainst₂ s hs x hx]
  -- the representative's row is cheapest, summed over the members
  have hle : ∑ s ∈ S, ∑ x ∈ Sᶜ, (orientedCost voters r rep x + orientedCost voters r x rep)
      ≤ ∑ s ∈ S, ∑ x ∈ Sᶜ, (orientedCost voters r s x + orientedCost voters r x s) :=
    Finset.sum_le_sum fun s hs ↦ hmin s hs
  rw [kemenyCost_eq_sum_orientedCost voters (contractClones r ω S rep),
    kemenyCost_eq_sum_orientedCost voters r, sum_sum_split S, sum_sum_split S]
  omega

/-- **The existence form** — the statement the reduction iterates: for a
nonempty clone set there is a representative whose contraction does not
increase the cost. The representative is a `sideCost` minimizer, produced by
`Finset.exists_min_image`. -/
theorem exists_contract_le (r : LinearOrder A) (hne : S.Nonempty)
    (hclone : ∀ v ∈ voters, ∀ s ∈ S, ∀ s' ∈ S, ∀ x, x ∉ S → (v.lt s x ↔ v.lt s' x))
    (hunan : ∀ v ∈ voters, ∀ s ∈ S, ∀ s' ∈ S, (v.lt s s' ↔ ω.lt s s')) :
    ∃ rep ∈ S,
      kemenyCost voters (contractClones r ω S rep) ≤ kemenyCost voters r := by
  obtain ⟨rep, hrep, hmin⟩ := S.exists_min_image (sideCost voters r S) hne
  exact ⟨rep, hrep,
    kemenyCost_contractClones_le hrep
      (fun v hv s hs x hx ↦ hclone v hv s hs rep hrep x hx) hunan hmin⟩

end CostTheorem

end Hardness
