import KemenyHardness.KemenyScore

/-!
# Relabeling equivariance of the Kemeny objective

The Kemeny objective does not see the names of the alternatives: relabeling all
alternatives by a bijection `e : A ≃ B`, applied uniformly to every voter and to
the output ranking, leaves every Kendall tau distance — and hence the whole
Kemeny cost — unchanged.

This is the workhorse that lets the certificate's adequacy proof compare a
decoded instance (whose alternatives are `Fin N`, the positions of the candidate
list) with the construction's instance (whose alternatives are the structured
`Cand n M G`): the two are related by the numbering bijection, and
`kemenyScore_relabel` turns the numbering into an `iff` of YES-instances.

The pushforward of a ranking along `e` is `mapOrder e`: it ranks `e a` above
`e b` exactly when the original ranks `a` above `b`. It is realized as
`LinearOrder.lift'` pulling the order back along `e.symm`, and is a genuine
bijection on rankings with inverse `mapOrder e.symm` (`mapOrder_symm_mapOrder`).
-/

namespace Hardness

open Finset

variable {A B : Type*}

/-! ## Pushing a ranking along a bijection -/

/-- Pushforward of a ranking along a bijection of alternatives: `mapOrder e r`
ranks `x` above `y` exactly when `r` ranks `e.symm x` above `e.symm y` — so
`e a` sits above `e b` under `mapOrder e r` iff `a` sits above `b` under `r`.
Realized by pulling `r` back along `e.symm`. -/
@[reducible] def mapOrder (e : A ≃ B) (r : LinearOrder A) : LinearOrder B :=
  letI := r
  LinearOrder.lift' e.symm e.symm.injective

@[simp] theorem mapOrder_le (e : A ≃ B) (r : LinearOrder A) (x y : B) :
    (mapOrder e r).le x y ↔ r.le (e.symm x) (e.symm y) := Iff.rfl

@[simp] theorem mapOrder_lt (e : A ≃ B) (r : LinearOrder A) (x y : B) :
    (mapOrder e r).lt x y ↔ r.lt (e.symm x) (e.symm y) := Iff.rfl

/-- `mapOrder e r` ranks `e a` above `e b` exactly when `r` ranks `a` above `b`
— the pushforward property in the orientation the adequacy proof reads. -/
theorem mapOrder_apply_lt (e : A ≃ B) (r : LinearOrder A) (a b : A) :
    (mapOrder e r).lt (e a) (e b) ↔ r.lt a b := by
  simp

/-- Pushing forward by `e` and then by `e.symm` is the identity on rankings:
`mapOrder e` is a bijection with inverse `mapOrder e.symm`. -/
@[simp] theorem mapOrder_symm_mapOrder (e : A ≃ B) (r : LinearOrder A) :
    mapOrder e.symm (mapOrder e r) = r :=
  LinearOrder.ext fun a b ↦ by simp

@[simp] theorem mapOrder_mapOrder_symm (e : A ≃ B) (s : LinearOrder B) :
    mapOrder e (mapOrder e.symm s) = s := by
  simpa using mapOrder_symm_mapOrder e.symm s

/-! ## Invariance of the distances -/

variable [Fintype A] [Fintype B]

/-- The discordant pairs of two pushed rankings are the image, under the
bijection applied componentwise, of the discordant pairs of the originals. -/
theorem discordantPairs_mapOrder [DecidableEq B] (e : A ≃ B) (r s : LinearOrder A) :
    discordantPairs (mapOrder e r) (mapOrder e s)
      = (discordantPairs r s).image (Prod.map e e) := by
  ext p
  rw [mem_discordantPairs, mem_image]
  constructor
  · intro h
    refine ⟨(e.symm p.1, e.symm p.2), ?_, ?_⟩
    · rw [mem_discordantPairs]
      simpa using h
    · simp [Prod.map]
  · rintro ⟨q, hq, rfl⟩
    rw [mem_discordantPairs] at hq
    simpa [Prod.map] using hq

/-- **Kendall tau is relabeling-invariant**: pushing both rankings along the
same bijection leaves their distance unchanged. -/
theorem kendallTau_mapOrder (e : A ≃ B) (r s : LinearOrder A) :
    kendallTau (mapOrder e r) (mapOrder e s) = kendallTau r s := by
  classical
  rw [kendallTau, kendallTau, discordantPairs_mapOrder,
    card_image_of_injective _ (e.injective.prodMap e.injective)]

/-- **The Kemeny cost is relabeling-invariant**: pushing every voter and the
output ranking along the same bijection leaves the total cost unchanged. -/
theorem kemenyCost_mapOrder (e : A ≃ B) (voters : List (LinearOrder A))
    (r : LinearOrder A) :
    kemenyCost (voters.map (mapOrder e)) (mapOrder e r) = kemenyCost voters r := by
  rw [kemenyCost, kemenyCost, List.map_map]
  refine congrArg List.sum (List.map_congr_left fun v _ ↦ ?_)
  exact kendallTau_mapOrder e v r

/-! ## Relabeling an instance -/

/-- Relabel every alternative of a KEMENY SCORE instance by a bijection,
applying the pushforward to every voter and keeping the budget. -/
def KemenyInstance.relabel (x : KemenyInstance) {B : Type} [Fintype B]
    [DecidableEq B] (e : x.A ≃ B) : KemenyInstance where
  A := B
  voters := x.voters.map (mapOrder e)
  b := x.b

/-- **Relabeling equivariance of KEMENY SCORE**: a bijection of alternatives
carries YES-instances to YES-instances in both directions. The pushforward of an
in-budget ranking is in budget, and vice versa via the inverse bijection. -/
theorem kemenyScore_relabel (x : KemenyInstance) {B : Type} [Fintype B]
    [DecidableEq B] (e : x.A ≃ B) :
    KEMENY_SCORE x ↔ KEMENY_SCORE (x.relabel e) := by
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨mapOrder e r, ?_⟩
    change kemenyCost (x.voters.map (mapOrder e)) (mapOrder e r) ≤ x.b
    rw [kemenyCost_mapOrder]; exact hr
  · rintro ⟨s, hs⟩
    replace hs : kemenyCost (x.voters.map (mapOrder e)) s ≤ x.b := hs
    refine ⟨mapOrder e.symm s, ?_⟩
    rw [← kemenyCost_mapOrder e x.voters (mapOrder e.symm s), mapOrder_mapOrder_symm]
    exact hs

end Hardness
