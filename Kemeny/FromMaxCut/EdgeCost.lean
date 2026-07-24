import Kemeny.FromMaxCut.Reverse

/-!
# The edge-candidate cost engine

Third step of the reverse direction: the machinery for lower-bounding what an
edge candidate costs against the vertex candidates in an *arbitrary* ranking
— the reverse counterpart of the forward direction's exact scans, which knew
where the edge candidates sit.

For any ranking, the two-way margin cost of a vertex–edge pair is the
disagreement indicator against the 2-of-3 majority
(`orientedMargin_ve_add_swap_gen`, the margins-±1 facts again). The majority
verdict depends on the vertex candidate only through its gadget and letter —
never the member index — and is recorded as the closed function
`edgeVerdict` (`againstCount_profile_ve`), with values in `{1, 2}` under
`SpreadEdges`. Summing over one supercandidate, the cost is a linear
interpolation governed by a single number: how many of the `M` members sit
above the edge candidate (`aboveCount`, `sum_ve_pair_cost_super`). The
walk analysis over these interpolations is the next file's work.
-/

namespace Hardness

open Finset

variable {n M : ℕ} {G : SimpleGraph (Fin n)}

/-! ## The majority verdict of a vertex–edge pair -/

/-- One voter's verdict on a vertex–edge pair, as a closed count: `0` if the
spec ranks the vertex candidate above the edge candidate, else `1`. The
member index does not appear. -/
def specMiss (V : VoterSpec n G) (e : EdgePair n G) (s : Side) (u : Fin n)
    (x : Letter) : ℕ :=
  if V.gadgetPos u < V.gadgetPos (V.edgeGadget e s)
      ∨ (V.gadgetPos u = V.gadgetPos (V.edgeGadget e s)
        ∧ V.localPos u x ≤ V.localPos (V.edgeGadget e s) (V.gapLetter e s))
  then 0 else 1

/-- The profile count against ranking the vertex candidate above the edge
candidate, as a closed function of gadget and letter alone. -/
def edgeVerdict (e : EdgePair n G) (s : Side) (u : Fin n) (x : Letter) : ℕ :=
  specMiss (spec1 n G) e s u x + specMiss (spec2 n G) e s u x
    + specMiss (spec3 n G) e s u x

/-- The profile count on a vertex–edge pair is the closed verdict — for every
member index. -/
theorem againstCount_profile_ve (e : EdgePair n G) (s : Side) (u : Fin n)
    (x : Letter) (m : Fin M) :
    againstCount (kemenyProfile n G M) (Sum.inl (u, x, m)) (Sum.inr (e, s))
      = edgeVerdict e s u x := by
  rw [againstCount_profile_eq, againstCount_singleton_ve (spec1 n G) e s u x m,
    againstCount_singleton_ve (spec2 n G) e s u x m,
    againstCount_singleton_ve (spec3 n G) e s u x m,
    edgeVerdict, specMiss, specMiss, specMiss]

/-- The verdicts are the ±1 margins of the profile: at least one voter on
each side. Needs a member to exist, and spread edges. -/
theorem edgeVerdict_bounds (hsp : SpreadEdges n G) (hM : 0 < M)
    (e : EdgePair n G) (s : Side) (u : Fin n) (x : Letter) :
    1 ≤ edgeVerdict e s u x ∧ edgeVerdict e s u x ≤ 2 := by
  have m₀ : Fin M := ⟨0, hM⟩
  have hne : (Sum.inl (u, x, m₀) : Cand n M G) ≠ Sum.inr (e, s) := Sum.inl_ne_inr
  have hns : ¬SameSuper (Sum.inl (u, x, m₀) : Cand n M G) (Sum.inr (e, s)) := by
    rintro ⟨i, y, m1, m2, -, hc⟩
    exact Sum.inr_ne_inl hc
  have h1 := one_le_againstCount_profile (M := M) hsp hne hns
  have h2 := againstCount_profile_le_two (M := M) hsp hne hns
  rw [againstCount_profile_ve] at h1 h2
  exact ⟨h1, h2⟩

/-! ## The two-way pair cost, for an arbitrary ranking -/

/-- **The two-way margin cost of a vertex–edge pair**, in any ranking:
`verdict − 1` when the vertex candidate is ranked above the edge candidate,
`2 − verdict` otherwise — the disagreement indicator against the 2-of-3
majority. The reverse counterpart of the forward direction's spec-bound
version. -/
theorem orientedMargin_ve_add_swap_gen (hsp : SpreadEdges n G)
    (r : LinearOrder (Cand n M G)) (e : EdgePair n G) (s : Side) (u : Fin n)
    (x : Letter) (m : Fin M) :
    orientedMargin (kemenyProfile n G M) r (Sum.inl (u, x, m)) (Sum.inr (e, s))
      + orientedMargin (kemenyProfile n G M) r (Sum.inr (e, s)) (Sum.inl (u, x, m))
      = if r.lt (Sum.inl (u, x, m)) (Sum.inr (e, s))
        then edgeVerdict e s u x - 1
        else 2 - edgeVerdict e s u x := by
  have hne : (Sum.inl (u, x, m) : Cand n M G) ≠ Sum.inr (e, s) := Sum.inl_ne_inr
  have hns : ¬SameSuper (Sum.inl (u, x, m) : Cand n M G) (Sum.inr (e, s)) := by
    rintro ⟨i, y, m1, m2, -, hc⟩
    exact Sum.inr_ne_inl hc
  have hns' : ¬SameSuper (Sum.inr (e, s) : Cand n M G) (Sum.inl (u, x, m)) := by
    rintro ⟨i, y, m1, m2, hc, -⟩
    exact Sum.inr_ne_inl hc
  have hlow := one_le_againstCount_profile (M := M) hsp hne hns
  have hlow' := one_le_againstCount_profile (M := M) hsp hne.symm hns'
  have hsum := againstCount_add_againstCount (kemenyProfile n G M) hne
  rw [kemenyProfile_length] at hsum
  rw [againstCount_profile_ve] at hlow hsum
  by_cases h : r.lt (Sum.inl (u, x, m)) (Sum.inr (e, s))
  · rw [if_pos h, orientedMargin_of_lt _ h,
      orientedMargin_of_not_lt _ (ranks_asymm h), againstCount_profile_ve]
    omega
  · have hlt : r.lt (Sum.inr (e, s)) (Sum.inl (u, x, m)) :=
      ranks_of_not_ranks hne h
    rw [if_neg h, orientedMargin_of_not_lt _ (ranks_asymm hlt),
      orientedMargin_of_lt _ hlt, againstCount_profile_ve]
    omega

/-! ## Summing over one supercandidate -/

/-- How many members of the supercandidate `(u, x)` are ranked above the edge
candidate `(e, s)` — the single number governing the supercandidate's cost
against it. -/
def aboveCount (r : LinearOrder (Cand n M G)) (e : EdgePair n G) (s : Side)
    (u : Fin n) (x : Letter) : ℕ :=
  letI := r.toDecidableLT
  (Finset.univ.filter fun m : Fin M ↦
    r.lt (Sum.inl (u, x, m)) (Sum.inr (e, s))).card

theorem aboveCount_le (r : LinearOrder (Cand n M G)) (e : EdgePair n G)
    (s : Side) (u : Fin n) (x : Letter) : aboveCount r e s u x ≤ M := by
  rw [aboveCount]
  calc (Finset.univ.filter fun m : Fin M ↦
        letI := r.toDecidableLT
        r.lt (Sum.inl (u, x, m)) (Sum.inr (e, s))).card
      ≤ (Finset.univ : Finset (Fin M)).card := Finset.card_filter_le _ _
    _ = M := by rw [Finset.card_univ, Fintype.card_fin]

/-- **One supercandidate's cost against an edge candidate**: a linear
interpolation in the number of members above it — `verdict − 1` per member
above, `2 − verdict` per member below. -/
theorem sum_ve_pair_cost_super (hsp : SpreadEdges n G)
    (r : LinearOrder (Cand n M G)) (e : EdgePair n G) (s : Side) (u : Fin n)
    (x : Letter) :
    ∑ m : Fin M,
      (orientedMargin (kemenyProfile n G M) r (Sum.inl (u, x, m)) (Sum.inr (e, s))
        + orientedMargin (kemenyProfile n G M) r (Sum.inr (e, s)) (Sum.inl (u, x, m)))
      = aboveCount r e s u x * (edgeVerdict e s u x - 1)
        + (M - aboveCount r e s u x) * (2 - edgeVerdict e s u x) := by
  letI := r.toDecidableLT
  rw [Finset.sum_congr rfl fun m (_ : m ∈ Finset.univ) ↦
    orientedMargin_ve_add_swap_gen hsp r e s u x m]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun m : Fin M ↦ r.lt (Sum.inl (u, x, m)) (Sum.inr (e, s)))]
  have h1 : ∑ m ∈ Finset.univ.filter (fun m : Fin M ↦
        r.lt (Sum.inl (u, x, m)) (Sum.inr (e, s))),
      (if r.lt (Sum.inl (u, x, m)) (Sum.inr (e, s))
        then edgeVerdict e s u x - 1 else 2 - edgeVerdict e s u x)
      = aboveCount r e s u x * (edgeVerdict e s u x - 1) := by
    rw [Finset.sum_congr rfl fun m hm ↦
      if_pos (Finset.mem_filter.mp hm).2]
    rw [Finset.sum_const, smul_eq_mul, aboveCount]
  have h2 : ∑ m ∈ Finset.univ.filter (fun m : Fin M ↦
        ¬r.lt (Sum.inl (u, x, m)) (Sum.inr (e, s))),
      (if r.lt (Sum.inl (u, x, m)) (Sum.inr (e, s))
        then edgeVerdict e s u x - 1 else 2 - edgeVerdict e s u x)
      = (M - aboveCount r e s u x) * (2 - edgeVerdict e s u x) := by
    rw [Finset.sum_congr rfl fun m hm ↦
      if_neg (Finset.mem_filter.mp hm).2]
    rw [Finset.sum_const, smul_eq_mul]
    congr 1
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin M)))
      (p := fun m : Fin M ↦ r.lt (Sum.inl (u, x, m)) (Sum.inr (e, s)))
    rw [Finset.card_univ, Fintype.card_fin] at hsplit
    rw [aboveCount]
    omega
  rw [h1, h2]

end Hardness
