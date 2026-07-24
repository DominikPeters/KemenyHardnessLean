import Kemeny.FromMaxCut.Reverse

/-!
# The edge-candidate cost engine

Third step of the reverse direction: the machinery for lower-bounding what an
edge candidate costs against the vertex candidates in an *arbitrary* ranking
— the reverse counterpart of the forward direction's exact scans, which knew
where the edge candidates sit.

The pair cost itself is already available for any ranking, from the shared
verdict engine (`Verdicts.lean`): `orientedMargin_ve_add_swap_gen` charges
`verdict − 1` above and `2 − verdict` below, with `edgeVerdict` a closed
function of the gadget and letter alone. What this file adds is the sum over
one supercandidate, which is then a linear interpolation governed by a single
number: how many of the `M` members sit above the edge candidate (`aboveCount`,
`sum_ve_pair_cost_super`). The walk analysis over these interpolations is the
next file's work.
-/

namespace Hardness

open Finset

variable {n M : ℕ} {G : SimpleGraph (Fin n)}

/-! ## Summing over one supercandidate -/

/-- How many members of the supercandidate `(u, x)` are ranked above the edge
candidate `(e, s)` — the single number governing the supercandidate's cost
against it. -/
def aboveCount (r : LinearOrder (Cand n M G)) (e : EdgePair n G) (s : Side)
    (u : Fin n) (x : Letter) : ℕ :=
  letI := r.toDecidableLT
  (Finset.univ.filter fun m : Fin M ↦
    r.lt (Sum.inl (u, x, m)) (Sum.inr (e, s))).card

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
