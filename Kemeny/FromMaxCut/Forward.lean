import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Kemeny.FromMaxCut.Scan
import Kemeny.FromMaxCut.Verdicts

/-!
# The forward direction: a cheap ranking from a cut

Given a colouring `χ : Fin n → Bool` of the vertices (`true` = the left part
`L`), the paper's Section 4.1 output ranking, built as one more `VoterSpec`:
gadgets ascending, gadget `i` ordered `ABCDEF` if `i ∈ L` and `DAEBFC` if
`i ∈ R`, and the two candidates of each edge placed by the four-case table —

| `χ i` | `χ j` | `ℓ_e`           | `r_e`           |
|-------|-------|-----------------|-----------------|
| L     | L     | after `A_i`     | after `B_i`     |
| L     | R     | after `A_i`     | after `D_j`     |
| R     | L     | after `E_j`     | after `F_i`     |
| R     | R     | after `A_i`     | after `F_i`     |

Because the output is a spec, injectivity and the four comparison laws of
`VoterSpec` apply to it unchanged; the work of this file is to *bound the
margin cost* of `(outSpec n G χ).ranking M` category by category, matching
the table's cost column. The blocks (`3nM²` exactly for vertex–vertex,
`M(6·span e + 2 + [e uncut])` per edge for vertex–edge both ways, at most
`pairSlack` between edge candidates) assemble into the additive master bound
`marginCost_out_add_cut_le` and the forward direction proper,
`exists_marginCost_le_marginBudget`: a cut of size `k` yields a ranking
within the margin budget.

What the three voters say about a pair is not recomputed here: the counts come
from the shared verdict engine (`Verdicts.lean`) — `beats` for two letters of a
gadget, `edgeVerdict` and its seven region rows for a vertex–edge pair — and the
interval bookkeeping from `Scan.lean`. The reverse direction reads the same
lemmas, so the two directions agree by construction rather than by coincidence.
-/

namespace Hardness

/-- The left-side local order `ABCDEF`. -/
def outPosL : Letter → ℕ
  | .A => 0 | .B => 1 | .C => 2 | .D => 3 | .E => 4 | .F => 5

/-- The right-side local order `DAEBFC`. -/
def outPosR : Letter → ℕ
  | .D => 0 | .A => 1 | .E => 2 | .B => 3 | .F => 4 | .C => 5

theorem outPosL_inj : Function.Injective outPosL := by
  intro x y h
  cases x <;> cases y <;> simp_all [outPosL]

theorem outPosR_inj : Function.Injective outPosR := by
  intro x y h
  cases x <;> cases y <;> simp_all [outPosR]

variable (n : ℕ) (G : SimpleGraph (Fin n))

/-- The output ranking of the forward direction, as a spec: gadgets
ascending, local order by the side of the cut, edge candidates per the
placement table. -/
def outSpec (χ : Fin n → Bool) : VoterSpec n G where
  gadgetPos := Fin.val
  gadgetPos_inj := Fin.val_injective
  localPos := fun i ↦ if χ i then outPosL else outPosR
  localPos_inj := fun i ↦ by
    split
    · exact outPosL_inj
    · exact outPosR_inj
  edgeGadget := fun e s ↦
    match s with
    | .left => if !χ e.i && χ e.j then e.j else e.i
    | .right => if χ e.i && !χ e.j then e.j else e.i
  gapLetter := fun e s ↦
    match s with
    | .left => if !χ e.i && χ e.j then Letter.E else Letter.A
    | .right =>
        if χ e.i then (if χ e.j then Letter.B else Letter.D) else Letter.F

variable {n G}

section CostVV

open Finset

variable {M : ℕ}

/-! ## The vertex–vertex block

Pointwise values first: within a supercandidate the margin cost is `0`
(natural order is unanimous, reversed order is unranked); on a same-gadget
letter pair it is the wrong-arc value of the side's local order; across two
gadgets it is `0` (the output's ascending order agrees with the 2-of-3
majority, and the reversed orientation is unranked). Then the sums: each
gadget contributes exactly `3M²`, the off-diagonal contributes nothing. -/

/-- Members of one supercandidate cost nothing in the output ranking. -/
theorem orientedMargin_out_same_letter (χ : Fin n → Bool) (u : Fin n)
    (x : Letter) (m m' : Fin M) :
    orientedMargin (kemenyProfile n G M) ((outSpec n G χ).ranking M)
      (Sum.inl (u, x, m)) (Sum.inl (u, x, m')) = 0 := by
  by_cases h : m < m'
  · rw [orientedMargin_of_lt _ (ranking_lt_same_super _ h),
      againstCount_profile_same_super h]
    omega
  · refine orientedMargin_of_not_lt _ fun hcon ↦ ?_
    rw [VoterSpec.lt_vertex_vertex] at hcon
    simp only [outSpec, Fin.lt_def] at hcon
    simp only [Fin.lt_def] at h
    omega

/-- The margin cost of a same-gadget letter pair in the output ranking: the
wrong-arc value of the side's local order, uniformly in the member
indices. -/
theorem orientedMargin_out_letters (χ : Fin n → Bool) (u : Fin n)
    {x x' : Letter} (hne : x ≠ x') (m m' : Fin M) :
    orientedMargin (kemenyProfile n G M) ((outSpec n G χ).ranking M)
      (Sum.inl (u, x, m)) (Sum.inl (u, x', m'))
      = if (if χ u then outPosL else outPosR) x < (if χ u then outPosL else outPosR) x'
          then beats x' x - beats x x' else 0 := by
  by_cases h : (if χ u then outPosL else outPosR) x < (if χ u then outPosL else outPosR) x'
  · have hlt : ((outSpec n G χ).ranking M).lt
        (Sum.inl (u, x, m)) (Sum.inl (u, x', m')) :=
      (VoterSpec.lt_vertex_vertex _).mpr (Or.inr ⟨rfl, Or.inl h⟩)
    rw [if_pos h, orientedMargin_of_lt _ hlt, againstCount_profile_letters hne,
      againstCount_profile_letters hne.symm]
  · rw [if_neg h]
    refine orientedMargin_of_not_lt _ fun hcon ↦ ?_
    rw [VoterSpec.lt_vertex_vertex] at hcon
    rcases hcon with hc | ⟨-, hc | ⟨hc, -⟩⟩
    · exact absurd hc (lt_irrefl _)
    · exact h hc
    · exact hne ((outSpec n G χ).localPos_inj u hc)

/-- **Each side's local order is wrong on exactly three unit arcs**: summing
the wrong-arc values over all ordered letter pairs gives `3`, for either
side. The `decide` that replaces the paper's triangle-packing analysis of
the forward direction. -/
theorem sum_out_letter_cost (b : Bool) :
    ∑ x : Letter, ∑ x' : Letter,
      (if (if b then outPosL else outPosR) x < (if b then outPosL else outPosR) x'
        then beats x' x - beats x x' else 0) = 3 := by
  cases b <;> decide

/-- **The diagonal**: one gadget of the output ranking costs exactly `3M²`
margin units. -/
theorem sum_orientedMargin_out_diag (χ : Fin n → Bool) (u : Fin n) :
    ∑ x : Letter, ∑ m : Fin M, ∑ x' : Letter, ∑ m' : Fin M,
      orientedMargin (kemenyProfile n G M) ((outSpec n G χ).ranking M)
        (Sum.inl (u, x, m)) (Sum.inl (u, x', m')) = 3 * M ^ 2 := by
  rw [Finset.sum_congr rfl fun x (_ : x ∈ univ) ↦
    (Finset.sum_comm :
      (∑ m : Fin M, ∑ x' : Letter, ∑ m' : Fin M,
        orientedMargin (kemenyProfile n G M) ((outSpec n G χ).ranking M)
          (Sum.inl (u, x, m)) (Sum.inl (u, x', m'))) = _)]
  have hinner : ∀ x x' : Letter,
      (∑ m : Fin M, ∑ m' : Fin M,
        orientedMargin (kemenyProfile n G M) ((outSpec n G χ).ranking M)
          (Sum.inl (u, x, m)) (Sum.inl (u, x', m')))
      = M ^ 2 * (if (if χ u then outPosL else outPosR) x
            < (if χ u then outPosL else outPosR) x'
          then beats x' x - beats x x' else 0) := by
    intro x x'
    by_cases hxx : x = x'
    · subst hxx
      rw [if_neg (lt_irrefl _), mul_zero]
      exact Finset.sum_eq_zero fun m _ ↦ Finset.sum_eq_zero fun m' _ ↦
        orientedMargin_out_same_letter χ u x m m'
    · rw [Finset.sum_congr rfl fun m (_ : m ∈ univ) ↦
        Finset.sum_congr rfl fun m' (_ : m' ∈ univ) ↦
          orientedMargin_out_letters χ u hxx m m']
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      ring
  rw [Finset.sum_congr rfl fun x (_ : x ∈ univ) ↦
    Finset.sum_congr rfl fun x' (_ : x' ∈ univ) ↦ hinner x x']
  simp only [← Finset.mul_sum]
  rw [sum_out_letter_cost (χ u)]
  ring

/-- **The off-diagonal**: a pair of vertex candidates from two different
gadgets costs nothing — ascending agrees with the 2-of-3 majority, and the
descending orientation is unranked. -/
theorem orientedMargin_out_offdiag (χ : Fin n → Bool) {u u' : Fin n}
    (hne : u ≠ u') (x x' : Letter) (m m' : Fin M) :
    orientedMargin (kemenyProfile n G M) ((outSpec n G χ).ranking M)
      (Sum.inl (u, x, m)) (Sum.inl (u', x', m')) = 0 := by
  have hb := u.isLt
  have hb' := u'.isLt
  rcases Nat.lt_or_ge u.val u'.val with hlt | hge
  · have hout : ((outSpec n G χ).ranking M).lt
        (Sum.inl (u, x, m)) (Sum.inl (u', x', m')) :=
      (VoterSpec.lt_vertex_vertex _).mpr (Or.inl hlt)
    have h1 : ((spec1 n G).ranking M).lt
        (Sum.inl (u, x, m)) (Sum.inl (u', x', m')) :=
      (VoterSpec.lt_vertex_vertex _).mpr (Or.inl hlt)
    have h3 : ((spec3 n G).ranking M).lt
        (Sum.inl (u, x, m)) (Sum.inl (u', x', m')) :=
      (VoterSpec.lt_vertex_vertex _).mpr (Or.inl hlt)
    have h2 : ((spec2 n G).ranking M).lt
        (Sum.inl (u', x', m')) (Sum.inl (u, x, m)) :=
      (VoterSpec.lt_vertex_vertex _).mpr (Or.inl (by simp only [spec2]; omega))
    rw [orientedMargin_of_lt _ hout, againstCount_profile_eq,
      againstCount_profile_eq, againstCount_singleton_of_lt h1,
      againstCount_singleton_of_gt h2, againstCount_singleton_of_lt h3,
      againstCount_singleton_of_gt h1, againstCount_singleton_of_lt h2,
      againstCount_singleton_of_gt h3]
  · refine orientedMargin_of_not_lt _ fun hcon ↦ ?_
    rw [VoterSpec.lt_vertex_vertex] at hcon
    rcases hcon with hc | ⟨hc, -⟩
    · simp only [outSpec] at hc
      omega
    · refine hne (Fin.ext ?_)
      simpa only [outSpec] using hc

/-- **The vertex–vertex block**: the output ranking's total margin cost
against vertex-candidate pairs is exactly `3nM²`. -/
theorem sum_orientedMargin_out_vv (χ : Fin n → Bool) :
    ∑ u : Fin n, ∑ x : Letter, ∑ m : Fin M,
      ∑ u' : Fin n, ∑ x' : Letter, ∑ m' : Fin M,
        orientedMargin (kemenyProfile n G M) ((outSpec n G χ).ranking M)
          (Sum.inl (u, x, m)) (Sum.inl (u', x', m')) = 3 * n * M ^ 2 := by
  have hper : ∀ (u : Fin n) (x : Letter) (m : Fin M),
      (∑ u' : Fin n, ∑ x' : Letter, ∑ m' : Fin M,
        orientedMargin (kemenyProfile n G M) ((outSpec n G χ).ranking M)
          (Sum.inl (u, x, m)) (Sum.inl (u', x', m')))
      = ∑ x' : Letter, ∑ m' : Fin M,
          orientedMargin (kemenyProfile n G M) ((outSpec n G χ).ranking M)
            (Sum.inl (u, x, m)) (Sum.inl (u, x', m')) := by
    intro u x m
    refine Finset.sum_eq_single u (fun u' _ hne ↦ ?_)
      (fun h ↦ absurd (Finset.mem_univ u) h)
    exact Finset.sum_eq_zero fun x' _ ↦ Finset.sum_eq_zero fun m' _ ↦
      orientedMargin_out_offdiag χ (Ne.symm hne) x x' m m'
  rw [Finset.sum_congr rfl fun u (_ : u ∈ univ) ↦
    Finset.sum_congr rfl fun x (_ : x ∈ univ) ↦
      Finset.sum_congr rfl fun m (_ : m ∈ univ) ↦ hper u x m]
  rw [Finset.sum_congr rfl fun u (_ : u ∈ univ) ↦ sum_orientedMargin_out_diag χ u]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  ring

end CostVV

section CostVE

open Finset

variable {M : ℕ}

/-! ## The vertex–edge and edge–vertex blocks

Both orientations of a vertex–edge pair are handled together: the pair's
two-way margin cost is `verdict − 1` if the output ranks the vertex candidate
above the edge candidate and `2 − verdict` otherwise
(`orientedMargin_ve_add_swap`). The verdict depends on the vertex candidate
only through its gadget `u` and letter `x`, never the member index — so each
`(u, x)` contributes its verdict `M`-fold, and per edge candidate the block is
`M` times a scan over `u`, piecewise constant on the seven ranges cut by the
edge's endpoints and midpoint (`sum_fin_scan`).

Each of the six placement cases is therefore seven rows over the six letters,
and only *one* of the seven is a real computation: the edge candidate's own
gadget, where the placement table decides letter by letter. The other six lie
wholly above or wholly below it (`sum_row_above`, `sum_row_below`), so their
rows are the region verdicts of `Verdicts.lean` summed with no case analysis at
all. -/

/-! ### The two shapes of letter row

Outside the gadget the edge candidate itself sits in, the output ranks a whole
gadget on one side of it, so its letter row is the verdict row with no case
analysis: `verdict − 1` per letter above, `2 − verdict` per letter below. Only
the edge candidate's own gadget splits, and only there does a row see the
placement table. -/

/-- A gadget the output ranks entirely *above* the edge candidate. -/
private theorem sum_row_above (W : VoterSpec n G) (e : EdgePair n G) (s : Side)
    {u : Fin n} (hlt : W.gadgetPos u < W.gadgetPos (W.edgeGadget e s)) :
    ∑ x : Letter, (if W.gadgetPos u < W.gadgetPos (W.edgeGadget e s)
          ∨ (W.gadgetPos u = W.gadgetPos (W.edgeGadget e s)
            ∧ W.localPos u x ≤ W.localPos (W.edgeGadget e s) (W.gapLetter e s))
        then edgeVerdict e s u x - 1 else 2 - edgeVerdict e s u x)
      = ∑ x : Letter, (edgeVerdict e s u x - 1) :=
  Finset.sum_congr rfl fun _ _ ↦ if_pos (Or.inl hlt)

/-- A gadget the output ranks entirely *below* the edge candidate. -/
private theorem sum_row_below (W : VoterSpec n G) (e : EdgePair n G) (s : Side)
    {u : Fin n} (hgt : W.gadgetPos (W.edgeGadget e s) < W.gadgetPos u) :
    ∑ x : Letter, (if W.gadgetPos u < W.gadgetPos (W.edgeGadget e s)
          ∨ (W.gadgetPos u = W.gadgetPos (W.edgeGadget e s)
            ∧ W.localPos u x ≤ W.localPos (W.edgeGadget e s) (W.gapLetter e s))
        then edgeVerdict e s u x - 1 else 2 - edgeVerdict e s u x)
      = ∑ x : Letter, (2 - edgeVerdict e s u x) :=
  Finset.sum_congr rfl fun _ _ ↦ if_neg (by rintro (h | ⟨h, -⟩) <;> omega)

/-- **The `ℓ_e` scan**: against all vertex candidates, the left edge
candidate costs exactly `M(3·span e + 2)` margin units in the output
ranking — plus `M` more when both endpoints are on the right (the `R,R` row
of the placement table, where `ℓ_e` sits after `A_i` in a right gadget and
`D_i` slips between). -/
private theorem sum_orientedMargin_out_ve_left (hsp : SpreadEdges n G)
    (χ : Fin n → Bool) (e : EdgePair n G) :
    ∑ u : Fin n, ∑ x : Letter, ∑ m : Fin M,
      (orientedMargin (kemenyProfile n G M) ((outSpec n G χ).ranking M)
          (Sum.inl (u, x, m)) (Sum.inr (e, Side.left))
        + orientedMargin (kemenyProfile n G M) ((outSpec n G χ).ranking M)
          (Sum.inr (e, Side.left)) (Sum.inl (u, x, m)))
      = M * (3 * e.span + 2 + (if χ e.i || χ e.j then 0 else 1)) := by
  obtain ⟨hiq, hqj, hmid⟩ := hsp e
  have hij := e.i_lt_j
  have hbq := e.mid.isLt
  have hbj := e.j.isLt
  simp only [orientedMargin_ve_add_swap hsp (outSpec n G χ), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, ← Finset.mul_sum]
  cases hb1 : χ e.i
  · cases hb2 : χ e.j
    · -- `R,R`: `ℓ_e` after `A_i` in the right gadget order `DAEBFC`
      have hgad : (outSpec n G χ).edgeGadget e Side.left = e.i := by simp [outSpec, hb1, hb2]
      simp only [Bool.false_or, Bool.false_eq_true, if_false]
      congr 1
      refine (sum_fin_scan 1 0 3 6 5 hiq hqj hbj ?_ ?_ ?_ ?_ ?_ ?_ ?_).trans ?_
      · intro u hu
        rw [sum_row_above _ e Side.left (by rw [hgad]; exact hu)]
        simp only [edgeVerdict_before_i hsp hu]
        decide
      · intro u hu
        obtain rfl : u = e.i := Fin.ext hu
        simp only [edgeVerdict_at_i_left hsp, outSpec, hb1, hb2, Bool.not_false,
          Bool.and_false, Bool.false_eq_true, if_false, lt_self_iff_false, false_or,
          true_and, outPosR]
        decide
      · intro u hu1 hu2
        rw [sum_row_below _ e Side.left (by rw [hgad]; exact hu1)]
        simp only [edgeVerdict_mid1 hsp hu1 hu2]
        decide
      · intro u hu
        obtain rfl : u = e.mid := Fin.ext hu
        rw [sum_row_below _ e Side.left (by rw [hgad]; exact hiq)]
        simp only [edgeVerdict_at_q hsp]
        decide
      · intro u hu1 hu2
        rw [sum_row_below _ e Side.left (by rw [hgad]; exact (show e.i.val < u.val by omega))]
        simp only [edgeVerdict_mid2 hsp hu1 hu2]
        decide
      · intro u hu
        obtain rfl : u = e.j := Fin.ext hu
        rw [sum_row_below _ e Side.left (by rw [hgad]; exact hij)]
        simp only [edgeVerdict_at_j_left hsp]
        decide
      · intro u hu
        rw [sum_row_below _ e Side.left (by rw [hgad]; exact (show e.i.val < u.val by omega))]
        simp only [edgeVerdict_after_j hsp hu]
        decide
      · rw [EdgePair.span_def]
        omega
    · -- `R,L`: `ℓ_e` after `E_j` in the left gadget order `ABCDEF`
      have hgad : (outSpec n G χ).edgeGadget e Side.left = e.j := by simp [outSpec, hb1, hb2]
      simp only [Bool.false_or, if_true]
      congr 1
      refine (sum_fin_scan 5 6 3 0 0 hiq hqj hbj ?_ ?_ ?_ ?_ ?_ ?_ ?_).trans ?_
      · intro u hu
        rw [sum_row_above _ e Side.left (by rw [hgad]; exact (show u.val < e.j.val by omega))]
        simp only [edgeVerdict_before_i hsp hu]
        decide
      · intro u hu
        obtain rfl : u = e.i := Fin.ext hu
        rw [sum_row_above _ e Side.left (by rw [hgad]; exact hij)]
        simp only [edgeVerdict_at_i_left hsp]
        decide
      · intro u hu1 hu2
        rw [sum_row_above _ e Side.left (by rw [hgad]; exact (show u.val < e.j.val by omega))]
        simp only [edgeVerdict_mid1 hsp hu1 hu2]
        decide
      · intro u hu
        obtain rfl : u = e.mid := Fin.ext hu
        rw [sum_row_above _ e Side.left (by rw [hgad]; exact hqj)]
        simp only [edgeVerdict_at_q hsp]
        decide
      · intro u hu1 hu2
        rw [sum_row_above _ e Side.left (by rw [hgad]; exact hu2)]
        simp only [edgeVerdict_mid2 hsp hu1 hu2]
        decide
      · intro u hu
        obtain rfl : u = e.j := Fin.ext hu
        simp only [edgeVerdict_at_j_left hsp, outSpec, hb1, hb2, Bool.not_false,
          Bool.and_true, if_true, lt_self_iff_false, false_or, true_and, outPosL]
        decide
      · intro u hu
        rw [sum_row_below _ e Side.left (by rw [hgad]; exact hu)]
        simp only [edgeVerdict_after_j hsp hu]
        decide
      · rw [EdgePair.span_def]
        omega
  · -- `χ e.i = true`: `ℓ_e` after `A_i` in the left gadget order, for either
    -- side of `e.j` — the two rows coincide
    have hgad : (outSpec n G χ).edgeGadget e Side.left = e.i := by simp [outSpec, hb1]
    simp only [Bool.true_or, if_true]
    congr 1
    refine (sum_fin_scan 0 0 3 6 5 hiq hqj hbj ?_ ?_ ?_ ?_ ?_ ?_ ?_).trans ?_
    · intro u hu
      rw [sum_row_above _ e Side.left (by rw [hgad]; exact hu)]
      simp only [edgeVerdict_before_i hsp hu]
      decide
    · intro u hu
      obtain rfl : u = e.i := Fin.ext hu
      simp only [edgeVerdict_at_i_left hsp, outSpec, hb1, Bool.not_true, Bool.false_and,
        Bool.false_eq_true, if_false, if_true, lt_self_iff_false, false_or, true_and,
        outPosL]
      decide
    · intro u hu1 hu2
      rw [sum_row_below _ e Side.left (by rw [hgad]; exact hu1)]
      simp only [edgeVerdict_mid1 hsp hu1 hu2]
      decide
    · intro u hu
      obtain rfl : u = e.mid := Fin.ext hu
      rw [sum_row_below _ e Side.left (by rw [hgad]; exact hiq)]
      simp only [edgeVerdict_at_q hsp]
      decide
    · intro u hu1 hu2
      rw [sum_row_below _ e Side.left (by rw [hgad]; exact (show e.i.val < u.val by omega))]
      simp only [edgeVerdict_mid2 hsp hu1 hu2]
      decide
    · intro u hu
      obtain rfl : u = e.j := Fin.ext hu
      rw [sum_row_below _ e Side.left (by rw [hgad]; exact hij)]
      simp only [edgeVerdict_at_j_left hsp]
      decide
    · intro u hu
      rw [sum_row_below _ e Side.left (by rw [hgad]; exact (show e.i.val < u.val by omega))]
      simp only [edgeVerdict_after_j hsp hu]
      decide
    · rw [EdgePair.span_def]
      omega

/-- **The `r_e` scan**: against all vertex candidates, the right edge
candidate costs exactly `M·3·span e` margin units in the output ranking —
plus `M` more when both endpoints are on the left (the `L,L` row, where
`r_e` sits after `B_i` in a left gadget and `E_i`, `F_i` slip between). -/
private theorem sum_orientedMargin_out_ve_right (hsp : SpreadEdges n G)
    (χ : Fin n → Bool) (e : EdgePair n G) :
    ∑ u : Fin n, ∑ x : Letter, ∑ m : Fin M,
      (orientedMargin (kemenyProfile n G M) ((outSpec n G χ).ranking M)
          (Sum.inl (u, x, m)) (Sum.inr (e, Side.right))
        + orientedMargin (kemenyProfile n G M) ((outSpec n G χ).ranking M)
          (Sum.inr (e, Side.right)) (Sum.inl (u, x, m)))
      = M * (3 * e.span + (if χ e.i && χ e.j then 1 else 0)) := by
  obtain ⟨hiq, hqj, hmid⟩ := hsp e
  have hij := e.i_lt_j
  have hbq := e.mid.isLt
  have hbj := e.j.isLt
  simp only [orientedMargin_ve_add_swap hsp (outSpec n G χ), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, ← Finset.mul_sum]
  cases hb1 : χ e.i
  · -- `χ e.i = false`: `r_e` after `F_i` in the right gadget order, for
    -- either side of `e.j` — the two rows coincide
    have hgad : (outSpec n G χ).edgeGadget e Side.right = e.i := by simp [outSpec, hb1]
    simp only [Bool.false_and, Bool.false_eq_true, if_false]
    congr 1
    refine (sum_fin_scan 1 0 3 6 2 hiq hqj hbj ?_ ?_ ?_ ?_ ?_ ?_ ?_).trans ?_
    · intro u hu
      rw [sum_row_above _ e Side.right (by rw [hgad]; exact hu)]
      simp only [edgeVerdict_before_i hsp hu]
      decide
    · intro u hu
      obtain rfl : u = e.i := Fin.ext hu
      simp only [edgeVerdict_at_i_right hsp, outSpec, hb1, Bool.false_and,
        Bool.false_eq_true, if_false, lt_self_iff_false, false_or, true_and, outPosR]
      decide
    · intro u hu1 hu2
      rw [sum_row_below _ e Side.right (by rw [hgad]; exact hu1)]
      simp only [edgeVerdict_mid1 hsp hu1 hu2]
      decide
    · intro u hu
      obtain rfl : u = e.mid := Fin.ext hu
      rw [sum_row_below _ e Side.right (by rw [hgad]; exact hiq)]
      simp only [edgeVerdict_at_q hsp]
      decide
    · intro u hu1 hu2
      rw [sum_row_below _ e Side.right (by rw [hgad]; exact (show e.i.val < u.val by omega))]
      simp only [edgeVerdict_mid2 hsp hu1 hu2]
      decide
    · intro u hu
      obtain rfl : u = e.j := Fin.ext hu
      rw [sum_row_below _ e Side.right (by rw [hgad]; exact hij)]
      simp only [edgeVerdict_at_j_right hsp]
      decide
    · intro u hu
      rw [sum_row_below _ e Side.right (by rw [hgad]; exact (show e.i.val < u.val by omega))]
      simp only [edgeVerdict_after_j hsp hu]
      decide
    · rw [EdgePair.span_def]
      omega
  · cases hb2 : χ e.j
    · -- `L,R`: `r_e` after `D_j` in the right gadget order `DAEBFC`
      have hgad : (outSpec n G χ).edgeGadget e Side.right = e.j := by simp [outSpec, hb1, hb2]
      simp only [Bool.true_and, Bool.false_eq_true, if_false]
      congr 1
      refine (sum_fin_scan 2 6 3 0 1 hiq hqj hbj ?_ ?_ ?_ ?_ ?_ ?_ ?_).trans ?_
      · intro u hu
        rw [sum_row_above _ e Side.right (by rw [hgad]; exact (show u.val < e.j.val by omega))]
        simp only [edgeVerdict_before_i hsp hu]
        decide
      · intro u hu
        obtain rfl : u = e.i := Fin.ext hu
        rw [sum_row_above _ e Side.right (by rw [hgad]; exact hij)]
        simp only [edgeVerdict_at_i_right hsp]
        decide
      · intro u hu1 hu2
        rw [sum_row_above _ e Side.right (by rw [hgad]; exact (show u.val < e.j.val by omega))]
        simp only [edgeVerdict_mid1 hsp hu1 hu2]
        decide
      · intro u hu
        obtain rfl : u = e.mid := Fin.ext hu
        rw [sum_row_above _ e Side.right (by rw [hgad]; exact hqj)]
        simp only [edgeVerdict_at_q hsp]
        decide
      · intro u hu1 hu2
        rw [sum_row_above _ e Side.right (by rw [hgad]; exact hu2)]
        simp only [edgeVerdict_mid2 hsp hu1 hu2]
        decide
      · intro u hu
        obtain rfl : u = e.j := Fin.ext hu
        simp only [edgeVerdict_at_j_right hsp, outSpec, hb1, hb2, Bool.not_false,
          Bool.and_true, if_true, Bool.false_eq_true, if_false, lt_self_iff_false,
          false_or, true_and, outPosR]
        decide
      · intro u hu
        rw [sum_row_below _ e Side.right (by rw [hgad]; exact hu)]
        simp only [edgeVerdict_after_j hsp hu]
        decide
      · rw [EdgePair.span_def]
        omega
    · -- `L,L`: `r_e` after `B_i` in the left gadget order `ABCDEF`
      have hgad : (outSpec n G χ).edgeGadget e Side.right = e.i := by simp [outSpec, hb1, hb2]
      simp only [Bool.true_and, if_true]
      congr 1
      refine (sum_fin_scan 2 0 3 6 2 hiq hqj hbj ?_ ?_ ?_ ?_ ?_ ?_ ?_).trans ?_
      · intro u hu
        rw [sum_row_above _ e Side.right (by rw [hgad]; exact hu)]
        simp only [edgeVerdict_before_i hsp hu]
        decide
      · intro u hu
        obtain rfl : u = e.i := Fin.ext hu
        simp only [edgeVerdict_at_i_right hsp, outSpec, hb1, hb2, Bool.not_true,
          Bool.and_false, Bool.false_eq_true, if_false, if_true, lt_self_iff_false,
          false_or, true_and, outPosL]
        decide
      · intro u hu1 hu2
        rw [sum_row_below _ e Side.right (by rw [hgad]; exact hu1)]
        simp only [edgeVerdict_mid1 hsp hu1 hu2]
        decide
      · intro u hu
        obtain rfl : u = e.mid := Fin.ext hu
        rw [sum_row_below _ e Side.right (by rw [hgad]; exact hiq)]
        simp only [edgeVerdict_at_q hsp]
        decide
      · intro u hu1 hu2
        rw [sum_row_below _ e Side.right (by rw [hgad]; exact (show e.i.val < u.val by omega))]
        simp only [edgeVerdict_mid2 hsp hu1 hu2]
        decide
      · intro u hu
        obtain rfl : u = e.j := Fin.ext hu
        rw [sum_row_below _ e Side.right (by rw [hgad]; exact hij)]
        simp only [edgeVerdict_at_j_right hsp]
        decide
      · intro u hu
        rw [sum_row_below _ e Side.right (by rw [hgad]; exact (show e.i.val < u.val by omega))]
        simp only [edgeVerdict_after_j hsp hu]
        decide
      · rw [EdgePair.span_def]
        omega

/-- **The vertex–edge and edge–vertex blocks, per edge**: both candidates of
an edge together cost `M(6·span e + 2)` margin units against all vertex
candidates — plus `M` exactly when the edge is *uncut*. Summed over the
edges this is `M·(edgeBound − cutsize)`, the edge term of the budget. -/
theorem sum_orientedMargin_out_ve (hsp : SpreadEdges n G) (χ : Fin n → Bool)
    (e : EdgePair n G) :
    ∑ s : Side, ∑ u : Fin n, ∑ x : Letter, ∑ m : Fin M,
      (orientedMargin (kemenyProfile n G M) ((outSpec n G χ).ranking M)
          (Sum.inl (u, x, m)) (Sum.inr (e, s))
        + orientedMargin (kemenyProfile n G M) ((outSpec n G χ).ranking M)
          (Sum.inr (e, s)) (Sum.inl (u, x, m)))
      = M * (6 * e.span + 2 + (if χ e.i = χ e.j then 1 else 0)) := by
  rw [show (Finset.univ : Finset Side) = {Side.left, Side.right} from by decide,
    Finset.sum_insert (by decide), Finset.sum_singleton,
    sum_orientedMargin_out_ve_left hsp χ e, sum_orientedMargin_out_ve_right hsp χ e,
    ← mul_add]
  congr 1
  cases hb1 : χ e.i <;> cases hb2 : χ e.j <;>
    simp only [Bool.true_or, Bool.false_or, Bool.true_and, Bool.false_and,
      Bool.false_eq_true, Bool.true_eq_false, if_true, if_false] <;>
    omega

end CostVE

section CostEE

open Finset

variable {M : ℕ}

/-! ## The edge–edge block

No exact accounting here: any ordered pair of edge candidates costs at most
`1` margin unit — outside supercandidates all margins are ±1, so a ranked
pair pays at most `2 − 1` — and the crude square `pairSlack` absorbs the
whole block, one unit per ordered pair including the diagonal. -/

/-- Any ordered pair of edge candidates costs at most `1` margin unit in the
output ranking. -/
private theorem orientedMargin_out_ee_le (hsp : SpreadEdges n G)
    (χ : Fin n → Bool) (p p' : EdgePair n G × Side) :
    orientedMargin (kemenyProfile n G M) ((outSpec n G χ).ranking M)
      (Sum.inr p) (Sum.inr p') ≤ 1 := by
  by_cases hlt : ((outSpec n G χ).ranking M).lt (Sum.inr p) (Sum.inr p')
  · have hne : (Sum.inr p : Cand n M G) ≠ Sum.inr p' := ranks_ne hlt
    have hns : ¬SameSuper (Sum.inr p : Cand n M G) (Sum.inr p') := by
      rintro ⟨i, y, m1, m2, hc, -⟩
      exact Sum.inr_ne_inl hc
    have hlow := one_le_againstCount_profile (M := M) hsp hne.symm
      fun hc ↦ hns hc.symm
    have hhigh := againstCount_profile_le_two (M := M) hsp hne hns
    rw [orientedMargin_of_lt _ hlt]
    omega
  · rw [orientedMargin_of_not_lt _ hlt]
    omega

/-- **The edge–edge block**: at most `pairSlack` in total — one margin unit
per ordered pair of edge candidates. -/
private theorem sum_orientedMargin_out_ee_le [DecidableRel G.Adj]
    (hsp : SpreadEdges n G) (χ : Fin n → Bool) :
    ∑ p : EdgePair n G × Side, ∑ p' : EdgePair n G × Side,
      orientedMargin (kemenyProfile n G M) ((outSpec n G χ).ranking M)
        (Sum.inr p) (Sum.inr p') ≤ pairSlack n G := by
  calc ∑ p : EdgePair n G × Side, ∑ p' : EdgePair n G × Side,
      orientedMargin (kemenyProfile n G M) ((outSpec n G χ).ranking M)
        (Sum.inr p) (Sum.inr p')
      ≤ ∑ _p : EdgePair n G × Side, ∑ _p' : EdgePair n G × Side, 1 :=
        Finset.sum_le_sum fun p _ ↦ Finset.sum_le_sum fun p' _ ↦
          orientedMargin_out_ee_le hsp χ p p'
    _ = pairSlack n G := by
        simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one,
          Fintype.card_prod]
        rw [pairSlack, show Fintype.card Side = 2 from rfl]
        ring

end CostEE

section CostTotal

open Finset

variable {M : ℕ}

/-! ## The master bound, and the forward direction

`marginCost_eq_sum_orientedMargin` writes the margin cost as a sum over the
ordered square of `Cand = VC ⊕ EC`; `Fintype.sum_sum_type` splits it into the
four blocks computed above. Stated additively — `marginCost + M·cutSize ≤ …`
— so the ℕ-subtraction of `marginBudget` never enters the block accounting;
it is discharged once, in `exists_marginCost_le_marginBudget`. -/

/-- **The master cost bound of the output ranking**: `3nM²` for the
vertex–vertex block, `M·edgeBound − M·cutSize` for the vertex–edge blocks
(via the per-edge exact value), `pairSlack` for the edge–edge block. -/
theorem marginCost_out_add_cut_le [DecidableRel G.Adj] (hsp : SpreadEdges n G)
    (χ : Fin n → Bool) :
    marginCost (kemenyProfile n G M) ((outSpec n G χ).ranking M)
        + M * cutSize G χ
      ≤ 3 * n * M ^ 2 + M * edgeBound n G + pairSlack n G := by
  rw [marginCost_eq_sum_orientedMargin]
  simp only [Fintype.sum_sum_type, Finset.sum_add_distrib]
  have hvv : ∑ a : Fin n × Letter × Fin M, ∑ a' : Fin n × Letter × Fin M,
      orientedMargin (kemenyProfile n G M) ((outSpec n G χ).ranking M)
        (Sum.inl a) (Sum.inl a') = 3 * n * M ^ 2 := by
    simp only [Fintype.sum_prod_type]
    exact sum_orientedMargin_out_vv χ
  have hveev : (∑ a : Fin n × Letter × Fin M, ∑ p : EdgePair n G × Side,
        orientedMargin (kemenyProfile n G M) ((outSpec n G χ).ranking M)
          (Sum.inl a) (Sum.inr p))
      + (∑ p : EdgePair n G × Side, ∑ a : Fin n × Letter × Fin M,
        orientedMargin (kemenyProfile n G M) ((outSpec n G χ).ranking M)
          (Sum.inr p) (Sum.inl a))
      + M * cutSize G χ = M * edgeBound n G := by
    rw [show (∑ a : Fin n × Letter × Fin M, ∑ p : EdgePair n G × Side,
          orientedMargin (kemenyProfile n G M) ((outSpec n G χ).ranking M)
            (Sum.inl a) (Sum.inr p))
        = ∑ p : EdgePair n G × Side, ∑ a : Fin n × Letter × Fin M,
          orientedMargin (kemenyProfile n G M) ((outSpec n G χ).ranking M)
            (Sum.inl a) (Sum.inr p) from Finset.sum_comm]
    simp only [← Finset.sum_add_distrib]
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_congr rfl fun e (_ : e ∈ univ) ↦
      sum_orientedMargin_out_ve hsp χ e]
    rw [cutSize_eq_sum_edgePair n G χ, edgeBound, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ ↦ ?_
    by_cases h : χ e.i = χ e.j
    · rw [if_pos h, if_pos h]
      ring
    · rw [if_neg h, if_neg h]
      ring
  have hee : ∑ p : EdgePair n G × Side, ∑ p' : EdgePair n G × Side,
      orientedMargin (kemenyProfile n G M) ((outSpec n G χ).ranking M)
        (Sum.inr p) (Sum.inr p') ≤ pairSlack n G :=
    sum_orientedMargin_out_ee_le hsp χ
  linarith [hvv, hveev, hee]

/-- **The forward direction**: a colouring cutting at least `x.k` edges
yields a ranking — the output ranking of the colouring — within the margin
budget. The truncated subtraction in `marginBudget` is harmless: the additive
master bound plus `M·k ≤ M·cutSize` is exactly what `Nat.le_sub_of_add_le`
needs. -/
theorem exists_marginCost_le_marginBudget (x : NumberedGraphInstance)
    (hsp : SpreadEdges x.n x.G) {χ : Fin x.n → Bool}
    (hcut : x.k ≤ cutSize x.G χ) :
    ∃ r : LinearOrder (Cand x.n (bigM x.n) x.G),
      marginCost (kemenyProfile x.n x.G (bigM x.n)) r ≤ marginBudget x := by
  refine ⟨(outSpec x.n x.G χ).ranking (bigM x.n), ?_⟩
  rw [marginBudget]
  refine Nat.le_sub_of_add_le ?_
  calc marginCost (kemenyProfile x.n x.G (bigM x.n))
        ((outSpec x.n x.G χ).ranking (bigM x.n)) + bigM x.n * x.k
      ≤ marginCost (kemenyProfile x.n x.G (bigM x.n))
          ((outSpec x.n x.G χ).ranking (bigM x.n))
        + bigM x.n * cutSize x.G χ :=
        Nat.add_le_add_left (Nat.mul_le_mul_left _ hcut) _
    _ ≤ 3 * x.n * bigM x.n ^ 2 + bigM x.n * edgeBound x.n x.G
        + pairSlack x.n x.G := marginCost_out_add_cut_le hsp χ

end CostTotal

end Hardness
