import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Kemeny.FromMaxCut.Margins

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

/-! ## Evaluating `againstCount` of the profile

The profile has three voters, so every count is a sum of three one-voter
verdicts (`againstCount_profile_eq`); each verdict is decided by the voter's
comparison law. For two letters within one gadget, the count is the
computable within-gadget tournament `beats`. -/

/-- The profile count, voter by voter. -/
theorem againstCount_profile_eq (c c' : Cand n M G) :
    againstCount (kemenyProfile n G M) c c' =
      againstCount [(spec1 n G).ranking M] c c'
        + againstCount [(spec2 n G).ranking M] c c'
        + againstCount [(spec3 n G).ranking M] c c' := by
  rw [kemenyProfile, againstCount_cons ((spec1 n G).ranking M) _ c c',
    againstCount_cons ((spec2 n G).ranking M) _ c c']
  omega

/-- How many of the three voters rank letter `x` above letter `y` within a
gadget: the within-gadget tournament, as a computable count. All fifteen
majority arcs of the paper's gadget figure are `beats x y = 2` facts. -/
def beats (x y : Letter) : ℕ :=
  (if pos1 x < pos1 y then 1 else 0) + (if pos2 x < pos2 y then 1 else 0)
    + (if pos3 x < pos3 y then 1 else 0)

/-- One voter's verdict on a same-gadget letter pair is its local-position
comparison. -/
theorem againstCount_singleton_letters (V : VoterSpec n G) {u : Fin n}
    {x x' : Letter} {m m' : Fin M} (hne : V.localPos u x ≠ V.localPos u x') :
    againstCount [V.ranking M] (Sum.inl (u, x, m)) (Sum.inl (u, x', m'))
      = if V.localPos u x' < V.localPos u x then 1 else 0 := by
  by_cases h : V.localPos u x' < V.localPos u x
  · rw [if_pos h]
    exact againstCount_singleton_of_gt
      ((VoterSpec.lt_vertex_vertex V).mpr (Or.inr ⟨rfl, Or.inl h⟩))
  · rw [if_neg h]
    exact againstCount_singleton_of_lt
      ((VoterSpec.lt_vertex_vertex V).mpr (Or.inr ⟨rfl, Or.inl (by omega)⟩))

/-- The profile's count on a same-gadget letter pair is the tournament
count — the same in every gadget. -/
theorem againstCount_profile_letters {u : Fin n} {x x' : Letter} {m m' : Fin M}
    (hne : x ≠ x') :
    againstCount (kemenyProfile n G M) (Sum.inl (u, x, m)) (Sum.inl (u, x', m'))
      = beats x' x := by
  rw [againstCount_profile_eq,
    againstCount_singleton_letters (spec1 n G) (fun h ↦ hne (pos1_inj h)),
    againstCount_singleton_letters (spec2 n G) (fun h ↦ hne (pos2_inj h)),
    againstCount_singleton_letters (spec3 n G) (fun h ↦ hne (pos3_inj h))]
  simp only [spec1, spec2, spec3, beats]
  rfl

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
two-way margin cost is `cnt − 1` if the output ranks the vertex candidate
above the edge candidate and `2 − cnt` otherwise, where `cnt ∈ {1, 2}` is the
profile count against the vertex-above-edge order (`orientedMargin_ve_add_swap`
— the margins-±1 facts in the exact form the block computation sums). The
verdicts of the three voters and of the output depend on the vertex candidate
only through its gadget `u` and letter `x`, never the member index — so each
`(u, x)` contributes its verdict `M`-fold, and per edge candidate the block is
`M` times a scan over `u`, piecewise constant on the seven ranges cut by the
edge's endpoints and midpoint (`sum_fin_scan`). On each range the letter count
is a `decide`. -/

/-- One voter's verdict on a vertex–edge pair, as the comparison of the
voter's positions: cost `0` exactly if the voter ranks the vertex candidate
above the edge candidate. -/
private theorem againstCount_singleton_ve (V : VoterSpec n G) (e : EdgePair n G)
    (s : Side) (u : Fin n) (x : Letter) (m : Fin M) :
    againstCount [V.ranking M] (Sum.inl (u, x, m)) (Sum.inr (e, s))
      = if V.gadgetPos u < V.gadgetPos (V.edgeGadget e s)
            ∨ (V.gadgetPos u = V.gadgetPos (V.edgeGadget e s)
              ∧ V.localPos u x ≤ V.localPos (V.edgeGadget e s) (V.gapLetter e s))
        then 0 else 1 := by
  by_cases h : V.gadgetPos u < V.gadgetPos (V.edgeGadget e s)
      ∨ (V.gadgetPos u = V.gadgetPos (V.edgeGadget e s)
        ∧ V.localPos u x ≤ V.localPos (V.edgeGadget e s) (V.gapLetter e s))
  · rw [if_pos h]
    exact againstCount_singleton_of_lt ((VoterSpec.lt_vertex_edge V).mpr h)
  · rw [if_neg h]
    exact againstCount_singleton_of_gt (ranks_of_not_ranks Sum.inl_ne_inr
      fun hc ↦ h ((VoterSpec.lt_vertex_edge V).mp hc))

/-- **The two-way margin cost of a vertex–edge pair**: `cnt − 1` when the
output spec ranks the vertex candidate above the edge candidate, `2 − cnt`
otherwise, `cnt` the profile count against vertex-above-edge. Both values are
the disagreement indicator between the output and the 2-of-3 majority, by the
margins-±1 facts. -/
private theorem orientedMargin_ve_add_swap (hsp : SpreadEdges n G)
    (W : VoterSpec n G) (e : EdgePair n G) (s : Side) (u : Fin n) (x : Letter)
    (m : Fin M) :
    orientedMargin (kemenyProfile n G M) (W.ranking M)
        (Sum.inl (u, x, m)) (Sum.inr (e, s))
      + orientedMargin (kemenyProfile n G M) (W.ranking M)
        (Sum.inr (e, s)) (Sum.inl (u, x, m))
      = if W.gadgetPos u < W.gadgetPos (W.edgeGadget e s)
            ∨ (W.gadgetPos u = W.gadgetPos (W.edgeGadget e s)
              ∧ W.localPos u x ≤ W.localPos (W.edgeGadget e s) (W.gapLetter e s))
        then againstCount (kemenyProfile n G M) (Sum.inl (u, x, m)) (Sum.inr (e, s)) - 1
        else 2 - againstCount (kemenyProfile n G M) (Sum.inl (u, x, m)) (Sum.inr (e, s)) := by
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
  by_cases h : W.gadgetPos u < W.gadgetPos (W.edgeGadget e s)
      ∨ (W.gadgetPos u = W.gadgetPos (W.edgeGadget e s)
        ∧ W.localPos u x ≤ W.localPos (W.edgeGadget e s) (W.gapLetter e s))
  · have hlt := (VoterSpec.lt_vertex_edge W (M := M) (m := m)).mpr h
    rw [if_pos h, orientedMargin_of_lt _ hlt,
      orientedMargin_of_not_lt _ (ranks_asymm hlt)]
    omega
  · have hlt : (W.ranking M).lt (Sum.inr (e, s)) (Sum.inl (u, x, m)) :=
      ranks_of_not_ranks hne fun hc ↦ h ((VoterSpec.lt_vertex_edge W).mp hc)
    rw [if_neg h, orientedMargin_of_not_lt _ (ranks_asymm hlt),
      orientedMargin_of_lt _ hlt]
    omega

/-- **The seven-range scan**: a function on `Fin n` that vanishes before `iv`
and after `jv` and is constant on the five remaining pieces sums to the
telescoped value. The interval bookkeeping of the vertex–edge block, once and
for all. -/
private theorem sum_fin_scan {f : Fin n → ℕ} {iv qv jv : ℕ}
    (a b c d g : ℕ) (hiq : iv < qv) (hqj : qv < jv) (hjn : jv < n)
    (h0 : ∀ u : Fin n, u.val < iv → f u = 0)
    (hI : ∀ u : Fin n, u.val = iv → f u = a)
    (h1 : ∀ u : Fin n, iv < u.val → u.val < qv → f u = b)
    (hQ : ∀ u : Fin n, u.val = qv → f u = c)
    (h2 : ∀ u : Fin n, qv < u.val → u.val < jv → f u = d)
    (hJ : ∀ u : Fin n, u.val = jv → f u = g)
    (h3 : ∀ u : Fin n, jv < u.val → f u = 0) :
    ∑ u : Fin n, f u = a + (qv - iv - 1) * b + c + (jv - qv - 1) * d + g := by
  set F : ℕ → ℕ := fun uv ↦ if h : uv < n then f ⟨uv, h⟩ else 0 with hF
  have hval : ∀ (uv : ℕ) (h : uv < n), F uv = f ⟨uv, h⟩ := by
    intro uv h
    rw [hF]
    exact dif_pos h
  have e0 : ∑ uv ∈ Finset.Ico 0 iv, F uv = 0 :=
    Finset.sum_eq_zero fun uv huv ↦ by
      rw [Finset.mem_Ico] at huv
      rw [hval uv (by omega)]
      exact h0 _ huv.2
  have eI : ∑ uv ∈ Finset.Ico iv (iv + 1), F uv = a := by
    rw [Nat.Ico_succ_singleton, Finset.sum_singleton, hval iv (by omega)]
    exact hI _ rfl
  have e1 : ∑ uv ∈ Finset.Ico (iv + 1) qv, F uv = (qv - (iv + 1)) * b := by
    have hpt : ∀ uv ∈ Finset.Ico (iv + 1) qv, F uv = b := by
      intro uv huv
      rw [Finset.mem_Ico] at huv
      rw [hval uv (by omega)]
      have hlo : iv < uv := by omega
      exact h1 _ hlo huv.2
    rw [Finset.sum_congr rfl hpt, Finset.sum_const, Nat.card_Ico, smul_eq_mul]
  have eQ : ∑ uv ∈ Finset.Ico qv (qv + 1), F uv = c := by
    rw [Nat.Ico_succ_singleton, Finset.sum_singleton, hval qv (by omega)]
    exact hQ _ rfl
  have e2 : ∑ uv ∈ Finset.Ico (qv + 1) jv, F uv = (jv - (qv + 1)) * d := by
    have hpt : ∀ uv ∈ Finset.Ico (qv + 1) jv, F uv = d := by
      intro uv huv
      rw [Finset.mem_Ico] at huv
      rw [hval uv (by omega)]
      have hlo : qv < uv := by omega
      exact h2 _ hlo huv.2
    rw [Finset.sum_congr rfl hpt, Finset.sum_const, Nat.card_Ico, smul_eq_mul]
  have eJ : ∑ uv ∈ Finset.Ico jv (jv + 1), F uv = g := by
    rw [Nat.Ico_succ_singleton, Finset.sum_singleton, hval jv hjn]
    exact hJ _ rfl
  have e3 : ∑ uv ∈ Finset.Ico (jv + 1) n, F uv = 0 :=
    Finset.sum_eq_zero fun uv huv ↦ by
      rw [Finset.mem_Ico] at huv
      rw [hval uv huv.2]
      have hlo : jv < uv := by omega
      exact h3 _ hlo
  calc ∑ u : Fin n, f u
      = ∑ u : Fin n, F u.val := Finset.sum_congr rfl fun u _ ↦ (hval u.val u.isLt).symm
    _ = ∑ uv ∈ Finset.range n, F uv := Fin.sum_univ_eq_sum_range F n
    _ = ∑ uv ∈ Finset.Ico 0 n, F uv := by rw [Finset.range_eq_Ico]
    _ = a + (qv - iv - 1) * b + c + (jv - qv - 1) * d + g := by
        rw [← Finset.sum_Ico_consecutive F (Nat.zero_le iv) (by omega : iv ≤ n),
          ← Finset.sum_Ico_consecutive F (by omega : iv ≤ iv + 1) (by omega : iv + 1 ≤ n),
          ← Finset.sum_Ico_consecutive F (by omega : iv + 1 ≤ qv) (by omega : qv ≤ n),
          ← Finset.sum_Ico_consecutive F (by omega : qv ≤ qv + 1) (by omega : qv + 1 ≤ n),
          ← Finset.sum_Ico_consecutive F (by omega : qv + 1 ≤ jv) (by omega : jv ≤ n),
          ← Finset.sum_Ico_consecutive F (by omega : jv ≤ jv + 1) (by omega : jv + 1 ≤ n),
          e0, eI, e1, eQ, e2, eJ, e3,
          show qv - (iv + 1) = qv - iv - 1 from by omega,
          show jv - (qv + 1) = jv - qv - 1 from by omega]
        ring

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
  simp only [orientedMargin_ve_add_swap hsp (outSpec n G χ), againstCount_profile_eq,
    againstCount_singleton_ve (spec1 n G), againstCount_singleton_ve (spec2 n G),
    againstCount_singleton_ve (spec3 n G)]
  simp only [spec1, spec2, spec3, outSpec, pos1, pos2, pos3]
  cases hb1 : χ e.i
  · cases hb2 : χ e.j
    · -- `R,R`: `ℓ_e` after `A_i` in the right gadget order `DAEBFC`
      simp only [hb1, Bool.not_false, Bool.and_false, Bool.false_or,
        Bool.false_eq_true, if_false, outPosR, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, smul_eq_mul, ← Finset.mul_sum]
      congr 1
      refine (sum_fin_scan 1 0 3 6 5 hiq hqj hbj ?_ ?_ ?_ ?_ ?_ ?_ ?_).trans ?_
      · intro u hu
        have hbu := u.isLt
        simp only [eq_true hu,
          eq_false (show ¬(n - 1 - u.val < n - 1 - e.mid.val) from by omega),
          eq_false (show ¬(n - 1 - u.val = n - 1 - e.mid.val) from by omega),
          eq_true (show u.val < e.j.val from by omega),
          true_or, false_or, false_and, if_true, if_false]
        decide
      · intro u hu
        obtain rfl : u = e.i := Fin.ext hu
        simp only [hb1, Bool.false_eq_true, lt_self_iff_false, 
          eq_false (show ¬(n - 1 - e.i.val < n - 1 - e.mid.val) from by omega),
          eq_false (show ¬(n - 1 - e.i.val = n - 1 - e.mid.val) from by omega),
          eq_true hij, true_or, false_or, true_and, false_and, if_true, if_false]
        decide
      · intro u hu1 hu2
        have hbu := u.isLt
        simp only [eq_false (show ¬(u.val < e.i.val) from by omega),
          eq_false (show ¬(u.val = e.i.val) from by omega),
          eq_false (show ¬(n - 1 - u.val < n - 1 - e.mid.val) from by omega),
          eq_false (show ¬(n - 1 - u.val = n - 1 - e.mid.val) from by omega),
          eq_true (show u.val < e.j.val from by omega),
          true_or, false_or, false_and, if_true, if_false]
        decide
      · intro u hu
        obtain rfl : u = e.mid := Fin.ext hu
        simp only [lt_self_iff_false, 
          eq_false (show ¬(e.mid.val < e.i.val) from by omega),
          eq_false (show ¬(e.mid.val = e.i.val) from by omega),
          eq_true hqj, true_or, false_or, true_and, false_and, if_true, if_false]
        decide
      · intro u hu1 hu2
        have hbu := u.isLt
        simp only [eq_false (show ¬(u.val < e.i.val) from by omega),
          eq_false (show ¬(u.val = e.i.val) from by omega),
          eq_true (show n - 1 - u.val < n - 1 - e.mid.val from by omega),
          eq_true hu2, true_or, false_or, false_and, if_true, if_false]
        decide
      · intro u hu
        obtain rfl : u = e.j := Fin.ext hu
        simp only [lt_self_iff_false, 
          eq_false (show ¬(e.j.val < e.i.val) from by omega),
          eq_false (show ¬(e.j.val = e.i.val) from by omega),
          eq_true (show n - 1 - e.j.val < n - 1 - e.mid.val from by omega),
          true_or, false_or, true_and, false_and, if_true, if_false]
        decide
      · intro u hu
        have hbu := u.isLt
        simp only [eq_false (show ¬(u.val < e.i.val) from by omega),
          eq_false (show ¬(u.val = e.i.val) from by omega),
          eq_true (show n - 1 - u.val < n - 1 - e.mid.val from by omega),
          eq_false (show ¬(u.val < e.j.val) from by omega),
          eq_false (show ¬(u.val = e.j.val) from by omega),
          true_or, false_or, false_and, if_true, if_false]
        decide
      · rw [EdgePair.span_def]
        omega
    · -- `R,L`: `ℓ_e` after `E_j` in the left gadget order `ABCDEF`
      simp only [hb2, Bool.not_false, Bool.and_true, 
        Bool.or_true, if_true, outPosL, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, smul_eq_mul, ← Finset.mul_sum]
      congr 1
      refine (sum_fin_scan 5 6 3 0 0 hiq hqj hbj ?_ ?_ ?_ ?_ ?_ ?_ ?_).trans ?_
      · intro u hu
        have hbu := u.isLt
        simp only [eq_true hu,
          eq_false (show ¬(n - 1 - u.val < n - 1 - e.mid.val) from by omega),
          eq_false (show ¬(n - 1 - u.val = n - 1 - e.mid.val) from by omega),
          eq_true (show u.val < e.j.val from by omega),
          true_or, false_or, false_and, if_true, if_false]
        decide
      · intro u hu
        obtain rfl : u = e.i := Fin.ext hu
        simp only [lt_self_iff_false, 
          eq_false (show ¬(n - 1 - e.i.val < n - 1 - e.mid.val) from by omega),
          eq_false (show ¬(n - 1 - e.i.val = n - 1 - e.mid.val) from by omega),
          eq_true hij, true_or, false_or, true_and, false_and, if_true, if_false]
        decide
      · intro u hu1 hu2
        have hbu := u.isLt
        simp only [eq_false (show ¬(u.val < e.i.val) from by omega),
          eq_false (show ¬(u.val = e.i.val) from by omega),
          eq_false (show ¬(n - 1 - u.val < n - 1 - e.mid.val) from by omega),
          eq_false (show ¬(n - 1 - u.val = n - 1 - e.mid.val) from by omega),
          eq_true (show u.val < e.j.val from by omega),
          true_or, false_or, false_and, if_true, if_false]
        decide
      · intro u hu
        obtain rfl : u = e.mid := Fin.ext hu
        simp only [lt_self_iff_false, 
          eq_false (show ¬(e.mid.val < e.i.val) from by omega),
          eq_false (show ¬(e.mid.val = e.i.val) from by omega),
          eq_true hqj, true_or, false_or, true_and, false_and, if_true, if_false]
        decide
      · intro u hu1 hu2
        have hbu := u.isLt
        simp only [eq_false (show ¬(u.val < e.i.val) from by omega),
          eq_false (show ¬(u.val = e.i.val) from by omega),
          eq_true (show n - 1 - u.val < n - 1 - e.mid.val from by omega),
          eq_true hu2, true_or, false_or, false_and, if_true, if_false]
        decide
      · intro u hu
        obtain rfl : u = e.j := Fin.ext hu
        simp only [hb2, lt_self_iff_false, 
          eq_false (show ¬(e.j.val < e.i.val) from by omega),
          eq_false (show ¬(e.j.val = e.i.val) from by omega),
          eq_true (show n - 1 - e.j.val < n - 1 - e.mid.val from by omega),
          true_or, false_or, true_and, false_and, if_true, if_false]
        decide
      · intro u hu
        have hbu := u.isLt
        simp only [eq_false (show ¬(u.val < e.i.val) from by omega),
          eq_false (show ¬(u.val = e.i.val) from by omega),
          eq_true (show n - 1 - u.val < n - 1 - e.mid.val from by omega),
          eq_false (show ¬(u.val < e.j.val) from by omega),
          eq_false (show ¬(u.val = e.j.val) from by omega),
          true_or, false_or, false_and, if_true, if_false]
        decide
      · rw [EdgePair.span_def]
        omega
  · -- `χ e.i = true`: `ℓ_e` after `A_i` in the left gadget order, for either
    -- side of `e.j` — the two rows coincide
    simp only [hb1, Bool.not_true, Bool.false_and, Bool.true_or, Bool.false_eq_true,
      if_true, if_false, outPosL, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, ← Finset.mul_sum]
    congr 1
    refine (sum_fin_scan 0 0 3 6 5 hiq hqj hbj ?_ ?_ ?_ ?_ ?_ ?_ ?_).trans ?_
    · intro u hu
      have hbu := u.isLt
      simp only [eq_true hu,
        eq_false (show ¬(n - 1 - u.val < n - 1 - e.mid.val) from by omega),
        eq_false (show ¬(n - 1 - u.val = n - 1 - e.mid.val) from by omega),
        eq_true (show u.val < e.j.val from by omega),
        true_or, false_or, false_and, if_true, if_false]
      decide
    · intro u hu
      obtain rfl : u = e.i := Fin.ext hu
      simp only [hb1, lt_self_iff_false, 
        eq_false (show ¬(n - 1 - e.i.val < n - 1 - e.mid.val) from by omega),
        eq_false (show ¬(n - 1 - e.i.val = n - 1 - e.mid.val) from by omega),
        eq_true hij, true_or, false_or, true_and, false_and, if_true, if_false]
      decide
    · intro u hu1 hu2
      have hbu := u.isLt
      simp only [eq_false (show ¬(u.val < e.i.val) from by omega),
        eq_false (show ¬(u.val = e.i.val) from by omega),
        eq_false (show ¬(n - 1 - u.val < n - 1 - e.mid.val) from by omega),
        eq_false (show ¬(n - 1 - u.val = n - 1 - e.mid.val) from by omega),
        eq_true (show u.val < e.j.val from by omega),
        true_or, false_or, false_and, if_true, if_false]
      decide
    · intro u hu
      obtain rfl : u = e.mid := Fin.ext hu
      simp only [lt_self_iff_false, 
        eq_false (show ¬(e.mid.val < e.i.val) from by omega),
        eq_false (show ¬(e.mid.val = e.i.val) from by omega),
        eq_true hqj, true_or, false_or, true_and, false_and, if_true, if_false]
      decide
    · intro u hu1 hu2
      have hbu := u.isLt
      simp only [eq_false (show ¬(u.val < e.i.val) from by omega),
        eq_false (show ¬(u.val = e.i.val) from by omega),
        eq_true (show n - 1 - u.val < n - 1 - e.mid.val from by omega),
        eq_true hu2, true_or, false_or, false_and, if_true, if_false]
      decide
    · intro u hu
      obtain rfl : u = e.j := Fin.ext hu
      simp only [lt_self_iff_false, 
        eq_false (show ¬(e.j.val < e.i.val) from by omega),
        eq_false (show ¬(e.j.val = e.i.val) from by omega),
        eq_true (show n - 1 - e.j.val < n - 1 - e.mid.val from by omega),
        true_or, false_or, true_and, false_and, if_true, if_false]
      decide
    · intro u hu
      have hbu := u.isLt
      simp only [eq_false (show ¬(u.val < e.i.val) from by omega),
        eq_false (show ¬(u.val = e.i.val) from by omega),
        eq_true (show n - 1 - u.val < n - 1 - e.mid.val from by omega),
        eq_false (show ¬(u.val < e.j.val) from by omega),
        eq_false (show ¬(u.val = e.j.val) from by omega),
        true_or, false_or, false_and, if_true, if_false]
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
  simp only [orientedMargin_ve_add_swap hsp (outSpec n G χ), againstCount_profile_eq,
    againstCount_singleton_ve (spec1 n G), againstCount_singleton_ve (spec2 n G),
    againstCount_singleton_ve (spec3 n G)]
  simp only [spec1, spec2, spec3, outSpec, pos1, pos2, pos3]
  cases hb1 : χ e.i
  · -- `χ e.i = false`: `r_e` after `F_i` in the right gadget order, for
    -- either side of `e.j` — the two rows coincide
    simp only [hb1, Bool.false_and, Bool.false_eq_true, if_false, outPosR,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
      ← Finset.mul_sum]
    congr 1
    refine (sum_fin_scan 1 0 3 6 2 hiq hqj hbj ?_ ?_ ?_ ?_ ?_ ?_ ?_).trans ?_
    · intro u hu
      have hbu := u.isLt
      simp only [eq_true hu,
        eq_false (show ¬(n - 1 - u.val < n - 1 - e.mid.val) from by omega),
        eq_false (show ¬(n - 1 - u.val = n - 1 - e.mid.val) from by omega),
        eq_true (show u.val < e.j.val from by omega),
        true_or, false_or, false_and, if_true, if_false]
      decide
    · intro u hu
      obtain rfl : u = e.i := Fin.ext hu
      simp only [hb1, Bool.false_eq_true, lt_self_iff_false, 
        eq_false (show ¬(n - 1 - e.i.val < n - 1 - e.mid.val) from by omega),
        eq_false (show ¬(n - 1 - e.i.val = n - 1 - e.mid.val) from by omega),
        eq_true hij, true_or, false_or, true_and, false_and, if_true, if_false]
      decide
    · intro u hu1 hu2
      have hbu := u.isLt
      simp only [eq_false (show ¬(u.val < e.i.val) from by omega),
        eq_false (show ¬(u.val = e.i.val) from by omega),
        eq_false (show ¬(n - 1 - u.val < n - 1 - e.mid.val) from by omega),
        eq_false (show ¬(n - 1 - u.val = n - 1 - e.mid.val) from by omega),
        eq_true (show u.val < e.j.val from by omega),
        true_or, false_or, false_and, if_true, if_false]
      decide
    · intro u hu
      obtain rfl : u = e.mid := Fin.ext hu
      simp only [lt_self_iff_false, 
        eq_false (show ¬(e.mid.val < e.i.val) from by omega),
        eq_false (show ¬(e.mid.val = e.i.val) from by omega),
        eq_true hqj, true_or, false_or, true_and, false_and, if_true, if_false]
      decide
    · intro u hu1 hu2
      have hbu := u.isLt
      simp only [eq_false (show ¬(u.val < e.i.val) from by omega),
        eq_false (show ¬(u.val = e.i.val) from by omega),
        eq_true (show n - 1 - u.val < n - 1 - e.mid.val from by omega),
        eq_true hu2, true_or, false_or, false_and, if_true, if_false]
      decide
    · intro u hu
      obtain rfl : u = e.j := Fin.ext hu
      simp only [lt_self_iff_false, 
        eq_false (show ¬(e.j.val < e.i.val) from by omega),
        eq_false (show ¬(e.j.val = e.i.val) from by omega),
        eq_true (show n - 1 - e.j.val < n - 1 - e.mid.val from by omega),
        true_or, false_or, true_and, false_and, if_true, if_false]
      decide
    · intro u hu
      have hbu := u.isLt
      simp only [eq_false (show ¬(u.val < e.i.val) from by omega),
        eq_false (show ¬(u.val = e.i.val) from by omega),
        eq_true (show n - 1 - u.val < n - 1 - e.mid.val from by omega),
        eq_false (show ¬(u.val < e.j.val) from by omega),
        eq_false (show ¬(u.val = e.j.val) from by omega),
        true_or, false_or, false_and, if_true, if_false]
      decide
    · rw [EdgePair.span_def]
      omega
  · cases hb2 : χ e.j
    · -- `L,R`: `r_e` after `D_j` in the right gadget order `DAEBFC`
      simp only [hb2, Bool.not_false, Bool.true_and, Bool.false_eq_true,
        if_true, if_false, outPosR, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, smul_eq_mul, ← Finset.mul_sum]
      congr 1
      refine (sum_fin_scan 2 6 3 0 1 hiq hqj hbj ?_ ?_ ?_ ?_ ?_ ?_ ?_).trans ?_
      · intro u hu
        have hbu := u.isLt
        simp only [eq_true hu,
          eq_false (show ¬(n - 1 - u.val < n - 1 - e.mid.val) from by omega),
          eq_false (show ¬(n - 1 - u.val = n - 1 - e.mid.val) from by omega),
          eq_true (show u.val < e.j.val from by omega),
          true_or, false_or, false_and, if_true, if_false]
        decide
      · intro u hu
        obtain rfl : u = e.i := Fin.ext hu
        simp only [lt_self_iff_false, 
          eq_false (show ¬(n - 1 - e.i.val < n - 1 - e.mid.val) from by omega),
          eq_false (show ¬(n - 1 - e.i.val = n - 1 - e.mid.val) from by omega),
          eq_true hij, true_or, false_or, true_and, false_and, if_true, if_false]
        decide
      · intro u hu1 hu2
        have hbu := u.isLt
        simp only [eq_false (show ¬(u.val < e.i.val) from by omega),
          eq_false (show ¬(u.val = e.i.val) from by omega),
          eq_false (show ¬(n - 1 - u.val < n - 1 - e.mid.val) from by omega),
          eq_false (show ¬(n - 1 - u.val = n - 1 - e.mid.val) from by omega),
          eq_true (show u.val < e.j.val from by omega),
          true_or, false_or, false_and, if_true, if_false]
        decide
      · intro u hu
        obtain rfl : u = e.mid := Fin.ext hu
        simp only [lt_self_iff_false, 
          eq_false (show ¬(e.mid.val < e.i.val) from by omega),
          eq_false (show ¬(e.mid.val = e.i.val) from by omega),
          eq_true hqj, true_or, false_or, true_and, false_and, if_true, if_false]
        decide
      · intro u hu1 hu2
        have hbu := u.isLt
        simp only [eq_false (show ¬(u.val < e.i.val) from by omega),
          eq_false (show ¬(u.val = e.i.val) from by omega),
          eq_true (show n - 1 - u.val < n - 1 - e.mid.val from by omega),
          eq_true hu2, true_or, false_or, false_and, if_true, if_false]
        decide
      · intro u hu
        obtain rfl : u = e.j := Fin.ext hu
        simp only [hb2, Bool.false_eq_true, lt_self_iff_false, 
          eq_false (show ¬(e.j.val < e.i.val) from by omega),
          eq_false (show ¬(e.j.val = e.i.val) from by omega),
          eq_true (show n - 1 - e.j.val < n - 1 - e.mid.val from by omega),
          true_or, false_or, true_and, false_and, if_true, if_false]
        decide
      · intro u hu
        have hbu := u.isLt
        simp only [eq_false (show ¬(u.val < e.i.val) from by omega),
          eq_false (show ¬(u.val = e.i.val) from by omega),
          eq_true (show n - 1 - u.val < n - 1 - e.mid.val from by omega),
          eq_false (show ¬(u.val < e.j.val) from by omega),
          eq_false (show ¬(u.val = e.j.val) from by omega),
          true_or, false_or, false_and, if_true, if_false]
        decide
      · rw [EdgePair.span_def]
        omega
    · -- `L,L`: `r_e` after `B_i` in the left gadget order `ABCDEF`
      simp only [hb1, Bool.not_true, Bool.true_and, Bool.false_eq_true,
        if_true, if_false, outPosL, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, smul_eq_mul, ← Finset.mul_sum]
      congr 1
      refine (sum_fin_scan 2 0 3 6 2 hiq hqj hbj ?_ ?_ ?_ ?_ ?_ ?_ ?_).trans ?_
      · intro u hu
        have hbu := u.isLt
        simp only [eq_true hu,
          eq_false (show ¬(n - 1 - u.val < n - 1 - e.mid.val) from by omega),
          eq_false (show ¬(n - 1 - u.val = n - 1 - e.mid.val) from by omega),
          eq_true (show u.val < e.j.val from by omega),
          true_or, false_or, false_and, if_true, if_false]
        decide
      · intro u hu
        obtain rfl : u = e.i := Fin.ext hu
        simp only [hb1, lt_self_iff_false, 
          eq_false (show ¬(n - 1 - e.i.val < n - 1 - e.mid.val) from by omega),
          eq_false (show ¬(n - 1 - e.i.val = n - 1 - e.mid.val) from by omega),
          eq_true hij, true_or, false_or, true_and, false_and, if_true, if_false]
        decide
      · intro u hu1 hu2
        have hbu := u.isLt
        simp only [eq_false (show ¬(u.val < e.i.val) from by omega),
          eq_false (show ¬(u.val = e.i.val) from by omega),
          eq_false (show ¬(n - 1 - u.val < n - 1 - e.mid.val) from by omega),
          eq_false (show ¬(n - 1 - u.val = n - 1 - e.mid.val) from by omega),
          eq_true (show u.val < e.j.val from by omega),
          true_or, false_or, false_and, if_true, if_false]
        decide
      · intro u hu
        obtain rfl : u = e.mid := Fin.ext hu
        simp only [lt_self_iff_false, 
          eq_false (show ¬(e.mid.val < e.i.val) from by omega),
          eq_false (show ¬(e.mid.val = e.i.val) from by omega),
          eq_true hqj, true_or, false_or, true_and, false_and, if_true, if_false]
        decide
      · intro u hu1 hu2
        have hbu := u.isLt
        simp only [eq_false (show ¬(u.val < e.i.val) from by omega),
          eq_false (show ¬(u.val = e.i.val) from by omega),
          eq_true (show n - 1 - u.val < n - 1 - e.mid.val from by omega),
          eq_true hu2, true_or, false_or, false_and, if_true, if_false]
        decide
      · intro u hu
        obtain rfl : u = e.j := Fin.ext hu
        simp only [lt_self_iff_false, 
          eq_false (show ¬(e.j.val < e.i.val) from by omega),
          eq_false (show ¬(e.j.val = e.i.val) from by omega),
          eq_true (show n - 1 - e.j.val < n - 1 - e.mid.val from by omega),
          true_or, false_or, true_and, false_and, if_true, if_false]
        decide
      · intro u hu
        have hbu := u.isLt
        simp only [eq_false (show ¬(u.val < e.i.val) from by omega),
          eq_false (show ¬(u.val = e.i.val) from by omega),
          eq_true (show n - 1 - u.val < n - 1 - e.mid.val from by omega),
          eq_false (show ¬(u.val < e.j.val) from by omega),
          eq_false (show ¬(u.val = e.j.val) from by omega),
          true_or, false_or, false_and, if_true, if_false]
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
