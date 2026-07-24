import Kemeny.FromMaxCut.Walk

/-!
# The reverse direction, assembled

The reverse counterpart of `Forward.lean`'s master bound: a *lower* bound on
the margin cost of a block ranking whose vertex part agrees with an output
spec, and from it the reverse direction proper — a ranking within the margin
budget yields a colouring cutting at least `k` edges.

The blocks: the vertex–vertex quarter is *exactly* `3nM²`, because the
oriented margins there depend on the ranking only through its vertex-part
comparisons, which `VertexAgree` equates with the output spec's — the forward
computation transfers pointwise (`orientedMargin_congr`). The vertex–edge
quarters dominate `M (6·span e + 2 + [e uncut])` per edge (the walk bounds),
which sums to `M·edgeBound − M·cutSize`; the edge–edge quarter is simply
dropped. Stated additively (`le_marginCost_add_cut`), mirroring the forward
master bound.

The reverse direction (`exists_cut_of_marginCost_le`) chains the milestones:
block companion (`exists_block_marginCost_le`), rigidity
(`exists_vertexAgree`, fed by the budget arithmetic `marginBudget <
3nM² + M²`), and the master bound; the budget then forces
`M·k ≤ pairSlack + M·cutSize`, and `pairSlack < M` divides out to
`k ≤ cutSize`. The arithmetic inputs are crude polynomial bounds:
`#edges ≤ n²`, so `edgeBound ≤ n²(6n+3)` and `pairSlack ≤ 4n⁴`, both far
below `M = 1000(n+1)⁴`.
-/

namespace Hardness

open Finset

variable {n M : ℕ} {G : SimpleGraph (Fin n)}

/-! ## Transferring oriented margins along comparison agreement -/

/-- The vertex–vertex block of a ranking whose vertex part agrees with the
output spec is the output spec's vertex–vertex block: exactly `3nM²`. -/
private theorem sum_orientedMargin_vv_eq {r : LinearOrder (Cand n M G)}
    {χ : Fin n → Bool} (hva : VertexAgree r χ) :
    (∑ a : Fin n × Letter × Fin M, ∑ a' : Fin n × Letter × Fin M,
      orientedMargin (kemenyProfile n G M) r (Sum.inl a) (Sum.inl a'))
      = 3 * n * M ^ 2 := by
  have hpt : ∀ a a' : Fin n × Letter × Fin M,
      orientedMargin (kemenyProfile n G M) r (Sum.inl a) (Sum.inl a')
        = orientedMargin (kemenyProfile n G M) ((outSpec n G χ).ranking M)
            (Sum.inl a) (Sum.inl a') := by
    rintro ⟨u, x, m⟩ ⟨u', x', m'⟩
    exact orientedMargin_congr (hva u x m u' x' m')
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) ↦
    Finset.sum_congr rfl fun a' (_ : a' ∈ univ) ↦ hpt a a']
  simp only [Fintype.sum_prod_type]
  exact sum_orientedMargin_out_vv χ

/-! ## The reverse master bound -/

/-- **The master cost bound of the reverse direction**: on a block ranking
whose vertex part agrees with the output spec of `χ`, the margin cost plus
`M·cutSize χ` is at least `3nM² + M·edgeBound` — the mirror of the forward
`marginCost_out_add_cut_le`, with the edge–edge block dropped instead of
bounded. -/
theorem le_marginCost_add_cut [DecidableRel G.Adj] (hsp : SpreadEdges n G)
    {r : LinearOrder (Cand n M G)} (hb : ∀ u x, BlockAt r u x)
    {χ : Fin n → Bool} (hva : VertexAgree r χ)
    (hlong : ∀ e : EdgePair n G, e.i.val + 3 ≤ e.j.val) :
    3 * n * M ^ 2 + M * edgeBound n G
      ≤ marginCost (kemenyProfile n G M) r + M * cutSize G χ := by
  rw [marginCost_eq_sum_orientedMargin]
  simp only [Fintype.sum_sum_type, Finset.sum_add_distrib]
  have hvv := sum_orientedMargin_vv_eq hva
  have hveev : M * edgeBound n G
      ≤ ((∑ a : Fin n × Letter × Fin M, ∑ p : EdgePair n G × Side,
          orientedMargin (kemenyProfile n G M) r (Sum.inl a) (Sum.inr p))
        + ∑ p : EdgePair n G × Side, ∑ a : Fin n × Letter × Fin M,
          orientedMargin (kemenyProfile n G M) r (Sum.inr p) (Sum.inl a))
        + M * cutSize G χ := by
    have hsplit : (∑ a : Fin n × Letter × Fin M, ∑ p : EdgePair n G × Side,
          orientedMargin (kemenyProfile n G M) r (Sum.inl a) (Sum.inr p))
        + (∑ p : EdgePair n G × Side, ∑ a : Fin n × Letter × Fin M,
          orientedMargin (kemenyProfile n G M) r (Sum.inr p) (Sum.inl a))
        = ∑ e : EdgePair n G, ∑ s : Side, ∑ u : Fin n, ∑ x : Letter, ∑ m : Fin M,
            (orientedMargin (kemenyProfile n G M) r
                (Sum.inl (u, x, m)) (Sum.inr (e, s))
              + orientedMargin (kemenyProfile n G M) r
                (Sum.inr (e, s)) (Sum.inl (u, x, m))) := by
      rw [show (∑ a : Fin n × Letter × Fin M, ∑ p : EdgePair n G × Side,
            orientedMargin (kemenyProfile n G M) r (Sum.inl a) (Sum.inr p))
          = ∑ p : EdgePair n G × Side, ∑ a : Fin n × Letter × Fin M,
            orientedMargin (kemenyProfile n G M) r (Sum.inl a) (Sum.inr p) from
          Finset.sum_comm]
      simp only [← Finset.sum_add_distrib]
      simp only [Fintype.sum_prod_type]
    have hper : (∑ e : EdgePair n G,
          M * (6 * e.span + 2 + (if χ e.i = χ e.j then 1 else 0)))
        ≤ ∑ e : EdgePair n G, ∑ s : Side, ∑ u : Fin n, ∑ x : Letter, ∑ m : Fin M,
            (orientedMargin (kemenyProfile n G M) r
                (Sum.inl (u, x, m)) (Sum.inr (e, s))
              + orientedMargin (kemenyProfile n G M) r
                (Sum.inr (e, s)) (Sum.inl (u, x, m))) :=
      Finset.sum_le_sum fun e _ ↦ sum_orientedMargin_ve_ge hsp hb hva e (hlong e)
    have hkey : (∑ e : EdgePair n G,
          M * (6 * e.span + 2 + (if χ e.i = χ e.j then 1 else 0)))
        + M * cutSize G χ = M * edgeBound n G := by
      rw [cutSize_eq_sum_edgePair n G χ, edgeBound, Finset.mul_sum, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun e _ ↦ ?_
      by_cases h : χ e.i = χ e.j
      · rw [if_pos h, if_pos h]
        ring
      · rw [if_neg h, if_neg h]
        ring
    rw [hsplit, ← hkey]
    exact Nat.add_le_add_right hper _
  rw [hvv]
  omega

/-! ## The size bounds feeding the budget arithmetic -/

theorem card_edgePair_le [DecidableRel G.Adj] :
    Fintype.card (EdgePair n G) ≤ n * n := by
  calc Fintype.card (EdgePair n G) ≤ Fintype.card (Fin n × Fin n) :=
      Fintype.card_subtype_le _
    _ = n * n := by rw [Fintype.card_prod, Fintype.card_fin]

theorem cutSize_le_card_edgePair [DecidableRel G.Adj] (χ : Fin n → Bool) :
    cutSize G χ ≤ Fintype.card (EdgePair n G) := by
  rw [cutSize_eq_sum_edgePair]
  calc (∑ e : EdgePair n G, if χ e.i = χ e.j then 0 else 1)
      ≤ ∑ _e : EdgePair n G, 1 :=
        Finset.sum_le_sum fun e _ ↦ by split <;> omega
    _ = Fintype.card (EdgePair n G) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]

theorem card_edgePair_le_edgeBound [DecidableRel G.Adj] :
    Fintype.card (EdgePair n G) ≤ edgeBound n G := by
  rw [edgeBound, ← Finset.card_univ, Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum fun e _ ↦ by omega

theorem edgeBound_le [DecidableRel G.Adj] :
    edgeBound n G ≤ n * n * (6 * n + 3) := by
  rw [edgeBound]
  calc (∑ e : EdgePair n G, (6 * e.span + 3))
      ≤ ∑ _e : EdgePair n G, (6 * n + 3) :=
        Finset.sum_le_sum fun e _ ↦ by
          have h1 := e.j.isLt
          have h2 := e.span_def
          omega
    _ = Fintype.card (EdgePair n G) * (6 * n + 3) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    _ ≤ n * n * (6 * n + 3) := Nat.mul_le_mul_right _ card_edgePair_le

theorem edgeBound_lt_bigM [DecidableRel G.Adj] : edgeBound n G < bigM n := by
  have hp : 0 < (n + 1) ^ 4 := pow_pos (Nat.succ_pos n) 4
  calc edgeBound n G ≤ n * n * (6 * n + 3) := edgeBound_le
    _ ≤ (n + 1) * (n + 1) * (9 * (n + 1)) :=
        Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
    _ = 9 * (n + 1) ^ 3 := by ring
    _ ≤ 9 * (n + 1) ^ 4 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
    _ < 1000 * (n + 1) ^ 4 := (Nat.mul_lt_mul_right hp).mpr (by omega)
    _ = bigM n := rfl

theorem pairSlack_lt_bigM [DecidableRel G.Adj] : pairSlack n G < bigM n := by
  have hp : 0 < (n + 1) ^ 4 := pow_pos (Nat.succ_pos n) 4
  calc pairSlack n G = (2 * Fintype.card (EdgePair n G)) ^ 2 := rfl
    _ ≤ (2 * (n * n)) ^ 2 :=
        Nat.pow_le_pow_left (Nat.mul_le_mul_left _ card_edgePair_le) 2
    _ = 4 * (n * n * (n * n)) := by ring
    _ ≤ 4 * (n + 1) ^ 4 := by
        refine Nat.mul_le_mul_left _ ?_
        calc n * n * (n * n) ≤ (n + 1) * (n + 1) * ((n + 1) * (n + 1)) :=
            Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega))
              (Nat.mul_le_mul (by omega) (by omega))
          _ = (n + 1) ^ 4 := by ring
    _ < 1000 * (n + 1) ^ 4 := (Nat.mul_lt_mul_right hp).mpr (by omega)
    _ = bigM n := rfl

theorem bigM_pos (n : ℕ) : 0 < bigM n :=
  Nat.mul_pos (by omega) (pow_pos (Nat.succ_pos n) 4)

/-- **The budget is below the rigidity threshold**: the edge and slack terms
of the margin budget together stay below `M²`, so any ranking within budget
costs less than `3nM² + M²` — the hypothesis rigidity needs. -/
theorem marginBudget_lt_rigidity (x : NumberedGraphInstance) :
    marginBudget x < 3 * x.n * bigM x.n ^ 2 + bigM x.n ^ 2 := by
  have hE : edgeBound x.n x.G < bigM x.n := edgeBound_lt_bigM
  have hP : pairSlack x.n x.G < bigM x.n := pairSlack_lt_bigM
  have hEM : bigM x.n * edgeBound x.n x.G + bigM x.n ≤ bigM x.n ^ 2 := by
    calc bigM x.n * edgeBound x.n x.G + bigM x.n
        = bigM x.n * (edgeBound x.n x.G + 1) := by ring
      _ ≤ bigM x.n * bigM x.n := Nat.mul_le_mul_left _ (by omega)
      _ = bigM x.n ^ 2 := by ring
  calc marginBudget x
      ≤ 3 * x.n * bigM x.n ^ 2 + bigM x.n * edgeBound x.n x.G
        + pairSlack x.n x.G := by
        rw [marginBudget]
        exact Nat.sub_le _ _
    _ < 3 * x.n * bigM x.n ^ 2 + bigM x.n ^ 2 := by linarith

/-! ## The reverse direction -/

/-- **The reverse direction**: on a long-even-edges instance with `k` at most
the edge count, any ranking within the margin budget yields a colouring
cutting at least `k` edges. Chain: block companion, rigidity, the reverse
master bound, and the budget arithmetic — `pairSlack < M` divides out to
`k ≤ cutSize`. -/
theorem exists_cut_of_marginCost_le (x : NumberedGraphInstance)
    (hlee : LongEvenEdges x) {r : LinearOrder (Cand x.n (bigM x.n) x.G)}
    (hr : marginCost (kemenyProfile x.n x.G (bigM x.n)) r ≤ marginBudget x)
    (hk : x.k ≤ Fintype.card (EdgePair x.n x.G)) :
    ∃ χ : Fin x.n → Bool, x.k ≤ cutSize x.G χ := by
  have hsp := spreadEdges_of_longEvenEdges hlee
  have hM := bigM_pos x.n
  obtain ⟨r', hb, hle⟩ := exists_block_marginCost_le hM r
  have hcost' : marginCost (kemenyProfile x.n x.G (bigM x.n)) r'
      ≤ marginBudget x := le_trans hle hr
  obtain ⟨χ, hva⟩ := exists_vertexAgree hM hb
    (lt_of_le_of_lt hcost' (marginBudget_lt_rigidity x))
  refine ⟨χ, ?_⟩
  have hlong : ∀ e : EdgePair x.n x.G, e.i.val + 3 ≤ e.j.val := fun e ↦ by
    have h := (hlee e.i e.j e.adj e.i_lt_j).1
    omega
  have hmaster := le_marginCost_add_cut hsp hb hva hlong
  have hMk : bigM x.n * x.k ≤ 3 * x.n * bigM x.n ^ 2
      + bigM x.n * edgeBound x.n x.G + pairSlack x.n x.G := by
    have h1 : bigM x.n * x.k ≤ bigM x.n * edgeBound x.n x.G :=
      Nat.mul_le_mul_left _ (le_trans hk card_edgePair_le_edgeBound)
    omega
  have hcancel : marginBudget x + bigM x.n * x.k
      = 3 * x.n * bigM x.n ^ 2 + bigM x.n * edgeBound x.n x.G
        + pairSlack x.n x.G := by
    rw [marginBudget, Nat.sub_add_cancel hMk]
  have hP : pairSlack x.n x.G < bigM x.n := pairSlack_lt_bigM
  have hbound : marginCost (kemenyProfile x.n x.G (bigM x.n)) r'
        + bigM x.n * cutSize x.G χ
      ≤ marginBudget x + bigM x.n * cutSize x.G χ :=
    Nat.add_le_add_right hcost' _
  have hchain : bigM x.n * x.k < bigM x.n * (cutSize x.G χ + 1) := by
    have hexp : bigM x.n * (cutSize x.G χ + 1)
        = bigM x.n * cutSize x.G χ + bigM x.n := by ring
    omega
  exact Nat.lt_succ_iff.mp (Nat.lt_of_mul_lt_mul_left hchain)

end Hardness
