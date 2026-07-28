import KemenyHardness.FromMaxCut.Meta
import KemenyHardness.FromMaxCut.Gadget

/-!
# The reverse direction: rigidity of cheap block rankings

Second step of the reverse direction. On a block ranking (`Meta.lean`), the
vertex–vertex margin cost decomposes into gadget-pair blocks of `M²`-weighted
meta-pairs: each gadget's diagonal block costs `M² · wrongArcCost` of its
induced letter order (`gadgetRank`, the rank of a letter among the six
supercandidates of its gadget), and every cross-gadget pair ranked against
the ascending 2-of-3 majority costs a further `M²`. Since every letter order
is wrong on at least three arcs (`Gadget.lean`), the vertex–vertex block
costs at least `3nM²` — and a budget below `3nM² + M²` *forces* the vertex
structure completely: every gadget order is exactly `ABCDEF` or `DAEBFC`, and
all cross-gadget pairs are ascending. The forced structure is recorded as
`VertexAgree`: the vertex part of the ranking coincides with the output spec
of the colouring `χ` that reads each gadget's side off its letter order —
the exact interface on which the edge-candidate analysis runs.
-/

namespace Hardness

open Finset

variable {n M : ℕ} {G : SimpleGraph (Fin n)}

/-! ## The induced letter order of a gadget -/

/-- The letters of gadget `u` ranked above `X_u`, read off the members with
index `m₀`. -/
def lettersBelow (r : LinearOrder (Cand n M G)) (m₀ : Fin M) (u : Fin n)
    (x : Letter) : Finset Letter :=
  letI := r.toDecidableLT
  Finset.univ.filter fun y : Letter ↦ r.lt (Sum.inl (u, y, m₀)) (Sum.inl (u, x, m₀))

@[simp] theorem mem_lettersBelow {r : LinearOrder (Cand n M G)} {m₀ : Fin M}
    {u : Fin n} {x y : Letter} :
    y ∈ lettersBelow r m₀ u x ↔ r.lt (Sum.inl (u, y, m₀)) (Sum.inl (u, x, m₀)) := by
  rw [lettersBelow, Finset.mem_filter]
  exact and_iff_right (Finset.mem_univ y)

/-- The rank of letter `x` in the induced order of gadget `u`: how many
letters sit above it. The position function whose classification is
`Gadget.lean`. -/
def gadgetRank (r : LinearOrder (Cand n M G)) (m₀ : Fin M) (u : Fin n)
    (x : Letter) : ℕ :=
  (lettersBelow r m₀ u x).card

theorem gadgetRank_lt_six (r : LinearOrder (Cand n M G)) (m₀ : Fin M) (u : Fin n)
    (x : Letter) : gadgetRank r m₀ u x < 6 := by
  have hsub : lettersBelow r m₀ u x ⊆ Finset.univ.erase x := by
    intro y hy
    rw [mem_lettersBelow] at hy
    rw [Finset.mem_erase]
    exact ⟨fun he ↦ ranks_ne hy (by rw [he]), Finset.mem_univ y⟩
  have h1 := Finset.card_le_card hsub
  have h2 : (Finset.univ.erase x).card = 5 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ]
    decide
  rw [gadgetRank]
  omega

/-- Ranks order as the ranking does: the rank map is the order isomorphism
onto its image. -/
theorem gadgetRank_lt_iff (r : LinearOrder (Cand n M G)) (m₀ : Fin M) (u : Fin n)
    {x x' : Letter} :
    gadgetRank r m₀ u x < gadgetRank r m₀ u x'
      ↔ r.lt (Sum.inl (u, x, m₀)) (Sum.inl (u, x', m₀)) := by
  rw [gadgetRank, gadgetRank]
  constructor
  · intro h
    by_contra hlt
    by_cases hxx : x = x'
    · subst hxx
      exact lt_irrefl _ h
    · have hne : (Sum.inl (u, x, m₀) : Cand n M G) ≠ Sum.inl (u, x', m₀) := by
        simp only [ne_eq, Sum.inl.injEq, Prod.mk.injEq]
        tauto
      have hrev := ranks_of_not_ranks hne hlt
      have hsub : lettersBelow r m₀ u x' ⊆ lettersBelow r m₀ u x := by
        intro y hy
        rw [mem_lettersBelow] at hy ⊢
        exact ranks_trans hy hrev
      exact absurd h (Nat.not_lt.mpr (Finset.card_le_card hsub))
  · intro hlt
    apply Finset.card_lt_card
    have hsub : lettersBelow r m₀ u x ⊆ lettersBelow r m₀ u x' := by
      intro y hy
      rw [mem_lettersBelow] at hy ⊢
      exact ranks_trans hy hlt
    rw [Finset.ssubset_iff_of_subset hsub]
    refine ⟨x, mem_lettersBelow.mpr hlt, fun hx ↦ ?_⟩
    rw [mem_lettersBelow] at hx
    exact ranks_ne hx rfl

theorem gadgetRank_injective (r : LinearOrder (Cand n M G)) (m₀ : Fin M)
    (u : Fin n) : Function.Injective (gadgetRank r m₀ u) := by
  intro x x' h
  by_contra hxx
  have hne : (Sum.inl (u, x, m₀) : Cand n M G) ≠ Sum.inl (u, x', m₀) := by
    simp only [ne_eq, Sum.inl.injEq, Prod.mk.injEq]
    tauto
  by_cases hlt : r.lt (Sum.inl (u, x, m₀)) (Sum.inl (u, x', m₀))
  · have := (gadgetRank_lt_iff r m₀ u).mpr hlt
    omega
  · have := (gadgetRank_lt_iff r m₀ u).mpr (ranks_of_not_ranks hne hlt)
    omega

/-! ## Member choice is immaterial on a block ranking -/

/-- On a block ranking, a comparison between members of two distinct
supercandidates does not depend on which members are compared. -/
theorem blockAt_lt_transfer {r : LinearOrder (Cand n M G)}
    (hb : ∀ u x, BlockAt r u x) {u u' : Fin n} {x x' : Letter}
    (hne : ¬(u = u' ∧ x = x')) (m m' m₀ m₀' : Fin M) :
    r.lt (Sum.inl (u, x, m)) (Sum.inl (u', x', m'))
      ↔ r.lt (Sum.inl (u, x, m₀)) (Sum.inl (u', x', m₀')) := by
  have hout : (Sum.inl (u', x', m') : Cand n M G) ∉ super u x :=
    not_mem_super_of_ne fun h ↦ hne ⟨h.1.symm, h.2.symm⟩
  have hout' : (Sum.inl (u, x, m₀) : Cand n M G) ∉ super u' x' :=
    not_mem_super_of_ne hne
  exact ((hb u x).2 _ hout m m₀).trans ((hb u' x').uniform_right hout' m' m₀')

/-! ## Cross-gadget margins of the profile

Voters 1 and 3 place the gadgets ascending, voter 2 descending: across two
gadgets the 2-of-3 majority is the ascending order, with margin ±1. -/

theorem againstCount_profile_offdiag {u u' : Fin n} (huu : u.val < u'.val)
    (x x' : Letter) (m m' : Fin M) :
    againstCount (kemenyProfile n G M) (Sum.inl (u, x, m)) (Sum.inl (u', x', m'))
      = 1 := by
  have hbu := u.isLt
  have hbu' := u'.isLt
  have h1 : ((spec1 n G).ranking M).lt (Sum.inl (u, x, m)) (Sum.inl (u', x', m')) :=
    (VoterSpec.lt_vertex_vertex _).mpr (Or.inl huu)
  have h3 : ((spec3 n G).ranking M).lt (Sum.inl (u, x, m)) (Sum.inl (u', x', m')) :=
    (VoterSpec.lt_vertex_vertex _).mpr (Or.inl huu)
  have h2 : ((spec2 n G).ranking M).lt (Sum.inl (u', x', m')) (Sum.inl (u, x, m)) :=
    (VoterSpec.lt_vertex_vertex _).mpr (Or.inl (by simp only [spec2]; omega))
  rw [againstCount_profile_eq, againstCount_singleton_of_lt h1,
    againstCount_singleton_of_gt h2, againstCount_singleton_of_lt h3]

theorem againstCount_profile_offdiag_rev {u u' : Fin n} (huu : u.val < u'.val)
    (x x' : Letter) (m m' : Fin M) :
    againstCount (kemenyProfile n G M) (Sum.inl (u', x', m')) (Sum.inl (u, x, m))
      = 2 := by
  have hbu := u.isLt
  have hbu' := u'.isLt
  have h1 : ((spec1 n G).ranking M).lt (Sum.inl (u, x, m)) (Sum.inl (u', x', m')) :=
    (VoterSpec.lt_vertex_vertex _).mpr (Or.inl huu)
  have h3 : ((spec3 n G).ranking M).lt (Sum.inl (u, x, m)) (Sum.inl (u', x', m')) :=
    (VoterSpec.lt_vertex_vertex _).mpr (Or.inl huu)
  have h2 : ((spec2 n G).ranking M).lt (Sum.inl (u', x', m')) (Sum.inl (u, x, m)) :=
    (VoterSpec.lt_vertex_vertex _).mpr (Or.inl (by simp only [spec2]; omega))
  rw [againstCount_profile_eq, againstCount_singleton_of_gt h1,
    againstCount_singleton_of_lt h2, againstCount_singleton_of_gt h3]

/-! ## Pointwise margin costs on a block ranking -/

/-- Members of one supercandidate cost nothing on a block ranking. -/
theorem orientedMargin_block_same_letter {r : LinearOrder (Cand n M G)}
    {u : Fin n} {x : Letter} (hb : BlockAt r u x) (m m' : Fin M) :
    orientedMargin (kemenyProfile n G M) r (Sum.inl (u, x, m)) (Sum.inl (u, x, m'))
      = 0 := by
  by_cases h : m < m'
  · rw [orientedMargin_of_lt _ ((hb.1 m m').mpr h), againstCount_profile_same_super h]
    omega
  · exact orientedMargin_of_not_lt _ fun hc ↦ h ((hb.1 m m').mp hc)

/-- A same-gadget letter pair costs the wrong-arc value of the induced order,
uniformly in the member indices. -/
theorem orientedMargin_block_letters {r : LinearOrder (Cand n M G)}
    (hb : ∀ u x, BlockAt r u x) (m₀ : Fin M) {u : Fin n} {x x' : Letter}
    (hxx : x ≠ x') (m m' : Fin M) :
    orientedMargin (kemenyProfile n G M) r (Sum.inl (u, x, m)) (Sum.inl (u, x', m'))
      = if gadgetRank r m₀ u x < gadgetRank r m₀ u x'
        then beats x' x - beats x x' else 0 := by
  have hiff : r.lt (Sum.inl (u, x, m)) (Sum.inl (u, x', m'))
      ↔ gadgetRank r m₀ u x < gadgetRank r m₀ u x' :=
    (blockAt_lt_transfer hb (fun h ↦ hxx h.2) m m' m₀ m₀).trans
      (gadgetRank_lt_iff r m₀ u).symm
  by_cases h : gadgetRank r m₀ u x < gadgetRank r m₀ u x'
  · rw [if_pos h, orientedMargin_of_lt _ (hiff.mpr h),
      againstCount_profile_letters hxx, againstCount_profile_letters hxx.symm]
  · rw [if_neg h]
    exact orientedMargin_of_not_lt _ fun hc ↦ h (hiff.mp hc)

/-- A cross-gadget pair ranked against the ascending majority costs one
margin unit. -/
theorem orientedMargin_block_cross_one {r : LinearOrder (Cand n M G)}
    {u u' : Fin n} {x x' : Letter} {m m' : Fin M} (huu : u'.val < u.val)
    (hlt : r.lt (Sum.inl (u, x, m)) (Sum.inl (u', x', m'))) :
    orientedMargin (kemenyProfile n G M) r (Sum.inl (u, x, m)) (Sum.inl (u', x', m'))
      = 1 := by
  rw [orientedMargin_of_lt _ hlt, againstCount_profile_offdiag_rev huu x' x m' m,
    againstCount_profile_offdiag huu x' x m' m]

/-! ## The gadget-pair decomposition of the vertex–vertex block -/

/-- The vertex–vertex margin cost between two gadgets. -/
def gadgetBlockCost (r : LinearOrder (Cand n M G)) (u u' : Fin n) : ℕ :=
  ∑ x : Letter, ∑ m : Fin M, ∑ x' : Letter, ∑ m' : Fin M,
    orientedMargin (kemenyProfile n G M) r (Sum.inl (u, x, m)) (Sum.inl (u', x', m'))

/-- The gadget-pair blocks together are a lower bound on the margin cost:
they are the vertex–vertex quarter of the ordered square. -/
theorem sum_gadgetBlockCost_le_marginCost [DecidableRel G.Adj]
    (r : LinearOrder (Cand n M G)) :
    ∑ u : Fin n, ∑ u' : Fin n, gadgetBlockCost r u u'
      ≤ marginCost (kemenyProfile n G M) r := by
  have hb1 : (∑ a : Fin n × Letter × Fin M, ∑ a' : Fin n × Letter × Fin M,
        orientedMargin (kemenyProfile n G M) r (Sum.inl a) (Sum.inl a'))
      = ∑ u : Fin n, ∑ u' : Fin n, gadgetBlockCost r u u' := by
    simp only [Fintype.sum_prod_type, gadgetBlockCost]
    refine Finset.sum_congr rfl fun u _ ↦ ?_
    rw [Finset.sum_congr rfl fun x (_ : x ∈ Finset.univ) ↦
      (Finset.sum_comm :
        (∑ m : Fin M, ∑ u' : Fin n, ∑ x' : Letter, ∑ m' : Fin M,
          orientedMargin (kemenyProfile n G M) r (Sum.inl (u, x, m))
            (Sum.inl (u', x', m')))
        = ∑ u' : Fin n, ∑ m : Fin M, ∑ x' : Letter, ∑ m' : Fin M,
          orientedMargin (kemenyProfile n G M) r (Sum.inl (u, x, m))
            (Sum.inl (u', x', m')))]
    exact Finset.sum_comm
  rw [marginCost_eq_sum_orientedMargin]
  simp only [Fintype.sum_sum_type, Finset.sum_add_distrib]
  omega

/-- **The diagonal block of a gadget**: exactly `M²` times the wrong-arc cost
of its induced letter order. -/
theorem gadgetBlockCost_diag {r : LinearOrder (Cand n M G)}
    (hb : ∀ u x, BlockAt r u x) (m₀ : Fin M) (u : Fin n) :
    gadgetBlockCost r u u = M ^ 2 * wrongArcCost (gadgetRank r m₀ u) := by
  rw [gadgetBlockCost]
  rw [Finset.sum_congr rfl fun x (_ : x ∈ Finset.univ) ↦
    (Finset.sum_comm :
      (∑ m : Fin M, ∑ x' : Letter, ∑ m' : Fin M,
        orientedMargin (kemenyProfile n G M) r (Sum.inl (u, x, m))
          (Sum.inl (u, x', m')))
      = ∑ x' : Letter, ∑ m : Fin M, ∑ m' : Fin M,
        orientedMargin (kemenyProfile n G M) r (Sum.inl (u, x, m))
          (Sum.inl (u, x', m')))]
  have hinner : ∀ x x' : Letter,
      (∑ m : Fin M, ∑ m' : Fin M,
        orientedMargin (kemenyProfile n G M) r (Sum.inl (u, x, m))
          (Sum.inl (u, x', m')))
      = M ^ 2 * (if gadgetRank r m₀ u x < gadgetRank r m₀ u x'
          then beats x' x - beats x x' else 0) := by
    intro x x'
    by_cases hxx : x = x'
    · subst hxx
      rw [if_neg (lt_irrefl _), mul_zero]
      exact Finset.sum_eq_zero fun m _ ↦ Finset.sum_eq_zero fun m' _ ↦
        orientedMargin_block_same_letter (hb u x) m m'
    · rw [Finset.sum_congr rfl fun m (_ : m ∈ Finset.univ) ↦
        Finset.sum_congr rfl fun m' (_ : m' ∈ Finset.univ) ↦
          orientedMargin_block_letters hb m₀ hxx m m']
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      ring
  rw [Finset.sum_congr rfl fun x (_ : x ∈ Finset.univ) ↦
    Finset.sum_congr rfl fun x' (_ : x' ∈ Finset.univ) ↦ hinner x x']
  simp only [← Finset.mul_sum]
  rw [wrongArcCost]

/-- **The diagonal lower bound**: the margin cost dominates `M²` times the
total wrong-arc cost of the induced gadget orders. -/
theorem mul_sum_wrongArcCost_le_marginCost [DecidableRel G.Adj]
    {r : LinearOrder (Cand n M G)} (hb : ∀ u x, BlockAt r u x) (m₀ : Fin M) :
    M ^ 2 * ∑ u : Fin n, wrongArcCost (gadgetRank r m₀ u)
      ≤ marginCost (kemenyProfile n G M) r := by
  calc M ^ 2 * ∑ u : Fin n, wrongArcCost (gadgetRank r m₀ u)
      = ∑ u : Fin n, gadgetBlockCost r u u := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun u _ ↦ (gadgetBlockCost_diag hb m₀ u).symm
    _ ≤ ∑ u : Fin n, ∑ u' : Fin n, gadgetBlockCost r u u' :=
        Finset.sum_le_sum fun u _ ↦
          Finset.single_le_sum (fun u' _ ↦ Nat.zero_le _) (Finset.mem_univ u)
    _ ≤ marginCost (kemenyProfile n G M) r := sum_gadgetBlockCost_le_marginCost r

/-- **The violation lower bound**: a cross-gadget pair ranked against the
ascending majority costs a further `M²` on top of the diagonal. -/
theorem mul_sum_wrongArcCost_add_le_marginCost [DecidableRel G.Adj]
    {r : LinearOrder (Cand n M G)} (hb : ∀ u x, BlockAt r u x) (m₀ : Fin M)
    {ua ub : Fin n} {xa xb : Letter} (hval : ub.val < ua.val)
    (hlt : r.lt (Sum.inl (ua, xa, m₀)) (Sum.inl (ub, xb, m₀))) :
    M ^ 2 * (∑ u : Fin n, wrongArcCost (gadgetRank r m₀ u)) + M ^ 2
      ≤ marginCost (kemenyProfile n G M) r := by
  have hne : ua ≠ ub := fun h ↦ by rw [h] at hval; exact lt_irrefl _ hval
  have hcross : M ^ 2 ≤ gadgetBlockCost r ua ub := by
    have hpt : ∀ m m' : Fin M,
        orientedMargin (kemenyProfile n G M) r (Sum.inl (ua, xa, m))
          (Sum.inl (ub, xb, m')) = 1 := by
      intro m m'
      refine orientedMargin_block_cross_one hval ?_
      exact (blockAt_lt_transfer hb (fun h ↦ hne h.1) m m' m₀ m₀).mpr hlt
    have hMM : M ^ 2 = ∑ m : Fin M, ∑ m' : Fin M,
        orientedMargin (kemenyProfile n G M) r (Sum.inl (ua, xa, m))
          (Sum.inl (ub, xb, m')) := by
      rw [Finset.sum_congr rfl fun m (_ : m ∈ Finset.univ) ↦
        Finset.sum_congr rfl fun m' (_ : m' ∈ Finset.univ) ↦ hpt m m']
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
        mul_one]
      ring
    rw [hMM, gadgetBlockCost]
    calc (∑ m : Fin M, ∑ m' : Fin M,
        orientedMargin (kemenyProfile n G M) r (Sum.inl (ua, xa, m))
          (Sum.inl (ub, xb, m')))
        ≤ ∑ m : Fin M, ∑ x' : Letter, ∑ m' : Fin M,
            orientedMargin (kemenyProfile n G M) r (Sum.inl (ua, xa, m))
              (Sum.inl (ub, x', m')) :=
          Finset.sum_le_sum fun m _ ↦
            Finset.single_le_sum
              (f := fun x' : Letter ↦ ∑ m' : Fin M,
                orientedMargin (kemenyProfile n G M) r (Sum.inl (ua, xa, m))
                  (Sum.inl (ub, x', m')))
              (fun x' _ ↦ Nat.zero_le _) (Finset.mem_univ xb)
      _ ≤ ∑ x : Letter, ∑ m : Fin M, ∑ x' : Letter, ∑ m' : Fin M,
            orientedMargin (kemenyProfile n G M) r (Sum.inl (ua, x, m))
              (Sum.inl (ub, x', m')) :=
          Finset.single_le_sum
            (f := fun x : Letter ↦ ∑ m : Fin M, ∑ x' : Letter, ∑ m' : Fin M,
              orientedMargin (kemenyProfile n G M) r (Sum.inl (ua, x, m))
                (Sum.inl (ub, x', m')))
            (fun x _ ↦ Nat.zero_le _) (Finset.mem_univ xa)
  have h1 : gadgetBlockCost r ua ua
      + ∑ u ∈ Finset.univ.erase ua, gadgetBlockCost r u u
      = ∑ u : Fin n, gadgetBlockCost r u u :=
    Finset.add_sum_erase _ (fun u ↦ gadgetBlockCost r u u) (Finset.mem_univ ua)
  have h2 : (∑ u' : Fin n, gadgetBlockCost r ua u')
      + ∑ u ∈ Finset.univ.erase ua, ∑ u' : Fin n, gadgetBlockCost r u u'
      = ∑ u : Fin n, ∑ u' : Fin n, gadgetBlockCost r u u' :=
    Finset.add_sum_erase _ (fun u ↦ ∑ u' : Fin n, gadgetBlockCost r u u')
      (Finset.mem_univ ua)
  have h3 : ∑ u ∈ Finset.univ.erase ua, gadgetBlockCost r u u
      ≤ ∑ u ∈ Finset.univ.erase ua, ∑ u' : Fin n, gadgetBlockCost r u u' :=
    Finset.sum_le_sum fun u _ ↦
      Finset.single_le_sum (fun u' _ ↦ Nat.zero_le _) (Finset.mem_univ u)
  have hpair : gadgetBlockCost r ua ua + gadgetBlockCost r ua ub
      ≤ ∑ u' : Fin n, gadgetBlockCost r ua u' := by
    rw [← Finset.sum_pair hne]
    exact Finset.sum_le_sum_of_subset fun z _ ↦ Finset.mem_univ z
  have hdiag : M ^ 2 * (∑ u : Fin n, wrongArcCost (gadgetRank r m₀ u))
      = ∑ u : Fin n, gadgetBlockCost r u u := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ ↦ (gadgetBlockCost_diag hb m₀ u).symm
  have hsum : (∑ u : Fin n, gadgetBlockCost r u u) + gadgetBlockCost r ua ub
      ≤ ∑ u : Fin n, ∑ u' : Fin n, gadgetBlockCost r u u' := by
    clear hcross hdiag
    omega
  calc M ^ 2 * (∑ u : Fin n, wrongArcCost (gadgetRank r m₀ u)) + M ^ 2
      = (∑ u : Fin n, gadgetBlockCost r u u) + M ^ 2 := by rw [hdiag]
    _ ≤ (∑ u : Fin n, gadgetBlockCost r u u) + gadgetBlockCost r ua ub :=
        Nat.add_le_add_left hcross _
    _ ≤ ∑ u : Fin n, ∑ u' : Fin n, gadgetBlockCost r u u' := hsum
    _ ≤ marginCost (kemenyProfile n G M) r := sum_gadgetBlockCost_le_marginCost r

/-- The pointwise squeeze `Σ = 3n ∧ each ≥ 3 → each = 3`, in a context free
of the heavy cost hypotheses (`omega` scans every arithmetic hypothesis in
scope, and whnf-normalizing one that mentions `marginCost` explodes). -/
private theorem eq_three_of_squeeze {W E S nn : ℕ} (h1 : W + E = S)
    (h2 : 3 * (nn - 1) ≤ E) (h3 : 3 ≤ W) (h4 : S ≤ 3 * nn) (h5 : 1 ≤ nn) :
    W = 3 := by
  omega

/-! ## Rigidity -/

/-- The vertex part of `r` coincides with the output spec of the colouring
`χ` — the forced structure a below-`3nM² + M²` budget imposes on a block
ranking, and the interface of the edge-candidate analysis. -/
def VertexAgree (r : LinearOrder (Cand n M G)) (χ : Fin n → Bool) : Prop :=
  ∀ (u : Fin n) (x : Letter) (m : Fin M) (u' : Fin n) (x' : Letter) (m' : Fin M),
    r.lt (Sum.inl (u, x, m)) (Sum.inl (u', x', m'))
      ↔ ((outSpec n G χ).ranking M).lt (Sum.inl (u, x, m)) (Sum.inl (u', x', m'))

/-- The gadget classification at an induced letter order: `gadgetRank` is
injective with values below `6`, so it is one of the `720` orders the
enumeration ranges over. -/
theorem three_le_wrongArcCost_gadgetRank (r : LinearOrder (Cand n M G)) (m₀ : Fin M)
    (u : Fin n) : 3 ≤ wrongArcCost (gadgetRank r m₀ u) :=
  three_le_wrongArcCost (gadgetRank_injective r m₀ u) (gadgetRank_lt_six r m₀ u)

/-- **The diagonal floor**: whatever the ranking, its gadgets are wrong on at
least `3n` arcs between them. -/
theorem three_mul_le_sum_wrongArcCost (r : LinearOrder (Cand n M G)) (m₀ : Fin M) :
    3 * n ≤ ∑ u : Fin n, wrongArcCost (gadgetRank r m₀ u) := by
  calc 3 * n = ∑ _u : Fin n, 3 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
        ring
    _ ≤ ∑ u : Fin n, wrongArcCost (gadgetRank r m₀ u) :=
        Finset.sum_le_sum fun u _ ↦ three_le_wrongArcCost_gadgetRank r m₀ u

/-- **The diagonal ceiling**: a block ranking of margin cost below
`3nM² + M²` has its gadgets wrong on at most `3n` arcs — the diagonal bound
divided by `M²`. -/
theorem sum_wrongArcCost_le_three_mul [DecidableRel G.Adj]
    {r : LinearOrder (Cand n M G)} (hb : ∀ u x, BlockAt r u x) (m₀ : Fin M)
    (hcost : marginCost (kemenyProfile n G M) r < 3 * n * M ^ 2 + M ^ 2) :
    ∑ u : Fin n, wrongArcCost (gadgetRank r m₀ u) ≤ 3 * n := by
  have h2 : M ^ 2 * (∑ u : Fin n, wrongArcCost (gadgetRank r m₀ u))
      < M ^ 2 * (3 * n + 1) := by
    calc M ^ 2 * (∑ u : Fin n, wrongArcCost (gadgetRank r m₀ u))
        ≤ marginCost (kemenyProfile n G M) r :=
          mul_sum_wrongArcCost_le_marginCost hb m₀
      _ < 3 * n * M ^ 2 + M ^ 2 := hcost
      _ = M ^ 2 * (3 * n + 1) := by ring
  exact Nat.lt_succ_iff.mp (Nat.lt_of_mul_lt_mul_left h2)

/-- **Every gadget is optimal**: floor and ceiling meet pointwise, so on a
cheap block ranking each gadget's induced order is wrong on exactly three
arcs — a fourth would cost `M²`. -/
theorem wrongArcCost_gadgetRank_eq_three [DecidableRel G.Adj]
    {r : LinearOrder (Cand n M G)} (hb : ∀ u x, BlockAt r u x) (m₀ : Fin M)
    (hcost : marginCost (kemenyProfile n G M) r < 3 * n * M ^ 2 + M ^ 2)
    (u₀ : Fin n) : wrongArcCost (gadgetRank r m₀ u₀) = 3 := by
  have h1 : wrongArcCost (gadgetRank r m₀ u₀)
      + ∑ u ∈ Finset.univ.erase u₀, wrongArcCost (gadgetRank r m₀ u)
      = ∑ u : Fin n, wrongArcCost (gadgetRank r m₀ u) :=
    Finset.add_sum_erase _ (fun u ↦ wrongArcCost (gadgetRank r m₀ u))
      (Finset.mem_univ u₀)
  have h2 : 3 * (n - 1)
      ≤ ∑ u ∈ Finset.univ.erase u₀, wrongArcCost (gadgetRank r m₀ u) := by
    calc 3 * (n - 1) = ∑ _u ∈ Finset.univ.erase u₀, 3 := by
          rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ u₀),
            Finset.card_univ, Fintype.card_fin, smul_eq_mul]
          ring
      _ ≤ _ := Finset.sum_le_sum fun u _ ↦ three_le_wrongArcCost_gadgetRank r m₀ u
  exact eq_three_of_squeeze h1 h2 (three_le_wrongArcCost_gadgetRank r m₀ u₀)
    (sum_wrongArcCost_le_three_mul hb m₀ hcost) u₀.pos

/-- **The gadgets ascend**: on a cheap block ranking no member of a later
gadget outranks a member of an earlier one — the violated cross pair would
cost `M²` on top of the diagonal's `3nM²`. -/
theorem not_lt_of_gadget_val_lt [DecidableRel G.Adj]
    {r : LinearOrder (Cand n M G)} (hb : ∀ u x, BlockAt r u x) (m₀ : Fin M)
    (hcost : marginCost (kemenyProfile n G M) r < 3 * n * M ^ 2 + M ^ 2)
    (ua ub : Fin n) (xa xb : Letter) (hval : ub.val < ua.val) :
    ¬ r.lt (Sum.inl (ua, xa, m₀)) (Sum.inl (ub, xb, m₀)) := by
  intro hlt
  have h3 : 3 * n * M ^ 2 + M ^ 2 ≤ marginCost (kemenyProfile n G M) r := by
    calc 3 * n * M ^ 2 + M ^ 2 = M ^ 2 * (3 * n) + M ^ 2 := by ring
      _ ≤ M ^ 2 * (∑ u : Fin n, wrongArcCost (gadgetRank r m₀ u)) + M ^ 2 :=
          Nat.add_le_add_right
            (Nat.mul_le_mul_left _ (three_mul_le_sum_wrongArcCost r m₀)) _
      _ ≤ marginCost (kemenyProfile n G M) r :=
          mul_sum_wrongArcCost_add_le_marginCost hb m₀ hval hlt
  exact absurd (h3.trans_lt hcost) (lt_irrefl _)

/-- **The forced structure is the agreement**: a block ranking whose gadgets
ascend and whose induced letter orders are those of `χ` has its whole vertex
part equal to `χ`'s output spec. The two hypotheses are read at a single
member index `m₀`; `BlockAt` spreads them to all members. -/
theorem vertexAgree_of_gadgetRank_eq {r : LinearOrder (Cand n M G)} {m₀ : Fin M}
    (hb : ∀ u x, BlockAt r u x)
    (hasc : ∀ (ua ub : Fin n) (xa xb : Letter), ub.val < ua.val →
      ¬ r.lt (Sum.inl (ua, xa, m₀)) (Sum.inl (ub, xb, m₀)))
    {χ : Fin n → Bool}
    (hrank : ∀ u x, gadgetRank r m₀ u x = (if χ u then outPosL else outPosR) x) :
    VertexAgree r χ := by
  intro u x m u' x' m'
  rw [VoterSpec.lt_vertex_vertex]
  simp only [outSpec]
  rcases Nat.lt_trichotomy u.val u'.val with hval | hval | hval
  · refine iff_of_true ?_ (Or.inl hval)
    have hnot : ¬ r.lt (Sum.inl (u', x', m')) (Sum.inl (u, x, m)) := by
      rw [blockAt_lt_transfer hb
        (fun h ↦ by rw [h.1] at hval; exact lt_irrefl _ hval) m' m m₀ m₀]
      exact hasc u' u x' x hval
    have hnexy : (Sum.inl (u', x', m') : Cand n M G) ≠ Sum.inl (u, x, m) := by
      intro hc
      simp only [Sum.inl.injEq, Prod.mk.injEq] at hc
      rw [hc.1] at hval
      exact lt_irrefl _ hval
    exact ranks_of_not_ranks hnexy hnot
  · have hu : u = u' := Fin.ext hval
    subst hu
    by_cases hxx : x = x'
    · subst hxx
      simp only [lt_self_iff_false, false_or, true_and]
      exact (hb u x).1 m m'
    · have hiff : r.lt (Sum.inl (u, x, m)) (Sum.inl (u, x', m'))
          ↔ gadgetRank r m₀ u x < gadgetRank r m₀ u x' :=
        (blockAt_lt_transfer hb (fun h ↦ hxx h.2) m m' m₀ m₀).trans
          (gadgetRank_lt_iff r m₀ u).symm
      rw [hiff, hrank u x, hrank u x']
      constructor
      · intro h
        exact Or.inr ⟨rfl, Or.inl h⟩
      · rintro (h | ⟨-, h | ⟨heq, -⟩⟩)
        · exact absurd h (lt_irrefl _)
        · exact h
        · exfalso
          cases hbb : χ u
          · simp only [hbb, Bool.false_eq_true, if_false] at heq
            exact hxx (outPosR_inj heq)
          · simp only [hbb, if_true] at heq
            exact hxx (outPosL_inj heq)
  · refine iff_of_false ?_ ?_
    · rw [blockAt_lt_transfer hb
        (fun h ↦ by rw [h.1] at hval; exact lt_irrefl _ hval) m m' m₀ m₀]
      exact hasc u u' x x' hval
    · rintro (h | ⟨h, -⟩)
      · exact absurd h (Nat.lt_asymm hval)
      · exact absurd h (Nat.ne_of_gt hval)

/-- **Rigidity**: a block ranking of margin cost below `3nM² + M²` has its
vertex part completely determined by a colouring — each gadget in `ABCDEF` or
`DAEBFC` order (else a fourth wrong arc costs `M²`) and the gadgets
ascending (else a violated cross pair costs `M²`). The colouring is the
gadgets' side bits, harvested by `choose`. -/
theorem exists_vertexAgree [DecidableRel G.Adj] (hM : 0 < M)
    {r : LinearOrder (Cand n M G)} (hb : ∀ u x, BlockAt r u x)
    (hcost : marginCost (kemenyProfile n G M) r < 3 * n * M ^ 2 + M ^ 2) :
    ∃ χ : Fin n → Bool, VertexAgree r χ := by
  have m₀ : Fin M := ⟨0, hM⟩
  have hside : ∀ u : Fin n, ∃ b : Bool,
      ∀ x, gadgetRank r m₀ u x = (if b then outPosL else outPosR) x := fun u ↦
    exists_side_of_wrongArcCost_eq_three (gadgetRank_injective r m₀ u)
      (gadgetRank_lt_six r m₀ u) (wrongArcCost_gadgetRank_eq_three hb m₀ hcost u)
  choose χ hχ using hside
  exact ⟨χ, vertexAgree_of_gadgetRank_eq hb
    (not_lt_of_gadget_val_lt hb m₀ hcost) hχ⟩

end Hardness
