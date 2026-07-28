import KemenyHardness.CloneContraction
import KemenyHardness.FromMaxCut.Construction

/-!
# The meta quotient: block rankings

First step of the reverse direction. A ranking within budget can scramble the
members of a supercandidate a little — a handful of inversions cost `O(1)`
margin units each, well inside the slack — so the rigidity analysis cannot
read gadget structure off an arbitrary cheap ranking directly. Clone
contraction repairs this: every supercandidate satisfies the clone condition
(all three voters compare its members uniformly against every other candidate,
and order them internally by member index), so contracting the `6n`
supercandidates one at a time produces a **block companion** of no larger
cost, on which every supercandidate is consecutive and internally in natural
order.

The block property is recorded comparison-wise, not positionally
(`BlockAt`): members are ordered by index among themselves, and compared
*uniformly* against every outside candidate. That is the exact interface the
meta analysis consumes — it makes the cost of a block ranking a function of
the induced order on the `6n + 2|E|` meta-candidates, with member pairs
counted `M²`-fold and member–edge pairs `M`-fold.

Iteration is by list recursion over the supercandidates: contracting one
supercandidate makes it a block (the comparison laws of `contractClones` are
precisely the block conditions) and preserves every existing block — an
outsider's comparisons are untouched, and comparisons against the contracted
set collapse to the representative, which the existing block already compares
uniformly. The main results are `exists_block_marginCost_le` (every ranking
has a block companion of no larger margin cost) via the affine bridge, so the
reverse direction may assume blocks from the start.
-/

namespace Hardness

open Finset

variable {n M : ℕ} {G : SimpleGraph (Fin n)}

/-! ## Supercandidates as finsets -/

/-- The members of the supercandidate `X_u`, as a finset of candidates. -/
def super (u : Fin n) (x : Letter) : Finset (Cand n M G) :=
  Finset.univ.image fun m : Fin M ↦ Sum.inl (u, x, m)

@[simp] theorem mem_super {c : Cand n M G} {u : Fin n} {x : Letter} :
    c ∈ super u x ↔ ∃ m : Fin M, c = Sum.inl (u, x, m) := by
  simp only [super, Finset.mem_image, Finset.mem_univ, true_and, eq_comm]

theorem inl_mem_super (u : Fin n) (x : Letter) (m : Fin M) :
    (Sum.inl (u, x, m) : Cand n M G) ∈ super u x := mem_super.mpr ⟨m, rfl⟩

theorem not_mem_super_of_ne {u u' : Fin n} {x x' : Letter} {m : Fin M}
    (h : ¬(u = u' ∧ x = x')) : (Sum.inl (u, x, m) : Cand n M G) ∉ super u' x' := by
  simp only [mem_super, Sum.inl.injEq, Prod.mk.injEq, not_exists]
  intro m₂ hc
  exact h ⟨hc.1, hc.2.1⟩

theorem inr_not_mem_super {p : EdgePair n G × Side} {u : Fin n} {x : Letter} :
    (Sum.inr p : Cand n M G) ∉ super u x := by
  simp only [mem_super, not_exists]
  exact fun m hc ↦ Sum.inr_ne_inl hc

/-! ## Supercandidates are clones

The clone condition of the contraction, for every spec ranking at once: the
member index is the last lex component of the key, so it decides a comparison
only against the *same* supercandidate. -/

/-- Within a supercandidate, every spec ranking is the natural member
order. -/
theorem ranking_lt_same_super_iff (V : VoterSpec n G) {u : Fin n} {x : Letter}
    {m m' : Fin M} :
    (V.ranking M).lt (Sum.inl (u, x, m)) (Sum.inl (u, x, m')) ↔ m < m' := by
  rw [VoterSpec.lt_vertex_vertex]
  constructor
  · rintro (h | ⟨-, h | ⟨-, h⟩⟩)
    · exact absurd h (lt_irrefl _)
    · exact absurd h (lt_irrefl _)
    · exact h
  · exact fun h ↦ Or.inr ⟨rfl, Or.inr ⟨rfl, h⟩⟩

/-- Every spec ranking compares the members of a supercandidate uniformly
against every outside candidate. -/
theorem ranking_uniform_on_super (V : VoterSpec n G) {u : Fin n} {x : Letter}
    (m m' : Fin M) {c : Cand n M G} (hc : c ∉ super u x) :
    ((V.ranking M).lt (Sum.inl (u, x, m)) c
      ↔ (V.ranking M).lt (Sum.inl (u, x, m')) c) := by
  obtain (⟨u', x', m₂⟩ | ⟨e, s⟩) := c
  · rw [VoterSpec.lt_vertex_vertex, VoterSpec.lt_vertex_vertex]
    have hne : ¬(V.gadgetPos u = V.gadgetPos u'
        ∧ V.localPos u x = V.localPos u' x') := by
      rintro ⟨h1, h2⟩
      obtain rfl := V.gadgetPos_inj h1
      obtain rfl := V.localPos_inj u h2
      exact hc (inl_mem_super u x m₂)
    constructor
    · rintro (h | ⟨h1, h2 | ⟨h2, -⟩⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h1, Or.inl h2⟩
      · exact absurd ⟨h1, h2⟩ hne
    · rintro (h | ⟨h1, h2 | ⟨h2, -⟩⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h1, Or.inl h2⟩
      · exact absurd ⟨h1, h2⟩ hne
  · rw [VoterSpec.lt_vertex_edge, VoterSpec.lt_vertex_edge]

/-- Membership in the three-voter profile, destructured. -/
private theorem profile_mem_cases {v : LinearOrder (Cand n M G)}
    (hv : v ∈ kemenyProfile n G M) :
    v = (spec1 n G).ranking M ∨ v = (spec2 n G).ranking M
      ∨ v = (spec3 n G).ranking M := by
  simpa only [kemenyProfile, List.mem_cons, List.not_mem_nil, or_false] using hv

/-! ## Block rankings -/

/-- Supercandidate `(u, x)` forms a **block** of `r`: the members are ordered
naturally among themselves and compared uniformly against every other
candidate. Comparison-wise consecutiveness — the interface on which the whole
meta analysis runs. -/
def BlockAt (r : LinearOrder (Cand n M G)) (u : Fin n) (x : Letter) : Prop :=
  (∀ m m' : Fin M, r.lt (Sum.inl (u, x, m)) (Sum.inl (u, x, m')) ↔ m < m')
  ∧ ∀ c ∉ super u x, ∀ m m' : Fin M,
      (r.lt (Sum.inl (u, x, m)) c ↔ r.lt (Sum.inl (u, x, m')) c)

/-- Uniformity in the other orientation, by totality. -/
theorem BlockAt.uniform_right {r : LinearOrder (Cand n M G)} {u : Fin n}
    {x : Letter} (hb : BlockAt r u x) {c : Cand n M G} (hc : c ∉ super u x)
    (m m' : Fin M) :
    (r.lt c (Sum.inl (u, x, m)) ↔ r.lt c (Sum.inl (u, x, m'))) := by
  have h1 : c ≠ Sum.inl (u, x, m) := fun h ↦ hc (h ▸ inl_mem_super u x m)
  have h2 : c ≠ Sum.inl (u, x, m') := fun h ↦ hc (h ▸ inl_mem_super u x m')
  rw [ranks_iff_not_ranks h1, ranks_iff_not_ranks h2]
  exact not_congr (hb.2 c hc m m')

/-! ## The contraction steps -/

/-- Contracting one supercandidate: some representative gives a companion of
no larger cost — `exists_contract_le` with the clone and unanimity conditions
discharged by the comparison laws, `ω` the first voter (any voter orders a
supercandidate naturally). -/
private theorem exists_contract_super_le [DecidableRel G.Adj] (hM : 0 < M)
    (r : LinearOrder (Cand n M G)) (u : Fin n) (x : Letter) :
    ∃ rep ∈ super (M := M) u x,
      kemenyCost (kemenyProfile n G M)
          (contractClones r ((spec1 n G).ranking M) (super u x) rep)
        ≤ kemenyCost (kemenyProfile n G M) r := by
  refine exists_contract_le r ⟨Sum.inl (u, x, ⟨0, hM⟩), inl_mem_super u x ⟨0, hM⟩⟩
    ?_ ?_
  · intro v hv s hs s' hs' c hc
    obtain ⟨m, rfl⟩ := mem_super.mp hs
    obtain ⟨m', rfl⟩ := mem_super.mp hs'
    rcases profile_mem_cases hv with rfl | rfl | rfl <;>
      exact ranking_uniform_on_super _ m m' hc
  · intro v hv s hs s' hs'
    obtain ⟨m, rfl⟩ := mem_super.mp hs
    obtain ⟨m', rfl⟩ := mem_super.mp hs'
    rcases profile_mem_cases hv with rfl | rfl | rfl <;>
      simp only [ranking_lt_same_super_iff]

/-- The contracted supercandidate is a block of the contracted ranking: the
comparison laws of `contractClones` are the block conditions on the nose. -/
private theorem blockAt_contract (r : LinearOrder (Cand n M G)) {u : Fin n}
    {x : Letter} {rep : Cand n M G} (hrep : rep ∈ super (M := M) u x) :
    BlockAt (contractClones r ((spec1 n G).ranking M) (super u x) rep) u x := by
  constructor
  · intro m m'
    rw [contractClones_lt_inside (inl_mem_super u x m) (inl_mem_super u x m'),
      ranking_lt_same_super_iff]
  · intro c hc m m'
    rw [contractClones_lt_left hrep (inl_mem_super u x m) hc,
      contractClones_lt_left hrep (inl_mem_super u x m') hc]

/-- Contracting a supercandidate preserves every block: an outside block's
comparisons are untouched, and its comparisons against the contracted set
collapse to the representative, which it already compares uniformly. -/
private theorem blockAt_contract_of_blockAt (r : LinearOrder (Cand n M G))
    {u u' : Fin n} {x x' : Letter} {rep : Cand n M G}
    (hrep : rep ∈ super (M := M) u x) (hb : BlockAt r u' x') :
    BlockAt (contractClones r ((spec1 n G).ranking M) (super u x) rep) u' x' := by
  by_cases heq : u' = u ∧ x' = x
  · obtain ⟨rfl, rfl⟩ := heq
    exact blockAt_contract r hrep
  · have hout : ∀ m : Fin M, (Sum.inl (u', x', m) : Cand n M G) ∉ super u x :=
      fun m ↦ not_mem_super_of_ne heq
    constructor
    · intro m m'
      rw [contractClones_lt_outside (hout m) (hout m')]
      exact hb.1 m m'
    · intro c hc m m'
      by_cases hcT : c ∈ super (M := M) u x
      · rw [contractClones_lt_right hrep hcT (hout m),
          contractClones_lt_right hrep hcT (hout m')]
        have hrepout : rep ∉ super (M := M) u' x' := by
          obtain ⟨mr, rfl⟩ := mem_super.mp hrep
          exact not_mem_super_of_ne fun h ↦ heq ⟨h.1.symm, h.2.symm⟩
        exact hb.2 rep hrepout m m'
      · rw [contractClones_lt_outside (hout m) hcT,
          contractClones_lt_outside (hout m') hcT]
        exact hb.2 c hc m m'

/-! ## The iteration -/

/-- Iterating the contraction over a list of supercandidates: all of them
become blocks, at no cost increase. -/
private theorem exists_block_on_list [DecidableRel G.Adj] (hM : 0 < M)
    (l : List (Fin n × Letter)) (r : LinearOrder (Cand n M G)) :
    ∃ r' : LinearOrder (Cand n M G),
      (∀ p ∈ l, BlockAt r' p.1 p.2)
        ∧ kemenyCost (kemenyProfile n G M) r'
          ≤ kemenyCost (kemenyProfile n G M) r := by
  induction l with
  | nil => exact ⟨r, by simp, le_rfl⟩
  | cons p t ih =>
    obtain ⟨r₁, hb₁, hc₁⟩ := ih
    obtain ⟨rep, hrep, hc₂⟩ := exists_contract_super_le hM r₁ p.1 p.2
    refine ⟨contractClones r₁ ((spec1 n G).ranking M) (super p.1 p.2) rep, ?_,
      le_trans hc₂ hc₁⟩
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact blockAt_contract r₁ hrep
    · exact blockAt_contract_of_blockAt r₁ hrep (hb₁ q hq)

/-- **The meta quotient**: every ranking has a block companion of no larger
margin cost — contract the `6n` supercandidates in any enumeration and
convert through the affine bridge. The reverse direction may therefore assume
every supercandidate is a block from the start. -/
theorem exists_block_marginCost_le [DecidableRel G.Adj] (hM : 0 < M)
    (r : LinearOrder (Cand n M G)) :
    ∃ r' : LinearOrder (Cand n M G),
      (∀ (u : Fin n) (x : Letter), BlockAt r' u x)
        ∧ marginCost (kemenyProfile n G M) r'
          ≤ marginCost (kemenyProfile n G M) r := by
  obtain ⟨r', hb, hc⟩ := exists_block_on_list hM Finset.univ.toList r
  refine ⟨r', fun u x ↦ hb (u, x) (Finset.mem_toList.mpr (Finset.mem_univ _)), ?_⟩
  have h1 := kemenyCost_eq_minTotal_add_marginCost (kemenyProfile n G M) r'
  have h2 := kemenyCost_eq_minTotal_add_marginCost (kemenyProfile n G M) r
  rw [minTotal_congr (kemenyProfile n G M) r' r] at h1
  omega

end Hardness
