import KemenyHardness.FromMaxCut.Construction

/-!
# Margin facts of the constructed profile

The paper's Section 6 claim about the constructed three-voter profile: **all
majority margins outside supercandidates are ±1**. In `againstCount` terms —
for any two distinct candidates:

* *within a supercandidate* the profile is unanimous in the natural member
  order (`againstCount_profile_same_super`, `…_rev`: counts `0` and `3`);
* *every other pair* has at least one voter on each side
  (`one_le_againstCount_profile`, `againstCount_profile_le_two`: counts in
  `{1, 2}`).

The engine is `sameSuper_of_unanimous`: if all three voters rank `c` above
`c'`, then `c` and `c'` are members of one supercandidate. Its case analysis
is the paper's argument made positional: voters 1 and 3 place the gadgets
ascending and key edge candidates by *left endpoint* and *right endpoint*
respectively, voter 2 places the gadgets descending and keys edge candidates
by *midpoint* — so unanimity squeezes the relevant indices from both sides
until everything collapses to a single gadget, where the three local letter
orders (`letters_not_unanimous`, a `decide`) or the opposed `ℓ_e`/`r_e` gap
slots of voters 1 and 3 finish the job.

The vertex–edge and edge–edge cases genuinely need the source restriction:
the midpoint of every edge must lie *strictly between* its endpoints and be
*exact* (`SpreadEdges`, implied by `LongEvenEdges`). For a short edge
`{i, i+1}` the midpoint gadget is `V_i` itself and the pair `B_i` versus
`r_e` really is unanimous — the formal counterpart of why the paper reduces
from MAX CUT with long even edges.

Tie-break directions between edge candidates sharing a gap are never used:
every unanimity contradiction already follows from gadget positions, gap
slots, and irreflexivity.
-/

namespace Hardness

variable {n M : ℕ} {G : SimpleGraph (Fin n)}

/-! ## Spread edges -/

/-- Every edge surrounds its midpoint gadget strictly, and the midpoint is
exact. This is what the margin analysis consumes from the long-even-edges
restriction: `i < q < j` separates the three gadgets an edge candidate
visits, and exactness of `q = (i+j)/2` makes midpoint equality collapse a
pair of edges to a single edge. -/
def SpreadEdges (n : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ e : EdgePair n G,
    e.i.val < e.mid.val ∧ e.mid.val < e.j.val ∧ e.i.val + e.j.val = 2 * e.mid.val

/-- Long even edges spread: `j − i ≥ 6` puts the midpoint strictly inside,
and evenness of `i + j` makes it exact. -/
theorem spreadEdges_of_longEvenEdges {x : NumberedGraphInstance}
    (h : LongEvenEdges x) : SpreadEdges x.n x.G := by
  intro e
  obtain ⟨hlong, heven⟩ := h e.i e.j e.adj e.i_lt_j
  rw [EdgePair.mid_val]
  omega

/-! ## Same-supercandidate pairs -/

/-- The pairs the profile is unanimous about: two members of one
supercandidate. -/
def SameSuper (c c' : Cand n M G) : Prop :=
  ∃ (i : Fin n) (x : Letter) (m m' : Fin M),
    c = Sum.inl (i, x, m) ∧ c' = Sum.inl (i, x, m')

theorem SameSuper.symm {c c' : Cand n M G} (h : SameSuper c c') :
    SameSuper c' c := by
  obtain ⟨i, x, m, m', rfl, rfl⟩ := h
  exact ⟨i, x, m', m, rfl, rfl⟩

/-- Every voter respects the natural member order within a supercandidate —
same gadget, same slot, member index decides, for any spec. -/
theorem ranking_lt_same_super (V : VoterSpec n G) {i : Fin n} {x : Letter}
    {m m' : Fin M} (h : m < m') :
    (V.ranking M).lt (Sum.inl (i, x, m)) (Sum.inl (i, x, m')) :=
  (VoterSpec.lt_vertex_vertex V).mpr (Or.inr ⟨rfl, Or.inr ⟨rfl, h⟩⟩)

/-! ## Unanimity forces a supercandidate -/

/-- No pair of letters is ordered the same way by all three local orders: the
within-gadget tournament has all margins ±1. Checked over the 36 pairs. -/
private theorem letters_not_unanimous :
    ∀ x y : Letter, ¬(pos1 x < pos1 y ∧ pos2 x < pos2 y ∧ pos3 x < pos3 y) := by
  decide

/-- **Unanimity happens only inside supercandidates**: if all three voters
rank `c` above `c'`, the two candidates are members of one supercandidate.
The contrapositive of the paper's "all margins ±1" claim, and the source of
the minority count `1` on every other pair. -/
theorem sameSuper_of_unanimous (hsp : SpreadEdges n G) {c c' : Cand n M G}
    (h1 : ((spec1 n G).ranking M).lt c c')
    (h2 : ((spec2 n G).ranking M).lt c c')
    (h3 : ((spec3 n G).ranking M).lt c c') :
    SameSuper c c' := by
  obtain (⟨u, x, m⟩ | ⟨e, s⟩) := c <;> obtain (⟨u', x', m'⟩ | ⟨e', s'⟩) := c'
  · -- vertex–vertex: voters 1 and 2 place the gadgets oppositely, so the
    -- vertices coincide; then either the letters coincide (a supercandidate)
    -- or the three local orders would be unanimous on a letter pair.
    rw [VoterSpec.lt_vertex_vertex] at h1 h2 h3
    simp only [spec1, spec2, spec3] at h1 h2 h3
    have hb := u.isLt
    have hb' := u'.isLt
    have hu : u.val = u'.val := by omega
    obtain rfl : u = u' := Fin.ext hu
    by_cases hx : x = x'
    · subst hx
      have hm : m < m' := by
        rcases h1 with h | ⟨-, h | ⟨-, h⟩⟩
        · omega
        · omega
        · exact h
      exact ⟨u, x, m, m', rfl, rfl⟩
    · exfalso
      have p1 : pos1 x < pos1 x' := by
        rcases h1 with h | ⟨-, h | ⟨h, -⟩⟩
        · omega
        · exact h
        · exact absurd (pos1_inj h) hx
      have p2 : pos2 x < pos2 x' := by
        rcases h2 with h | ⟨-, h | ⟨h, -⟩⟩
        · omega
        · exact h
        · exact absurd (pos2_inj h) hx
      have p3 : pos3 x < pos3 x' := by
        rcases h3 with h | ⟨-, h | ⟨h, -⟩⟩
        · omega
        · exact h
        · exact absurd (pos3_inj h) hx
      exact letters_not_unanimous x x' ⟨p1, p2, p3⟩
  · -- vertex–edge: voter 1 pins the vertex weakly before the left endpoint,
    -- voter 2 weakly after the midpoint — impossible, the midpoint is
    -- strictly inside.
    exfalso
    rw [VoterSpec.lt_vertex_edge] at h1 h2
    simp only [spec1, spec2] at h1 h2
    obtain ⟨hs1, hs2, -⟩ := hsp e'
    have hb := u.isLt
    have hbm := e'.mid.isLt
    omega
  · -- edge–vertex: voter 2 pins the vertex weakly before the midpoint,
    -- voter 3 weakly after the right endpoint — same squeeze.
    exfalso
    rw [VoterSpec.lt_edge_vertex] at h2 h3
    simp only [spec2, spec3] at h2 h3
    obtain ⟨-, hs2, -⟩ := hsp e
    have hb := u'.isLt
    have hbm := e.mid.isLt
    omega
  · -- edge–edge: voters 1 and 3 give `i ≤ i'` and `j ≤ j'`, voter 2 gives
    -- `q' ≤ q`; with exact midpoints the edges coincide, and then voters 1
    -- and 3 order the two sides of one edge oppositely.
    exfalso
    rw [VoterSpec.lt_edge_edge] at h1 h2 h3
    simp only [spec1, spec2, spec3] at h1 h2 h3
    obtain ⟨-, -, hq⟩ := hsp e
    obtain ⟨-, -, hq'⟩ := hsp e'
    have hbm := e.mid.isLt
    have hbm' := e'.mid.isLt
    have hii : e.i.val = e'.i.val := by omega
    have hjj : e.j.val = e'.j.val := by omega
    obtain rfl : e = e' := Subtype.ext (Prod.ext (Fin.ext hii) (Fin.ext hjj))
    cases s <;> cases s' <;>
      simp only [pos1, pos2, pos3] at h1 h2 h3 <;> omega

/-! ## The margin counts -/

/-- **Unanimity within a supercandidate**: no voter is against the natural
member order. -/
theorem againstCount_profile_same_super {i : Fin n} {x : Letter} {m m' : Fin M}
    (h : m < m') :
    againstCount (kemenyProfile n G M) (Sum.inl (i, x, m)) (Sum.inl (i, x, m')) = 0 := by
  apply againstCount_eq_zero
  intro v hv
  have hlt : v.lt (Sum.inl (i, x, m)) (Sum.inl (i, x, m') : Cand n M G) := by
    simp only [kemenyProfile, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl <;> exact ranking_lt_same_super _ h
  exact ranks_asymm hlt

/-- …and every voter is against the reversed member order. -/
theorem againstCount_profile_same_super_rev {i : Fin n} {x : Letter} {m m' : Fin M}
    (h : m < m') :
    againstCount (kemenyProfile n G M) (Sum.inl (i, x, m')) (Sum.inl (i, x, m)) = 3 := by
  rw [show (3 : ℕ) = (kemenyProfile n G M).length from rfl]
  apply againstCount_eq_length
  intro v hv
  simp only [kemenyProfile, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl <;> exact ranking_lt_same_super _ h

/-- **No unanimity outside supercandidates**: every ordered pair of distinct
candidates not sharing a supercandidate has at least one voter against it —
the paper's "all margins ±1" claim, minority side. -/
theorem one_le_againstCount_profile (hsp : SpreadEdges n G) {c c' : Cand n M G}
    (hne : c ≠ c') (hns : ¬SameSuper c c') :
    1 ≤ againstCount (kemenyProfile n G M) c c' := by
  by_cases hall : ((spec1 n G).ranking M).lt c c' ∧ ((spec2 n G).ranking M).lt c c'
      ∧ ((spec3 n G).ranking M).lt c c'
  · exact absurd (sameSuper_of_unanimous hsp hall.1 hall.2.1 hall.2.2) hns
  · have hex : ∃ v ∈ kemenyProfile n G M, v.lt c' c := by
      rcases not_and_or.mp hall with h | h
      · exact ⟨(spec1 n G).ranking M, by simp [kemenyProfile],
          ranks_of_not_ranks hne h⟩
      rcases not_and_or.mp h with h | h
      · exact ⟨(spec2 n G).ranking M, by simp [kemenyProfile],
          ranks_of_not_ranks hne h⟩
      · exact ⟨(spec3 n G).ranking M, by simp [kemenyProfile],
          ranks_of_not_ranks hne h⟩
    obtain ⟨v, hv, hlt⟩ := hex
    exact one_le_againstCount hv hlt

/-- The majority side of the ±1 margins: at most two of the three voters are
against any pair outside a supercandidate. -/
theorem againstCount_profile_le_two (hsp : SpreadEdges n G) {c c' : Cand n M G}
    (hne : c ≠ c') (hns : ¬SameSuper c c') :
    againstCount (kemenyProfile n G M) c c' ≤ 2 := by
  have hrev : 1 ≤ againstCount (kemenyProfile n G M) c' c :=
    one_le_againstCount_profile hsp hne.symm fun h ↦ hns h.symm
  have hsum := againstCount_add_againstCount (a := c) (b := c')
    (kemenyProfile n G M) hne
  rw [kemenyProfile_length] at hsum
  omega

end Hardness
