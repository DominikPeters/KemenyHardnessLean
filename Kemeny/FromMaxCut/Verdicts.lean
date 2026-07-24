import Kemeny.FromMaxCut.Margins

/-!
# The majority verdicts of the constructed profile

What the three voters say about a pair, as closed functions of the pair — the
engine *both* directions of the reduction run on, so that neither re-derives it.

The profile has three voters, so every count is a sum of three one-voter
verdicts (`againstCount_profile_eq`), each decided by that voter's comparison
law. Two shapes of pair matter:

* **two letters of one gadget** — the count is the within-gadget tournament
  `beats`, the same in every gadget (`againstCount_profile_letters`);
* **a vertex candidate against an edge candidate** — the count depends on the
  vertex candidate only through its gadget and letter, never the member index,
  and is the closed `edgeVerdict` (`againstCount_profile_ve`), with values in
  `{1, 2}` under `SpreadEdges` (`edgeVerdict_bounds`).

From `edgeVerdict` the two-way margin cost of a vertex–edge pair follows for an
*arbitrary* ranking (`orientedMargin_ve_add_swap_gen`): `verdict − 1` when the
ranking puts the vertex candidate above the edge candidate, `2 − verdict`
otherwise — the disagreement indicator against the 2-of-3 majority, which is all
either direction ever charges on such a pair.

## The verdicts region by region

`edgeVerdict e s u x` is piecewise constant in `u` on the seven ranges cut by
the edge's endpoints and midpoint `i < q < j`: `2` before the midpoint, `1`
after it, with the three landmarks `i`, `q`, `j` carrying letter-dependent rows.
Gap letters matter only at the landmark the voter places the candidate in, so
the two inner ranges and the midpoint are side-generic. The forward direction
reads these rows to compute its exact per-edge cost, the reverse direction to
bound its cut sums from below; the two outer ranges are never needed, because
every case on either side drops them.
-/

namespace Hardness

variable {n M : ℕ} {G : SimpleGraph (Fin n)}

/-! ## The profile's counts, voter by voter -/

/-- The profile count, voter by voter. -/
theorem againstCount_profile_eq (c c' : Cand n M G) :
    againstCount (kemenyProfile n G M) c c' =
      againstCount [(spec1 n G).ranking M] c c'
        + againstCount [(spec2 n G).ranking M] c c'
        + againstCount [(spec3 n G).ranking M] c c' := by
  rw [kemenyProfile, againstCount_cons ((spec1 n G).ranking M) _ c c',
    againstCount_cons ((spec2 n G).ranking M) _ c c']
  omega

/-! ## Two letters of one gadget -/

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

/-- Expanding a sum over the six letters. -/
theorem sum_letter (h : Letter → ℕ) :
    ∑ x : Letter, h x = h .A + h .B + h .C + h .D + h .E + h .F := by
  rw [show (Finset.univ : Finset Letter) = {.A, .B, .C, .D, .E, .F} from by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  omega

/-! ## A vertex candidate against an edge candidate -/

/-- One voter's verdict on a vertex–edge pair, as the comparison of the
voter's positions: cost `0` exactly if the voter ranks the vertex candidate
above the edge candidate. -/
theorem againstCount_singleton_ve (V : VoterSpec n G) (e : EdgePair n G)
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

/-- **The two-way margin cost of a vertex–edge pair**, in any ranking:
`verdict − 1` when the vertex candidate is ranked above the edge candidate,
`2 − verdict` otherwise — the disagreement indicator against the 2-of-3
majority. Both directions charge such a pair through this identity. -/
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

/-- **The two-way margin cost of a vertex–edge pair in a spec ranking**: the
same identity with the comparison read off the spec's own positions, which is
the form both the output ranking of the forward direction and the three voters
are given in. -/
theorem orientedMargin_ve_add_swap (hsp : SpreadEdges n G) (W : VoterSpec n G)
    (e : EdgePair n G) (s : Side) (u : Fin n) (x : Letter) (m : Fin M) :
    orientedMargin (kemenyProfile n G M) (W.ranking M)
        (Sum.inl (u, x, m)) (Sum.inr (e, s))
      + orientedMargin (kemenyProfile n G M) (W.ranking M)
        (Sum.inr (e, s)) (Sum.inl (u, x, m))
      = if W.gadgetPos u < W.gadgetPos (W.edgeGadget e s)
            ∨ (W.gadgetPos u = W.gadgetPos (W.edgeGadget e s)
              ∧ W.localPos u x ≤ W.localPos (W.edgeGadget e s) (W.gapLetter e s))
        then edgeVerdict e s u x - 1
        else 2 - edgeVerdict e s u x := by
  rw [orientedMargin_ve_add_swap_gen hsp (W.ranking M) e s u x m]
  exact if_congr (VoterSpec.lt_vertex_edge W) rfl rfl

/-! ## The verdicts, region by region

Closed evaluations of `edgeVerdict` as functions of the letter alone, per range
of the gadget relative to the edge's endpoints `i < q < j`. -/

theorem edgeVerdict_before_i {e : EdgePair n G} (hsp : SpreadEdges n G)
    {u : Fin n} (h : u.val < e.i.val) (s : Side) (x : Letter) :
    edgeVerdict e s u x = 1 := by
  obtain ⟨hiq, hqj, -⟩ := hsp e
  have hun := u.isLt
  have hqn := e.mid.isLt
  simp only [edgeVerdict, specMiss, spec1, spec2, spec3,
    eq_true h,
    eq_false (show ¬(n - 1 - u.val < n - 1 - e.mid.val) from by omega),
    eq_false (show ¬(n - 1 - u.val = n - 1 - e.mid.val) from by omega),
    eq_true (show u.val < e.j.val from by omega),
    true_or, false_or, false_and, if_true, if_false]

theorem edgeVerdict_after_j {e : EdgePair n G} (hsp : SpreadEdges n G)
    {u : Fin n} (h : e.j.val < u.val) (s : Side) (x : Letter) :
    edgeVerdict e s u x = 2 := by
  obtain ⟨hiq, hqj, -⟩ := hsp e
  have hun := u.isLt
  have hqn := e.mid.isLt
  simp only [edgeVerdict, specMiss, spec1, spec2, spec3,
    eq_false (show ¬(u.val < e.i.val) from by omega),
    eq_false (show ¬(u.val = e.i.val) from by omega),
    eq_true (show n - 1 - u.val < n - 1 - e.mid.val from by omega),
    eq_false (show ¬(u.val < e.j.val) from by omega),
    eq_false (show ¬(u.val = e.j.val) from by omega),
    true_or, false_or, false_and, if_true, if_false]

theorem edgeVerdict_mid1 {e : EdgePair n G} (hsp : SpreadEdges n G)
    {u : Fin n} (h1 : e.i.val < u.val) (h2 : u.val < e.mid.val) (s : Side)
    (x : Letter) : edgeVerdict e s u x = 2 := by
  obtain ⟨hiq, hqj, -⟩ := hsp e
  have hun := u.isLt
  have hqn := e.mid.isLt
  simp only [edgeVerdict, specMiss, spec1, spec2, spec3,
    eq_false (show ¬(u.val < e.i.val) from by omega),
    eq_false (show ¬(u.val = e.i.val) from by omega),
    eq_false (show ¬(n - 1 - u.val < n - 1 - e.mid.val) from by omega),
    eq_false (show ¬(n - 1 - u.val = n - 1 - e.mid.val) from by omega),
    eq_true (show u.val < e.j.val from by omega),
    true_or, false_or, false_and, if_true, if_false]

theorem edgeVerdict_at_q {e : EdgePair n G} (hsp : SpreadEdges n G)
    (s : Side) (x : Letter) :
    edgeVerdict e s e.mid x = if x = .B ∨ x = .D ∨ x = .F then 1 else 2 := by
  obtain ⟨hiq, hqj, -⟩ := hsp e
  have hqn := e.mid.isLt
  simp only [edgeVerdict, specMiss, spec1, spec2, spec3,
    eq_false (show ¬(e.mid.val < e.i.val) from by omega),
    eq_false (show ¬(e.mid.val = e.i.val) from by omega),
    eq_false (show ¬(n - 1 - e.mid.val < n - 1 - e.mid.val) from by omega),
    eq_true hqj,
    true_or, false_or, false_and, if_true, if_false]
  cases x <;> decide

theorem edgeVerdict_mid2 {e : EdgePair n G} (hsp : SpreadEdges n G)
    {u : Fin n} (h1 : e.mid.val < u.val) (h2 : u.val < e.j.val) (s : Side)
    (x : Letter) : edgeVerdict e s u x = 1 := by
  obtain ⟨hiq, hqj, -⟩ := hsp e
  have hun := u.isLt
  have hqn := e.mid.isLt
  simp only [edgeVerdict, specMiss, spec1, spec2, spec3,
    eq_false (show ¬(u.val < e.i.val) from by omega),
    eq_false (show ¬(u.val = e.i.val) from by omega),
    eq_true (show n - 1 - u.val < n - 1 - e.mid.val from by omega),
    eq_true h2,
    true_or, false_or, false_and, if_true, if_false]

theorem edgeVerdict_at_i_left {e : EdgePair n G} (hsp : SpreadEdges n G)
    (x : Letter) :
    edgeVerdict e Side.left e.i x = if x = .A then 1 else 2 := by
  obtain ⟨hiq, hqj, -⟩ := hsp e
  have hin := e.i.isLt
  have hqn := e.mid.isLt
  simp only [edgeVerdict, specMiss, spec1, spec2, spec3,
    eq_false (show ¬(e.i.val < e.i.val) from by omega),
    eq_false (show ¬(n - 1 - e.i.val < n - 1 - e.mid.val) from by omega),
    eq_false (show ¬(n - 1 - e.i.val = n - 1 - e.mid.val) from by omega),
    eq_true (show e.i.val < e.j.val from by omega),
    true_or, false_or, false_and, if_true, if_false]
  cases x <;> decide

theorem edgeVerdict_at_i_right {e : EdgePair n G} (hsp : SpreadEdges n G)
    (x : Letter) :
    edgeVerdict e Side.right e.i x = if x = .C ∨ x = .D then 2 else 1 := by
  obtain ⟨hiq, hqj, -⟩ := hsp e
  have hin := e.i.isLt
  have hqn := e.mid.isLt
  simp only [edgeVerdict, specMiss, spec1, spec2, spec3,
    eq_false (show ¬(e.i.val < e.i.val) from by omega),
    eq_false (show ¬(n - 1 - e.i.val < n - 1 - e.mid.val) from by omega),
    eq_false (show ¬(n - 1 - e.i.val = n - 1 - e.mid.val) from by omega),
    eq_true (show e.i.val < e.j.val from by omega),
    true_or, false_or, false_and, if_true, if_false]
  cases x <;> decide

theorem edgeVerdict_at_j_left {e : EdgePair n G} (hsp : SpreadEdges n G)
    (x : Letter) :
    edgeVerdict e Side.left e.j x = if x = .F then 2 else 1 := by
  obtain ⟨hiq, hqj, -⟩ := hsp e
  have hjn := e.j.isLt
  have hqn := e.mid.isLt
  simp only [edgeVerdict, specMiss, spec1, spec2, spec3,
    eq_false (show ¬(e.j.val < e.i.val) from by omega),
    eq_false (show ¬(e.j.val = e.i.val) from by omega),
    eq_true (show n - 1 - e.j.val < n - 1 - e.mid.val from by omega),
    eq_false (show ¬(e.j.val < e.j.val) from by omega),
    true_or, false_or, false_and, if_true, if_false]
  cases x <;> decide

theorem edgeVerdict_at_j_right {e : EdgePair n G} (hsp : SpreadEdges n G)
    (x : Letter) :
    edgeVerdict e Side.right e.j x = if x = .C ∨ x = .D then 1 else 2 := by
  obtain ⟨hiq, hqj, -⟩ := hsp e
  have hjn := e.j.isLt
  have hqn := e.mid.isLt
  simp only [edgeVerdict, specMiss, spec1, spec2, spec3,
    eq_false (show ¬(e.j.val < e.i.val) from by omega),
    eq_false (show ¬(e.j.val = e.i.val) from by omega),
    eq_true (show n - 1 - e.j.val < n - 1 - e.mid.val from by omega),
    eq_false (show ¬(e.j.val < e.j.val) from by omega),
    true_or, false_or, false_and, if_true, if_false]
  cases x <;> decide

end Hardness
