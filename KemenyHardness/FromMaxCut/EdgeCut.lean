import KemenyHardness.FromMaxCut.EdgeCost

/-!
# The cut structure of an edge candidate in a block ranking

Fourth step of the reverse direction. On a block ranking every supercandidate
compares uniformly against an edge candidate — the edge candidate is an
outsider to every super — so each super sits *entirely* above or entirely
below it (`EdgeAbove`), and the interpolated cost of `EdgeCost.lean`
collapses to its endpoints: `M · (verdict − 1)` above, `M · (2 − verdict)`
below (`sum_ve_pair_cost_block`).

When the vertex part moreover agrees with an output spec (`VertexAgree`), the
supers above an edge candidate form an up-set of the output chain, by
transitivity. Reading positions through `superHeight` — the bijection of the
`6n` supers with `0, …, 6n − 1` in output-chain order — an up-set is a height
*prefix*: the above-set is exactly `superHeight < t` for a single cut
position `t ≤ 6n` (`exists_edgeAbove_iff_height_lt`). The edge candidate's
whole cost against the vertex block is therefore `M` times a cut sum of
verdict disagreements (`exists_sum_ve_cost_eq_cut`): verdict-`2` supers above
the cut plus verdict-`1` supers below it. Lower-bounding that cut sum over
all `t` is the walk analysis of the next file — note the height granularity
already accounts for cuts *inside* a gadget, so no separate letter-level
split analysis is needed.
-/

namespace Hardness

open Finset

variable {n M : ℕ} {G : SimpleGraph (Fin n)}

/-! ## Supers sit entirely above or entirely below an edge candidate -/

/-- The supercandidate `(u, x)` sits entirely above the edge candidate
`(e, s)`. On a block ranking any single member comparison decides it
(`blockAt_edgeAbove_iff`). -/
def EdgeAbove (r : LinearOrder (Cand n M G)) (e : EdgePair n G) (s : Side)
    (u : Fin n) (x : Letter) : Prop :=
  ∀ m : Fin M, r.lt (Sum.inl (u, x, m)) (Sum.inr (e, s))

instance (r : LinearOrder (Cand n M G)) (e : EdgePair n G) (s : Side)
    (u : Fin n) (x : Letter) : Decidable (EdgeAbove r e s u x) :=
  letI := r.toDecidableLT
  inferInstanceAs (Decidable (∀ m : Fin M, r.lt (Sum.inl (u, x, m)) (Sum.inr (e, s))))

/-- An edge candidate is an outsider to every super, so a block compares
uniformly against it: one member comparison decides the whole super. -/
theorem blockAt_edgeAbove_iff {r : LinearOrder (Cand n M G)} {u : Fin n}
    {x : Letter} (hb : BlockAt r u x) {e : EdgePair n G} {s : Side} (m : Fin M) :
    r.lt (Sum.inl (u, x, m)) (Sum.inr (e, s)) ↔ EdgeAbove r e s u x :=
  ⟨fun h m' ↦ (hb.2 _ inr_not_mem_super m m').mp h, fun h ↦ h m⟩

/-- On a block ranking, the members above an edge candidate are all of them
or none: supercandidates never split. -/
theorem aboveCount_block {r : LinearOrder (Cand n M G)} {u : Fin n}
    {x : Letter} (hb : BlockAt r u x) (e : EdgePair n G) (s : Side) :
    aboveCount r e s u x = if EdgeAbove r e s u x then M else 0 := by
  letI := r.toDecidableLT
  by_cases h : EdgeAbove r e s u x
  · rw [if_pos h, aboveCount, Finset.filter_true_of_mem fun m _ ↦ h m,
      Finset.card_univ, Fintype.card_fin]
  · rw [if_neg h, aboveCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun m _ hm ↦ h ((blockAt_edgeAbove_iff hb m).mp hm)

/-- **One supercandidate's cost against an edge candidate, on a block
ranking**: the interpolation collapses to its endpoints — `M · (verdict − 1)`
entirely above, `M · (2 − verdict)` entirely below. -/
theorem sum_ve_pair_cost_block (hsp : SpreadEdges n G)
    {r : LinearOrder (Cand n M G)} {u : Fin n} {x : Letter}
    (hb : BlockAt r u x) (e : EdgePair n G) (s : Side) :
    ∑ m : Fin M,
      (orientedMargin (kemenyProfile n G M) r (Sum.inl (u, x, m)) (Sum.inr (e, s))
        + orientedMargin (kemenyProfile n G M) r (Sum.inr (e, s)) (Sum.inl (u, x, m)))
      = M * (if EdgeAbove r e s u x then edgeVerdict e s u x - 1
          else 2 - edgeVerdict e s u x) := by
  rw [sum_ve_pair_cost_super hsp r e s u x, aboveCount_block hb e s]
  by_cases h : EdgeAbove r e s u x
  · rw [if_pos h, if_pos h, Nat.sub_self, Nat.zero_mul, Nat.add_zero]
  · rw [if_neg h, if_neg h, Nat.zero_mul, Nat.zero_add, Nat.sub_zero]

/-! ## Super heights along the output chain -/

theorem outPos_lt_six (b : Bool) (x : Letter) :
    (if b then outPosL else outPosR) x < 6 := by
  cases b <;> cases x <;> decide

theorem outPos_surj :
    ∀ (b : Bool) (p : Fin 6), ∃ x : Letter, (if b then outPosL else outPosR) x = p.val := by
  decide

/-- The height of a supercandidate in the output chain of the colouring `χ`:
gadgets ascending, six letters per gadget in the side's local order. A
bijection of the `6n` supers with `0, …, 6n − 1`, respecting the output
spec's order (`outSpec_lt_of_superHeight_lt`). -/
def superHeight (χ : Fin n → Bool) (u : Fin n) (x : Letter) : ℕ :=
  6 * u.val + (if χ u then outPosL else outPosR) x

theorem superHeight_lt_six_mul (χ : Fin n → Bool) (u : Fin n) (x : Letter) :
    superHeight χ u x < 6 * n := by
  have h1 := outPos_lt_six (χ u) x
  have h2 := u.isLt
  rw [superHeight]
  omega

theorem superHeight_injective (χ : Fin n → Bool) :
    Function.Injective fun p : Fin n × Letter ↦ superHeight χ p.1 p.2 := by
  rintro ⟨u, x⟩ ⟨u', x'⟩ h
  simp only [superHeight] at h
  have h1 := outPos_lt_six (χ u) x
  have h2 := outPos_lt_six (χ u') x'
  obtain rfl : u = u' := Fin.ext (by omega)
  refine Prod.ext rfl ?_
  have hxx : (if χ u then outPosL else outPosR) x
      = (if χ u then outPosL else outPosR) x' := by omega
  by_cases hb : χ u = true
  · rw [if_pos hb] at hxx
    exact outPosL_inj hxx
  · rw [if_neg hb] at hxx
    exact outPosR_inj hxx

theorem superHeight_surj (χ : Fin n → Bool) {t : ℕ} (ht : t < 6 * n) :
    ∃ (u : Fin n) (x : Letter), superHeight χ u x = t := by
  have hu : t / 6 < n := by omega
  obtain ⟨x, hx⟩ := outPos_surj (χ ⟨t / 6, hu⟩) ⟨t % 6, by omega⟩
  refine ⟨⟨t / 6, hu⟩, x, ?_⟩
  rw [superHeight, hx]
  change 6 * (t / 6) + t % 6 = t
  omega

/-- Heights order supercandidates as the output spec does — with any member
indices, since distinct supers never compare by member. -/
theorem outSpec_lt_of_superHeight_lt {χ : Fin n → Bool} {u u' : Fin n}
    {x x' : Letter} (h : superHeight χ u x < superHeight χ u' x') (m m' : Fin M) :
    ((outSpec n G χ).ranking M).lt (Sum.inl (u, x, m)) (Sum.inl (u', x', m')) := by
  rw [VoterSpec.lt_vertex_vertex]
  simp only [outSpec]
  rw [superHeight, superHeight] at h
  have h1 := outPos_lt_six (χ u) x
  have h2 := outPos_lt_six (χ u') x'
  rcases Nat.lt_or_ge u.val u'.val with hlt | hge
  · exact Or.inl hlt
  · exact Or.inr ⟨by omega, Or.inl (by omega)⟩

/-- The supers above an edge candidate form a height up-set when the vertex
part agrees with the output spec: whatever is spec-higher than a super above
the edge candidate is above it too, by transitivity. -/
theorem edgeAbove_of_superHeight_lt {r : LinearOrder (Cand n M G)}
    {χ : Fin n → Bool} (hva : VertexAgree r χ) {e : EdgePair n G} {s : Side}
    {u u' : Fin n} {x x' : Letter} (ha : EdgeAbove r e s u' x')
    (h : superHeight χ u x < superHeight χ u' x') : EdgeAbove r e s u x :=
  fun m ↦ ranks_trans
    ((hva u x m u' x' m).mpr (outSpec_lt_of_superHeight_lt h m m)) (ha m)

/-- A downward-closed finite set of naturals is an initial range. -/
private theorem eq_range_card_of_downward_closed {S : Finset ℕ}
    (hdc : ∀ a b : ℕ, a ≤ b → b ∈ S → a ∈ S) : S = Finset.range S.card := by
  have hlt : ∀ a ∈ S, a < S.card := by
    intro a ha
    have hsub : Finset.range (a + 1) ⊆ S := fun b hb ↦
      hdc b a (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)) ha
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_range] at hcard
    omega
  exact Finset.eq_of_subset_of_card_le
    (fun a ha ↦ Finset.mem_range.mpr (hlt a ha)) (le_of_eq (Finset.card_range _))

/-- **The cut position of an edge candidate**: on a ranking whose vertex part
agrees with the output spec, the supercandidates above an edge candidate are
exactly a height prefix — described by a single cut position `t`. -/
theorem exists_edgeAbove_iff_height_lt {r : LinearOrder (Cand n M G)}
    {χ : Fin n → Bool} (hva : VertexAgree r χ) (e : EdgePair n G) (s : Side) :
    ∃ t ≤ 6 * n, ∀ (u : Fin n) (x : Letter),
      (EdgeAbove r e s u x ↔ superHeight χ u x < t) := by
  set S : Finset ℕ := (Finset.univ.filter fun p : Fin n × Letter ↦
    EdgeAbove r e s p.1 p.2).image (fun p ↦ superHeight χ p.1 p.2) with hS
  have hmem : ∀ (u : Fin n) (x : Letter),
      superHeight χ u x ∈ S ↔ EdgeAbove r e s u x := by
    intro u x
    simp only [hS, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨p, hp, hph⟩
      obtain rfl : p = (u, x) := superHeight_injective χ hph
      exact hp
    · exact fun h ↦ ⟨(u, x), h, rfl⟩
  have hdc : ∀ a b : ℕ, a ≤ b → b ∈ S → a ∈ S := by
    intro a b hab hb
    rcases hab.lt_or_eq with hlt | rfl
    · simp only [hS, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
        true_and] at hb
      obtain ⟨p, hp, hph⟩ := hb
      have hb6 : b < 6 * n := hph ▸ superHeight_lt_six_mul χ p.1 p.2
      obtain ⟨u₀, x₀, hux⟩ := superHeight_surj χ (lt_trans hlt hb6)
      have ha : EdgeAbove r e s u₀ x₀ :=
        edgeAbove_of_superHeight_lt hva hp (by rw [hux, hph]; exact hlt)
      rw [← hux]
      exact (hmem u₀ x₀).mpr ha
    · exact hb
  have hsub : S ⊆ Finset.range (6 * n) := by
    intro a ha
    simp only [hS, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and] at ha
    obtain ⟨p, -, hph⟩ := ha
    rw [Finset.mem_range, ← hph]
    exact superHeight_lt_six_mul χ p.1 p.2
  have hrange := eq_range_card_of_downward_closed hdc
  refine ⟨S.card, ?_, fun u x ↦ ?_⟩
  · have hle := Finset.card_le_card hsub
    rw [Finset.card_range] at hle
    exact hle
  · constructor
    · intro h
      have hin := (hmem u x).mpr h
      rw [hrange, Finset.mem_range] at hin
      exact hin
    · intro h
      refine (hmem u x).mp ?_
      rw [hrange, Finset.mem_range]
      exact h

/-! ## The whole vertex-block cost of an edge candidate, as a cut sum -/

/-- **The edge candidate's vertex-block cost is a cut sum**: `M` times the
verdict disagreements across a single cut position — verdict-`2` supers above
the cut plus verdict-`1` supers below it. The walk bounds of the next file
lower-bound the cut sum over all `t`. -/
theorem exists_sum_ve_cost_eq_cut (hsp : SpreadEdges n G)
    {r : LinearOrder (Cand n M G)} (hb : ∀ u x, BlockAt r u x)
    {χ : Fin n → Bool} (hva : VertexAgree r χ) (e : EdgePair n G) (s : Side) :
    ∃ t ≤ 6 * n,
      (∑ u : Fin n, ∑ x : Letter, ∑ m : Fin M,
        (orientedMargin (kemenyProfile n G M) r (Sum.inl (u, x, m)) (Sum.inr (e, s))
          + orientedMargin (kemenyProfile n G M) r (Sum.inr (e, s)) (Sum.inl (u, x, m))))
      = M * ∑ u : Fin n, ∑ x : Letter,
          (if superHeight χ u x < t then edgeVerdict e s u x - 1
            else 2 - edgeVerdict e s u x) := by
  obtain ⟨t, ht, hcut⟩ := exists_edgeAbove_iff_height_lt hva e s
  refine ⟨t, ht, ?_⟩
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [sum_ve_pair_cost_block hsp (hb u x) e s]
  exact congrArg (M * ·) (if_congr (hcut u x) rfl rfl)

end Hardness
