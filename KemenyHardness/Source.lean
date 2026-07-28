import HardnessReductions.Graph.MaxCut

/-!
# SIMPLE MAX CUT on numbered vertices, with long even edges

The source problem of the Kemeny reduction. The paper reduces to Kemeny from
SIMPLE MAX CUT restricted to instances whose edges are *long and even*: the two
endpoint labels of every edge differ by at least six and have even sum. The
catalog's `SIMPLE_MAX_CUT` cannot even state that restriction — its vertex type
is abstract, and the condition speaks about *numeric labels*. So this file
introduces a numbered instance type (`NumberedGraphInstance`, vertices `Fin n`),
restates the problem on it (`SIMPLE_MAX_CUT_NUMBERED`), states the restriction
(`LongEvenEdges`, `SIMPLE_MAX_CUT_LEE`), and proves the restricted problem hard
by reduction from the catalog entry.

The instance map is a relabeling: number the vertices through
`Fintype.equivFin` and stretch by six, so vertex `v` becomes label `6 * (e v)`
inside `Fin (6 * m)`. Distinct labels then differ by at least six and every
label is even, which is `LongEvenEdges` on the nose; the labels skipped by the
stretch are isolated vertices, which cost nothing — isolated vertices are
represented anyway under the library's explicit-vertex-list discipline. The
workhorse is `cutSize_map`: pushing a graph forward along an injective
embedding leaves the cut objective unchanged, because the edges correspond one
for one — the counting analogue of the entry's `cutSize_eq_of_equiv`, for
embeddings instead of bijections.
-/

namespace Hardness

/-! ## Numbered instances -/

/-- An instance of a graph problem whose vertices are *numbers*: a graph on
`Fin n` with decidable adjacency, together with a threshold `k`. The numbered
twin of `GraphThresholdInstance`, needed because the long-even-edges
restriction constrains the numeric labels of adjacent vertices — a condition
the abstract vertex type cannot express. No `Fintype`/`DecidableEq` fields:
`Fin n` carries both. -/
structure NumberedGraphInstance where
  /-- The number of vertices; the vertices are `Fin n`. -/
  n : ℕ
  /-- The graph on the numeric labels. -/
  G : SimpleGraph (Fin n)
  [decAdj : DecidableRel G.Adj]
  /-- The threshold. -/
  k : ℕ

attribute [instance] NumberedGraphInstance.decAdj

/-- **SIMPLE MAX CUT**, on numbered instances: is there a bipartition of the
labels crossed by at least `k` edges? The same question as the catalog's
`SIMPLE_MAX_CUT`, asked of a `NumberedGraphInstance` so that restrictions on
the labels can be stated. -/
def SIMPLE_MAX_CUT_NUMBERED : Problem NumberedGraphInstance :=
  fun x ↦ ∃ χ : Fin x.n → Bool, x.k ≤ cutSize x.G χ

/-- The long-even-edges restriction: the endpoints of every edge are at least
six apart, and their sum is even. Stated with the guard `i < j`, which makes
the symmetric cases free — the condition on `{i, j}` is checked once, in the
increasing orientation. -/
def LongEvenEdges (x : NumberedGraphInstance) : Prop :=
  ∀ i j : Fin x.n, x.G.Adj i j → i.val < j.val → i.val + 6 ≤ j.val ∧ 2 ∣ (i.val + j.val)

/-- **SIMPLE MAX CUT with long even edges**: SIMPLE MAX CUT on numbered
instances, hard even if every edge is long and even. The source problem of the
Kemeny reduction.

Hardness proof: from SIMPLE MAX CUT (`simpleMaxCutToLee` below). -/
def SIMPLE_MAX_CUT_LEE : Problem NumberedGraphInstance :=
  SIMPLE_MAX_CUT_NUMBERED.restrict LongEvenEdges

/-! ## Cuts of mapped graphs -/

/-- Adjacency in the pushforward of a graph along a function is decidable: it
is a bounded search for a preimage edge. Mathlib's `instDecidableMapAdj` asks
for decidability of the underlying `Relation.Map`, which instance search never
finds; this instance decides the unfolded existential directly. -/
instance decidableMapAdj {V W : Type*} [Fintype V] [DecidableEq W]
    {G : SimpleGraph V} [DecidableRel G.Adj] {f : V → W} :
    DecidableRel (G.map f).Adj := fun a b ↦
  decidable_of_iff (a ≠ b ∧ ∃ u v : V, G.Adj u v ∧ f u = a ∧ f v = b)
    (SimpleGraph.map_adj' f G a b).symm

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W]

/-- **The cut objective survives an injective pushforward**: cutting `G.map f`
with `χ` is cutting `G` with `χ` read through `f`. The counting analogue of
`cutSize_eq_of_equiv` for embeddings — the edges of `G.map f` are exactly the
`Sym2.map f` images of the edges of `G`, one for one, and whether an edge
crosses is a function of its endpoint colours only. -/
theorem cutSize_map (G : SimpleGraph V) [DecidableRel G.Adj] (f : V ↪ W) (χ : W → Bool) :
    cutSize (G.map f) χ = cutSize G fun v ↦ χ (f v) := by
  rw [cutSize, cutSize]
  refine (Finset.card_nbij (Sym2.map f) ?_ ?_ ?_).symm
  · intro e he
    induction e using Sym2.ind with
    | _ u v =>
      rw [Finset.mem_coe, Finset.mem_filter, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet] at he
      rw [Sym2.map_mk, Finset.mem_coe, Finset.mem_filter, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet]
      exact ⟨SimpleGraph.map_adj_apply.mpr he.1, he.2⟩
  · exact (Sym2.map.injective f.injective).injOn
  · intro e he
    induction e using Sym2.ind with
    | _ a b =>
      rw [Finset.mem_coe, Finset.mem_filter, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet, SimpleGraph.map_adj] at he
      obtain ⟨⟨u, v, huv, hu, hv⟩, hcr⟩ := he
      subst hu; subst hv
      refine ⟨s(u, v), ?_, Sym2.map_mk ..⟩
      rw [Finset.mem_coe, Finset.mem_filter, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet]
      exact ⟨huv, hcr⟩

/-- **A `k`-cut exists in the pushforward iff one exists in the original.**
Forward, restrict the colouring along `f`; backward, extend it by `false` on
the labels outside the range — `cutSize_map` says neither move changes the
count, since the extension restricts back to the original colouring
(`Function.Injective.extend_apply`). -/
theorem exists_le_cutSize_map_iff (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : V ↪ W) (k : ℕ) :
    (∃ χ : W → Bool, k ≤ cutSize (G.map f) χ) ↔ ∃ χ : V → Bool, k ≤ cutSize G χ := by
  constructor
  · rintro ⟨χ, hχ⟩
    exact ⟨fun v ↦ χ (f v), by rwa [← cutSize_map G f χ]⟩
  · rintro ⟨χ, hχ⟩
    refine ⟨Function.extend f χ fun _ ↦ false, ?_⟩
    rw [cutSize_map]
    have hres : (fun v ↦ Function.extend f χ (fun _ ↦ false) (f v)) = χ := by
      funext v
      exact f.injective.extend_apply χ _ v
    rwa [hres]

/-! ## The reduction -/

/-- The label embedding: vertex `v` becomes label `6 * (e v)` inside
`Fin (6 * m)`, where `e` numbers the vertices through `Fintype.equivFin` and
`m` is the vertex count. Labels `0, 6, 12, …` — any two distinct labels differ
by at least six, and every label is even. -/
noncomputable def sixfoldEmbedding (x : GraphThresholdInstance) :
    x.V ↪ Fin (6 * Fintype.card x.V) where
  toFun v :=
    ⟨6 * (Fintype.equivFin x.V v).val, by have := (Fintype.equivFin x.V v).isLt; omega⟩
  inj' v w h := by
    simp only [Fin.mk.injEq] at h
    exact (Fintype.equivFin x.V).injective (Fin.ext (by omega))

/-- The instance map: push the graph forward along the sixfold embedding,
threshold unchanged. The labels skipped by the stretch are isolated vertices
of the image graph. -/
noncomputable def numberMap (x : GraphThresholdInstance) : NumberedGraphInstance where
  n := 6 * Fintype.card x.V
  G := x.G.map (sixfoldEmbedding x)
  k := x.k

/-- **The image instances have long even edges.** An edge of the mapped graph
joins two labels `6a` and `6b` with `a ≠ b` (adjacent vertices are distinct),
so the labels differ by at least six and their sum is even. -/
theorem longEvenEdges_numberMap (x : GraphThresholdInstance) :
    LongEvenEdges (numberMap x) := by
  intro i j hadj hlt
  obtain ⟨u, v, huv, hu, hv⟩ := (SimpleGraph.map_adj (sixfoldEmbedding x) x.G i j).mp hadj
  have hne : (Fintype.equivFin x.V u).val ≠ (Fintype.equivFin x.V v).val :=
    fun h ↦ x.G.ne_of_adj huv ((Fintype.equivFin x.V).injective (Fin.ext h))
  have hi : i.val = 6 * (Fintype.equivFin x.V u).val := by rw [← hu]; rfl
  have hj : j.val = 6 * (Fintype.equivFin x.V v).val := by rw [← hv]; rfl
  omega

/-- **Correctness of the instance map**: the numbered image has a `k`-cut iff
the original does — the pushforward step of `exists_le_cutSize_map_iff`,
specialized to the sixfold embedding. -/
theorem simpleMaxCutNumbered_numberMap_iff (x : GraphThresholdInstance) :
    SIMPLE_MAX_CUT_NUMBERED (numberMap x) ↔ SIMPLE_MAX_CUT x :=
  exists_le_cutSize_map_iff x.G (sixfoldEmbedding x) x.k

/-- **SIMPLE MAX CUT reduces to SIMPLE MAX CUT with long even edges**: the
relabeling is a correct reduction into the numbered problem whose outputs all
have long even edges, so it strengthens into the restriction
(`Reduction.codRestrict`). -/
noncomputable def simpleMaxCutToLee : SIMPLE_MAX_CUT ⟶ᵣ SIMPLE_MAX_CUT_LEE :=
  Reduction.codRestrict
    (⟨numberMap, fun x ↦ (simpleMaxCutNumbered_numberMap_iff x).symm⟩ :
      SIMPLE_MAX_CUT ⟶ᵣ SIMPLE_MAX_CUT_NUMBERED)
    LongEvenEdges longEvenEdges_numberMap

end Hardness
