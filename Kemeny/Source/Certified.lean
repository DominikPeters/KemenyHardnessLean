import Kemeny.Source
import HardnessReductions.Graph.Encoding

/-!
# Certifying the numbering hop: SIMPLE MAX CUT → SIMPLE MAX CUT with long even edges

The source reduction of the Kemeny project (`Kemeny/Source.lean`) relabels a
graph so that every edge becomes *long and even*: number the vertices, stretch
by six, and every label is an even multiple of six, so distinct labels differ
by at least six. This file certifies that hop at the concrete level.

Concrete numbered instances reuse `GraphTy`: a `NumberedGraphInstance` is
decoded from `(vertices, (edges, k))` exactly as a `GraphThresholdInstance` is,
reading the vertex count off the list length (`decodeNumbered`). The program
`stretchCode` stretches the vertex list sixfold (only its length matters — the
labels are junk) and maps every raw edge `(a, b)` to `(6a, 6b)`.

The decoded output graph is not syntactically `numberMap (decodeGraph x)` — the
abstract map numbers through `Fintype.equivFin`, whereas the program uses the
identity numbering of the positions. But both are pushforwards of the decoded
graph along a sixfold embedding, so the cut objective is preserved
(`exists_le_cutSize_map_iff`, generic over the embedding) and every image edge
is long and even. That is all the correctness `iff` needs; going *into* the
restriction is free, since long-even-ness of the outputs is just a conjunct.
-/

namespace Hardness
namespace Cert

open Finset

/-! ## Decoding a numbered instance -/

/-- Decode a concrete instance `(vertices, (edges, k))` as a
`NumberedGraphInstance`: the vertices are the positions of the vertex list (the
list length is the vertex count), edges are index pairs, junk ignored. The
numbered twin of `decodeGraph`, differing only in the target structure. -/
def decodeNumbered (x : GraphTy.denote) : NumberedGraphInstance where
  n := x.1.length
  G := SimpleGraph.fromRel fun i j : Fin x.1.length ↦ (i.val, j.val) ∈ x.2.1
  k := x.2.2

/-- Adjacency in a decoded numbered graph, unfolded: distinct positions joined
by a raw edge in either orientation. -/
theorem decodeNumbered_adj (x : GraphTy.denote) (u v : Fin x.1.length) :
    (decodeNumbered x).G.Adj u v ↔
      u ≠ v ∧ ((u.val, v.val) ∈ x.2.1 ∨ (v.val, u.val) ∈ x.2.1) := by
  rw [show (decodeNumbered x).G = SimpleGraph.fromRel
    (fun i j : Fin x.1.length ↦ (i.val, j.val) ∈ x.2.1) from rfl, SimpleGraph.fromRel_adj]

/-! ## The stretch program -/

/-- The vertex list stretched sixfold: cross the vertex list with a fixed
six-element list and keep the first components. Only the length matters — it
becomes `|vertices| * 6` — so the labels are discarded (`decodeNumbered` reads
positions, not labels). -/
def stretchVerts : Code GraphTy (.list .nat) :=
  .comp (.pair gVertices (.const (.list .nat) [0, 0, 0, 0, 0, 0]))
    (.comp Code.cross (.listMap .fst))

/-- Every raw edge `(a, b)` mapped to `(6a, 6b)`. -/
def stretchEdges : Code GraphTy (.list (.pair .nat .nat)) :=
  .comp gEdges (.listMap (.pair (Code.mul (.const .nat 6) .fst) (Code.mul (.const .nat 6) .snd)))

/-- The instance map: stretch the vertices sixfold, map the edges `(a, b) ↦
(6a, 6b)`, keep the threshold. -/
def stretchCode : Code GraphTy GraphTy :=
  .pair stretchVerts (.pair stretchEdges gThreshold)

/-- The stretched vertex list has length `|vertices| * 6`. -/
theorem stretchCode_verts_length (x : GraphTy.denote) :
    (stretchCode.eval x).1.length = x.1.length * 6 := by
  change ((Code.cross.eval (x.1, [0, 0, 0, 0, 0, 0])).map Prod.fst).length = x.1.length * 6
  rw [List.length_map, length_cross_eval]
  rfl

/-- The stretched edge list maps every raw edge `(a, b)` to `(6a, 6b)`. -/
theorem stretchCode_edges (x : GraphTy.denote) :
    (stretchCode.eval x).2.1 = x.2.1.map fun e ↦ (6 * e.1, 6 * e.2) := rfl

/-- Membership in the stretched edge list, with `ℕ`-typed witnesses (so
`omega` sees the label arithmetic): `(s, t)` is a stretched edge iff it is
`(6a, 6b)` for a raw edge `(a, b)`. -/
theorem mem_stretchCode_edges (x : GraphTy.denote) (s t : ℕ) :
    (s, t) ∈ (stretchCode.eval x).2.1 ↔
      ∃ a b : ℕ, (a, b) ∈ x.2.1 ∧ s = 6 * a ∧ t = 6 * b := by
  rw [stretchCode_edges]
  constructor
  · intro h
    obtain ⟨⟨a, b⟩, hmem, heq⟩ := List.mem_map.mp h
    simp only [Prod.mk.injEq] at heq
    exact ⟨a, b, hmem, heq.1.symm, heq.2.symm⟩
  · rintro ⟨a, b, hmem, rfl, rfl⟩
    exact List.mem_map.mpr ⟨(a, b), hmem, rfl⟩

/-- The threshold passes through the stretch unchanged. -/
theorem stretchCode_threshold (x : GraphTy.denote) :
    (stretchCode.eval x).2.2 = x.2.2 := rfl

/-! ## The sixfold embedding and the graph equality -/

/-- The sixfold embedding of the decoded positions into the stretched label
space: position `i` becomes label `6 * i`. -/
def stretchEmb (x : GraphTy.denote) :
    (decodeGraph x).V ↪ Fin (decodeNumbered (stretchCode.eval x)).n where
  toFun i := ⟨6 * i.val, by
    have h := stretchCode_verts_length x
    have := i.isLt
    change 6 * i.val < (stretchCode.eval x).1.length
    omega⟩
  inj' i j h := by
    simp only [Fin.mk.injEq] at h
    exact Fin.ext (by omega)

theorem stretchEmb_apply (x : GraphTy.denote) (i : (decodeGraph x).V) :
    ((stretchEmb x) i).val = 6 * i.val := rfl

/-- **The decoded stretched graph is the sixfold pushforward of the decoded
input graph.** Both put an edge between labels `6a` and `6b` exactly when the
input has an edge between positions `a` and `b`. -/
theorem decodeNumbered_stretch_G (x : GraphTy.denote) :
    (decodeNumbered (stretchCode.eval x)).G = (decodeGraph x).G.map (stretchEmb x) := by
  ext p q
  rw [decodeNumbered_adj, SimpleGraph.map_adj]
  have hlen : (decodeNumbered (stretchCode.eval x)).n = x.1.length * 6 :=
    stretchCode_verts_length x
  have hp := p.isLt; have hq := q.isLt
  constructor
  · rintro ⟨hne, hor⟩
    rcases hor with hm | hm
    · obtain ⟨a, b, hemem, h1, h2⟩ := (mem_stretchCode_edges x p.val q.val).mp hm
      have hb1 : a < x.1.length := by omega
      have hb2 : b < x.1.length := by omega
      refine ⟨⟨a, hb1⟩, ⟨b, hb2⟩, ?_, Fin.ext h1.symm, Fin.ext h2.symm⟩
      rw [decodeGraph_adj]
      exact ⟨fun hc ↦ hne (Fin.ext (by have h : a = b := congrArg Fin.val hc; omega)), Or.inl hemem⟩
    · obtain ⟨a, b, hemem, h1, h2⟩ := (mem_stretchCode_edges x q.val p.val).mp hm
      have hb1 : a < x.1.length := by omega
      have hb2 : b < x.1.length := by omega
      refine ⟨⟨b, hb2⟩, ⟨a, hb1⟩, ?_, Fin.ext h2.symm, Fin.ext h1.symm⟩
      rw [decodeGraph_adj]
      exact ⟨fun hc ↦ hne (Fin.ext (by have h : b = a := congrArg Fin.val hc; omega)), Or.inr hemem⟩
  · rintro ⟨u, v, hadj, hu, hv⟩
    rw [decodeGraph_adj] at hadj
    obtain ⟨huv, hor⟩ := hadj
    have hpu : 6 * u.val = p.val := (stretchEmb_apply x u).symm.trans (congrArg Fin.val hu)
    have hqv : 6 * v.val = q.val := (stretchEmb_apply x v).symm.trans (congrArg Fin.val hv)
    refine ⟨fun hpq ↦ huv (Fin.ext (by have h := congrArg Fin.val hpq; omega)), ?_⟩
    rcases hor with hm | hm
    · exact Or.inl ((mem_stretchCode_edges x p.val q.val).mpr
        ⟨u.val, v.val, hm, hpu.symm, hqv.symm⟩)
    · exact Or.inr ((mem_stretchCode_edges x q.val p.val).mpr
        ⟨v.val, u.val, hm, hqv.symm, hpu.symm⟩)

/-! ## Long even edges -/

/-- **Every edge of the decoded stretched graph is long and even.** Its
endpoint labels are distinct multiples of six, so they differ by at least six
and their sum is even. -/
theorem longEvenEdges_stretch (x : GraphTy.denote) :
    LongEvenEdges (decodeNumbered (stretchCode.eval x)) := by
  intro i j hadj hlt
  rw [decodeNumbered_adj] at hadj
  obtain ⟨-, hor⟩ := hadj
  rcases hor with hm | hm
  · obtain ⟨a, b, -, h1, h2⟩ := (mem_stretchCode_edges x i.val j.val).mp hm
    omega
  · obtain ⟨a, b, -, h1, h2⟩ := (mem_stretchCode_edges x j.val i.val).mp hm
    omega

/-! ## Cut objective transfer -/

/-- The cut objective does not depend on the choice of decidability instance:
two decidability instances for the same graph give the same cut. -/
theorem cutSize_congr {V : Type*} [Fintype V] {G H : SimpleGraph V}
    [DecidableRel G.Adj] [DecidableRel H.Adj] (h : G = H) (χ : V → Bool) :
    cutSize G χ = cutSize H χ := by
  subst h
  congr 1

/-- **The stretched numbered instance has a `k`-cut iff the input does.** The
decoded graph is a sixfold pushforward, so `exists_le_cutSize_map_iff` transfers
the cut. -/
theorem simpleMaxCutNumbered_stretch_iff (x : GraphTy.denote) :
    SIMPLE_MAX_CUT_NUMBERED (decodeNumbered (stretchCode.eval x))
      ↔ SIMPLE_MAX_CUT (decodeGraph x) := by
  have hcong : ∀ χ, cutSize (decodeNumbered (stretchCode.eval x)).G χ
      = cutSize ((decodeGraph x).G.map (stretchEmb x)) χ :=
    fun χ ↦ cutSize_congr (decodeNumbered_stretch_G x) χ
  rw [SIMPLE_MAX_CUT_NUMBERED]
  simp only [hcong]
  exact exists_le_cutSize_map_iff (decodeGraph x).G (stretchEmb x) (decodeGraph x).k

/-! ## The concrete problem and the certified reduction -/

namespace Concrete

/-- SIMPLE MAX CUT with long even edges, on concrete instances. -/
def SIMPLE_MAX_CUT_LEE : Problem GraphTy.denote :=
  Hardness.SIMPLE_MAX_CUT_LEE.comap decodeNumbered

end Concrete

/-- **The numbering hop, certified**: `stretchCode` reduces concrete SIMPLE MAX
CUT to concrete SIMPLE MAX CUT with long even edges. -/
def smcToLeeCertified :
    CertifiedReduction Concrete.SIMPLE_MAX_CUT Concrete.SIMPLE_MAX_CUT_LEE where
  code := stretchCode
  correct x := by
    rw [Concrete.SIMPLE_MAX_CUT_LEE, Problem.comap, Hardness.SIMPLE_MAX_CUT_LEE,
      Problem.restrict, and_iff_right (longEvenEdges_stretch x)]
    exact (simpleMaxCutNumbered_stretch_iff x).symm

end Cert
end Hardness
