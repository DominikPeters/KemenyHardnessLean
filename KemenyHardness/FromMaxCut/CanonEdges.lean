import KemenyHardness.Source.Certified
import KemenyHardness.FromMaxCut.Construction
import Mathlib.Data.List.NodupEquivFin

/-!
# The canonical edge list

Every downstream part of the Kemeny profile program reads the edges of the
decoded source graph *in one fixed order*: the candidate numbering assigns
`6nM + 2·(canon index) + side` to each edge candidate, the ballots splice the
edge candidates at their gadget positions in that order, and the budget sums
`6·span + 3` over that order. This file builds that order once, as a `Code`
program `canonEdges`, and proves the three facts the rest of phase 2 consumes:

* it is duplicate-free (`canonEdges_nodup`),
* its members are exactly the edges of the decoded numbered graph in increasing
  orientation (`mem_canonEdges`), and
* it is **lexicographically sorted** — strictly increasing in `K (s, t) = s·n +
  t` (`canonEdges_pairwise`).

The sortedness is what pins the ballots' within-gap edge order to the abstract
tie key `EdgePair.tie e s = 2·(e.i·n + e.j) + side`: two edge candidates sharing
a gadget slot are separated in a voter's ranking by `tie`, and the ballot lists
them in canonical-list order, so the two orders must coincide. `K` is exactly
the `e.i·n + e.j` of `tie`, so a `K`-sorted list makes the ballot order match
`tie` order with no reshuffling and no sort combinator (the language has
neither sort nor division).

Together, membership and nodup give the **enumeration bijection**
`edgePairEquiv` between the `EdgePair`s of the decoded graph — undirected edges
carried as `i < j` pairs — and the positions `Fin (canonEdges.eval x).length`
of the list, sending an edge to its index. This is the block that feeds
`Numbering.ofEquiv` when the candidate numbering is assembled.

## Construction

The edges are enumerated in lexicographic order directly, rather than read off
the raw edge list (whose order is arbitrary input):

1. **enumerate** — cross the position list `[0, …, n-1]` with itself, giving all
   index pairs `(i, j)` in lexicographic order;
2. **keep** — `canonKeep` retains `(i, j)` with `i < j` that name a genuine
   adjacency of the decoded graph (the raw list holds `(i, j)` or `(j, i)`).

The cross of a `Nodup` list with itself is `Nodup`, and lexicographic order and
sortedness are inherited from the cross and preserved by the filter, so no
`dedup` pass and no comparison of the raw edges is needed.
-/

namespace Hardness
namespace Cert

open Finset

/-! ## Two list identities -/

/-- `Code.cross` on two computed lists is mathlib's `List.product`. -/
theorem crossPP_eval (l₁ l₂ : List ℕ) :
    (Code.cross (σ := .nat) (τ := .nat)).eval (l₁, l₂) = l₁.product l₂ := by
  have h : (Code.cross (σ := .nat) (τ := .nat)).eval (l₁, l₂)
      = (l₁.map fun a ↦ l₂.map fun b ↦ (a, b)).flatten := rfl
  rw [h, List.product, List.flatMap_def]

/-- The lexicographic index `K (i, j) = i·m + j` enumerates `range n ×ˢ range m`
as `range (n·m)`: the product in lexicographic order is `0, 1, …, n·m − 1` under
`K`. This is why the canonical list, filtered from the product, is `K`-sorted. -/
theorem map_K_product (m : ℕ) : ∀ n : ℕ,
    ((List.range n).product (List.range m)).map (fun p : ℕ × ℕ ↦ p.1 * m + p.2)
      = List.range (n * m) := by
  intro n
  induction n with
  | zero => rw [Nat.zero_mul]; rfl
  | succ k ih =>
    have hsplit : (List.range (k + 1)).product (List.range m)
        = (List.range k).product (List.range m) ++ (List.range m).map (k, ·) := by
      rw [List.range_succ]; simp [List.product, List.flatMap_append]
    rw [hsplit, List.map_append, ih, List.map_map]
    have h2 : ((fun p : ℕ × ℕ ↦ p.1 * m + p.2) ∘ fun x ↦ (k, x)) = (fun x ↦ k * m + x) := by
      funext x; simp
    rw [h2, show (k + 1) * m = k * m + m by ring, List.range_add]

/-! ## The canonical edge list -/

/-- Keep-test for a candidate index pair `(i, j)` against the raw edge list `E`
(threaded as environment): increasing (`i < j`) and a genuine adjacency (`(i,
j)` or `(j, i)` in `E`). -/
def canonKeep : Code (.pair (.list (.pair .nat .nat)) (.pair .nat .nat)) .bool :=
  .comp
    (.pair
      (.comp (.pair (.comp .snd .fst) (.comp .snd .snd)) Code.natLt)
      (.comp
        (.pair (.comp (.pair .snd .fst) memEdge)
          (.comp (.pair (.pair (.comp .snd .snd) (.comp .snd .fst)) .fst) memEdge))
        .boolOr))
    .boolAnd

/-- `canonKeep` decides increasing genuine adjacency. -/
theorem canonKeep_eval_true (E : List (ℕ × ℕ)) (q : ℕ × ℕ) :
    canonKeep.eval (E, q) = true ↔ q.1 < q.2 ∧ (q ∈ E ∨ (q.2, q.1) ∈ E) := by
  have h : canonKeep.eval (E, q) =
      (Code.natLt.eval (q.1, q.2) && (memEdge.eval (q, E) || memEdge.eval ((q.2, q.1), E))) := rfl
  rw [h, Bool.and_eq_true, Bool.or_eq_true, natLt_eval_true, memEdge_eval_true, memEdge_eval_true]

/-- The canonical edge list: enumerate the index pairs in lexicographic order
(the self-cross of the position list) and keep the increasing genuine
adjacencies. One increasing pair per edge of the decoded graph, in the fixed
lexicographic order that all of phase 2 reads. -/
def canonEdges : Code GraphTy (.list (.pair .nat .nat)) :=
  .comp (.pair gEdges (.comp (.pair positions positions) Code.cross)) (Code.filterEnv canonKeep)

/-- The canonical edge list is the lexicographic index-pair enumeration filtered
by `canonKeep`. -/
theorem canonEdges_eval (x : GraphTy.denote) :
    canonEdges.eval x =
      ((List.range x.1.length).product (List.range x.1.length)).filter
        (fun q ↦ canonKeep.eval (x.2.1, q)) := by
  have h : canonEdges.eval x =
      (Code.filterEnv canonKeep).eval
        (gEdges.eval x, Code.cross.eval (positions.eval x, positions.eval x)) := rfl
  rw [h, filterEnv_eval, crossPP_eval, positions_eval]; rfl

/-- **The canonical edge list is duplicate-free.** -/
theorem canonEdges_nodup (x : GraphTy.denote) : (canonEdges.eval x).Nodup := by
  rw [canonEdges_eval]
  exact (List.nodup_range.product List.nodup_range).filter _

/-- **Membership in the canonical edge list**: `(s, t)` is a canonical edge iff
it is an increasing pair naming an edge of the decoded graph (in range,
off-diagonal, present in the raw list in either orientation). -/
theorem mem_canonEdges (x : GraphTy.denote) (s t : ℕ) :
    (s, t) ∈ canonEdges.eval x ↔
      s < t ∧ s < x.1.length ∧ t < x.1.length ∧ ((s, t) ∈ x.2.1 ∨ (t, s) ∈ x.2.1) := by
  rw [canonEdges_eval, List.mem_filter, List.pair_mem_product, List.mem_range, List.mem_range,
    canonKeep_eval_true]
  constructor
  · rintro ⟨⟨hs, ht⟩, hlt, hor⟩; exact ⟨hlt, hs, ht, hor⟩
  · rintro ⟨hlt, hs, ht, hor⟩; exact ⟨⟨hs, ht⟩, hlt, hor⟩

/-! ## Lexicographic sortedness -/

/-- The self-cross of `range n` is strictly increasing in the lexicographic
index `K (i, j) = i·n + j`. -/
theorem pairwise_K_product (n : ℕ) :
    List.Pairwise (fun p q : ℕ × ℕ ↦ p.1 * n + p.2 < q.1 * n + q.2)
      ((List.range n).product (List.range n)) := by
  rw [← List.pairwise_map (R := (· < ·)) (f := fun p : ℕ × ℕ ↦ p.1 * n + p.2), map_K_product]
  exact List.pairwise_lt_range

/-- **The canonical edge list is lexicographically sorted**: strictly increasing
in `K (s, t) = s·n + t`. This is the bridge that pins the ballots' within-gap
edge order to the abstract tie key `EdgePair.tie`, whose leading term is exactly
this `K`. -/
theorem canonEdges_pairwise (x : GraphTy.denote) :
    List.Pairwise (fun p q : ℕ × ℕ ↦ p.1 * x.1.length + p.2 < q.1 * x.1.length + q.2)
      (canonEdges.eval x) := by
  rw [canonEdges_eval]
  exact (pairwise_K_product x.1.length).sublist List.filter_sublist

/-! ## The enumeration bijection -/

/-- The `ℕ × ℕ` incarnation of an `EdgePair`: its two endpoints as values. -/
def toPair {n : ℕ} {G : SimpleGraph (Fin n)} (e : EdgePair n G) : ℕ × ℕ :=
  (e.i.val, e.j.val)

variable {x : GraphTy.denote}

/-- Every `EdgePair` of the decoded graph sits in the canonical list. -/
theorem toPair_mem (e : EdgePair (decodeNumbered x).n (decodeNumbered x).G) :
    toPair e ∈ canonEdges.eval x := by
  have hadj := e.adj
  rw [decodeNumbered_adj] at hadj
  exact (mem_canonEdges x e.i.val e.j.val).mpr ⟨e.i_lt_j, e.i.isLt, e.j.isLt, hadj.2⟩

/-- Decode a canonical edge back to an `EdgePair`. -/
def decodeEdge (s t : ℕ) (h : (s, t) ∈ canonEdges.eval x) :
    EdgePair (decodeNumbered x).n (decodeNumbered x).G :=
  ⟨(⟨s, ((mem_canonEdges x s t).mp h).2.1⟩, ⟨t, ((mem_canonEdges x s t).mp h).2.2.1⟩),
    (decodeNumbered_adj x _ _).mpr
      ⟨fun hc ↦ absurd (congrArg Fin.val hc) (Nat.ne_of_lt ((mem_canonEdges x s t).mp h).1),
        ((mem_canonEdges x s t).mp h).2.2.2⟩,
    ((mem_canonEdges x s t).mp h).1⟩

@[simp] theorem toPair_decodeEdge (s t : ℕ) (h : (s, t) ∈ canonEdges.eval x) :
    toPair (decodeEdge s t h) = (s, t) := rfl

theorem decodeEdge_toPair (e : EdgePair (decodeNumbered x).n (decodeNumbered x).G)
    (h : (e.i.val, e.j.val) ∈ canonEdges.eval x) : decodeEdge e.i.val e.j.val h = e :=
  Subtype.ext (Prod.ext (Fin.ext rfl) (Fin.ext rfl))

/-- The `EdgePair`s of the decoded graph, bijecting with the canonical members
via `toPair`. -/
def edgeSubEquiv (x : GraphTy.denote) :
    EdgePair (decodeNumbered x).n (decodeNumbered x).G ≃ {p : ℕ × ℕ // p ∈ canonEdges.eval x} where
  toFun e := ⟨toPair e, toPair_mem e⟩
  invFun p := decodeEdge p.val.1 p.val.2 p.2
  left_inv e := decodeEdge_toPair e (toPair_mem e)
  right_inv p := Subtype.ext (toPair_decodeEdge p.val.1 p.val.2 p.2)

/-- **The enumeration bijection**: an `EdgePair` of the decoded graph corresponds
to its position in the canonical edge list, sending an edge to the index of
`toPair e`. Feeds `Numbering.ofEquiv` in the candidate numbering.

The underlying position is `List.idxOf (toPair e) (canonEdges.eval x)`
(`List.Nodup.getEquiv_symm_apply_val`); its identification with the index the
profile program computes is deferred to the adequacy proof, where it is matched
against that program's structural equality test. -/
def edgePairEquiv (x : GraphTy.denote) :
    EdgePair (decodeNumbered x).n (decodeNumbered x).G ≃ Fin (canonEdges.eval x).length :=
  (edgeSubEquiv x).trans (List.Nodup.getEquiv _ (canonEdges_nodup x)).symm

end Cert
end Hardness
