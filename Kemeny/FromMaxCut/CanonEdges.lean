import Kemeny.Source.Certified
import Kemeny.FromMaxCut.Construction
import Mathlib.Data.List.NodupEquivFin

/-!
# The canonical edge list

Every downstream part of the Kemeny profile program reads the edges of the
decoded source graph *in one fixed order*: the candidate numbering assigns
`6nM + 2·(canon index) + side` to each edge candidate, the ballots splice the
edge candidates at their gadget positions in that order, and the budget sums
`6·span + 3` over that order. This file builds that order once, as a `Code`
program `canonEdges`, and proves the two facts the rest of phase 2 consumes:

* it is duplicate-free (`canonEdges_nodup`), and
* its members are exactly the edges of the decoded numbered graph in increasing
  orientation (`mem_canonEdges`).

Together these give the **enumeration bijection** `edgePairEquiv` between the
`EdgePair`s of the decoded graph — undirected edges carried as `i < j` pairs —
and the positions `Fin (canonEdges.eval x).length` of the list, sending an edge
to its index (`edgePairEquiv_apply`). This is the block that feeds
`Numbering.ofEquiv` when the candidate numbering is assembled.

## Construction

The raw edge list carries junk (out-of-range or diagonal pairs the decoding
ignores) and redundancy (an undirected edge may appear as both `(a, b)` and
`(b, a)`, or be literally repeated). Three passes clean it up:

1. **sanitize** — `goodEdges` keeps the in-range, off-diagonal pairs (shared
   with every gadget that copies its input's adjacencies);
2. **orient** — `orient` sends `(a, b)` to `(min a b, max a b)`, so the two
   directions of an undirected edge collapse to one increasing pair;
3. **dedup** — `Code.dedupBy Code.natPairEq` removes the resulting duplicates,
   exactly mathlib's `List.dedup`.
-/

namespace Hardness
namespace Cert

open Finset

/-! ## Orienting a pair -/

/-- Orient an index pair to increasing order: `(a, b) ↦ (a, b)` if `a ≤ b`, else
`(b, a)`. The two orientations of an undirected edge collapse to one pair. -/
def orient : Code (.pair .nat .nat) (.pair .nat .nat) :=
  .branch .natLe (.pair .fst .snd) (.pair .snd .fst)

theorem orient_eval (a b : ℕ) : orient.eval (a, b) = if a ≤ b then (a, b) else (b, a) := by
  by_cases h : a ≤ b
  · rw [if_pos h]
    change (if (decide (a ≤ b) = true) then ((a, b) : ℕ × ℕ) else (b, a)) = (a, b)
    rw [if_pos (by simpa using h)]
  · rw [if_neg h]
    change (if (decide (a ≤ b) = true) then ((a, b) : ℕ × ℕ) else (b, a)) = (b, a)
    rw [if_neg (by simpa using h)]

/-! ## The canonical edge list -/

/-- The canonical edge list: sanitize the raw edges, orient each to increasing
order, deduplicate. One increasing pair per edge of the decoded graph, in a
fixed order that all of phase 2 reads. -/
def canonEdges : Code GraphTy (.list (.pair .nat .nat)) :=
  .comp goodEdges (.comp (.listMap orient) (Code.dedupBy Code.natPairEq))

/-- `Code.natPairEq` computes decidable equality of index pairs — the hypothesis
`Code.dedupBy`'s specification asks for. -/
theorem natPairEq_eval (p q : ℕ × ℕ) : Code.natPairEq.eval (p, q) = decide (p = q) := by
  rcases eq_or_ne p q with h | h
  · rw [(natPairEq_eval_true p q).mpr h]
    exact (decide_eq_true_iff.mpr h).symm
  · have hf : Code.natPairEq.eval (p, q) = false := by
      rcases Bool.eq_false_or_eq_true (Code.natPairEq.eval (p, q)) with h' | h'
      · exact absurd ((natPairEq_eval_true p q).mp h') h
      · exact h'
    rw [hf, decide_eq_false h]

/-- The canonical edge list is the deduplicated list of oriented sanitized
edges. -/
theorem canonEdges_eval (x : GraphTy.denote) :
    canonEdges.eval x = ((goodEdges.eval x).map (fun q ↦ orient.eval q)).dedup := by
  change (Code.dedupBy Code.natPairEq).eval ((goodEdges.eval x).map (fun q ↦ orient.eval q)) = _
  exact dedupBy_eval natPairEq_eval _

/-- **The canonical edge list is duplicate-free.** -/
theorem canonEdges_nodup (x : GraphTy.denote) : (canonEdges.eval x).Nodup := by
  rw [canonEdges_eval]
  exact List.nodup_dedup _

/-- **Membership in the canonical edge list**: `(s, t)` is a canonical edge iff
it is an increasing pair naming an edge of the decoded graph (in range,
off-diagonal, present in the raw list in either orientation). -/
theorem mem_canonEdges (x : GraphTy.denote) (s t : ℕ) :
    (s, t) ∈ canonEdges.eval x ↔
      s < t ∧ s < x.1.length ∧ t < x.1.length ∧ ((s, t) ∈ x.2.1 ∨ (t, s) ∈ x.2.1) := by
  rw [canonEdges_eval, List.mem_dedup, List.mem_map]
  constructor
  · rintro ⟨⟨a, b⟩, hmem, heq⟩
    have hg := (mem_goodEdges_eval x a b).mp hmem
    rw [orient_eval] at heq
    rcases le_or_gt a b with hab | hab
    · rw [if_pos hab] at heq
      injection heq with h1 h2; subst h1; subst h2
      exact ⟨lt_of_le_of_ne hab hg.2.2.2, hg.2.1, hg.2.2.1, Or.inl hg.1⟩
    · rw [if_neg (Nat.not_le.mpr hab)] at heq
      injection heq with h1 h2; subst h1; subst h2
      exact ⟨hab, hg.2.2.1, hg.2.1, Or.inr hg.1⟩
  · rintro ⟨hlt, hs, ht, hor⟩
    rcases hor with he | he
    · exact ⟨(s, t), (mem_goodEdges_eval x s t).mpr ⟨he, hs, ht, Nat.ne_of_lt hlt⟩,
        by rw [orient_eval, if_pos (Nat.le_of_lt hlt)]⟩
    · exact ⟨(t, s), (mem_goodEdges_eval x t s).mpr ⟨he, ht, hs, (Nat.ne_of_lt hlt).symm⟩,
        by rw [orient_eval, if_neg (Nat.not_le.mpr hlt)]⟩

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
