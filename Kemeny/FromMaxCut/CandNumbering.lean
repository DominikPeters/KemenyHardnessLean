import Kemeny.BallotOrder
import Kemeny.FromMaxCut.Ballots

/-!
# The candidate numbering, and the edges in canonical order

The profile program numbers the `N = 6nM + 2|E|` candidates of the produced
instance by the layout described in `Ballots.lean`:

  `num (u, x, m) = 6M·u + M·ξ(x) + m`,   `num (e, side) = 6nM + 2·idx(e) + side`.

This file realizes that layout as a `Numbering (DCand x)` assembled from the
generic block combinators — a rectangle `n × 6 × M` for the vertex candidates,
laid before a rectangle `|E| × 2` for the edge candidates — and states the two
*face* lemmas that check the assembly against the numbers the program emits.
The numbering's `size` is the length of `candList`, so the decoded instance's
alternatives `Fin (candList.eval x).length` are exactly the positions the
numbering enumerates.

The `|E|` block needs a bijection `EdgePair ≃ Fin |canon|`, which is
`edgePairEquiv`. Its inverse, run over all positions, is `edgeOrder`: the edges
of the decoded graph listed in canonical order. Three facts about it are what the
ballot proofs consume — it is complete, it maps onto the canonical list under
`toPair`, and it is sorted for the lexicographic key `K (e) = e.i·n + e.j` whose
double is the leading term of the abstract tie key `EdgePair.tie`. The fourth,
`canonEdges_zipIdx`, rewrites the program's enumerated edge list as an
`edgeOrder`-indexed list, which is how a gap's `filter`/`map` over the program's
list becomes a `filter`/`map` over abstract edges.
-/

namespace Hardness
namespace Cert

/-! ## The digit numberings -/

/-- The six letters, numbered by the global letter index `ξ`. -/
def letterNum : Numbering Letter where
  num := letterIdx
  size := 6
  num_lt x := by cases x <;> decide
  num_inj a b h := by cases a <;> cases b <;> simp_all [letterIdx]
  num_surj i hi := match i, hi with
    | 0, _ => ⟨.A, rfl⟩
    | 1, _ => ⟨.B, rfl⟩
    | 2, _ => ⟨.C, rfl⟩
    | 3, _ => ⟨.D, rfl⟩
    | 4, _ => ⟨.E, rfl⟩
    | 5, _ => ⟨.F, rfl⟩

@[simp] theorem letterNum_num (x : Letter) : letterNum.num x = letterIdx x := rfl

@[simp] theorem letterNum_size : letterNum.size = 6 := rfl

/-- The side index `left ↦ 0`, `right ↦ 1` — the low digit of an edge
candidate's number, matching `leftNum`/`rightNum`. -/
def sideIdx : Side → ℕ
  | .left => 0
  | .right => 1

/-- The two sides, numbered `left` first. -/
def sideNum : Numbering Side where
  num := sideIdx
  size := 2
  num_lt s := by cases s <;> decide
  num_inj a b h := by cases a <;> cases b <;> simp_all [sideIdx]
  num_surj i hi := match i, hi with
    | 0, _ => ⟨.left, rfl⟩
    | 1, _ => ⟨.right, rfl⟩

@[simp] theorem sideNum_num (s : Side) : sideNum.num s = sideIdx s := rfl

@[simp] theorem sideNum_size : sideNum.size = 2 := rfl

/-! ## The candidates of a decoded instance -/

/-- The candidate type the construction builds on the decoded input — the
alternative type of `kemenyMap (decodeNumbered x)` on the guarded branch. -/
abbrev DCand (x : GraphTy.denote) : Type :=
  Cand (decodeNumbered x).n (bigM (decodeNumbered x).n) (decodeNumbered x).G

/-- The decoded vertex count is the vertex-list length — the spelling the
program's eval lemmas use. -/
@[simp] theorem decodeNumbered_n (x : GraphTy.denote) : (decodeNumbered x).n = x.1.length := rfl

/-- **The candidate numbering**: the vertex block `n × 6 × M` (gadget, letter,
member — row-major, so each supercandidate's `M` members are contiguous) laid
before the edge block `|E| × 2` (canonical index, side). -/
def candNumbering (x : GraphTy.denote) : Numbering (DCand x) :=
  ((Numbering.fin (decodeNumbered x).n).prod
      (letterNum.prod (Numbering.fin (bigM (decodeNumbered x).n)))).sum
    ((Numbering.ofEquiv (edgePairEquiv x)).prod sideNum)

variable {x : GraphTy.denote}

/-- **The vertex face**: a vertex candidate sits at `6M·u + M·ξ(x) + m`, the
base of `letterRun` plus the member index. -/
theorem candNumbering_inl (u : Fin (decodeNumbered x).n) (lx : Letter)
    (m : Fin (bigM (decodeNumbered x).n)) :
    (candNumbering x).num (Sum.inl (u, lx, m))
      = 6 * bigM x.1.length * u.val + letterIdx lx * bigM x.1.length + m.val := by
  simp only [candNumbering, Numbering.sum_num_inl, Numbering.prod_num, Numbering.prod_size,
    Numbering.fin_num, Numbering.fin_size, letterNum_num, letterNum_size, decodeNumbered_n]
  ring

/-- **The edge face**: an edge candidate sits at `6nM + 2·idx(e) + side`, the
number `leftNum`/`rightNum` emit. -/
theorem candNumbering_inr (e : EdgePair (decodeNumbered x).n (decodeNumbered x).G) (s : Side) :
    (candNumbering x).num (Sum.inr (e, s))
      = 6 * x.1.length * bigM x.1.length + 2 * (edgePairEquiv x e).val + sideIdx s := by
  simp only [candNumbering, Numbering.sum_num_inr, Numbering.prod_num, Numbering.prod_size,
    Numbering.fin_size, Numbering.ofEquiv_num, letterNum_size, sideNum_num, sideNum_size,
    decodeNumbered_n]
  ac_rfl

/-- **The numbering enumerates the alternatives of the decoded instance**: its
size is the length of the emitted candidate list. -/
theorem candNumbering_size (x : GraphTy.denote) :
    (candNumbering x).size = (candList.eval x).length := by
  rw [candList_length]
  simp only [candNumbering, Numbering.sum_size, Numbering.prod_size, Numbering.fin_size,
    letterNum_size, sideNum_size, Numbering.ofEquiv_size, decodeNumbered_n]
  ring

/-! ## The edges in canonical order -/

/-- The `EdgePair`s of the decoded graph — the abstract edges the canonical list
enumerates. -/
abbrev DEdge (x : GraphTy.denote) : Type :=
  EdgePair (decodeNumbered x).n (decodeNumbered x).G

/-- The `EdgePair`s of the decoded graph, listed in canonical-edge-list order:
the inverse enumeration bijection run over all positions. -/
def edgeOrder (x : GraphTy.denote) :
    List (EdgePair (decodeNumbered x).n (decodeNumbered x).G) :=
  (List.finRange (canonEdges.eval x).length).map (edgePairEquiv x).symm

/-- The edge at canonical position `i` is the pair the canonical list holds
there. -/
theorem toPair_edgePairEquiv_symm (i : Fin (canonEdges.eval x).length) :
    toPair ((edgePairEquiv x).symm i) = (canonEdges.eval x)[i.val] := rfl

/-- **`edgeOrder` is the canonical edge list, read abstractly.** -/
theorem edgeOrder_map_toPair (x : GraphTy.denote) :
    (edgeOrder x).map toPair = canonEdges.eval x := by
  rw [edgeOrder, List.map_map]
  have h : toPair ∘ (edgePairEquiv x).symm = fun i ↦ (canonEdges.eval x)[i.val] := by
    funext i
    exact toPair_edgePairEquiv_symm i
  rw [h]
  exact List.map_getElem_finRange _

/-- Every edge of the decoded graph occurs in `edgeOrder`. -/
theorem mem_edgeOrder (e : EdgePair (decodeNumbered x).n (decodeNumbered x).G) :
    e ∈ edgeOrder x :=
  List.mem_map.mpr ⟨edgePairEquiv x e, List.mem_finRange _, (edgePairEquiv x).symm_apply_apply e⟩

theorem edgeOrder_nodup (x : GraphTy.denote) : (edgeOrder x).Nodup :=
  (List.nodup_finRange _).map (edgePairEquiv x).symm.injective

/-- **`edgeOrder` is sorted for the lexicographic key `K (e) = e.i·n + e.j`** —
inherited from `canonEdges_pairwise`. Since `EdgePair.tie e s = 2·K(e) + side`,
this is what makes a gap's edges come out in abstract tie order. -/
theorem edgeOrder_pairwise (x : GraphTy.denote) :
    (edgeOrder x).Pairwise fun e e' ↦
      e.i.val * x.1.length + e.j.val < e'.i.val * x.1.length + e'.j.val := by
  have h := canonEdges_pairwise x
  rw [← edgeOrder_map_toPair x, List.pairwise_map] at h
  exact h

/-- **The program's enumerated edge list, read abstractly**: the canonical list
paired with positions is `edgeOrder` with each edge sent to its pair and its
index. Every gap of every ballot is a `filter`/`map` over the left-hand side;
this identity turns it into a `filter`/`map` over abstract edges. -/
theorem canonEdges_zipIdx (x : GraphTy.denote) :
    (canonEdges.eval x).zipIdx
      = (edgeOrder x).map fun e ↦ (toPair e, (edgePairEquiv x e).val) := by
  rw [edgeOrder, List.map_map]
  refine List.ext_getElem (by simp) fun i h1 h2 ↦ ?_
  rw [List.getElem_zipIdx, List.getElem_map, List.getElem_finRange]
  rw [Function.comp_apply, Equiv.apply_symm_apply, toPair_edgePairEquiv_symm]
  simp only [Fin.val_cast, Nat.zero_add]

end Cert
end Hardness
