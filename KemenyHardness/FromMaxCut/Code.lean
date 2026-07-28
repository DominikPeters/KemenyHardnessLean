import KemenyHardness.FromMaxCut.CanonEdges
import Mathlib.Algebra.BigOperators.Intervals

/-!
# The profile program: size-honest length gadgets

The reduction's output is a concrete KEMENY SCORE instance `(candidates,
(ballots, budget))` of `KemenyTy`. Its alternative set has `N = card (Cand n M
G) = 6nM + 2|E|` candidates, where `M = 1000 (n+1)⁴` is the supercandidate size.
Both `M` and `N` are polynomial in the input but far larger than any number the
input names directly, so — under the size discipline (no combinator may iterate
a binary-encoded number) — they must be built *structurally*, as lengths of
lists assembled by Cartesian products of lists the program already holds.

This file builds those lists and reads the two magnitudes off their lengths:

* `mList` — a list of length exactly `M = 1000 (n+1)⁴`, the fourth Cartesian
  power of the vertex list padded by one (`(n+1)⁴`) crossed with a literal
  1000-element list. `mNum = |mList|` is `M` as a number.
* `candList` — a list of length exactly `N = 6nM + 2|E|`: the `6nM` vertex
  candidates (six letters × `n` gadgets × `M` members) as `6 × n × M`, appended
  to the `2|E|` edge candidates (two sides × `|E|` canonical edges) as
  `2 × |E|`. It is the emitted alternative set, and `N` never has to be
  computed as a number — the Gauss sum of the budget indexes the list itself.

Everything downstream — the candidate numbering, the ballots, and the Gauss
sums in the budget — indexes these two lists.
-/

namespace Hardness
namespace Cert

variable {σ α β : Ty}

/-! ## Applied Cartesian product -/

/-- Cartesian product of two computed lists. Only its *length* — the product of
the two lengths — is ever used here: it is how the program builds a list of a
prescribed magnitude out of lists it already has. -/
def crossC (a : Code σ (.list α)) (b : Code σ (.list β)) : Code σ (.list (.pair α β)) :=
  .comp (.pair a b) Code.cross

theorem crossC_length (a : Code σ (.list α)) (b : Code σ (.list β)) (x : σ.denote) :
    ((crossC a b).eval x).length = (a.eval x).length * (b.eval x).length :=
  length_cross_eval _ _

/-- Collapse a list to a list of zeros of the same length, so lists of different
element types can be concatenated when only their combined length matters. -/
def toNatList (L : Code σ (.list α)) : Code σ (.list .nat) :=
  .comp L (.listMap (.const .nat 0))

theorem toNatList_length (L : Code σ (.list α)) (x : σ.denote) :
    ((toNatList L).eval x).length = (L.eval x).length := by
  change ((L.eval x).map _).length = _
  rw [List.length_map]

/-! ## The supercandidate size `M` -/

/-- The vertex list padded by one junk entry: length `n + 1`. -/
def vertsPlus : Code GraphTy (.list .nat) :=
  Code.append gVertices (.const (.list .nat) [0])

theorem vertsPlus_length (x : GraphTy.denote) : (vertsPlus.eval x).length = x.1.length + 1 := by
  rw [vertsPlus, append_eval]
  change (x.1 ++ [0]).length = _
  rw [List.length_append]
  rfl

/-- `(n+1)²`, as `vertsPlus × vertsPlus`. -/
def sq : Code GraphTy (.list (.pair .nat .nat)) := crossC vertsPlus vertsPlus

theorem sq_length (x : GraphTy.denote) : (sq.eval x).length = (x.1.length + 1) ^ 2 := by
  rw [sq, crossC_length, vertsPlus_length, Nat.pow_two]

/-- `(n+1)⁴`, as `sq × sq`. -/
def quad : Code GraphTy (.list (.pair (.pair .nat .nat) (.pair .nat .nat))) := crossC sq sq

theorem quad_length (x : GraphTy.denote) : (quad.eval x).length = (x.1.length + 1) ^ 4 := by
  rw [quad, crossC_length, sq_length, ← pow_add]

/-- A literal list of 1000 entries. -/
def thousand : Code GraphTy (.list .nat) := .const (.list .nat) (List.replicate 1000 0)

theorem thousand_length (x : GraphTy.denote) : (thousand.eval x).length = 1000 := by
  change (List.replicate 1000 0).length = 1000
  rw [List.length_replicate]

/-- A list of length exactly `M = 1000 (n+1)⁴`. -/
def mList : Code GraphTy (.list (.pair (.pair (.pair .nat .nat) (.pair .nat .nat)) .nat)) :=
  crossC quad thousand

theorem mList_length (x : GraphTy.denote) : (mList.eval x).length = bigM x.1.length := by
  rw [mList, crossC_length, quad_length, thousand_length, bigM, Nat.mul_comm]

/-- `M` as a number: the length of `mList`. -/
def mNum : Code GraphTy .nat := .comp mList .listLen

theorem mNum_eval (x : GraphTy.denote) : mNum.eval x = bigM x.1.length := mList_length x

/-! ## The candidate count `N` -/

/-- A literal list of six entries — the six letters of a gadget. -/
def sixList : Code GraphTy (.list .nat) := .const (.list .nat) (List.replicate 6 0)

theorem sixList_length (x : GraphTy.denote) : (sixList.eval x).length = 6 := by
  change (List.replicate 6 0).length = 6
  rw [List.length_replicate]

/-- A literal list of two entries — the two sides of an edge. -/
def twoList : Code GraphTy (.list .nat) := .const (.list .nat) [0, 0]

theorem twoList_length (x : GraphTy.denote) : (twoList.eval x).length = 2 := rfl

/-- The `6nM` vertex candidates: six letters × `n` gadgets × `M` members. -/
def vertexCandList : Code GraphTy (.list .nat) :=
  toNatList (crossC sixList (crossC gVertices mList))

theorem vertexCandList_length (x : GraphTy.denote) :
    (vertexCandList.eval x).length = 6 * x.1.length * bigM x.1.length := by
  rw [vertexCandList, toNatList_length, crossC_length, crossC_length, sixList_length,
    mList_length]
  change 6 * (x.1.length * bigM x.1.length) = _
  rw [Nat.mul_assoc]

/-- The `2|E|` edge candidates: two sides × `|E|` canonical edges. -/
def edgeCandList : Code GraphTy (.list .nat) :=
  toNatList (crossC twoList canonEdges)

theorem edgeCandList_length (x : GraphTy.denote) :
    (edgeCandList.eval x).length = 2 * (canonEdges.eval x).length := by
  rw [edgeCandList, toNatList_length, crossC_length, twoList_length]

/-- A list of length exactly `N = 6nM + 2|E|`: the alternative set of the
produced instance. Its entries are junk — decoding reads only its length. -/
def candList : Code GraphTy (.list .nat) := Code.append vertexCandList edgeCandList

theorem candList_length (x : GraphTy.denote) :
    (candList.eval x).length
      = 6 * x.1.length * bigM x.1.length + 2 * (canonEdges.eval x).length := by
  rw [candList, append_eval, List.length_append, vertexCandList_length, edgeCandList_length]

/-! ## The budget

The budget number is `kemenyBudget = minTotal + marginBudget`, and each summand
is arithmetic in `n`, `M`, `|E|`, `k`, the per-edge cost `Σ (6·span + 3)`, and
the two Gauss sums `T(N)`, `T(M)`. The program computes the Gauss sums honestly
by `Code.listSum ∘ Code.indices` over the length gadgets (there is no division
primitive, so the closed form `y(y-1)/2` is unavailable). Identification of the
result with the abstract `kemenyBudget` — the bridges `|E| = card (EdgePair …)`
and `Σ (6·span + 3) = edgeBound` — is deferred to the adequacy proof; here the
eval lemma delivers the value in the same shape as the abstract definitions. -/

/-- Applied truncated subtraction. -/
def subC (a b : Code σ .nat) : Code σ .nat := .comp (.pair a b) .natSub

theorem subC_eval (a b : Code σ .nat) (x : σ.denote) :
    (subC a b).eval x = a.eval x - b.eval x := rfl

/-- The number of vertices `n`. -/
def nNum : Code GraphTy .nat := gNumVertices

/-- The threshold `k`. -/
def kNum : Code GraphTy .nat := gThreshold

/-- The number of canonical edges `|E|`. -/
def canonLen : Code GraphTy .nat := .comp canonEdges .listLen

/-- The Gauss sum `T(y) = Σ_{i < y} i` of the length of a computed list. -/
def sumRangeLen (L : Code σ (.list α)) : Code σ .nat :=
  .comp L (.comp Code.indices Code.listSum)

theorem sumRangeLen_eval (L : Code σ (.list α)) (x : σ.denote) :
    (sumRangeLen L).eval x = (List.range (L.eval x).length).sum := by
  change (Code.indices.eval (L.eval x)).sum = _
  rw [indices_eval]

/-- `T(y) = Σ_{i < y} i` in Finset form — the shape `minTotal`'s closed form
uses. -/
theorem listRange_sum (m : ℕ) : (List.range m).sum = ∑ i ∈ Finset.range m, i := by
  induction m with
  | zero => rfl
  | succ k ih => rw [List.range_succ, List.sum_append, ih, Finset.sum_range_succ]; simp

/-- The per-edge cost `6·span + 3 = 6·(t − s) + 3` of a canonical edge `(s, t)`. -/
def edgeSpanCost : Code (.pair .nat .nat) .nat :=
  Code.add (Code.mul (.const .nat 6) (subC .snd .fst)) (.const .nat 3)

theorem edgeSpanCost_eval (s t : ℕ) : edgeSpanCost.eval (s, t) = 6 * (t - s) + 3 := rfl

/-- The edge term `Σ_e (6·span e + 3)`, as a sum over the canonical edges. -/
def edgeBoundCode : Code GraphTy .nat :=
  .comp canonEdges (.comp (.listMap edgeSpanCost) Code.listSum)

theorem edgeBoundCode_eval (x : GraphTy.denote) :
    edgeBoundCode.eval x = ((canonEdges.eval x).map fun p ↦ 6 * (p.2 - p.1) + 3).sum := by
  change ((canonEdges.eval x).map fun p ↦ edgeSpanCost.eval p).sum = _
  rfl

theorem nNum_eval (x : GraphTy.denote) : nNum.eval x = x.1.length := rfl

theorem kNum_eval (x : GraphTy.denote) : kNum.eval x = x.2.2 := rfl

theorem canonLen_eval (x : GraphTy.denote) : canonLen.eval x = (canonEdges.eval x).length := rfl

/-- The minority total `T(N) − 6n·T(M)`. -/
def minTotalCode : Code GraphTy .nat :=
  subC (sumRangeLen candList) (Code.mul (Code.mul (.const .nat 6) nNum) (sumRangeLen mList))

theorem minTotalCode_eval (x : GraphTy.denote) :
    minTotalCode.eval x
      = (∑ i ∈ Finset.range (6 * x.1.length * bigM x.1.length + 2 * (canonEdges.eval x).length), i)
        - 6 * x.1.length * ∑ i ∈ Finset.range (bigM x.1.length), i := by
  rw [minTotalCode, subC_eval, sumRangeLen_eval, mul_eval, mul_eval, sumRangeLen_eval,
    candList_length, mList_length, listRange_sum, listRange_sum, nNum_eval]
  rfl

/-- The pair slack `(2|E|)²`. -/
def pairSlackCode : Code GraphTy .nat :=
  Code.mul (Code.mul (.const .nat 2) canonLen) (Code.mul (.const .nat 2) canonLen)

theorem pairSlackCode_eval (x : GraphTy.denote) :
    pairSlackCode.eval x = (2 * (canonEdges.eval x).length) ^ 2 := by
  simp only [pairSlackCode, mul_eval, canonLen_eval]
  rw [← Nat.pow_two]
  rfl

/-- `3nM²`. -/
def threeNMsq : Code GraphTy .nat := Code.mul (Code.mul (.const .nat 3) nNum) (Code.mul mNum mNum)

theorem threeNMsq_eval (x : GraphTy.denote) :
    threeNMsq.eval x = 3 * x.1.length * bigM x.1.length ^ 2 := by
  simp only [threeNMsq, mul_eval, nNum_eval, mNum_eval]
  rw [← Nat.pow_two]
  rfl

/-- The margin budget `3nM² + M·edgeBound + pairSlack − Mk`. -/
def marginBudgetCode : Code GraphTy .nat :=
  subC (Code.add (Code.add threeNMsq (Code.mul mNum edgeBoundCode)) pairSlackCode)
    (Code.mul mNum kNum)

theorem marginBudgetCode_eval (x : GraphTy.denote) :
    marginBudgetCode.eval x
      = 3 * x.1.length * bigM x.1.length ^ 2
          + bigM x.1.length * ((canonEdges.eval x).map fun p ↦ 6 * (p.2 - p.1) + 3).sum
          + (2 * (canonEdges.eval x).length) ^ 2
        - bigM x.1.length * x.2.2 := by
  rw [marginBudgetCode, subC_eval, add_eval, add_eval, threeNMsq_eval, pairSlackCode_eval,
    mul_eval, mul_eval, mNum_eval, kNum_eval, edgeBoundCode_eval]

/-- The budget `kemenyBudget = minTotal + marginBudget`. Its spec is the
identification with the abstract budget, `budgetCode_eq` in the adequacy annex;
the two summands' arithmetic forms above are what that proof consumes. -/
def budgetCode : Code GraphTy .nat := Code.add minTotalCode marginBudgetCode

end Cert
end Hardness
