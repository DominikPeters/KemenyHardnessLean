import Kemeny.FromMaxCut.CandNumbering
import Kemeny.FromMaxCut.MinTotal

/-!
# The emitted budget is the instance's budget

The number the certificate ships as the third component of the produced KEMENY
instance is `budgetCode.eval x`; the abstract instance map ships
`kemenyBudget (decodeNumbered x) = minTotal + marginBudget`. This file matches
them.

Both summands are already available in arithmetic form — `minTotalCode_eval` and
`marginBudgetCode_eval` on the program side, `minTotal_kemenyProfile` (8a's
closed form `T(N) − 6n·T(M)`) and the definitions of `marginBudget`, `edgeBound`,
`pairSlack` on the abstract side. What is missing is the translation of the three
*counts* those forms disagree about:

* `Fintype.card (EdgePair …) = |canon|` — the enumeration bijection
  (`card_edgePair`), which fixes `pairSlack`;
* `Fintype.card (Cand …) = 6nM + 2|canon|` — the candidate numbering, whose size
  is the emitted candidate list's length (`card_cand`), which fixes `T(N)`;
* `Σ_e f e = Σ over the canonical list` — `edgeOrder` is a nodup enumeration of
  the edges (`sum_edgeOrder`), which fixes `edgeBound`.

The `minTotal` closed form needs the edges spread (`SpreadEdges`), which the
program's guard delivers through `LongEvenEdges`; it is the only hypothesis.
-/

namespace Hardness
namespace Cert

variable {x : GraphTy.denote}

/-! ## The three counts -/

/-- **The canonical edge list counts the edge pairs.** -/
theorem card_edgePair (x : GraphTy.denote) :
    Fintype.card (DEdge x) = (canonEdges.eval x).length := by
  rw [Fintype.card_congr (edgePairEquiv x), Fintype.card_fin]

/-- **The candidate list counts the candidates**, via the numbering that
enumerates its positions. -/
theorem card_cand (x : GraphTy.denote) :
    Fintype.card (DCand x)
      = 6 * x.1.length * bigM x.1.length + 2 * (canonEdges.eval x).length := by
  rw [(candNumbering x).card_eq, candNumbering_size, candList_length]

/-- **A sum over the edges is a sum over the canonical list**: `edgeOrder` is a
duplicate-free enumeration of every edge. -/
theorem sum_edgeOrder {β : Type*} [AddCommMonoid β] (f : DEdge x → β) :
    ((edgeOrder x).map f).sum = ∑ e : DEdge x, f e := by
  classical
  rw [← List.sum_toFinset f (edgeOrder_nodup x)]
  congr 1
  exact Finset.eq_univ_iff_forall.mpr fun e ↦ List.mem_toFinset.mpr (mem_edgeOrder e)

/-! ## The three summands -/

/-- **The edge term matches**: the program sums `6·(t − s) + 3` over the
canonical list, the instance sums `6·span e + 3` over the edges. -/
theorem edgeBoundCode_eq (x : GraphTy.denote) :
    edgeBoundCode.eval x = edgeBound (decodeNumbered x).n (decodeNumbered x).G := by
  rw [edgeBoundCode_eval, ← edgeOrder_map_toPair, List.map_map, edgeBound, ← sum_edgeOrder]
  rfl

/-- **The pair slack matches.** -/
theorem pairSlackCode_eq (x : GraphTy.denote) :
    pairSlackCode.eval x = pairSlack (decodeNumbered x).n (decodeNumbered x).G := by
  rw [pairSlackCode_eval, pairSlack, card_edgePair]

/-- **The margin budget matches.** -/
theorem marginBudgetCode_eq (x : GraphTy.denote) :
    marginBudgetCode.eval x = marginBudget (decodeNumbered x) := by
  rw [marginBudget, ← edgeBoundCode_eq, ← pairSlackCode_eq, marginBudgetCode_eval,
    edgeBoundCode_eval, pairSlackCode_eval]
  rfl

/-- **The minority total matches** — 8a's closed form against the program's two
Gauss sums, with the candidate count supplied by the numbering. -/
theorem minTotalCode_eq (x : GraphTy.denote)
    (hsp : SpreadEdges (decodeNumbered x).n (decodeNumbered x).G) :
    minTotalCode.eval x
      = minTotal (kemenyProfile (decodeNumbered x).n (decodeNumbered x).G
            (bigM (decodeNumbered x).n))
          ((spec1 (decodeNumbered x).n (decodeNumbered x).G).ranking
            (bigM (decodeNumbered x).n)) := by
  rw [minTotal_kemenyProfile hsp, minTotalCode_eval, card_cand, decodeNumbered_n]

/-! ## The budget -/

/-- **The emitted budget is the instance's budget.** -/
theorem budgetCode_eq (x : GraphTy.denote)
    (hsp : SpreadEdges (decodeNumbered x).n (decodeNumbered x).G) :
    budgetCode.eval x = kemenyBudget (decodeNumbered x) := by
  rw [budgetCode, add_eval, minTotalCode_eq x hsp, marginBudgetCode_eq, kemenyBudget]

end Cert
end Hardness
