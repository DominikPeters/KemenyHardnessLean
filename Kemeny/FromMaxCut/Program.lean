import Kemeny.FromMaxCut.Ballots
import Kemeny.Encoding

/-!
# The profile program: guards and assembly

The reduction's output is a concrete KEMENY SCORE instance. This file guards the
construction and assembles the pieces (candidate list, ballots, budget) into the
final program `kemenyCode : Code GraphTy KemenyTy`.

## The guards

The abstract instance map `kemenyLeeMap` guards `kemenyMap` behind the
long-even-edges restriction, and `kemenyMap` itself guards `k ≤ #edges`; a
failed guard yields the fixed NO instance. The program mirrors both:

* **`leeHolds`** decides `LongEvenEdges (decodeNumbered x)`. The canonical edge
  list already enumerates the increasing adjacencies, so the check is: every
  `(s, t)` there is *long* (`s + 6 ≤ t`, via `natLe`) and *even* (`2 ∣ (s + t)`).
  The language has no division, so evenness is decided by a bounded membership
  test — `s + t ∈ [0, 2, …, 2(n-1)]` (`doubles`) — correct because `s + t < 2n`.
  `leeHolds` is then "no canonical edge violates either condition".
* **`kLeCard`** decides `k ≤ |E|` as `natLe` against the canonical list length
  (which the adequacy proof identifies with `card (EdgePair …)`).

## Assembly

On the guarded branch the output is `(candList, (profileBallots, budgetCode))`;
off it, the fixed NO instance `([0,1], ([[0,1],[0,1],[1,0]], 0))` — two ballots
ranking `0 < 1` against one ranking `1 < 0`, budget `0`, a NO instance of
three-voter KEMENY SCORE (proved in the adequacy annex).
-/

namespace Hardness
namespace Cert

open Finset

/-! ## Natural-number membership -/

/-- `Code.natEq` decides equality. -/
theorem natEq_eval_true (m q : ℕ) : Code.natEq.eval (m, q) = true ↔ m = q := by
  have h : Code.natEq.eval (m, q) = decide (m = q) := rfl
  rw [h, decide_eq_true_iff]

/-- List-membership test for a binary natural, the `natEq` twin of `memEdge`:
map an equality test over the list (the sought number in the environment),
filter, and test whether anything survived. -/
def memNat : Code (.pair .nat (.list .nat)) .bool :=
  .comp (.listMapEnv Code.natEq)
    (.comp (.listFilter .id) (.comp .listLen (.comp (.pair (.const .nat 1) .id) .natLe)))

/-- `memNat` decides list membership. -/
theorem memNat_eval_true (m : ℕ) (l : List ℕ) : memNat.eval (m, l) = true ↔ m ∈ l := by
  have h : memNat.eval (m, l) =
      decide (1 ≤ ((l.map fun a ↦ Code.natEq.eval (m, a)).filter fun b ↦ b).length) := rfl
  rw [h, decide_eq_true_iff]
  clear h
  induction l with
  | nil => simp
  | cons q l ih =>
    simp only [List.map_cons, List.filter_cons, List.mem_cons]
    by_cases hmq : m = q
    · rw [if_pos ((natEq_eval_true m q).mpr hmq)]
      exact ⟨fun _ ↦ Or.inl hmq, fun _ ↦ by rw [List.length_cons]; exact Nat.le_add_left 1 _⟩
    · rw [if_neg fun hc ↦ hmq ((natEq_eval_true m q).mp hc)]
      exact ih.trans ⟨Or.inr, fun hor ↦ hor.resolve_left hmq⟩

/-! ## The evenness list -/

/-- The even numbers below `2n`: `[0, 2, 4, …, 2(n-1)]`, as `positions` doubled.
Membership in it decides evenness for a sum `s + t < 2n`. -/
def doubles : Code GraphTy (.list .nat) :=
  .comp positions (.listMap (Code.mul (.const .nat 2) .id))

theorem doubles_eval (x : GraphTy.denote) :
    doubles.eval x = (List.range x.1.length).map fun q ↦ 2 * q := by
  have h : doubles.eval x
      = (positions.eval x).map fun q ↦ (Code.mul (σ := .nat) (.const .nat 2) .id).eval q := rfl
  rw [h, positions_eval]; rfl

/-- **Evenness via bounded membership**: for `m < 2n`, `m` is in `doubles` iff
`m` is even — the certificate's stand-in for the missing division primitive. -/
theorem mem_doubles_iff (x : GraphTy.denote) (m : ℕ) (hm : m < 2 * x.1.length) :
    m ∈ doubles.eval x ↔ 2 ∣ m := by
  rw [doubles_eval, List.mem_map]
  exact ⟨fun ⟨q, _, hq⟩ ↦ ⟨q, hq.symm⟩, fun ⟨q, hq⟩ ↦ ⟨q, List.mem_range.mpr (by omega), hq.symm⟩⟩

/-! ## The long-even-edges decider -/

/-- Violation test for a canonical edge `(s, t)` against `doubles` (threaded as
environment): the edge is *not* long-and-even, i.e. `¬(s + 6 ≤ t ∧ s + t ∈
doubles)`. -/
def violationTest : Code (.pair (.list .nat) (.pair .nat .nat)) .bool :=
  .comp
    (Code.and
      (.comp (.pair (Code.add (.comp .snd .fst) (.const .nat 6)) (.comp .snd .snd)) .natLe)
      (.comp (.pair (Code.add (.comp .snd .fst) (.comp .snd .snd)) .fst) memNat))
    .boolNot

theorem violationTest_eval_false (D : List ℕ) (s t : ℕ) :
    violationTest.eval (D, (s, t)) = false ↔ s + 6 ≤ t ∧ (s + t) ∈ D := by
  have h : violationTest.eval (D, (s, t)) = !(decide (s + 6 ≤ t) && memNat.eval (s + t, D)) := rfl
  rw [h, Bool.not_eq_false', Bool.and_eq_true, decide_eq_true_iff, memNat_eval_true]

/-- The number of canonical edges that violate long-even-ness. -/
def leeViolators : Code GraphTy .nat :=
  .comp (.pair doubles canonEdges) (.comp (Code.filterEnv violationTest) .listLen)

theorem leeViolators_eval (x : GraphTy.denote) :
    leeViolators.eval x
      = ((canonEdges.eval x).filter fun st ↦ violationTest.eval (doubles.eval x, st)).length := by
  have h : leeViolators.eval x
      = ((Code.filterEnv violationTest).eval (doubles.eval x, canonEdges.eval x)).length := rfl
  rw [h, filterEnv_eval]

/-- The long-even-edges decider: no canonical edge violates the restriction. -/
def leeHolds : Code GraphTy .bool := .comp (.pair leeViolators (.const .nat 0)) Code.natEq

theorem leeHolds_eval_true (x : GraphTy.denote) :
    leeHolds.eval x = true ↔
      ∀ st ∈ canonEdges.eval x, st.1 + 6 ≤ st.2 ∧ (st.1 + st.2) ∈ doubles.eval x := by
  have h : leeHolds.eval x = Code.natEq.eval (leeViolators.eval x, 0) := rfl
  rw [h, natEq_eval_true, leeViolators_eval, List.length_eq_zero_iff, List.filter_eq_nil_iff]
  refine forall₂_congr fun st _ ↦ ?_
  obtain ⟨s, t⟩ := st
  rw [Bool.not_eq_true, violationTest_eval_false]

/-- **`leeHolds` decides `LongEvenEdges`.** The canonical list enumerates the
increasing adjacencies of the decoded graph, so long-even-ness of every edge is
long-even-ness at every increasing adjacency; `mem_doubles_iff` turns the
evenness membership into `2 ∣ (i + j)` (the sum is below `2n`). -/
theorem leeHolds_eval_LongEven (x : GraphTy.denote) :
    leeHolds.eval x = true ↔ LongEvenEdges (decodeNumbered x) := by
  rw [leeHolds_eval_true]
  constructor
  · intro hf i j hadj hlt
    rw [decodeNumbered_adj] at hadj
    have hi : i.val < x.1.length := i.isLt
    have hj : j.val < x.1.length := j.isLt
    obtain ⟨hlong, heven⟩ := hf (i.val, j.val)
      ((mem_canonEdges x i.val j.val).mpr ⟨hlt, hi, hj, hadj.2⟩)
    exact ⟨hlong, (mem_doubles_iff x _ (by omega)).mp heven⟩
  · intro hle st hst
    obtain ⟨s, t⟩ := st
    obtain ⟨hlt, hs, ht, hor⟩ := (mem_canonEdges x s t).mp hst
    have hadj : (decodeNumbered x).G.Adj ⟨s, hs⟩ ⟨t, ht⟩ :=
      (decodeNumbered_adj x _ _).mpr ⟨fun hc ↦ absurd (congrArg Fin.val hc) (Nat.ne_of_lt hlt), hor⟩
    obtain ⟨hlong, heven⟩ := hle ⟨s, hs⟩ ⟨t, ht⟩ hadj hlt
    exact ⟨hlong, (mem_doubles_iff x _ (by omega)).mpr heven⟩

/-! ## The threshold guard -/

/-- The threshold guard `k ≤ |E|`, against the canonical list length. -/
def kLeCard : Code GraphTy .bool := .comp (.pair kNum canonLen) .natLe

theorem kLeCard_eval_true (x : GraphTy.denote) :
    kLeCard.eval x = true ↔ x.2.2 ≤ (canonEdges.eval x).length := by
  have h : kLeCard.eval x = decide (x.2.2 ≤ (canonEdges.eval x).length) := rfl
  rw [h, decide_eq_true_iff]

/-! ## The full guard and the assembly -/

/-- The full guard: long-even-edges and `k ≤ |E|`. -/
def guardCode : Code GraphTy .bool := Code.and leeHolds kLeCard

theorem guardCode_eval_true (x : GraphTy.denote) :
    guardCode.eval x = true ↔
      LongEvenEdges (decodeNumbered x) ∧ x.2.2 ≤ (canonEdges.eval x).length := by
  rw [guardCode, and_eval_true, leeHolds_eval_LongEven, kLeCard_eval_true]

/-- The guarded output: candidate list, three ballots, budget. -/
def realCode : Code GraphTy KemenyTy := .pair candList (.pair profileBallots budgetCode)

/-- The fixed NO instance: two alternatives, two ballots `[0,1]` against one
`[1,0]`, budget `0`. Its decoding is a NO instance of three-voter KEMENY SCORE
(the adequacy annex). -/
def kemenyNoCode : Code GraphTy KemenyTy :=
  .const KemenyTy ([0, 1], ([[0, 1], [0, 1], [1, 0]], 0))

/-- **The reduction program**: the guarded three-voter profile, or the fixed NO
instance when a guard fails. -/
def kemenyCode : Code GraphTy KemenyTy := .branch guardCode realCode kemenyNoCode

theorem kemenyCode_eval (x : GraphTy.denote) :
    kemenyCode.eval x = if guardCode.eval x = true
      then (candList.eval x, (profileBallots.eval x, budgetCode.eval x))
      else ([0, 1], ([[0, 1], [0, 1], [1, 0]], 0)) := rfl

end Cert
end Hardness
