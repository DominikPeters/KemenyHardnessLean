import Kemeny.FromMaxCut.Code

/-!
# The profile program: candidate numbering and the three ballots

The produced KEMENY instance has `N = 6nM + 2|E|` candidates. This file fixes
their numbering and emits the three voters' ballots — each an explicit `List ℕ`
enumerating the candidate numbers in that voter's ranking order, so that
`decodeBallot` recovers the voter (8f).

## The numbering

Globally, a vertex candidate `(u, x, m)` (gadget `u`, letter `x`, member `m <
M`) is numbered

  `num (u, x, m) = 6M·u + M·ξ(x) + m`,     `ξ = A,…,F ↦ 0,…,5`  (`letterIdx`),

occupying `[0, 6nM)`; an edge candidate `(e, side)` is numbered

  `6nM + 2·idx(e) + side`,                  `side = left,right ↦ 0,1`,

occupying `[6nM, N)`, where `idx(e)` is `e`'s position in the canonical edge
list. The two blocks make each letter's `M` members a *contiguous* run, which is
what lets the ballots be built without a sort.

## A ballot

A voter lists candidates by its key `(gadgetPos, slot, tie)`. The ballot is the
`flatMap` over gadgets — in `gadgetPos` order (ascending vertex index for voters
1 and 3, descending for voter 2, `gadgetDesc`) — of a per-gadget *block*. A block
is the six letters in the voter's local order, each as a length-`M` run
(`letterRun` = `runFrom`, the contiguous `[base, base+M)`), with the edge
candidates spliced into their gaps:

* a **letter run** for `(u, x)` is `6M·u + M·ξ(x) + [0, M)`;
* a **gap** after letter `x` in gadget `u` holds the edge candidates the voter
  keys to that slot — filtered from the canonical edge enumeration by an
  endpoint/midpoint test, each emitting its number.

The canonical list is `K`-sorted (`canonEdges_pairwise`), so the gap edges come
out in `tie` order automatically; voter 2's midpoint gap holds *both* sides of
each edge, emitted left-then-right (`bothGap`) to match `tie = 2K + side`.
-/

namespace Hardness
namespace Cert

open Finset

/-! ## Two combinators: contiguous runs and filter-flatMap -/

variable {σ α τ' : Ty}

/-- The contiguous run `[base, base+1, …, base + |L| − 1]`: enumerate `L`'s
positions and shift each by `base`. The length is read off `L`, per the size
discipline — the run's magnitude is exhibited as a list length, never counted. -/
def runFrom (base : Code σ .nat) (L : Code σ (.list α)) : Code σ (.list .nat) :=
  .comp (.pair base (.comp L Code.indices)) (.listMapEnv (Code.add .fst .snd))

theorem runFrom_eval (base : Code σ .nat) (L : Code σ (.list α)) (x : σ.denote) :
    (runFrom base L).eval x = (List.range (L.eval x).length).map (fun i ↦ base.eval x + i) := by
  have h : (runFrom base L).eval x = (Code.indices.eval (L.eval x)).map
      (fun i ↦ (Code.add (σ := .pair .nat .nat) .fst .snd).eval (base.eval x, i)) := rfl
  rw [h, indices_eval]; rfl

/-- **Filter-then-flatMap with an environment in scope**: survivors of `test`
emit the *list* `f a` (rather than a single value), and the results are
concatenated. This is the one place a gap emits more than one candidate per edge
— voter 2's midpoint gap, where each edge contributes both its sides. -/
def filterFlatMapEnv {ε τ : Ty} (test : Code (.pair ε τ) .bool)
    (f : Code (.pair ε τ) (.list τ')) : Code (.pair ε (.list τ)) (.list τ') :=
  .comp (.listMapEnv (.branch test f (.const (.list τ') []))) .listJoin

theorem filterFlatMapEnv_eval {ε τ : Ty} (test : Code (.pair ε τ) .bool)
    (f : Code (.pair ε τ) (.list τ')) (e : ε.denote) (l : List τ.denote) :
    (filterFlatMapEnv test f).eval (e, l)
      = (l.map fun a ↦ if test.eval (e, a) = true then f.eval (e, a) else []).flatten := rfl

/-! ## The global letter index -/

/-- The global letter index `ξ : A,…,F ↦ 0,…,5` of the candidate numbering. Not
a voter's local order (those are `pos1`–`pos3`); this is the fixed numbering the
three ballots and the `Numbering` of the adequacy proof share. -/
def letterIdx : Letter → ℕ
  | .A => 0 | .B => 1 | .C => 2 | .D => 3 | .E => 4 | .F => 5

/-! ## Block-level accessors

A block is built with the graph input and the current gadget value `u` in scope:
the environment is `S = GraphTy × ℕ`. -/

/-- The block-level environment: graph input paired with the gadget value. -/
abbrev BEnv : Ty := .pair GraphTy .nat

/-- The graph input, inside a block. -/
def gx : Code BEnv GraphTy := .fst

/-- The gadget value `u`, inside a block. -/
def gu : Code BEnv .nat := .snd

/-- `M` as a number, inside a block. -/
def mNum' : Code BEnv .nat := .comp gx mNum

theorem mNum'_eval (g : GraphTy.denote) (u : ℕ) : mNum'.eval (g, u) = bigM g.1.length :=
  mNum_eval g

/-- The length-`M` list, inside a block. -/
def mList' : Code BEnv (.list (.pair (.pair (.pair .nat .nat) (.pair .nat .nat)) .nat)) :=
  .comp gx mList

/-- The canonical edge enumeration `[(edge, index)]`, inside a block. -/
def canonEnum : Code BEnv (.list (.pair (.pair .nat .nat) .nat)) :=
  .comp gx (.comp canonEdges .listEnum)

theorem canonEnum_eval (g : GraphTy.denote) (u : ℕ) :
    canonEnum.eval (g, u) = (canonEdges.eval g).zipIdx := rfl

/-! ## Letter runs -/

/-- The base number `6M·u + M·ξ(x)` of the letter run for `(u, x)`. -/
def letterBase (x : Letter) : Code BEnv .nat :=
  Code.add (Code.mul (Code.mul (.const .nat 6) mNum') gu)
    (Code.mul (.const .nat (letterIdx x)) mNum')

theorem letterBase_eval (lx : Letter) (g : GraphTy.denote) (u : ℕ) :
    (letterBase lx).eval (g, u) = 6 * bigM g.1.length * u + letterIdx lx * bigM g.1.length := by
  rw [letterBase, add_eval, mul_eval, mul_eval, mul_eval, mNum'_eval]; rfl

/-- The letter run for `(u, x)`: the `M` contiguous numbers `6M·u + M·ξ(x) +
[0, M)` — the members of supercandidate `x` in gadget `u`, in member order. -/
def letterRun (x : Letter) : Code BEnv (.list .nat) := runFrom (letterBase x) mList'

theorem letterRun_eval (lx : Letter) (g : GraphTy.denote) (u : ℕ) :
    (letterRun lx).eval (g, u) = (List.range (bigM g.1.length)).map
      (fun m ↦ 6 * bigM g.1.length * u + letterIdx lx * bigM g.1.length + m) := by
  rw [letterRun, runFrom_eval,
    show (mList'.eval (g, u)).length = bigM g.1.length from mList_length g]
  exact List.map_congr_left fun i _ ↦ by rw [letterBase_eval]

/-! ## Edge-candidate numbers and endpoint tests

Inside a gap the environment is `EEnv = BEnv × (edge × index)`: the block
environment paired with an enumerated canonical edge. -/

/-- The gap environment: the block environment paired with an enumerated edge. -/
abbrev EEnv : Ty := .pair BEnv (.pair (.pair .nat .nat) .nat)

/-- The smaller endpoint `e.i`, inside a gap. -/
def ei : Code EEnv .nat := .comp (.comp .snd .fst) .fst

/-- The larger endpoint `e.j`, inside a gap. -/
def ej : Code EEnv .nat := .comp (.comp .snd .fst) .snd

/-- The gadget value `u`, inside a gap. -/
def uu : Code EEnv .nat := .comp .fst .snd

/-- The edge's canonical index, inside a gap. -/
def idxc : Code EEnv .nat := .comp .snd .snd

/-- `n`, inside a gap. -/
def nNum'' : Code EEnv .nat := .comp (.comp .fst .fst) nNum

/-- `M`, inside a gap. -/
def mNum'' : Code EEnv .nat := .comp (.comp .fst .fst) mNum

theorem mNum''_eval (g : GraphTy.denote) (u : ℕ) (p : ℕ × ℕ) (i : ℕ) :
    mNum''.eval ((g, u), (p, i)) = bigM g.1.length := mNum_eval g

/-- The base edge number `6nM + 2·idx` (the `left` side); `right` adds one. -/
def baseEdge : Code EEnv .nat :=
  Code.add (Code.mul (Code.mul (.const .nat 6) nNum'') mNum'') (Code.mul (.const .nat 2) idxc)

theorem baseEdge_eval (g : GraphTy.denote) (u : ℕ) (p : ℕ × ℕ) (i : ℕ) :
    baseEdge.eval ((g, u), (p, i)) = 6 * g.1.length * bigM g.1.length + 2 * i := by
  rw [baseEdge, add_eval, mul_eval, mul_eval, mul_eval, mNum''_eval]; rfl

/-- The `left` edge candidate number `6nM + 2·idx`. -/
def leftNum : Code EEnv .nat := baseEdge

/-- The `right` edge candidate number `6nM + 2·idx + 1`. -/
def rightNum : Code EEnv .nat := Code.add baseEdge (.const .nat 1)

/-- Both sides of an edge, `left` then `right` — voter 2's midpoint gap. -/
def bothNum : Code EEnv (.list .nat) :=
  Code.append (.comp leftNum .listSingle) (.comp rightNum .listSingle)

theorem leftNum_eval (g : GraphTy.denote) (u : ℕ) (p : ℕ × ℕ) (i : ℕ) :
    leftNum.eval ((g, u), (p, i)) = 6 * g.1.length * bigM g.1.length + 2 * i :=
  baseEdge_eval g u p i

theorem rightNum_eval (g : GraphTy.denote) (u : ℕ) (p : ℕ × ℕ) (i : ℕ) :
    rightNum.eval ((g, u), (p, i)) = 6 * g.1.length * bigM g.1.length + 2 * i + 1 := by
  rw [rightNum, add_eval, baseEdge_eval]; rfl

theorem bothNum_eval (g : GraphTy.denote) (u : ℕ) (p : ℕ × ℕ) (i : ℕ) :
    bothNum.eval ((g, u), (p, i))
      = [6 * g.1.length * bigM g.1.length + 2 * i,
         6 * g.1.length * bigM g.1.length + 2 * i + 1] := by
  have h : bothNum.eval ((g, u), (p, i))
      = [leftNum.eval ((g, u), (p, i))] ++ [rightNum.eval ((g, u), (p, i))] := rfl
  rw [h, leftNum_eval, rightNum_eval]; rfl

/-- Test: the edge's smaller endpoint is the current gadget (`e.i = u`). -/
def eiEqU : Code EEnv .bool := .comp (.pair ei uu) .natEq

/-- Test: the edge's larger endpoint is the current gadget (`e.j = u`). -/
def ejEqU : Code EEnv .bool := .comp (.pair ej uu) .natEq

/-- Test: the current gadget is the edge's midpoint (`2u ≤ i + j < 2u + 2`, i.e.
`(i + j) / 2 = u`) — the language has no division, so the midpoint is tested by
the bracketing inequalities. -/
def midEqU : Code EEnv .bool :=
  Code.and (.comp (.pair (Code.mul (.const .nat 2) uu) (Code.add ei ej)) .natLe)
    (Code.lt (Code.add ei ej) (Code.add (Code.mul (.const .nat 2) uu) (.const .nat 2)))

theorem eiEqU_eval_true (g : GraphTy.denote) (u : ℕ) (p : ℕ × ℕ) (i : ℕ) :
    eiEqU.eval ((g, u), (p, i)) = true ↔ p.1 = u := by
  have h : eiEqU.eval ((g, u), (p, i)) = decide (p.1 = u) := rfl
  rw [h, decide_eq_true_iff]

theorem ejEqU_eval_true (g : GraphTy.denote) (u : ℕ) (p : ℕ × ℕ) (i : ℕ) :
    ejEqU.eval ((g, u), (p, i)) = true ↔ p.2 = u := by
  have h : ejEqU.eval ((g, u), (p, i)) = decide (p.2 = u) := rfl
  rw [h, decide_eq_true_iff]

theorem midEqU_eval_true (g : GraphTy.denote) (u : ℕ) (p : ℕ × ℕ) (i : ℕ) :
    midEqU.eval ((g, u), (p, i)) = true ↔ 2 * u ≤ p.1 + p.2 ∧ p.1 + p.2 < 2 * u + 2 := by
  have h : midEqU.eval ((g, u), (p, i))
      = (decide (2 * u ≤ p.1 + p.2) && Code.natLt.eval (p.1 + p.2, 2 * u + 2)) := rfl
  rw [h, Bool.and_eq_true, decide_eq_true_iff, natLt_eval_true]

/-! ## Gaps -/

/-- A single-side gap: filter the canonical edge enumeration by `test`, each
survivor emitting one number `emit`. -/
def sideGap (test : Code EEnv .bool) (emit : Code EEnv .nat) : Code BEnv (.list .nat) :=
  .comp (.pair .id canonEnum) (Code.filterMapEnv test emit)

theorem sideGap_eval (test : Code EEnv .bool) (emit : Code EEnv .nat) (g : GraphTy.denote) (u : ℕ) :
    (sideGap test emit).eval (g, u)
      = (((canonEdges.eval g).zipIdx).filter fun a ↦ test.eval ((g, u), a)).map
          fun a ↦ emit.eval ((g, u), a) := by
  have h : (sideGap test emit).eval (g, u)
      = (Code.filterMapEnv test emit).eval ((g, u), (canonEdges.eval g).zipIdx) := rfl
  rw [h, filterMapEnv_eval]

/-- A both-sides gap: filter by `test`, each survivor emitting the list `emit`. -/
def bothGap (test : Code EEnv .bool) (emit : Code EEnv (.list .nat)) : Code BEnv (.list .nat) :=
  .comp (.pair .id canonEnum) (filterFlatMapEnv test emit)

theorem bothGap_eval (test : Code EEnv .bool) (emit : Code EEnv (.list .nat))
    (g : GraphTy.denote) (u : ℕ) :
    (bothGap test emit).eval (g, u)
      = ((canonEdges.eval g).zipIdx.map
          fun a ↦ if test.eval ((g, u), a) = true then emit.eval ((g, u), a) else []).flatten :=
  rfl

/-! ## The three blocks

Each block is the six letters in the voter's local order, with the edge gaps
spliced in at their slots (`spec1`–`spec3`). -/

/-- Voter 1's gadget block: letters in `AEFBCD` order, `ℓ_e` after `A` and `r_e`
after `B` (both at the smaller endpoint, `e.i = u`). -/
def block1 : Code BEnv (.list .nat) :=
  Code.append (letterRun .A) (Code.append (sideGap eiEqU leftNum) (Code.append (letterRun .E)
    (Code.append (letterRun .F) (Code.append (letterRun .B) (Code.append (sideGap eiEqU rightNum)
      (Code.append (letterRun .C) (letterRun .D)))))))

/-- Voter 2's gadget block: letters in `BDFACE` order, both edge candidates after
`F` (at the midpoint, `e.mid = u`), emitted left-then-right. -/
def block2 : Code BEnv (.list .nat) :=
  Code.append (letterRun .B) (Code.append (letterRun .D) (Code.append (letterRun .F)
    (Code.append (bothGap midEqU bothNum) (Code.append (letterRun .A)
      (Code.append (letterRun .C) (letterRun .E))))))

/-- Voter 3's gadget block: letters in `CDEABF` order, `r_e` after `D` and `ℓ_e`
after `B` (both at the larger endpoint, `e.j = u`). -/
def block3 : Code BEnv (.list .nat) :=
  Code.append (letterRun .C) (Code.append (letterRun .D) (Code.append (sideGap ejEqU rightNum)
    (Code.append (letterRun .E) (Code.append (letterRun .A) (Code.append (letterRun .B)
      (Code.append (sideGap ejEqU leftNum) (letterRun .F)))))))

/-! ## The descending gadget list -/

/-- The gadget values in descending order `[n-1, …, 0]` — voter 2's gadget
order. Built by mapping `i ↦ (n-1) − i` over the ascending positions; the
language has no list reversal. -/
def gadgetDesc : Code GraphTy (.list .nat) :=
  .comp (.pair (subC gNumVertices (.const .nat 1)) positions) (.listMapEnv (subC .fst .snd))

theorem gadgetDesc_eval (g : GraphTy.denote) :
    gadgetDesc.eval g = (List.range g.1.length).map fun i ↦ (g.1.length - 1) - i := by
  have h : gadgetDesc.eval g = (positions.eval g).map
      fun i ↦ (subC (σ := .pair .nat .nat) .fst .snd).eval (g.1.length - 1, i) := rfl
  rw [h, positions_eval]; rfl

/-! ## The three ballots -/

/-- Voter 1's ballot: gadgets ascending, each expanded to `block1`. -/
def ballot1 : Code GraphTy (.list .nat) :=
  .comp (.pair .id positions) (.comp (.listMapEnv block1) .listJoin)

/-- Voter 2's ballot: gadgets descending, each expanded to `block2`. -/
def ballot2 : Code GraphTy (.list .nat) :=
  .comp (.pair .id gadgetDesc) (.comp (.listMapEnv block2) .listJoin)

/-- Voter 3's ballot: gadgets ascending, each expanded to `block3`. -/
def ballot3 : Code GraphTy (.list .nat) :=
  .comp (.pair .id positions) (.comp (.listMapEnv block3) .listJoin)

theorem ballot1_eval (g : GraphTy.denote) :
    ballot1.eval g = ((List.range g.1.length).map fun u ↦ block1.eval (g, u)).flatten := by
  have h : ballot1.eval g = ((positions.eval g).map fun u ↦ block1.eval (g, u)).flatten := rfl
  rw [h, positions_eval]

theorem ballot2_eval (g : GraphTy.denote) :
    ballot2.eval g = ((gadgetDesc.eval g).map fun u ↦ block2.eval (g, u)).flatten := rfl

theorem ballot3_eval (g : GraphTy.denote) :
    ballot3.eval g = ((List.range g.1.length).map fun u ↦ block3.eval (g, u)).flatten := by
  have h : ballot3.eval g = ((positions.eval g).map fun u ↦ block3.eval (g, u)).flatten := rfl
  rw [h, positions_eval]

/-- The three ballots, as the profile the produced instance carries. -/
def profileBallots : Code GraphTy (.list (.list .nat)) :=
  Code.cons ballot1 (Code.cons ballot2 (Code.cons ballot3 (.const (.list (.list .nat)) [])))

theorem profileBallots_eval (g : GraphTy.denote) :
    profileBallots.eval g = [ballot1.eval g, ballot2.eval g, ballot3.eval g] := rfl

end Cert
end Hardness
