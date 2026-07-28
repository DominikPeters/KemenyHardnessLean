import KemenyHardness.FromMaxCut.AbsBallots

/-!
# The emitted ballots decode to the three voters

The last step of the ballot half of the adequacy proof. `AbsBallots.lean` built,
for each voter, an *abstract* candidate list that is strictly sorted by that
voter and lists every candidate; this file matches those lists with what the
program emits,

  `(absBallot i x).map (candNumbering x).num = (ballot i).eval x`,

and then reads off the deliverable through `decodeBallot_eq_mapOrder'`:

  `decodeBallot |candList| ((ballot i).eval x)
     = mapOrder (candEquiv x) ((spec i).ranking M)`.

## How the two sides meet

Both a ballot and a block are built by the same three steps on both sides, and
each step is matched by one lemma:

* **a letter run** — `letterSeg` enumerates `Fin M`, `letterRun` the shifted
  `range M`; `map_finRange_val` identifies them and `candNumbering_inl` matches
  the numbers;
* **a gap** — `gapSeg`/`bothSeg` filter and map over *abstract* edges,
  `sideGap`/`bothGap` over the program's enumerated canonical list.
  `canonEdges_zipIdx` rewrites the latter as the former under the encoding
  `e ↦ (toPair e, idx e)`, and `map_filter_map_comp` (resp.
  `flatten_map_ite_comp`) then only asks that the *test* and the *emission*
  agree along that encoding — which is what `eiEqU_num`, `ejEqU_num`,
  `midEqU_num` and `leftNum_num`, `rightNum_num`, `bothNum_num` say;
* **the concatenations** — a block is a `flatten` of segments against a chain of
  `Code.append`, a ballot a `flatten` of blocks against a `flatMap` over the
  gadget values, matched by `ballot_num` plus the identification of the abstract
  gadget list with the program's (`map_val_finRange`, `map_val_gadgetDescList`).

No arithmetic is done anywhere: every number is produced on both sides by the
same expression, so the matching lemmas close by `rfl` after one rewrite.
-/

namespace Hardness
namespace Cert

/-! ## Three list identities -/

section Lists

variable {α β γ : Type*}

/-- **Filter-then-map across a change of representation.** The program filters
and maps over *encoded* items, the abstract list over the objects they encode;
when the test and the emission agree along the encoding `g`, the two agree. -/
theorem map_filter_map_comp (l : List α) (g : α → β) (T : β → Bool) (E : β → γ)
    (p : α → Bool) (f : α → γ) (hT : ∀ a, T (g a) = p a) (hE : ∀ a, E (g a) = f a) :
    ((l.map g).filter T).map E = (l.filter p).map f := by
  rw [map_filter_comm, List.map_map, show (fun a ↦ T (g a)) = p from funext hT,
    show E ∘ g = f from funext hE]

/-- The same across the keep-or-drop idiom emitting a *list* per survivor —
voter 2's midpoint gap, where each edge contributes both its candidates. -/
theorem flatten_map_ite_comp (l : List α) (g : α → β) (T : β → Bool) (E : β → List γ)
    (p : α → Bool) (f : α → List γ) (hT : ∀ a, T (g a) = p a) (hE : ∀ a, E (g a) = f a) :
    ((l.map g).map fun b ↦ if T b = true then E b else []).flatten
      = (l.filter p).flatMap f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.map_cons, List.flatten_cons, List.filter_cons, hT a]
    by_cases h : p a = true
    · rw [if_pos h, if_pos h, List.flatMap_cons, ih, hE a]
    · rw [if_neg h, if_neg h, ih, List.nil_append]

/-- Running over `Fin`-indexed positions is running over `ℕ`-indexed ones — the
abstract lists index by `Fin n`, the program's by `range n`. -/
theorem map_finRange_val (N : ℕ) (f : ℕ → β) :
    (List.finRange N).map (fun m ↦ f m.val) = (List.range N).map f := by
  rw [← List.map_coe_finRange_eq_range (n := N), List.map_map]
  rfl

end Lists

variable {x : GraphTy.denote}

/-! ## Letter runs -/

/-- **A letter run matches**: the `M` members of a supercandidate, numbered, are
the contiguous run the program emits. -/
theorem letterSeg_num (u : Fin (decodeNumbered x).n) (lx : Letter) :
    (letterSeg x u lx).map (candNumbering x).num = (letterRun lx).eval (x, u.val) := by
  rw [letterSeg, List.map_map, letterRun_eval, ← map_finRange_val]
  exact List.map_congr_left fun m _ ↦ candNumbering_inl u lx m

/-! ## Edge tests and edge numbers

Each is one program-side fact about an encoded edge `(toPair e, idx e)`, matched
with the abstract test or number. -/

/-- The program's smaller-endpoint test is the abstract filter `e.i = u`. -/
theorem eiEqU_num (u : Fin (decodeNumbered x).n) (e : DEdge x) :
    eiEqU.eval ((x, u.val), (toPair e, (edgePairEquiv x e).val))
      = edgeAt (fun e ↦ e.i) u e := by
  rw [Bool.eq_iff_iff, eiEqU_eval_true]
  simp only [edgeAt, decide_eq_true_eq, ← Fin.val_inj, toPair]

/-- The program's larger-endpoint test is the abstract filter `e.j = u`. -/
theorem ejEqU_num (u : Fin (decodeNumbered x).n) (e : DEdge x) :
    ejEqU.eval ((x, u.val), (toPair e, (edgePairEquiv x e).val))
      = edgeAt (fun e ↦ e.j) u e := by
  rw [Bool.eq_iff_iff, ejEqU_eval_true]
  simp only [edgeAt, decide_eq_true_eq, ← Fin.val_inj, toPair]

/-- The program's bracketing midpoint test is the abstract filter `e.mid = u` —
the one place the division-free encoding has to be undone. -/
theorem midEqU_num (u : Fin (decodeNumbered x).n) (e : DEdge x) :
    midEqU.eval ((x, u.val), (toPair e, (edgePairEquiv x e).val))
      = edgeAt (fun e ↦ e.mid) u e := by
  rw [Bool.eq_iff_iff, midEqU_eval_true]
  simp only [edgeAt, decide_eq_true_eq, ← Fin.val_inj, EdgePair.mid_val, toPair]
  omega

/-- The `left` candidate's number is the numbering's. -/
theorem leftNum_num (u : Fin (decodeNumbered x).n) (e : DEdge x) :
    leftNum.eval ((x, u.val), (toPair e, (edgePairEquiv x e).val))
      = (candNumbering x).num (Sum.inr (e, Side.left)) := by
  rw [leftNum_eval, candNumbering_inr]
  simp [sideIdx]

/-- The `right` candidate's number is the numbering's. -/
theorem rightNum_num (u : Fin (decodeNumbered x).n) (e : DEdge x) :
    rightNum.eval ((x, u.val), (toPair e, (edgePairEquiv x e).val))
      = (candNumbering x).num (Sum.inr (e, Side.right)) := by
  rw [rightNum_eval, candNumbering_inr]
  simp [sideIdx]

/-- Voter 2's gap emits both candidates of an edge, left then right. -/
theorem bothNum_num (u : Fin (decodeNumbered x).n) (e : DEdge x) :
    bothNum.eval ((x, u.val), (toPair e, (edgePairEquiv x e).val))
      = [(candNumbering x).num (Sum.inr (e, Side.left)),
         (candNumbering x).num (Sum.inr (e, Side.right))] := by
  rw [bothNum_eval, candNumbering_inr, candNumbering_inr]
  simp [sideIdx]

/-! ## Gaps -/

/-- **A single-side gap matches**, given that its test and its emission agree
with the abstract ones on every encoded edge. -/
theorem gapSeg_num (u : Fin (decodeNumbered x).n) (s : Side) (p : DEdge x → Bool)
    (test : Code EEnv .bool) (emit : Code EEnv .nat)
    (htest : ∀ e : DEdge x, test.eval ((x, u.val), (toPair e, (edgePairEquiv x e).val)) = p e)
    (hemit : ∀ e : DEdge x, emit.eval ((x, u.val), (toPair e, (edgePairEquiv x e).val))
      = (candNumbering x).num (Sum.inr (e, s))) :
    (gapSeg x p s).map (candNumbering x).num = (sideGap test emit).eval (x, u.val) := by
  rw [sideGap_eval, canonEdges_zipIdx, gapSeg, List.map_map]
  symm
  exact map_filter_map_comp (edgeOrder x) _ _ _ p _ htest hemit

/-- **A both-sides gap matches.** -/
theorem bothSeg_num (u : Fin (decodeNumbered x).n) (p : DEdge x → Bool)
    (test : Code EEnv .bool) (emit : Code EEnv (.list .nat))
    (htest : ∀ e : DEdge x, test.eval ((x, u.val), (toPair e, (edgePairEquiv x e).val)) = p e)
    (hemit : ∀ e : DEdge x, emit.eval ((x, u.val), (toPair e, (edgePairEquiv x e).val))
      = [(candNumbering x).num (Sum.inr (e, Side.left)),
         (candNumbering x).num (Sum.inr (e, Side.right))]) :
    (bothSeg x p).map (candNumbering x).num = (bothGap test emit).eval (x, u.val) := by
  rw [bothGap_eval, canonEdges_zipIdx, bothSeg, List.map_flatMap]
  symm
  exact flatten_map_ite_comp (edgeOrder x) _ _ _ p _ htest hemit

/-- Voter 1's first gap. -/
theorem gapSeg_i_left_num (u : Fin (decodeNumbered x).n) :
    (gapSeg x (edgeAt (fun e ↦ e.i) u) Side.left).map (candNumbering x).num
      = (sideGap eiEqU leftNum).eval (x, u.val) :=
  gapSeg_num u Side.left _ eiEqU leftNum (eiEqU_num u) (leftNum_num u)

/-- Voter 1's second gap. -/
theorem gapSeg_i_right_num (u : Fin (decodeNumbered x).n) :
    (gapSeg x (edgeAt (fun e ↦ e.i) u) Side.right).map (candNumbering x).num
      = (sideGap eiEqU rightNum).eval (x, u.val) :=
  gapSeg_num u Side.right _ eiEqU rightNum (eiEqU_num u) (rightNum_num u)

/-- Voter 3's first gap. -/
theorem gapSeg_j_right_num (u : Fin (decodeNumbered x).n) :
    (gapSeg x (edgeAt (fun e ↦ e.j) u) Side.right).map (candNumbering x).num
      = (sideGap ejEqU rightNum).eval (x, u.val) :=
  gapSeg_num u Side.right _ ejEqU rightNum (ejEqU_num u) (rightNum_num u)

/-- Voter 3's second gap. -/
theorem gapSeg_j_left_num (u : Fin (decodeNumbered x).n) :
    (gapSeg x (edgeAt (fun e ↦ e.j) u) Side.left).map (candNumbering x).num
      = (sideGap ejEqU leftNum).eval (x, u.val) :=
  gapSeg_num u Side.left _ ejEqU leftNum (ejEqU_num u) (leftNum_num u)

/-- Voter 2's midpoint gap. -/
theorem bothSeg_mid_num (u : Fin (decodeNumbered x).n) :
    (bothSeg x (edgeAt (fun e ↦ e.mid) u)).map (candNumbering x).num
      = (bothGap midEqU bothNum).eval (x, u.val) :=
  bothSeg_num u _ midEqU bothNum (midEqU_num u) (bothNum_num u)

/-! ## The three blocks -/

theorem absBlock1_num (u : Fin (decodeNumbered x).n) :
    (absBlock1 x u).map (candNumbering x).num = block1.eval (x, u.val) := by
  simp only [absBlock1, block1Segs, block1, List.map_cons, List.map_nil, List.flatten_cons,
    List.flatten_nil, List.map_append, List.append_nil, append_eval, letterSeg_num,
    gapSeg_i_left_num, gapSeg_i_right_num]

theorem absBlock2_num (u : Fin (decodeNumbered x).n) :
    (absBlock2 x u).map (candNumbering x).num = block2.eval (x, u.val) := by
  simp only [absBlock2, block2Segs, block2, List.map_cons, List.map_nil, List.flatten_cons,
    List.flatten_nil, List.map_append, List.append_nil, append_eval, letterSeg_num,
    bothSeg_mid_num]

theorem absBlock3_num (u : Fin (decodeNumbered x).n) :
    (absBlock3 x u).map (candNumbering x).num = block3.eval (x, u.val) := by
  simp only [absBlock3, block3Segs, block3, List.map_cons, List.map_nil, List.flatten_cons,
    List.flatten_nil, List.map_append, List.append_nil, append_eval, letterSeg_num,
    gapSeg_j_left_num, gapSeg_j_right_num]

/-! ## The three ballots -/

/-- **A ballot matches as soon as its blocks do**: numbering commutes with both
the `flatten` and the pass to the program's `ℕ`-valued gadget list. -/
theorem ballot_num (gl : List (Fin (decodeNumbered x).n))
    (blk : Fin (decodeNumbered x).n → List (DCand x)) (prog : ℕ → List ℕ)
    (hblk : ∀ u, (blk u).map (candNumbering x).num = prog u.val) :
    ((gl.map blk).flatten).map (candNumbering x).num = ((gl.map Fin.val).map prog).flatten := by
  rw [List.map_flatten, List.map_map, List.map_map]
  exact congrArg List.flatten (List.map_congr_left fun u _ ↦ hblk u)

/-- The ascending gadget list, as the program spells it. -/
theorem map_val_finRange (N : ℕ) : (List.finRange N).map Fin.val = List.range N :=
  List.map_coe_finRange_eq_range

/-- Voter 2's descending gadget list, as the program spells it. -/
theorem map_val_gadgetDescList (n : ℕ) :
    (gadgetDescList n).map Fin.val = (List.range n).map fun i ↦ n - 1 - i := by
  rw [gadgetDescList, List.map_map, ← map_val_finRange n, List.map_map]
  rfl

theorem absBallot1_num (x : GraphTy.denote) :
    (absBallot1 x).map (candNumbering x).num = ballot1.eval x := by
  rw [absBallot1, ballot_num (List.finRange _) (absBlock1 x) (fun u ↦ block1.eval (x, u))
    (absBlock1_num (x := x)), map_val_finRange, ballot1_eval, decodeNumbered_n]

theorem absBallot2_num (x : GraphTy.denote) :
    (absBallot2 x).map (candNumbering x).num = ballot2.eval x := by
  rw [absBallot2, ballot_num (gadgetDescList _) (absBlock2 x) (fun u ↦ block2.eval (x, u))
    (absBlock2_num (x := x)), map_val_gadgetDescList, ballot2_eval, gadgetDesc_eval,
    decodeNumbered_n]

theorem absBallot3_num (x : GraphTy.denote) :
    (absBallot3 x).map (candNumbering x).num = ballot3.eval x := by
  rw [absBallot3, ballot_num (List.finRange _) (absBlock3 x) (fun u ↦ block3.eval (x, u))
    (absBlock3_num (x := x)), map_val_finRange, ballot3_eval, decodeNumbered_n]

/-! ## The decoded ballots -/

/-- **The relabeling bijection of the adequacy proof**: abstract candidates
versus the positions of the emitted candidate list, which is how the decoded
instance names its alternatives. -/
noncomputable def candEquiv (x : GraphTy.denote) : DCand x ≃ Fin (candList.eval x).length :=
  (candNumbering x).equivFin.trans (finCongr (candNumbering_size x))

/-- **Voter 1 decodes correctly.** -/
theorem decodeBallot_ballot1 (x : GraphTy.denote) :
    decodeBallot (candList.eval x).length (ballot1.eval x)
      = mapOrder (candEquiv x) ((dspec1 x).ranking (bigM (decodeNumbered x).n)) := by
  rw [← absBallot1_num]
  exact decodeBallot_eq_mapOrder' _ _ _ (absBallot1_pairwise x) (absBallot1_complete x) _

/-- **Voter 2 decodes correctly.** -/
theorem decodeBallot_ballot2 (x : GraphTy.denote) :
    decodeBallot (candList.eval x).length (ballot2.eval x)
      = mapOrder (candEquiv x) ((dspec2 x).ranking (bigM (decodeNumbered x).n)) := by
  rw [← absBallot2_num]
  exact decodeBallot_eq_mapOrder' _ _ _ (absBallot2_pairwise x) (absBallot2_complete x) _

/-- **Voter 3 decodes correctly.** -/
theorem decodeBallot_ballot3 (x : GraphTy.denote) :
    decodeBallot (candList.eval x).length (ballot3.eval x)
      = mapOrder (candEquiv x) ((dspec3 x).ranking (bigM (decodeNumbered x).n)) := by
  rw [← absBallot3_num]
  exact decodeBallot_eq_mapOrder' _ _ _ (absBallot3_pairwise x) (absBallot3_complete x) _

/-- **The emitted profile decodes to the abstract profile**, relabeled along the
candidate numbering — the deliverable the adequacy proof consumes. -/
theorem decodeProfile_eq (x : GraphTy.denote) :
    (profileBallots.eval x).map (decodeBallot (candList.eval x).length)
      = (kemenyProfile (decodeNumbered x).n (decodeNumbered x).G
          (bigM (decodeNumbered x).n)).map (mapOrder (candEquiv x)) := by
  rw [profileBallots_eval, kemenyProfile]
  simp only [List.map_cons, List.map_nil]
  rw [decodeBallot_ballot1, decodeBallot_ballot2, decodeBallot_ballot3]

end Cert
end Hardness
