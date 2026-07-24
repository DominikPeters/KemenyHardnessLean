import Kemeny.FromMaxCut.CandNumbering

/-!
# The three voters as sorted candidate lists

`decodeBallot_eq_mapOrder` reduces each voter's adequacy obligation to two
combinatorial facts about a list of *abstract* candidates — it is strictly sorted
by the voter's ranking, and it lists every candidate — plus one identity matching
the program's ballot with that list mapped through the numbering. This file
builds the three lists and proves the two facts; the identity is the next step.

## Shape

A ballot is a `flatten` of *levelled segments* at two nesting levels, exactly as
the program builds it:

* **ballot level** — one segment per gadget, levelled by `gadgetPos` (ascending
  vertex index for voters 1 and 3, descending for voter 2, `gadgetDescList`);
* **block level** — inside a gadget, one segment per *slot*: the six letter runs
  at the odd slots `2p + 1` and the edge gaps at the even slots `2p + 2`, in the
  voter's local order.

`pairwise_segments` handles both levels. At the block level the levels are the
literal slot numerals of the voter's local order (voter 1: `1, 2, 3, 5, 7, 8, 9,
11`), so the increasing-levels hypothesis is a numeral check; at the ballot level
they are `0, 1, …, n − 1`.

A segment is fit for both levels when it is `GoodSeg`: one slot, one gadget,
internally sorted. `block_pairwise`/`block_gpos` turn a list of good segments
into a block, and `ballot_pairwise`/`ballot_complete` turn the blocks into a
ballot — so each voter costs only its segment table and the check that its slot
numerals increase.

## Why the comparison never sees a key

`VoterSpec.lt_iff_lex` states the ranking as the lexicographic comparison of the
triple `(gpos, slot, tiek)`, uniformly in the candidate kind — the one place the
`Sum` is destructured. Both applications of `pairwise_segments` then instantiate
its `hcross` with the first `Or.inl` of that disjunction, and each segment's own
sortedness is a `tiek` comparison at a fixed slot: member index inside a letter
run, `EdgePair.tie` inside a gap. The latter is where `edgeOrder_pairwise`
enters — `tie e s = 2·K(e) + side` with `K` the canonical sort key.
-/

namespace Hardness

/-! ## The ranking as a lexicographic triple -/

namespace VoterSpec

variable {n M : ℕ} {G : SimpleGraph (Fin n)}

/-- The gadget level of a candidate: which gadget block it sits in. -/
def gpos (V : VoterSpec n G) : Cand n M G → ℕ
  | .inl (i, _, _) => V.gadgetPos i
  | .inr (e, s) => V.gadgetPos (V.edgeGadget e s)

/-- The slot of a candidate inside its gadget block: letters at the odd slots
`2p + 1`, edge candidates at the even gap slots `2p + 2`. -/
def slot (V : VoterSpec n G) : Cand n M G → ℕ
  | .inl (i, x, _) => 2 * V.localPos i x + 1
  | .inr (e, s) => 2 * V.localPos (V.edgeGadget e s) (V.gapLetter e s) + 2

/-- The tie-break of a candidate inside its slot: the member index inside a
letter run, `EdgePair.tie` inside a gap. -/
def tiek (_V : VoterSpec n G) : Cand n M G → ℕ
  | .inl (_, _, m) => m.val
  | .inr (e, s) => e.tie s

@[simp] theorem gpos_inl (V : VoterSpec n G) (i : Fin n) (x : Letter) (m : Fin M) :
    V.gpos (Sum.inl (i, x, m)) = V.gadgetPos i := rfl

@[simp] theorem gpos_inr (V : VoterSpec n G) (e : EdgePair n G) (s : Side) :
    V.gpos (M := M) (Sum.inr (e, s)) = V.gadgetPos (V.edgeGadget e s) := rfl

@[simp] theorem slot_inl (V : VoterSpec n G) (i : Fin n) (x : Letter) (m : Fin M) :
    V.slot (Sum.inl (i, x, m)) = 2 * V.localPos i x + 1 := rfl

@[simp] theorem slot_inr (V : VoterSpec n G) (e : EdgePair n G) (s : Side) :
    V.slot (M := M) (Sum.inr (e, s)) =
      2 * V.localPos (V.edgeGadget e s) (V.gapLetter e s) + 2 := rfl

@[simp] theorem tiek_inl (V : VoterSpec n G) (i : Fin n) (x : Letter) (m : Fin M) :
    V.tiek (Sum.inl (i, x, m)) = m.val := rfl

@[simp] theorem tiek_inr (V : VoterSpec n G) (e : EdgePair n G) (s : Side) :
    V.tiek (M := M) (Sum.inr (e, s)) = e.tie s := rfl

theorem key_eq (V : VoterSpec n G) (c : Cand n M G) :
    V.key c = toLex (V.gpos c, toLex (V.slot c, V.tiek c)) := by
  rcases c with ⟨i, x, m⟩ | ⟨e, s⟩ <;> rfl

/-- **The voter, as one lexicographic comparison.** The only place a candidate
is destructured: everything downstream compares the triple `(gpos, slot,
tiek)`. -/
theorem lt_iff_lex (V : VoterSpec n G) {c c' : Cand n M G} :
    (V.ranking M).lt c c' ↔
      V.gpos c < V.gpos c' ∨ V.gpos c = V.gpos c' ∧
        (V.slot c < V.slot c' ∨ V.slot c = V.slot c' ∧ V.tiek c < V.tiek c') := by
  rw [ranking_lt_iff, key_eq, key_eq]
  simp only [Prod.Lex.lt_iff, ofLex_toLex]

/-- The within-block order: same gadget, compare slot then tie. -/
def slotLex (V : VoterSpec n G) (M : ℕ) (a b : Cand n M G) : Prop :=
  V.slot a < V.slot b ∨ V.slot a = V.slot b ∧ V.tiek a < V.tiek b

/-- Inside one gadget block — where `gpos` is constant — the within-block order
*is* the voter's order. -/
theorem lt_of_slotLex (V : VoterSpec n G) {M : ℕ} {a b : Cand n M G}
    (hg : V.gpos a = V.gpos b) (h : V.slotLex M a b) : (V.ranking M).lt a b :=
  lt_iff_lex V |>.mpr (Or.inr ⟨hg, h⟩)

end VoterSpec

/-! ## The abstract segments -/

namespace Cert

open Hardness.VoterSpec

variable {x : GraphTy.denote}

/-- The `EdgePair`s of the decoded graph — the abstract edges the gaps hold. -/
abbrev DEdge (x : GraphTy.denote) : Type :=
  EdgePair (decodeNumbered x).n (decodeNumbered x).G

/-- A **letter run**: the `M` members of supercandidate `lx` in gadget `u`, in
member order. -/
def letterSeg (x : GraphTy.denote) (u : Fin (decodeNumbered x).n) (lx : Letter) :
    List (DCand x) :=
  (List.finRange (bigM (decodeNumbered x).n)).map fun m ↦ Sum.inl (u, lx, m)

/-- A **single-side gap**: the `s`-side candidates of the edges `p` selects, in
canonical order. -/
def gapSeg (x : GraphTy.denote) (p : DEdge x → Bool) (s : Side) : List (DCand x) :=
  ((edgeOrder x).filter p).map fun e ↦ Sum.inr (e, s)

/-- A **both-sides gap**: both candidates of each edge `p` selects, left then
right — voter 2's midpoint gap. -/
def bothSeg (x : GraphTy.denote) (p : DEdge x → Bool) : List (DCand x) :=
  ((edgeOrder x).filter p).flatMap fun e ↦ [Sum.inr (e, .left), Sum.inr (e, .right)]

/-! ### Membership -/

theorem mem_letterSeg_iff {u : Fin (decodeNumbered x).n} {lx : Letter} {c : DCand x} :
    c ∈ letterSeg x u lx ↔ ∃ m, c = Sum.inl (u, lx, m) := by
  simp only [letterSeg, List.mem_map, List.mem_finRange, true_and]
  exact ⟨fun ⟨m, h⟩ ↦ ⟨m, h.symm⟩, fun ⟨m, h⟩ ↦ ⟨m, h.symm⟩⟩

theorem mem_letterSeg {u : Fin (decodeNumbered x).n} {lx : Letter}
    (m : Fin (bigM (decodeNumbered x).n)) : (Sum.inl (u, lx, m) : DCand x) ∈ letterSeg x u lx :=
  mem_letterSeg_iff.mpr ⟨m, rfl⟩

theorem mem_gapSeg_iff {p : DEdge x → Bool} {s : Side} {c : DCand x} :
    c ∈ gapSeg x p s ↔ ∃ e, p e = true ∧ c = Sum.inr (e, s) := by
  simp only [gapSeg, List.mem_map, List.mem_filter, mem_edgeOrder, true_and]
  exact ⟨fun ⟨e, he, h⟩ ↦ ⟨e, he, h.symm⟩, fun ⟨e, he, h⟩ ↦ ⟨e, he, h.symm⟩⟩

theorem mem_gapSeg {p : DEdge x → Bool} {s : Side} {e : DEdge x} (he : p e = true) :
    (Sum.inr (e, s) : DCand x) ∈ gapSeg x p s :=
  mem_gapSeg_iff.mpr ⟨e, he, rfl⟩

theorem mem_bothSeg_iff {p : DEdge x → Bool} {c : DCand x} :
    c ∈ bothSeg x p ↔ ∃ e s, p e = true ∧ c = Sum.inr (e, s) := by
  simp only [bothSeg, List.mem_flatMap, List.mem_filter, mem_edgeOrder, true_and]
  constructor
  · rintro ⟨e, he, hc⟩
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨e, .left, he, rfl⟩
    · rcases List.mem_cons.mp hc with rfl | hc
      · exact ⟨e, .right, he, rfl⟩
      · exact absurd hc (List.not_mem_nil)
  · rintro ⟨e, s, he, rfl⟩
    exact ⟨e, he, by cases s <;> simp only [List.mem_cons, List.not_mem_nil, or_false] <;> tauto⟩

theorem mem_bothSeg {p : DEdge x → Bool} {e : DEdge x} (s : Side) (he : p e = true) :
    (Sum.inr (e, s) : DCand x) ∈ bothSeg x p :=
  mem_bothSeg_iff.mpr ⟨e, s, he, rfl⟩

/-! ### Segments are good

Each segment sits at one slot and in one gadget, and is internally sorted — the
three hypotheses the two applications of `pairwise_segments` consume. -/

/-- The abstract tie key in the arithmetic form `edgeOrder_pairwise` speaks
about: twice the canonical sort key `K (e) = e.i·n + e.j`, plus the side. -/
theorem tie_eq (e : DEdge x) (s : Side) :
    e.tie s = 2 * (e.i.val * x.1.length + e.j.val) + sideIdx s := by
  cases s <;> rfl

/-- A voter of a decoded instance. -/
abbrev DVoter (x : GraphTy.denote) : Type :=
  VoterSpec (decodeNumbered x).n (decodeNumbered x).G

/-- **What a block's segment supplies.** -/
structure GoodSeg (V : DVoter x) (u : Fin (decodeNumbered x).n) (lev : ℕ)
    (l : List (DCand x)) : Prop where
  /-- Every member sits at the segment's slot. -/
  slot_eq : ∀ c ∈ l, V.slot c = lev
  /-- Every member sits in gadget `u`. -/
  gpos_eq : ∀ c ∈ l, V.gpos c = V.gadgetPos u
  /-- The segment is sorted within its slot. -/
  sorted : l.Pairwise (V.slotLex _)

/-- A letter run is good: constant slot `2p + 1`, constant gadget, member index
increasing. -/
theorem goodSeg_letterSeg (V : DVoter x) (u : Fin (decodeNumbered x).n) (lx : Letter) (lev : ℕ)
    (hlev : 2 * V.localPos u lx + 1 = lev) :
    GoodSeg V u lev (letterSeg x u lx) where
  slot_eq c hc := by obtain ⟨m, rfl⟩ := mem_letterSeg_iff.mp hc; exact hlev
  gpos_eq c hc := by obtain ⟨m, rfl⟩ := mem_letterSeg_iff.mp hc; rfl
  sorted := by
    rw [letterSeg, List.pairwise_map]
    exact (List.sortedLT_finRange _).pairwise.imp fun {_ _} h ↦ Or.inr ⟨rfl, h⟩

/-- The filter a gap uses: the edges whose gadget for this side is `u`. -/
def edgeAt (f : DEdge x → Fin (decodeNumbered x).n) (u : Fin (decodeNumbered x).n) :
    DEdge x → Bool := fun e ↦ decide (f e = u)

theorem edgeAt_eq {f : DEdge x → Fin (decodeNumbered x).n} {u : Fin (decodeNumbered x).n}
    {e : DEdge x} (h : edgeAt f u e = true) : f e = u := of_decide_eq_true h

theorem edgeAt_self (f : DEdge x → Fin (decodeNumbered x).n) (e : DEdge x) :
    edgeAt f (f e) e = true := by simp [edgeAt]

/-- A single-side gap is good: the slot is constant because the voters' local
orders do not depend on the gadget, the gadget is constant because that is what
the filter tests, and the order is `EdgePair.tie`, i.e. the canonical edge
order. -/
theorem goodSeg_gapSeg (V : DVoter x) (u : Fin (decodeNumbered x).n) (s : Side)
    (p : DEdge x → Bool) (lev : ℕ)
    (hslot : ∀ e : DEdge x, V.slot (M := bigM (decodeNumbered x).n) (Sum.inr (e, s)) = lev)
    (hgad : ∀ e : DEdge x, p e = true → V.edgeGadget e s = u) :
    GoodSeg V u lev (gapSeg x p s) where
  slot_eq c hc := by obtain ⟨e, -, rfl⟩ := mem_gapSeg_iff.mp hc; exact hslot e
  gpos_eq c hc := by
    obtain ⟨e, he, rfl⟩ := mem_gapSeg_iff.mp hc
    rw [gpos_inr, hgad e he]
  sorted := by
    rw [gapSeg, List.pairwise_map]
    refine ((edgeOrder_pairwise x).filter p).imp fun {e e'} h ↦ Or.inr ⟨?_, ?_⟩
    · rw [hslot e, hslot e']
    · rw [tiek_inr, tiek_inr, tie_eq, tie_eq]
      omega

/-- A both-sides gap is good; inside one edge `left` precedes `right`, which is
`tie`'s low bit. -/
theorem goodSeg_bothSeg (V : DVoter x) (u : Fin (decodeNumbered x).n)
    (p : DEdge x → Bool) (lev : ℕ)
    (hslot : ∀ (e : DEdge x) (s : Side),
      V.slot (M := bigM (decodeNumbered x).n) (Sum.inr (e, s)) = lev)
    (hgad : ∀ (e : DEdge x) (s : Side), p e = true → V.edgeGadget e s = u) :
    GoodSeg V u lev (bothSeg x p) where
  slot_eq c hc := by obtain ⟨e, s, -, rfl⟩ := mem_bothSeg_iff.mp hc; exact hslot e s
  gpos_eq c hc := by
    obtain ⟨e, s, he, rfl⟩ := mem_bothSeg_iff.mp hc
    rw [gpos_inr, hgad e s he]
  sorted := by
    rw [bothSeg, List.pairwise_flatMap]
    refine ⟨fun e _ ↦ ?_, ((edgeOrder_pairwise x).filter p).imp fun {e e'} h a ha b hb ↦ ?_⟩
    · refine List.pairwise_cons.mpr ⟨fun c hc ↦ ?_, List.pairwise_singleton _ _⟩
      rcases List.mem_singleton.mp hc with rfl
      exact Or.inr ⟨(hslot e .left).trans (hslot e .right).symm, by
        rw [tiek_inr, tiek_inr, tie_eq, tie_eq]; simp [sideIdx]⟩
    · obtain ⟨s, rfl⟩ : ∃ s, a = Sum.inr (e, s) := by
        rcases List.mem_cons.mp ha with rfl | ha
        · exact ⟨.left, rfl⟩
        · rcases List.mem_cons.mp ha with rfl | ha
          · exact ⟨.right, rfl⟩
          · exact absurd ha List.not_mem_nil
      obtain ⟨s', rfl⟩ : ∃ s', b = Sum.inr (e', s') := by
        rcases List.mem_cons.mp hb with rfl | hb
        · exact ⟨.left, rfl⟩
        · rcases List.mem_cons.mp hb with rfl | hb
          · exact ⟨.right, rfl⟩
          · exact absurd hb List.not_mem_nil
      refine Or.inr ⟨(hslot e s).trans (hslot e' s').symm, ?_⟩
      rw [tiek_inr, tiek_inr, tie_eq, tie_eq]
      have hs : sideIdx s ≤ 1 := by cases s <;> simp [sideIdx]
      have hs' : 0 ≤ sideIdx s' := Nat.zero_le _
      omega

/-! ### Assembling a block, and assembling a ballot -/

/-- **A block is sorted**: its segments laid end to end at increasing slots. -/
theorem block_pairwise (V : DVoter x) (u : Fin (decodeNumbered x).n)
    (segs : List (ℕ × List (DCand x))) (hgood : ∀ q ∈ segs, GoodSeg V u q.1 q.2)
    (hlev : (segs.map Prod.fst).Pairwise (· < ·)) :
    ((segs.map Prod.snd).flatten).Pairwise (V.slotLex _) :=
  pairwise_segments V.slot segs (fun q hq c hc ↦ (hgood q hq).slot_eq c hc)
    (fun q hq ↦ (hgood q hq).sorted) hlev fun _ _ h ↦ Or.inl h

/-- **A block lives in one gadget.** -/
theorem block_gpos (V : DVoter x) (u : Fin (decodeNumbered x).n)
    (segs : List (ℕ × List (DCand x))) (hgood : ∀ q ∈ segs, GoodSeg V u q.1 q.2) :
    ∀ c ∈ (segs.map Prod.snd).flatten, V.gpos c = V.gadgetPos u := by
  intro c hc
  obtain ⟨l, hl, hcl⟩ := List.mem_flatten.mp hc
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hl
  exact (hgood q hq).gpos_eq c hcl

/-- **A ballot is sorted**: its blocks laid end to end at increasing gadget
positions. -/
theorem ballot_pairwise (V : DVoter x) (blk : Fin (decodeNumbered x).n → List (DCand x))
    (gl : List (Fin (decodeNumbered x).n))
    (hblk : ∀ u, (blk u).Pairwise (V.slotLex _))
    (hgpos : ∀ u, ∀ c ∈ blk u, V.gpos c = V.gadgetPos u)
    (hgl : (gl.map V.gadgetPos).Pairwise (· < ·)) :
    ((gl.map blk).flatten).Pairwise fun a b ↦ (V.ranking _).lt a b := by
  have hmap : gl.map blk = (gl.map fun u ↦ (V.gadgetPos u, blk u)).map Prod.snd := by
    rw [List.map_map]; rfl
  rw [hmap]
  refine pairwise_segments V.gpos _ ?_ ?_ ?_ fun a b h ↦ lt_iff_lex V |>.mpr (Or.inl h)
  · rintro q hq c hc
    obtain ⟨u, -, rfl⟩ := List.mem_map.mp hq
    exact hgpos u c hc
  · rintro q hq
    obtain ⟨u, -, rfl⟩ := List.mem_map.mp hq
    exact (hblk u).imp_of_mem fun {a b} ha hb h ↦
      lt_of_slotLex V ((hgpos u a ha).trans (hgpos u b hb).symm) h
  · rw [List.map_map]; exact hgl

/-- **A ballot is complete**, as soon as the gadget list is and every candidate
belongs to some block. -/
theorem ballot_complete (blk : Fin (decodeNumbered x).n → List (DCand x))
    (gl : List (Fin (decodeNumbered x).n)) (hgl : ∀ u, u ∈ gl)
    (hcov : ∀ c : DCand x, ∃ u, c ∈ blk u) (c : DCand x) :
    c ∈ (gl.map blk).flatten := by
  obtain ⟨u, hu⟩ := hcov c
  exact List.mem_flatten.mpr ⟨blk u, List.mem_map_of_mem (hgl u), hu⟩

/-! ## The three voters, and the gadget lists -/

/-- Voter 1 on a decoded instance. -/
abbrev dspec1 (x : GraphTy.denote) : DVoter x := spec1 _ _

/-- Voter 2 on a decoded instance. -/
abbrev dspec2 (x : GraphTy.denote) : DVoter x := spec2 _ _

/-- Voter 3 on a decoded instance. -/
abbrev dspec3 (x : GraphTy.denote) : DVoter x := spec3 _ _

/-- The order-reversing involution on `Fin n` — voter 2 runs the gadgets
through it. -/
def revFin {n : ℕ} (i : Fin n) : Fin n := ⟨n - 1 - i.val, by have := i.isLt; omega⟩

@[simp] theorem revFin_val {n : ℕ} (i : Fin n) : (revFin i).val = n - 1 - i.val := rfl

theorem revFin_revFin {n : ℕ} (i : Fin n) : revFin (revFin i) = i :=
  Fin.ext (by have := i.isLt; simp only [revFin_val]; omega)

/-- Voter 2's gadget order `[n-1, …, 0]`, matching `gadgetDesc`. -/
def gadgetDescList (n : ℕ) : List (Fin n) := (List.finRange n).map revFin

theorem mem_gadgetDescList {n : ℕ} (i : Fin n) : i ∈ gadgetDescList n :=
  List.mem_map.mpr ⟨revFin i, List.mem_finRange _, revFin_revFin i⟩

/-- Run descending through `n - 1 - ·` and the gadget positions come out
ascending. -/
theorem gadgetDescList_pairwise (n : ℕ) :
    ((gadgetDescList n).map fun v : Fin n ↦ n - 1 - v.val).Pairwise (· < ·) := by
  rw [gadgetDescList, List.map_map]
  have h : ((fun v : Fin n ↦ n - 1 - v.val) ∘ revFin) = fun i : Fin n ↦ i.val := by
    funext i
    have := i.isLt
    simp only [Function.comp_apply, revFin_val]
    omega
  rw [h, List.pairwise_map]
  exact (List.sortedLT_finRange n).pairwise

/-! ## Voter 1

Local order `AEFBCD`, gadgets ascending, both gaps at the smaller endpoint:
`ℓ_e` after `A` (slot 2) and `r_e` after `B` (slot 8). -/

/-- Voter 1's block, as levelled segments. -/
def block1Segs (x : GraphTy.denote) (u : Fin (decodeNumbered x).n) :
    List (ℕ × List (DCand x)) :=
  [(1, letterSeg x u .A),
   (2, gapSeg x (edgeAt (fun e ↦ e.i) u) .left),
   (3, letterSeg x u .E),
   (5, letterSeg x u .F),
   (7, letterSeg x u .B),
   (8, gapSeg x (edgeAt (fun e ↦ e.i) u) .right),
   (9, letterSeg x u .C),
   (11, letterSeg x u .D)]

/-- Voter 1's gadget block. -/
def absBlock1 (x : GraphTy.denote) (u : Fin (decodeNumbered x).n) : List (DCand x) :=
  ((block1Segs x u).map Prod.snd).flatten

theorem block1Segs_good (x : GraphTy.denote) (u : Fin (decodeNumbered x).n)
    (q : ℕ × List (DCand x)) (hq : q ∈ block1Segs x u) :
    GoodSeg (dspec1 x) u q.1 q.2 := by
  simp only [block1Segs, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only
  · exact goodSeg_letterSeg _ u .A 1 rfl
  · exact goodSeg_gapSeg _ u .left (edgeAt (fun e ↦ e.i) u) 2 (fun _ ↦ rfl) fun _ he ↦ edgeAt_eq he
  · exact goodSeg_letterSeg _ u .E 3 rfl
  · exact goodSeg_letterSeg _ u .F 5 rfl
  · exact goodSeg_letterSeg _ u .B 7 rfl
  · exact goodSeg_gapSeg _ u .right (edgeAt (fun e ↦ e.i) u) 8 (fun _ ↦ rfl) fun _ he ↦ edgeAt_eq he
  · exact goodSeg_letterSeg _ u .C 9 rfl
  · exact goodSeg_letterSeg _ u .D 11 rfl

theorem absBlock1_pairwise (x : GraphTy.denote) (u : Fin (decodeNumbered x).n) :
    (absBlock1 x u).Pairwise ((dspec1 x).slotLex _) :=
  block_pairwise _ u _ (block1Segs_good x u)
    (by simp only [block1Segs, List.map_cons, List.map_nil]; decide)

theorem absBlock1_gpos (x : GraphTy.denote) (u : Fin (decodeNumbered x).n) :
    ∀ c ∈ absBlock1 x u, (dspec1 x).gpos c = (dspec1 x).gadgetPos u :=
  block_gpos _ u _ (block1Segs_good x u)

theorem absBlock1_cover (c : DCand x) : ∃ u, c ∈ absBlock1 x u := by
  simp only [absBlock1]
  rcases c with ⟨u, lx, m⟩ | ⟨e, s⟩
  · exact ⟨u, List.mem_flatten.mpr ⟨letterSeg x u lx,
      by cases lx <;> simp [block1Segs], mem_letterSeg m⟩⟩
  · exact ⟨e.i, List.mem_flatten.mpr ⟨gapSeg x (edgeAt (fun e ↦ e.i) e.i) s,
      by cases s <;> simp [block1Segs], mem_gapSeg (edgeAt_self _ e)⟩⟩

/-- **Voter 1's ballot**, abstractly: the blocks of the gadgets in ascending
order. -/
def absBallot1 (x : GraphTy.denote) : List (DCand x) :=
  ((List.finRange (decodeNumbered x).n).map (absBlock1 x)).flatten

theorem absBallot1_pairwise (x : GraphTy.denote) :
    (absBallot1 x).Pairwise fun a b ↦ ((dspec1 x).ranking _).lt a b :=
  ballot_pairwise _ _ _ (absBlock1_pairwise x) (absBlock1_gpos x)
    (by rw [List.pairwise_map]; exact (List.sortedLT_finRange _).pairwise)

theorem absBallot1_complete (x : GraphTy.denote) (c : DCand x) : c ∈ absBallot1 x :=
  ballot_complete _ _ (List.mem_finRange) absBlock1_cover c

/-! ## Voter 2

Local order `BDFACE`, gadgets descending, both edge candidates in one gap at the
midpoint, after `F` (slot 6). -/

/-- Voter 2's block, as levelled segments. -/
def block2Segs (x : GraphTy.denote) (u : Fin (decodeNumbered x).n) :
    List (ℕ × List (DCand x)) :=
  [(1, letterSeg x u .B),
   (3, letterSeg x u .D),
   (5, letterSeg x u .F),
   (6, bothSeg x (edgeAt (fun e ↦ e.mid) u)),
   (7, letterSeg x u .A),
   (9, letterSeg x u .C),
   (11, letterSeg x u .E)]

/-- Voter 2's gadget block. -/
def absBlock2 (x : GraphTy.denote) (u : Fin (decodeNumbered x).n) : List (DCand x) :=
  ((block2Segs x u).map Prod.snd).flatten

theorem block2Segs_good (x : GraphTy.denote) (u : Fin (decodeNumbered x).n)
    (q : ℕ × List (DCand x)) (hq : q ∈ block2Segs x u) :
    GoodSeg (dspec2 x) u q.1 q.2 := by
  simp only [block2Segs, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only
  · exact goodSeg_letterSeg _ u .B 1 rfl
  · exact goodSeg_letterSeg _ u .D 3 rfl
  · exact goodSeg_letterSeg _ u .F 5 rfl
  · exact goodSeg_bothSeg _ u (edgeAt (fun e ↦ e.mid) u) 6 (fun _ _ ↦ rfl) fun _ _ he ↦ edgeAt_eq he
  · exact goodSeg_letterSeg _ u .A 7 rfl
  · exact goodSeg_letterSeg _ u .C 9 rfl
  · exact goodSeg_letterSeg _ u .E 11 rfl

theorem absBlock2_pairwise (x : GraphTy.denote) (u : Fin (decodeNumbered x).n) :
    (absBlock2 x u).Pairwise ((dspec2 x).slotLex _) :=
  block_pairwise _ u _ (block2Segs_good x u)
    (by simp only [block2Segs, List.map_cons, List.map_nil]; decide)

theorem absBlock2_gpos (x : GraphTy.denote) (u : Fin (decodeNumbered x).n) :
    ∀ c ∈ absBlock2 x u, (dspec2 x).gpos c = (dspec2 x).gadgetPos u :=
  block_gpos _ u _ (block2Segs_good x u)

theorem absBlock2_cover (c : DCand x) : ∃ u, c ∈ absBlock2 x u := by
  simp only [absBlock2]
  rcases c with ⟨u, lx, m⟩ | ⟨e, s⟩
  · exact ⟨u, List.mem_flatten.mpr ⟨letterSeg x u lx,
      by cases lx <;> simp [block2Segs], mem_letterSeg m⟩⟩
  · exact ⟨e.mid, List.mem_flatten.mpr ⟨bothSeg x (edgeAt (fun e ↦ e.mid) e.mid),
      by simp [block2Segs], mem_bothSeg s (edgeAt_self _ e)⟩⟩

/-- **Voter 2's ballot**, abstractly: the blocks of the gadgets in descending
order. -/
def absBallot2 (x : GraphTy.denote) : List (DCand x) :=
  ((gadgetDescList (decodeNumbered x).n).map (absBlock2 x)).flatten

theorem absBallot2_pairwise (x : GraphTy.denote) :
    (absBallot2 x).Pairwise fun a b ↦ ((dspec2 x).ranking _).lt a b :=
  ballot_pairwise _ _ _ (absBlock2_pairwise x) (absBlock2_gpos x)
    (gadgetDescList_pairwise _)

theorem absBallot2_complete (x : GraphTy.denote) (c : DCand x) : c ∈ absBallot2 x :=
  ballot_complete _ _ mem_gadgetDescList absBlock2_cover c

/-! ## Voter 3

Local order `CDEABF`, gadgets ascending, both gaps at the larger endpoint: `r_e`
after `D` (slot 4) and `ℓ_e` after `B` (slot 10). -/

/-- Voter 3's block, as levelled segments. -/
def block3Segs (x : GraphTy.denote) (u : Fin (decodeNumbered x).n) :
    List (ℕ × List (DCand x)) :=
  [(1, letterSeg x u .C),
   (3, letterSeg x u .D),
   (4, gapSeg x (edgeAt (fun e ↦ e.j) u) .right),
   (5, letterSeg x u .E),
   (7, letterSeg x u .A),
   (9, letterSeg x u .B),
   (10, gapSeg x (edgeAt (fun e ↦ e.j) u) .left),
   (11, letterSeg x u .F)]

/-- Voter 3's gadget block. -/
def absBlock3 (x : GraphTy.denote) (u : Fin (decodeNumbered x).n) : List (DCand x) :=
  ((block3Segs x u).map Prod.snd).flatten

theorem block3Segs_good (x : GraphTy.denote) (u : Fin (decodeNumbered x).n)
    (q : ℕ × List (DCand x)) (hq : q ∈ block3Segs x u) :
    GoodSeg (dspec3 x) u q.1 q.2 := by
  simp only [block3Segs, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only
  · exact goodSeg_letterSeg _ u .C 1 rfl
  · exact goodSeg_letterSeg _ u .D 3 rfl
  · exact goodSeg_gapSeg _ u .right (edgeAt (fun e ↦ e.j) u) 4 (fun _ ↦ rfl) fun _ he ↦ edgeAt_eq he
  · exact goodSeg_letterSeg _ u .E 5 rfl
  · exact goodSeg_letterSeg _ u .A 7 rfl
  · exact goodSeg_letterSeg _ u .B 9 rfl
  · exact goodSeg_gapSeg _ u .left (edgeAt (fun e ↦ e.j) u) 10 (fun _ ↦ rfl) fun _ he ↦ edgeAt_eq he
  · exact goodSeg_letterSeg _ u .F 11 rfl

theorem absBlock3_pairwise (x : GraphTy.denote) (u : Fin (decodeNumbered x).n) :
    (absBlock3 x u).Pairwise ((dspec3 x).slotLex _) :=
  block_pairwise _ u _ (block3Segs_good x u)
    (by simp only [block3Segs, List.map_cons, List.map_nil]; decide)

theorem absBlock3_gpos (x : GraphTy.denote) (u : Fin (decodeNumbered x).n) :
    ∀ c ∈ absBlock3 x u, (dspec3 x).gpos c = (dspec3 x).gadgetPos u :=
  block_gpos _ u _ (block3Segs_good x u)

theorem absBlock3_cover (c : DCand x) : ∃ u, c ∈ absBlock3 x u := by
  simp only [absBlock3]
  rcases c with ⟨u, lx, m⟩ | ⟨e, s⟩
  · exact ⟨u, List.mem_flatten.mpr ⟨letterSeg x u lx,
      by cases lx <;> simp [block3Segs], mem_letterSeg m⟩⟩
  · exact ⟨e.j, List.mem_flatten.mpr ⟨gapSeg x (edgeAt (fun e ↦ e.j) e.j) s,
      by cases s <;> simp [block3Segs], mem_gapSeg (edgeAt_self _ e)⟩⟩

/-- **Voter 3's ballot**, abstractly: the blocks of the gadgets in ascending
order. -/
def absBallot3 (x : GraphTy.denote) : List (DCand x) :=
  ((List.finRange (decodeNumbered x).n).map (absBlock3 x)).flatten

theorem absBallot3_pairwise (x : GraphTy.denote) :
    (absBallot3 x).Pairwise fun a b ↦ ((dspec3 x).ranking _).lt a b :=
  ballot_pairwise _ _ _ (absBlock3_pairwise x) (absBlock3_gpos x)
    (by rw [List.pairwise_map]; exact (List.sortedLT_finRange _).pairwise)

theorem absBallot3_complete (x : GraphTy.denote) (c : DCand x) : c ∈ absBallot3 x :=
  ballot_complete _ _ (List.mem_finRange) absBlock3_cover c

end Cert
end Hardness
