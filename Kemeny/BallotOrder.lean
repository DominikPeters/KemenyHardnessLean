import Kemeny.Encoding
import Kemeny.Relabel
import HardnessReductions.Cert.Numbering

/-!
# From a sorted candidate list to a decoded ballot

The certificate emits each voter as an explicit list of candidate *numbers*, and
the adequacy proof must recognize the decoded ranking as the abstract voter,
transported along the candidate numbering. This file supplies the bridge, once
and for all:

  **`decodeBallot_eq_mapOrder`** — if `L` lists *every* candidate, strictly
  sorted by the voter's ranking, then `decodeBallot` applied to `L.map num` is
  exactly the pushforward `mapOrder equivFin` of that ranking.

So a per-voter obligation reduces to two combinatorial facts about a list of
abstract candidates — it is sorted, and it is complete — and one identity
matching the program's output with `L.map num`. No position is ever computed:
positions enter only through `List.idxOf`, and `idxOf_lt_iff_of_sorted` turns
the comparison of positions in a sorted list back into the order itself.

The remaining lemmas are the list tools the ballot half of the adequacy proof
runs on: `pairwise_segments` (a list of levelled segments, laid end to end in
increasing level, is sorted as soon as each segment is), which proves the
sortedness fact at both nesting levels, and the `idxOf`/`filter`/`map`
commutations.
-/

namespace Hardness
namespace Cert

/-! ## Lists, positions and injections -/

section Lists

variable {α β : Type*}

/-- `filter` after `map` is `map` after the pulled-back `filter`. -/
theorem map_filter_comm (f : α → β) (p : β → Bool) (l : List α) :
    (l.map f).filter p = (l.filter fun a ↦ p (f a)).map f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.filter_cons, List.filter_cons]
    by_cases h : p (f a) = true
    · rw [if_pos h, if_pos h, List.map_cons, ih]
    · rw [if_neg h, if_neg h, ih]

variable [DecidableEq α]

/-- Mapping by an injection does not move positions. -/
theorem idxOf_map_of_injective {f : α → ℕ} (hf : Function.Injective f) (l : List α) (a : α) :
    (l.map f).idxOf (f a) = l.idxOf a := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    rw [List.map_cons]
    by_cases h : b = a
    · subst h
      rw [List.idxOf_cons_self, List.idxOf_cons_self]
    · rw [List.idxOf_cons_ne _ h, List.idxOf_cons_ne _ fun hc ↦ h (hf hc), ih]

/-- **Positions in a sorted list compare like the order**: in a list strictly
increasing for a ranking, one member precedes another exactly when the ranking
puts it first. This is what makes the ballot obligations positional-arithmetic
free. -/
theorem idxOf_lt_iff_of_sorted (r : LinearOrder α) {L : List α}
    (hs : L.Pairwise fun a b ↦ r.lt a b) {a b : α} (ha : a ∈ L) (hb : b ∈ L) :
    L.idxOf a < L.idxOf b ↔ r.lt a b := by
  have key : ∀ c d : α, c ∈ L → d ∈ L → L.idxOf c < L.idxOf d → r.lt c d := by
    intro c d hc hd h
    have hcl := List.idxOf_lt_length_of_mem hc
    have hdl := List.idxOf_lt_length_of_mem hd
    have hR := List.pairwise_iff_getElem.mp hs _ _ hcl hdl h
    rwa [List.getElem_idxOf, List.getElem_idxOf] at hR
  refine ⟨key a b ha hb, fun h ↦ ?_⟩
  rcases Nat.lt_trichotomy (L.idxOf a) (L.idxOf b) with hlt | heq | hgt
  · exact hlt
  · exact absurd (idxOf_inj_mem ha hb heq) (ranks_ne h)
  · exact absurd (key b a hb ha hgt) (ranks_asymm h)

omit [DecidableEq α] in
/-- **Levelled segments**: lists laid end to end, each carrying a level that its
members share, the levels strictly increasing, are sorted as soon as each segment
is — provided a lower level always ranks first. Used at both nesting levels of a
ballot: gadgets inside the ballot, and slots inside a gadget block. -/
theorem pairwise_segments {R : α → α → Prop} (lev : α → ℕ) (segs : List (ℕ × List α))
    (hin : ∀ p ∈ segs, ∀ a ∈ p.2, lev a = p.1)
    (hseg : ∀ p ∈ segs, p.2.Pairwise R)
    (hsorted : (segs.map Prod.fst).Pairwise (· < ·))
    (hcross : ∀ a b, lev a < lev b → R a b) :
    ((segs.map Prod.snd).flatten).Pairwise R := by
  rw [List.pairwise_flatten]
  refine ⟨fun l hl ↦ ?_, ?_⟩
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hl
    exact hseg p hp
  · rw [List.pairwise_map]
    rw [List.pairwise_map] at hsorted
    refine hsorted.imp_of_mem fun {p q} hp hq hlt a ha b hb ↦ ?_
    exact hcross a b (by rw [hin p hp a ha, hin q hq b hb]; exact hlt)

end Lists

/-! ## Two bundled rankings agreeing -/

/-- Comparability in bundled form: `a ≤ b` is the failure of `b < a`. -/
theorem le_iff_not_ranks {A : Type*} (r : LinearOrder A) (a b : A) : r.le a b ↔ ¬r.lt b a := by
  letI := r
  exact not_lt.symm

/-- Two rankings with the same strict order are equal. -/
theorem linearOrder_ext_lt {A : Type*} {r s : LinearOrder A}
    (h : ∀ a b, r.lt a b ↔ s.lt a b) : r = s :=
  LinearOrder.ext fun a b ↦ by
    rw [le_iff_not_ranks r, le_iff_not_ranks s]
    exact not_congr (h b a)

/-! ## The bridge -/

/-- **A sorted, complete candidate list decodes to the ranking that sorted it.**
The certificate emits `L.map Nu.num` as a ballot; if `L` lists every candidate in
the voter's order, the decoded ranking on the `Nu.size` candidate positions is
exactly the voter, pushed along the numbering bijection.

Both hypotheses are combinatorial and local: `hsort` compares neighbours through
the ranking, `hcomp` says nothing is missing. Everything positional —
permutation-ness of the ballot, first-occurrence indices, the lex tie-break of
`decodeBallot` — is discharged here. -/
theorem decodeBallot_eq_mapOrder {α : Type} (Nu : Numbering α)
    (r : LinearOrder α) (L : List α) (hsort : L.Pairwise fun a b ↦ r.lt a b)
    (hcomp : ∀ a, a ∈ L) :
    decodeBallot Nu.size (L.map Nu.num) = mapOrder Nu.equivFin r := by
  classical
  have hnodupL : L.Nodup := hsort.imp fun h ↦ ranks_ne h
  have hnodup : (L.map Nu.num).Nodup := hnodupL.map Nu.num_inj
  have hperm : List.Perm (L.map Nu.num) (List.range Nu.size) := by
    rw [List.perm_ext_iff_of_nodup hnodup List.nodup_range]
    intro m
    rw [List.mem_map, List.mem_range]
    refine ⟨?_, fun hm ↦ ?_⟩
    · rintro ⟨a, -, rfl⟩
      exact Nu.num_lt a
    · obtain ⟨a, ha⟩ := Nu.num_surj m hm
      exact ⟨a, hcomp a, ha⟩
  refine linearOrder_ext_lt fun a b ↦ ?_
  have hval : ∀ c : Fin Nu.size, Nu.num (Nu.equivFin.symm c) = c.val := fun c ↦ by
    rw [← Numbering.equivFin_val, Equiv.apply_symm_apply]
  rw [decodeBallot_lt_of_perm hperm, ← hval a, ← hval b,
    idxOf_map_of_injective Nu.num_inj, idxOf_map_of_injective Nu.num_inj,
    idxOf_lt_iff_of_sorted r hsort (hcomp _) (hcomp _)]
  exact (mapOrder_lt Nu.equivFin r a b).symm

/-- **The bridge at a transported size.** The decoded instance counts its
candidates as the *length of the emitted candidate list*, which the numbering's
`size` only equals — it is not that term. Since the count is a type index, the
equation has to be carried by the bijection, which is what this restatement
does. -/
theorem decodeBallot_eq_mapOrder' {α : Type} (Nu : Numbering α)
    (r : LinearOrder α) (L : List α) (hsort : L.Pairwise fun a b ↦ r.lt a b)
    (hcomp : ∀ a, a ∈ L) {N : ℕ} (hN : Nu.size = N) :
    decodeBallot N (L.map Nu.num) = mapOrder (Nu.equivFin.trans (finCongr hN)) r := by
  subst hN
  rw [decodeBallot_eq_mapOrder Nu r L hsort hcomp]
  rfl

end Cert
end Hardness
