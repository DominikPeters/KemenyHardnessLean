import HardnessReductions.Cert.Bridge
import Kemeny.KemenyScore
import Mathlib.Data.Prod.Lex

/-!
# Concrete encoding of KEMENY SCORE instances

A concrete KEMENY SCORE instance is `(candidates, (ballots, b))`: an explicit
candidate list, a list of ballots, and a budget. The candidates are the
*positions* of the candidate list (`Fin candidates.length`), so the list length
is the number of alternatives — the size-model discipline, exactly as for
graphs (`Graph/Encoding.lean`): a bare numeral `N` is exponentially concise, so
`N` alternatives must cost `N` input symbols. The candidate-list entries are
mere labels, discarded by decoding.

## Decoding a ballot

A ballot is a `List ℕ` of candidate indices, decoded to a bundled ranking on
`Fin N` by the lex key

  `c ↦ (first position of c in the ballot, c)  :  ℕ ×ₗ ℕ`,

so a candidate ranks higher the earlier it is first mentioned, ties (a
candidate not mentioned at all gets key position `length`) broken by index.
Missing candidates thus sink below all mentioned ones, index-ordered; and the
second coordinate makes the key injective, so it bundles into a `LinearOrder`
via `LinearOrder.lift'`. Decoding is **total** — every `List ℕ` is some ranking
— and *faithful* on genuine permutation ballots: when a ballot is a `Nodup`
enumeration of `range N`, the decoded strict order is exactly list precedence
(`decodeBallot_lt_of_perm`). That faithfulness lemma is the only bridge the
certificate's adequacy proof needs.
-/

namespace Hardness
namespace Cert

open scoped List

/-- Concrete KEMENY SCORE instances: `(candidates, (ballots, budget))`. -/
abbrev KemenyTy : Ty := .pair (.list .nat) (.pair (.list (.list .nat)) .nat)

/-! ## Decoding a ballot -/

/-- First-occurrence index is injective across members: at a shared
first-occurrence position sit equal elements (no `Nodup` needed — the
`getElem`-at-`idxOf` returns the element itself). -/
theorem idxOf_inj_aux {l : List ℕ} {a b : ℕ}
    (ha : a ∈ l) (hb : b ∈ l) (h : l.idxOf a = l.idxOf b) : a = b := by
  have e1 : l[l.idxOf a]'(List.idxOf_lt_length_of_mem ha) = a := List.getElem_idxOf _
  have e2 : l[l.idxOf b]'(List.idxOf_lt_length_of_mem hb) = b := List.getElem_idxOf _
  rw [← e1, ← e2]
  simp [h]

/-- The lex key of candidate `c` under a ballot: its first position in the
ballot (or the ballot's length if unmentioned), broken by the index `c`. -/
def ballotKey (ballot : List ℕ) (c : ℕ) : ℕ ×ₗ ℕ := toLex (ballot.idxOf c, c)

/-- The key restricted to `Fin N` is injective: the second lex coordinate is
the index itself. -/
theorem ballotKey_fin_injective (N : ℕ) (ballot : List ℕ) :
    Function.Injective (fun c : Fin N ↦ ballotKey ballot c.val) := by
  intro a b h
  have : (a.val : ℕ) = b.val := congrArg (fun p => (ofLex p).2) h
  exact Fin.ext this

/-- Decode a ballot to a bundled ranking on the `N` candidate positions: rank
candidates by first mention, ties by index. -/
@[reducible] def decodeBallot (N : ℕ) (ballot : List ℕ) : LinearOrder (Fin N) :=
  LinearOrder.lift' (fun c : Fin N ↦ ballotKey ballot c.val)
    (ballotKey_fin_injective N ballot)

/-- The strict order of a decoded ballot compares the lex keys. -/
theorem decodeBallot_lt (N : ℕ) (ballot : List ℕ) (a b : Fin N) :
    (decodeBallot N ballot).lt a b ↔ ballotKey ballot a.val < ballotKey ballot b.val :=
  Iff.rfl

/-- **Faithfulness of ballot decoding**: when a ballot is a `Nodup` enumeration
of `range N` (a genuine permutation of the `N` candidates), the decoded strict
order is exactly list precedence — `a` beats `b` iff `a` is mentioned before
`b`. The certificate produces exactly such ballots; this is the only bridge its
adequacy proof needs. -/
theorem decodeBallot_lt_of_perm {N : ℕ} {ballot : List ℕ}
    (hperm : ballot ~ List.range N) (a b : Fin N) :
    (decodeBallot N ballot).lt a b ↔ ballot.idxOf a.val < ballot.idxOf b.val := by
  rw [decodeBallot_lt, ballotKey, ballotKey, Prod.Lex.lt_iff, ofLex_toLex, ofLex_toLex]
  have hma : a.val ∈ ballot := hperm.mem_iff.mpr (List.mem_range.mpr a.isLt)
  have hmb : b.val ∈ ballot := hperm.mem_iff.mpr (List.mem_range.mpr b.isLt)
  constructor
  · rintro (h | ⟨heq, hlt⟩)
    · exact h
    · exact absurd (idxOf_inj_aux hma hmb heq) (Nat.ne_of_lt hlt)
  · exact fun h => Or.inl h

/-- The ballot `[2, 0, 1]` ranks candidate `2` above candidate `0` (mentioned
earlier). -/
example : (decodeBallot 3 [2, 0, 1]).lt ⟨2, by omega⟩ ⟨0, by omega⟩ := by decide

/-- …and candidate `0` above candidate `1`. -/
example : (decodeBallot 3 [2, 0, 1]).lt ⟨0, by omega⟩ ⟨1, by omega⟩ := by decide

/-! ## Decoding an instance -/

/-- Decode a concrete KEMENY SCORE instance `(candidates, (ballots, b))`. The
alternatives are the positions of the candidate list, each ballot is decoded to
a ranking, and the budget passes through. Decoding is total. -/
def decodeKemeny (x : KemenyTy.denote) : KemenyInstance where
  A := Fin x.1.length
  voters := x.2.1.map (decodeBallot x.1.length)
  b := x.2.2

namespace Concrete

/-- KEMENY SCORE on concrete instances. -/
def KEMENY_SCORE : Problem KemenyTy.denote :=
  Hardness.KEMENY_SCORE.comap decodeKemeny

/-- KEMENY SCORE with three voters, on concrete instances. Decoding preserves
the voter count (`List.map` preserves length), so the three-voter restriction
comaps transparently. -/
def KEMENY_SCORE_3VOTERS : Problem KemenyTy.denote :=
  Hardness.KEMENY_SCORE_3VOTERS.comap decodeKemeny

/-- Unfolding of `Concrete.KEMENY_SCORE_3VOTERS`: exactly three ballots, and a
concrete YES-instance. -/
theorem kemenyScore3Voters_iff (x : KemenyTy.denote) :
    KEMENY_SCORE_3VOTERS x ↔ x.2.1.length = 3 ∧ KEMENY_SCORE x := by
  refine Iff.and ?_ Iff.rfl
  rw [decodeKemeny]
  simp

end Concrete

end Cert
end Hardness
