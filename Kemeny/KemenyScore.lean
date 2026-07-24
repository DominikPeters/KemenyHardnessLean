import Kemeny.Rankings

/-!
# KEMENY SCORE, and its three-voter restriction

The target problem of the Kemeny project: given a profile of rankings and a
budget, is there an output ranking whose total Kendall tau distance to the
profile is within budget?

The problem is stated for an arbitrary number of voters — the profile is an
explicit `List (LinearOrder A)` — and the catalog-style entry of this project
is the `Problem.restrict` to exactly three voters, the case left open by
Dwork–Kumar–Naor–Sivakumar (2001) and resolved by the MAX CUT reduction
formalized here (`Kemeny/FromMaxCut/`). Keeping the general problem around
costs nothing and leaves room for the even case (`n = 4`, from FEEDBACK ARC
SET) as a later restriction of the same statement.

Membership of the *instance* count in the statement, rather than a promise:
an instance whose voter list does not have length three is simply a
no-instance of the restricted problem, per the library's promise-free
restriction idiom.
-/

namespace Hardness

/-- An instance of KEMENY SCORE: a finite set of alternatives, a profile of
rankings given as an explicit list — one bundled `LinearOrder` per voter —
and a cost budget. -/
structure KemenyInstance : Type 1 where
  /-- The alternatives. -/
  A : Type
  [fintypeA : Fintype A]
  [decEqA : DecidableEq A]
  /-- The profile: one ranking per voter, as an explicit list. -/
  voters : List (LinearOrder A)
  /-- The cost budget. -/
  b : ℕ

attribute [instance] KemenyInstance.fintypeA KemenyInstance.decEqA

/-- **KEMENY SCORE**: is there a ranking whose total Kendall tau distance to
the profile is at most the budget? -/
def KEMENY_SCORE : Problem KemenyInstance :=
  fun x ↦ ∃ r : LinearOrder x.A, kemenyCost x.voters r ≤ x.b

/-- **KEMENY SCORE with three voters**: the restriction of KEMENY SCORE to
profiles of exactly three rankings — the `n = 3` case of
Dwork–Kumar–Naor–Sivakumar's question, and the target of this project's
MAX CUT reduction. -/
def KEMENY_SCORE_3VOTERS : Problem KemenyInstance :=
  KEMENY_SCORE.restrict fun x ↦ x.voters.length = 3

end Hardness
