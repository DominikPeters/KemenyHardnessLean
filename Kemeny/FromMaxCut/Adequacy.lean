import Kemeny.FromMaxCut
import Kemeny.FromMaxCut.Program
import Kemeny.FromMaxCut.BallotMatch
import Kemeny.FromMaxCut.BudgetMatch
import Kemeny.Source.Certified
import HardnessReductions.Logic.Sat3.FromSat.Adequacy
import HardnessReductions.Logic.MaxSat.FromSat3.Adequacy
import HardnessReductions.Graph.MaxCut.FromMaxSat2.Adequacy

/-!
# Adequacy: the profile program is the reduction

The last step of phase 2. `kemenyCode` is shown to decide the same question as
the abstract instance map `kemenyLeeMap`, giving

  `simpleMaxCutLeeToKemeny3Certified :
     CertifiedReduction Concrete.SIMPLE_MAX_CUT_LEE Concrete.KEMENY_SCORE_3VOTERS`,

and the catalog chain composes it into `satToKemeny3Certified`.

## The two branches

The program's guard (`guardCode`) is exactly the abstract guard: `leeHolds`
decides `LongEvenEdges` (`leeHolds_eval_LongEven`) and `kLeCard` decides
`k ≤ |E|`, which `card_edgePair` identifies with the abstract `k ≤ card
(EdgePair …)`.

*On the guarded branch* the decoded output is the abstract instance **relabeled**
along `candEquiv`: `decodeProfile_eq` (8f-3) matches the voters, `budgetCode_eq`
(8f-4) matches the budget, and the alternatives are the positions of the emitted
candidate list rather than the gadget candidates. `kemenyScore_relabel` (8a) is
what makes that difference invisible to the question.

*Off it* both sides are the fixed NO instance — the abstract `kemenyNoInstance`
on `Bool` and the decoded `([0,1], ([[0,1],[0,1],[1,0]], 0))` on `Fin 2`. They
are not the same object and are not compared: each is separately shown to be a
NO instance, by the same argument (`not_kemenyScore_of_contested`) — a budget-zero
instance on which some pair is contested in both directions cannot be satisfied.
-/

namespace Hardness

/-! ## A contested pair kills a zero budget -/

/-- **A budget-zero instance with a contested pair is a NO instance**: whichever
way the output ranks the pair, some voter disagrees, so the cost is at least
`1`. Both fixed NO instances of the reduction — the abstract one on `Bool` and
the decoded one on `Fin 2` — are NO for this reason. -/
theorem not_kemenyScore_of_contested {y : KemenyInstance} (hb : y.b = 0) {a c : y.A}
    (hne : a ≠ c) (h1 : 1 ≤ againstCount y.voters a c)
    (h2 : 1 ≤ againstCount y.voters c a) : ¬KEMENY_SCORE y := by
  rintro ⟨r, hr⟩
  rw [hb, Nat.le_zero, kemenyCost_eq_sum_against] at hr
  have key : ∀ u v : y.A, r.lt u v →
      againstCount y.voters u v ≤ ∑ q ∈ rankedPairs r, againstCount y.voters q.1 q.2 := by
    intro u v huv
    exact Finset.single_le_sum (f := fun q : y.A × y.A ↦ againstCount y.voters q.1 q.2)
      (fun q _ ↦ Nat.zero_le _) ((mem_rankedPairs (p := (u, v))).mpr huv)
  by_cases hlt : r.lt a c
  · have := key a c hlt
    omega
  · have := key c a (ranks_of_not_ranks hne hlt)
    omega

/-- Every image of `kemenyLeeMap` has three voters. -/
theorem kemenyLeeMap_voters_length (y : NumberedGraphInstance) :
    (kemenyLeeMap y).voters.length = 3 := by
  by_cases h : LongEvenEdges y
  · rw [kemenyLeeMap, if_pos h]
    exact kemenyMap_voters_length y
  · rw [kemenyLeeMap, if_neg h]
    rfl

namespace Cert

/-! ## The guarded branch -/

/-- The abstract instance the guarded branch produces: the gadget candidates,
the three voters, the paper's budget. -/
def absInstance (x : GraphTy.denote) : KemenyInstance where
  A := DCand x
  voters := kemenyProfile (decodeNumbered x).n (decodeNumbered x).G (bigM (decodeNumbered x).n)
  b := kemenyBudget (decodeNumbered x)

/-- **The decoded output is the abstract instance, relabeled**: same voters and
same budget, with the gadget candidates renamed to the positions of the emitted
candidate list. -/
theorem decodeKemeny_real (x : GraphTy.denote)
    (hsp : SpreadEdges (decodeNumbered x).n (decodeNumbered x).G) :
    decodeKemeny (candList.eval x, (profileBallots.eval x, budgetCode.eval x))
      = (absInstance x).relabel (candEquiv x) := by
  simp only [decodeKemeny, KemenyInstance.relabel, absInstance]
  rw [decodeProfile_eq, budgetCode_eq x hsp]

/-- **The guarded branch asks the abstract question** — relabeling equivariance
absorbs the renaming of the alternatives. -/
theorem kemenyScore_decodeReal (x : GraphTy.denote)
    (hsp : SpreadEdges (decodeNumbered x).n (decodeNumbered x).G) :
    KEMENY_SCORE (decodeKemeny (candList.eval x, (profileBallots.eval x, budgetCode.eval x)))
      ↔ KEMENY_SCORE (absInstance x) := by
  rw [decodeKemeny_real x hsp]
  exact (kemenyScore_relabel (absInstance x) (candEquiv x)).symm

/-- On the guarded branch the abstract map produces `absInstance`. -/
theorem kemenyMap_eq_absInstance (x : GraphTy.denote)
    (hk : x.2.2 ≤ (canonEdges.eval x).length) :
    kemenyMap (decodeNumbered x) = absInstance x := by
  rw [kemenyMap, if_pos (show (decodeNumbered x).k ≤ Fintype.card (DEdge x) by
    rw [card_edgePair]; exact hk)]
  rfl

/-! ## The unguarded branch -/

/-- **The decoded fixed NO instance is a NO instance**: on two alternatives, two
of the three ballots rank `0` first and one ranks `1` first, so both orders of
the only pair cost at least `1` against a budget of `0`. -/
theorem not_kemenyScore_decodeNo :
    ¬KEMENY_SCORE (decodeKemeny ([0, 1], ([[0, 1], [0, 1], [1, 0]], 0))) := by
  refine not_kemenyScore_of_contested rfl (a := (0 : Fin 2)) (c := (1 : Fin 2)) ?_ ?_ ?_
  · change (0 : Fin 2) ≠ (1 : Fin 2)
    decide
  · decide
  · decide

/-! ## Adequacy -/

/-- Every produced instance has three voters, on both branches. -/
theorem decodeKemeny_voters_length (x : GraphTy.denote) :
    (decodeKemeny (kemenyCode.eval x)).voters.length = 3 := by
  rw [kemenyCode_eval]
  by_cases hg : guardCode.eval x = true
  · rw [if_pos hg]
    rfl
  · rw [if_neg hg]
    rfl

/-- **The program asks the same question as the abstract instance map.** -/
theorem kemenyScore_decodeKemeny (x : GraphTy.denote) :
    KEMENY_SCORE (kemenyLeeMap (decodeNumbered x))
      ↔ KEMENY_SCORE (decodeKemeny (kemenyCode.eval x)) := by
  rw [kemenyCode_eval]
  by_cases hg : guardCode.eval x = true
  · obtain ⟨hlee, hk⟩ := (guardCode_eval_true x).mp hg
    rw [if_pos hg, kemenyLeeMap, if_pos hlee, kemenyMap_eq_absInstance x hk,
      kemenyScore_decodeReal x (spreadEdges_of_longEvenEdges hlee)]
  · rw [if_neg hg]
    refine iff_of_false ?_ not_kemenyScore_decodeNo
    by_cases hlee : LongEvenEdges (decodeNumbered x)
    · have hk : ¬(decodeNumbered x).k ≤ Fintype.card (DEdge x) := fun hc ↦
        hg ((guardCode_eval_true x).mpr ⟨hlee, by rw [← card_edgePair]; exact hc⟩)
      rw [kemenyLeeMap, if_pos hlee, kemenyMap, if_neg hk]
      exact not_kemenyScore_noInstance
    · rw [kemenyLeeMap, if_neg hlee]
      exact not_kemenyScore_noInstance

/-- **Adequacy of the profile program.** -/
theorem kemenyCode_correct (x : GraphTy.denote) :
    Concrete.SIMPLE_MAX_CUT_LEE x ↔ Concrete.KEMENY_SCORE_3VOTERS (kemenyCode.eval x) := by
  rw [Concrete.SIMPLE_MAX_CUT_LEE, Problem.comap, simpleMaxCutLee_iff_kemeny (decodeNumbered x)]
  simp only [Concrete.KEMENY_SCORE_3VOTERS, Problem.comap, KEMENY_SCORE_3VOTERS, Problem.restrict]
  exact Iff.and
    (iff_of_true (kemenyLeeMap_voters_length _) (decodeKemeny_voters_length x))
    (kemenyScore_decodeKemeny x)

/-- **SIMPLE MAX CUT with long even edges → KEMENY SCORE with three voters,
certified.** -/
def simpleMaxCutLeeToKemeny3Certified :
    CertifiedReduction Concrete.SIMPLE_MAX_CUT_LEE Concrete.KEMENY_SCORE_3VOTERS where
  code := kemenyCode
  correct := kemenyCode_correct

/-- **KEMENY SCORE with three voters is NP-hard, certified end to end**: the
chain from SAT through 3SAT, MAX 2-SAT, SIMPLE MAX CUT and its long-even-edges
restriction, every hop carried by a program of the builder language. -/
def satToKemeny3Certified :
    CertifiedReduction Concrete.SAT Concrete.KEMENY_SCORE_3VOTERS :=
  split3Certified.comp (sat3ToMaxSat2Certified.comp
    (maxSat2ToSimpleMaxCutCertified.comp
      (smcToLeeCertified.comp simpleMaxCutLeeToKemeny3Certified)))

end Cert
end Hardness
