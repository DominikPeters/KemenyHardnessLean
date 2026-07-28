import HardnessReductions.Logic.Sat3.FromSat
import HardnessReductions.Logic.MaxSat.FromSat3
import HardnessReductions.Graph.MaxCut.FromMaxSat2
import KemenyHardness.FromMaxCut.Assembly

/-!
# The reduction: KEMENY SCORE with three voters is NP-hard

The headline of the project. The instance map guards the long-even-edges
restriction on top of `kemenyMap`'s threshold guard — a failed restriction is
a NO instance of `SIMPLE_MAX_CUT_LEE` by definition, and is sent to the fixed
NO instance. On the guarded branch, correctness is the affine bridge
(`kemenyMap_iff_marginCost`) between the forward direction
(`exists_marginCost_le_marginBudget`) and the reverse direction
(`exists_cut_of_marginCost_le`); off it, `kemenyNoInstance` really is a NO
instance (`not_kemenyScore_noInstance`): its profile splits two voters
against one on the only pair, so every ranking costs at least `1 > 0`.

The chain from the catalog composes to
`satToKemeny3 : SAT ⟶ᵣ KEMENY_SCORE_3VOTERS`, through 3SAT, MAX 2-SAT,
SIMPLE MAX CUT, and its long-even-edges restriction — resolving the `n = 3`
case of Dwork–Kumar–Naor–Sivakumar (2001).
-/

namespace Hardness

/-! ## The fixed NO instance is a NO instance -/

/-- `kemenyNoInstance` is a NO instance of KEMENY SCORE: two voters rank the
pair one way and one the other, so every ranking disagrees with at least one
voter — cost at least `1`, budget `0`. -/
theorem not_kemenyScore_noInstance : ¬KEMENY_SCORE kemenyNoInstance := by
  rintro ⟨r, hr⟩
  have h1 : 1 ≤ againstCount kemenyNoInstance.voters false true := by decide
  have h2 : 1 ≤ againstCount kemenyNoInstance.voters true false := by decide
  rw [show kemenyNoInstance.b = 0 from rfl, Nat.le_zero,
    kemenyCost_eq_sum_against] at hr
  by_cases hlt : r.lt false true
  · have hmem : ((false, true) : Bool × Bool) ∈ rankedPairs r :=
      mem_rankedPairs.mpr hlt
    have hle : againstCount kemenyNoInstance.voters false true
        ≤ ∑ p ∈ rankedPairs r, againstCount kemenyNoInstance.voters p.1 p.2 :=
      Finset.single_le_sum
        (f := fun p : Bool × Bool ↦ againstCount kemenyNoInstance.voters p.1 p.2)
        (fun p _ ↦ Nat.zero_le _) hmem
    omega
  · have hlt' : r.lt true false := ranks_of_not_ranks Bool.false_ne_true hlt
    have hmem : ((true, false) : Bool × Bool) ∈ rankedPairs r :=
      mem_rankedPairs.mpr hlt'
    have hle : againstCount kemenyNoInstance.voters true false
        ≤ ∑ p ∈ rankedPairs r, againstCount kemenyNoInstance.voters p.1 p.2 :=
      Finset.single_le_sum
        (f := fun p : Bool × Bool ↦ againstCount kemenyNoInstance.voters p.1 p.2)
        (fun p _ ↦ Nat.zero_le _) hmem
    omega

/-! ## The reduction -/

instance (x : NumberedGraphInstance) : Decidable (LongEvenEdges x) :=
  inferInstanceAs (Decidable (∀ i j : Fin x.n, x.G.Adj i j → i.val < j.val →
    i.val + 6 ≤ j.val ∧ 2 ∣ (i.val + j.val)))

/-- The full instance map: `kemenyMap` behind the long-even-edges guard.
Instances failing the restriction are NO instances of `SIMPLE_MAX_CUT_LEE`
by definition, and are sent to the fixed NO instance. -/
def kemenyLeeMap (x : NumberedGraphInstance) : KemenyInstance :=
  if LongEvenEdges x then kemenyMap x else kemenyNoInstance

/-- **Correctness of the reduction**: a numbered graph instance is a YES
instance of SIMPLE MAX CUT with long even edges exactly if its image is a
YES instance of three-voter KEMENY SCORE. -/
theorem simpleMaxCutLee_iff_kemeny (x : NumberedGraphInstance) :
    SIMPLE_MAX_CUT_LEE x ↔ KEMENY_SCORE_3VOTERS (kemenyLeeMap x) := by
  by_cases hlee : LongEvenEdges x
  · rw [kemenyLeeMap, if_pos hlee]
    by_cases hk : x.k ≤ Fintype.card (EdgePair x.n x.G)
    · constructor
      · rintro ⟨-, χ, hcut⟩
        refine ⟨kemenyMap_voters_length x, ?_⟩
        rw [kemenyMap_iff_marginCost x hk]
        exact exists_marginCost_le_marginBudget x
          (spreadEdges_of_longEvenEdges hlee) hcut
      · rintro ⟨-, hkem⟩
        rw [kemenyMap_iff_marginCost x hk] at hkem
        obtain ⟨r, hr⟩ := hkem
        exact ⟨hlee, exists_cut_of_marginCost_le x hlee hr hk⟩
    · refine iff_of_false ?_ ?_
      · rintro ⟨-, χ, hcut⟩
        exact hk (le_trans hcut (cutSize_le_card_edgePair χ))
      · rw [kemenyMap, if_neg hk]
        rintro ⟨-, hkem⟩
        exact not_kemenyScore_noInstance hkem
  · rw [kemenyLeeMap, if_neg hlee]
    exact iff_of_false (fun h ↦ hlee h.1) fun h ↦ not_kemenyScore_noInstance h.2

/-- **SIMPLE MAX CUT with long even edges reduces to KEMENY SCORE with three
voters** — the reduction of the paper, formalized. -/
def simpleMaxCutLeeToKemeny3 : SIMPLE_MAX_CUT_LEE ⟶ᵣ KEMENY_SCORE_3VOTERS :=
  ⟨kemenyLeeMap, simpleMaxCutLee_iff_kemeny⟩

/-- **KEMENY SCORE with three voters is NP-hard**: the chain from SAT,
through 3SAT, MAX 2-SAT, SIMPLE MAX CUT, and long even edges — the `n = 3`
case of Dwork–Kumar–Naor–Sivakumar (2001). -/
noncomputable def satToKemeny3 : SAT ⟶ᵣ KEMENY_SCORE_3VOTERS :=
  satTo3Sat.comp (sat3ToMaxSat2.comp (maxSat2ToSimpleMaxCut.comp
    (simpleMaxCutToLee.comp simpleMaxCutLeeToKemeny3)))

end Hardness
