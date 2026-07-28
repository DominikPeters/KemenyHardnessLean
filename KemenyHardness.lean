import KemenyHardness.Rankings
import KemenyHardness.Margins
import KemenyHardness.KemenyScore
import KemenyHardness.Relabel
import KemenyHardness.Encoding
import KemenyHardness.BallotOrder
import KemenyHardness.CloneContraction
import KemenyHardness.Source
import KemenyHardness.Source.Certified
import KemenyHardness.FromMaxCut.Construction
import KemenyHardness.FromMaxCut.CanonEdges
import KemenyHardness.FromMaxCut.Code
import KemenyHardness.FromMaxCut.Ballots
import KemenyHardness.FromMaxCut.CandNumbering
import KemenyHardness.FromMaxCut.AbsBallots
import KemenyHardness.FromMaxCut.BallotMatch
import KemenyHardness.FromMaxCut.BudgetMatch
import KemenyHardness.FromMaxCut.Program
import KemenyHardness.FromMaxCut.Margins
import KemenyHardness.FromMaxCut.MinTotal
import KemenyHardness.FromMaxCut.Verdicts
import KemenyHardness.FromMaxCut.Scan
import KemenyHardness.FromMaxCut.Forward
import KemenyHardness.FromMaxCut.Meta
import KemenyHardness.FromMaxCut.Gadget
import KemenyHardness.FromMaxCut.Reverse
import KemenyHardness.FromMaxCut.EdgeCost
import KemenyHardness.FromMaxCut.EdgeCut
import KemenyHardness.FromMaxCut.Walk
import KemenyHardness.FromMaxCut.Assembly
import KemenyHardness.FromMaxCut
import KemenyHardness.FromMaxCut.Adequacy

/-!
# The Kemeny three-voters project

Formalization of "Kemeny Rank Aggregation is NP-Hard for Three Voters"
(Peters 2026): a reduction from SIMPLE MAX CUT showing that KEMENY SCORE is
NP-hard already for profiles of three rankings, resolving the question of
Dwork–Kumar–Naor–Sivakumar (2001).

The reduction lands twice. `satToKemeny3 : SAT ⟶ᵣ KEMENY_SCORE_3VOTERS` is the
mathematical statement, over bundled instances; `satToKemeny3Certified :
CertifiedReduction Concrete.SAT Concrete.KEMENY_SCORE_3VOTERS` is the same
reduction as a program of the catalog's builder language, so its instance map
comes with polynomial cost and output-size bounds for free. The certificate's
output names the alternatives by their position in the emitted candidate list
rather than as gadget candidates; relabeling equivariance of the Kemeny score
(`kemenyScore_relabel`) is what makes that difference invisible.

Developed against the `HardnessReductions` catalog (which supplies the source
problem SIMPLE MAX CUT, hard from SAT end to end), but not part of it —
this library is destined for extraction into its own repository.
-/
