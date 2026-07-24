import Kemeny.Rankings
import Kemeny.Margins
import Kemeny.KemenyScore
import Kemeny.Relabel
import Kemeny.Encoding
import Kemeny.BallotOrder
import Kemeny.CloneContraction
import Kemeny.Source
import Kemeny.Source.Certified
import Kemeny.FromMaxCut.Construction
import Kemeny.FromMaxCut.CanonEdges
import Kemeny.FromMaxCut.Code
import Kemeny.FromMaxCut.Ballots
import Kemeny.FromMaxCut.CandNumbering
import Kemeny.FromMaxCut.AbsBallots
import Kemeny.FromMaxCut.BallotMatch
import Kemeny.FromMaxCut.BudgetMatch
import Kemeny.FromMaxCut.Program
import Kemeny.FromMaxCut.Margins
import Kemeny.FromMaxCut.MinTotal
import Kemeny.FromMaxCut.Verdicts
import Kemeny.FromMaxCut.Scan
import Kemeny.FromMaxCut.Forward
import Kemeny.FromMaxCut.Meta
import Kemeny.FromMaxCut.Gadget
import Kemeny.FromMaxCut.Reverse
import Kemeny.FromMaxCut.EdgeCost
import Kemeny.FromMaxCut.EdgeCut
import Kemeny.FromMaxCut.Walk
import Kemeny.FromMaxCut.Assembly
import Kemeny.FromMaxCut
import Kemeny.FromMaxCut.Adequacy

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
