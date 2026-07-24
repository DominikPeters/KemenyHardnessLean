import Kemeny.Rankings
import Kemeny.Margins
import Kemeny.KemenyScore
import Kemeny.CloneContraction
import Kemeny.Source
import Kemeny.FromMaxCut.Construction
import Kemeny.FromMaxCut.Margins
import Kemeny.FromMaxCut.Forward
import Kemeny.FromMaxCut.Meta
import Kemeny.FromMaxCut.Gadget
import Kemeny.FromMaxCut.Reverse
import Kemeny.FromMaxCut.EdgeCost
import Kemeny.FromMaxCut.EdgeCut
import Kemeny.FromMaxCut.Walk

/-!
# The Kemeny three-voters project

Formalization of "Kemeny Rank Aggregation is NP-Hard for Three Voters"
(Peters 2026): a reduction from SIMPLE MAX CUT showing that KEMENY SCORE is
NP-hard already for profiles of three rankings, resolving the question of
Dwork–Kumar–Naor–Sivakumar (2001).

Developed against the `HardnessReductions` catalog (which supplies the source
problem SIMPLE MAX CUT, hard from SAT end to end), but not part of it —
this library is destined for extraction into its own repository.
-/
