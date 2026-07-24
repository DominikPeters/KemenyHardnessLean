import Mathlib.Tactic.DeriveFintype
import Kemeny.KemenyScore
import Kemeny.Margins
import Kemeny.Source

/-!
# The construction: a three-voter Kemeny instance from a MAX CUT instance

The instance map of the reduction SIMPLE MAX CUT with long even edges →
KEMENY SCORE with three voters, following the paper's Sections 3 and 6.

## Candidates

For each vertex `i` of the graph, six *supercandidates* `A_i, …, F_i`, each a
set of `M` fresh candidates (`M = 1000 (n+1)⁴`, `bigM`); for each edge `e`,
two *edge candidates* `ℓ_e` and `r_e` (`ℓ_e` wants an endpoint of `e` in the
left part of the cut, `r_e` in the right part). Fresh names are tagged tuples,
per the library's discipline: a vertex candidate is `(i, X, s) : Fin n ×
Letter × Fin M`, an edge candidate is `(e, side)` with `e` an edge in its
increasing orientation (`EdgePair`).

## The three voters

Each voter is a linear order obtained by lifting an injective key
`Cand → ℕ ×ₗ ℕ ×ₗ ℕ` — (gadget, slot, tie) — so that all comparisons happen
in the *canonical* order on `ℕ` and the bundled-order instance traps of
`STYLE.md` cannot arise at the key level. A `VoterSpec` packages what varies
between the three voters:

* `gadgetPos`: where each vertex gadget goes (voters 1 and 3 ascending,
  voter 2 descending);
* `localPos`: the voter's ordering of the six letters within a gadget
  (`AEFBCD`, `BDFACE`, `CDEABF` — the orders whose majority is the paper's
  gadget tournament);
* `edgeGadget`, `gapLetter`: which gadget an edge candidate visits for this
  voter, and *after which letter* it sits there (voter 1: `ℓ_e` after `A_i`,
  `r_e` after `B_i`; voter 2: both after `F_q`, `q` the midpoint; voter 3:
  `ℓ_e` after `B_j`, `r_e` after `D_j`).

Slots interleave letters and gaps by parity: the letter at local position `p`
occupies slot `2p + 1`, and an edge candidate in the gap *after* the letter at
local position `p` occupies slot `2p + 2`. Edge candidates sharing a gap are
tied on (gadget, slot) and separated by an injective tie key whose *direction*
is never consumed by any correctness argument — the paper's "break ties
arbitrarily".

## The instance map

`kemenyMap` sends a numbered graph instance to the three-voter profile with
budget `b = 3nM² + M·Σ_e (6·span e + 3) + n⁴ − Mk` — guarded by
`k ≤ #edges`. Instances with `k > #edges` are NO instances of MAX CUT (a cut
cannot exceed the edge count) and are sent to the fixed NO instance
`kemenyNoInstance`; on the guarded branch the budget's truncated subtraction
is exact, since `Mk ≤ M·Σ_e (6·span e + 3)`. The guard matters: the paper's
budget lives in `ℤ`, and truncating it at `0` would otherwise turn the empty
graph with `k ≥ 1` into a YES instance (the empty profile has cost `0`).
-/

namespace Hardness

/-! ## Letters and sides -/

/-- The six supercandidate letters of a vertex gadget. -/
inductive Letter : Type
  | A | B | C | D | E | F
  deriving DecidableEq, Fintype

/-- Which endpoint an edge candidate roots for: `ℓ_e` (`left`) wants an
endpoint of its edge in the left part of the cut, `r_e` (`right`) in the
right part. -/
inductive Side : Type
  | left | right
  deriving DecidableEq, Fintype

/-! ## Edges in increasing orientation -/

/-- An edge of a numbered graph, carried in its increasing orientation: an
adjacent pair with `i < j`. Each undirected edge appears exactly once, so
sums and counts over `EdgePair` are sums and counts over the edge set. -/
abbrev EdgePair (n : ℕ) (G : SimpleGraph (Fin n)) : Type :=
  {p : Fin n × Fin n // G.Adj p.1 p.2 ∧ p.1.val < p.2.val}

namespace EdgePair

variable {n : ℕ} {G : SimpleGraph (Fin n)}

/-- The smaller endpoint of the edge. -/
def i (e : EdgePair n G) : Fin n := e.val.1

/-- The larger endpoint of the edge. -/
def j (e : EdgePair n G) : Fin n := e.val.2

theorem adj (e : EdgePair n G) : G.Adj e.i e.j := e.prop.1

theorem i_lt_j (e : EdgePair n G) : e.i.val < e.j.val := e.prop.2

/-- The midpoint gadget index `q = (i + j) / 2` of the edge — a genuine
midpoint on long even edges, and in any case a valid vertex index. -/
def mid (e : EdgePair n G) : Fin n :=
  ⟨(e.val.1.val + e.val.2.val) / 2, by
    have h1 := e.val.2.isLt
    have h2 := e.prop.2
    omega⟩

theorem mid_val (e : EdgePair n G) : e.mid.val = (e.i.val + e.j.val) / 2 := rfl

/-- The span `d = j − i` of the edge — the `d` of the paper's cost tables. -/
def span (e : EdgePair n G) : ℕ := e.val.2.val - e.val.1.val

theorem span_def (e : EdgePair n G) : e.span = e.j.val - e.i.val := rfl

/-- The tie key separating edge candidates that share a (gadget, slot) pair
in some voter. Injective on `(edge, side)` pairs — which is all any proof
ever uses: the *direction* of a tie is the paper's "break ties arbitrarily"
and is never consumed. -/
def tie (e : EdgePair n G) (s : Side) : ℕ :=
  2 * (e.val.1.val * n + e.val.2.val) + (match s with | Side.left => 0 | Side.right => 1)

private theorem base_inj {a b a' b' N : ℕ} (hb : b < N) (hb' : b' < N)
    (h : a * N + b = a' * N + b') : a = a' ∧ b = b' := by
  rcases Nat.lt_trichotomy a a' with hlt | rfl | hlt
  · have key : (a + 1) * N ≤ a' * N := Nat.mul_le_mul_right N hlt
    rw [Nat.succ_mul] at key
    omega
  · exact ⟨rfl, by omega⟩
  · have key : (a' + 1) * N ≤ a * N := Nat.mul_le_mul_right N hlt
    rw [Nat.succ_mul] at key
    omega

theorem tie_injective {e e' : EdgePair n G} {s s' : Side}
    (h : tie e s = tie e' s') : e = e' ∧ s = s' := by
  have hj := e.val.2.isLt
  have hj' := e'.val.2.isLt
  cases s <;> cases s' <;> simp only [tie] at h
  case left.right | right.left => omega
  all_goals
    obtain ⟨h1, h2⟩ := base_inj hj hj' (by omega :
      e.val.1.val * n + e.val.2.val = e'.val.1.val * n + e'.val.2.val)
    exact ⟨Subtype.ext (Prod.ext (Fin.ext h1) (Fin.ext h2)), rfl⟩

end EdgePair

/-! ## Candidates -/

/-- The candidate set of the produced Kemeny instance: a vertex candidate is
(vertex, letter, member index within the supercandidate); an edge candidate
is (edge, side). -/
abbrev Cand (n M : ℕ) (G : SimpleGraph (Fin n)) : Type :=
  (Fin n × Letter × Fin M) ⊕ (EdgePair n G × Side)

/-! ## Voter specifications -/

/-- What distinguishes the three voters: where the vertex gadgets go, how the
six letters are ordered within a gadget, and which gadget — and which gap of
it — each edge candidate visits. The key built from a spec (`VoterSpec.key`)
is injective, and the voter is the lift of the key
(`VoterSpec.ranking`). -/
structure VoterSpec (n : ℕ) (G : SimpleGraph (Fin n)) : Type where
  /-- Position of each vertex gadget in this ranking. -/
  gadgetPos : Fin n → ℕ
  gadgetPos_inj : Function.Injective gadgetPos
  /-- The ordering of the six letters within gadget `i`: `localPos i x` is
  the local position of supercandidate `X_i`. Vertex-dependent so that the
  *output* ranking of the forward direction — `ABCDEF` or `DAEBFC` per the
  side of the cut — is also an instance; the three voters use a constant
  order. -/
  localPos : Fin n → Letter → ℕ
  localPos_inj : ∀ i, Function.Injective (localPos i)
  /-- The gadget an edge candidate visits in this ranking. Edge- and
  side-dependent for the output ranking's placement table; the voters key
  all edge candidates of `e` by one endpoint or the midpoint. -/
  edgeGadget : EdgePair n G → Side → Fin n
  /-- The letter after which an edge candidate sits, inside its gadget. -/
  gapLetter : EdgePair n G → Side → Letter

namespace VoterSpec

variable {n : ℕ} {G : SimpleGraph (Fin n)}

/-- The key of a candidate: (gadget position, slot within gadget, tie).
Letters occupy odd slots `2·pos + 1`, edge candidates the even gap slots
`2·pos + 2`, so the two kinds never collide. -/
def key (V : VoterSpec n G) {M : ℕ} : Cand n M G → ℕ ×ₗ ℕ ×ₗ ℕ
  | .inl (i, x, m) =>
      toLex (V.gadgetPos i, toLex (2 * V.localPos i x + 1, m.val))
  | .inr (e, s) =>
      toLex (V.gadgetPos (V.edgeGadget e s),
        toLex (2 * V.localPos (V.edgeGadget e s) (V.gapLetter e s) + 2, e.tie s))

@[simp] theorem key_inl (V : VoterSpec n G) {M : ℕ} (i : Fin n) (x : Letter) (m : Fin M) :
    V.key (Sum.inl (i, x, m)) =
      toLex (V.gadgetPos i, toLex (2 * V.localPos i x + 1, m.val)) := rfl

@[simp] theorem key_inr (V : VoterSpec n G) {M : ℕ} (e : EdgePair n G) (s : Side) :
    V.key (M := M) (Sum.inr (e, s)) =
      toLex (V.gadgetPos (V.edgeGadget e s),
        toLex (2 * V.localPos (V.edgeGadget e s) (V.gapLetter e s) + 2, e.tie s)) := rfl

theorem key_injective (V : VoterSpec n G) (M : ℕ) :
    Function.Injective (V.key (M := M)) := by
  rintro (⟨i, x, m⟩ | ⟨e, s⟩) (⟨i', x', m'⟩ | ⟨e', s'⟩) h <;>
    simp only [key_inl, key_inr, toLex_inj, Prod.mk.injEq] at h
  · obtain ⟨h1, h2, h3⟩ := h
    obtain rfl := V.gadgetPos_inj h1
    obtain rfl : x = x' := V.localPos_inj i (by omega)
    obtain rfl : m = m' := Fin.ext h3
    rfl
  · exact absurd h.2.1 (by omega)
  · exact absurd h.2.1 (by omega)
  · obtain ⟨-, -, h3⟩ := h
    obtain ⟨rfl, rfl⟩ := EdgePair.tie_injective h3
    rfl

/-- The voter: the linear order on candidates lifted from the key. -/
@[implicit_reducible]
def ranking (V : VoterSpec n G) (M : ℕ) : LinearOrder (Cand n M G) :=
  LinearOrder.lift' V.key (V.key_injective M)

/-- The raw comparison law: the lifted order compares keys. -/
theorem ranking_lt_iff (V : VoterSpec n G) {M : ℕ} {c c' : Cand n M G} :
    (V.ranking M).lt c c' ↔ V.key c < V.key c' := Iff.rfl

private theorem lex3_lt_iff {a b c a' b' c' : ℕ} :
    (toLex (a, toLex (b, c)) : ℕ ×ₗ ℕ ×ₗ ℕ) < toLex (a', toLex (b', c')) ↔
      a < a' ∨ a = a' ∧ (b < b' ∨ b = b' ∧ c < c') := by
  simp only [Prod.Lex.lt_iff, ofLex_toLex]

/-! ### Comparison laws by candidate kind

The complete downstream interface: nothing below this file ever unfolds a
key again. Slot arithmetic (`2p + 1` versus `2q + 2`) is discharged here once
and for all — between a letter and a gap, "at or after the gap's letter"
versus "strictly after" is the parity of the slots. -/

theorem lt_vertex_vertex (V : VoterSpec n G) {M : ℕ} {i i' : Fin n}
    {x x' : Letter} {m m' : Fin M} :
    (V.ranking M).lt (Sum.inl (i, x, m)) (Sum.inl (i', x', m')) ↔
      V.gadgetPos i < V.gadgetPos i' ∨ V.gadgetPos i = V.gadgetPos i' ∧
        (V.localPos i x < V.localPos i' x' ∨
          V.localPos i x = V.localPos i' x' ∧ m < m') := by
  rw [ranking_lt_iff, key_inl, key_inl, lex3_lt_iff]
  constructor
  · rintro (h | ⟨h1, h2 | ⟨h2, h3⟩⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h1, Or.inl (by omega)⟩
    · exact Or.inr ⟨h1, Or.inr ⟨by omega, Fin.lt_def.mpr h3⟩⟩
  · rintro (h | ⟨h1, h2 | ⟨h2, h3⟩⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h1, Or.inl (by omega)⟩
    · exact Or.inr ⟨h1, Or.inr ⟨by omega, Fin.lt_def.mp h3⟩⟩

theorem lt_vertex_edge (V : VoterSpec n G) {M : ℕ} {i : Fin n} {x : Letter}
    {m : Fin M} {e : EdgePair n G} {s : Side} :
    (V.ranking M).lt (Sum.inl (i, x, m)) (Sum.inr (e, s)) ↔
      V.gadgetPos i < V.gadgetPos (V.edgeGadget e s) ∨
        V.gadgetPos i = V.gadgetPos (V.edgeGadget e s) ∧
          V.localPos i x ≤ V.localPos (V.edgeGadget e s) (V.gapLetter e s) := by
  rw [ranking_lt_iff, key_inl, key_inr, lex3_lt_iff]
  constructor
  · rintro (h | ⟨h1, h2 | ⟨h2, -⟩⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h1, by omega⟩
    · exact Or.inr ⟨h1, by omega⟩
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h1, Or.inl (by omega)⟩

theorem lt_edge_vertex (V : VoterSpec n G) {M : ℕ} {e : EdgePair n G} {s : Side}
    {i : Fin n} {x : Letter} {m : Fin M} :
    (V.ranking M).lt (Sum.inr (e, s)) (Sum.inl (i, x, m)) ↔
      V.gadgetPos (V.edgeGadget e s) < V.gadgetPos i ∨
        V.gadgetPos (V.edgeGadget e s) = V.gadgetPos i ∧
          V.localPos (V.edgeGadget e s) (V.gapLetter e s) < V.localPos i x := by
  rw [ranking_lt_iff, key_inr, key_inl, lex3_lt_iff]
  constructor
  · rintro (h | ⟨h1, h2 | ⟨h2, -⟩⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h1, by omega⟩
    · exact Or.inr ⟨h1, by omega⟩
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h1, Or.inl (by omega)⟩

theorem lt_edge_edge (V : VoterSpec n G) {M : ℕ} {e e' : EdgePair n G} {s s' : Side} :
    (V.ranking M).lt (Sum.inr (e, s)) (Sum.inr (e', s')) ↔
      V.gadgetPos (V.edgeGadget e s) < V.gadgetPos (V.edgeGadget e' s') ∨
        V.gadgetPos (V.edgeGadget e s) = V.gadgetPos (V.edgeGadget e' s') ∧
          (V.localPos (V.edgeGadget e s) (V.gapLetter e s) <
              V.localPos (V.edgeGadget e' s') (V.gapLetter e' s') ∨
            V.localPos (V.edgeGadget e s) (V.gapLetter e s) =
              V.localPos (V.edgeGadget e' s') (V.gapLetter e' s') ∧
              e.tie s < e'.tie s') := by
  rw [ranking_lt_iff, key_inr, key_inr, lex3_lt_iff]
  constructor <;>
  · rintro (h | ⟨h1, h2 | ⟨h2, h3⟩⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h1, Or.inl (by omega)⟩
    · exact Or.inr ⟨h1, Or.inr ⟨by omega, h3⟩⟩

end VoterSpec

/-! ## The three voters -/

/-- Voter 1's local order `AEFBCD`. -/
def pos1 : Letter → ℕ
  | .A => 0 | .E => 1 | .F => 2 | .B => 3 | .C => 4 | .D => 5

/-- Voter 2's local order `BDFACE`. -/
def pos2 : Letter → ℕ
  | .B => 0 | .D => 1 | .F => 2 | .A => 3 | .C => 4 | .E => 5

/-- Voter 3's local order `CDEABF`. -/
def pos3 : Letter → ℕ
  | .C => 0 | .D => 1 | .E => 2 | .A => 3 | .B => 4 | .F => 5

theorem pos1_inj : Function.Injective pos1 := by
  intro x y h
  cases x <;> cases y <;> simp_all [pos1]

theorem pos2_inj : Function.Injective pos2 := by
  intro x y h
  cases x <;> cases y <;> simp_all [pos2]

theorem pos3_inj : Function.Injective pos3 := by
  intro x y h
  cases x <;> cases y <;> simp_all [pos3]

variable (n : ℕ) (G : SimpleGraph (Fin n))

/-- Voter 1: gadgets ascending in local order `AEFBCD`; `ℓ_e` after `A_i` and
`r_e` after `B_i`, at the *left endpoint* of the edge. -/
def spec1 : VoterSpec n G where
  gadgetPos := Fin.val
  gadgetPos_inj := Fin.val_injective
  localPos := fun _ ↦ pos1
  localPos_inj := fun _ ↦ pos1_inj
  edgeGadget := fun e _ ↦ e.i
  gapLetter := fun _ s ↦ match s with | .left => .A | .right => .B

/-- Voter 2: gadgets *descending* in local order `BDFACE`; both edge
candidates after `F_q`, at the *midpoint* of the edge. -/
def spec2 : VoterSpec n G where
  gadgetPos := fun v ↦ n - 1 - v.val
  gadgetPos_inj := fun v w h ↦ by
    have hv := v.isLt
    have hw := w.isLt
    dsimp only at h
    exact Fin.ext (by omega)
  localPos := fun _ ↦ pos2
  localPos_inj := fun _ ↦ pos2_inj
  edgeGadget := fun e _ ↦ e.mid
  gapLetter := fun _ _ ↦ .F

/-- Voter 3: gadgets ascending in local order `CDEABF`; `ℓ_e` after `B_j` and
`r_e` after `D_j`, at the *right endpoint* of the edge. -/
def spec3 : VoterSpec n G where
  gadgetPos := Fin.val
  gadgetPos_inj := Fin.val_injective
  localPos := fun _ ↦ pos3
  localPos_inj := fun _ ↦ pos3_inj
  edgeGadget := fun e _ ↦ e.j
  gapLetter := fun _ s ↦ match s with | .left => .B | .right => .D

/-- The profile of the produced instance: the three voters, in order. -/
def kemenyProfile (M : ℕ) : List (LinearOrder (Cand n M G)) :=
  [(spec1 n G).ranking M, (spec2 n G).ranking M, (spec3 n G).ranking M]

@[simp] theorem kemenyProfile_length (M : ℕ) : (kemenyProfile n G M).length = 3 := rfl

/-! ## The instance map -/

/-- The supercandidate size `M = 1000 (n+1)⁴`: large enough that one
supercandidate outweighs all edge-candidate interactions (`n⁴ < M`), and
`M²` outweighs everything not counted in multiples of `M²`. -/
def bigM (n : ℕ) : ℕ := 1000 * (n + 1) ^ 4

/-- The edge term of the budget: `Σ_e (6·span e + 3)` — each edge's two
candidates cost `M(6d + 3)` when the edge is uncut, `M(6d + 2)` when cut. -/
def edgeBound [DecidableRel G.Adj] : ℕ :=
  ∑ e : EdgePair n G, (6 * e.span + 3)

/-- The slack absorbing all cost between pairs of edge candidates: the square
of the number of edge candidates. The paper uses `C(2|E|,2) ≤ n⁴`; the crude
square needs no combinatorics on either side — the forward direction bounds
the pair count by an injection, and the reverse direction only needs
`pairSlack < M`, via `#edges ≤ n²`. -/
def pairSlack [DecidableRel G.Adj] : ℕ :=
  (2 * Fintype.card (EdgePair n G)) ^ 2

/-- **The cut objective as a sum over `EdgePair`**: every edge of the graph is
carried by exactly one increasing-orientation pair, so counting the crossing
edges of a colouring is summing the crossing indicator over `EdgePair` — the
bridge between the catalog's `cutSize` and the reduction's per-edge cost
accounting. -/
theorem cutSize_eq_sum_edgePair [DecidableRel G.Adj] (χ : Fin n → Bool) :
    cutSize G χ = ∑ e : EdgePair n G, (if χ e.i = χ e.j then 0 else 1) := by
  have hsum : ∑ e : EdgePair n G, (if χ e.i = χ e.j then 0 else 1)
      = (Finset.univ.filter fun e : EdgePair n G ↦ χ e.i ≠ χ e.j).card := by
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun e _ ↦ ?_
    by_cases h : χ e.i = χ e.j
    · rw [if_pos h, if_neg (not_not_intro h)]
    · rw [if_neg h, if_pos h]
  rw [hsum, cutSize]
  refine (Finset.card_nbij (fun e ↦ s(e.i, e.j)) ?_ ?_ ?_).symm
  · intro e he
    rw [Finset.mem_coe, Finset.mem_filter] at he
    rw [Finset.mem_coe, Finset.mem_filter, SimpleGraph.mem_edgeFinset,
      SimpleGraph.mem_edgeSet]
    exact ⟨e.adj, (crosses_iff χ e.i e.j).mpr he.2⟩
  · intro e he e' he' h
    rw [Sym2.eq_iff] at h
    have hlt := e.i_lt_j
    have hlt' := e'.i_lt_j
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Subtype.ext (Prod.ext h1 h2)
    · exfalso
      have hv1 : e.i.val = e'.j.val := congrArg Fin.val h1
      have hv2 : e.j.val = e'.i.val := congrArg Fin.val h2
      omega
  · intro ed hed
    induction ed using Sym2.ind with
    | _ u v =>
      rw [Finset.mem_coe, Finset.mem_filter, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet] at hed
      obtain ⟨hadj, hcr⟩ := hed
      have hne := (crosses_iff χ u v).mp hcr
      rcases Nat.lt_or_ge u.val v.val with hlt | hge
      · refine ⟨⟨(u, v), hadj, hlt⟩, ?_, rfl⟩
        rw [Finset.mem_coe, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hne⟩
      · have hvu : v.val < u.val := by
          have hne' : u.val ≠ v.val := fun hc ↦ G.ne_of_adj hadj (Fin.ext hc)
          omega
        refine ⟨⟨(v, u), hadj.symm, hvu⟩, ?_, Sym2.eq_swap⟩
        rw [Finset.mem_coe, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, Ne.symm hne⟩

/-- The budget in *margin units* (Kemeny₂) — the paper's
`b = 3nM² + M·Σ_e (6·span e + 3) + n⁴ − Mk`, with the `n⁴` slack replaced by
`pairSlack`. Exact (no truncation) whenever `k` is at most the number of
edges, which the instance map guards. -/
def marginBudget (x : NumberedGraphInstance) : ℕ :=
  3 * x.n * bigM x.n ^ 2 + bigM x.n * edgeBound x.n x.G + pairSlack x.n x.G
    - bigM x.n * x.k

/-- The budget of the produced instance, in honest Kendall-tau units: the
profile constant `Σ_pairs min(n_ab, n_ba)` — as `minTotal` against voter 1
as reference — plus the margin budget, per the affine bridge
`Kemeny₁ = Σ min + Kemeny₂`. (The paper's `b` is the margin-unit budget: its
forward computation charges nothing for correctly-ordered cross-gadget
pairs, which cost `1` each in Kendall-tau units. The draft states the
instance budget without adding the constant — reported upstream.) -/
def kemenyBudget (x : NumberedGraphInstance) : ℕ :=
  minTotal (kemenyProfile x.n x.G (bigM x.n)) ((spec1 x.n x.G).ranking (bigM x.n))
    + marginBudget x

/-- The standard order on `Bool`, as a bundled value. -/
@[implicit_reducible]
def boolStd : LinearOrder Bool := inferInstance

/-- The reversed order on `Bool`: the lift of the standard order along
negation. -/
@[implicit_reducible]
def boolOrderRev : LinearOrder Bool :=
  LinearOrder.lift' Bool.not fun a b h ↦ by cases a <;> cases b <;> simp_all

/-- A fixed NO instance of KEMENY SCORE with three voters: two alternatives,
two voters against one, budget zero — every ranking disagrees with some voter
on the pair, so costs at least `1`. The image of the MAX CUT instances with
`k > #edges`, which are NO instances (a cut cannot exceed the edge count). -/
def kemenyNoInstance : KemenyInstance where
  A := Bool
  voters := [boolStd, boolOrderRev, boolStd]
  b := 0

/-- The instance map of the reduction. On the guard `k ≤ #edges`: the
three-voter profile on the gadget candidates, with the paper's budget. Beyond
the guard the MAX CUT instance is a NO instance, and is sent to the fixed NO
instance `kemenyNoInstance`. -/
def kemenyMap (x : NumberedGraphInstance) : KemenyInstance :=
  if x.k ≤ Fintype.card (EdgePair x.n x.G) then
    { A := Cand x.n (bigM x.n) x.G
      voters := kemenyProfile x.n x.G (bigM x.n)
      b := kemenyBudget x }
  else kemenyNoInstance

/-- The image instances all have three voters: the map lands in the domain of
the three-voter restriction. -/
theorem kemenyMap_voters_length (x : NumberedGraphInstance) :
    (kemenyMap x).voters.length = 3 := by
  by_cases h : x.k ≤ Fintype.card (EdgePair x.n x.G)
  · rw [kemenyMap, if_pos h]
    rfl
  · rw [kemenyMap, if_neg h]
    rfl

/-- **The produced question, in margin units**: on guarded instances, the
image is a YES instance of KEMENY SCORE exactly if some ranking meets the
*margin* budget — the affine bridge `exists_kemenyCost_le_iff`, specialized
to the instance map. Both correctness directions go through this and never
see Kendall-tau units again. -/
theorem kemenyMap_iff_marginCost (x : NumberedGraphInstance)
    (hk : x.k ≤ Fintype.card (EdgePair x.n x.G)) :
    KEMENY_SCORE (kemenyMap x) ↔
      ∃ r : LinearOrder (Cand x.n (bigM x.n) x.G),
        marginCost (kemenyProfile x.n x.G (bigM x.n)) r ≤ marginBudget x := by
  have hmap : kemenyMap x =
      { A := Cand x.n (bigM x.n) x.G
        voters := kemenyProfile x.n x.G (bigM x.n)
        b := kemenyBudget x } := by
    rw [kemenyMap, if_pos hk]
  rw [hmap]
  simp only [KEMENY_SCORE, kemenyBudget]
  exact exists_kemenyCost_le_iff _ _ _

end Hardness
