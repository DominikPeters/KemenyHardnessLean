import Mathlib.Tactic.IntervalCases
import Kemeny.FromMaxCut.EdgeCut

/-!
# The walk bounds: every cut position pays the per-edge cost

Final mathematical step of the reverse direction's edge analysis.
`EdgeCut.lean` reduced the cost of an edge candidate against the vertex block
to `M` times a cut sum: verdict-`2` supers above a cut position `t` plus
verdict-`1` supers below it. This file bounds that cut sum from below for
*every* cut position — the formal counterpart of walking the edge candidate
through the output chain.

The majority verdicts are evaluated region by region on the seven ranges cut
by the edge's endpoints and midpoint (`edgeVerdict_mid1`, …; the two outer
ranges are never needed — every case drops them). The cut sum is then bounded
by a seven-range scan (`sum_fin_scan_ge`): landmark gadgets and the one
relevant inner range contribute their exact rows (`w_q_below`, …), the rest
is dropped, and the gadget the cut splits contributes a partial term checked
by `decide` over the five interior cut positions (`w_i_left_partial`, …).
Seven cases on the cut position later, each side's minimum is exactly the
forward table: `3d + 2 + [χ i = χ j = R]` for `ℓ_e` and `3d + [χ i = χ j = L]`
for `r_e`, tight at the forward placements. The per-edge deliverable
`sum_orientedMargin_ve_ge` combines the sides: on a block ranking whose
vertex part agrees with the output spec, each edge costs at least
`M (6·span e + 2 + [e uncut])` — the forward value exactly.

The midpoint case of side `r` is the one place that needs edges *long*, not
merely spread: for `span = 2` the bound is genuinely false (parking `r_e`
just below `D_q` of a right midpoint gadget beats the table), so the walk
takes `span ≥ 3`; long even edges give `span ≥ 6`.
-/

namespace Hardness

open Finset

variable {n M : ℕ} {G : SimpleGraph (Fin n)}

/-! ## The verdicts, region by region

Closed evaluations of `edgeVerdict` as functions of the letter alone, per
range of the gadget relative to the edge's endpoints `i < q < j`. Gap letters
matter only at the landmark the voter places the candidate in, so the two
inner ranges and the midpoint are side-generic. -/

private theorem edgeVerdict_mid1 {e : EdgePair n G} (hsp : SpreadEdges n G)
    {u : Fin n} (h1 : e.i.val < u.val) (h2 : u.val < e.mid.val) (s : Side)
    (x : Letter) : edgeVerdict e s u x = 2 := by
  obtain ⟨hiq, hqj, -⟩ := hsp e
  have hun := u.isLt
  have hqn := e.mid.isLt
  simp only [edgeVerdict, specMiss, spec1, spec2, spec3,
    eq_false (show ¬(u.val < e.i.val) from by omega),
    eq_false (show ¬(u.val = e.i.val) from by omega),
    eq_false (show ¬(n - 1 - u.val < n - 1 - e.mid.val) from by omega),
    eq_false (show ¬(n - 1 - u.val = n - 1 - e.mid.val) from by omega),
    eq_true (show u.val < e.j.val from by omega),
    true_or, false_or, false_and, if_true, if_false]

private theorem edgeVerdict_at_q {e : EdgePair n G} (hsp : SpreadEdges n G)
    (s : Side) (x : Letter) :
    edgeVerdict e s e.mid x = if x = .B ∨ x = .D ∨ x = .F then 1 else 2 := by
  obtain ⟨hiq, hqj, -⟩ := hsp e
  have hqn := e.mid.isLt
  simp only [edgeVerdict, specMiss, spec1, spec2, spec3,
    eq_false (show ¬(e.mid.val < e.i.val) from by omega),
    eq_false (show ¬(e.mid.val = e.i.val) from by omega),
    eq_false (show ¬(n - 1 - e.mid.val < n - 1 - e.mid.val) from by omega),
    eq_true hqj,
    true_or, false_or, false_and, if_true, if_false]
  cases x <;> decide

private theorem edgeVerdict_mid2 {e : EdgePair n G} (hsp : SpreadEdges n G)
    {u : Fin n} (h1 : e.mid.val < u.val) (h2 : u.val < e.j.val) (s : Side)
    (x : Letter) : edgeVerdict e s u x = 1 := by
  obtain ⟨hiq, hqj, -⟩ := hsp e
  have hun := u.isLt
  have hqn := e.mid.isLt
  simp only [edgeVerdict, specMiss, spec1, spec2, spec3,
    eq_false (show ¬(u.val < e.i.val) from by omega),
    eq_false (show ¬(u.val = e.i.val) from by omega),
    eq_true (show n - 1 - u.val < n - 1 - e.mid.val from by omega),
    eq_true h2,
    true_or, false_or, false_and, if_true, if_false]

private theorem edgeVerdict_at_i_left {e : EdgePair n G} (hsp : SpreadEdges n G)
    (x : Letter) :
    edgeVerdict e Side.left e.i x = if x = .A then 1 else 2 := by
  obtain ⟨hiq, hqj, -⟩ := hsp e
  have hin := e.i.isLt
  have hqn := e.mid.isLt
  simp only [edgeVerdict, specMiss, spec1, spec2, spec3,
    eq_false (show ¬(e.i.val < e.i.val) from by omega),
    eq_false (show ¬(n - 1 - e.i.val < n - 1 - e.mid.val) from by omega),
    eq_false (show ¬(n - 1 - e.i.val = n - 1 - e.mid.val) from by omega),
    eq_true (show e.i.val < e.j.val from by omega),
    true_or, false_or, false_and, if_true, if_false]
  cases x <;> decide

private theorem edgeVerdict_at_i_right {e : EdgePair n G} (hsp : SpreadEdges n G)
    (x : Letter) :
    edgeVerdict e Side.right e.i x = if x = .C ∨ x = .D then 2 else 1 := by
  obtain ⟨hiq, hqj, -⟩ := hsp e
  have hin := e.i.isLt
  have hqn := e.mid.isLt
  simp only [edgeVerdict, specMiss, spec1, spec2, spec3,
    eq_false (show ¬(e.i.val < e.i.val) from by omega),
    eq_false (show ¬(n - 1 - e.i.val < n - 1 - e.mid.val) from by omega),
    eq_false (show ¬(n - 1 - e.i.val = n - 1 - e.mid.val) from by omega),
    eq_true (show e.i.val < e.j.val from by omega),
    true_or, false_or, false_and, if_true, if_false]
  cases x <;> decide

private theorem edgeVerdict_at_j_left {e : EdgePair n G} (hsp : SpreadEdges n G)
    (x : Letter) :
    edgeVerdict e Side.left e.j x = if x = .F then 2 else 1 := by
  obtain ⟨hiq, hqj, -⟩ := hsp e
  have hjn := e.j.isLt
  have hqn := e.mid.isLt
  simp only [edgeVerdict, specMiss, spec1, spec2, spec3,
    eq_false (show ¬(e.j.val < e.i.val) from by omega),
    eq_false (show ¬(e.j.val = e.i.val) from by omega),
    eq_true (show n - 1 - e.j.val < n - 1 - e.mid.val from by omega),
    eq_false (show ¬(e.j.val < e.j.val) from by omega),
    true_or, false_or, false_and, if_true, if_false]
  cases x <;> decide

private theorem edgeVerdict_at_j_right {e : EdgePair n G} (hsp : SpreadEdges n G)
    (x : Letter) :
    edgeVerdict e Side.right e.j x = if x = .C ∨ x = .D then 1 else 2 := by
  obtain ⟨hiq, hqj, -⟩ := hsp e
  have hjn := e.j.isLt
  have hqn := e.mid.isLt
  simp only [edgeVerdict, specMiss, spec1, spec2, spec3,
    eq_false (show ¬(e.j.val < e.i.val) from by omega),
    eq_false (show ¬(e.j.val = e.i.val) from by omega),
    eq_true (show n - 1 - e.j.val < n - 1 - e.mid.val from by omega),
    eq_false (show ¬(e.j.val < e.j.val) from by omega),
    true_or, false_or, false_and, if_true, if_false]
  cases x <;> decide

/-! ## Stripping the cut condition on unsplit gadgets -/

/-- A gadget entirely below the cut contributes its `A`-row. -/
private theorem inner_below {χ : Fin n → Bool} {u : Fin n} {t : ℕ}
    (ht : t ≤ 6 * u.val) {e : EdgePair n G} (s : Side) :
    ∑ x : Letter, (if superHeight χ u x < t then edgeVerdict e s u x - 1
        else 2 - edgeVerdict e s u x)
      = ∑ x : Letter, (2 - edgeVerdict e s u x) :=
  Finset.sum_congr rfl fun x _ ↦ if_neg (by rw [superHeight]; omega)

/-- A gadget entirely above the cut contributes its `B`-row. -/
private theorem inner_above {χ : Fin n → Bool} {u : Fin n} {t : ℕ}
    (ht : 6 * u.val + 5 < t) {e : EdgePair n G} (s : Side) :
    ∑ x : Letter, (if superHeight χ u x < t then edgeVerdict e s u x - 1
        else 2 - edgeVerdict e s u x)
      = ∑ x : Letter, (edgeVerdict e s u x - 1) :=
  Finset.sum_congr rfl fun x _ ↦
    if_pos (by have h := outPos_lt_six (χ u) x; rw [superHeight]; omega)

/-! ## The rows of the landmark gadgets and inner ranges -/

private theorem w_mid1_above {e : EdgePair n G} (hsp : SpreadEdges n G)
    {u : Fin n} (h1 : e.i.val < u.val) (h2 : u.val < e.mid.val) (s : Side)
    (χ : Fin n → Bool) {t : ℕ} (ht : 6 * u.val + 5 < t) :
    ∑ x : Letter, (if superHeight χ u x < t then edgeVerdict e s u x - 1
        else 2 - edgeVerdict e s u x) = 6 := by
  rw [inner_above ht s]
  simp only [edgeVerdict_mid1 hsp h1 h2 s]
  rw [sum_letter]

private theorem w_mid2_below {e : EdgePair n G} (hsp : SpreadEdges n G)
    {u : Fin n} (h1 : e.mid.val < u.val) (h2 : u.val < e.j.val) (s : Side)
    (χ : Fin n → Bool) {t : ℕ} (ht : t ≤ 6 * u.val) :
    ∑ x : Letter, (if superHeight χ u x < t then edgeVerdict e s u x - 1
        else 2 - edgeVerdict e s u x) = 6 := by
  rw [inner_below ht s]
  simp only [edgeVerdict_mid2 hsp h1 h2 s]
  rw [sum_letter]

private theorem w_q_below {e : EdgePair n G} (hsp : SpreadEdges n G) (s : Side)
    (χ : Fin n → Bool) {t : ℕ} (ht : t ≤ 6 * e.mid.val) :
    ∑ x : Letter, (if superHeight χ e.mid x < t then edgeVerdict e s e.mid x - 1
        else 2 - edgeVerdict e s e.mid x) = 3 := by
  rw [inner_below ht s]
  simp only [edgeVerdict_at_q hsp s]
  rw [sum_letter]
  decide

private theorem w_q_above {e : EdgePair n G} (hsp : SpreadEdges n G) (s : Side)
    (χ : Fin n → Bool) {t : ℕ} (ht : 6 * e.mid.val + 5 < t) :
    ∑ x : Letter, (if superHeight χ e.mid x < t then edgeVerdict e s e.mid x - 1
        else 2 - edgeVerdict e s e.mid x) = 3 := by
  rw [inner_above ht s]
  simp only [edgeVerdict_at_q hsp s]
  rw [sum_letter]
  decide

private theorem w_i_left_below {e : EdgePair n G} (hsp : SpreadEdges n G)
    (χ : Fin n → Bool) {t : ℕ} (ht : t ≤ 6 * e.i.val) :
    ∑ x : Letter, (if superHeight χ e.i x < t then edgeVerdict e Side.left e.i x - 1
        else 2 - edgeVerdict e Side.left e.i x) = 1 := by
  rw [inner_below ht Side.left]
  simp only [edgeVerdict_at_i_left hsp]
  rw [sum_letter]
  decide

private theorem w_i_left_above {e : EdgePair n G} (hsp : SpreadEdges n G)
    (χ : Fin n → Bool) {t : ℕ} (ht : 6 * e.i.val + 5 < t) :
    ∑ x : Letter, (if superHeight χ e.i x < t then edgeVerdict e Side.left e.i x - 1
        else 2 - edgeVerdict e Side.left e.i x) = 5 := by
  rw [inner_above ht Side.left]
  simp only [edgeVerdict_at_i_left hsp]
  rw [sum_letter]
  decide

private theorem w_j_left_below {e : EdgePair n G} (hsp : SpreadEdges n G)
    (χ : Fin n → Bool) {t : ℕ} (ht : t ≤ 6 * e.j.val) :
    ∑ x : Letter, (if superHeight χ e.j x < t then edgeVerdict e Side.left e.j x - 1
        else 2 - edgeVerdict e Side.left e.j x) = 5 := by
  rw [inner_below ht Side.left]
  simp only [edgeVerdict_at_j_left hsp]
  rw [sum_letter]
  decide

private theorem w_j_left_above {e : EdgePair n G} (hsp : SpreadEdges n G)
    (χ : Fin n → Bool) {t : ℕ} (ht : 6 * e.j.val + 5 < t) :
    ∑ x : Letter, (if superHeight χ e.j x < t then edgeVerdict e Side.left e.j x - 1
        else 2 - edgeVerdict e Side.left e.j x) = 1 := by
  rw [inner_above ht Side.left]
  simp only [edgeVerdict_at_j_left hsp]
  rw [sum_letter]
  decide

private theorem w_i_right_below {e : EdgePair n G} (hsp : SpreadEdges n G)
    (χ : Fin n → Bool) {t : ℕ} (ht : t ≤ 6 * e.i.val) :
    ∑ x : Letter, (if superHeight χ e.i x < t then edgeVerdict e Side.right e.i x - 1
        else 2 - edgeVerdict e Side.right e.i x) = 4 := by
  rw [inner_below ht Side.right]
  simp only [edgeVerdict_at_i_right hsp]
  rw [sum_letter]
  decide

private theorem w_i_right_above {e : EdgePair n G} (hsp : SpreadEdges n G)
    (χ : Fin n → Bool) {t : ℕ} (ht : 6 * e.i.val + 5 < t) :
    ∑ x : Letter, (if superHeight χ e.i x < t then edgeVerdict e Side.right e.i x - 1
        else 2 - edgeVerdict e Side.right e.i x) = 2 := by
  rw [inner_above ht Side.right]
  simp only [edgeVerdict_at_i_right hsp]
  rw [sum_letter]
  decide

private theorem w_j_right_below {e : EdgePair n G} (hsp : SpreadEdges n G)
    (χ : Fin n → Bool) {t : ℕ} (ht : t ≤ 6 * e.j.val) :
    ∑ x : Letter, (if superHeight χ e.j x < t then edgeVerdict e Side.right e.j x - 1
        else 2 - edgeVerdict e Side.right e.j x) = 2 := by
  rw [inner_below ht Side.right]
  simp only [edgeVerdict_at_j_right hsp]
  rw [sum_letter]
  decide

private theorem w_j_right_above {e : EdgePair n G} (hsp : SpreadEdges n G)
    (χ : Fin n → Bool) {t : ℕ} (ht : 6 * e.j.val + 5 < t) :
    ∑ x : Letter, (if superHeight χ e.j x < t then edgeVerdict e Side.right e.j x - 1
        else 2 - edgeVerdict e Side.right e.j x) = 4 := by
  rw [inner_above ht Side.right]
  simp only [edgeVerdict_at_j_right hsp]
  rw [sum_letter]
  decide

/-! ## The split gadgets

Only the landmarks `i` and `j` are ever split by a surviving cut — every case
that splits `q` has slack and drops the partial term. The five interior cut
positions are a `decide` after the letter order is fixed by the colouring. -/

private theorem w_i_left_partial {e : EdgePair n G} (hsp : SpreadEdges n G)
    (χ : Fin n → Bool) {t : ℕ} (h1 : 6 * e.i.val < t) (h2 : t < 6 * (e.i.val + 1)) :
    (if χ e.i then 0 else 1)
      ≤ ∑ x : Letter, (if superHeight χ e.i x < t then edgeVerdict e Side.left e.i x - 1
          else 2 - edgeVerdict e Side.left e.i x) := by
  simp only [edgeVerdict_at_i_left hsp]
  obtain ⟨c, rfl⟩ : ∃ c, t = 6 * e.i.val + c := ⟨t - 6 * e.i.val, by omega⟩
  have hc1 : 0 < c := by omega
  have hc2 : c < 6 := by omega
  simp only [superHeight, add_lt_add_iff_left]
  rw [sum_letter]
  cases hχ : χ e.i
  · simp only [Bool.false_eq_true, if_false]
    interval_cases c <;> decide
  · simp only [if_true]
    interval_cases c <;> decide

private theorem w_i_right_partial {e : EdgePair n G} (hsp : SpreadEdges n G)
    (χ : Fin n → Bool) {t : ℕ} (h1 : 6 * e.i.val < t) (h2 : t < 6 * (e.i.val + 1)) :
    (if χ e.i then 2 else 1)
      ≤ ∑ x : Letter, (if superHeight χ e.i x < t then edgeVerdict e Side.right e.i x - 1
          else 2 - edgeVerdict e Side.right e.i x) := by
  simp only [edgeVerdict_at_i_right hsp]
  obtain ⟨c, rfl⟩ : ∃ c, t = 6 * e.i.val + c := ⟨t - 6 * e.i.val, by omega⟩
  have hc1 : 0 < c := by omega
  have hc2 : c < 6 := by omega
  simp only [superHeight, add_lt_add_iff_left]
  rw [sum_letter]
  cases hχ : χ e.i
  · simp only [Bool.false_eq_true, if_false]
    interval_cases c <;> decide
  · simp only [if_true]
    interval_cases c <;> decide

private theorem w_j_left_partial {e : EdgePair n G} (hsp : SpreadEdges n G)
    (χ : Fin n → Bool) {t : ℕ} (h1 : 6 * e.j.val < t) (h2 : t < 6 * (e.j.val + 1)) :
    (if χ e.j then 0 else 1)
      ≤ ∑ x : Letter, (if superHeight χ e.j x < t then edgeVerdict e Side.left e.j x - 1
          else 2 - edgeVerdict e Side.left e.j x) := by
  simp only [edgeVerdict_at_j_left hsp]
  obtain ⟨c, rfl⟩ : ∃ c, t = 6 * e.j.val + c := ⟨t - 6 * e.j.val, by omega⟩
  have hc1 : 0 < c := by omega
  have hc2 : c < 6 := by omega
  simp only [superHeight, add_lt_add_iff_left]
  rw [sum_letter]
  cases hχ : χ e.j
  · simp only [Bool.false_eq_true, if_false]
    interval_cases c <;> decide
  · simp only [if_true]
    interval_cases c <;> decide

private theorem w_j_right_partial {e : EdgePair n G} (hsp : SpreadEdges n G)
    (χ : Fin n → Bool) {t : ℕ} (h1 : 6 * e.j.val < t) (h2 : t < 6 * (e.j.val + 1)) :
    (if χ e.j then 2 else 1)
      ≤ ∑ x : Letter, (if superHeight χ e.j x < t then edgeVerdict e Side.right e.j x - 1
          else 2 - edgeVerdict e Side.right e.j x) := by
  simp only [edgeVerdict_at_j_right hsp]
  obtain ⟨c, rfl⟩ : ∃ c, t = 6 * e.j.val + c := ⟨t - 6 * e.j.val, by omega⟩
  have hc1 : 0 < c := by omega
  have hc2 : c < 6 := by omega
  simp only [superHeight, add_lt_add_iff_left]
  rw [sum_letter]
  cases hχ : χ e.j
  · simp only [Bool.false_eq_true, if_false]
    interval_cases c <;> decide
  · simp only [if_true]
    interval_cases c <;> decide

/-! ## The seven-range lower-bound scan -/

/-- **The seven-range lower-bound scan**: a sum over `Fin n` dominates the
landmark values at `iv`, `qv`, `jv` plus constants on the two inner ranges;
the outer ranges are dropped. The interval bookkeeping of the walk bounds,
once and for all. -/
private theorem sum_fin_scan_ge {f : Fin n → ℕ} {iv qv jv : ℕ}
    (a b c d g : ℕ) (hiq : iv < qv) (hqj : qv < jv) (hjn : jv < n)
    (hI : ∀ u : Fin n, u.val = iv → a ≤ f u)
    (h1 : ∀ u : Fin n, iv < u.val → u.val < qv → b ≤ f u)
    (hQ : ∀ u : Fin n, u.val = qv → c ≤ f u)
    (h2 : ∀ u : Fin n, qv < u.val → u.val < jv → d ≤ f u)
    (hJ : ∀ u : Fin n, u.val = jv → g ≤ f u) :
    a + (qv - (iv + 1)) * b + c + (jv - (qv + 1)) * d + g ≤ ∑ u : Fin n, f u := by
  set F : ℕ → ℕ := fun uv ↦ if h : uv < n then f ⟨uv, h⟩ else 0 with hF
  have hval : ∀ (uv : ℕ) (h : uv < n), F uv = f ⟨uv, h⟩ := by
    intro uv h
    rw [hF]
    exact dif_pos h
  have eI : a ≤ ∑ uv ∈ Finset.Ico iv (iv + 1), F uv := by
    rw [Nat.Ico_succ_singleton, Finset.sum_singleton, hval iv (by omega)]
    exact hI _ rfl
  have e1 : (qv - (iv + 1)) * b ≤ ∑ uv ∈ Finset.Ico (iv + 1) qv, F uv := by
    calc (qv - (iv + 1)) * b = ∑ _uv ∈ Finset.Ico (iv + 1) qv, b := by
          rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]
      _ ≤ ∑ uv ∈ Finset.Ico (iv + 1) qv, F uv :=
          Finset.sum_le_sum fun uv huv ↦ by
            rw [Finset.mem_Ico] at huv
            rw [hval uv (by omega)]
            exact h1 _ (show iv < uv from by omega) huv.2
  have eQ : c ≤ ∑ uv ∈ Finset.Ico qv (qv + 1), F uv := by
    rw [Nat.Ico_succ_singleton, Finset.sum_singleton, hval qv (by omega)]
    exact hQ _ rfl
  have e2 : (jv - (qv + 1)) * d ≤ ∑ uv ∈ Finset.Ico (qv + 1) jv, F uv := by
    calc (jv - (qv + 1)) * d = ∑ _uv ∈ Finset.Ico (qv + 1) jv, d := by
          rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]
      _ ≤ ∑ uv ∈ Finset.Ico (qv + 1) jv, F uv :=
          Finset.sum_le_sum fun uv huv ↦ by
            rw [Finset.mem_Ico] at huv
            rw [hval uv (by omega)]
            exact h2 _ (show qv < uv from by omega) huv.2
  have eJ : g ≤ ∑ uv ∈ Finset.Ico jv (jv + 1), F uv := by
    rw [Nat.Ico_succ_singleton, Finset.sum_singleton, hval jv hjn]
    exact hJ _ rfl
  have hsplit : ∑ uv ∈ Finset.Ico 0 iv, F uv + ∑ uv ∈ Finset.Ico iv (iv + 1), F uv
      + ∑ uv ∈ Finset.Ico (iv + 1) qv, F uv + ∑ uv ∈ Finset.Ico qv (qv + 1), F uv
      + ∑ uv ∈ Finset.Ico (qv + 1) jv, F uv + ∑ uv ∈ Finset.Ico jv (jv + 1), F uv
      + ∑ uv ∈ Finset.Ico (jv + 1) n, F uv = ∑ uv ∈ Finset.Ico 0 n, F uv := by
    rw [Finset.sum_Ico_consecutive F (Nat.zero_le iv) (by omega : iv ≤ iv + 1),
      Finset.sum_Ico_consecutive F (Nat.zero_le (iv + 1)) (by omega : iv + 1 ≤ qv),
      Finset.sum_Ico_consecutive F (Nat.zero_le qv) (by omega : qv ≤ qv + 1),
      Finset.sum_Ico_consecutive F (Nat.zero_le (qv + 1)) (by omega : qv + 1 ≤ jv),
      Finset.sum_Ico_consecutive F (Nat.zero_le jv) (by omega : jv ≤ jv + 1),
      Finset.sum_Ico_consecutive F (Nat.zero_le (jv + 1)) (by omega : jv + 1 ≤ n)]
  have htotal : ∑ uv ∈ Finset.Ico 0 n, F uv = ∑ u : Fin n, f u := by
    rw [← Finset.range_eq_Ico, ← Fin.sum_univ_eq_sum_range F n]
    exact Finset.sum_congr rfl fun u _ ↦ hval u.val u.isLt
  have hmid5 : a + (qv - (iv + 1)) * b + c + (jv - (qv + 1)) * d + g
      ≤ ∑ uv ∈ Finset.Ico iv (iv + 1), F uv + ∑ uv ∈ Finset.Ico (iv + 1) qv, F uv
        + ∑ uv ∈ Finset.Ico qv (qv + 1), F uv + ∑ uv ∈ Finset.Ico (qv + 1) jv, F uv
        + ∑ uv ∈ Finset.Ico jv (jv + 1), F uv :=
    Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add eI e1) eQ) e2) eJ
  have hdrop : ∑ uv ∈ Finset.Ico iv (iv + 1), F uv + ∑ uv ∈ Finset.Ico (iv + 1) qv, F uv
      + ∑ uv ∈ Finset.Ico qv (qv + 1), F uv + ∑ uv ∈ Finset.Ico (qv + 1) jv, F uv
      + ∑ uv ∈ Finset.Ico jv (jv + 1), F uv ≤ ∑ uv ∈ Finset.Ico 0 n, F uv := by
    omega
  exact hmid5.trans (hdrop.trans htotal.le)

/-! ## The per-side walk bounds -/

/-- **The `ℓ_e` walk bound**: every cut position pays at least `3d + 2`, plus
one more when both endpoints are on the right — matching the forward
placement of `ℓ_e` exactly. -/
private theorem cut_sum_left_ge (hsp : SpreadEdges n G) (e : EdgePair n G)
    (χ : Fin n → Bool) (t : ℕ) :
    3 * e.span + 2 + (if χ e.i || χ e.j then 0 else 1)
      ≤ ∑ u : Fin n, ∑ x : Letter,
          (if superHeight χ u x < t then edgeVerdict e Side.left u x - 1
            else 2 - edgeVerdict e Side.left u x) := by
  obtain ⟨hiq, hqj, hmid⟩ := hsp e
  have hjn := e.j.isLt
  have hspan := e.span_def
  rcases le_or_gt t (6 * e.i.val) with c1 | c1
  · -- the cut is above gadget `i`: everything from `i` on is fully below
    have hscan := sum_fin_scan_ge (f := fun u ↦ ∑ x : Letter,
        (if superHeight χ u x < t then edgeVerdict e Side.left u x - 1
          else 2 - edgeVerdict e Side.left u x)) 1 0 3 6 5 hiq hqj hjn
      (fun u hu ↦ by
        obtain rfl : u = e.i := Fin.ext hu
        exact (w_i_left_below hsp χ (by omega)).ge)
      (fun u h1 h2 ↦ Nat.zero_le _)
      (fun u hu ↦ by
        obtain rfl : u = e.mid := Fin.ext hu
        exact (w_q_below hsp Side.left χ (by omega)).ge)
      (fun u h1 h2 ↦ (w_mid2_below hsp h1 h2 Side.left χ (by omega)).ge)
      (fun u hu ↦ by
        obtain rfl : u = e.j := Fin.ext hu
        exact (w_j_left_below hsp χ (by omega)).ge)
    have hite : (if χ e.i || χ e.j then 0 else 1) ≤ 1 := by
      split <;> omega
    omega
  rcases lt_or_ge t (6 * (e.i.val + 1)) with c2 | c2
  · -- the cut splits gadget `i`
    have hscan := sum_fin_scan_ge (f := fun u ↦ ∑ x : Letter,
        (if superHeight χ u x < t then edgeVerdict e Side.left u x - 1
          else 2 - edgeVerdict e Side.left u x))
      (if χ e.i then 0 else 1) 0 3 6 5 hiq hqj hjn
      (fun u hu ↦ by
        obtain rfl : u = e.i := Fin.ext hu
        exact w_i_left_partial hsp χ (by omega) (by omega))
      (fun u h1 h2 ↦ Nat.zero_le _)
      (fun u hu ↦ by
        obtain rfl : u = e.mid := Fin.ext hu
        exact (w_q_below hsp Side.left χ (by omega)).ge)
      (fun u h1 h2 ↦ (w_mid2_below hsp h1 h2 Side.left χ (by omega)).ge)
      (fun u hu ↦ by
        obtain rfl : u = e.j := Fin.ext hu
        exact (w_j_left_below hsp χ (by omega)).ge)
    have hite : (if χ e.i || χ e.j then 0 else 1) ≤ (if χ e.i then 0 else 1) := by
      cases χ e.i <;> cases χ e.j <;> simp
    omega
  rcases le_or_gt t (6 * e.mid.val) with c3 | c3
  · -- the cut is strictly between gadgets `i` and `q`
    have hscan := sum_fin_scan_ge (f := fun u ↦ ∑ x : Letter,
        (if superHeight χ u x < t then edgeVerdict e Side.left u x - 1
          else 2 - edgeVerdict e Side.left u x)) 5 0 3 6 5 hiq hqj hjn
      (fun u hu ↦ by
        obtain rfl : u = e.i := Fin.ext hu
        exact (w_i_left_above hsp χ (by omega)).ge)
      (fun u h1 h2 ↦ Nat.zero_le _)
      (fun u hu ↦ by
        obtain rfl : u = e.mid := Fin.ext hu
        exact (w_q_below hsp Side.left χ (by omega)).ge)
      (fun u h1 h2 ↦ (w_mid2_below hsp h1 h2 Side.left χ (by omega)).ge)
      (fun u hu ↦ by
        obtain rfl : u = e.j := Fin.ext hu
        exact (w_j_left_below hsp χ (by omega)).ge)
    have hite : (if χ e.i || χ e.j then 0 else 1) ≤ 1 := by
      split <;> omega
    omega
  rcases lt_or_ge t (6 * (e.mid.val + 1)) with c4 | c4
  · -- the cut splits gadget `q`: enough slack to drop the partial term
    have hscan := sum_fin_scan_ge (f := fun u ↦ ∑ x : Letter,
        (if superHeight χ u x < t then edgeVerdict e Side.left u x - 1
          else 2 - edgeVerdict e Side.left u x)) 5 6 0 6 5 hiq hqj hjn
      (fun u hu ↦ by
        obtain rfl : u = e.i := Fin.ext hu
        exact (w_i_left_above hsp χ (by omega)).ge)
      (fun u h1 h2 ↦ (w_mid1_above hsp h1 h2 Side.left χ (by omega)).ge)
      (fun u hu ↦ Nat.zero_le _)
      (fun u h1 h2 ↦ (w_mid2_below hsp h1 h2 Side.left χ (by omega)).ge)
      (fun u hu ↦ by
        obtain rfl : u = e.j := Fin.ext hu
        exact (w_j_left_below hsp χ (by omega)).ge)
    have hite : (if χ e.i || χ e.j then 0 else 1) ≤ 1 := by
      split <;> omega
    omega
  rcases le_or_gt t (6 * e.j.val) with c5 | c5
  · -- the cut is strictly between gadgets `q` and `j`
    have hscan := sum_fin_scan_ge (f := fun u ↦ ∑ x : Letter,
        (if superHeight χ u x < t then edgeVerdict e Side.left u x - 1
          else 2 - edgeVerdict e Side.left u x)) 5 6 3 0 5 hiq hqj hjn
      (fun u hu ↦ by
        obtain rfl : u = e.i := Fin.ext hu
        exact (w_i_left_above hsp χ (by omega)).ge)
      (fun u h1 h2 ↦ (w_mid1_above hsp h1 h2 Side.left χ (by omega)).ge)
      (fun u hu ↦ by
        obtain rfl : u = e.mid := Fin.ext hu
        exact (w_q_above hsp Side.left χ (by omega)).ge)
      (fun u h1 h2 ↦ Nat.zero_le _)
      (fun u hu ↦ by
        obtain rfl : u = e.j := Fin.ext hu
        exact (w_j_left_below hsp χ (by omega)).ge)
    have hite : (if χ e.i || χ e.j then 0 else 1) ≤ 1 := by
      split <;> omega
    omega
  rcases lt_or_ge t (6 * (e.j.val + 1)) with c6 | c6
  · -- the cut splits gadget `j`
    have hscan := sum_fin_scan_ge (f := fun u ↦ ∑ x : Letter,
        (if superHeight χ u x < t then edgeVerdict e Side.left u x - 1
          else 2 - edgeVerdict e Side.left u x)) 5 6 3 0
      (if χ e.j then 0 else 1) hiq hqj hjn
      (fun u hu ↦ by
        obtain rfl : u = e.i := Fin.ext hu
        exact (w_i_left_above hsp χ (by omega)).ge)
      (fun u h1 h2 ↦ (w_mid1_above hsp h1 h2 Side.left χ (by omega)).ge)
      (fun u hu ↦ by
        obtain rfl : u = e.mid := Fin.ext hu
        exact (w_q_above hsp Side.left χ (by omega)).ge)
      (fun u h1 h2 ↦ Nat.zero_le _)
      (fun u hu ↦ by
        obtain rfl : u = e.j := Fin.ext hu
        exact w_j_left_partial hsp χ (by omega) (by omega))
    have hite : (if χ e.i || χ e.j then 0 else 1) ≤ (if χ e.j then 0 else 1) := by
      cases χ e.i <;> cases χ e.j <;> simp
    omega
  · -- the cut is below gadget `j`: everything up to `j` is fully above
    have hscan := sum_fin_scan_ge (f := fun u ↦ ∑ x : Letter,
        (if superHeight χ u x < t then edgeVerdict e Side.left u x - 1
          else 2 - edgeVerdict e Side.left u x)) 5 6 3 0 1 hiq hqj hjn
      (fun u hu ↦ by
        obtain rfl : u = e.i := Fin.ext hu
        exact (w_i_left_above hsp χ (by omega)).ge)
      (fun u h1 h2 ↦ (w_mid1_above hsp h1 h2 Side.left χ (by omega)).ge)
      (fun u hu ↦ by
        obtain rfl : u = e.mid := Fin.ext hu
        exact (w_q_above hsp Side.left χ (by omega)).ge)
      (fun u h1 h2 ↦ Nat.zero_le _)
      (fun u hu ↦ by
        obtain rfl : u = e.j := Fin.ext hu
        exact (w_j_left_above hsp χ (by omega)).ge)
    have hite : (if χ e.i || χ e.j then 0 else 1) ≤ 1 := by
      split <;> omega
    omega

/-- **The `r_e` walk bound**: every cut position pays at least `3d`, plus one
more when both endpoints are on the left — matching the forward placement of
`r_e` exactly. The midpoint case is where long edges are needed: `span ≥ 3`
(the bound is false for `span = 2`). -/
private theorem cut_sum_right_ge (hsp : SpreadEdges n G) (e : EdgePair n G)
    (hlong : e.i.val + 3 ≤ e.j.val) (χ : Fin n → Bool) (t : ℕ) :
    3 * e.span + (if χ e.i && χ e.j then 1 else 0)
      ≤ ∑ u : Fin n, ∑ x : Letter,
          (if superHeight χ u x < t then edgeVerdict e Side.right u x - 1
            else 2 - edgeVerdict e Side.right u x) := by
  obtain ⟨hiq, hqj, hmid⟩ := hsp e
  have hjn := e.j.isLt
  have hspan := e.span_def
  rcases le_or_gt t (6 * e.i.val) with c1 | c1
  · have hscan := sum_fin_scan_ge (f := fun u ↦ ∑ x : Letter,
        (if superHeight χ u x < t then edgeVerdict e Side.right u x - 1
          else 2 - edgeVerdict e Side.right u x)) 4 0 3 6 2 hiq hqj hjn
      (fun u hu ↦ by
        obtain rfl : u = e.i := Fin.ext hu
        exact (w_i_right_below hsp χ (by omega)).ge)
      (fun u h1 h2 ↦ Nat.zero_le _)
      (fun u hu ↦ by
        obtain rfl : u = e.mid := Fin.ext hu
        exact (w_q_below hsp Side.right χ (by omega)).ge)
      (fun u h1 h2 ↦ (w_mid2_below hsp h1 h2 Side.right χ (by omega)).ge)
      (fun u hu ↦ by
        obtain rfl : u = e.j := Fin.ext hu
        exact (w_j_right_below hsp χ (by omega)).ge)
    have hite : (if χ e.i && χ e.j then 1 else 0) ≤ 1 := by
      split <;> omega
    omega
  rcases lt_or_ge t (6 * (e.i.val + 1)) with c2 | c2
  · have hscan := sum_fin_scan_ge (f := fun u ↦ ∑ x : Letter,
        (if superHeight χ u x < t then edgeVerdict e Side.right u x - 1
          else 2 - edgeVerdict e Side.right u x))
      (if χ e.i then 2 else 1) 0 3 6 2 hiq hqj hjn
      (fun u hu ↦ by
        obtain rfl : u = e.i := Fin.ext hu
        exact w_i_right_partial hsp χ (by omega) (by omega))
      (fun u h1 h2 ↦ Nat.zero_le _)
      (fun u hu ↦ by
        obtain rfl : u = e.mid := Fin.ext hu
        exact (w_q_below hsp Side.right χ (by omega)).ge)
      (fun u h1 h2 ↦ (w_mid2_below hsp h1 h2 Side.right χ (by omega)).ge)
      (fun u hu ↦ by
        obtain rfl : u = e.j := Fin.ext hu
        exact (w_j_right_below hsp χ (by omega)).ge)
    have hite : (if χ e.i && χ e.j then 1 else 0) + 1 ≤ (if χ e.i then 2 else 1) := by
      cases χ e.i <;> cases χ e.j <;> simp
    omega
  rcases le_or_gt t (6 * e.mid.val) with c3 | c3
  · have hscan := sum_fin_scan_ge (f := fun u ↦ ∑ x : Letter,
        (if superHeight χ u x < t then edgeVerdict e Side.right u x - 1
          else 2 - edgeVerdict e Side.right u x)) 2 0 3 6 2 hiq hqj hjn
      (fun u hu ↦ by
        obtain rfl : u = e.i := Fin.ext hu
        exact (w_i_right_above hsp χ (by omega)).ge)
      (fun u h1 h2 ↦ Nat.zero_le _)
      (fun u hu ↦ by
        obtain rfl : u = e.mid := Fin.ext hu
        exact (w_q_below hsp Side.right χ (by omega)).ge)
      (fun u h1 h2 ↦ (w_mid2_below hsp h1 h2 Side.right χ (by omega)).ge)
      (fun u hu ↦ by
        obtain rfl : u = e.j := Fin.ext hu
        exact (w_j_right_below hsp χ (by omega)).ge)
    have hite : (if χ e.i && χ e.j then 1 else 0) ≤ 1 := by
      split <;> omega
    omega
  rcases lt_or_ge t (6 * (e.mid.val + 1)) with c4 | c4
  · -- the midpoint split: the long-edge case
    have hscan := sum_fin_scan_ge (f := fun u ↦ ∑ x : Letter,
        (if superHeight χ u x < t then edgeVerdict e Side.right u x - 1
          else 2 - edgeVerdict e Side.right u x)) 2 6 0 6 2 hiq hqj hjn
      (fun u hu ↦ by
        obtain rfl : u = e.i := Fin.ext hu
        exact (w_i_right_above hsp χ (by omega)).ge)
      (fun u h1 h2 ↦ (w_mid1_above hsp h1 h2 Side.right χ (by omega)).ge)
      (fun u hu ↦ Nat.zero_le _)
      (fun u h1 h2 ↦ (w_mid2_below hsp h1 h2 Side.right χ (by omega)).ge)
      (fun u hu ↦ by
        obtain rfl : u = e.j := Fin.ext hu
        exact (w_j_right_below hsp χ (by omega)).ge)
    have hite : (if χ e.i && χ e.j then 1 else 0) ≤ 1 := by
      split <;> omega
    omega
  rcases le_or_gt t (6 * e.j.val) with c5 | c5
  · have hscan := sum_fin_scan_ge (f := fun u ↦ ∑ x : Letter,
        (if superHeight χ u x < t then edgeVerdict e Side.right u x - 1
          else 2 - edgeVerdict e Side.right u x)) 2 6 3 0 2 hiq hqj hjn
      (fun u hu ↦ by
        obtain rfl : u = e.i := Fin.ext hu
        exact (w_i_right_above hsp χ (by omega)).ge)
      (fun u h1 h2 ↦ (w_mid1_above hsp h1 h2 Side.right χ (by omega)).ge)
      (fun u hu ↦ by
        obtain rfl : u = e.mid := Fin.ext hu
        exact (w_q_above hsp Side.right χ (by omega)).ge)
      (fun u h1 h2 ↦ Nat.zero_le _)
      (fun u hu ↦ by
        obtain rfl : u = e.j := Fin.ext hu
        exact (w_j_right_below hsp χ (by omega)).ge)
    have hite : (if χ e.i && χ e.j then 1 else 0) ≤ 1 := by
      split <;> omega
    omega
  rcases lt_or_ge t (6 * (e.j.val + 1)) with c6 | c6
  · have hscan := sum_fin_scan_ge (f := fun u ↦ ∑ x : Letter,
        (if superHeight χ u x < t then edgeVerdict e Side.right u x - 1
          else 2 - edgeVerdict e Side.right u x)) 2 6 3 0
      (if χ e.j then 2 else 1) hiq hqj hjn
      (fun u hu ↦ by
        obtain rfl : u = e.i := Fin.ext hu
        exact (w_i_right_above hsp χ (by omega)).ge)
      (fun u h1 h2 ↦ (w_mid1_above hsp h1 h2 Side.right χ (by omega)).ge)
      (fun u hu ↦ by
        obtain rfl : u = e.mid := Fin.ext hu
        exact (w_q_above hsp Side.right χ (by omega)).ge)
      (fun u h1 h2 ↦ Nat.zero_le _)
      (fun u hu ↦ by
        obtain rfl : u = e.j := Fin.ext hu
        exact w_j_right_partial hsp χ (by omega) (by omega))
    have hite : (if χ e.i && χ e.j then 1 else 0) + 1 ≤ (if χ e.j then 2 else 1) := by
      cases χ e.i <;> cases χ e.j <;> simp
    omega
  · have hscan := sum_fin_scan_ge (f := fun u ↦ ∑ x : Letter,
        (if superHeight χ u x < t then edgeVerdict e Side.right u x - 1
          else 2 - edgeVerdict e Side.right u x)) 2 6 3 0 4 hiq hqj hjn
      (fun u hu ↦ by
        obtain rfl : u = e.i := Fin.ext hu
        exact (w_i_right_above hsp χ (by omega)).ge)
      (fun u h1 h2 ↦ (w_mid1_above hsp h1 h2 Side.right χ (by omega)).ge)
      (fun u hu ↦ by
        obtain rfl : u = e.mid := Fin.ext hu
        exact (w_q_above hsp Side.right χ (by omega)).ge)
      (fun u h1 h2 ↦ Nat.zero_le _)
      (fun u hu ↦ by
        obtain rfl : u = e.j := Fin.ext hu
        exact (w_j_right_above hsp χ (by omega)).ge)
    have hite : (if χ e.i && χ e.j then 1 else 0) ≤ 1 := by
      split <;> omega
    omega

/-! ## The per-edge lower bound -/

/-- **The per-edge cost of the reverse direction**: on a block ranking whose
vertex part agrees with the output spec of `χ`, the two candidates of an edge
cost at least `M (6·span e + 2)` against the vertex block — plus `M` more
when `χ` leaves the edge uncut. The exact mirror of the forward direction's
`sum_orientedMargin_out_ve`, as a lower bound over *all* block rankings. -/
theorem sum_orientedMargin_ve_ge (hsp : SpreadEdges n G)
    {r : LinearOrder (Cand n M G)} (hb : ∀ u x, BlockAt r u x)
    {χ : Fin n → Bool} (hva : VertexAgree r χ) (e : EdgePair n G)
    (hlong : e.i.val + 3 ≤ e.j.val) :
    M * (6 * e.span + 2 + (if χ e.i = χ e.j then 1 else 0))
      ≤ ∑ s : Side, ∑ u : Fin n, ∑ x : Letter, ∑ m : Fin M,
          (orientedMargin (kemenyProfile n G M) r (Sum.inl (u, x, m)) (Sum.inr (e, s))
            + orientedMargin (kemenyProfile n G M) r (Sum.inr (e, s)) (Sum.inl (u, x, m))) := by
  obtain ⟨tl, -, hl⟩ := exists_sum_ve_cost_eq_cut hsp hb hva e Side.left
  obtain ⟨tr, -, hr⟩ := exists_sum_ve_cost_eq_cut hsp hb hva e Side.right
  rw [show (Finset.univ : Finset Side) = {Side.left, Side.right} from by decide,
    Finset.sum_insert (by decide), Finset.sum_singleton, hl, hr]
  have h1 := cut_sum_left_ge hsp e χ tl
  have h2 := cut_sum_right_ge hsp e hlong χ tr
  have hsum : 6 * e.span + 2 + (if χ e.i = χ e.j then 1 else 0)
      = (3 * e.span + 2 + (if χ e.i || χ e.j then 0 else 1))
        + (3 * e.span + (if χ e.i && χ e.j then 1 else 0)) := by
    cases hb1 : χ e.i <;> cases hb2 : χ e.j <;>
      simp only [Bool.true_or, Bool.false_or, Bool.true_and, Bool.false_and,
        Bool.false_eq_true, Bool.true_eq_false, if_true, if_false] <;>
      omega
  rw [hsum, mul_add]
  exact Nat.add_le_add (Nat.mul_le_mul_left _ h1) (Nat.mul_le_mul_left _ h2)

end Hardness
