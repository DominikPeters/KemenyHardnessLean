import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Seven-range scans over `Fin n`

The interval bookkeeping of the edge-candidate cost analysis, once and for all.
Both directions of the reduction sum a quantity over the gadgets `Fin n` that is
piecewise constant on the seven ranges cut by an edge's endpoints `i < q < j` —
before `i`, at `i`, strictly between `i` and `q`, at `q`, strictly between `q`
and `j`, at `j`, after `j` — and both need the telescoped value of that sum:

* `sum_fin_scan` — the forward direction's *exact* scan, where the two outer
  ranges vanish and the five inner pieces have known values;
* `sum_fin_scan_ge` — the reverse direction's *lower bound*, where the two outer
  ranges are simply dropped and the five inner pieces are bounded below.

Both are the same split of `Finset.range n` into seven consecutive `Ico`s
(`sum_fin_split`), taken through the extension-by-zero `finExt` that turns a
`Fin n`-indexed function into an `ℕ`-indexed one — the index type the `Ico`
lemmas want. Nothing here mentions the reduction; the landmarks are three
naturals `iv < qv < jv < n`.
-/

namespace Hardness

variable {n : ℕ}

/-! ## Extension by zero -/

/-- A `Fin n`-indexed function read at an arbitrary natural, `0` out of range —
the `ℕ`-indexed form the `Finset.Ico` lemmas consume. -/
def finExt (f : Fin n → ℕ) (uv : ℕ) : ℕ :=
  if h : uv < n then f ⟨uv, h⟩ else 0

theorem finExt_of_lt (f : Fin n → ℕ) {uv : ℕ} (h : uv < n) : finExt f uv = f ⟨uv, h⟩ :=
  dif_pos h

theorem sum_finExt_range (f : Fin n → ℕ) :
    ∑ uv ∈ Finset.range n, finExt f uv = ∑ u : Fin n, f u := by
  rw [← Fin.sum_univ_eq_sum_range (finExt f) n]
  exact Finset.sum_congr rfl fun u _ ↦ finExt_of_lt f u.isLt

/-! ## The split -/

/-- **The seven-range split**: a sum over `Fin n` cut at the landmarks
`iv < qv < jv`, into the two outer ranges, the three landmark singletons and the
two inner ranges. The one piece of interval arithmetic the two scans share. -/
theorem sum_fin_split (f : Fin n → ℕ) {iv qv jv : ℕ}
    (hiq : iv < qv) (hqj : qv < jv) (hjn : jv < n) :
    ∑ u : Fin n, f u
      = ∑ uv ∈ Finset.Ico 0 iv, finExt f uv
        + ∑ uv ∈ Finset.Ico iv (iv + 1), finExt f uv
        + ∑ uv ∈ Finset.Ico (iv + 1) qv, finExt f uv
        + ∑ uv ∈ Finset.Ico qv (qv + 1), finExt f uv
        + ∑ uv ∈ Finset.Ico (qv + 1) jv, finExt f uv
        + ∑ uv ∈ Finset.Ico jv (jv + 1), finExt f uv
        + ∑ uv ∈ Finset.Ico (jv + 1) n, finExt f uv := by
  have hmerge : ∑ uv ∈ Finset.Ico 0 iv, finExt f uv
        + ∑ uv ∈ Finset.Ico iv (iv + 1), finExt f uv
        + ∑ uv ∈ Finset.Ico (iv + 1) qv, finExt f uv
        + ∑ uv ∈ Finset.Ico qv (qv + 1), finExt f uv
        + ∑ uv ∈ Finset.Ico (qv + 1) jv, finExt f uv
        + ∑ uv ∈ Finset.Ico jv (jv + 1), finExt f uv
        + ∑ uv ∈ Finset.Ico (jv + 1) n, finExt f uv
      = ∑ uv ∈ Finset.Ico 0 n, finExt f uv := by
    rw [Finset.sum_Ico_consecutive (finExt f) (Nat.zero_le iv) (by omega : iv ≤ iv + 1),
      Finset.sum_Ico_consecutive (finExt f) (Nat.zero_le (iv + 1)) (by omega : iv + 1 ≤ qv),
      Finset.sum_Ico_consecutive (finExt f) (Nat.zero_le qv) (by omega : qv ≤ qv + 1),
      Finset.sum_Ico_consecutive (finExt f) (Nat.zero_le (qv + 1)) (by omega : qv + 1 ≤ jv),
      Finset.sum_Ico_consecutive (finExt f) (Nat.zero_le jv) (by omega : jv ≤ jv + 1),
      Finset.sum_Ico_consecutive (finExt f) (Nat.zero_le (jv + 1)) (by omega : jv + 1 ≤ n)]
  rw [hmerge, ← Finset.range_eq_Ico, sum_finExt_range]

/-! ## The two scans -/

/-- **The exact scan**: a function on `Fin n` that vanishes before `iv` and
after `jv` and is constant on the five remaining pieces sums to the telescoped
value. The vertex–edge block of the forward direction. -/
theorem sum_fin_scan {f : Fin n → ℕ} {iv qv jv : ℕ}
    (a b c d g : ℕ) (hiq : iv < qv) (hqj : qv < jv) (hjn : jv < n)
    (h0 : ∀ u : Fin n, u.val < iv → f u = 0)
    (hI : ∀ u : Fin n, u.val = iv → f u = a)
    (h1 : ∀ u : Fin n, iv < u.val → u.val < qv → f u = b)
    (hQ : ∀ u : Fin n, u.val = qv → f u = c)
    (h2 : ∀ u : Fin n, qv < u.val → u.val < jv → f u = d)
    (hJ : ∀ u : Fin n, u.val = jv → f u = g)
    (h3 : ∀ u : Fin n, jv < u.val → f u = 0) :
    ∑ u : Fin n, f u = a + (qv - iv - 1) * b + c + (jv - qv - 1) * d + g := by
  have e0 : ∑ uv ∈ Finset.Ico 0 iv, finExt f uv = 0 :=
    Finset.sum_eq_zero fun uv huv ↦ by
      rw [Finset.mem_Ico] at huv
      rw [finExt_of_lt f (by omega)]
      exact h0 _ huv.2
  have eI : ∑ uv ∈ Finset.Ico iv (iv + 1), finExt f uv = a := by
    rw [Nat.Ico_succ_singleton, Finset.sum_singleton, finExt_of_lt f (by omega : iv < n)]
    exact hI _ rfl
  have e1 : ∑ uv ∈ Finset.Ico (iv + 1) qv, finExt f uv = (qv - iv - 1) * b := by
    have hpt : ∀ uv ∈ Finset.Ico (iv + 1) qv, finExt f uv = b := fun uv huv ↦ by
      rw [Finset.mem_Ico] at huv
      rw [finExt_of_lt f (by omega)]
      exact h1 _ (show iv < uv from by omega) huv.2
    rw [Finset.sum_congr rfl hpt, Finset.sum_const, Nat.card_Ico, smul_eq_mul,
      show qv - (iv + 1) = qv - iv - 1 from by omega]
  have eQ : ∑ uv ∈ Finset.Ico qv (qv + 1), finExt f uv = c := by
    rw [Nat.Ico_succ_singleton, Finset.sum_singleton, finExt_of_lt f (by omega : qv < n)]
    exact hQ _ rfl
  have e2 : ∑ uv ∈ Finset.Ico (qv + 1) jv, finExt f uv = (jv - qv - 1) * d := by
    have hpt : ∀ uv ∈ Finset.Ico (qv + 1) jv, finExt f uv = d := fun uv huv ↦ by
      rw [Finset.mem_Ico] at huv
      rw [finExt_of_lt f (by omega)]
      exact h2 _ (show qv < uv from by omega) huv.2
    rw [Finset.sum_congr rfl hpt, Finset.sum_const, Nat.card_Ico, smul_eq_mul,
      show jv - (qv + 1) = jv - qv - 1 from by omega]
  have eJ : ∑ uv ∈ Finset.Ico jv (jv + 1), finExt f uv = g := by
    rw [Nat.Ico_succ_singleton, Finset.sum_singleton, finExt_of_lt f hjn]
    exact hJ _ rfl
  have e3 : ∑ uv ∈ Finset.Ico (jv + 1) n, finExt f uv = 0 :=
    Finset.sum_eq_zero fun uv huv ↦ by
      rw [Finset.mem_Ico] at huv
      rw [finExt_of_lt f huv.2]
      exact h3 _ (show jv < uv from by omega)
  rw [sum_fin_split f hiq hqj hjn, e0, eI, e1, eQ, e2, eJ, e3]
  omega

/-- **The lower-bound scan**: a sum over `Fin n` dominates the landmark values
at `iv`, `qv`, `jv` plus constants on the two inner ranges; the outer ranges are
dropped. The vertex–edge block of the reverse direction. -/
theorem sum_fin_scan_ge {f : Fin n → ℕ} {iv qv jv : ℕ}
    (a b c d g : ℕ) (hiq : iv < qv) (hqj : qv < jv) (hjn : jv < n)
    (hI : ∀ u : Fin n, u.val = iv → a ≤ f u)
    (h1 : ∀ u : Fin n, iv < u.val → u.val < qv → b ≤ f u)
    (hQ : ∀ u : Fin n, u.val = qv → c ≤ f u)
    (h2 : ∀ u : Fin n, qv < u.val → u.val < jv → d ≤ f u)
    (hJ : ∀ u : Fin n, u.val = jv → g ≤ f u) :
    a + (qv - (iv + 1)) * b + c + (jv - (qv + 1)) * d + g ≤ ∑ u : Fin n, f u := by
  have eI : a ≤ ∑ uv ∈ Finset.Ico iv (iv + 1), finExt f uv := by
    rw [Nat.Ico_succ_singleton, Finset.sum_singleton, finExt_of_lt f (by omega : iv < n)]
    exact hI _ rfl
  have e1 : (qv - (iv + 1)) * b ≤ ∑ uv ∈ Finset.Ico (iv + 1) qv, finExt f uv := by
    calc (qv - (iv + 1)) * b = ∑ _uv ∈ Finset.Ico (iv + 1) qv, b := by
          rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum fun uv huv ↦ by
          rw [Finset.mem_Ico] at huv
          rw [finExt_of_lt f (by omega)]
          exact h1 _ (show iv < uv from by omega) huv.2
  have eQ : c ≤ ∑ uv ∈ Finset.Ico qv (qv + 1), finExt f uv := by
    rw [Nat.Ico_succ_singleton, Finset.sum_singleton, finExt_of_lt f (by omega : qv < n)]
    exact hQ _ rfl
  have e2 : (jv - (qv + 1)) * d ≤ ∑ uv ∈ Finset.Ico (qv + 1) jv, finExt f uv := by
    calc (jv - (qv + 1)) * d = ∑ _uv ∈ Finset.Ico (qv + 1) jv, d := by
          rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum fun uv huv ↦ by
          rw [Finset.mem_Ico] at huv
          rw [finExt_of_lt f (by omega)]
          exact h2 _ (show qv < uv from by omega) huv.2
  have eJ : g ≤ ∑ uv ∈ Finset.Ico jv (jv + 1), finExt f uv := by
    rw [Nat.Ico_succ_singleton, Finset.sum_singleton, finExt_of_lt f hjn]
    exact hJ _ rfl
  rw [sum_fin_split f hiq hqj hjn]
  omega

end Hardness
