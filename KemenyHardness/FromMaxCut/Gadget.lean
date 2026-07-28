import Mathlib.Data.List.FinRange
import KemenyHardness.FromMaxCut.Forward

/-!
# The gadget classification

The finite heart of the reverse direction: **every linear order of the six
letters is wrong on at least three arcs of the gadget tournament, with
equality exactly for `ABCDEF` and `DAEBFC`** — the two orders the output
ranking of the forward direction uses. The paper proves this by exhibiting
two arc-disjoint triangle packings and analysing an incidence 6-cycle; here
the entire claim is a kernel-checked enumeration of the `720` orders, and the
packing argument survives only as the *reason* the enumeration comes out this
way.

An order of the letters is carried as a position function `Letter → ℕ` that is
injective with values below `6` — on a six-element domain that is exactly a
bijection onto `{0, …, 5}`. Its cost is `wrongArcCost`, the total margin the
profile charges for the within-gadget arcs the order ranks against the 2-of-3
majority (`beats`). The classification is stated over `Letter → ℕ` rather than
over `Letter → Fin 6` *on purpose*: its consumer's position function is
`gadgetRank`, already `ℕ`-valued, and a `Fin 6`-valued statement would make
every use site an `isDefEq` through `wrongArcCost`'s unfolded `Finset.sum`
(12s a call — see `STYLE.md`). Enumerating the `6⁶` functions through the `Decidable`
framework is infeasible (the `Fintype` instance on the function space blows
up both elaborator and kernel), so the check is phrased as a `Bool`-valued
fold over `List.finRange` with a `List`-computable cost (`decide +kernel`
reduces it in about twenty seconds), and the two classification theorems
(`three_le_wrongArcCost`, `wrongArcCost_eq_three_cases`) recover the
`Prop`-level statements by symbolic glue.
-/

namespace Hardness

open Finset

/-! ## The wrong-arc cost of a letter order -/

/-- The margin cost the profile charges within one gadget whose letters are
ordered by the position function `f`: over each ordered pair placed
`x`-above-`x'`, the (truncated) majority margin against that orientation.
Since all within-gadget margins are ±1, this counts the arcs of the gadget
tournament that `f` ranks against the majority. -/
def wrongArcCost (f : Letter → ℕ) : ℕ :=
  ∑ x : Letter, ∑ x' : Letter, if f x < f x' then beats x' x - beats x x' else 0

/-! ## The kernel-checkable form -/

private def letterList : List Letter := [.A, .B, .C, .D, .E, .F]

private theorem mem_letterList (x : Letter) : x ∈ letterList := by
  cases x <;> decide

/-- `wrongArcCost` as a bare `List` computation — no `Finset`/`Multiset`
machinery, so the kernel can evaluate it fast. -/
private def wrongArcCostL (f : Letter → ℕ) : ℕ :=
  (letterList.map fun x ↦
    (letterList.map fun y ↦ if f x < f y then beats y x - beats x y else 0).sum).sum

private theorem wrongArcCost_eq_list (f : Letter → ℕ) :
    wrongArcCost f = wrongArcCostL f := by
  simp only [wrongArcCost, sum_letter, wrongArcCostL, letterList, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil]
  omega

/-- A position function from six values. -/
private def mkPos (a b c d e f : Fin 6) : Letter → ℕ
  | .A => a | .B => b | .C => c | .D => d | .E => e | .F => f

private def distinct6 (a b c d e f : Fin 6) : Bool :=
  a != b && a != c && a != d && a != e && a != f &&
  b != c && b != d && b != e && b != f &&
  c != d && c != e && c != f &&
  d != e && d != f && e != f

/-- The leaf check: an injective order has cost at least `3`, and cost
exactly `3` only for the positions `ABCDEF` (`outPosL`) or `DAEBFC`
(`outPosR`). -/
private def checkOne (a b c d e f : Fin 6) : Bool :=
  !distinct6 a b c d e f ||
    (Nat.ble 3 (wrongArcCostL (mkPos a b c d e f)) &&
      (wrongArcCostL (mkPos a b c d e f) != 3 ||
        letterList.all (fun x ↦ mkPos a b c d e f x == outPosL x) ||
        letterList.all (fun x ↦ mkPos a b c d e f x == outPosR x)))

private def checkAll : Bool :=
  (List.finRange 6).all fun a ↦ (List.finRange 6).all fun b ↦
    (List.finRange 6).all fun c ↦ (List.finRange 6).all fun d ↦
      (List.finRange 6).all fun e ↦ (List.finRange 6).all fun f ↦
        checkOne a b c d e f

/-- **The enumeration** — the paper's two-triangle-packings argument, as a
kernel computation over the `6⁶` position tuples (~20s; the elaborator's
evaluator cannot do it, hence `+kernel`). -/
private theorem checkAll_true : checkAll = true := by decide +kernel

private theorem checkOne_true (a b c d e f : Fin 6) : checkOne a b c d e f = true := by
  have h := checkAll_true
  rw [checkAll] at h
  simp only [List.all_eq_true] at h
  exact h a (List.mem_finRange a) b (List.mem_finRange b) c (List.mem_finRange c)
    d (List.mem_finRange d) e (List.mem_finRange e) f (List.mem_finRange f)

/-! ## The classification -/

section Classification

variable {f : Letter → ℕ}

/-- The `Fin 6` repackaging of a bounded position function — the shape the
enumeration is phrased in, kept out of the classification's *statement*. -/
private def toFin6 (hlt : ∀ x, f x < 6) (x : Letter) : Fin 6 := ⟨f x, hlt x⟩

private theorem mkPos_eval (hlt : ∀ x, f x < 6) :
    mkPos (toFin6 hlt .A) (toFin6 hlt .B) (toFin6 hlt .C) (toFin6 hlt .D)
      (toFin6 hlt .E) (toFin6 hlt .F) = f := by
  funext x
  cases x <;> rfl

private theorem distinct6_of_injective (hinj : Function.Injective f)
    (hlt : ∀ x, f x < 6) :
    distinct6 (toFin6 hlt .A) (toFin6 hlt .B) (toFin6 hlt .C) (toFin6 hlt .D)
      (toFin6 hlt .E) (toFin6 hlt .F) = true := by
  have hne : ∀ x y : Letter, x ≠ y → toFin6 hlt x ≠ toFin6 hlt y :=
    fun x y hxy hc ↦ hxy (hinj (congrArg Fin.val hc))
  simp only [distinct6, Bool.and_eq_true, bne_iff_ne, ne_eq]
  repeat' apply And.intro
  all_goals exact hne _ _ (by decide)

private theorem checkOne_unfold (hinj : Function.Injective f) (hlt : ∀ x, f x < 6) :
    3 ≤ wrongArcCostL f
      ∧ (wrongArcCostL f ≠ 3
          ∨ (∀ x, f x = outPosL x) ∨ (∀ x, f x = outPosR x)) := by
  have hone := checkOne_true (toFin6 hlt .A) (toFin6 hlt .B) (toFin6 hlt .C)
    (toFin6 hlt .D) (toFin6 hlt .E) (toFin6 hlt .F)
  rw [checkOne, distinct6_of_injective hinj hlt, mkPos_eval hlt] at hone
  simp only [Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true,
    bne_iff_ne, ne_eq, List.all_eq_true, beq_iff_eq] at hone
  refine ⟨Nat.le_of_ble_eq_true hone.1, ?_⟩
  rcases hone.2 with (h | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl fun x ↦ h x (mem_letterList x))
  · exact Or.inr (Or.inr fun x ↦ h x (mem_letterList x))

/-- **Every injective letter order is wrong on at least three arcs.** -/
theorem three_le_wrongArcCost (hinj : Function.Injective f) (hlt : ∀ x, f x < 6) :
    3 ≤ wrongArcCost f := by
  rw [wrongArcCost_eq_list]
  exact (checkOne_unfold hinj hlt).1

/-- **The two optimal orders**: an injective letter order wrong on exactly
three arcs is `ABCDEF` or `DAEBFC`. -/
theorem wrongArcCost_eq_three_cases (hinj : Function.Injective f)
    (hlt : ∀ x, f x < 6) (h3 : wrongArcCost f = 3) :
    (∀ x, f x = outPosL x) ∨ (∀ x, f x = outPosR x) := by
  rw [wrongArcCost_eq_list] at h3
  rcases (checkOne_unfold hinj hlt).2 with h | h
  · exact absurd h3 h
  · exact h

/-- **The side bit of an optimal order** — `wrongArcCost_eq_three_cases`
packaged as the colouring value the rigidity argument reads off a gadget, in
the `if · then outPosL else outPosR` shape of `outSpec`'s `localPos`. -/
theorem exists_side_of_wrongArcCost_eq_three (hinj : Function.Injective f)
    (hlt : ∀ x, f x < 6) (h3 : wrongArcCost f = 3) :
    ∃ b : Bool, ∀ x, f x = (if b then outPosL else outPosR) x := by
  rcases wrongArcCost_eq_three_cases hinj hlt h3 with h | h
  · exact ⟨true, h⟩
  · exact ⟨false, h⟩

end Classification

end Hardness
