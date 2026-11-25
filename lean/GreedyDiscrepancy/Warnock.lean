import GreedyDiscrepancy.Defs

/-!
# Adding one point: the L² discrepancy changes by Kritzinger's objective

`l2sq (x :: xs) = kObj xs x + c xs`, where `c xs` does not depend on `x`.
So minimising the L² discrepancy of the extended set is the same as
minimising `kObj xs`. This justifies Algorithm 2 of Kritzinger.
-/

namespace GreedyDiscrepancy

lemma sum_map_one_sub (xs : List ℝ) (g : ℝ → ℝ) :
    (xs.map fun a => 1 - g a).sum = xs.length - (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons a as ih => simp [ih]; ring

lemma sum_map_add' (xs : List ℝ) (g h : ℝ → ℝ) :
    (xs.map fun a => g a + h a).sum = (xs.map g).sum + (xs.map h).sum := by
  induction xs with
  | nil => simp
  | cons a as ih => simp [ih]; ring

/-- The part of `l2sq (x :: xs)` that does not depend on `x`. -/
noncomputable def l2Const (xs : List ℝ) : ℝ :=
  (xs.map fun a => (xs.map fun b => 1 - max a b).sum).sum + xs.length
    - ((xs.length : ℝ) + 1) * (xs.map fun a => 1 - a ^ 2).sum
    + ((xs.length : ℝ) + 1) ^ 2 / 3

theorem l2sq_cons (xs : List ℝ) (x : ℝ) :
    l2sq (x :: xs) = kObj xs x + l2Const xs := by
  have h1 : (xs.map fun a => (1 - max a x) + (xs.map fun b => 1 - max a b).sum).sum
      = (xs.length - (xs.map fun a => max a x).sum)
        + (xs.map fun a => (xs.map fun b => 1 - max a b).sum).sum := by
    rw [sum_map_add' xs (fun a => 1 - max a x), sum_map_one_sub]
  have h2 : (xs.map fun b => 1 - max x b).sum = xs.length - (xs.map fun a => max a x).sum := by
    rw [sum_map_one_sub]; simp [max_comm]
  simp only [l2sq, kObj, l2Const, List.map_cons, List.sum_cons, List.length_cons, max_self,
    Nat.cast_succ]
  rw [h1, h2]
  ring

/-- Minimising the extended L² discrepancy is equivalent to minimising `kObj`. -/
theorem l2sq_cons_le_iff (xs : List ℝ) (x y : ℝ) :
    l2sq (x :: xs) ≤ l2sq (y :: xs) ↔ kObj xs x ≤ kObj xs y := by
  rw [l2sq_cons, l2sq_cons]; constructor <;> intro h <;> linarith

end GreedyDiscrepancy
