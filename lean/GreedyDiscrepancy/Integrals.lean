import GreedyDiscrepancy.Quadrature
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The closed forms are the integrals they stand for

The library defines the integrated discrepancy `G` and the squared `L²`
discrepancy `l2sq` by closed forms. Here we prove that they are the integrals
of the local discrepancy

  `D xs s = #{a ∈ xs : a < s} − |xs| s`

(counting with `<` or `≤` changes `D` only at finitely many points):

* `G_eq_integral_D`: `G xs t = ∫₀ᵗ D xs s ds` for points in `[0, ∞)` and `t ≥ 0`;
* `l2sq_eq_integral`: `l2sq xs = ∫₀¹ (D xs s)² ds` for points in `[0,1]`
  (Warnock's formula).
-/

open intervalIntegral MeasureTheory Set

namespace GreedyDiscrepancy

/-- Local discrepancy `#{a ∈ xs : a < s} − |xs| s`. -/
noncomputable def D (xs : List ℝ) (s : ℝ) : ℝ := (countBelow xs s : ℝ) - xs.length * s

/-- Indicator of `a < s` as a real number. -/
noncomputable def ind (a s : ℝ) : ℝ := if a < s then 1 else 0

lemma countBelow_cons (a : ℝ) (xs : List ℝ) (s : ℝ) :
    (countBelow (a :: xs) s : ℝ) = ind a s + countBelow xs s := by
  simp only [countBelow, List.countP_cons, ind]
  split_ifs with h <;> simp_all; ring

lemma countBelow_eq_sum (xs : List ℝ) (s : ℝ) :
    (countBelow xs s : ℝ) = (xs.map fun a => ind a s).sum := by
  induction xs with
  | nil => simp [countBelow]
  | cons a as ih => rw [countBelow_cons, ih]; simp

lemma ind_measurable (a : ℝ) : Measurable (ind a) := by
  unfold ind
  exact Measurable.ite (measurableSet_Ioi) measurable_const measurable_const

lemma ind_intervalIntegrable (a u v : ℝ) : IntervalIntegrable (ind a) volume u v := by
  refine (intervalIntegrable_iff).2 ?_
  refine Integrable.mono' (g := fun _ => (1:ℝ)) ?_ (ind_measurable a).aestronglyMeasurable ?_
  · exact integrableOn_const (by simp [Real.volume_uIoc] ) |>.integrable
  · refine Filter.Eventually.of_forall fun s => ?_
    unfold ind; split_ifs <;> simp

/-- `∫₀ᵗ 1[a < s] ds = (t − a)₊` for `0 ≤ a` and `0 ≤ t`. -/
lemma integral_ind (a t : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t) :
    ∫ s in (0:ℝ)..t, ind a s = max (t - a) 0 := by
  rcases le_total t a with hta | hat
  · rw [max_eq_right (by linarith)]
    rw [integral_congr (g := fun _ => (0:ℝ))]
    · simp
    · intro s hs
      rw [uIcc_of_le ht] at hs
      simp [ind, not_lt.2 (hs.2.trans hta)]
  · rw [max_eq_left (by linarith),
      ← integral_add_adjacent_intervals (ind_intervalIntegrable a 0 a)
        (ind_intervalIntegrable a a t)]
    have h0 : ∫ s in (0:ℝ)..a, ind a s = 0 := by
      rw [integral_congr (g := fun _ => (0:ℝ))]
      · simp
      · intro s hs
        rw [uIcc_of_le ha] at hs
        simp [ind, not_lt.2 hs.2]
    have h1 : ∫ s in a..t, ind a s = ∫ s in a..t, (1:ℝ) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun s hs => ?_)
      rw [uIoc_of_le hat] at hs
      simp [ind, hs.1]
    rw [h0, h1]; simp

lemma intervalIntegrable_list_sum (xs : List ℝ) (f : ℝ → ℝ → ℝ) (u v : ℝ)
    (hf : ∀ a ∈ xs, IntervalIntegrable (f a) volume u v) :
    IntervalIntegrable (fun s => (xs.map fun a => f a s).sum) volume u v := by
  induction xs with
  | nil => simp
  | cons b bs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hf b (by simp)).add (ih fun a ha => hf a (by simp [ha]))

lemma integral_list_sum (xs : List ℝ) (f : ℝ → ℝ → ℝ) (u v : ℝ)
    (hf : ∀ a ∈ xs, IntervalIntegrable (f a) volume u v) :
    ∫ s in u..v, (xs.map fun a => f a s).sum = (xs.map fun a => ∫ s in u..v, f a s).sum := by
  induction xs with
  | nil => simp
  | cons b bs ih =>
    have hbs : ∀ a ∈ bs, IntervalIntegrable (f a) volume u v :=
      fun a ha => hf a (by simp [ha])
    simp only [List.map_cons, List.sum_cons]
    rw [integral_add (hf b (by simp)) (intervalIntegrable_list_sum bs f u v hbs), ih hbs]

/-- **`G` is the integrated discrepancy**: `G xs t = ∫₀ᵗ D xs s ds`. -/
theorem G_eq_integral_D (xs : List ℝ) (hxs : ∀ a ∈ xs, 0 ≤ a) (t : ℝ) (ht : 0 ≤ t) :
    G xs t = ∫ s in (0:ℝ)..t, D xs s := by
  have hcount : ∀ s, (countBelow xs s : ℝ) = (xs.map fun a => ind a s).sum :=
    countBelow_eq_sum xs
  have hI : IntervalIntegrable (fun s => (xs.map fun a => ind a s).sum) volume 0 t :=
    intervalIntegrable_list_sum xs ind 0 t fun a _ => ind_intervalIntegrable a 0 t
  unfold D
  simp_rw [hcount]
  have hlin : IntervalIntegrable (fun s : ℝ => (xs.length : ℝ) * s) volume 0 t :=
    (continuous_const.mul continuous_id).intervalIntegrable 0 t
  rw [integral_sub hI hlin, integral_list_sum xs ind 0 t
    (fun a _ => ind_intervalIntegrable a 0 t)]
  rw [intervalIntegral.integral_const_mul, integral_id]
  unfold G
  congr 1
  · congr 1
    apply List.map_congr_left
    intro a ha
    exact (integral_ind a t (hxs a ha) ht).symm
  · ring

lemma ind_mul (a b s : ℝ) : ind a s * ind b s = ind (max a b) s := by
  unfold ind
  by_cases h1 : a < s <;> by_cases h2 : b < s <;> simp [h1, h2]

lemma sq_sum_ind (xs : List ℝ) (s : ℝ) :
    ((xs.map fun a => ind a s).sum) ^ 2
      = (xs.map fun a => (xs.map fun b => ind (max a b) s).sum).sum := by
  rw [sq, ← List.sum_map_mul_right]
  congr 1
  apply List.map_congr_left
  intro a _
  rw [← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro b _
  exact ind_mul a b s

/-- `∫₀¹ s · 1[a < s] ds = (1 − a²)/2` for `a ∈ [0,1]`. -/
lemma integral_mul_ind (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∫ s in (0:ℝ)..1, s * ind a s = (1 - a ^ 2) / 2 := by
  have hint : ∀ u v : ℝ, IntervalIntegrable (fun s => s * ind a s) volume u v :=
    fun u v => (ind_intervalIntegrable a u v).continuousOn_mul continuous_id.continuousOn
  rw [← integral_add_adjacent_intervals (hint 0 a) (hint a 1)]
  have h0 : ∫ s in (0:ℝ)..a, s * ind a s = 0 := by
    rw [integral_congr (g := fun _ => (0:ℝ))]
    · simp
    · intro s hs
      rw [uIcc_of_le ha0] at hs
      simp [ind, not_lt.2 hs.2]
  have h1 : ∫ s in a..1, s * ind a s = ∫ s in a..1, s := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun s hs => ?_)
    rw [uIoc_of_le ha1] at hs
    simp [ind, hs.1]
  rw [h0, h1, integral_id]; ring

/-- Pointwise expansion of `D²`. -/
lemma D_sq (xs : List ℝ) (s : ℝ) :
    D xs s ^ 2 = (xs.map fun a => (xs.map fun b => ind (max a b) s).sum).sum
      - (xs.map fun a => 2 * xs.length * (s * ind a s)).sum + (xs.length : ℝ) ^ 2 * s ^ 2 := by
  unfold D
  rw [countBelow_eq_sum, List.sum_map_mul_left]
  have h := sq_sum_ind xs s
  have h2 : (xs.map fun a => s * ind a s).sum = s * (xs.map fun a => ind a s).sum :=
    List.sum_map_mul_left _ _ _
  rw [h2]
  nlinarith [h]

/-- **Warnock's formula**: the closed form `l2sq` is the squared `L²` star
discrepancy `∫₀¹ D² ds`, for points in `[0,1]`. -/
theorem l2sq_eq_integral (xs : List ℝ) (hxs : ∀ a ∈ xs, 0 ≤ a ∧ a ≤ 1) :
    l2sq xs = ∫ s in (0:ℝ)..1, D xs s ^ 2 := by
  have hmax : ∀ a ∈ xs, ∀ b ∈ xs, 0 ≤ max a b ∧ max a b ≤ 1 := fun a ha b hb =>
    ⟨le_max_of_le_left (hxs a ha).1, max_le (hxs a ha).2 (hxs b hb).2⟩
  have hI1 : ∀ a, IntervalIntegrable
      (fun s => (xs.map fun b => ind (max a b) s).sum) volume 0 1 := fun a =>
    intervalIntegrable_list_sum xs (fun b s => ind (max a b) s) 0 1
      fun b _ => ind_intervalIntegrable _ 0 1
  have hI2 : ∀ a, IntervalIntegrable (fun s => 2 * xs.length * (s * ind a s)) volume 0 1 :=
    fun a => ((ind_intervalIntegrable a 0 1).continuousOn_mul
      continuous_id.continuousOn).const_mul _
  have hA := intervalIntegrable_list_sum xs
    (fun a s => (xs.map fun b => ind (max a b) s).sum) 0 1 fun a _ => hI1 a
  have hB := intervalIntegrable_list_sum xs
    (fun a s => 2 * xs.length * (s * ind a s)) 0 1 fun a _ => hI2 a
  have hC : IntervalIntegrable (fun s : ℝ => (xs.length : ℝ) ^ 2 * s ^ 2) volume 0 1 :=
    (continuous_const.mul (continuous_pow 2)).intervalIntegrable 0 1
  simp_rw [D_sq]
  rw [integral_add (hA.sub hB) hC, integral_sub hA hB,
    integral_list_sum xs _ 0 1 fun a _ => hI1 a,
    integral_list_sum xs _ 0 1 fun a _ => hI2 a,
    intervalIntegral.integral_const_mul, integral_pow]
  have e1 : (xs.map fun a => ∫ s in (0:ℝ)..1, (xs.map fun b => ind (max a b) s).sum).sum
      = (xs.map fun a => (xs.map fun b => 1 - max a b).sum).sum := by
    congr 1
    apply List.map_congr_left
    intro a ha
    rw [integral_list_sum xs _ 0 1 fun b _ => ind_intervalIntegrable _ 0 1]
    congr 1
    apply List.map_congr_left
    intro b hb
    rw [integral_ind _ 1 (hmax a ha b hb).1 zero_le_one,
      max_eq_left (by linarith [(hmax a ha b hb).2])]
  have e2 : (xs.map fun a => ∫ s in (0:ℝ)..1, 2 * xs.length * (s * ind a s)).sum
      = (xs.length : ℝ) * (xs.map fun a => 1 - a ^ 2).sum := by
    rw [← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro a ha
    rw [intervalIntegral.integral_const_mul, integral_mul_ind a (hxs a ha).1 (hxs a ha).2]
    ring
  rw [e1, e2]
  unfold l2sq
  ring

section Quadrature

variable {f f' : ℝ → ℝ}

lemma sum_map_const_sub (xs : List ℝ) (c : ℝ) (g : ℝ → ℝ) :
    (xs.map fun a => c - g a).sum = xs.length * c - (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons b bs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_succ, ih]; ring

/-- `∫₀¹ 1[a < s] f'(s) ds = f(1) − f(a)` for `a ∈ [0,1]`. -/
lemma integral_ind_mul_deriv (hf : ∀ x, HasDerivAt f (f' x) x) (hc : Continuous f')
    (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    ∫ s in (0:ℝ)..1, ind a s * f' s = f 1 - f a := by
  have hint : ∀ u v : ℝ, IntervalIntegrable (fun s => ind a s * f' s) volume u v :=
    fun u v => by
      have := (ind_intervalIntegrable a u v).continuousOn_mul hc.continuousOn
      simpa [mul_comm] using this
  rw [← integral_add_adjacent_intervals (hint 0 a) (hint a 1)]
  have h0 : ∫ s in (0:ℝ)..a, ind a s * f' s = 0 := by
    rw [integral_congr (g := fun _ => (0:ℝ))]
    · simp
    · intro s hs
      rw [uIcc_of_le ha0] at hs
      simp [ind, not_lt.2 hs.2]
  have h1 : ∫ s in a..1, ind a s * f' s = ∫ s in a..1, f' s := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun s hs => ?_)
    rw [uIoc_of_le ha1] at hs
    simp [ind, hs.1]
  rw [h0, h1, integral_eq_sub_of_hasDerivAt (fun x _ => hf x) (hc.intervalIntegrable a 1)]
  ring

/-- **Quadrature error as an integral of the local discrepancy**: for `f` of
class `C¹` and points in `[0,1]`,
`Σ_{a ∈ xs} f a − |xs| ∫₀¹ f = −∫₀¹ D xs s · f'(s) ds`. -/
theorem quadrature_eq_integral_D (hf : ∀ x, HasDerivAt f (f' x) x) (hc : Continuous f')
    (xs : List ℝ) (hxs : ∀ a ∈ xs, 0 ≤ a ∧ a ≤ 1) :
    (xs.map f).sum - xs.length * ∫ t in (0:ℝ)..1, f t = -∫ s in (0:ℝ)..1, D xs s * f' s := by
  have hcf : Continuous f := continuous_iff_continuousAt.2 fun x => (hf x).continuousAt
  have hI : ∀ a, IntervalIntegrable (fun s => ind a s * f' s) volume 0 1 := fun a => by
    have := (ind_intervalIntegrable a 0 1).continuousOn_mul hc.continuousOn
    simpa [mul_comm] using this
  have hexp : ∀ s, D xs s * f' s
      = (xs.map fun a => ind a s * f' s).sum - xs.length * (s * f' s) := by
    intro s
    unfold D
    rw [countBelow_eq_sum, sub_mul, List.sum_map_mul_right]
    ring
  have hA := intervalIntegrable_list_sum xs (fun a s => ind a s * f' s) 0 1 fun a _ => hI a
  have hB : IntervalIntegrable (fun s => (xs.length : ℝ) * (s * f' s)) volume 0 1 :=
    ((continuous_id.mul hc).const_mul _).intervalIntegrable 0 1
  have hibp : ∫ s in (0:ℝ)..1, s * f' s = f 1 - ∫ s in (0:ℝ)..1, f s := by
    have h := integral_mul_deriv_eq_deriv_mul (u := fun s => s) (u' := fun _ => 1)
      (fun x _ => hasDerivAt_id' x) (fun x _ => hf x) (by simp) (hc.intervalIntegrable 0 1)
    simpa using h
  simp_rw [hexp]
  rw [integral_sub hA hB, integral_list_sum xs _ 0 1 fun a _ => hI a,
    intervalIntegral.integral_const_mul, hibp]
  have e : (xs.map fun a => ∫ s in (0:ℝ)..1, ind a s * f' s).sum
      = (xs.map fun a => f 1 - f a).sum := by
    congr 1
    apply List.map_congr_left
    intro a ha
    exact integral_ind_mul_deriv hf hc a (hxs a ha).1 (hxs a ha).2
  rw [e]
  rw [sum_map_const_sub]
  ring

end Quadrature

end GreedyDiscrepancy
