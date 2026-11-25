import GreedyDiscrepancy.Envelope
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Quadrature of convex functions

For `f` of class `C²` (given with explicit derivatives `f'`, `f''`, `f''`
continuous) and points `xs ⊆ [0,1]`:

  `Σ_{a ∈ xs} f a − |xs| ∫₀¹ f = −f'(1) G xs 1 + ∫₀¹ G xs t f''(t) dt`.

Combined with the envelope theorem this gives, for every greedy `L²`
sequence and every convex `f` (`f'' ≥ 0` on `[0,1]`), a bound on
`Σ_{k<n} f(x_k) − n ∫₀¹ f` that does not depend on `n`.
-/

open intervalIntegral MeasureTheory Set

namespace GreedyDiscrepancy

lemma G_cons (a : ℝ) (xs : List ℝ) (t : ℝ) :
    G (a :: xs) t = G xs t + max (t - a) 0 - t ^ 2 / 2 := by
  simp only [G, List.map_cons, List.sum_cons, List.length_cons, Nat.cast_succ]; ring

lemma G_continuous (xs : List ℝ) : Continuous (G xs) := by
  induction xs with
  | nil =>
    have : G [] = fun _ => (0:ℝ) := by funext t; simp [G]
    rw [this]; exact continuous_const
  | cons a as ih =>
    have : G (a :: as) = fun t => G as t + max (t - a) 0 - t ^ 2 / 2 := by
      funext t; exact G_cons a as t
    rw [this]
    exact (ih.add ((continuous_sub_right a).max continuous_const)).sub
      ((continuous_pow 2).div_const 2)

section Calculus

variable {f f' f'' : ℝ → ℝ}

lemma cont_f' (hf' : ∀ x, HasDerivAt f' (f'' x) x) : Continuous f' := continuous_iff_continuousAt.2 fun x => (hf' x).continuousAt

lemma cont_f (hf : ∀ x, HasDerivAt f (f' x) x) : Continuous f := continuous_iff_continuousAt.2 fun x => (hf x).continuousAt

/-- Taylor's formula at `1` with integral remainder, written over `[0,1]`. -/
lemma taylor_point (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x) (hc : Continuous f'') (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    f a = f 1 + f' 1 * (a - 1) + ∫ t in (0:ℝ)..1, max (t - a) 0 * f'' t := by
  have hcf' := cont_f' hf'
  have hint : ∀ u v : ℝ, IntervalIntegrable (fun t => max (t - a) 0 * f'' t) volume u v :=
    fun u v => ((continuous_sub_right a).max continuous_const |>.mul hc).intervalIntegrable u v
  rw [← integral_add_adjacent_intervals (hint 0 a) (hint a 1)]
  have h0 : ∫ t in (0:ℝ)..a, max (t - a) 0 * f'' t = 0 := by
    rw [integral_congr (g := fun _ => (0:ℝ))]
    · simp
    · intro t ht
      rw [uIcc_of_le ha0] at ht
      simp [max_eq_right (by linarith [ht.2] : t - a ≤ 0)]
  have h1 : ∫ t in a..1, max (t - a) 0 * f'' t = ∫ t in a..1, (t - a) * f'' t := by
    apply integral_congr
    intro t ht
    rw [uIcc_of_le ha1] at ht
    simp [max_eq_left (by linarith [ht.1] : 0 ≤ t - a)]
  have hibp := integral_mul_deriv_eq_deriv_mul (a := a) (b := 1) (u := fun t => t - a)
    (u' := fun _ => (1:ℝ)) (v := f') (v' := f'')
    (fun t _ => (hasDerivAt_id t).sub_const a) (fun t _ => hf' t)
    intervalIntegrable_const (hc.intervalIntegrable a 1)
  have hftc := integral_eq_sub_of_hasDerivAt (a := a) (b := 1) (fun t _ => hf t)
    (hcf'.intervalIntegrable a 1)
  rw [h0, h1, zero_add, hibp]
  simp only [one_mul, sub_self, zero_mul, sub_zero]
  rw [hftc]
  ring

/-- `∫₀¹ f = f 1 − f'(1)/2 + ∫₀¹ (t²/2) f''(t) dt`. -/
lemma integral_formula (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x) (hc : Continuous f'') :
    ∫ t in (0:ℝ)..1, f t = f 1 - f' 1 / 2 + ∫ t in (0:ℝ)..1, t ^ 2 / 2 * f'' t := by
  have hcf' := cont_f' hf'
  have hd2 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => t ^ 2 / 2) t t := by
    intro t
    exact ((hasDerivAt_pow 2 t).div_const 2).congr_deriv (by norm_num)
  have hibp1 := integral_mul_deriv_eq_deriv_mul (a := 0) (b := 1) (u := fun t : ℝ => t ^ 2 / 2)
    (u' := fun t => t) (v := f') (v' := f'') (fun t _ => hd2 t) (fun t _ => hf' t)
    (continuous_id.intervalIntegrable 0 1) (hc.intervalIntegrable 0 1)
  have hibp2 := integral_mul_deriv_eq_deriv_mul (a := 0) (b := 1) (u := fun t : ℝ => t)
    (u' := fun _ => (1:ℝ)) (v := f) (v' := f') (fun t _ => hasDerivAt_id t) (fun t _ => hf t)
    intervalIntegrable_const (hcf'.intervalIntegrable 0 1)
  simp only [one_mul] at hibp2
  rw [hibp1, hibp2]
  norm_num
  ring

/-- One point: `f a − ∫₀¹ f = −f'(1) ((1−a)₊ − 1/2) + ∫₀¹ ((t−a)₊ − t²/2) f''`. -/
lemma point_formula (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x) (hc : Continuous f'') (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    f a - ∫ t in (0:ℝ)..1, f t =
      -f' 1 * (max (1 - a) 0 - 1 / 2) +
        ∫ t in (0:ℝ)..1, (max (t - a) 0 - t ^ 2 / 2) * f'' t := by
  have i1 : IntervalIntegrable (fun t => max (t - a) 0 * f'' t) volume 0 1 :=
    ((continuous_sub_right a).max continuous_const |>.mul hc).intervalIntegrable 0 1
  have i2 : IntervalIntegrable (fun t : ℝ => t ^ 2 / 2 * f'' t) volume 0 1 :=
    ((continuous_pow 2).div_const 2 |>.mul hc).intervalIntegrable 0 1
  have hsplit : ∫ t in (0:ℝ)..1, (max (t - a) 0 - t ^ 2 / 2) * f'' t =
      (∫ t in (0:ℝ)..1, max (t - a) 0 * f'' t) - ∫ t in (0:ℝ)..1, t ^ 2 / 2 * f'' t := by
    rw [← integral_sub i1 i2]
    congr 1; ext t; ring
  rw [hsplit, max_eq_left (by linarith : (0:ℝ) ≤ 1 - a), integral_formula hf hf' hc]
  rw [taylor_point hf hf' hc a ha0 ha1]
  ring

/-- The quadrature identity `Σ f − n∫f = −f'(1) G(1) + ∫ G f''`. -/
theorem quadrature_identity (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x) (hc : Continuous f'') (xs : List ℝ) (hxs : ∀ a ∈ xs, 0 ≤ a ∧ a ≤ 1) :
    (xs.map f).sum - xs.length * ∫ t in (0:ℝ)..1, f t =
      -f' 1 * G xs 1 + ∫ t in (0:ℝ)..1, G xs t * f'' t := by
  induction xs with
  | nil => simp [G]
  | cons a as ih =>
    have ha := hxs a (by simp)
    have ih' := ih (fun b hb => hxs b (by simp [hb]))
    have hp := point_formula hf hf' hc a ha.1 ha.2
    have iG : IntervalIntegrable (fun t => G as t * f'' t) volume 0 1 :=
      ((G_continuous as).mul hc).intervalIntegrable 0 1
    have iK : IntervalIntegrable (fun t => (max (t - a) 0 - t ^ 2 / 2) * f'' t) volume 0 1 :=
      ((((continuous_sub_right a).max continuous_const).sub ((continuous_pow 2).div_const 2)).mul
        hc).intervalIntegrable 0 1
    have hsum : ∫ t in (0:ℝ)..1, G (a :: as) t * f'' t =
        (∫ t in (0:ℝ)..1, G as t * f'' t) +
          ∫ t in (0:ℝ)..1, (max (t - a) 0 - t ^ 2 / 2) * f'' t := by
      rw [← integral_add iG iK]
      congr 1; ext t; rw [G_cons]; ring
    rw [hsum, G_cons]
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_succ]
    linarith [hp, ih']

/-- `∫₀¹ (t/2) f'' = f'(1)/2 − (f 1 − f 0)/2`. -/
lemma integral_half_t (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x) (hc : Continuous f'') :
    ∫ t in (0:ℝ)..1, t / 2 * f'' t = f' 1 / 2 - (f 1 - f 0) / 2 := by
  have hcf' := cont_f' hf'
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => t / 2) (1 / 2) t := fun t =>
    (hasDerivAt_id' (x := t)).div_const 2
  have hibp := integral_mul_deriv_eq_deriv_mul (a := 0) (b := 1) (u := fun t : ℝ => t / 2)
    (u' := fun _ => (1 / 2 : ℝ)) (v := f') (v' := f'') (fun t _ => hd t) (fun t _ => hf' t)
    intervalIntegrable_const (hc.intervalIntegrable 0 1)
  have hftc := integral_eq_sub_of_hasDerivAt (a := 0) (b := 1) (fun t _ => hf t)
    (hcf'.intervalIntegrable 0 1)
  rw [hibp, intervalIntegral.integral_const_mul, hftc]
  ring

/-- `∫₀¹ ((1−t)/2) f'' = −f'(0)/2 + (f 1 − f 0)/2`. -/
lemma integral_half_one_sub (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x) (hc : Continuous f'') :
    ∫ t in (0:ℝ)..1, (1 - t) / 2 * f'' t = -(f' 0 / 2) + (f 1 - f 0) / 2 := by
  have hcf' := cont_f' hf'
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (1 - t) / 2) (-(1 / 2)) t := fun t => by
    exact (((hasDerivAt_id' (x := t)).const_sub 1).div_const 2).congr_deriv (by norm_num)
  have hibp := integral_mul_deriv_eq_deriv_mul (a := 0) (b := 1) (u := fun t : ℝ => (1 - t) / 2)
    (u' := fun _ => (-(1 / 2) : ℝ)) (v := f') (v' := f'') (fun t _ => hd t) (fun t _ => hf' t)
    intervalIntegrable_const (hc.intervalIntegrable 0 1)
  have hftc := integral_eq_sub_of_hasDerivAt (a := 0) (b := 1) (fun t _ => hf t)
    (hcf'.intervalIntegrable 0 1)
  rw [hibp, intervalIntegral.integral_const_mul, hftc]
  ring

/-- `∫₀¹ f'' = f'(1) − f'(0)`. -/
lemma integral_f'' (hf' : ∀ x, HasDerivAt f' (f'' x) x) (hc : Continuous f'') : ∫ t in (0:ℝ)..1, f'' t = f' 1 - f' 0 :=
  integral_eq_sub_of_hasDerivAt (fun t _ => hf' t) (hc.intervalIntegrable 0 1)

/-- **Convex quadrature bound** for any point list satisfying the envelope
inequalities and `|G(1)| ≤ 1/2`. -/
theorem convex_bound (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x) (hc : Continuous f'') (xs : List ℝ) (hxs : ∀ a ∈ xs, 0 ≤ a ∧ a ≤ 1)
    (hA : ∀ t, 0 ≤ t → t ≤ 1 → G xs t ≤ t / 2)
    (hC : ∀ t, 0 ≤ t → t ≤ 1 → G xs t ≤ G xs 1 + (1 - t) / 2)
    (hG1 : |G xs 1| ≤ 1 / 2) (hconv : ∀ t, 0 ≤ t → t ≤ 1 → 0 ≤ f'' t) :
    (xs.map f).sum - xs.length * ∫ t in (0:ℝ)..1, f t ≤
      min ((f 1 - f 0) / 2 + max 0 (-f' 0)) (max 0 (f' 1) - (f 1 - f 0) / 2) := by
  rw [quadrature_identity hf hf' hc xs hxs]
  have iG : IntervalIntegrable (fun t => G xs t * f'' t) volume 0 1 :=
    ((G_continuous xs).mul hc).intervalIntegrable 0 1
  -- bound through (C)
  have iC : IntervalIntegrable (fun t => (G xs 1 + (1 - t) / 2) * f'' t) volume 0 1 :=
    ((continuous_const.add ((continuous_const.sub continuous_id).div_const 2)).mul
      hc).intervalIntegrable 0 1
  have mC : ∫ t in (0:ℝ)..1, G xs t * f'' t ≤ ∫ t in (0:ℝ)..1, (G xs 1 + (1 - t) / 2) * f'' t :=
    integral_mono_on (by norm_num) iG iC fun t ht =>
      mul_le_mul_of_nonneg_right (hC t ht.1 ht.2) (hconv t ht.1 ht.2)
  have eC : ∫ t in (0:ℝ)..1, (G xs 1 + (1 - t) / 2) * f'' t =
      G xs 1 * (f' 1 - f' 0) + (-(f' 0 / 2) + (f 1 - f 0) / 2) := by
    have i1 : IntervalIntegrable (fun t => G xs 1 * f'' t) volume 0 1 :=
      (continuous_const.mul hc).intervalIntegrable 0 1
    have i2 : IntervalIntegrable (fun t : ℝ => (1 - t) / 2 * f'' t) volume 0 1 :=
      (((continuous_const.sub continuous_id).div_const 2).mul hc).intervalIntegrable 0 1
    have : (fun t => (G xs 1 + (1 - t) / 2) * f'' t) =
        fun t => G xs 1 * f'' t + (1 - t) / 2 * f'' t := by funext t; ring
    rw [this, integral_add i1 i2, intervalIntegral.integral_const_mul, integral_f'' hf' hc,
      integral_half_one_sub hf hf' hc]
  -- bound through (A)
  have iA : IntervalIntegrable (fun t : ℝ => t / 2 * f'' t) volume 0 1 :=
    ((continuous_id.div_const 2).mul hc).intervalIntegrable 0 1
  have mA : ∫ t in (0:ℝ)..1, G xs t * f'' t ≤ ∫ t in (0:ℝ)..1, t / 2 * f'' t :=
    integral_mono_on (by norm_num) iG iA fun t ht =>
      mul_le_mul_of_nonneg_right (hA t ht.1 ht.2) (hconv t ht.1 ht.2)
  rw [integral_half_t hf hf' hc] at mA
  rw [eC] at mC
  have hG := abs_le.1 hG1
  apply le_min
  · -- −f'1 G1 + G1 (f'1 − f'0) − f'0/2 + (f1−f0)/2 = (f1−f0)/2 − f'0 (G1 + 1/2)
    have key : -f' 0 * (G xs 1 + 1 / 2) ≤ max 0 (-f' 0) := by
      rcases le_total 0 (-f' 0) with h | h
      · rw [max_eq_right h]; nlinarith
      · rw [max_eq_left h]; nlinarith
    nlinarith [key]
  · have key : f' 1 * (1 / 2 - G xs 1) ≤ max 0 (f' 1) := by
      rcases le_total 0 (f' 1) with h | h
      · rw [max_eq_right h]; nlinarith
      · rw [max_eq_left h]; nlinarith
    nlinarith [key]


/-- **Sharp convex quadrature bound** (found by GPT-6.2 Sol):
with `b = G(1) + 1/2 ∈ [0,1]`, the envelopes give `G t ≤ t/2 − (t − b)₊`, hence
`Σ f − n∫f ≤ (f 0 + f 1)/2 − f b` for convex `f`, with equality for affine `f`. -/
theorem convex_bound_sharp (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (f'' x) x) (hc : Continuous f'') (xs : List ℝ)
    (hxs : ∀ a ∈ xs, 0 ≤ a ∧ a ≤ 1)
    (hA : ∀ t, 0 ≤ t → t ≤ 1 → G xs t ≤ t / 2)
    (hC : ∀ t, 0 ≤ t → t ≤ 1 → G xs t ≤ G xs 1 + (1 - t) / 2)
    (hG1 : |G xs 1| ≤ 1 / 2) (hconv : ∀ t, 0 ≤ t → t ≤ 1 → 0 ≤ f'' t) :
    (xs.map f).sum - xs.length * ∫ t in (0:ℝ)..1, f t ≤
      (f 0 + f 1) / 2 - f (G xs 1 + 1 / 2) := by
  set b := G xs 1 + 1 / 2 with hb
  have hG := abs_le.1 hG1
  have hb0 : 0 ≤ b := by linarith
  have hb1 : b ≤ 1 := by linarith
  rw [quadrature_identity hf hf' hc xs hxs]
  have iG : IntervalIntegrable (fun t => G xs t * f'' t) volume 0 1 :=
    ((G_continuous xs).mul hc).intervalIntegrable 0 1
  have i1 : IntervalIntegrable (fun t : ℝ => t / 2 * f'' t) volume 0 1 :=
    ((continuous_id.div_const 2).mul hc).intervalIntegrable 0 1
  have i2 : IntervalIntegrable (fun t => max (t - b) 0 * f'' t) volume 0 1 :=
    (((continuous_sub_right b).max continuous_const).mul hc).intervalIntegrable 0 1
  have iE : IntervalIntegrable (fun t => (t / 2 - max (t - b) 0) * f'' t) volume 0 1 :=
    ((((continuous_id.div_const 2).sub ((continuous_sub_right b).max continuous_const))).mul
      hc).intervalIntegrable 0 1
  have mono : ∫ t in (0:ℝ)..1, G xs t * f'' t ≤ ∫ t in (0:ℝ)..1, (t / 2 - max (t - b) 0) * f'' t :=
    integral_mono_on (by norm_num) iG iE fun t ht => by
      apply mul_le_mul_of_nonneg_right _ (hconv t ht.1 ht.2)
      rcases le_total t b with htb | htb
      · rw [max_eq_right (by linarith)]; linarith [hA t ht.1 ht.2]
      · rw [max_eq_left (by linarith)]; linarith [hC t ht.1 ht.2]
  have split : ∫ t in (0:ℝ)..1, (t / 2 - max (t - b) 0) * f'' t =
      (∫ t in (0:ℝ)..1, t / 2 * f'' t) - ∫ t in (0:ℝ)..1, max (t - b) 0 * f'' t := by
    rw [← integral_sub i1 i2]; congr 1; ext t; ring
  have hT := taylor_point hf hf' hc b hb0 hb1
  rw [split, integral_half_t hf hf' hc] at mono
  have hprod : f' 1 * (b - 1) = f' 1 * G xs 1 - f' 1 / 2 := by rw [hb]; ring
  rw [hprod] at hT
  linarith [mono, hT]

end Calculus

/-- **Theorem.** For every greedy `L²` sequence started from the empty set,
every `C²` convex `f` on `[0,1]` and every `n`:
`Σ_{k<n} f(x_k) − n ∫₀¹ f ≤ min((f 1 − f 0)/2 + max(0, −f'(0)), max(0, f'(1)) − (f 1 − f 0)/2)`. -/
theorem greedy_convex_quadrature {f f' f'' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (f'' x) x) (hc : Continuous f'')
    (hconv : ∀ t, 0 ≤ t → t ≤ 1 → 0 ≤ f'' t)
    (x : ℕ → ℝ) (hx : ∀ n, IsGreedyStep (pref x n) (x n)) (n : ℕ) :
    ((pref x n).map f).sum - n * ∫ t in (0:ℝ)..1, f t ≤
      min ((f 1 - f 0) / 2 + max 0 (-f' 0)) (max 0 (f' 1) - (f 1 - f 0) / 2) := by
  have hl : ((pref x n).length : ℝ) = n := by simp [pref]
  have hxs : ∀ a ∈ pref x n, 0 ≤ a ∧ a ≤ 1 := by
    intro a ha
    simp only [pref, List.mem_map, List.mem_range] at ha
    obtain ⟨k, -, rfl⟩ := ha
    exact ⟨(hx k).1, (hx k).2.1⟩
  have hG1 : |G (pref x n) 1| ≤ 1 / 2 := by
    have h1 := (envelope x hx n).1 1 (by norm_num) le_rfl
    have h0 := (envelope x hx n).2 0 le_rfl (by norm_num)
    have hG0 : G (pref x n) 0 = 0 := by
      have hge : ∀ a ∈ pref x n, 0 ≤ a := fun a ha => (hxs a ha).1
      have : ((pref x n).map fun a => max (0 - a) 0).sum =
          ((pref x n).map fun _ => (0:ℝ)).sum := by
        congr 1
        apply List.map_congr_left
        intro a ha
        exact max_eq_right (by linarith [hge a ha])
      unfold G
      rw [this]
      simp
    rw [abs_le]; constructor <;> linarith
  rw [← hl]
  exact convex_bound hf hf' hc (pref x n) hxs (envelope x hx n).1 (envelope x hx n).2 hG1 hconv

/-- Greedy sequences: `Σ_{k<n} f(x_k) − n∫₀¹ f ≤ (f 0 + f 1)/2 − f(b_n)` for convex `f`,
where `b_n = (n+1)/2 − Σ_{k<n} x_k ∈ [0,1]`. -/
theorem greedy_convex_quadrature_sharp {f f' f'' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (f'' x) x) (hc : Continuous f'')
    (hconv : ∀ t, 0 ≤ t → t ≤ 1 → 0 ≤ f'' t)
    (x : ℕ → ℝ) (hx : ∀ n, IsGreedyStep (pref x n) (x n)) (n : ℕ) :
    ((pref x n).map f).sum - n * ∫ t in (0:ℝ)..1, f t ≤
      (f 0 + f 1) / 2 - f ((n + 1) / 2 - (pref x n).sum) := by
  have hl : ((pref x n).length : ℝ) = n := by simp [pref]
  have hxs : ∀ a ∈ pref x n, 0 ≤ a ∧ a ≤ 1 := by
    intro a ha
    simp only [pref, List.mem_map, List.mem_range] at ha
    obtain ⟨k, -, rfl⟩ := ha
    exact ⟨(hx k).1, (hx k).2.1⟩
  have hG1eq : G (pref x n) 1 = n / 2 - (pref x n).sum := by
    have : ((pref x n).map fun a => max (1 - a) 0).sum =
        ((pref x n).map fun a => 1 - a).sum := by
      congr 1
      apply List.map_congr_left
      intro a ha
      exact max_eq_left (by linarith [(hxs a ha).2])
    unfold G
    rw [this, sum_one_sub, hl]
    ring
  have hG1 : |G (pref x n) 1| ≤ 1 / 2 := by
    rw [hG1eq]
    have := sum_near_half x hx n
    rw [abs_le] at this ⊢; constructor <;> linarith [this.1, this.2]
  have key := convex_bound_sharp hf hf' hc (pref x n) hxs (envelope x hx n).1
    (envelope x hx n).2 hG1 hconv
  rw [hl, hG1eq] at key
  have : (n : ℝ) / 2 - (pref x n).sum + 1 / 2 = (n + 1) / 2 - (pref x n).sum := by ring
  rw [this] at key
  exact key

theorem kritzinger_convex_quadrature {f f' f'' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (f'' x) x) (hc : Continuous f'')
    (hconv : ∀ t, 0 ≤ t → t ≤ 1 → 0 ≤ f'' t)
    (x : ℕ → ℝ) (hx : IsKritzingerSeq x) (n : ℕ) :
    ((pref x n).map f).sum - n * ∫ t in (0:ℝ)..1, f t ≤
      min ((f 1 - f 0) / 2 + max 0 (-f' 0)) (max 0 (f' 1) - (f 1 - f 0) / 2) :=
  greedy_convex_quadrature hf hf' hc hconv x (kritzinger_greedy x hx) n

end GreedyDiscrepancy
