import GreedyDiscrepancy.Quadrature
import GreedyDiscrepancy.LowerBound

/-!
# Two-sided quadrature error

Combining the quadrature identity `Σ f − n∫f = −f'(1) G(1) + ∫ G f''` with the
two-sided bound `−2/3 ≤ G ≤ 1/2`: for every greedy `L²` sequence started
from the empty set, every `C²` function `f` and every `n`,

  `|Σ_{k<n} f(x_k) − n ∫₀¹ f| ≤ |f'(1)|/2 + (2/3) ∫₀¹ |f''|`.

So the total quadrature error is bounded independently of `n`.
-/

open intervalIntegral MeasureTheory Set

namespace GreedyDiscrepancy

theorem greedy_quadrature_two_sided {f f' f'' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (f'' x) x) (hc : Continuous f'')
    (x : ℕ → ℝ) (hx : ∀ n, IsGreedyStep (pref x n) (x n)) (n : ℕ) :
    |((pref x n).map f).sum - n * ∫ t in (0:ℝ)..1, f t| ≤
      |f' 1| / 2 + 2 / 3 * ∫ t in (0:ℝ)..1, |f'' t| := by
  have hl : ((pref x n).length : ℝ) = n := by simp [pref]
  have hxs : ∀ a ∈ pref x n, 0 ≤ a ∧ a ≤ 1 := by
    intro a ha
    simp only [pref, List.mem_map, List.mem_range] at ha
    obtain ⟨k, -, rfl⟩ := ha
    exact ⟨(hx k).1, (hx k).2.1⟩
  have hid := quadrature_identity hf hf' hc (pref x n) hxs
  rw [hl] at hid
  rw [hid]
  -- |G(1)| ≤ 1/2
  have hG1 : |G (pref x n) 1| ≤ 1 / 2 := by
    rw [abs_le]
    exact ⟨by linarith [greedy_G_ge_two_thirds x hx n 1 (by norm_num) le_rfl,
        (envelope x hx n).2 0 le_rfl (by norm_num), greedy_G_zero x hx n],
      G_le_half x hx n 1 (by norm_num) le_rfl⟩
  -- |G t| ≤ 173/240 on [0,1]
  have hGt : ∀ t, 0 ≤ t → t ≤ 1 → |G (pref x n) t| ≤ 2 / 3 := by
    intro t h0 h1
    rw [abs_le]
    constructor
    · exact greedy_G_ge_two_thirds x hx n t h0 h1
    · linarith [G_le_half x hx n t h0 h1]
  have iGf : IntervalIntegrable (fun t => |G (pref x n) t * f'' t|) volume 0 1 :=
    ((G_continuous _).mul hc).abs.intervalIntegrable 0 1
  have ic : IntervalIntegrable (fun t => 2 / 3 * |f'' t|) volume 0 1 :=
    (continuous_const.mul hc.abs).intervalIntegrable 0 1
  have h1 : |∫ t in (0:ℝ)..1, G (pref x n) t * f'' t| ≤
      ∫ t in (0:ℝ)..1, |G (pref x n) t * f'' t| :=
    abs_integral_le_integral_abs (by norm_num)
  have h2 : ∫ t in (0:ℝ)..1, |G (pref x n) t * f'' t| ≤
      ∫ t in (0:ℝ)..1, 2 / 3 * |f'' t| :=
    integral_mono_on (by norm_num) iGf ic fun t ht => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hGt t ht.1 ht.2) (abs_nonneg _)
  rw [intervalIntegral.integral_const_mul] at h2
  have h3 : |-f' 1 * G (pref x n) 1| ≤ |f' 1| / 2 := by
    rw [abs_mul, abs_neg]
    nlinarith [abs_nonneg (f' 1), abs_nonneg (G (pref x n) 1)]
  calc |-f' 1 * G (pref x n) 1 + ∫ t in (0:ℝ)..1, G (pref x n) t * f'' t|
      ≤ |-f' 1 * G (pref x n) 1| + |∫ t in (0:ℝ)..1, G (pref x n) t * f'' t| := abs_add_le _ _
    _ ≤ |f' 1| / 2 + 2 / 3 * ∫ t in (0:ℝ)..1, |f'' t| := by linarith

theorem kritzinger_quadrature_two_sided {f f' f'' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, HasDerivAt f' (f'' x) x) (hc : Continuous f'')
    (x : ℕ → ℝ) (hx : IsKritzingerSeq x) (n : ℕ) :
    |((pref x n).map f).sum - n * ∫ t in (0:ℝ)..1, f t| ≤
      |f' 1| / 2 + 2 / 3 * ∫ t in (0:ℝ)..1, |f'' t| :=
  greedy_quadrature_two_sided hf hf' hc x (kritzinger_greedy x hx) n

/-- Kritzinger's sequence: `−2/3 ≤ G_n t ≤ 1/2` for all `n` and `t ∈ [0,1]`. -/
theorem kritzinger_G_two_sided (x : ℕ → ℝ) (hx : IsKritzingerSeq x) (n : ℕ)
    (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    -(2 / 3) ≤ G (pref x n) t ∧ G (pref x n) t ≤ 1 / 2 :=
  ⟨greedy_G_ge_two_thirds x (kritzinger_greedy x hx) n t h0 h1,
    kritzinger_G_le_half x hx n t h0 h1⟩

end GreedyDiscrepancy
