import GreedyDiscrepancy.QuadratureTwoSided
import GreedyDiscrepancy.Integrals

/-!
# A square-root bound for the star discrepancy

A large local discrepancy forces a large change of `G` over a short interval:
if `#{a ≤ t} − N t = K > 0` then `D ≥ K − N (s − t)` for `s ≥ t`, so `G`
increases by at least `K² / (2N)` on `[t, t + K/N]`; symmetrically for a
deficit. Since `−2/3 ≤ G ≤ 1/2`, every greedy `L²` sequence satisfies, for
all `N` and `t ∈ [0,1]`,

  `|#{k < N : x_k ≤ t} − N t| ≤ √(7N/3)` and `|#{k < N : x_k < t} − N t| ≤ √(7N/3)`.

The proof only uses the closed form of `G` (no integrals).
-/

namespace GreedyDiscrepancy

/-- Number of points of `xs` in `[0, t]`. -/
noncomputable def countLE (xs : List ℝ) (t : ℝ) : ℕ := xs.countP fun a => decide (a ≤ t)

lemma countLE_cons (a : ℝ) (xs : List ℝ) (t : ℝ) :
    (countLE (a :: xs) t : ℝ) = (if a ≤ t then 1 else 0) + countLE xs t := by
  simp only [countLE, List.countP_cons]
  split_ifs with h <;> simp_all; ring

lemma countLE_le_length (xs : List ℝ) (t : ℝ) : (countLE xs t : ℝ) ≤ xs.length := by
  exact_mod_cast List.countP_le_length

lemma countBelow_le_length (xs : List ℝ) (t : ℝ) : (countBelow xs t : ℝ) ≤ xs.length := by
  exact_mod_cast List.countP_le_length

/-- Excess on the right of `t`: `G (t+L) − G t ≥ L (#{a ≤ t} − N t) − N L²/2`. -/
lemma G_increment_ge (xs : List ℝ) (t L : ℝ) (hL : 0 ≤ L) :
    L * ((countLE xs t : ℝ) - xs.length * t) - xs.length * L ^ 2 / 2 ≤ G xs (t + L) - G xs t := by
  induction xs with
  | nil => simp [G, countLE]
  | cons a as ih =>
    rw [G_cons, G_cons, countLE_cons]
    simp only [List.length_cons, Nat.cast_succ]
    have key : L * (if a ≤ t then 1 else 0) ≤ max (t + L - a) 0 - max (t - a) 0 := by
      split_ifs with h
      · rw [max_eq_left (by linarith), max_eq_left (by linarith)]; linarith
      · rw [max_eq_right (by linarith : t - a ≤ 0)]; simp
    nlinarith [key, ih]

/-- Deficit on the left of `t`: `G t − G (t−L) ≤ L (#{a < t} − N t) + N L²/2`. -/
lemma G_decrement_le (xs : List ℝ) (t L : ℝ) (hL : 0 ≤ L) :
    G xs t - G xs (t - L) ≤ L * ((countBelow xs t : ℝ) - xs.length * t) + xs.length * L ^ 2 / 2 := by
  induction xs with
  | nil => simp [G, countBelow]
  | cons a as ih =>
    rw [G_cons, G_cons, countBelow_cons]
    simp only [List.length_cons, Nat.cast_succ]
    have key : max (t - a) 0 - max (t - L - a) 0 ≤ L * ind a t := by
      unfold ind
      split_ifs with h
      · rcases le_total (t - L - a) 0 with h2 | h2
        · rw [max_eq_left (by linarith), max_eq_right h2]; linarith
        · rw [max_eq_left (by linarith), max_eq_left h2]; linarith
      · rw [max_eq_right (by linarith : t - a ≤ 0), max_eq_right (by linarith : t - L - a ≤ 0)]
        simp
    nlinarith [key, ih]

lemma length_pref (x : ℕ → ℝ) (n : ℕ) : (pref x n).length = n := by simp [pref]

/-- Abstract form: if `G` takes values in `[−c₁, c₂]` on `[0,1]`, the
local discrepancy is at most `√(2 N (c₁ + c₂))` in absolute value. -/
theorem star_le_of_G_bounds (xs : List ℝ) (c : ℝ)
    (hG : ∀ s t, 0 ≤ s → s ≤ 1 → 0 ≤ t → t ≤ 1 → G xs t - G xs s ≤ c)
    (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    (countLE xs t : ℝ) - xs.length * t ≤ Real.sqrt (2 * xs.length * c) ∧
      xs.length * t - countBelow xs t ≤ Real.sqrt (2 * xs.length * c) := by
  set N : ℝ := (xs.length : ℝ) with hN
  constructor
  · set K := (countLE xs t : ℝ) - N * t with hK
    rcases le_or_gt K 0 with hk | hk
    · exact hk.trans (Real.sqrt_nonneg _)
    have hNpos : 0 < N := by
      have := countLE_le_length xs t
      nlinarith
    have hLle : t + K / N ≤ 1 := by
      have := countLE_le_length xs t
      have : K ≤ N * (1 - t) := by rw [hK]; nlinarith
      have h' : K / N ≤ 1 - t := by rw [div_le_iff₀ hNpos]; linarith
      linarith
    have hinc := G_increment_ge xs t (K / N) (div_nonneg hk.le hNpos.le)
    have hc := hG t (t + K / N) h0 h1 (by positivity) hLle
    have hsq : K ^ 2 / (2 * N) ≤ c := by
      have e : K / N * K - N * (K / N) ^ 2 / 2 = K ^ 2 / (2 * N) := by field_simp; ring
      rw [← hN] at hinc
      linarith
    apply Real.le_sqrt_of_sq_le
    rw [div_le_iff₀ (by positivity)] at hsq
    linarith
  · set K := N * t - (countBelow xs t : ℝ) with hK
    rcases le_or_gt K 0 with hk | hk
    · exact hk.trans (Real.sqrt_nonneg _)
    have hNpos : 0 < N := by
      have : (0 : ℝ) ≤ countBelow xs t := Nat.cast_nonneg _
      nlinarith
    have hL0 : 0 ≤ t - K / N := by
      have : (0 : ℝ) ≤ countBelow xs t := Nat.cast_nonneg _
      have h' : K / N ≤ t := by rw [div_le_iff₀ hNpos]; linarith
      linarith
    have hdec := G_decrement_le xs t (K / N) (div_nonneg hk.le hNpos.le)
    have hc := hG t (t - K / N) h0 h1 hL0 (by linarith [div_nonneg hk.le hNpos.le])
    have hsq : K ^ 2 / (2 * N) ≤ c := by
      have e : K / N * (-K) + N * (K / N) ^ 2 / 2 = -(K ^ 2 / (2 * N)) := by field_simp; ring
      rw [← hN] at hdec
      have : K / N * ((countBelow xs t : ℝ) - N * t) = K / N * (-K) := by rw [hK]; ring
      linarith
    apply Real.le_sqrt_of_sq_le
    rw [div_le_iff₀ (by positivity)] at hsq
    linarith

/-- **Star discrepancy `O(√N)`** for every greedy `L²` sequence (any tie-break):
`|#{k < N : x_k ≤ t} − N t| ≤ √(7N/3)` and the same with `<`. -/
theorem greedy_star_le_sqrt (x : ℕ → ℝ) (hx : ∀ n, IsGreedyStep (pref x n) (x n)) (n : ℕ)
    (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    |(countLE (pref x n) t : ℝ) - n * t| ≤ Real.sqrt (7 * n / 3) ∧
      |(countBelow (pref x n) t : ℝ) - n * t| ≤ Real.sqrt (7 * n / 3) := by
  have hG : ∀ s u, 0 ≤ s → s ≤ 1 → 0 ≤ u → u ≤ 1 →
      G (pref x n) u - G (pref x n) s ≤ 7 / 6 := fun s u hs0 hs1 hu0 hu1 => by
    have := G_le_half x hx n u hu0 hu1
    have := greedy_G_ge_two_thirds x hx n s hs0 hs1
    linarith
  have h := star_le_of_G_bounds (pref x n) (7 / 6) hG t h0 h1
  rw [length_pref] at h
  have e : (2 * (n : ℝ) * (7 / 6)) = 7 * n / 3 := by ring
  rw [e] at h
  have hle : (countBelow (pref x n) t : ℝ) ≤ countLE (pref x n) t := by
    have : (pref x n).countP (fun a => decide (a < t)) ≤ (pref x n).countP (fun a => decide (a ≤ t)) :=
      List.countP_mono_left fun a _ ha => by simp at ha ⊢; linarith
    exact_mod_cast this
  constructor <;> rw [abs_le] <;> constructor <;> linarith [h.1, h.2]

/-- The same bound for Kritzinger's sequence. -/
theorem kritzinger_star_le_sqrt (x : ℕ → ℝ) (hx : IsKritzingerSeq x) (n : ℕ)
    (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    |(countLE (pref x n) t : ℝ) - n * t| ≤ Real.sqrt (7 * n / 3) ∧
      |(countBelow (pref x n) t : ℝ) - n * t| ≤ Real.sqrt (7 * n / 3) :=
  greedy_star_le_sqrt x (kritzinger_greedy x hx) n t h0 h1

end GreedyDiscrepancy
