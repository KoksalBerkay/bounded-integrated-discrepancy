import GreedyDiscrepancy.HalfOpen
import GreedyDiscrepancy.RepairLower

/-!
# Logarithmic star discrepancy from an arbitrary start

Steinerberger considers Kritzinger sequences started from an arbitrary finite
initial set. With `μ = 1`, the repaired chord invariant (`greedy_chordRepair`)
gives, for `n > m`,

  `G(t+h) + G(t−h) − 2 G(t) ≤ 2h + e`,  `e = m² / (4 (n − m))`,

and the repaired envelopes give `G ≤ t/2 + δ`, `G ≤ G(1) + (1−t)/2 + δ` with
`δ = (m−1/2)²/(2n)`. The dyadic argument of `LogStar`, run from the scale
`h ≈ 1/n`, loses at most `e · 2^{J+1} / t₀ ≤ 4 e n` to the extra term. Result
(`greedy_star_log_from`): for `n ≥ 2m`,

  `|#{k < n : x_k ≤ t} − n t| ≤ ⌈log₂ n⌉ + 3 + 3 m²`,

and the same with `<`. The leading term `log₂ n` does not depend on the
initial set.
-/

namespace GreedyDiscrepancy

/-- Second differences bounded by `c h + e`. -/
def SecondDiffBoundCE (G : ℝ → ℝ) (c e : ℝ) : Prop :=
  ∀ t h : ℝ, 0 ≤ h → 0 ≤ t - h → t + h ≤ 1 → G (t + h) + G (t - h) - 2 * G t ≤ c * h + e

lemma dyadic_left_E (G : ℝ → ℝ) (c e : ℝ) (hS : SecondDiffBoundCE G c e) (t₀ h K : ℝ)
    (J : ℕ) (hh : 0 < h) (ht : t₀ = 2 ^ J * h) (ht1 : t₀ + h ≤ 1)
    (base : h * (K - 1 / 2) ≤ G (t₀ + h) - G t₀) :
    t₀ * (K - 1 / 2 - c - c * J / 2) - e * (2 ^ (J + 1) - 1) ≤ G t₀ - G 0 := by
  have claim : ∀ j : ℕ, j ≤ J →
      2 ^ j * h * (K - 1 / 2 - c - c * j / 2) - e * (2 ^ (j + 1) - 1)
        ≤ G t₀ - G (t₀ - 2 ^ j * h) := by
    intro j
    induction j with
    | zero =>
      intro _
      have hpow : (1 : ℝ) ≤ 2 ^ J := one_le_pow₀ (by norm_num)
      have h0 : 0 ≤ t₀ - h := by rw [ht]; nlinarith
      have := hS t₀ h hh.le h0 ht1
      simp only [pow_zero, one_mul, Nat.cast_zero, zero_add, pow_one]
      nlinarith
    | succ j ih =>
      intro hj
      have ih' := ih (by omega)
      have hpj : (2 : ℝ) ^ (j + 1) ≤ 2 ^ J := pow_le_pow_right₀ (by norm_num) hj
      have hH : 0 ≤ 2 ^ j * h := by positivity
      have e3 : (2 : ℝ) ^ (j + 1) = 2 * 2 ^ j := by ring
      have h0 : 0 ≤ (t₀ - 2 ^ j * h) - 2 ^ j * h := by rw [ht]; nlinarith
      have h1 : (t₀ - 2 ^ j * h) + 2 ^ j * h ≤ 1 := by linarith
      have hs := hS (t₀ - 2 ^ j * h) (2 ^ j * h) hH h0 h1
      have e1 : t₀ - 2 ^ j * h + 2 ^ j * h = t₀ := by ring
      have e2 : t₀ - 2 ^ j * h - 2 ^ j * h = t₀ - 2 ^ (j + 1) * h := by ring
      rw [e1, e2] at hs
      have e4 : (2 : ℝ) ^ (j + 1 + 1) = 2 * (2 * 2 ^ j) := by ring
      push_cast
      rw [e4]
      rw [e3] at ih' hs ⊢
      linarith [ih', hs]
  have := claim J le_rfl
  rw [← ht, sub_self] at this
  exact this

lemma dyadic_right_E (G : ℝ → ℝ) (c e : ℝ) (hS : SecondDiffBoundCE G c e) (t₀ h K : ℝ)
    (J : ℕ) (hh : 0 < h) (ht : 1 - t₀ = 2 ^ J * h) (ht0 : 0 ≤ t₀ - h)
    (base : G t₀ - G (t₀ - h) ≤ h * (-K + 1 / 2)) :
    G 1 - G t₀ ≤ (1 - t₀) * (-K + 1 / 2 + c + c * J / 2) + e * (2 ^ (J + 1) - 1) := by
  have claim : ∀ j : ℕ, j ≤ J →
      G (t₀ + 2 ^ j * h) - G t₀ ≤ 2 ^ j * h * (-K + 1 / 2 + c + c * j / 2)
        + e * (2 ^ (j + 1) - 1) := by
    intro j
    induction j with
    | zero =>
      intro _
      have hpow : (1 : ℝ) ≤ 2 ^ J := one_le_pow₀ (by norm_num)
      have h1 : t₀ + h ≤ 1 := by nlinarith
      have := hS t₀ h hh.le ht0 h1
      simp only [pow_zero, one_mul, Nat.cast_zero, zero_add, pow_one]
      nlinarith
    | succ j ih =>
      intro hj
      have ih' := ih (by omega)
      have hpj : (2 : ℝ) ^ (j + 1) ≤ 2 ^ J := pow_le_pow_right₀ (by norm_num) hj
      have hH : 0 ≤ 2 ^ j * h := by positivity
      have e3 : (2 : ℝ) ^ (j + 1) = 2 * 2 ^ j := by ring
      have h0 : 0 ≤ (t₀ + 2 ^ j * h) - 2 ^ j * h := by linarith
      have h1 : (t₀ + 2 ^ j * h) + 2 ^ j * h ≤ 1 := by nlinarith
      have hs := hS (t₀ + 2 ^ j * h) (2 ^ j * h) hH h0 h1
      have e1 : t₀ + 2 ^ j * h - 2 ^ j * h = t₀ := by ring
      have e2 : t₀ + 2 ^ j * h + 2 ^ j * h = t₀ + 2 ^ (j + 1) * h := by ring
      rw [e1, e2] at hs
      have e4 : (2 : ℝ) ^ (j + 1 + 1) = 2 * (2 * 2 ^ j) := by ring
      push_cast
      rw [e4]
      rw [e3] at ih' hs ⊢
      linarith [ih', hs]
  have := claim J le_rfl
  rw [← ht, add_sub_cancel] at this
  exact this

lemma G_ge_neg_sq (xs : List ℝ) (t : ℝ) : -(xs.length : ℝ) * t ^ 2 / 2 ≤ G xs t := by
  have : 0 ≤ (xs.map fun a => max (t - a) 0).sum :=
    List.sum_nonneg (by simp only [List.mem_map]; rintro _ ⟨a, -, rfl⟩; exact le_max_right _ _)
  unfold G; linarith

lemma G_one_sub_le (xs : List ℝ) (t : ℝ) (ht : t ≤ 1) :
    G xs 1 - G xs t ≤ xs.length * (1 - t) ^ 2 / 2 := by
  have key : ∀ a ∈ xs, max (1 - a) 0 - max (t - a) 0 ≤ 1 - t := by
    intro a _
    rcases le_total (t - a) 0 with h | h
    · rw [max_eq_right h]
      rcases le_total (1 - a) 0 with h' | h'
      · rw [max_eq_right h']; linarith
      · rw [max_eq_left h']; linarith
    · rw [max_eq_left h, max_eq_left (by linarith)]; linarith
  have hdiff : (xs.map fun a => max (1 - a) 0).sum - (xs.map fun a => max (t - a) 0).sum
      = (xs.map fun a => max (1 - a) 0 - max (t - a) 0).sum := by
    clear key
    induction xs with
    | nil => simp
    | cons b bs ih => simp only [List.map_cons, List.sum_cons]; linarith
  have hle := sum_max_le_length_mul xs (fun a => max (1 - a) 0 - max (t - a) 0) (1 - t) key
  unfold G
  nlinarith

/-- Second differences from the repaired chord invariant (`μ = 1`). -/
lemma secondDiff_from (x : ℕ → ℝ) (m : ℕ) (hx : ∀ n, m ≤ n → IsGreedyStep (pref x n) (x n))
    (n : ℕ) (hn : m < n) :
    SecondDiffBoundCE (G (pref x n)) 2 ((m : ℝ) ^ 2 / (4 * ((n : ℝ) - m))) := by
  intro t h hh h0 h1
  have hnm : (m : ℝ) < n := by exact_mod_cast hn
  have hd : 0 < (1 : ℝ) * ((n : ℝ) - m) := by linarith
  rcases hh.eq_or_lt with rfl | hpos
  · simp only [add_zero, sub_zero, mul_zero, zero_add]
    have : 0 ≤ (m : ℝ) ^ 2 / (4 * ((n : ℝ) - m)) := by
      apply div_nonneg (sq_nonneg _); linarith
    linarith
  have hch := greedy_chordRepair x m 1 zero_le_one le_rfl hx n hn.le (t - h) t (t + h) h0
    (by linarith) (by linarith) h1 (by linarith)
  obtain ⟨q, hq0, hqp, hq⟩ := hch
  have hex := excess_le ((m : ℝ) / 2) _ q hd hq0
  have e1 : t + h - t = h := by ring
  have e2 : t - (t - h) = h := by ring
  have e3 : t + h - (t - h) = 2 * h := by ring
  unfold chordGap at hq
  rw [e1, e2, e3, Real.sqrt_mul_self hh] at hq
  have key : (h * G (pref x n) (t - h) + h * G (pref x n) (t + h)) / (2 * h)
      = (G (pref x n) (t - h) + G (pref x n) (t + h)) / 2 := by field_simp
  rw [key] at hq
  have eE : ((m : ℝ) / 2) ^ 2 / (2 * (1 * ((n : ℝ) - m))) = (m : ℝ) ^ 2 / (4 * ((n : ℝ) - m)) / 2 := by
    field_simp; ring
  rw [eE] at hex
  nlinarith

/-! ### Real-variable steps of the main proof -/

/-- A scale `h ∈ (1/(2n), 1/n]` with `2^J h = s` and `J ≤ ⌈log₂ n⌉`, for `1 < n s`, `s ≤ 1`. -/
lemma exists_scale (n : ℕ) (s : ℝ) (hs : 1 < (n : ℝ) * s) (hs1 : s ≤ 1) :
    ∃ J : ℕ, ∃ h : ℝ, 0 < h ∧ s = 2 ^ J * h ∧ (n : ℝ) * h ≤ 1 ∧ 1 < 2 * n * h ∧
      (J : ℝ) ≤ Nat.clog 2 n := by
  have hnpos : (0 : ℝ) < n := by
    rcases (Nat.cast_nonneg n : (0:ℝ) ≤ n).eq_or_lt with h | h
    · rw [← h] at hs; simp at hs; linarith
    · exact h
  have hspos : 0 < s := by
    by_contra hc; push Not at hc; nlinarith
  set J := Nat.clog 2 ⌈(n : ℝ) * s⌉₊
  have hc1 : 1 < ⌈(n : ℝ) * s⌉₊ := by
    rw [Nat.lt_ceil]; exact_mod_cast hs
  have hup : (n : ℝ) * s ≤ 2 ^ J := by
    have := Nat.le_pow_clog (by norm_num : 1 < 2) ⌈(n : ℝ) * s⌉₊
    calc (n : ℝ) * s ≤ ⌈(n : ℝ) * s⌉₊ := Nat.le_ceil _
      _ ≤ 2 ^ J := by exact_mod_cast this
  have hJ1 : 1 ≤ J := by
    have : 0 < Nat.clog 2 ⌈(n : ℝ) * s⌉₊ := Nat.clog_pos (by norm_num) hc1
    omega
  have hlow : (2 : ℝ) ^ J < 2 * ((n : ℝ) * s) := by
    have hlt := Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) hc1
    have hlt' : 2 ^ (J - 1) + 1 ≤ ⌈(n : ℝ) * s⌉₊ := hlt
    have hceil : (⌈(n : ℝ) * s⌉₊ : ℝ) < (n : ℝ) * s + 1 := Nat.ceil_lt_add_one (by positivity)
    have h3 : ((2 ^ (J - 1) : ℕ) : ℝ) + 1 ≤ ⌈(n : ℝ) * s⌉₊ := by exact_mod_cast hlt'
    have e2 : (2 : ℝ) ^ J = 2 * ((2 ^ (J - 1) : ℕ) : ℝ) := by
      push_cast; rw [← pow_succ']; congr 1; omega
    linarith
  have hJn : (J : ℝ) ≤ Nat.clog 2 n := by
    have : ⌈(n : ℝ) * s⌉₊ ≤ n := by rw [Nat.ceil_le]; nlinarith
    exact_mod_cast Nat.clog_mono_right 2 this
  have hpow : (0 : ℝ) < 2 ^ J := by positivity
  refine ⟨J, s / 2 ^ J, by positivity, by field_simp, ?_, ?_, hJn⟩
  · rw [mul_div_assoc', div_le_one hpow]; linarith
  · rw [mul_div_assoc', lt_div_iff₀ hpow]; linarith

lemma excess_small (n K δ Δ : ℝ) (hn : 0 < n) (u : ℝ) (hu : n * u = 1)
    (hmain : K * u - u / 2 ≤ Δ) (hΔ : Δ ≤ 3 * u / 2 + δ) : K ≤ 2 + n * δ := by
  have h1 : K * u ≤ 2 * u + δ := by linarith
  have h2 := mul_le_mul_of_nonneg_left h1 hn.le
  have e1 : n * (K * u) = K := by rw [mul_comm K u, ← mul_assoc, hu, one_mul]
  have e2 : n * (2 * u + δ) = 2 + n * δ := by rw [mul_add, ← mul_assoc, mul_comm n 2, mul_assoc, hu]; ring
  rw [e1, e2] at h2
  exact h2

lemma excess_big (n s K δ e J Jmax : ℝ) (_hn : 0 < n) (hs : 0 < s) (hns : 1 < n * s)
    (he : 0 ≤ e) (hδ : 0 ≤ δ) (P : ℝ) (_hP0 : 0 ≤ P) (hP : P ≤ 2 * n * s)
    (hJ : J ≤ Jmax)
    (hd : s * (K - 1 / 2 - 2 - 2 * J / 2) - e * (2 * P - 1) ≤ s / 2 + δ) :
    K ≤ Jmax + 3 + 4 * e * n + n * δ := by
  have h1 : e * (2 * P - 1) ≤ s * (4 * e * n) := by nlinarith
  have h2 : δ ≤ s * (n * δ) := by nlinarith
  have h3 : s * (K - 3 - J) ≤ s * (4 * e * n + n * δ) := by nlinarith
  have := le_of_mul_le_mul_left h3 hs
  linarith

/-- **Logarithmic star discrepancy from any start.** Let `x_0, …, x_{m−1} ∈ [0,1]`
(`m ≥ 1`) be arbitrary and every later term a greedy step. For `n ≥ 2m` and
`t ∈ [0,1]`, both `#{k<n : x_k ≤ t} − n t` and `n t − #{k<n : x_k < t}` are at
most `⌈log₂ n⌉ + 3 + 3 m²`. -/
theorem greedy_star_log_from (x : ℕ → ℝ) (m : ℕ) (hm : 1 ≤ m)
    (hrange : ∀ k, 0 ≤ x k ∧ x k ≤ 1)
    (hx : ∀ n, m ≤ n → IsGreedyStep (pref x n) (x n)) (n : ℕ) (hn : 2 * m ≤ n)
    (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    (countLE (pref x n) t : ℝ) - n * t ≤ Nat.clog 2 n + 3 + 3 * (m : ℝ) ^ 2 ∧
      n * t - (countBelow (pref x n) t : ℝ) ≤ Nat.clog 2 n + 3 + 3 * (m : ℝ) ^ 2 := by
  have hmn : m < n := by omega
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hnR : (2 * (m : ℝ)) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  set e : ℝ := (m : ℝ) ^ 2 / (4 * ((n : ℝ) - m)) with he
  set δ : ℝ := ((m : ℝ) - 1 / 2) ^ 2 / (2 * n) with hδ
  have hS := secondDiff_from x m hx n hmn
  have hxs : ∀ a ∈ pref x n, 0 ≤ a ∧ a ≤ 1 := by
    intro a ha
    simp only [pref, List.mem_map, List.mem_range] at ha
    obtain ⟨k, -, rfl⟩ := ha
    exact hrange k
  have hG0 : G (pref x n) 0 = 0 := G_zero_of_nonneg _ fun a ha => (hxs a ha).1
  have hlen : ((pref x n).length : ℝ) = n := by rw [length_pref]
  have hrep := fun s (hs0 : 0 ≤ s) (hs1 : s ≤ 1) =>
    envelope_repair x m hm (fun k _ => hrange k) hx n (by omega) s hs0 hs1
  -- the constants
  have hen : 4 * e * n ≤ 2 * (m : ℝ) ^ 2 := by
    rw [he]
    have hpos : 0 < 4 * ((n : ℝ) - m) := by linarith
    rw [show 4 * ((m : ℝ) ^ 2 / (4 * ((n : ℝ) - m))) * n = (m : ℝ) ^ 2 * n / ((n : ℝ) - m) by
      field_simp]
    rw [div_le_iff₀ (by linarith)]
    nlinarith [sq_nonneg (m : ℝ)]
  have hδn : n * δ ≤ (m : ℝ) ^ 2 / 2 := by
    rw [hδ, show (n : ℝ) * (((m : ℝ) - 1 / 2) ^ 2 / (2 * n)) = ((m : ℝ) - 1 / 2) ^ 2 / 2 by
      field_simp]
    nlinarith
  have he0 : 0 ≤ e := by rw [he]; apply div_nonneg (sq_nonneg _); linarith
  have hδ0 : 0 ≤ δ := by rw [hδ]; positivity
  constructor
  · set K := (countLE (pref x n) t : ℝ) - n * t with hK
    by_contra hcon
    push Not at hcon
    have hclog0 : (0 : ℝ) ≤ Nat.clog 2 n := Nat.cast_nonneg _
    have hK1 : 1 ≤ K := by linarith only [hcon, hclog0, sq_nonneg (m : ℝ)]
    have hcount := countLE_le_length (pref x n) t
    rw [hlen] at hcount
    have hnt : n * t ≤ n - 1 := by linarith only [hcount, hK1, hK]
    have hu : (n : ℝ) * (1 / n) = 1 := by field_simp
    rcases le_or_gt ((n : ℝ) * t) 1 with hsmall | hbig
    · have ht1 : t + 1 / n ≤ 1 := by
        have : (n : ℝ) * (t + 1 / n) ≤ n := by rw [mul_add, hu]; linarith only [hnt]
        by_contra hc; push Not at hc; nlinarith only [hc, this, hnpos]
      have hinc := G_increment_ge (pref x n) t (1 / n) (by positivity)
      rw [hlen, ← hK] at hinc
      have hA' := (hrep (t + 1 / n) (by positivity) ht1).1
      have hlow := G_ge_neg_sq (pref x n) t
      rw [hlen] at hlow
      have htu : t ≤ 1 / n := by rw [le_div_iff₀ hnpos]; linarith only [hsmall]
      have hnt2 : (n : ℝ) * t ^ 2 ≤ 1 / n := by
        have : (n : ℝ) * t ^ 2 ≤ t := by nlinarith only [hsmall, h0]
        linarith only [this, htu]
      have hsq : (n : ℝ) * (1 / n) ^ 2 = 1 / n := by field_simp
      rw [hsq] at hinc
      have := excess_small n K δ (G (pref x n) (t + 1 / n) - G (pref x n) t) hnpos (1 / n) hu
        (by linarith only [hinc])
        (by rw [hδ]; linarith only [hA', hlow, htu, hnt2])
      linarith only [this, hδn, hclog0, hcon, sq_nonneg (m : ℝ)]
    · obtain ⟨J, h, hh, ht, hnh, hn2h, hJ⟩ := exists_scale n t hbig h1
      have htpos : 0 < t := by rw [ht]; positivity
      have ht1 : t + h ≤ 1 := by
        have : (n : ℝ) * (t + h) ≤ n := by rw [mul_add]; linarith only [hnt, hnh]
        by_contra hc; push Not at hc; nlinarith only [hc, this, hnpos]
      have hinc := G_increment_ge (pref x n) t h hh.le
      rw [hlen, ← hK] at hinc
      have base : h * (K - 1 / 2) ≤ G (pref x n) (t + h) - G (pref x n) t := by
        have : (n : ℝ) * h ^ 2 / 2 ≤ h / 2 := by nlinarith only [hnh, hh]
        linarith only [hinc, this]
      have hd := dyadic_left_E (G (pref x n)) 2 e hS t h K J hh ht ht1 base
      rw [hG0, sub_zero] at hd
      have hA := (hrep t h0 h1).1
      have hP : (2 : ℝ) ^ J ≤ 2 * n * t := by
        have h2 := mul_le_mul_of_nonneg_left hn2h.le (by positivity : (0:ℝ) ≤ 2 ^ J)
        rw [ht]; nlinarith only [h2]
      have hpp : (2 : ℝ) ^ (J + 1) = 2 * 2 ^ J := by ring
      rw [hpp] at hd
      have := excess_big n t K δ e J (Nat.clog 2 n) hnpos htpos hbig he0 hδ0 (2 ^ J)
        (by positivity) hP hJ (by rw [hδ]; linarith only [hd, hA])
      linarith only [this, hen, hδn, hcon, sq_nonneg (m : ℝ)]
  · set K := (n : ℝ) * t - (countBelow (pref x n) t : ℝ) with hK
    by_contra hcon
    push Not at hcon
    have hclog0 : (0 : ℝ) ≤ Nat.clog 2 n := Nat.cast_nonneg _
    have hK1 : 1 ≤ K := by linarith only [hcon, hclog0, sq_nonneg (m : ℝ)]
    have hcb : (0 : ℝ) ≤ countBelow (pref x n) t := Nat.cast_nonneg _
    have hnt : 1 ≤ n * t := by linarith only [hK1, hK, hcb]
    have hu : (n : ℝ) * (1 / n) = 1 := by field_simp
    have htn : 1 / n ≤ t := by rw [div_le_iff₀ hnpos]; linarith only [hnt]
    rcases le_or_gt ((n : ℝ) * (1 - t)) 1 with hsmall | hbig
    · have ht0 : 0 ≤ t - 1 / n := by linarith only [htn]
      have hdec := G_decrement_le (pref x n) t (1 / n) (by positivity)
      rw [hlen] at hdec
      have hinvpos : (0:ℝ) ≤ 1 / n := by positivity
      have hC' := (hrep (t - 1 / n) ht0 (by linarith only [h1, hinvpos])).2
      have hone := G_one_sub_le (pref x n) t h1
      rw [hlen] at hone
      have hsu : 1 - t ≤ 1 / n := by rw [le_div_iff₀ hnpos]; linarith only [hsmall]
      have hone' : (n : ℝ) * (1 - t) ^ 2 / 2 ≤ 1 / n / 2 := by
        have : (n : ℝ) * (1 - t) ^ 2 ≤ 1 - t := by nlinarith only [hsmall, h1]
        linarith only [this, hsu]
      have hsq : (n : ℝ) * (1 / n) ^ 2 = 1 / n := by field_simp
      have hdec' : G (pref x n) t - G (pref x n) (t - 1 / n) ≤ -(K * (1 / n)) + 1 / n / 2 := by
        have e7 : 1 / (n : ℝ) * ((countBelow (pref x n) t : ℝ) - n * t) = -(K * (1 / n)) := by
          rw [hK]; ring
        rw [e7, hsq] at hdec; linarith only [hdec]
      have e6 : 1 - (t - 1 / (n : ℝ)) = (1 - t) + 1 / n := by ring
      rw [e6] at hC'
      have := excess_small n K δ (-(G (pref x n) t - G (pref x n) (t - 1 / n))) hnpos (1 / n) hu
        (by linarith only [hdec'])
        (by rw [hδ]; linarith only [hC', hone, hone', hsu])
      linarith only [this, hδn, hclog0, hcon, sq_nonneg (m : ℝ)]
    · obtain ⟨J, h, hh, ht, hnh, hn2h, hJ⟩ := exists_scale n (1 - t) hbig (by linarith only [h0])
      have hst : 0 < 1 - t := by rw [ht]; positivity
      have ht0 : 0 ≤ t - h := by
        have : h ≤ 1 / n := by rw [le_div_iff₀ hnpos]; linarith only [hnh]
        linarith only [this, htn]
      have hdec := G_decrement_le (pref x n) t h hh.le
      rw [hlen] at hdec
      have base : G (pref x n) t - G (pref x n) (t - h) ≤ h * (-K + 1 / 2) := by
        have : (n : ℝ) * h ^ 2 / 2 ≤ h / 2 := by nlinarith only [hnh, hh]
        have e7 : h * ((countBelow (pref x n) t : ℝ) - n * t) = h * (-K) := by rw [hK]; ring
        rw [e7] at hdec; linarith only [hdec, this]
      have hd := dyadic_right_E (G (pref x n)) 2 e hS t h K J hh ht ht0 base
      have hC := (hrep t h0 h1).2
      have hP : (2 : ℝ) ^ J ≤ 2 * n * (1 - t) := by
        have h2 := mul_le_mul_of_nonneg_left hn2h.le (by positivity : (0:ℝ) ≤ 2 ^ J)
        rw [ht]; nlinarith only [h2]
      have hpp : (2 : ℝ) ^ (J + 1) = 2 * 2 ^ J := by ring
      rw [hpp] at hd
      have := excess_big n (1 - t) K δ e J (Nat.clog 2 n) hnpos hst hbig he0 hδ0 (2 ^ J)
        (by positivity) hP hJ (by rw [hδ]; linarith only [hd, hC])
      linarith only [this, hen, hδn, hcon, sq_nonneg (m : ℝ)]

end GreedyDiscrepancy
