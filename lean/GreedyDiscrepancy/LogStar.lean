import GreedyDiscrepancy.StarDiscrepancy

/-!
# The star discrepancy is `O(log N)` (Kritzinger's conjecture)

The chord invariant (`greedy_chord_deficit_sharp`) with `a = t − h`, `b = t + h`
says that the second differences of `G` are small:

  `G(t+h) + G(t−h) − 2 G(t) ≤ 2h`,

i.e. the average of `D` over `[t, t+h]` exceeds its average over `[t−h, t]` by
at most `2`, at every scale `h`. If `D(t₀) = K`, then `D ≥ K − 1/2` on average
just to the right of `t₀` (at scale `≤ 1/N`), so the average of `D` on the
dyadic intervals `[t₀ − 2^j h, t₀]` is at least `K − 5/2 − j`. Taking
`2^J h = t₀` gives `G(t₀) ≥ t₀ (K − 5/2 − J)`, and `G(t₀) ≤ t₀/2` forces
`K ≤ J + 3`. With `J = ⌈log₂ N⌉` (so `2^J ≥ N`) this is `K ≤ ⌈log₂ N⌉ + 3 ≤ log₂ N + 4`. Deficits are symmetric,
using the other envelope.

Main results:
* `greedy_star_log`: for every greedy `L²` sequence started from the empty set,
  `|#{k < n : x_k ≤ t} − n t| ≤ J + 3` and `|#{k < n : x_k < t} − n t| ≤ J + 3`
  whenever `n ≤ 2^J`;
* `kritzinger_conjecture_holds : KritzingerConjecture`.
-/

namespace GreedyDiscrepancy

/-- Second-difference form of the chord invariant. -/
def SecondDiffBound (G : ℝ → ℝ) : Prop :=
  ∀ t h : ℝ, 0 ≤ h → 0 ≤ t - h → t + h ≤ 1 → G (t + h) + G (t - h) - 2 * G t ≤ 2 * h

lemma greedy_secondDiff (x : ℕ → ℝ) (hx : ∀ n, IsGreedyStep (pref x n) (x n)) (n : ℕ) :
    SecondDiffBound (G (pref x n)) := by
  intro t h hh h0 h1
  rcases hh.eq_or_lt with rfl | hpos
  · simp only [add_zero, sub_zero]; linarith
  have hc := greedy_chord_deficit_sharp x hx n (t - h) t (t + h) h0 (by linarith)
    (by linarith) h1 (by linarith)
  have e1 : t + h - t = h := by ring
  have e2 : t - (t - h) = h := by ring
  have e3 : t + h - (t - h) = 2 * h := by ring
  rw [e1, e2, e3] at hc
  have hs : Real.sqrt (h * h) = h := Real.sqrt_mul_self hh
  rw [hs] at hc
  have key : (h * G (pref x n) (t - h) + h * G (pref x n) (t + h)) / (2 * h)
      = (G (pref x n) (t - h) + G (pref x n) (t + h)) / 2 := by
    field_simp
  rw [key] at hc
  nlinarith

/-- Dyadic propagation of an excess to the left, ending at `0`. -/
lemma dyadic_left (G : ℝ → ℝ) (hS : SecondDiffBound G) (t₀ h K : ℝ) (J : ℕ)
    (hh : 0 < h) (ht : t₀ = 2 ^ J * h) (ht1 : t₀ + h ≤ 1)
    (base : h * (K - 1 / 2) ≤ G (t₀ + h) - G t₀) :
    t₀ * (K - 5 / 2 - J) ≤ G t₀ - G 0 := by
  have claim : ∀ j : ℕ, j ≤ J →
      2 ^ j * h * (K - 5 / 2 - j) ≤ G t₀ - G (t₀ - 2 ^ j * h) := by
    intro j
    induction j with
    | zero =>
      intro _
      have hpow : (1 : ℝ) ≤ 2 ^ J := one_le_pow₀ (by norm_num)
      have h0 : 0 ≤ t₀ - h := by rw [ht]; nlinarith
      have := hS t₀ h hh.le h0 ht1
      simp only [pow_zero, one_mul, Nat.cast_zero, sub_zero]
      linarith
    | succ j ih =>
      intro hj
      have ih' := ih (by omega)
      have hpj : (2 : ℝ) ^ (j + 1) ≤ 2 ^ J := pow_le_pow_right₀ (by norm_num) hj
      have hH : 0 ≤ 2 ^ j * h := by positivity
      have h0 : 0 ≤ (t₀ - 2 ^ j * h) - 2 ^ j * h := by
        rw [ht]; have : (2:ℝ) ^ (j + 1) = 2 * 2 ^ j := by ring
        nlinarith
      have h1 : (t₀ - 2 ^ j * h) + 2 ^ j * h ≤ 1 := by linarith
      have hs := hS (t₀ - 2 ^ j * h) (2 ^ j * h) hH h0 h1
      have e1 : t₀ - 2 ^ j * h + 2 ^ j * h = t₀ := by ring
      have e2 : t₀ - 2 ^ j * h - 2 ^ j * h = t₀ - 2 ^ (j + 1) * h := by ring
      rw [e1, e2] at hs
      push_cast
      have e3 : (2 : ℝ) ^ (j + 1) = 2 * 2 ^ j := by ring
      rw [e3] at hs ⊢
      nlinarith
  have := claim J le_rfl
  rw [← ht, sub_self] at this
  exact this

/-- Dyadic propagation of a deficit to the right, ending at `1`. -/
lemma dyadic_right (G : ℝ → ℝ) (hS : SecondDiffBound G) (t₀ h K : ℝ) (J : ℕ)
    (hh : 0 < h) (ht : 1 - t₀ = 2 ^ J * h) (ht0 : 0 ≤ t₀ - h)
    (base : G t₀ - G (t₀ - h) ≤ h * (-K + 1 / 2)) :
    G 1 - G t₀ ≤ (1 - t₀) * (-K + 5 / 2 + J) := by
  have claim : ∀ j : ℕ, j ≤ J →
      G (t₀ + 2 ^ j * h) - G t₀ ≤ 2 ^ j * h * (-K + 5 / 2 + j) := by
    intro j
    induction j with
    | zero =>
      intro _
      have hpow : (1 : ℝ) ≤ 2 ^ J := one_le_pow₀ (by norm_num)
      have h1 : t₀ + h ≤ 1 := by nlinarith
      have := hS t₀ h hh.le ht0 h1
      simp only [pow_zero, one_mul, Nat.cast_zero, add_zero]
      linarith
    | succ j ih =>
      intro hj
      have ih' := ih (by omega)
      have hpj : (2 : ℝ) ^ (j + 1) ≤ 2 ^ J := pow_le_pow_right₀ (by norm_num) hj
      have hH : 0 ≤ 2 ^ j * h := by positivity
      have h0 : 0 ≤ (t₀ + 2 ^ j * h) - 2 ^ j * h := by linarith
      have h1 : (t₀ + 2 ^ j * h) + 2 ^ j * h ≤ 1 := by
        have : (2:ℝ) ^ (j + 1) = 2 * 2 ^ j := by ring
        nlinarith
      have hs := hS (t₀ + 2 ^ j * h) (2 ^ j * h) hH h0 h1
      have e1 : t₀ + 2 ^ j * h - 2 ^ j * h = t₀ := by ring
      have e2 : t₀ + 2 ^ j * h + 2 ^ j * h = t₀ + 2 ^ (j + 1) * h := by ring
      rw [e1, e2] at hs
      push_cast
      have e3 : (2 : ℝ) ^ (j + 1) = 2 * 2 ^ j := by ring
      rw [e3] at hs ⊢
      nlinarith
  have := claim J le_rfl
  rw [← ht, add_sub_cancel] at this
  exact this

/-- **Logarithmic star discrepancy.** For every greedy `L²` sequence started from
the empty set (any tie-break), every `n`, every `J` with `n ≤ 2^J` and every
`t ∈ [0,1]`: `#{k < n : x_k ≤ t} − n t ≤ J + 3` and `n t − #{k < n : x_k < t} ≤ J + 3`. -/
theorem greedy_star_log (x : ℕ → ℝ) (hx : ∀ n, IsGreedyStep (pref x n) (x n)) (n J : ℕ)
    (hJ : (n : ℝ) ≤ 2 ^ J) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    (countLE (pref x n) t : ℝ) - n * t ≤ J + 3 ∧
      n * t - (countBelow (pref x n) t : ℝ) ≤ J + 3 := by
  have hS := greedy_secondDiff x hx n
  have hA := (envelope x hx n).1
  have hC := (envelope x hx n).2
  have hG0 : G (pref x n) 0 = 0 := greedy_G_zero x hx n
  have hlen : ((pref x n).length : ℝ) = n := by rw [length_pref]
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  have hpow : (0 : ℝ) < 2 ^ J := by positivity
  constructor
  · set K := (countLE (pref x n) t : ℝ) - n * t with hK
    by_contra hcon
    push Not at hcon
    have hK1 : 1 ≤ K := by linarith
    have hcount := countLE_le_length (pref x n) t
    rw [hlen] at hcount
    have hnpos : (0 : ℝ) < n := by nlinarith
    have hnt : n * t ≤ n - 1 := by linarith
    have hinv : (1 : ℝ) / n * n = 1 := by field_simp
    rcases h0.eq_or_lt with rfl | htpos
    · -- t = 0: one step of length 1/n
      have hinc := G_increment_ge (pref x n) 0 (1 / n) (by positivity)
      rw [hlen, zero_add] at hinc
      have hA' := hA (1 / n) (by positivity) (by rw [div_le_one hnpos]; linarith)
      rw [hG0] at hinc
      have e : (1 / (n : ℝ)) * ((countLE (pref x n) 0 : ℝ) - n * 0) - n * (1 / n) ^ 2 / 2
          = (K - 1 / 2) / n := by rw [hK]; field_simp; try ring
      rw [e] at hinc
      have : (K - 1 / 2) / n ≤ 1 / n / 2 := by linarith
      rw [div_le_iff₀ hnpos] at this
      have e2 : 1 / (n : ℝ) / 2 * n = 1 / 2 := by field_simp
      rw [e2] at this
      linarith
    · set h := t / 2 ^ J with hhdef
      have hhpos : 0 < h := div_pos htpos hpow
      have ht : t = 2 ^ J * h := by rw [hhdef]; field_simp
      have hnh : n * h ≤ 1 := by
        rw [hhdef, mul_div_assoc', div_le_one hpow]
        nlinarith
      have ht1 : t + h ≤ 1 := by
        have : h ≤ 1 / n := by rw [le_div_iff₀ hnpos]; linarith
        have : n * (t + h) ≤ n := by nlinarith
        nlinarith
      have hinc := G_increment_ge (pref x n) t h hhpos.le
      rw [hlen] at hinc
      have base : h * (K - 1 / 2) ≤ G (pref x n) (t + h) - G (pref x n) t := by
        have : (n : ℝ) * h ^ 2 / 2 ≤ h / 2 := by nlinarith
        rw [hK]; nlinarith
      have hd := dyadic_left (G (pref x n)) hS t h K J hhpos ht ht1 base
      rw [hG0, sub_zero] at hd
      have := hA t h0 h1
      have : t * (K - 5 / 2 - J) ≤ t * (1 / 2) := by linarith
      have := le_of_mul_le_mul_left this htpos
      linarith
  · set K := (n : ℝ) * t - (countBelow (pref x n) t : ℝ) with hK
    by_contra hcon
    push Not at hcon
    have hK1 : 1 ≤ K := by linarith
    have hcb : (0 : ℝ) ≤ countBelow (pref x n) t := Nat.cast_nonneg _
    have hnpos : (0 : ℝ) < n := by
      rcases (Nat.cast_nonneg n : (0:ℝ) ≤ n).eq_or_lt with h | h
      · rw [← h] at hK; simp at hK; linarith
      · exact h
    have hnt : 1 ≤ n * t := by linarith
    rcases h1.eq_or_lt with rfl | htlt
    · -- t = 1: one step of length 1/n to the left
      have hdec := G_decrement_le (pref x n) 1 (1 / n) (by positivity)
      rw [hlen] at hdec
      have hc := hC (1 - 1 / n) (by rw [sub_nonneg, div_le_one hnpos]; linarith)
        (by have : (0:ℝ) ≤ 1 / n := by positivity
            linarith)
      have e : (1 / (n : ℝ)) * ((countBelow (pref x n) 1 : ℝ) - n * 1) + n * (1 / n) ^ 2 / 2
          = (-K + 1 / 2) / n := by rw [hK]; field_simp; try ring
      rw [e] at hdec
      have e2 : (1 : ℝ) - (1 - 1 / n) = 1 / n := by ring
      rw [e2] at hc
      have : -(1 / (n : ℝ)) / 2 ≤ (-K + 1 / 2) / n := by linarith
      rw [le_div_iff₀ hnpos] at this
      have e3 : -(1 / (n : ℝ)) / 2 * n = -(1 / 2) := by field_simp
      rw [e3] at this
      linarith
    · set h := (1 - t) / 2 ^ J with hhdef
      have hhpos : 0 < h := div_pos (by linarith) hpow
      have ht : 1 - t = 2 ^ J * h := by rw [hhdef]; field_simp
      have hnh : n * h ≤ 1 := by
        rw [hhdef, mul_div_assoc', div_le_one hpow]
        nlinarith
      have ht0 : 0 ≤ t - h := by
        have : h ≤ 1 / n := by rw [le_div_iff₀ hnpos]; linarith
        have : (1 : ℝ) / n ≤ t := by rw [div_le_iff₀ hnpos]; linarith
        linarith
      have hdec := G_decrement_le (pref x n) t h hhpos.le
      rw [hlen] at hdec
      have base : G (pref x n) t - G (pref x n) (t - h) ≤ h * (-K + 1 / 2) := by
        have : (n : ℝ) * h ^ 2 / 2 ≤ h / 2 := by nlinarith
        rw [hK]; nlinarith
      have hd := dyadic_right (G (pref x n)) hS t h K J hhpos ht ht0 base
      have := hC t h0 h1
      have : (1 - t) * (-(1 / 2)) ≤ (1 - t) * (-K + 5 / 2 + J) := by linarith
      have := le_of_mul_le_mul_left this (by linarith)
      linarith

/-- With `J = ⌊log₂ n⌋ + 1`: `|#{k < n : x_k < t} − n t| ≤ log₂ n + 4`, stated
with natural logarithms as `≤ 5 log n / log 2` for `n ≥ 2`. -/
theorem greedy_star_le_log (x : ℕ → ℝ) (hx : ∀ n, IsGreedyStep (pref x n) (x n)) (n : ℕ)
    (hn : 2 ≤ n) : StarDiscLE (pref x n) (5 / Real.log 2 * Real.log n) := by
  intro t h0 h1
  set J := Nat.log 2 n + 1 with hJdef
  have hnJ : n < 2 ^ J := Nat.lt_pow_succ_log_self (by norm_num) n
  have hJn : 2 ^ (J - 1) ≤ n := by
    rw [hJdef, Nat.add_sub_cancel]; exact Nat.pow_log_le_self 2 (by omega)
  have hJR : (n : ℝ) ≤ 2 ^ J := by exact_mod_cast hnJ.le
  obtain ⟨hpos, hneg⟩ := greedy_star_log x hx n J hJR t h0 h1
  rw [length_pref]
  have hle : (countBelow (pref x n) t : ℝ) ≤ countLE (pref x n) t := by
    have : (pref x n).countP (fun a => decide (a < t)) ≤
        (pref x n).countP (fun a => decide (a ≤ t)) :=
      List.countP_mono_left fun a _ ha => by simp at ha ⊢; linarith
    exact_mod_cast this
  -- J + 3 ≤ 5 log n / log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hJ1 : 1 ≤ J := by omega
  have hkey : (2 : ℝ) ^ (J + 3) ≤ (n : ℝ) ^ 5 := by
    have h2 : (2 : ℝ) ^ (J - 1) ≤ n := by exact_mod_cast hJn
    have e : (2 : ℝ) ^ (J + 3) = 16 * 2 ^ (J - 1) := by
      rw [show J + 3 = (J - 1) + 4 by omega, pow_add]; ring
    rw [e]
    have hn4 : (16 : ℝ) ≤ (n : ℝ) ^ 4 := by
      have : (2 : ℝ) ^ 4 ≤ (n : ℝ) ^ 4 := pow_le_pow_left₀ (by norm_num) hnR 4
      norm_num at this; linarith
    have : (n : ℝ) ^ 5 = (n : ℝ) ^ 4 * n := by ring
    rw [this]
    have h2' : (0 : ℝ) ≤ 2 ^ (J - 1) := by positivity
    nlinarith
  have hlogle := Real.log_le_log (by positivity) hkey
  rw [Real.log_pow, Real.log_pow] at hlogle
  have hbound : (J : ℝ) + 3 ≤ 5 / Real.log 2 * Real.log n := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    push_cast at hlogle
    linarith
  rw [abs_le]
  constructor <;> linarith

/-- **Kritzinger's conjecture holds**: the star discrepancy of the first `n`
points of Kritzinger's sequence is `O(log n)`. -/
theorem kritzinger_conjecture_holds : KritzingerConjecture := by
  intro x hx
  exact ⟨5 / Real.log 2, fun n hn => greedy_star_le_log x (kritzinger_greedy x hx) n hn⟩

end GreedyDiscrepancy
