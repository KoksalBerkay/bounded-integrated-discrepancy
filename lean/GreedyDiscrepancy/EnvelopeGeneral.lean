import GreedyDiscrepancy.Envelope

/-!
# The envelope from an arbitrary initial set

Steinerberger (arXiv:2207.08043) considers Kritzinger sequences started from an
arbitrary finite initial set. The algebra of `envelope_step` shows more than
invariance: the amounts by which `G` exceeds the two envelopes,

  `sup_t (G_N t − t/2)`  and  `sup_t (G_N t − G_N 1 − (1−t)/2)`,

never increase under a greedy step, whatever the current point set is. Hence,
from any initial points `x_0, …, x_{m−1} ∈ [0,1]` followed by greedy steps,
`G_N t ≤ t/2 + e_A` and `G_N t ≤ G_N 1 + (1−t)/2 + e_C` for all `N ≥ m`,
where `e_A, e_C` bound the initial excesses.
-/

namespace GreedyDiscrepancy

/-- One greedy step does not increase the excess over either envelope. -/
theorem envelope_step_excess {xs : List ℝ} {x : ℝ} (hx : IsGreedyStep xs x) (eA eC : ℝ)
    (hA : ∀ t, 0 ≤ t → t ≤ 1 → G xs t ≤ t / 2 + eA)
    (hC : ∀ t, 0 ≤ t → t ≤ 1 → G xs t ≤ G xs 1 + (1 - t) / 2 + eC) :
    (∀ t, 0 ≤ t → t ≤ 1 → G (xs ++ [x]) t ≤ t / 2 + eA) ∧
    (∀ t, 0 ≤ t → t ≤ 1 → G (xs ++ [x]) t ≤ G (xs ++ [x]) 1 + (1 - t) / 2 + eC) := by
  have hx0 := hx.1
  have hx1 := hx.2.1
  have h1x : max (1 - x) 0 = 1 - x := max_eq_left (by linarith)
  refine ⟨fun t h0 h1 => ?_, fun t h0 h1 => ?_⟩
  · rw [G_append]
    rcases le_total t x with htx | htx
    · rw [max_eq_right (by linarith)]
      have := hA t h0 h1
      nlinarith [sq_nonneg t]
    · rw [max_eq_left (by linarith)]
      have hm := greedy_max hx h0 h1
      have := hA x hx0 hx1
      nlinarith [sq_nonneg x]
  · rw [G_append, G_append, h1x]
    rcases le_total t x with htx | htx
    · rw [max_eq_right (by linarith)]
      have hm := greedy_max hx h0 h1
      have := hC x hx0 hx1
      nlinarith [sq_nonneg (x - 1)]
    · rw [max_eq_left (by linarith)]
      have := hC t h0 h1
      nlinarith [sq_nonneg (1 - t)]

/-- **Envelope from an arbitrary start.** If `x_0, …, x_{m−1}` are arbitrary and
every later term is a greedy step, the initial excesses `eA`, `eC` bound the
excess at every later time. -/
theorem envelope_from (x : ℕ → ℝ) (m : ℕ) (eA eC : ℝ)
    (hx : ∀ n, m ≤ n → IsGreedyStep (pref x n) (x n))
    (hA : ∀ t, 0 ≤ t → t ≤ 1 → G (pref x m) t ≤ t / 2 + eA)
    (hC : ∀ t, 0 ≤ t → t ≤ 1 → G (pref x m) t ≤ G (pref x m) 1 + (1 - t) / 2 + eC) :
    ∀ n, m ≤ n →
      (∀ t, 0 ≤ t → t ≤ 1 → G (pref x n) t ≤ t / 2 + eA) ∧
      (∀ t, 0 ≤ t → t ≤ 1 → G (pref x n) t ≤ G (pref x n) 1 + (1 - t) / 2 + eC) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact ⟨hA, hC⟩
  | succ n hmn ih =>
    rw [pref_succ]
    exact envelope_step_excess (hx n hmn) eA eC ih.1 ih.2

/-- Consequence: from an arbitrary start in `[0,1]`, the sum of the first `n`
terms stays within `1/2 + max(eA, eC)` of `n/2`, and `G_n ≤ 1/2 + eA`. -/
theorem sum_near_half_from (x : ℕ → ℝ) (m : ℕ) (eA eC : ℝ)
    (hrange : ∀ k, 0 ≤ x k ∧ x k ≤ 1)
    (hx : ∀ n, m ≤ n → IsGreedyStep (pref x n) (x n))
    (hA : ∀ t, 0 ≤ t → t ≤ 1 → G (pref x m) t ≤ t / 2 + eA)
    (hC : ∀ t, 0 ≤ t → t ≤ 1 → G (pref x m) t ≤ G (pref x m) 1 + (1 - t) / 2 + eC)
    (n : ℕ) (hn : m ≤ n) :
    (pref x n).sum - n / 2 ≤ 1 / 2 + eC ∧ n / 2 - (pref x n).sum ≤ 1 / 2 + eA := by
  obtain ⟨hA', hC'⟩ := envelope_from x m eA eC hx hA hC n hn
  have h1 := hA' 1 (by norm_num) le_rfl
  have h0 := hC' 0 le_rfl (by norm_num)
  have hxs : ∀ a ∈ pref x n, 0 ≤ a ∧ a ≤ 1 := by
    intro a ha
    simp only [pref, List.mem_map, List.mem_range] at ha
    obtain ⟨k, -, rfl⟩ := ha
    exact hrange k
  have hG1 : G (pref x n) 1 = n / 2 - (pref x n).sum := by
    have : ((pref x n).map fun a => max (1 - a) 0).sum =
        ((pref x n).map fun a => 1 - a).sum := by
      congr 1
      apply List.map_congr_left
      intro a ha
      exact max_eq_left (by linarith [(hxs a ha).2])
    have hl : ((pref x n).length : ℝ) = n := by simp [pref]
    unfold G
    rw [this, sum_one_sub, hl]
    ring
  have hG0 : G (pref x n) 0 = 0 := by
    have : ((pref x n).map fun a => max (0 - a) 0).sum =
        ((pref x n).map fun _ => (0:ℝ)).sum := by
      congr 1
      apply List.map_congr_left
      intro a ha
      exact max_eq_right (by linarith [(hxs a ha).1])
    unfold G
    rw [this]
    simp
  constructor <;> linarith

end GreedyDiscrepancy
