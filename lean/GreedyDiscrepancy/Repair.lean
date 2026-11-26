import GreedyDiscrepancy.EnvelopeGeneral

/-!
# Bad starts are repaired: the excess over the envelopes decays like `1/N`

`EnvelopeGeneral` shows that the excesses of `G` over the two envelopes
`t/2` and `G 1 + (1−t)/2` never increase. Here we show that they decay.
The algebra of `envelope_step` gives, for a greedy step at `x`,

  `G' t − t/2 ≤ (G s − s/2) − s²/2`     with `s = min t x`,

so after `k` steps the excess at `t` is at most `max_{s ≤ t} (e₀ s − k s²/2)`.
For an initial list of `m ≥ 1` points in `[0,1]` the initial excess is at most
`(m − 1/2) s − m s²/2`, and we get, for every `N ≥ m` and `t ∈ [0,1]`,

  `G_N t ≤ t/2 + (m − 1/2)² / (2N)`  and
  `G_N t ≤ G_N 1 + (1−t)/2 + (m − 1/2)² / (2N)`.

Consequences: `G_N ≤ 1/2 + (m−1/2)²/(2N)` and
`|Σ_{k<N} x_k − N/2| ≤ 1/2 + (m−1/2)²/(2N)`, for every initial list.
-/

namespace GreedyDiscrepancy

lemma length_append_one (xs : List ℝ) (x : ℝ) :
    ((xs ++ [x]).length : ℝ) = xs.length + 1 := by simp

/-- Decay of the excess over `t/2` in one greedy step. -/
lemma repairA_step {xs : List ℝ} {x : ℝ} (hx : IsGreedyStep xs x) (c : ℝ)
    (h : ∀ t, 0 ≤ t → t ≤ 1 → ∃ s, 0 ≤ s ∧ s ≤ t ∧
      G xs t - t / 2 ≤ c * s - xs.length * s ^ 2 / 2) :
    ∀ t, 0 ≤ t → t ≤ 1 → ∃ s, 0 ≤ s ∧ s ≤ t ∧
      G (xs ++ [x]) t - t / 2 ≤ c * s - (xs ++ [x]).length * s ^ 2 / 2 := by
  intro t h0 h1
  rw [length_append_one, G_append]
  have hx0 := hx.1
  have hx1 := hx.2.1
  rcases le_total t x with htx | htx
  · obtain ⟨s, hs0, hst, hs⟩ := h t h0 h1
    refine ⟨s, hs0, hst, ?_⟩
    rw [max_eq_right (by linarith)]
    have : s ^ 2 ≤ t ^ 2 := by nlinarith
    nlinarith
  · obtain ⟨s, hs0, hsx, hs⟩ := h x hx0 hx1
    refine ⟨s, hs0, hsx.trans htx, ?_⟩
    rw [max_eq_left (by linarith)]
    have hm := greedy_max hx h0 h1
    have : s ^ 2 ≤ x ^ 2 := by nlinarith
    nlinarith

/-- Decay of the excess over `G 1 + (1−t)/2` in one greedy step. -/
lemma repairC_step {xs : List ℝ} {x : ℝ} (hx : IsGreedyStep xs x) (c : ℝ)
    (h : ∀ t, 0 ≤ t → t ≤ 1 → ∃ s, t ≤ s ∧ s ≤ 1 ∧
      G xs t - G xs 1 - (1 - t) / 2 ≤ c * (1 - s) - xs.length * (1 - s) ^ 2 / 2) :
    ∀ t, 0 ≤ t → t ≤ 1 → ∃ s, t ≤ s ∧ s ≤ 1 ∧
      G (xs ++ [x]) t - G (xs ++ [x]) 1 - (1 - t) / 2
        ≤ c * (1 - s) - (xs ++ [x]).length * (1 - s) ^ 2 / 2 := by
  intro t h0 h1
  rw [length_append_one, G_append, G_append]
  have hx0 := hx.1
  have hx1 := hx.2.1
  have h1x : max (1 - x) 0 = 1 - x := max_eq_left (by linarith)
  rw [h1x]
  rcases le_total x t with hxt | hxt
  · obtain ⟨s, hts, hs1, hs⟩ := h t h0 h1
    refine ⟨s, hts, hs1, ?_⟩
    rw [max_eq_left (by linarith)]
    have : (1 - s) ^ 2 ≤ (1 - t) ^ 2 := by nlinarith
    nlinarith
  · obtain ⟨s, hxs, hs1, hs⟩ := h x hx0 hx1
    refine ⟨s, hxt.trans hxs, hs1, ?_⟩
    rw [max_eq_right (by linarith)]
    have hm := greedy_max hx h0 h1
    have : (1 - s) ^ 2 ≤ (1 - x) ^ 2 := by nlinarith
    nlinarith

lemma sum_max_le_length_mul (xs : List ℝ) (f : ℝ → ℝ) (B : ℝ) (hB : ∀ a ∈ xs, f a ≤ B) :
    (xs.map f).sum ≤ xs.length * B := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_succ]
    have := hB a (by simp)
    have := ih fun b hb => hB b (by simp [hb])
    linarith

/-- Initial excess over `t/2` for points in `[0, ∞)`. -/
lemma repairA_base (xs : List ℝ) (hxs : ∀ a ∈ xs, 0 ≤ a) (t : ℝ) (h0 : 0 ≤ t) :
    G xs t - t / 2 ≤ (xs.length - 1 / 2) * t - xs.length * t ^ 2 / 2 := by
  have := sum_max_le_length_mul xs (fun a => max (t - a) 0) t fun a ha =>
    max_le (by linarith [hxs a ha]) h0
  unfold G
  nlinarith

/-- Initial excess over `G 1 + (1−t)/2` for points in `(−∞, 1]`. -/
lemma repairC_base (xs : List ℝ) (hxs : ∀ a ∈ xs, a ≤ 1) (t : ℝ) (h1 : t ≤ 1) :
    G xs t - G xs 1 - (1 - t) / 2
      ≤ (xs.length - 1 / 2) * (1 - t) - xs.length * (1 - t) ^ 2 / 2 := by
  have key : ∀ a ∈ xs, max (t - a) 0 - max (1 - a) 0 ≤ 0 := fun a _ =>
    sub_nonpos.2 (max_le_max (by linarith) le_rfl)
  have hdiff : (xs.map fun a => max (t - a) 0).sum - (xs.map fun a => max (1 - a) 0).sum
      = (xs.map fun a => max (t - a) 0 - max (1 - a) 0).sum := by
    clear key
    induction xs with
    | nil => simp
    | cons b bs ih =>
      simp only [List.map_cons, List.sum_cons]
      have := ih fun a ha => hxs a (by simp [ha])
      linarith
  have hle := sum_max_le_length_mul xs (fun a => max (t - a) 0 - max (1 - a) 0) 0 key
  unfold G
  nlinarith

lemma quad_le (c N s : ℝ) (hN : 0 < N) : c * s - N * s ^ 2 / 2 ≤ c ^ 2 / (2 * N) := by
  rw [le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (N * s - c)]

/-- **Repair theorem.** Let `x_0, …, x_{m−1} ∈ [0,1]` be arbitrary (`m ≥ 1`) and
let every later term be a greedy step. Then for all `n ≥ m` and `t ∈ [0,1]`,
`G_n t ≤ t/2 + (m−1/2)²/(2n)` and `G_n t ≤ G_n 1 + (1−t)/2 + (m−1/2)²/(2n)`. -/
theorem envelope_repair (x : ℕ → ℝ) (m : ℕ) (hm : 1 ≤ m)
    (hrange : ∀ k, k < m → 0 ≤ x k ∧ x k ≤ 1)
    (hx : ∀ n, m ≤ n → IsGreedyStep (pref x n) (x n)) (n : ℕ) (hn : m ≤ n)
    (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    G (pref x n) t ≤ t / 2 + ((m : ℝ) - 1 / 2) ^ 2 / (2 * n) ∧
      G (pref x n) t ≤ G (pref x n) 1 + (1 - t) / 2 + ((m : ℝ) - 1 / 2) ^ 2 / (2 * n) := by
  set c : ℝ := (m : ℝ) - 1 / 2
  have hmem : ∀ a ∈ pref x m, 0 ≤ a ∧ a ≤ 1 := by
    intro a ha
    simp only [pref, List.mem_map, List.mem_range] at ha
    obtain ⟨k, hk, rfl⟩ := ha
    exact hrange k hk
  have hlen : ∀ k, ((pref x k).length : ℝ) = k := fun k => by simp [pref]
  -- invariants
  have IA : ∀ k, m ≤ k → ∀ t, 0 ≤ t → t ≤ 1 → ∃ s, 0 ≤ s ∧ s ≤ t ∧
      G (pref x k) t - t / 2 ≤ c * s - (pref x k).length * s ^ 2 / 2 := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      intro t h0 _
      refine ⟨t, h0, le_rfl, ?_⟩
      have := repairA_base (pref x m) (fun a ha => (hmem a ha).1) t h0
      rw [hlen] at this ⊢
      exact this
    | succ k hmk ih =>
      rw [pref_succ]
      exact repairA_step (hx k hmk) c ih
  have IC : ∀ k, m ≤ k → ∀ t, 0 ≤ t → t ≤ 1 → ∃ s, t ≤ s ∧ s ≤ 1 ∧
      G (pref x k) t - G (pref x k) 1 - (1 - t) / 2
        ≤ c * (1 - s) - (pref x k).length * (1 - s) ^ 2 / 2 := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base =>
      intro t _ h1
      refine ⟨t, le_rfl, h1, ?_⟩
      have := repairC_base (pref x m) (fun a ha => (hmem a ha).2) t h1
      rw [hlen] at this ⊢
      exact this
    | succ k hmk ih =>
      rw [pref_succ]
      exact repairC_step (hx k hmk) c ih
  have hnpos : (0 : ℝ) < n := by
    have : (1 : ℝ) ≤ n := by exact_mod_cast hm.trans hn
    linarith
  obtain ⟨s, -, -, hs⟩ := IA n hn t h0 h1
  obtain ⟨s', -, -, hs'⟩ := IC n hn t h0 h1
  rw [hlen] at hs hs'
  have q1 := quad_le c n s hnpos
  have q2 := quad_le c n (1 - s') hnpos
  constructor <;> linarith

/-- Corollary: from any initial list of `m ≥ 1` points in `[0,1]`,
`G_n ≤ 1/2 + (m−1/2)²/(2n)` and `|Σ_{k<n} x_k − n/2| ≤ 1/2 + (m−1/2)²/(2n)`. -/
theorem repair_consequences (x : ℕ → ℝ) (m : ℕ) (hm : 1 ≤ m)
    (hrange : ∀ k, 0 ≤ x k ∧ x k ≤ 1)
    (hx : ∀ n, m ≤ n → IsGreedyStep (pref x n) (x n)) (n : ℕ) (hn : m ≤ n) :
    (∀ t, 0 ≤ t → t ≤ 1 → G (pref x n) t ≤ 1 / 2 + ((m : ℝ) - 1 / 2) ^ 2 / (2 * n)) ∧
      |(pref x n).sum - n / 2| ≤ 1 / 2 + ((m : ℝ) - 1 / 2) ^ 2 / (2 * n) := by
  have hr : ∀ k, k < m → 0 ≤ x k ∧ x k ≤ 1 := fun k _ => hrange k
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
  refine ⟨fun t h0 h1 => ?_, ?_⟩
  · have := (envelope_repair x m hm hr hx n hn t h0 h1).1
    linarith
  · have hA := (envelope_repair x m hm hr hx n hn 1 zero_le_one le_rfl).1
    have hC := (envelope_repair x m hm hr hx n hn 0 le_rfl zero_le_one).2
    rw [abs_le]
    constructor <;> linarith

end GreedyDiscrepancy
