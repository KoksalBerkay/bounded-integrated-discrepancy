import GreedyDiscrepancy.FirstSteps

/-!
# An upper envelope for the integrated discrepancy

For points `xs`, let `G xs t = ∫₀ᵗ (#{a ∈ xs : a ≤ s} − |xs| s) ds
= Σ_a (t − a)₊ − |xs| t²/2` (the integrated discrepancy of Steinerberger,
arXiv:2207.08043, Theorem 2).

Kritzinger's objective satisfies `kObj xs t = −2 Σ xs − 2 (G xs t + t(1−t)/2)`,
so a greedy step maximises `G xs + ψ` with `ψ t = t(1−t)/2`.

Main result (`envelope`): along any sequence of greedy steps started from the
empty set, for all `N` and `t ∈ [0,1]`,
`G_N t ≤ t/2` and `G_N t ≤ G_N 1 + (1−t)/2`.
Corollaries: `G_N t ≤ 1/2` and `|Σ_{k<N} x_k − N/2| ≤ 1/2`.
The proof uses only that each new point maximises `G + ψ`; it does not use the
tie-break rule.
-/

namespace GreedyDiscrepancy

/-- Integrated discrepancy `Σ_a (t − a)₊ − |xs| t² / 2`. -/
noncomputable def G (xs : List ℝ) (t : ℝ) : ℝ :=
  (xs.map fun a => max (t - a) 0).sum - (xs.length : ℝ) * t ^ 2 / 2

lemma sum_one_sub (xs : List ℝ) : (xs.map fun a => 1 - a).sum = xs.length - xs.sum := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_succ, ih]; ring

lemma sum_max_eq (xs : List ℝ) (t : ℝ) :
    (xs.map fun a => max a t).sum = xs.sum + (xs.map fun a => max (t - a) 0).sum := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    have : max a t = a + max (t - a) 0 := by
      rcases le_total a t with h | h
      · rw [max_eq_right h, max_eq_left (by linarith)]; ring
      · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    rw [this]; ring

/-- Kritzinger's objective in terms of `G`. -/
theorem kObj_eq_G (xs : List ℝ) (t : ℝ) :
    kObj xs t = -2 * xs.sum - 2 * (G xs t + t * (1 - t) / 2) := by
  simp only [kObj, G, sum_max_eq]; ring

/-- A greedy step maximises `G + ψ` over `[0,1]`. -/
lemma greedy_max {xs : List ℝ} {x : ℝ} (h : IsGreedyStep xs x) {t : ℝ}
    (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    G xs t + t * (1 - t) / 2 ≤ G xs x + x * (1 - x) / 2 := by
  have := h.2.2 t h0 h1
  rw [kObj_eq_G, kObj_eq_G] at this
  linarith

lemma G_append (xs : List ℝ) (x t : ℝ) :
    G (xs ++ [x]) t = G xs t + max (t - x) 0 - t ^ 2 / 2 := by
  simp only [G, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
    List.sum_nil, List.length_append, List.length_cons, List.length_nil,
    Nat.cast_succ]
  ring

lemma pref_succ (x : ℕ → ℝ) (n : ℕ) : pref x (n + 1) = pref x n ++ [x n] := by
  simp [pref, List.range_succ]

/-- The envelope is preserved by one greedy step. -/
theorem envelope_step {xs : List ℝ} {x : ℝ} (hx : IsGreedyStep xs x)
    (hA : ∀ t, 0 ≤ t → t ≤ 1 → G xs t ≤ t / 2)
    (hC : ∀ t, 0 ≤ t → t ≤ 1 → G xs t ≤ G xs 1 + (1 - t) / 2) :
    (∀ t, 0 ≤ t → t ≤ 1 → G (xs ++ [x]) t ≤ t / 2) ∧
    (∀ t, 0 ≤ t → t ≤ 1 → G (xs ++ [x]) t ≤ G (xs ++ [x]) 1 + (1 - t) / 2) := by
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

/-- **Envelope theorem.** If every term is a greedy step from the previous
terms (starting from the empty set), then for all `n` and `t ∈ [0,1]`:
`G_n t ≤ t/2` and `G_n t ≤ G_n 1 + (1−t)/2`. -/
theorem envelope (x : ℕ → ℝ) (hx : ∀ n, IsGreedyStep (pref x n) (x n)) (n : ℕ) :
    (∀ t, 0 ≤ t → t ≤ 1 → G (pref x n) t ≤ t / 2) ∧
    (∀ t, 0 ≤ t → t ≤ 1 → G (pref x n) t ≤ G (pref x n) 1 + (1 - t) / 2) := by
  induction n with
  | zero =>
    refine ⟨fun t h0 _ => ?_, fun t _ h1 => ?_⟩ <;> simp [pref, G] <;> linarith
  | succ n ih =>
    rw [pref_succ]
    exact envelope_step (hx n) ih.1 ih.2

/-- The sum of the first `n` terms is within `1/2` of `n/2`. -/
theorem sum_near_half (x : ℕ → ℝ) (hx : ∀ n, IsGreedyStep (pref x n) (x n)) (n : ℕ) :
    |(pref x n).sum - n / 2| ≤ 1 / 2 := by
  obtain ⟨hA, hC⟩ := envelope x hx n
  have h1 := hA 1 (by norm_num) le_rfl
  have h0 := hC 0 le_rfl (by norm_num)
  have hG1 : G (pref x n) 1 = n / 2 - (pref x n).sum := by
    have hle : ∀ a ∈ pref x n, a ≤ 1 := by
      intro a ha
      simp only [pref, List.mem_map, List.mem_range] at ha
      obtain ⟨k, -, rfl⟩ := ha
      exact (hx k).2.1
    have : ((pref x n).map fun a => max (1 - a) 0).sum = ((pref x n).map fun a => 1 - a).sum := by
      congr 1
      apply List.map_congr_left
      intro a ha
      exact max_eq_left (by linarith [hle a ha])
    have hl : ((pref x n).length : ℝ) = n := by simp [pref]
    unfold G
    rw [this, sum_one_sub, hl]
    ring
  have hG0 : G (pref x n) 0 = 0 := by
    have hge : ∀ a ∈ pref x n, 0 ≤ a := by
      intro a ha
      simp only [pref, List.mem_map, List.mem_range] at ha
      obtain ⟨k, -, rfl⟩ := ha
      exact (hx k).1
    have : ((pref x n).map fun a => max (0 - a) 0).sum = ((pref x n).map fun _ => (0:ℝ)).sum := by
      congr 1
      apply List.map_congr_left
      intro a ha
      exact max_eq_right (by linarith [hge a ha])
    unfold G
    rw [this]
    simp
  rw [abs_le]
  constructor <;> linarith

/-- One-sided bound on the integrated discrepancy: `G_n t ≤ 1/2`. -/
theorem G_le_half (x : ℕ → ℝ) (hx : ∀ n, IsGreedyStep (pref x n) (x n)) (n : ℕ)
    (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) : G (pref x n) t ≤ 1 / 2 := by
  have := (envelope x hx n).1 t h0 h1
  linarith

/-- Kritzinger's sequence satisfies the hypothesis of `envelope`. -/
lemma kritzinger_greedy (x : ℕ → ℝ) (hx : IsKritzingerSeq x) :
    ∀ n, IsGreedyStep (pref x n) (x n) := by
  intro n
  cases n with
  | zero =>
    have : pref x 0 = [] := by simp [pref]
    rw [this, hx.1]
    exact greedy_nil.1
  | succ n => exact (hx.2 n).1

theorem kritzinger_sum_near_half (x : ℕ → ℝ) (hx : IsKritzingerSeq x) (n : ℕ) :
    |(pref x n).sum - n / 2| ≤ 1 / 2 :=
  sum_near_half x (kritzinger_greedy x hx) n

theorem kritzinger_G_le_half (x : ℕ → ℝ) (hx : IsKritzingerSeq x) (n : ℕ)
    (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) : G (pref x n) t ≤ 1 / 2 :=
  G_le_half x (kritzinger_greedy x hx) n t h0 h1

end GreedyDiscrepancy
