import GreedyDiscrepancy.Existence

/-!
# Kritzinger's original search space `[0,1)`

Kritzinger's Algorithm 2 chooses `x_{N+1}` as the least minimiser of `f_N`
over `[0,1)`; the library uses `[0,1]`. They agree: `1` is never a minimiser
over `[0,1]`, because `f_N(1) − f_N(y) ≥ (1−y)((N+1)y − N) > 0` for
`N/(N+1) < y < 1`. Hence the two notions of greedy step, of least greedy step
and of Kritzinger sequence coincide, and Kritzinger's conjecture holds in his
own formulation (`kritzinger_conjecture_halfOpen`).
-/

namespace GreedyDiscrepancy

/-- `x` minimises Kritzinger's objective over `[0,1)` (his Algorithm 2). -/
def IsGreedyStepHO (xs : List ℝ) (x : ℝ) : Prop :=
  0 ≤ x ∧ x < 1 ∧ ∀ y : ℝ, 0 ≤ y → y < 1 → kObj xs x ≤ kObj xs y

/-- The least minimiser over `[0,1)`. -/
def IsLeastGreedyStepHO (xs : List ℝ) (x : ℝ) : Prop :=
  IsGreedyStepHO xs x ∧ ∀ y : ℝ, IsGreedyStepHO xs y → x ≤ y

/-- Kritzinger's sequence exactly as in his Algorithm 2. -/
def IsKritzingerSeqHO (x : ℕ → ℝ) : Prop :=
  x 0 = 1 / 2 ∧ ∀ n : ℕ, IsLeastGreedyStepHO (pref x (n + 1)) (x (n + 1))

/-- Kritzinger's Conjecture 2 (first part) in his formulation. -/
def KritzingerConjectureHO : Prop :=
  ∀ x : ℕ → ℝ, IsKritzingerSeqHO x →
    ∃ C : ℝ, ∀ n : ℕ, 2 ≤ n → StarDiscLE (pref x n) (C * Real.log n)

lemma max_sub_max_le (a y : ℝ) (hy : y ≤ 1) : max a 1 - max a y ≤ 1 - y := by
  rcases le_total a y with h | h
  · rw [max_eq_right h, max_eq_right (h.trans hy)]
  · rw [max_eq_left h]
    rcases le_total a 1 with h' | h'
    · rw [max_eq_right h']; linarith
    · rw [max_eq_left h']; linarith

lemma sum_max_one_sub_le (xs : List ℝ) (y : ℝ) (hy : y ≤ 1) :
    (xs.map fun a => max a 1).sum - (xs.map fun a => max a y).sum ≤ xs.length * (1 - y) := by
  induction xs with
  | nil => simp
  | cons b bs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_succ]
    have := max_sub_max_le b y hy
    linarith

/-- `f_N(1) − f_N(y) ≥ (1−y)((N+1)y − N)` for `y ≤ 1`. -/
lemma kObj_one_sub_ge (xs : List ℝ) (y : ℝ) (hy : y ≤ 1) :
    (1 - y) * ((xs.length + 1) * y - xs.length) ≤ kObj xs 1 - kObj xs y := by
  have := sum_max_one_sub_le xs y hy
  unfold kObj
  nlinarith

/-- `1` is never a minimiser of `f_N` over `[0,1]`. -/
lemma exists_lt_kObj_one (xs : List ℝ) : ∃ y, 0 ≤ y ∧ y < 1 ∧ kObj xs y < kObj xs 1 := by
  set N : ℝ := (xs.length : ℝ)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  refine ⟨(2 * N + 1) / (2 * N + 2), by positivity, ?_, ?_⟩
  · rw [div_lt_one (by positivity)]; linarith
  · have hy : (2 * N + 1) / (2 * N + 2) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    have h := kObj_one_sub_ge xs _ hy
    have e1 : 1 - (2 * N + 1) / (2 * N + 2) = 1 / (2 * N + 2) := by
      field_simp; ring
    have e2 : (N + 1) * ((2 * N + 1) / (2 * N + 2)) - N = 1 / 2 := by
      field_simp; ring
    rw [e1, e2] at h
    have : 0 < 1 / (2 * N + 2) * (1 / 2) := by positivity
    linarith

theorem isGreedyStep_iff_HO (xs : List ℝ) (x : ℝ) : IsGreedyStep xs x ↔ IsGreedyStepHO xs x := by
  obtain ⟨y₀, hy0, hy1, hlt⟩ := exists_lt_kObj_one xs
  constructor
  · rintro ⟨h0, h1, h⟩
    have hx1 : x < 1 := by
      rcases h1.lt_or_eq with h1 | rfl
      · exact h1
      · exact absurd (h y₀ hy0 hy1.le) (not_le.2 hlt)
    exact ⟨h0, hx1, fun y hy0' hy1' => h y hy0' hy1'.le⟩
  · rintro ⟨h0, h1, h⟩
    refine ⟨h0, h1.le, fun y hy0' hy1' => ?_⟩
    rcases hy1'.lt_or_eq with hy | rfl
    · exact h y hy0' hy
    · exact (h y₀ hy0 hy1).trans hlt.le

theorem isLeastGreedyStep_iff_HO (xs : List ℝ) (x : ℝ) :
    IsLeastGreedyStep xs x ↔ IsLeastGreedyStepHO xs x := by
  simp only [IsLeastGreedyStep, IsLeastGreedyStepHO, isGreedyStep_iff_HO]

theorem isKritzingerSeq_iff_HO (x : ℕ → ℝ) : IsKritzingerSeq x ↔ IsKritzingerSeqHO x := by
  simp only [IsKritzingerSeq, IsKritzingerSeqHO, isLeastGreedyStep_iff_HO]

/-- **Kritzinger's Conjecture 2 (first part), in his own formulation**: for the
sequence of his Algorithm 2 (search over `[0,1)`), the unnormalised star
discrepancy `sup_{t∈[0,1]} |#{k < n : x_k < t} − n t|` is `O(log n)`. -/
theorem kritzinger_conjecture_halfOpen : KritzingerConjectureHO := by
  intro x hx
  exact kritzinger_conjecture_holds x ((isKritzingerSeq_iff_HO x).2 hx)

/-- The sequence of Algorithm 2 exists, is unique, and equals `kSeq`. -/
theorem exists_unique_kritzingerSeqHO :
    IsKritzingerSeqHO kSeq ∧ ∀ y, IsKritzingerSeqHO y → y = kSeq :=
  ⟨(isKritzingerSeq_iff_HO kSeq).1 kSeq_isKritzinger, fun _ hy =>
    kritzingerSeq_unique ((isKritzingerSeq_iff_HO _).2 hy) kSeq_isKritzinger⟩

end GreedyDiscrepancy
