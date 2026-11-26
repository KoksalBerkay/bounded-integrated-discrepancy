import GreedyDiscrepancy.LogStar
import Mathlib.Topology.Order.Compact

/-!
# Kritzinger's sequence exists

For every finite list the objective `kObj xs` is continuous, so it attains its
minimum on `[0,1]`; the set of minimisers is closed and nonempty, so it has a
least element. Iterating this choice from the empty list gives a sequence
satisfying `IsKritzingerSeq`. Hence the statements about Kritzinger's sequence
(e.g. `kritzinger_conjecture_holds`) are not vacuous.
-/

open Set

namespace GreedyDiscrepancy

lemma continuous_sum_max (xs : List ℝ) : Continuous fun x : ℝ => (xs.map fun a => max a x).sum := by
  induction xs with
  | nil => simp; exact continuous_const
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (continuous_const.max continuous_id).add ih

lemma continuous_kObj' (xs : List ℝ) : Continuous (kObj xs) := by
  have h := continuous_sum_max xs
  have : kObj xs = fun x => -2 * (xs.map fun a => max a x).sum
      + ((xs.length : ℝ) + 1) * x ^ 2 - x := by
    funext x; rfl
  rw [this]
  exact ((continuous_const.mul h).add (continuous_const.mul (continuous_pow 2))).sub continuous_id

/-- Every list has a least greedy step. -/
theorem exists_leastGreedyStep (xs : List ℝ) : ∃ x, IsLeastGreedyStep xs x := by
  have hc := continuous_kObj' xs
  obtain ⟨x₀, hx₀, hmin⟩ :=
    (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_isMinOn (nonempty_Icc.2 zero_le_one)
      hc.continuousOn
  set S : Set ℝ := Icc 0 1 ∩ kObj xs ⁻¹' Iic (kObj xs x₀)
  have hSc : IsClosed S := isClosed_Icc.inter (isClosed_Iic.preimage hc)
  have hSne : S.Nonempty := ⟨x₀, hx₀, show kObj xs x₀ ≤ kObj xs x₀ from le_rfl⟩
  have hSbdd : BddBelow S := ⟨0, fun y hy => hy.1.1⟩
  have hmem := hSc.csInf_mem hSne hSbdd
  have greedy_iff : ∀ y, IsGreedyStep xs y ↔ y ∈ S := by
    intro y
    constructor
    · rintro ⟨h0, h1, h⟩
      exact ⟨⟨h0, h1⟩, h x₀ hx₀.1 hx₀.2⟩
    · rintro ⟨⟨h0, h1⟩, hy⟩
      refine ⟨h0, h1, fun z hz0 hz1 => ?_⟩
      exact le_trans hy (hmin ⟨hz0, hz1⟩)
  refine ⟨sInf S, (greedy_iff _).2 hmem, fun y hy => csInf_le hSbdd ((greedy_iff y).1 hy)⟩

/-- The least greedy step after `xs`. -/
noncomputable def leastStep (xs : List ℝ) : ℝ := Classical.choose (exists_leastGreedyStep xs)

lemma leastStep_spec (xs : List ℝ) : IsLeastGreedyStep xs (leastStep xs) :=
  Classical.choose_spec (exists_leastGreedyStep xs)

/-- The first `n` terms of the constructed sequence. -/
noncomputable def kList : ℕ → List ℝ
  | 0 => []
  | n + 1 => kList n ++ [leastStep (kList n)]

/-- Kritzinger's sequence, constructed. -/
noncomputable def kSeq (n : ℕ) : ℝ := leastStep (kList n)

lemma pref_kSeq (n : ℕ) : pref kSeq n = kList n := by
  induction n with
  | zero => simp [pref, kList]
  | succ n ih => rw [pref_succ, ih]; rfl

lemma leastGreedyStep_unique {xs : List ℝ} {x y : ℝ} (hx : IsLeastGreedyStep xs x)
    (hy : IsLeastGreedyStep xs y) : x = y :=
  le_antisymm (hx.2 y hy.1) (hy.2 x hx.1)

/-- **Existence.** The constructed sequence is a Kritzinger sequence. -/
theorem kSeq_isKritzinger : IsKritzingerSeq kSeq := by
  refine ⟨?_, fun n => ?_⟩
  · exact leastGreedyStep_unique (leastStep_spec []) greedy_nil
  · rw [pref_kSeq]
    exact leastStep_spec _

theorem exists_kritzingerSeq : ∃ x : ℕ → ℝ, IsKritzingerSeq x := ⟨kSeq, kSeq_isKritzinger⟩

/-- Kritzinger's sequence is unique: two Kritzinger sequences agree. -/
theorem kritzingerSeq_unique {x y : ℕ → ℝ} (hx : IsKritzingerSeq x) (hy : IsKritzingerSeq y) :
    x = y := by
  have h : ∀ n, ∀ k < n, x k = y k := by
    intro n
    induction n with
    | zero => intro k hk; omega
    | succ n ih =>
      intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · exact ih k hk
      · cases k with
        | zero => rw [hx.1, hy.1]
        | succ k =>
          have hp : pref x (k + 1) = pref y (k + 1) := by
            simp only [pref, List.map_inj_left, List.mem_range]
            intro j hj; exact ih j (by omega)
          have := hy.2 k
          rw [← hp] at this
          exact leastGreedyStep_unique (hx.2 k) this
  funext n
  exact h (n + 1) n (by omega)

/-- The star discrepancy of *the* Kritzinger sequence is `O(log n)`: an explicit,
non-vacuous form of `kritzinger_conjecture_holds`. -/
theorem kSeq_star_le_log (n : ℕ) (hn : 2 ≤ n) :
    StarDiscLE (pref kSeq n) (5 / Real.log 2 * Real.log n) :=
  greedy_star_le_log kSeq (kritzinger_greedy kSeq kSeq_isKritzinger) n hn

end GreedyDiscrepancy
