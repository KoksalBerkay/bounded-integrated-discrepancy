import GreedyDiscrepancy.Defs

/-!
# The first greedy steps

From the empty set the unique minimiser is `1/2`. After `[1/2]` the
minimisers are `1/4` and `3/4` (a tie), and the tie-break picks `1/4`,
matching Kritzinger's listed sequence `1/2, 1/4, 5/6, …`.
-/

namespace GreedyDiscrepancy

theorem greedy_nil : IsLeastGreedyStep [] (1 / 2) := by
  refine ⟨⟨by norm_num, by norm_num, fun y _ _ => ?_⟩, fun y hy => ?_⟩
  · simp only [kObj, List.map_nil, List.sum_nil, List.length_nil]; nlinarith [sq_nonneg (y - 1/2)]
  · obtain ⟨-, -, h⟩ := hy
    have := h (1 / 2) (by norm_num) (by norm_num)
    simp only [kObj, List.map_nil, List.sum_nil, List.length_nil] at this
    nlinarith [sq_nonneg (y - 1/2)]

lemma kObj_half (y : ℝ) : kObj [1 / 2] y = -2 * max (1 / 2) y + 2 * y ^ 2 - y := by
  simp only [kObj, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil, Nat.cast_zero, Nat.cast_succ]
  ring

theorem greedy_half : IsLeastGreedyStep [1 / 2] (1 / 4) := by
  refine ⟨⟨by norm_num, by norm_num, fun y _ _ => ?_⟩, fun y hy => ?_⟩
  · rw [kObj_half, kObj_half]
    rcases le_total y (1 / 2) with h | h
    · rw [max_eq_left h]; rw [max_eq_left (by norm_num)]; nlinarith [sq_nonneg (y - 1/4)]
    · rw [max_eq_right h]; rw [max_eq_left (by norm_num)]; nlinarith [sq_nonneg (y - 3/4)]
  · obtain ⟨-, -, h⟩ := hy
    have := h (1 / 4) (by norm_num) (by norm_num)
    rw [kObj_half, kObj_half, max_eq_left (by norm_num : (1:ℝ)/4 ≤ 1/2)] at this
    by_contra hlt0
    have hlt : y < 1 / 4 := not_le.mp hlt0
    rw [max_eq_left (by linarith)] at this
    nlinarith [sq_nonneg (y - 1/4)]

end GreedyDiscrepancy
