import GreedyDiscrepancy

/-! Headline theorems. Each may depend only on `propext`, `Classical.choice`,
`Quot.sound`. `check.sh` fails on `sorryAx`, `Lean.ofReduceBool` or
`Lean.trustCompiler`. -/

#print axioms GreedyDiscrepancy.l2sq_cons
#print axioms GreedyDiscrepancy.l2sq_cons_le_iff
#print axioms GreedyDiscrepancy.greedy_nil
#print axioms GreedyDiscrepancy.greedy_half
#print axioms GreedyDiscrepancy.kObj_eq_G
#print axioms GreedyDiscrepancy.envelope
#print axioms GreedyDiscrepancy.sum_near_half
#print axioms GreedyDiscrepancy.G_le_half
#print axioms GreedyDiscrepancy.kritzinger_sum_near_half
#print axioms GreedyDiscrepancy.kritzinger_G_le_half
#print axioms GreedyDiscrepancy.quadrature_identity
#print axioms GreedyDiscrepancy.greedy_convex_quadrature
#print axioms GreedyDiscrepancy.kritzinger_convex_quadrature
#print axioms GreedyDiscrepancy.envelope_from
#print axioms GreedyDiscrepancy.sum_near_half_from
#print axioms GreedyDiscrepancy.greedy_convex_quadrature_sharp
#print axioms GreedyDiscrepancy.greedy_chord_deficit
#print axioms GreedyDiscrepancy.greedy_G_ge_constant
#print axioms GreedyDiscrepancy.greedy_G_ge_173_over_240
#print axioms GreedyDiscrepancy.kritzinger_G_ge_173_over_240
#print axioms GreedyDiscrepancy.greedy_chord_deficit_with_age
#print axioms GreedyDiscrepancy.greedy_quadrature_two_sided
#print axioms GreedyDiscrepancy.kritzinger_quadrature_two_sided
#print axioms GreedyDiscrepancy.greedy_chord_deficit_sharp
#print axioms GreedyDiscrepancy.greedy_G_ge_two_thirds
#print axioms GreedyDiscrepancy.greedy_G_ge_2997_over_4160
#print axioms GreedyDiscrepancy.greedy_G_lower_from_start
#print axioms GreedyDiscrepancy.kritzinger_G_two_sided
#print axioms GreedyDiscrepancy.G_eq_integral_D
#print axioms GreedyDiscrepancy.l2sq_eq_integral
#print axioms GreedyDiscrepancy.quadrature_eq_integral_D
#print axioms GreedyDiscrepancy.star_le_of_G_bounds
#print axioms GreedyDiscrepancy.greedy_star_le_sqrt
#print axioms GreedyDiscrepancy.kritzinger_star_le_sqrt
#print axioms GreedyDiscrepancy.envelope_repair
#print axioms GreedyDiscrepancy.repair_consequences
#print axioms GreedyDiscrepancy.greedy_chordRepair
#print axioms GreedyDiscrepancy.greedy_G_lower_repair
#print axioms GreedyDiscrepancy.greedy_G_eventually
#print axioms GreedyDiscrepancy.greedy_star_log
#print axioms GreedyDiscrepancy.greedy_star_le_log
#print axioms GreedyDiscrepancy.kritzinger_conjecture_holds
#print axioms GreedyDiscrepancy.exists_kritzingerSeq
#print axioms GreedyDiscrepancy.kritzingerSeq_unique
#print axioms GreedyDiscrepancy.kSeq_star_le_log
#print axioms GreedyDiscrepancy.isKritzingerSeq_iff_HO
#print axioms GreedyDiscrepancy.kritzinger_conjecture_halfOpen
#print axioms GreedyDiscrepancy.exists_unique_kritzingerSeqHO
#print axioms GreedyDiscrepancy.greedy_star_log_from
#print axioms GreedyDiscrepancy.greedy_secondDiff
#print axioms GreedyDiscrepancy.dyadic_left
#print axioms GreedyDiscrepancy.dyadic_right
#print axioms GreedyDiscrepancy.dyadic_left_E
#print axioms GreedyDiscrepancy.dyadic_right_E
#print axioms GreedyDiscrepancy.G_increment_ge
#print axioms GreedyDiscrepancy.G_decrement_le
#print axioms GreedyDiscrepancy.excess_le
#print axioms GreedyDiscrepancy.secondDiff_from
#print axioms GreedyDiscrepancy.exists_scale
#print axioms GreedyDiscrepancy.isGreedyStep_iff_HO
