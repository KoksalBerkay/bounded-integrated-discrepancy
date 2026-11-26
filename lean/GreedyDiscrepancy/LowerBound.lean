import GreedyDiscrepancy.EnvelopeGeneral
import Mathlib.Analysis.Real.Sqrt

/-!
# A lower bound for the integrated discrepancy (chord-deficit invariant)

The chord invariant was found by GPT-6.2 Sol.

Key invariant (`greedy_chord_deficit`): for every greedy `L²` sequence started
from the empty set, all `N` and `0 ≤ a ≤ t ≤ b ≤ 1`, `a < b`,

  `((b−t) G(a) + (t−a) G(b))/(b−a) − G(t) ≤ √((t−a)(b−t))`,

i.e. `G_N` never falls far below its chords. With `a = 0`, `b = 1` and
`G_N(1) ≥ −1/2` this gives `G_N ≥ −(1+√5)/4`, refined to `G_N ≥ −173/240`.
Together with `G_le_half` this bounds the integrated discrepancy on both sides
for every `N`.
-/

namespace GreedyDiscrepancy

noncomputable def chordGap (f : ℝ → ℝ) (a t b : ℝ) : ℝ :=
  ((b - t) * f a + (t - a) * f b) / (b - a) - f t

private def chordBound (f : ℝ → ℝ) (B : ℝ) : Prop :=
  ∀ a t b : ℝ, 0 ≤ a → a ≤ t → t ≤ b → b ≤ 1 → a < b →
    chordGap f a t b ≤ B + Real.sqrt ((t - a) * (b - t))

lemma chordGap_append_outside (xs : List ℝ) {a t b x : ℝ}
    (hab : a < b) (hat : a ≤ t) (htb : t ≤ b) (h : x ≤ a ∨ b ≤ x) :
    chordGap (G (xs ++ [x])) a t b =
      chordGap (G xs) a t b - (t - a) * (b - t) / 2 := by
  have hn := ne_of_gt (sub_pos.mpr hab)
  unfold chordGap
  simp only [G_append]
  rcases h with h | h
  · rw [max_eq_left (by linarith : 0 ≤ a - x), max_eq_left (by linarith : 0 ≤ b - x),
      max_eq_left (by linarith : 0 ≤ t - x)]
    field_simp [hn] ; ring
  · rw [max_eq_right (by linarith : a - x ≤ 0), max_eq_right (by linarith : b - x ≤ 0),
      max_eq_right (by linarith : t - x ≤ 0)]
    field_simp [hn] ; ring

lemma chordGap_append_at_max {xs : List ℝ} {a b x : ℝ}
    (hx : IsGreedyStep xs x) (ha : 0 ≤ a) (hb : b ≤ 1) (hax : a < x) (hxb : x < b) :
    chordGap (G (xs ++ [x])) a x b ≤ (x - a) * (b - x) / (b - a) := by
  have hp : 0 < b - a := by linarith
  have hA := greedy_max hx ha (by linarith : a ≤ 1)
  have hB := greedy_max hx (by linarith : 0 ≤ b) hb
  have hw := add_le_add (mul_le_mul_of_nonneg_left hA (sub_nonneg.mpr hxb.le))
    (mul_le_mul_of_nonneg_left hB (sub_nonneg.mpr hax.le))
  have hprior : chordGap (G xs) a x b ≤ (x - a) * (b - x) / 2 := by
    unfold chordGap
    rw [sub_le_iff_le_add, div_le_iff₀ hp]
    nlinarith only [hw]
  have heq : chordGap (G (xs ++ [x])) a x b =
      chordGap (G xs) a x b + (x - a) * (b - x) / (b - a) -
      (x - a) * (b - x) / 2 := by
    unfold chordGap
    simp only [G_append, sub_self, max_self]
    rw [max_eq_right (by linarith : a - x ≤ 0), max_eq_left (by linarith : 0 ≤ b - x)]
    field_simp [ne_of_gt hp] ; ring
  rw [heq]
  linarith

lemma chordGap_split_left (f : ℝ → ℝ) {a t x b : ℝ}
    (hax : a < x) (hxb : x < b) :
    chordGap f a t b = chordGap f a t x + (t - a) / (x - a) * chordGap f a x b := by
  unfold chordGap
  field_simp [ne_of_gt (sub_pos.mpr hax), (by linarith : b - a ≠ 0)]
  ; ring

lemma chordGap_split_right (f : ℝ → ℝ) {a t x b : ℝ}
    (hax : a < x) (hxb : x < b) :
    chordGap f a t b = chordGap f x t b + (b - t) / (b - x) * chordGap f a x b := by
  unfold chordGap
  field_simp [ne_of_gt (sub_pos.mpr hxb), (by linarith : b - a ≠ 0)]
  ; ring

lemma sqrt_amgm {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    Real.sqrt (u * v) ≤ (u + v) / 2 := by
  apply (Real.sqrt_le_iff).2
  exact ⟨by linarith, by nlinarith [sq_nonneg (u - v)]⟩

lemma sqrt_chord_split {u v w : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hL : 0 < u + v + w) :
    Real.sqrt (u * v) + u * w / (u + v + w) ≤ Real.sqrt (u * (v + w)) := by
  set s := Real.sqrt (u * v)
  set r := Real.sqrt (u * (v + w))
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hsr : s ≤ r := Real.sqrt_le_sqrt (by nlinarith only [mul_nonneg hu hw])
  have hab := sqrt_amgm hu hv
  have habc := sqrt_amgm hu (add_nonneg hv hw)
  change s ≤ (u + v) / 2 at hab
  change r ≤ (u + (v + w)) / 2 at habc
  have hsum : r + s ≤ u + v + w := by linarith
  have hsq1 : r ^ 2 = u * (v + w) := Real.sq_sqrt (mul_nonneg hu (add_nonneg hv hw))
  have hsq2 : s ^ 2 = u * v := Real.sq_sqrt (mul_nonneg hu hv)
  have hfac : (r - s) * (r + s) = u * w := by nlinarith only [hsq1, hsq2]
  have hfinal : u * w / (u + v + w) ≤ r - s := by
    apply (div_le_iff₀ hL).2
    rw [← hfac]
    exact mul_le_mul_of_nonneg_left hsum (sub_nonneg.mpr hsr)
  linarith only [hfinal]

private theorem chordBound_step {xs : List ℝ} {x B : ℝ}
    (hx : IsGreedyStep xs x) (hc : chordBound (G xs) B) :
    chordBound (G (xs ++ [x])) B := by
  intro a t b ha hat htb hb hab
  have hL : 0 < b - a := sub_pos.mpr hab
  by_cases hxa : x ≤ a
  · rw [chordGap_append_outside xs hab hat htb (Or.inl hxa)]
    exact (sub_le_self _ (div_nonneg (mul_nonneg (sub_nonneg.mpr hat)
      (sub_nonneg.mpr htb)) (by norm_num))).trans (hc a t b ha hat htb hb hab)
  by_cases hbx : b ≤ x
  · rw [chordGap_append_outside xs hab hat htb (Or.inr hbx)]
    exact (sub_le_self _ (div_nonneg (mul_nonneg (sub_nonneg.mpr hat)
      (sub_nonneg.mpr htb)) (by norm_num))).trans (hc a t b ha hat htb hb hab)
  have hax : a < x := lt_of_not_ge hxa
  have hxb : x < b := lt_of_not_ge hbx
  have hs := chordGap_append_at_max hx ha hb hax hxb
  rcases le_total t x with htx | hxt
  · have hw : 0 ≤ (t - a) / (x - a) :=
      div_nonneg (sub_nonneg.mpr hat) (sub_nonneg.mpr hax.le)
    have hchild := hc a t x ha hat htx (hxb.le.trans hb) hax
    have hbridge := sqrt_chord_split (sub_nonneg.mpr hat) (sub_nonneg.mpr htx)
      (sub_nonneg.mpr hxb.le) (by linarith : 0 < t - a + (x - t) + (b - x))
    rw [show t - a + (x - t) + (b - x) = b - a by ring,
      show x - t + (b - x) = b - t by ring] at hbridge
    have hcancel : (t - a) / (x - a) * ((x - a) * (b - x) / (b - a)) =
        (t - a) * (b - x) / (b - a) := by
      field_simp [ne_of_gt hL, ne_of_gt (sub_pos.mpr hax)]
    rw [chordGap_split_left _ hax hxb, chordGap_append_outside xs hax hat htx (Or.inr le_rfl)]
    have hdrop : 0 ≤ (t - a) * (x - t) / 2 := by positivity
    have hchild' := (sub_le_self _ hdrop).trans hchild
    have hh := add_le_add hchild' (mul_le_mul_of_nonneg_left hs hw)
    rw [hcancel] at hh
    exact hh.trans (by linarith only [hbridge])
  · have hw : 0 ≤ (b - t) / (b - x) :=
      div_nonneg (sub_nonneg.mpr htb) (sub_nonneg.mpr hxb.le)
    have hchild := hc x t b (ha.trans hax.le) hxt htb hb hxb
    have hbridge := sqrt_chord_split (sub_nonneg.mpr htb) (sub_nonneg.mpr hxt)
      (sub_nonneg.mpr hax.le) (by linarith : 0 < b - t + (t - x) + (x - a))
    rw [show b - t + (t - x) + (x - a) = b - a by ring,
      show t - x + (x - a) = t - a by ring, mul_comm (b - t) (t - a),
      mul_comm (b - t) (t - x)] at hbridge
    have hcancel : (b - t) / (b - x) * ((x - a) * (b - x) / (b - a)) =
        (b - t) * (x - a) / (b - a) := by
      field_simp [ne_of_gt hL, ne_of_gt (sub_pos.mpr hxb)]
    rw [chordGap_split_right _ hax hxb, chordGap_append_outside xs hxb hxt htb (Or.inl le_rfl)]
    have hdrop : 0 ≤ (t - x) * (b - t) / 2 := by positivity
    have hchild' := (sub_le_self _ hdrop).trans hchild
    have hh := add_le_add hchild' (mul_le_mul_of_nonneg_left hs hw)
    rw [hcancel] at hh
    exact hh.trans (by linarith only [hbridge])

theorem greedy_chord_deficit (x : ℕ → ℝ) (hx : ∀ n, IsGreedyStep (pref x n) (x n))
    (n : ℕ) (a t b : ℝ) (ha : 0 ≤ a) (hat : a ≤ t) (htb : t ≤ b) (hb : b ≤ 1)
    (hab : a < b) :
    ((b - t) * G (pref x n) a + (t - a) * G (pref x n) b) / (b - a) -
      G (pref x n) t ≤ Real.sqrt ((t - a) * (b - t)) := by
  have hc (n : ℕ) : chordBound (G (pref x n)) 0 := by
    induction n with
    | zero =>
      intro a t b _ _ _ _ _
      simp [chordGap, pref, G, Real.sqrt_nonneg]
    | succ n ih =>
      rw [pref_succ]
      exact chordBound_step (hx n) ih
  simpa [chordGap] using hc n a t b ha hat htb hb hab

lemma greedy_G_zero (x : ℕ → ℝ) (hx : ∀ n, IsGreedyStep (pref x n) (x n))
    (n : ℕ) : G (pref x n) 0 = 0 := by
  induction n with
  | zero => simp [pref, G]
  | succ n ih =>
    rw [pref_succ, G_append, ih, max_eq_right (by linarith [(hx n).1])]
    ring

theorem greedy_G_ge_chord (x : ℕ → ℝ) (hx : ∀ n, IsGreedyStep (pref x n) (x n))
    (n : ℕ) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    t * G (pref x n) 1 - Real.sqrt (t * (1 - t)) ≤ G (pref x n) t := by
  have h := greedy_chord_deficit x hx n 0 t 1 le_rfl h0 h1 le_rfl (by norm_num)
  simp [greedy_G_zero x hx n] at h
  linarith

theorem greedy_G_ge_constant (x : ℕ → ℝ) (hx : ∀ n, IsGreedyStep (pref x n) (x n))
    (n : ℕ) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    -(1 + Real.sqrt 5) / 4 ≤ G (pref x n) t := by
  have h := greedy_G_ge_chord x hx n t h0 h1
  have hg0 := (envelope x hx n).2 0 le_rfl (by norm_num)
  rw [greedy_G_zero x hx n] at hg0
  have hg : -(1 / 2) ≤ G (pref x n) 1 := by linarith
  have htg := mul_le_mul_of_nonneg_left hg h0
  set r := Real.sqrt (t * (1 - t))
  have hr2 : r ^ 2 = t * (1 - t) := Real.sq_sqrt (by positivity)
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hsq : ((t - 1 / 2) / 2 + r) ^ 2 ≤ (Real.sqrt 5 / 4) ^ 2 := by
    nlinarith only [hr2, h5, sq_nonneg (t - 1 / 2 - r / 2)]
  have ht : (t - 1 / 2) / 2 + r ≤ Real.sqrt 5 / 4 := by
    by_cases hpos : 0 ≤ (t - 1 / 2) / 2 + r
    · exact (sq_le_sq₀ hpos (by positivity)).mp hsq
    · linarith only [hpos, Real.sqrt_nonneg 5]
  linarith only [h, htg, ht]

theorem kritzinger_G_ge_constant (x : ℕ → ℝ) (hx : IsKritzingerSeq x)
    (n : ℕ) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    -(1 + Real.sqrt 5) / 4 ≤ G (pref x n) t :=
  greedy_G_ge_constant x (kritzinger_greedy x hx) n t h0 h1




private lemma latest_ge_line (x : ℕ → ℝ) (hx : ∀ n, IsGreedyStep (pref x n) (x n))
    (n : ℕ) :
    -x n / 2 ≤ G (pref x (n + 1)) (x n) := by
  have hm := greedy_max (hx n) (t := 0) le_rfl (by norm_num)
  rw [greedy_G_zero x hx n] at hm
  rw [pref_succ, G_append, sub_self, max_self]
  nlinarith only [hm]

private lemma G_one_ge_line (x : ℕ → ℝ) (hx : ∀ n, IsGreedyStep (pref x n) (x n))
    (n : ℕ) :
    -(1 / 2) ≤ G (pref x n) 1 := by
  have hh := (envelope x hx n).2 0 le_rfl (by norm_num)
  rw [greedy_G_zero x hx n] at hh
  linarith

private lemma greedy_G_ge_child (x : ℕ → ℝ) (hx : ∀ n, IsGreedyStep (pref x n) (x n))
    (n : ℕ) {a t b : ℝ} (ha : 0 ≤ a) (hat : a ≤ t) (htb : t ≤ b) (hb : b ≤ 1)
    (hab : a < b) (hout : x n ≤ a ∨ b ≤ x n)
    (hla : -a / 2 ≤ G (pref x (n + 1)) a) (hlb : -b / 2 ≤ G (pref x (n + 1)) b) :
    -t / 2 - (1 / 5 + 3 / 4 * ((t - a) * (b - t))) ≤ G (pref x (n + 1)) t := by
  have hc := greedy_chord_deficit x hx n a t b ha hat htb hb hab
  change chordGap (G (pref x n)) a t b ≤ Real.sqrt ((t - a) * (b - t)) at hc
  rw [pref_succ] at hla hlb ⊢
  have hnew := chordGap_append_outside (pref x n) hab hat htb hout
  have hchord : -t / 2 ≤
      ((b - t) * G (pref x n ++ [x n]) a + (t - a) * G (pref x n ++ [x n]) b) / (b - a) := by
    apply (le_div_iff₀ (sub_pos.mpr hab)).2
    have hLa := mul_le_mul_of_nonneg_left hla (sub_nonneg.mpr htb)
    have hLb := mul_le_mul_of_nonneg_left hlb (sub_nonneg.mpr hat)
    nlinarith only [hLa, hLb]
  unfold chordGap at hc hnew
  have hsq : Real.sqrt ((t - a) * (b - t)) ^ 2 = (t - a) * (b - t) :=
    Real.sq_sqrt (by positivity)
  nlinarith only [hc, hnew, hchord, hsq,
    sq_nonneg (Real.sqrt ((t - a) * (b - t)) - 2 / 5)]

theorem greedy_G_ge_quadratic (x : ℕ → ℝ) (hx : ∀ n, IsGreedyStep (pref x n) (x n))
    (n : ℕ) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    -t / 2 - (1 / 5 + 3 / 4 * (t * (1 - t))) ≤ G (pref x n) t := by
  have hp : 0 ≤ t * (1 - t) := by positivity
  cases n with
  | zero =>
    simp [G, pref]
    nlinarith only [hp, h0]
  | succ n =>
    have hs := latest_ge_line x hx n
    rcases lt_trichotomy t (x n) with hlt | heq | hgt
    · have hh := greedy_G_ge_child x hx n (a := 0) (t := t) (b := x n)
        le_rfl h0 hlt.le (hx n).2.1 (lt_of_le_of_lt h0 hlt)
        (Or.inr le_rfl) (by rw [greedy_G_zero x hx (n + 1)]; norm_num) hs
      have hq : (t - 0) * (x n - t) ≤ t * (1 - t) := by
        nlinarith only [mul_nonneg h0 (sub_nonneg.mpr (hx n).2.1)]
      linarith only [hq, hh]
    · rw [heq] at hp ⊢
      nlinarith only [hs, hp]
    · have hh := greedy_G_ge_child x hx n (a := x n) (t := t) (b := 1)
        (hx n).1 hgt.le h1 le_rfl (lt_of_lt_of_le hgt h1)
        (Or.inl le_rfl) hs (by linarith only [G_one_ge_line x hx (n + 1)])
      have hq : (t - x n) * (1 - t) ≤ t * (1 - t) := by
        nlinarith only [mul_nonneg (hx n).1 (sub_nonneg.mpr h1)]
      linarith only [hq, hh]

theorem greedy_G_ge_173_over_240 (x : ℕ → ℝ) (hx : ∀ n, IsGreedyStep (pref x n) (x n))
    (n : ℕ) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    -(173 / 240) ≤ G (pref x n) t := by
  nlinarith only [greedy_G_ge_quadratic x hx n t h0 h1, sq_nonneg (t - 5 / 6)]

theorem kritzinger_G_ge_173_over_240 (x : ℕ → ℝ) (hx : IsKritzingerSeq x)
    (n : ℕ) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    -(173 / 240) ≤ G (pref x n) t :=
  greedy_G_ge_173_over_240 x (kritzinger_greedy x hx) n t h0 h1




private lemma chordGap_prefix_after_outside (x : ℕ → ℝ) (n k : ℕ) {a t b : ℝ}
    (hab : a < b) (hat : a ≤ t) (htb : t ≤ b)
    (hout : ∀ i < k, x (n + i) ≤ a ∨ b ≤ x (n + i)) :
    chordGap (G (pref x (n + k))) a t b =
      chordGap (G (pref x n)) a t b - (k : ℝ) * ((t - a) * (b - t) / 2) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.add_succ, pref_succ,
      chordGap_append_outside _ hab hat htb (hout k (Nat.lt_succ_self k)),
      ih (fun i hi => hout i (hi.trans (Nat.lt_succ_self k))), Nat.cast_succ]
    ring

theorem greedy_chord_deficit_with_age
    (x : ℕ → ℝ) (hx : ∀ n, IsGreedyStep (pref x n) (x n))
    (n k : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1)
    (hax : a < x n) (hxb : x n < b)
    (hout : ∀ i < k, x (n + 1 + i) ≤ a ∨ b ≤ x (n + 1 + i)) :
    ((b - x n) * G (pref x (n + 1 + k)) a +
      (x n - a) * G (pref x (n + 1 + k)) b) / (b - a) -
      G (pref x (n + 1 + k)) (x n) ≤
      (x n - a) * (b - x n) * (1 / (b - a) - (k : ℝ) / 2) := by
  have hs := chordGap_append_at_max (hx n) ha hb hax hxb
  rw [← pref_succ] at hs
  change chordGap (G (pref x (n + 1 + k))) a (x n) b ≤ _
  rw [chordGap_prefix_after_outside x (n + 1) k (hax.trans hxb) hax.le hxb.le hout]
  calc
    _ ≤ (x n - a) * (b - x n) / (b - a) -
        (k : ℝ) * ((x n - a) * (b - x n) / 2) := by linarith only [hs]
    _ = _ := by ring


/-! ## Sharper constants and arbitrary starts

Found by GPT-6.2 Sol. The chord invariant
strengthens to `Γ ≤ √p − p/2` (`greedy_chord_deficit_sharp`), giving `G ≥ −2/3`;
with an initial constant `B` it holds after any initial list (`greedy_G_lower_from_start`). -/


private lemma greedy_G_ge_child_v2 (x : ℕ → ℝ) (hx : ∀ n, IsGreedyStep (pref x n) (x n))
    (n : ℕ) {a t b : ℝ} (ha : 0 ≤ a) (hat : a ≤ t) (htb : t ≤ b) (hb : b ≤ 1)
    (hab : a < b) (hout : x n ≤ a ∨ b ≤ x n)
    (hla : -a / 2 ≤ G (pref x (n + 1)) a) (hlb : -b / 2 ≤ G (pref x (n + 1)) b) :
    -t / 2 - (5 / 26 + 4 / 5 * ((t - a) * (b - t))) ≤ G (pref x (n + 1)) t := by
  have hc := greedy_chord_deficit x hx n a t b ha hat htb hb hab
  change chordGap (G (pref x n)) a t b ≤ Real.sqrt ((t - a) * (b - t)) at hc
  rw [pref_succ] at hla hlb ⊢
  have hnew := chordGap_append_outside (pref x n) hab hat htb hout
  have hchord : -t / 2 ≤
      ((b - t) * G (pref x n ++ [x n]) a + (t - a) * G (pref x n ++ [x n]) b) / (b - a) := by
    apply (le_div_iff₀ (sub_pos.mpr hab)).2
    have hLa := mul_le_mul_of_nonneg_left hla (sub_nonneg.mpr htb)
    have hLb := mul_le_mul_of_nonneg_left hlb (sub_nonneg.mpr hat)
    nlinarith only [hLa, hLb]
  unfold chordGap at hc hnew
  have hsq : Real.sqrt ((t - a) * (b - t)) ^ 2 = (t - a) * (b - t) :=
    Real.sq_sqrt (by positivity)
  nlinarith only [hc, hnew, hchord, hsq,
    sq_nonneg (Real.sqrt ((t - a) * (b - t)) - 5 / 13)]

theorem greedy_G_ge_quadratic_v2 (x : ℕ → ℝ) (hx : ∀ n, IsGreedyStep (pref x n) (x n))
    (n : ℕ) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    -t / 2 - (5 / 26 + 4 / 5 * (t * (1 - t))) ≤ G (pref x n) t := by
  have hp : 0 ≤ t * (1 - t) := by positivity
  cases n with
  | zero =>
    simp [G, pref]
    nlinarith only [hp, h0]
  | succ n =>
    have hs := latest_ge_line x hx n
    rcases lt_trichotomy t (x n) with hlt | heq | hgt
    · have hh := greedy_G_ge_child_v2 x hx n (a := 0) (t := t) (b := x n)
        le_rfl h0 hlt.le (hx n).2.1 (lt_of_le_of_lt h0 hlt)
        (Or.inr le_rfl) (by rw [greedy_G_zero x hx (n + 1)]; norm_num) hs
      have hq : (t - 0) * (x n - t) ≤ t * (1 - t) := by
        nlinarith only [mul_nonneg h0 (sub_nonneg.mpr (hx n).2.1)]
      linarith only [hq, hh]
    · rw [heq] at hp ⊢
      nlinarith only [hs, hp]
    · have hh := greedy_G_ge_child_v2 x hx n (a := x n) (t := t) (b := 1)
        (hx n).1 hgt.le h1 le_rfl (lt_of_lt_of_le hgt h1)
        (Or.inl le_rfl) hs (by linarith only [G_one_ge_line x hx (n + 1)])
      have hq : (t - x n) * (1 - t) ≤ t * (1 - t) := by
        nlinarith only [mul_nonneg (hx n).1 (sub_nonneg.mpr h1)]
      linarith only [hq, hh]

theorem greedy_G_ge_2997_over_4160 (x : ℕ → ℝ) (hx : ∀ n, IsGreedyStep (pref x n) (x n))
    (n : ℕ) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    -(2997 / 4160) ≤ G (pref x n) t := by
  nlinarith only [greedy_G_ge_quadratic_v2 x hx n t h0 h1, sq_nonneg (t - 13 / 16)]



lemma sqrt_chord_split_sharp {u v w : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hL : 0 < u + v + w) (hL1 : u + v + w ≤ 1) :
    Real.sqrt (u * v) - u * v + u * w / (u + v + w) ≤
      Real.sqrt (u * (v + w)) - u * (v + w) / 2 := by
  set r := Real.sqrt (u * (v + w))
  set s := Real.sqrt (u * v)
  by_cases hwv : w ≤ v
  · have hh := sqrt_chord_split hu hv hw hL
    have hmul := mul_le_mul_of_nonneg_left hwv hu
    nlinarith only [hh, hmul]
  have hwp : 0 < w := lt_of_le_of_lt hv (lt_of_not_ge hwv)
  rcases hu.eq_or_lt with h | hu'
  · simp [← h, r, s]
  have hr : 0 < r := Real.sqrt_pos.2 (mul_pos hu' (by linarith))
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hrs : s ≤ r := Real.sqrt_le_sqrt (by nlinarith only [mul_nonneg hu hw])
  have hram := sqrt_amgm hu (add_nonneg hv hw)
  change r ≤ (u + (v + w)) / 2 at hram
  have hrhalf : r ≤ 1 / 2 := by linarith
  set q := s / r
  have hq : 0 ≤ q := div_nonneg hs hr.le
  have hq1 : q ≤ 1 := (div_le_iff₀ hr).2 (by simpa using hrs)
  have hqr : q * r = s := div_mul_cancel₀ s hr.ne'
  have hrsq : r ^ 2 = u * (v + w) := Real.sq_sqrt (by positivity)
  have hssq : s ^ 2 = u * v := Real.sq_sqrt (by positivity)
  have hqss : r ^ 2 * q ^ 2 = u * v := by rw [← mul_pow, mul_comm r q, hqr, hssq]
  have hqws : r ^ 2 * (1 - q ^ 2) = u * w := by nlinarith only [hrsq, hqss]
  have hqdiff : r ^ 2 * (1 - 2 * q ^ 2) = u * w - u * v := by
    nlinarith only [hrsq, hqss]
  have hcoeff : 0 ≤ 1 - 2 * q ^ 2 := by
    have hprod : 0 ≤ u * w - u * v := sub_nonneg.mpr (mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge hwv)) hu)
    exact nonneg_of_mul_nonneg_right (hqdiff.symm ▸ hprod) (by positivity : 0 < r ^ 2)
  have hdiv : u * w / (u + v + w) ≤ r * (1 - q ^ 2) / 2 := by
    apply (div_le_iff₀ hL).2
    have hh := mul_le_mul_of_nonneg_right hram (show 0 ≤ r * (1 - q ^ 2) by
      apply mul_nonneg hr.le
      nlinarith only [mul_nonneg hq (sub_nonneg.mpr hq1), hq1])
    nlinarith only [hh, hqws]
  have hsub : (u * w - u * v) / 2 ≤ r * (1 - 2 * q ^ 2) / 4 := by
    have hh := mul_le_mul_of_nonneg_right hrhalf (mul_nonneg hr.le hcoeff)
    nlinarith only [hh, hqdiff]
  nlinarith only [hdiv, hsub, hqr, mul_nonneg hr.le (sq_nonneg (q - 1 / 2))]

private def chordBoundSharp (f : ℝ → ℝ) (B : ℝ) : Prop :=
  ∀ a t b : ℝ, 0 ≤ a → a ≤ t → t ≤ b → b ≤ 1 → a < b →
    chordGap f a t b ≤ B + Real.sqrt ((t - a) * (b - t)) - (t - a) * (b - t) / 2

private theorem chordBoundSharp_step_v2 {xs : List ℝ} {x B : ℝ}
    (hx : IsGreedyStep xs x) (hc : chordBoundSharp (G xs) B) :
    chordBoundSharp (G (xs ++ [x])) B := by
  intro a t b ha hat htb hb hab
  have hL : 0 < b - a := sub_pos.mpr hab
  by_cases hxa : x ≤ a
  · rw [chordGap_append_outside xs hab hat htb (Or.inl hxa)]
    exact (sub_le_self _ (div_nonneg (mul_nonneg (sub_nonneg.mpr hat)
      (sub_nonneg.mpr htb)) (by norm_num))).trans (hc a t b ha hat htb hb hab)
  by_cases hbx : b ≤ x
  · rw [chordGap_append_outside xs hab hat htb (Or.inr hbx)]
    exact (sub_le_self _ (div_nonneg (mul_nonneg (sub_nonneg.mpr hat)
      (sub_nonneg.mpr htb)) (by norm_num))).trans (hc a t b ha hat htb hb hab)
  have hax : a < x := lt_of_not_ge hxa
  have hxb : x < b := lt_of_not_ge hbx
  have hs := chordGap_append_at_max hx ha hb hax hxb
  rcases le_total t x with htx | hxt
  · have hw : 0 ≤ (t - a) / (x - a) :=
      div_nonneg (sub_nonneg.mpr hat) (sub_nonneg.mpr hax.le)
    have hchild := hc a t x ha hat htx (hxb.le.trans hb) hax
    have hbridge := sqrt_chord_split_sharp (sub_nonneg.mpr hat) (sub_nonneg.mpr htx)
      (sub_nonneg.mpr hxb.le) (by linarith : 0 < t - a + (x - t) + (b - x))
      (by linarith : t - a + (x - t) + (b - x) ≤ 1)
    rw [show t - a + (x - t) + (b - x) = b - a by ring,
      show x - t + (b - x) = b - t by ring] at hbridge
    have hcancel : (t - a) / (x - a) * ((x - a) * (b - x) / (b - a)) =
        (t - a) * (b - x) / (b - a) := by
      field_simp [ne_of_gt hL, ne_of_gt (sub_pos.mpr hax)]
    rw [chordGap_split_left _ hax hxb, chordGap_append_outside xs hax hat htx (Or.inr le_rfl)]

    have hchild' := sub_le_sub_right hchild ((t - a) * (x - t) / 2)
    have hh := add_le_add hchild' (mul_le_mul_of_nonneg_left hs hw)
    rw [hcancel] at hh
    exact hh.trans (by linarith only [hbridge])
  · have hw : 0 ≤ (b - t) / (b - x) :=
      div_nonneg (sub_nonneg.mpr htb) (sub_nonneg.mpr hxb.le)
    have hchild := hc x t b (ha.trans hax.le) hxt htb hb hxb
    have hbridge := sqrt_chord_split_sharp (sub_nonneg.mpr htb) (sub_nonneg.mpr hxt)
      (sub_nonneg.mpr hax.le) (by linarith : 0 < b - t + (t - x) + (x - a))
      (by linarith : b - t + (t - x) + (x - a) ≤ 1)
    rw [show b - t + (t - x) + (x - a) = b - a by ring,
      show t - x + (x - a) = t - a by ring, mul_comm (b - t) (t - a),
      mul_comm (b - t) (t - x)] at hbridge
    have hcancel : (b - t) / (b - x) * ((x - a) * (b - x) / (b - a)) =
        (b - t) * (x - a) / (b - a) := by
      field_simp [ne_of_gt hL, ne_of_gt (sub_pos.mpr hxb)]
    rw [chordGap_split_right _ hax hxb, chordGap_append_outside xs hxb hxt htb (Or.inl le_rfl)]

    have hchild' := sub_le_sub_right hchild ((t - x) * (b - t) / 2)
    have hh := add_le_add hchild' (mul_le_mul_of_nonneg_left hs hw)
    rw [hcancel] at hh
    exact hh.trans (by linarith only [hbridge])

theorem greedy_chord_deficit_sharp (x : ℕ → ℝ) (hx : ∀ n, IsGreedyStep (pref x n) (x n))
    (n : ℕ) (a t b : ℝ) (ha : 0 ≤ a) (hat : a ≤ t) (htb : t ≤ b) (hb : b ≤ 1)
    (hab : a < b) :
    ((b - t) * G (pref x n) a + (t - a) * G (pref x n) b) / (b - a) -
      G (pref x n) t ≤ Real.sqrt ((t - a) * (b - t)) - (t - a) * (b - t) / 2 := by
  have hc (n : ℕ) : chordBoundSharp (G (pref x n)) 0 := by
    induction n with
    | zero =>
      intro a t b ha hat htb hb hab
      have h1 : 0 ≤ (t - a) * (b - t) := by positivity
      have h2 : Real.sqrt ((t - a) * (b - t)) ≤ 1 / 2 := by
        have hh := sqrt_amgm (sub_nonneg.mpr hat) (sub_nonneg.mpr htb)
        linarith
      simp only [chordGap, pref, G, List.range_zero, List.map_nil, List.sum_nil,
        List.length_nil, Nat.cast_zero, zero_mul, zero_div, sub_zero, mul_zero, zero_add]
      nlinarith only [Real.sq_sqrt h1, Real.sqrt_nonneg ((t - a) * (b - t)),
        mul_nonneg (Real.sqrt_nonneg ((t - a) * (b - t))) (sub_nonneg.mpr h2)]
    | succ n ih =>
      rw [pref_succ]
      exact chordBoundSharp_step_v2 (hx n) ih
  simpa [chordGap] using hc n a t b ha hat htb hb hab


private lemma greedy_G_ge_child_sharp_v2 (x : ℕ → ℝ) (hx : ∀ n, IsGreedyStep (pref x n) (x n))
    (n : ℕ) {a t b : ℝ} (ha : 0 ≤ a) (hat : a ≤ t) (htb : t ≤ b) (hb : b ≤ 1)
    (hab : a < b) (hout : x n ≤ a ∨ b ≤ x n)
    (hla : -a / 2 ≤ G (pref x (n + 1)) a) (hlb : -b / 2 ≤ G (pref x (n + 1)) b) :
    -t / 2 - (1 / 6 + 1 / 2 * ((t - a) * (b - t))) ≤ G (pref x (n + 1)) t := by
  have hc := greedy_chord_deficit_sharp x hx n a t b ha hat htb hb hab
  change chordGap (G (pref x n)) a t b ≤ Real.sqrt ((t - a) * (b - t)) - (t - a) * (b - t) / 2 at hc
  rw [pref_succ] at hla hlb ⊢
  have hnew := chordGap_append_outside (pref x n) hab hat htb hout
  have hchord : -t / 2 ≤
      ((b - t) * G (pref x n ++ [x n]) a + (t - a) * G (pref x n ++ [x n]) b) / (b - a) := by
    apply (le_div_iff₀ (sub_pos.mpr hab)).2
    have hLa := mul_le_mul_of_nonneg_left hla (sub_nonneg.mpr htb)
    have hLb := mul_le_mul_of_nonneg_left hlb (sub_nonneg.mpr hat)
    nlinarith only [hLa, hLb]
  unfold chordGap at hc hnew
  have hsq : Real.sqrt ((t - a) * (b - t)) ^ 2 = (t - a) * (b - t) :=
    Real.sq_sqrt (by positivity)
  nlinarith only [hc, hnew, hchord, hsq,
    sq_nonneg (Real.sqrt ((t - a) * (b - t)) - 1 / 3)]

theorem greedy_G_ge_quadratic_sharp_v2 (x : ℕ → ℝ) (hx : ∀ n, IsGreedyStep (pref x n) (x n))
    (n : ℕ) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    -t / 2 - (1 / 6 + 1 / 2 * (t * (1 - t))) ≤ G (pref x n) t := by
  have hp : 0 ≤ t * (1 - t) := by positivity
  cases n with
  | zero =>
    simp [G, pref]
    nlinarith only [hp, h0]
  | succ n =>
    have hs := latest_ge_line x hx n
    rcases lt_trichotomy t (x n) with hlt | heq | hgt
    · have hh := greedy_G_ge_child_sharp_v2 x hx n (a := 0) (t := t) (b := x n)
        le_rfl h0 hlt.le (hx n).2.1 (lt_of_le_of_lt h0 hlt)
        (Or.inr le_rfl) (by rw [greedy_G_zero x hx (n + 1)]; norm_num) hs
      have hq : (t - 0) * (x n - t) ≤ t * (1 - t) := by
        nlinarith only [mul_nonneg h0 (sub_nonneg.mpr (hx n).2.1)]
      linarith only [hq, hh]
    · rw [heq] at hp ⊢
      nlinarith only [hs, hp]
    · have hh := greedy_G_ge_child_sharp_v2 x hx n (a := x n) (t := t) (b := 1)
        (hx n).1 hgt.le h1 le_rfl (lt_of_lt_of_le hgt h1)
        (Or.inl le_rfl) hs (by linarith only [G_one_ge_line x hx (n + 1)])
      have hq : (t - x n) * (1 - t) ≤ t * (1 - t) := by
        nlinarith only [mul_nonneg (hx n).1 (sub_nonneg.mpr h1)]
      linarith only [hq, hh]

theorem greedy_G_ge_two_thirds (x : ℕ → ℝ) (hx : ∀ n, IsGreedyStep (pref x n) (x n))
    (n : ℕ) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    -(2 / 3) ≤ G (pref x n) t := by
  nlinarith only [greedy_G_ge_quadratic_sharp_v2 x hx n t h0 h1, sq_nonneg (t - 1)]





private theorem greedy_tail_chord_bound (x : ℕ → ℝ) (m : ℕ) (B : ℝ)
    (hx : ∀ n, m ≤ n → IsGreedyStep (pref x n) (x n))
    (hB : chordBound (G (pref x m)) B) (n : ℕ) (hn : m ≤ n) :
    chordBound (G (pref x n)) B := by
  induction n, hn using Nat.le_induction with
  | base => exact hB
  | succ n hmn ih =>
    rw [pref_succ]
    exact chordBound_step (hx n hmn) ih

theorem greedy_G_lower_from_start (x : ℕ → ℝ) (m : ℕ) (eA eC B : ℝ)
    (hrange : ∀ k, 0 ≤ x k)
    (hx : ∀ n, m ≤ n → IsGreedyStep (pref x n) (x n))
    (hA : ∀ t, 0 ≤ t → t ≤ 1 → G (pref x m) t ≤ t / 2 + eA)
    (hC : ∀ t, 0 ≤ t → t ≤ 1 → G (pref x m) t ≤ G (pref x m) 1 + (1 - t) / 2 + eC)
    (hB : ∀ a t b : ℝ, 0 ≤ a → a ≤ t → t ≤ b → b ≤ 1 → a < b →
      ((b - t) * G (pref x m) a + (t - a) * G (pref x m) b) / (b - a) -
        G (pref x m) t ≤ B + Real.sqrt ((t - a) * (b - t)))
    (n : ℕ) (hn : m ≤ n) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    -(1 / 2 + eC) * t - B - Real.sqrt (t * (1 - t)) ≤ G (pref x n) t := by
  have hz : G (pref x n) 0 = 0 := by
    clear hn
    induction n with
    | zero => simp [G, pref]
    | succ n ih =>
      have h := hrange n
      rw [pref_succ, G_append, ih, max_eq_right (by linarith)]
      ring
  have hE := (envelope_from x m eA eC hx hA hC n hn).2 0 le_rfl (by norm_num)
  have h1' : -(1 / 2 + eC) ≤ G (pref x n) 1 := by rw [hz] at hE; linarith
  have hmul := mul_le_mul_of_nonneg_right h1' h0
  have hch := greedy_tail_chord_bound x m B hx hB n hn 0 t 1 le_rfl h0 h1 le_rfl (by norm_num)
  simp [chordGap, hz] at hch
  linarith only [hch, hmul]


end GreedyDiscrepancy
