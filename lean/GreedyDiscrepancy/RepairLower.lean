import GreedyDiscrepancy.Repair
import GreedyDiscrepancy.LowerBound

/-!
# Bad starts are repaired: the lower bound from an arbitrary start

For `μ ∈ [0,1]` the chord function `φ_μ(p) = √p − (1−μ) p / 2` is preserved by
a greedy step with a margin: if the chord gap of `G` exceeds `φ_μ` by `β`, then
after the step the excess on `[a,b]` is at most

* `β(a,t,b) − p/2` if the new point is outside `(a,b)`,
* `β(a,t,x) − μ p'/2` if it is at `x ∈ [t,b)`, where `p' = (t−a)(x−t)`
  (and symmetrically for `x ∈ (a,t]`).

So the excess decays. Starting from `m` arbitrary points, the excess is at most
`(m/2)√p` at the start, hence at most `(m/2)√q − μ k q/2 ≤ m²/(8 μ k)` after
`k` steps. With the last-point argument (`G_N(x_N) ≥ −x_N/2`) and the
upper repair bound for `G_N(1)` this gives, for every `n > m` and `μ ∈ (0,1]`,

  `G_{n+1}(t) ≥ −2/3 − μ/8 − (m−1/2)²/(2(n+1)) − m²/(8 μ (n−m))`.

With `μ = m/√(n−m)` the error is `O(m/√n)`, so every greedy `L²` sequence,
whatever its initial points, satisfies `liminf_N min_t G_N(t) ≥ −2/3`.
-/

namespace GreedyDiscrepancy

/-- The chord-gap invariant with decaying excess. -/
def chordRepair (f : ℝ → ℝ) (μ c d : ℝ) : Prop :=
  ∀ a t b : ℝ, 0 ≤ a → a ≤ t → t ≤ b → b ≤ 1 → a < b →
    ∃ q, 0 ≤ q ∧ q ≤ (t - a) * (b - t) ∧
      chordGap f a t b ≤ Real.sqrt ((t - a) * (b - t)) - (1 - μ) * ((t - a) * (b - t)) / 2
        + c * Real.sqrt q - d * q / 2

/-- Convex combination of the two bridge inequalities of `LowerBound`. -/
lemma sqrt_chord_split_mu {u v w μ : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hL : 0 < u + v + w) (hL1 : u + v + w ≤ 1) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    Real.sqrt (u * v) - (1 - μ) * (u * v) + u * w / (u + v + w) ≤
      Real.sqrt (u * (v + w)) - (1 - μ) * (u * (v + w)) / 2 := by
  have h1 := sqrt_chord_split_sharp hu hv hw hL hL1
  have h2 := sqrt_chord_split hu hv hw hL
  have e1 := mul_le_mul_of_nonneg_left h1 (sub_nonneg.mpr hμ1)
  have e2 := mul_le_mul_of_nonneg_left h2 hμ0
  nlinarith only [e1, e2]

theorem chordRepair_step {xs : List ℝ} {x μ c d : ℝ} (hx : IsGreedyStep xs x)
    (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (h : chordRepair (G xs) μ c d) : chordRepair (G (xs ++ [x])) μ c (d + μ) := by
  intro a t b ha hat htb hb hab
  have hL : 0 < b - a := sub_pos.mpr hab
  have hp : 0 ≤ (t - a) * (b - t) := mul_nonneg (sub_nonneg.mpr hat) (sub_nonneg.mpr htb)
  -- outside: the gap drops by p/2
  have outside : x ≤ a ∨ b ≤ x → ∃ q, 0 ≤ q ∧ q ≤ (t - a) * (b - t) ∧
      chordGap (G (xs ++ [x])) a t b ≤ Real.sqrt ((t - a) * (b - t))
        - (1 - μ) * ((t - a) * (b - t)) / 2 + c * Real.sqrt q - (d + μ) * q / 2 := by
    intro hout
    obtain ⟨q, hq0, hqp, hq⟩ := h a t b ha hat htb hb hab
    refine ⟨q, hq0, hqp, ?_⟩
    rw [chordGap_append_outside xs hab hat htb hout]
    have : μ * q ≤ (t - a) * (b - t) := by nlinarith
    nlinarith
  by_cases hxa : x ≤ a
  · exact outside (Or.inl hxa)
  by_cases hbx : b ≤ x
  · exact outside (Or.inr hbx)
  have hax : a < x := lt_of_not_ge hxa
  have hxb : x < b := lt_of_not_ge hbx
  have hs := chordGap_append_at_max hx ha hb hax hxb
  rcases le_total t x with htx | hxt
  · have hw : 0 ≤ (t - a) / (x - a) :=
      div_nonneg (sub_nonneg.mpr hat) (sub_nonneg.mpr hax.le)
    obtain ⟨q, hq0, hqp, hq⟩ := h a t x ha hat htx (hxb.le.trans hb) hax
    have hpc : (t - a) * (x - t) ≤ (t - a) * (b - t) :=
      mul_le_mul_of_nonneg_left (by linarith) (sub_nonneg.mpr hat)
    refine ⟨q, hq0, hqp.trans hpc, ?_⟩
    have hbridge := sqrt_chord_split_mu (sub_nonneg.mpr hat) (sub_nonneg.mpr htx)
      (sub_nonneg.mpr hxb.le) (by linarith : 0 < t - a + (x - t) + (b - x))
      (by linarith : t - a + (x - t) + (b - x) ≤ 1) hμ0 hμ1
    rw [show t - a + (x - t) + (b - x) = b - a by ring,
      show x - t + (b - x) = b - t by ring] at hbridge
    have hcancel : (t - a) / (x - a) * ((x - a) * (b - x) / (b - a)) =
        (t - a) * (b - x) / (b - a) := by
      field_simp [ne_of_gt hL, ne_of_gt (sub_pos.mpr hax)]
    rw [chordGap_split_left _ hax hxb, chordGap_append_outside xs hax hat htx (Or.inr le_rfl)]
    have hh := mul_le_mul_of_nonneg_left hs hw
    rw [hcancel] at hh
    have : μ * q ≤ μ * ((t - a) * (x - t)) := mul_le_mul_of_nonneg_left hqp hμ0
    nlinarith only [hh, hq, hbridge, this]
  · have hw : 0 ≤ (b - t) / (b - x) :=
      div_nonneg (sub_nonneg.mpr htb) (sub_nonneg.mpr hxb.le)
    obtain ⟨q, hq0, hqp, hq⟩ := h x t b (ha.trans hax.le) hxt htb hb hxb
    have hpc : (t - x) * (b - t) ≤ (t - a) * (b - t) :=
      mul_le_mul_of_nonneg_right (by linarith) (sub_nonneg.mpr htb)
    refine ⟨q, hq0, hqp.trans hpc, ?_⟩
    have hbridge := sqrt_chord_split_mu (sub_nonneg.mpr htb) (sub_nonneg.mpr hxt)
      (sub_nonneg.mpr hax.le) (by linarith : 0 < b - t + (t - x) + (x - a))
      (by linarith : b - t + (t - x) + (x - a) ≤ 1) hμ0 hμ1
    rw [show b - t + (t - x) + (x - a) = b - a by ring,
      show t - x + (x - a) = t - a by ring, mul_comm (b - t) (t - a),
      mul_comm (b - t) (t - x)] at hbridge
    have hcancel : (b - t) / (b - x) * ((x - a) * (b - x) / (b - a)) =
        (b - t) * (x - a) / (b - a) := by
      field_simp [ne_of_gt hL, ne_of_gt (sub_pos.mpr hxb)]
    rw [chordGap_split_right _ hax hxb, chordGap_append_outside xs hxb hxt htb (Or.inl le_rfl)]
    have hh := mul_le_mul_of_nonneg_left hs hw
    rw [hcancel] at hh
    have : μ * q ≤ μ * ((t - x) * (b - t)) := mul_le_mul_of_nonneg_left hqp hμ0
    nlinarith only [hh, hq, hbridge, this]

/-- Chord gap of a ramp. -/
lemma chordGap_ramp (y a t b : ℝ) (hat : a ≤ t) (htb : t ≤ b) (hab : a < b) :
    chordGap (fun s => max (s - y) 0) a t b ≤ (t - a) * (b - t) / (b - a) := by
  have hL : 0 < b - a := sub_pos.mpr hab
  have e : chordGap (fun s => max (s - y) 0) a t b =
      ((b - t) * max (a - y) 0 + (t - a) * max (b - y) 0 - (b - a) * max (t - y) 0) / (b - a) := by
    unfold chordGap; field_simp
  rw [e]
  apply div_le_div_of_nonneg_right _ hL.le
  have hp := mul_nonneg (sub_nonneg.mpr hat) (sub_nonneg.mpr htb)
  rcases le_total y a with hya | hay
  · rw [max_eq_left (by linarith), max_eq_left (by linarith), max_eq_left (by linarith)]
    nlinarith
  rcases le_total b y with hby | hyb
  · rw [max_eq_right (by linarith), max_eq_right (by linarith), max_eq_right (by linarith)]
    nlinarith
  rw [max_eq_right (by linarith : a - y ≤ 0), max_eq_left (by linarith : 0 ≤ b - y)]
  rcases le_total t y with hty | hyt
  · rw [max_eq_right (by linarith : t - y ≤ 0)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hat) (sub_nonneg.mpr hty)]
  · rw [max_eq_left (by linarith : 0 ≤ t - y)]
    nlinarith [mul_nonneg (sub_nonneg.mpr htb) (sub_nonneg.mpr hyt)]

lemma G_cons' (a : ℝ) (xs : List ℝ) (t : ℝ) :
    G (a :: xs) t = G xs t + max (t - a) 0 - t ^ 2 / 2 := by
  simp only [G, List.map_cons, List.sum_cons, List.length_cons, Nat.cast_succ]; ring

lemma chordGap_G_cons (y : ℝ) (xs : List ℝ) (a t b : ℝ) (hab : a < b) :
    chordGap (G (y :: xs)) a t b = chordGap (G xs) a t b
      + chordGap (fun s => max (s - y) 0) a t b - (t - a) * (b - t) / 2 := by
  unfold chordGap
  simp only [G_cons']
  field_simp [ne_of_gt (sub_pos.mpr hab)]
  ring

lemma chordGap_G_le (xs : List ℝ) (a t b : ℝ) (hat : a ≤ t) (htb : t ≤ b) (hab : a < b) :
    chordGap (G xs) a t b ≤ xs.length * ((t - a) * (b - t) / (b - a)) := by
  induction xs with
  | nil =>
    unfold chordGap; simp [G]
  | cons y ys ih =>
    rw [chordGap_G_cons y ys a t b hab]
    have := chordGap_ramp y a t b hat htb hab
    have hp : 0 ≤ (t - a) * (b - t) := mul_nonneg (sub_nonneg.mpr hat) (sub_nonneg.mpr htb)
    simp only [List.length_cons, Nat.cast_succ]
    nlinarith

/-- `uv/(u+v) ≤ √(uv)/2`. -/
lemma harm_le_sqrt {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hL : 0 < u + v) :
    u * v / (u + v) ≤ Real.sqrt (u * v) / 2 := by
  rw [div_le_iff₀ hL]
  have hs := sqrt_amgm hu hv
  have hsq : Real.sqrt (u * v) ^ 2 = u * v := Real.sq_sqrt (mul_nonneg hu hv)
  nlinarith [Real.sqrt_nonneg (u * v)]

theorem chordRepair_base (xs : List ℝ) (μ : ℝ) (hμ0 : 0 ≤ μ) :
    chordRepair (G xs) μ (xs.length / 2) 0 := by
  intro a t b ha hat htb hb hab
  set p := (t - a) * (b - t)
  have hp : 0 ≤ p := mul_nonneg (sub_nonneg.mpr hat) (sub_nonneg.mpr htb)
  refine ⟨p, hp, le_rfl, ?_⟩
  have h1 := chordGap_G_le xs a t b hat htb hab
  have h2 := harm_le_sqrt (sub_nonneg.mpr hat) (sub_nonneg.mpr htb)
    (by linarith : 0 < t - a + (b - t))
  rw [show t - a + (b - t) = b - a by ring] at h2
  have hn : (0 : ℝ) ≤ xs.length := Nat.cast_nonneg _
  have h3 := mul_le_mul_of_nonneg_left h2 hn
  -- √p ≥ p ≥ (1-μ) p / 2 since p ≤ 1
  have hp1 : p ≤ 1 := by
    have := sqrt_amgm (sub_nonneg.mpr hat) (sub_nonneg.mpr htb)
    have hs : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp
    nlinarith [Real.sqrt_nonneg p]
  have hsp : p ≤ Real.sqrt p := by
    have hs : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp
    nlinarith [Real.sqrt_nonneg p, Real.sqrt_le_one.mpr hp1]
  have : (1 - μ) * p / 2 ≤ p := by nlinarith
  nlinarith [Real.sqrt_nonneg p]

lemma excess_le (c d q : ℝ) (hd : 0 < d) (hq : 0 ≤ q) :
    c * Real.sqrt q - d * q / 2 ≤ c ^ 2 / (2 * d) := by
  rw [le_div_iff₀ (by positivity)]
  have hs : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq
  have h2 : d ^ 2 * q = (d * Real.sqrt q) ^ 2 := by rw [mul_pow, hs]
  nlinarith [sq_nonneg (c - d * Real.sqrt q)]

/-- The chord invariant with decaying excess along a sequence started from
`m` arbitrary points. -/
theorem greedy_chordRepair (x : ℕ → ℝ) (m : ℕ) (μ : ℝ) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (hx : ∀ n, m ≤ n → IsGreedyStep (pref x n) (x n)) (n : ℕ) (hn : m ≤ n) :
    chordRepair (G (pref x n)) μ ((m : ℝ) / 2) (μ * ((n : ℝ) - m)) := by
  induction n, hn using Nat.le_induction with
  | base =>
    have := chordRepair_base (pref x m) μ hμ0
    simp only [sub_self, mul_zero]
    simpa [pref] using this
  | succ n hmn ih =>
    rw [pref_succ]
    have hnm : (m : ℝ) ≤ n := by exact_mod_cast hmn
    have := chordRepair_step (hx n hmn) hμ0 hμ1 ih
    have e : μ * ((n : ℝ) - m) + μ = μ * (((n + 1 : ℕ) : ℝ) - m) := by push_cast; ring
    rwa [e] at this

lemma G_zero_of_nonneg (xs : List ℝ) (h : ∀ a ∈ xs, 0 ≤ a) : G xs 0 = 0 := by
  have : (xs.map fun a => max (0 - a) 0).sum = (xs.map fun _ => (0:ℝ)).sum := by
    congr 1
    apply List.map_congr_left
    intro a ha
    exact max_eq_right (by linarith [h a ha])
  unfold G
  rw [this]
  simp

/-- **Lower bound from an arbitrary start.** Let `x_0, …, x_{m−1} ∈ [0,1]`
(`m ≥ 1`) be arbitrary, every later term a greedy step, `n > m` and
`μ ∈ (0,1]`. Then for all `t ∈ [0,1]`,
`G_{n+1}(t) ≥ −2/3 − μ/8 − (m−1/2)²/(2(n+1)) − m²/(8 μ (n−m))`. -/
theorem greedy_G_lower_repair (x : ℕ → ℝ) (m : ℕ) (hm : 1 ≤ m)
    (hrange : ∀ k, 0 ≤ x k ∧ x k ≤ 1)
    (hx : ∀ n, m ≤ n → IsGreedyStep (pref x n) (x n))
    (μ : ℝ) (hμ0 : 0 < μ) (hμ1 : μ ≤ 1) (n : ℕ) (hn : m < n)
    (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    -(2 / 3) - μ / 8 - ((m : ℝ) - 1 / 2) ^ 2 / (2 * (n + 1 : ℕ))
      - (m : ℝ) ^ 2 / (8 * μ * ((n : ℝ) - m)) ≤ G (pref x (n + 1)) t := by
  set δ : ℝ := ((m : ℝ) - 1 / 2) ^ 2 / (2 * (n + 1 : ℕ))
  set E : ℝ := (m : ℝ) ^ 2 / (8 * μ * ((n : ℝ) - m))
  have hnm : (m : ℝ) < n := by exact_mod_cast hn
  have hδ : 0 ≤ δ := by positivity
  have hE : 0 ≤ E := by
    have : 0 < 8 * μ * ((n : ℝ) - m) := by have := sub_pos.mpr hnm; positivity
    positivity
  have hxs : ∀ k, ∀ a ∈ pref x k, 0 ≤ a ∧ a ≤ 1 := by
    intro k a ha
    simp only [pref, List.mem_map, List.mem_range] at ha
    obtain ⟨j, -, rfl⟩ := ha
    exact hrange j
  have hstep := hx n hn.le
  have hxn0 := hstep.1
  have hxn1 := hstep.2.1
  -- endpoint values of G_{n+1}
  have hG0 : G (pref x (n + 1)) 0 = 0 := G_zero_of_nonneg _ fun a ha => (hxs _ a ha).1
  have hGx : -x n / 2 ≤ G (pref x (n + 1)) (x n) := by
    have hm0 := greedy_max hstep (t := 0) le_rfl (by norm_num)
    rw [G_zero_of_nonneg _ fun a ha => (hxs _ a ha).1] at hm0
    rw [pref_succ, G_append, sub_self, max_self]
    nlinarith only [hm0]
  have hG1 : -(1 / 2) - δ ≤ G (pref x (n + 1)) 1 := by
    have := (envelope_repair x m hm (fun k _ => hrange k) hx (n + 1) (by omega) 0 le_rfl
      zero_le_one).2
    rw [hG0] at this
    simp only [δ]
    linarith
  -- chord bound for G_n with the excess bounded by E
  have hch := greedy_chordRepair x m μ hμ0.le hμ1 hx n hn.le
  have hd : 0 < μ * ((n : ℝ) - m) := mul_pos hμ0 (sub_pos.mpr hnm)
  have hEq : ((m : ℝ) / 2) ^ 2 / (2 * (μ * ((n : ℝ) - m))) = E := by
    simp only [E]; field_simp; ring
  -- generic child estimate
  have child : ∀ a b : ℝ, 0 ≤ a → a ≤ t → t ≤ b → b ≤ 1 → a < b → (x n ≤ a ∨ b ≤ x n) →
      -a / 2 - δ ≤ G (pref x (n + 1)) a → -b / 2 - δ ≤ G (pref x (n + 1)) b →
      -(2 / 3) - μ / 8 - δ - E ≤ G (pref x (n + 1)) t := by
    intro a b ha hat htb hb hab hout hla hlb
    obtain ⟨q, hq0, hqp, hq⟩ := hch a t b ha hat htb hb hab
    have hex := excess_le ((m : ℝ) / 2) _ q hd hq0
    rw [hEq] at hex
    rw [pref_succ] at hla hlb ⊢
    have hnew := chordGap_append_outside (pref x n) hab hat htb hout
    have hchord : -t / 2 - δ ≤
        ((b - t) * G (pref x n ++ [x n]) a + (t - a) * G (pref x n ++ [x n]) b) / (b - a) := by
      apply (le_div_iff₀ (sub_pos.mpr hab)).2
      have hLa := mul_le_mul_of_nonneg_left hla (sub_nonneg.mpr htb)
      have hLb := mul_le_mul_of_nonneg_left hlb (sub_nonneg.mpr hat)
      nlinarith only [hLa, hLb]
    unfold chordGap at hq hnew
    have hp : 0 ≤ (t - a) * (b - t) := mul_nonneg (sub_nonneg.mpr hat) (sub_nonneg.mpr htb)
    have hsq : Real.sqrt ((t - a) * (b - t)) ^ 2 = (t - a) * (b - t) := Real.sq_sqrt hp
    have hpt : (t - a) * (b - t) ≤ t * (1 - t) := by
      nlinarith only [mul_nonneg ha (sub_nonneg.mpr htb), mul_nonneg h0 (sub_nonneg.mpr hb)]
    have hp4 : (t - a) * (b - t) ≤ 1 / 4 := by nlinarith only [hpt, sq_nonneg (t - 1 / 2)]
    have hμp : μ * ((t - a) * (b - t)) ≤ μ * (1 / 4) := mul_le_mul_of_nonneg_left hp4 hμ0.le
    have hsqrt : Real.sqrt ((t - a) * (b - t)) ≤ 3 * ((t - a) * (b - t)) / 2 + 1 / 6 := by
      nlinarith only [sq_nonneg (Real.sqrt ((t - a) * (b - t)) - 1 / 3), hsq]
    have ht2 : t / 2 + (t - a) * (b - t) / 2 ≤ 1 / 2 := by
      nlinarith only [hpt, sq_nonneg (t - 1)]
    linarith only [hq, hnew, hchord, hex, hsqrt, hμp, ht2]
  rcases lt_trichotomy t (x n) with hlt | heq | hgt
  · exact (child 0 (x n) le_rfl h0 hlt.le hxn1 (lt_of_le_of_lt h0 hlt) (Or.inr le_rfl)
      (by rw [hG0]; linarith) (by linarith)).trans' (by linarith)
  · rw [heq]
    linarith only [hGx, hxn1, hδ, hE, hμ0]
  · exact (child (x n) 1 hxn0 hgt.le h1 le_rfl (lt_of_lt_of_le hgt h1) (Or.inl le_rfl)
      (by linarith) (by linarith)).trans' (by linarith)

/-- **Asymptotically universal bounds.** Whatever the `m ≥ 1` initial points
in `[0,1]`, for every `ε > 0` there is `N₀` such that
`−2/3 − ε ≤ G_N(t) ≤ 1/2 + ε` for all `N ≥ N₀` and `t ∈ [0,1]`. -/
theorem greedy_G_eventually (x : ℕ → ℝ) (m : ℕ) (hm : 1 ≤ m)
    (hrange : ∀ k, 0 ≤ x k ∧ x k ≤ 1)
    (hx : ∀ n, m ≤ n → IsGreedyStep (pref x n) (x n)) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ t, 0 ≤ t → t ≤ 1 →
      -(2 / 3) - ε ≤ G (pref x N) t ∧ G (pref x N) t ≤ 1 / 2 + ε := by
  set μ : ℝ := min ε 1
  have hμ0 : 0 < μ := lt_min hε one_pos
  have hμ1 : μ ≤ 1 := min_le_right _ _
  have hμε : μ ≤ ε := min_le_left _ _
  set C : ℝ := 2 * (m : ℝ) ^ 2 + 2 * ((m : ℝ) - 1 / 2) ^ 2 + 1
  have hC : 0 < C := by positivity
  refine ⟨m + 2 + ⌈C / (μ * ε)⌉₊, fun N hN t h0 h1 => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hceil : C / (μ * ε) ≤ ⌈C / (μ * ε)⌉₊ := Nat.le_ceil _
  have hk : C / (μ * ε) + 1 ≤ (n : ℝ) - m := by
    have : (m : ℝ) + 1 + ⌈C / (μ * ε)⌉₊ ≤ n := by exact_mod_cast (by omega : m + 1 + ⌈C / (μ * ε)⌉₊ ≤ n)
    linarith
  have hk0 : 0 < (n : ℝ) - m := by
    have : 0 ≤ C / (μ * ε) := by positivity
    linarith
  have hnm : m < n := by
    have : (m : ℝ) < n := by linarith
    exact_mod_cast this
  have hlow := greedy_G_lower_repair x m hm hrange hx μ hμ0 hμ1 n hnm t h0 h1
  have hup := (repair_consequences x m hm hrange hx (n + 1) (by omega)).1 t h0 h1
  -- the error terms
  have hCk : C ≤ μ * ε * ((n : ℝ) - m) := by
    have := (div_le_iff₀ (by positivity : 0 < μ * ε)).1 (by linarith : C / (μ * ε) ≤ (n : ℝ) - m)
    linarith
  have hδ : ((m : ℝ) - 1 / 2) ^ 2 / (2 * ((n + 1 : ℕ) : ℝ)) ≤ ε / 4 := by
    rw [div_le_iff₀ (by positivity)]
    have hn1 : (n : ℝ) - m ≤ ((n + 1 : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
    have hme : μ * ε ≤ ε := by nlinarith
    nlinarith [sq_nonneg ((m : ℝ) - 1 / 2), sq_nonneg (m : ℝ)]
  have hE : (m : ℝ) ^ 2 / (8 * μ * ((n : ℝ) - m)) ≤ ε / 8 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg ((m : ℝ) - 1 / 2), sq_nonneg (m : ℝ)]
  constructor
  · linarith
  · linarith

end GreedyDiscrepancy
