import Mathlib

/-!
# S8.2 P06a infrastructure (1): dyadic mean-value summation near the origin
For `G` differentiable off `0` with `‖fderiv G y‖ <= B |y|^(a-1) (1+|log|y||)^b` (`a > 0`, `|y| <= 1/2`), the dyadic points
`2^-N z` satisfy `‖G z - G (2^-N z)‖ <= B K(a,b) |z|^a (1+|log|z||)^b`, uniformly in `N`.
-/

set_option autoImplicit false
noncomputable section
open Real

namespace HRS.MS.R26T8A

theorem r26t8a_p06_pw1 (a : ℝ) {l s : ℝ} (hl : 0 < l) (hs1 : l ≤ s) (hs2 : s ≤ 2 * l) :
    s ^ (a - 1) ≤ 2 ^ |a - 1| * (2 * l) ^ (a - 1) := by
  have hs : 0 < s := lt_of_lt_of_le hl hs1
  rcases le_total 0 (a - 1) with h | h
  · rw [abs_of_nonneg h]
    calc s ^ (a - 1) ≤ (2 * l) ^ (a - 1) := Real.rpow_le_rpow hs.le hs2 h
      _ ≤ 2 ^ (a - 1) * (2 * l) ^ (a - 1) := by
        have : (1 : ℝ) ≤ 2 ^ (a - 1) := Real.one_le_rpow (by norm_num) h
        nlinarith [Real.rpow_nonneg (by positivity : (0:ℝ) ≤ 2 * l) (a - 1)]
  · rw [abs_of_nonpos h]
    calc s ^ (a - 1) ≤ l ^ (a - 1) := Real.rpow_le_rpow_of_nonpos hl hs1 h
      _ = 2 ^ (-(a - 1)) * (2 * l) ^ (a - 1) := by
        rw [Real.mul_rpow (by norm_num) hl.le, ← mul_assoc, ← Real.rpow_add (by norm_num)]
        simp

theorem r26t8a_p06_pw2 (b : ℕ) {l s : ℝ} (hl : 0 < l) (hs1 : l ≤ s) (hs2 : s ≤ 1) :
    (1 + |Real.log s|) ^ b ≤ (1 + |Real.log l|) ^ b := by
  have hs : 0 < s := lt_of_lt_of_le hl hs1
  have h1 : |Real.log s| ≤ |Real.log l| := by
    rw [abs_of_nonpos (Real.log_nonpos hs.le hs2), abs_of_nonpos (Real.log_nonpos hl.le (hs1.trans hs2))]
    linarith [Real.log_le_log hl hs1]
  exact pow_le_pow_left₀ (by positivity) (by linarith) b

theorem r26t8a_p06_pw3 (b n : ℕ) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    (1 + |Real.log (((1:ℝ)/2) ^ n * r)|) ^ b ≤ ((n:ℝ) + 1) ^ b * (1 + |Real.log r|) ^ b := by
  rw [← mul_pow]
  refine pow_le_pow_left₀ (by positivity) ?_ b
  have hp : 0 < ((1:ℝ)/2) ^ n := by positivity
  have hle : ((1:ℝ)/2) ^ n * r ≤ 1 := by
    have : ((1:ℝ)/2) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  rw [abs_of_nonpos (Real.log_nonpos (by positivity) hle), abs_of_nonpos (Real.log_nonpos hr.le hr1),
    Real.log_mul hp.ne' hr.ne', Real.log_pow]
  have : Real.log ((1:ℝ)/2) = -Real.log 2 := by simp [Real.log_inv]
  rw [this]
  have hl2 : Real.log 2 ≤ 1 := by
    have := Real.log_two_lt_d9; linarith
  have hl2' : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have h0 : 0 ≤ -Real.log r := by linarith [Real.log_nonpos hr.le hr1]
  nlinarith [mul_nonneg hn h0, mul_nonneg hn hl2', mul_le_mul_of_nonneg_left hl2 hn]

theorem r26t8a_p06_summable (b : ℕ) {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) :
    Summable (fun n : ℕ => ((n : ℝ) + 2) ^ b * ρ ^ n) := by
  have h2 := summable_pow_mul_geometric_of_norm_lt_one b (r := ρ) (by rwa [Real.norm_of_nonneg h0])
  have h3 : Summable (fun n : ℕ => ρ ^ n) := summable_geometric_of_lt_one h0 h1
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((h2.add h3).mul_left (3 ^ b))
  have h3b : (0:ℝ) < 3 ^ b := by positivity
  have : ((n : ℝ) + 2) ^ b ≤ 3 ^ b * ((n : ℝ) ^ b + 1) := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
      calc (2:ℝ) ^ b ≤ 3 ^ b := pow_le_pow_left₀ (by norm_num) (by norm_num) b
        _ ≤ _ := by have h := pow_nonneg (le_refl (0:ℝ)) b; nlinarith
    · have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
      calc ((n : ℝ) + 2) ^ b ≤ (3 * n) ^ b := by
            apply pow_le_pow_left₀ (by positivity); linarith
        _ = 3 ^ b * (n:ℝ) ^ b := by rw [mul_pow]
        _ ≤ _ := by nlinarith [pow_nonneg (Nat.cast_nonneg n : (0:ℝ) ≤ n) b]
  have hr : 0 ≤ ρ ^ n := pow_nonneg h0 n
  calc ((n : ℝ) + 2) ^ b * ρ ^ n ≤ 3 ^ b * ((n : ℝ) ^ b + 1) * ρ ^ n :=
        mul_le_mul_of_nonneg_right this hr
    _ = 3 ^ b * ((n : ℝ) ^ b * ρ ^ n + ρ ^ n) := by ring

theorem r26t8a_p06_step {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V]
    [NormedSpace ℝ V]
    (G : E → V) (a : ℝ) (b : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hdiff : ∀ y : E, 0 < ‖y‖ → ‖y‖ ≤ 1 / 2 → DifferentiableAt ℝ G y)
    (hder : ∀ y : E, 0 < ‖y‖ → ‖y‖ ≤ 1 / 2 →
      ‖fderiv ℝ G y‖ ≤ B * ‖y‖ ^ (a - 1) * (1 + |Real.log ‖y‖|) ^ b)
    (z : E) (hz : 0 < ‖z‖) (hz2 : ‖z‖ ≤ 1 / 2) (n : ℕ) (t : ℝ) (ht1 : ((1:ℝ) / 2) ^ (n + 1) ≤ t)
    (ht2 : t ≤ ((1:ℝ) / 2) ^ n) :
    ‖G (((1:ℝ) / 2) ^ n • z) - G (t • z)‖ ≤
      B * (2 ^ |a - 1| / 2) * (((n : ℝ) + 2) ^ b * (((1:ℝ) / 2) ^ a) ^ n) *
        (‖z‖ ^ a * (1 + |Real.log ‖z‖|) ^ b) := by
  set r := ‖z‖ with hr
  set c0 : ℝ := ((1:ℝ) / 2) ^ n with hc0
  set c1 : ℝ := ((1:ℝ) / 2) ^ (n + 1) with hc1
  have hc0p : 0 < c0 := by positivity
  have hc10 : c1 = c0 / 2 := by rw [hc1, hc0, pow_succ]; ring
  have hc1p : 0 < c1 := by positivity
  have hc0le : c0 ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  set u := c0 * r with hu
  have hup : 0 < u := by positivity
  have hseg : ∀ y ∈ segment ℝ (c1 • z) (c0 • z), c1 * r ≤ ‖y‖ ∧ ‖y‖ ≤ c0 * r := by
    intro y hy
    obtain ⟨α, β, hα, hβ, hαβ, rfl⟩ := hy
    have : α • (c1 • z) + β • (c0 • z) = (α * c1 + β * c0) • z := by
      rw [smul_smul, smul_smul, ← add_smul]
    rw [this, norm_smul, Real.norm_of_nonneg (by positivity)]
    have s1 : c1 ≤ α * c1 + β * c0 := by nlinarith
    have s2 : α * c1 + β * c0 ≤ c0 := by nlinarith
    exact ⟨mul_le_mul_of_nonneg_right s1 hz.le, mul_le_mul_of_nonneg_right s2 hz.le⟩
  have hbound : ∀ y ∈ segment ℝ (c1 • z) (c0 • z),
      ‖fderiv ℝ G y‖ ≤ B * 2 ^ |a - 1| * u ^ (a - 1) * (((n : ℝ) + 2) ^ b * (1 + |Real.log r|) ^ b) := by
    intro y hy
    obtain ⟨h1, h2⟩ := hseg y hy
    have hy0 : 0 < ‖y‖ := lt_of_lt_of_le (by positivity) h1
    have hy2 : ‖y‖ ≤ 1 / 2 := h2.trans (by nlinarith)
    refine (hder y hy0 hy2).trans ?_
    have p1 := r26t8a_p06_pw1 a (l := c1 * r) (s := ‖y‖) (by positivity) h1 (by rw [hc10]; nlinarith)
    have p2 := r26t8a_p06_pw2 b (l := c1 * r) (s := ‖y‖) (by positivity) h1 (by linarith)
    have p3 := r26t8a_p06_pw3 b (n + 1) (r := r) hz (by linarith)
    have e : (2 * (c1 * r)) = u := by rw [hc10]; ring
    rw [e] at p1
    have p3' : (1 + |Real.log (c1 * r)|) ^ b ≤ (((n : ℝ) + 2) ^ b) * (1 + |Real.log r|) ^ b := by
      have := p3
      push_cast at this
      rw [show (n : ℝ) + 1 + 1 = n + 2 by ring] at this
      exact this
    calc B * ‖y‖ ^ (a - 1) * (1 + |Real.log ‖y‖|) ^ b
        ≤ B * (2 ^ |a - 1| * u ^ (a - 1)) * (((n : ℝ) + 2) ^ b * (1 + |Real.log r|) ^ b) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left p1 hB) ((p2.trans p3')) (by positivity) (by positivity)
      _ = _ := by ring
  have htmem : t • z ∈ segment ℝ (c1 • z) (c0 • z) := by
    have hd : 0 < c0 - c1 := by rw [hc10]; linarith
    refine ⟨(c0 - t) / (c0 - c1), (t - c1) / (c0 - c1), div_nonneg (by linarith) hd.le,
      div_nonneg (by linarith) hd.le, by field_simp; ring, ?_⟩
    rw [smul_smul, smul_smul, ← add_smul]
    congr 1
    field_simp
    ring
  have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := G)
    (s := segment ℝ (c1 • z) (c0 • z)) (x := t • z) (y := c0 • z)
    (fun y hy => hdiff y (lt_of_lt_of_le (by positivity) (hseg y hy).1)
      ((hseg y hy).2.trans (by nlinarith)))
    hbound (convex_segment _ _) htmem (right_mem_segment _ _ _)
  have hdist : ‖c0 • z - t • z‖ ≤ u / 2 := by
    rw [← sub_smul, norm_smul, Real.norm_of_nonneg (by linarith)]
    rw [hu]; nlinarith
  have hC : 0 ≤ B * 2 ^ |a - 1| * u ^ (a - 1) * (((n : ℝ) + 2) ^ b * (1 + |Real.log r|) ^ b) := by positivity
  have hmv' := hmv.trans (mul_le_mul_of_nonneg_left hdist hC)
  have hu_a : u ^ (a - 1) * u = u ^ a := by
    rw [← Real.rpow_add_one hup.ne']; congr 1; ring
  have hpow : (c0) ^ a = (((1:ℝ) / 2) ^ a) ^ n := by
    rw [hc0, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
      Real.rpow_natCast]
  have hua : u ^ a = (((1:ℝ) / 2) ^ a) ^ n * r ^ a := by
    rw [hu, Real.mul_rpow hc0p.le hz.le, hpow]
  have hfin : ‖G (c0 • z) - G (t • z)‖ ≤ B * 2 ^ |a - 1| * u ^ (a - 1) *
      (((n : ℝ) + 2) ^ b * (1 + |Real.log r|) ^ b) * (u / 2) := by
    exact hmv'
  calc ‖G (c0 • z) - G (t • z)‖ ≤ _ := hfin
    _ = B * 2 ^ |a - 1| * ((1 + |Real.log r|) ^ b * ((n : ℝ) + 2) ^ b) * (u ^ (a - 1) * u) / 2 := by ring
    _ = _ := by rw [hu_a, hua]; ring

/-- The summation constant of the dyadic estimate. -/
def r26t8a_p06_K (a : ℝ) (b : ℕ) : ℝ :=
  2 ^ |a - 1| / 2 * ∑' n : ℕ, ((n : ℝ) + 2) ^ b * (((1:ℝ) / 2) ^ a) ^ n

theorem r26t8a_p06_K_nonneg (a : ℝ) (b : ℕ) : 0 ≤ r26t8a_p06_K a b := by
  unfold r26t8a_p06_K
  refine mul_nonneg (by positivity) (tsum_nonneg fun n => by positivity)

/-- Partial dyadic sums. -/
theorem r26t8a_p06_partial {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V]
    [NormedSpace ℝ V]
    (G : E → V) {a : ℝ} (ha : 0 < a) (b : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hdiff : ∀ y : E, 0 < ‖y‖ → ‖y‖ ≤ 1 / 2 → DifferentiableAt ℝ G y)
    (hder : ∀ y : E, 0 < ‖y‖ → ‖y‖ ≤ 1 / 2 →
      ‖fderiv ℝ G y‖ ≤ B * ‖y‖ ^ (a - 1) * (1 + |Real.log ‖y‖|) ^ b)
    (z : E) (hz : 0 < ‖z‖) (hz2 : ‖z‖ ≤ 1 / 2) (N : ℕ) :
    ‖G z - G (((1:ℝ) / 2) ^ N • z)‖ ≤ B * r26t8a_p06_K a b * (‖z‖ ^ a * (1 + |Real.log ‖z‖|) ^ b) := by
  have hρ0 : 0 ≤ ((1:ℝ) / 2) ^ a := by positivity
  have hρ1 : ((1:ℝ) / 2) ^ a < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) ha
  have hsum := r26t8a_p06_summable b hρ0 hρ1
  have h1 : dist (G (((1:ℝ) / 2) ^ 0 • z)) (G (((1:ℝ) / 2) ^ N • z)) ≤
      ∑ n ∈ Finset.range N, dist (G (((1:ℝ) / 2) ^ n • z)) (G (((1:ℝ) / 2) ^ (n + 1) • z)) :=
    dist_le_range_sum_dist (fun n => G (((1:ℝ) / 2) ^ n • z)) N
  simp only [pow_zero, one_smul, dist_eq_norm] at h1
  refine h1.trans ?_
  have h2 : ∀ n ∈ Finset.range N, ‖G (((1:ℝ) / 2) ^ n • z) - G (((1:ℝ) / 2) ^ (n + 1) • z)‖ ≤
      B * (2 ^ |a - 1| / 2) * (‖z‖ ^ a * (1 + |Real.log ‖z‖|) ^ b) *
        (((n : ℝ) + 2) ^ b * (((1:ℝ) / 2) ^ a) ^ n) := fun n _ => by
    have := r26t8a_p06_step G a b B hB hdiff hder z hz hz2 n (((1:ℝ) / 2) ^ (n + 1)) le_rfl
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.le_succ n))
    linarith
  refine (Finset.sum_le_sum h2).trans ?_
  rw [← Finset.mul_sum]
  have h3 : ∑ n ∈ Finset.range N, ((n : ℝ) + 2) ^ b * (((1:ℝ) / 2) ^ a) ^ n ≤
      ∑' n : ℕ, ((n : ℝ) + 2) ^ b * (((1:ℝ) / 2) ^ a) ^ n :=
    hsum.sum_le_tsum _ (fun n _ => by positivity)
  have h4 : 0 ≤ B * (2 ^ |a - 1| / 2) * (‖z‖ ^ a * (1 + |Real.log ‖z‖|) ^ b) := by positivity
  calc B * (2 ^ |a - 1| / 2) * (‖z‖ ^ a * (1 + |Real.log ‖z‖|) ^ b) *
        ∑ n ∈ Finset.range N, ((n : ℝ) + 2) ^ b * (((1:ℝ) / 2) ^ a) ^ n
      ≤ B * (2 ^ |a - 1| / 2) * (‖z‖ ^ a * (1 + |Real.log ‖z‖|) ^ b) *
        ∑' n : ℕ, ((n : ℝ) + 2) ^ b * (((1:ℝ) / 2) ^ a) ^ n := mul_le_mul_of_nonneg_left h3 h4
    _ = _ := by unfold r26t8a_p06_K; ring

/-- Radial version: any point of the segment `(0, z]`. -/
theorem r26t8a_p06_radial {E V : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V]
    [NormedSpace ℝ V]
    (G : E → V) {a : ℝ} (ha : 0 < a) (b : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hdiff : ∀ y : E, 0 < ‖y‖ → ‖y‖ ≤ 1 / 2 → DifferentiableAt ℝ G y)
    (hder : ∀ y : E, 0 < ‖y‖ → ‖y‖ ≤ 1 / 2 →
      ‖fderiv ℝ G y‖ ≤ B * ‖y‖ ^ (a - 1) * (1 + |Real.log ‖y‖|) ^ b)
    (z : E) (hz : 0 < ‖z‖) (hz2 : ‖z‖ ≤ 1 / 2) (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ‖G z - G (t • z)‖ ≤ 2 * B * r26t8a_p06_K a b * (‖z‖ ^ a * (1 + |Real.log ‖z‖|) ^ b) := by
  obtain ⟨N, hN1, hN2⟩ := exists_nat_pow_near_of_lt_one ht0 ht1 (by norm_num : (0:ℝ) < 1 / 2)
    (by norm_num : ((1:ℝ) / 2) < 1)
  have h1 := r26t8a_p06_partial G ha b B hB hdiff hder z hz hz2 N
  have h2 := r26t8a_p06_step G a b B hB hdiff hder z hz hz2 N t hN1.le hN2
  have hρ0 : 0 ≤ ((1:ℝ) / 2) ^ a := by positivity
  have hρ1 : ((1:ℝ) / 2) ^ a < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) ha
  have hsum := r26t8a_p06_summable b hρ0 hρ1
  have h3 : ((N : ℝ) + 2) ^ b * (((1:ℝ) / 2) ^ a) ^ N ≤
      ∑' n : ℕ, ((n : ℝ) + 2) ^ b * (((1:ℝ) / 2) ^ a) ^ n :=
    hsum.le_tsum N (fun n _ => by positivity)
  have h4 : B * (2 ^ |a - 1| / 2) * (((N : ℝ) + 2) ^ b * (((1:ℝ) / 2) ^ a) ^ N) *
      (‖z‖ ^ a * (1 + |Real.log ‖z‖|) ^ b) ≤ B * r26t8a_p06_K a b *
        (‖z‖ ^ a * (1 + |Real.log ‖z‖|) ^ b) := by
    unfold r26t8a_p06_K
    have h5 : 0 ≤ B * (2 ^ |a - 1| / 2) * (‖z‖ ^ a * (1 + |Real.log ‖z‖|) ^ b) := by positivity
    calc _ = B * (2 ^ |a - 1| / 2) * (‖z‖ ^ a * (1 + |Real.log ‖z‖|) ^ b) *
          (((N : ℝ) + 2) ^ b * (((1:ℝ) / 2) ^ a) ^ N) := by ring
      _ ≤ B * (2 ^ |a - 1| / 2) * (‖z‖ ^ a * (1 + |Real.log ‖z‖|) ^ b) *
          ∑' n : ℕ, ((n : ℝ) + 2) ^ b * (((1:ℝ) / 2) ^ a) ^ n := mul_le_mul_of_nonneg_left h3 h5
      _ = _ := by ring
  calc ‖G z - G (t • z)‖ = ‖(G z - G (((1:ℝ) / 2) ^ N • z)) + (G (((1:ℝ) / 2) ^ N • z) - G (t • z))‖ := by
        congr 1; abel
    _ ≤ _ := norm_add_le _ _
    _ ≤ 2 * B * r26t8a_p06_K a b * (‖z‖ ^ a * (1 + |Real.log ‖z‖|) ^ b) := by linarith

end HRS.MS.R26T8A
