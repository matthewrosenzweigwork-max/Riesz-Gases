import HRS.MS.CritForceMom4

/-!
# S8.2 NormalForm packet R03, part 5: the two cutoff-free rows
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HRS.MS.S82N

open HRS HRS.Whole

variable {d : ℕ}

/-- The Gaussian moment constant. -/
def s82n_Mom (d : ℕ) (M G c : ℝ) : ℝ := G * ∫ y : Euc d, Real.exp (-c * ‖y‖ ^ 2) * jbracket y ^ M

lemma s82n_Mom_nonneg (hd : 1 ≤ d) (M G c : ℝ) (hM : 0 ≤ M) (hG : 0 ≤ G) (hc : 0 < c) :
    0 ≤ s82n_Mom d M G c := by
  unfold s82n_Mom
  refine mul_nonneg hG (integral_nonneg fun y => ?_)
  exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (s82n_jb_pos y).le _)

/-- The master estimate with the Gaussian constant filled in. -/
theorem s82n_row (hd : 1 ≤ d) (M G c r0 K0 : ℝ) (hM : 0 ≤ M) (hG : 0 ≤ G) (hc : 0 < c)
    (hr0 : 0 < r0) (hr1 : r0 ≤ 1) (hK0 : 0 ≤ K0)
    (ρ : Euc d → ℝ) (hρ : HRS.Whole.IsProbDensity ρ) (hρG : HRS.Whole.HasR2GaussianUpper G c ρ)
    (x : Euc d) (Φ : Euc d → ℝ) (hΦm : Measurable Φ) (Ψ g : ℝ → ℝ)
    (hΨ0 : ∀ r, 0 ≤ r → 0 ≤ Ψ r) (hΨm : Measurable Ψ) (hg : IntervalIntegrable g volume 0 r0)
    (hle : ∀ r ∈ Ioo (0 : ℝ) r0, r ^ (d - 1) * Ψ r ≤ g r)
    (near : ∀ y, ‖x - y‖ < r0 → Φ y ≤ Ψ ‖x - y‖) (far : ∀ y, r0 ≤ ‖x - y‖ → Φ y ≤ K0) :
    ∫⁻ y, ENNReal.ofReal (jbracket y ^ M * Φ y) ∂(HRS.Whole.withDensityReal ρ) ≤
      ENNReal.ofReal (jbracket x ^ M * (4 ^ M * G * ((d : ℝ) *
        (volume : Measure (Euc d)).real (Metric.ball (0 : Euc d) 1) * ∫ r in (0 : ℝ)..r0, g r) +
        K0 * s82n_Mom d M G c)) :=
  s82n_master hd M G c (s82n_Mom d M G c) r0 K0 hM hG hc.le hr0 hr1 hK0
    (s82n_Mom_nonneg hd M G c hM hG hc) (s82n_mom_bound hd M G c hM hG hc) ρ hρ.measurable
    hρ.nonneg (fun y => hρG.2 y) x Φ hΦm Ψ g hΨ0 hΨm hg hle near far

lemma s82n_smallRadius_near (x y : Euc d) (h : ‖x - y‖ < 1) : s82n_smallRadius x y = ‖x - y‖ :=
  min_eq_right h.le

lemma s82n_smallRadius_far (x y : Euc d) (r0 : ℝ) (hr0 : 0 < r0) (hr1 : r0 ≤ 1) (h : r0 ≤ ‖x - y‖) :
    r0 ≤ s82n_smallRadius x y ∧ s82n_smallRadius x y ≤ 1 :=
  ⟨le_min hr1 h, min_le_left _ _⟩

lemma s82n_measurable_smallRadius (x : Euc d) : Measurable (fun y : Euc d => s82n_smallRadius x y) := by
  unfold s82n_smallRadius; fun_prop

lemma s82n_E1_profile (hd : 2 ≤ d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    r ^ (d - 1) * (1 + r ^ (1 - s82n_critS d)) ^ 2 ≤ 4 := by
  obtain ⟨f1, -, -, f4⟩ := s82n_rpow_forms (by omega : 1 ≤ d) r hr
  have hs := s82n_critS_pos (by omega : 1 ≤ d)
  set w := r ^ s82n_critS d with hw
  have hw0 : 0 < w := Real.rpow_pos_of_pos hr _
  have hw1 : w ≤ 1 := Real.rpow_le_one hr.le hr1 hs.le
  have hP : r ^ (d - 1) ≤ 1 := pow_le_one₀ hr.le hr1
  rw [f4]
  have key : r ^ (d - 1) * (1 + r / w) ^ 2 = r ^ (d - 1) + 2 * w + r := by
    rw [f1]; field_simp; ring
  rw [key]; linarith

theorem s82n_E1 (hd : 2 ≤ d) (M G c r0 : ℝ) (hM : 0 ≤ M) (hG : 0 ≤ G) (hc : 0 < c)
    (hr0 : 0 < r0) (hr1 : r0 ≤ 1)
    (ρ : Euc d → ℝ) (hρ : HRS.Whole.IsProbDensity ρ) (hρG : HRS.Whole.HasR2GaussianUpper G c ρ)
    (x : Euc d) :
    ∫⁻ y, ENNReal.ofReal (jbracket y ^ M * (1 + s82n_smallRadius x y ^ (1 - s82n_critS d)) ^ 2)
        ∂(HRS.Whole.withDensityReal ρ) ≤
      ENNReal.ofReal (jbracket x ^ M * (4 ^ M * G * ((d : ℝ) *
        (volume : Measure (Euc d)).real (Metric.ball (0 : Euc d) 1) * (4 * r0)) +
        (1 + r0 ^ (1 - s82n_critS d)) ^ 2 * s82n_Mom d M G c)) := by
  have hs1 := s82n_critS_ge_one hd
  have := s82n_row (by omega : 1 ≤ d) M G c r0 ((1 + r0 ^ (1 - s82n_critS d)) ^ 2) hM hG hc hr0 hr1
    (sq_nonneg _) ρ hρ hρG x
    (fun y => (1 + s82n_smallRadius x y ^ (1 - s82n_critS d)) ^ 2)
    (by have := s82n_measurable_smallRadius x; fun_prop)
    (fun r => (1 + r ^ (1 - s82n_critS d)) ^ 2) (fun _ => 4)
    (fun r _ => sq_nonneg _) (by fun_prop) intervalIntegrable_const
    (fun r hr => s82n_E1_profile hd r hr.1 (hr.2.le.trans hr1))
    (fun y hy => by
      rw [s82n_smallRadius_near x y (lt_of_lt_of_le hy hr1)])
    (fun y hy => by
      obtain ⟨h1, h2⟩ := s82n_smallRadius_far x y r0 hr0 hr1 hy
      have ht : 0 < s82n_smallRadius x y := lt_of_lt_of_le hr0 h1
      have e : 1 - s82n_critS d = -(s82n_critS d - 1) := by ring
      have h3 : s82n_smallRadius x y ^ (1 - s82n_critS d) ≤ r0 ^ (1 - s82n_critS d) := by
        rw [e]; exact s82n_rpow_neg_anti _ r0 _ (by linarith) hr0 h1
      have h4 : 0 ≤ s82n_smallRadius x y ^ (1 - s82n_critS d) := Real.rpow_nonneg ht.le _
      show (1 + s82n_smallRadius x y ^ (1 - s82n_critS d)) ^ 2 ≤ _
      gcongr)
  simpa [intervalIntegral.integral_const, mul_comm] using this

lemma s82n_E2_profile (hd : 2 ≤ d) (r : ℝ) (hr : 0 < r) (hr1 : r ≤ 1) :
    r ^ (d - 1) * ((1 + r ^ (1 - s82n_critS d)) * (1 + r ^ (-s82n_critS d))) ≤ 4 := by
  obtain ⟨f1, f2, f3, f4⟩ := s82n_rpow_forms (by omega : 1 ≤ d) r hr
  have hs := s82n_critS_pos (by omega : 1 ≤ d)
  have hs1 := s82n_critS_ge_one hd
  set w := r ^ s82n_critS d with hw
  have hw0 : 0 < w := Real.rpow_pos_of_pos hr _
  have hw1 : w ≤ 1 := Real.rpow_le_one hr.le hr1 hs.le
  have hP : r ^ (d - 1) ≤ 1 := pow_le_one₀ hr.le hr1
  have hQ : r ^ (s82n_critS d - 1) ≤ 1 := Real.rpow_le_one hr.le hr1 (by linarith)
  rw [f4, f3]
  have key : r ^ (d - 1) * ((1 + r / w) * (1 + w⁻¹)) =
      r ^ (d - 1) + r ^ (s82n_critS d - 1) + w + 1 := by
    rw [f1, f2]; field_simp; ring
  rw [key]; linarith

theorem s82n_E2 (hd : 2 ≤ d) (M G c r0 : ℝ) (hM : 0 ≤ M) (hG : 0 ≤ G) (hc : 0 < c)
    (hr0 : 0 < r0) (hr1 : r0 ≤ 1)
    (ρ : Euc d → ℝ) (hρ : HRS.Whole.IsProbDensity ρ) (hρG : HRS.Whole.HasR2GaussianUpper G c ρ)
    (x : Euc d) :
    ∫⁻ y, ENNReal.ofReal (jbracket y ^ M * ((1 + s82n_smallRadius x y ^ (1 - s82n_critS d)) *
          s82n_pole x y)) ∂(HRS.Whole.withDensityReal ρ) ≤
      ENNReal.ofReal (jbracket x ^ M * (4 ^ M * G * ((d : ℝ) *
        (volume : Measure (Euc d)).real (Metric.ball (0 : Euc d) 1) * (4 * r0)) +
        ((1 + r0 ^ (1 - s82n_critS d)) * (1 + r0 ^ (-s82n_critS d))) * s82n_Mom d M G c)) := by
  have hs1 := s82n_critS_ge_one hd
  have hs0 := s82n_critS_pos (by omega : 1 ≤ d)
  have hK : 0 ≤ (1 + r0 ^ (1 - s82n_critS d)) * (1 + r0 ^ (-s82n_critS d)) :=
    mul_nonneg (by have := Real.rpow_nonneg hr0.le (1 - s82n_critS d); linarith)
      (by have := Real.rpow_nonneg hr0.le (-s82n_critS d); linarith)
  have := s82n_row (by omega : 1 ≤ d) M G c r0 _ hM hG hc hr0 hr1 hK ρ hρ hρG x
    (fun y => (1 + s82n_smallRadius x y ^ (1 - s82n_critS d)) * s82n_pole x y)
    (by have := s82n_measurable_smallRadius x; unfold s82n_pole; fun_prop)
    (fun r => (1 + r ^ (1 - s82n_critS d)) * (1 + r ^ (-s82n_critS d))) (fun _ => 4)
    (fun r hr => mul_nonneg (by have := Real.rpow_nonneg hr (1 - s82n_critS d); linarith)
      (by have := Real.rpow_nonneg hr (-s82n_critS d); linarith))
    (by fun_prop) intervalIntegrable_const
    (fun r hr => s82n_E2_profile hd r hr.1 (hr.2.le.trans hr1))
    (fun y hy => by
      show (1 + s82n_smallRadius x y ^ (1 - s82n_critS d)) *
        (1 + s82n_smallRadius x y ^ (-s82n_critS d)) ≤ _
      rw [s82n_smallRadius_near x y (lt_of_lt_of_le hy hr1)])
    (fun y hy => by
      obtain ⟨h1, h2⟩ := s82n_smallRadius_far x y r0 hr0 hr1 hy
      have ht : 0 < s82n_smallRadius x y := lt_of_lt_of_le hr0 h1
      have e : 1 - s82n_critS d = -(s82n_critS d - 1) := by ring
      have h3 : s82n_smallRadius x y ^ (1 - s82n_critS d) ≤ r0 ^ (1 - s82n_critS d) := by
        rw [e]; exact s82n_rpow_neg_anti _ r0 _ (by linarith) hr0 h1
      have h5 : s82n_smallRadius x y ^ (-s82n_critS d) ≤ r0 ^ (-s82n_critS d) :=
        s82n_rpow_neg_anti _ r0 _ hs0.le hr0 h1
      have h4 : 0 ≤ s82n_smallRadius x y ^ (1 - s82n_critS d) := Real.rpow_nonneg ht.le _
      have h6 : 0 ≤ s82n_smallRadius x y ^ (-s82n_critS d) := Real.rpow_nonneg ht.le _
      show (1 + s82n_smallRadius x y ^ (1 - s82n_critS d)) *
        (1 + s82n_smallRadius x y ^ (-s82n_critS d)) ≤ _
      gcongr)
  simpa [intervalIntegral.integral_const, mul_comm] using this

end HRS.MS.S82N
