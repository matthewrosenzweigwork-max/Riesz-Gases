import HRS.MS.CritForceMom2

/-!
# S8.2 NormalForm packet R03, part 3: master estimate for a radial row

For `x` fixed, a weighted row `∫ ⟨y⟩^M Φ(x,y) dμ(y)` with `μ = ρ dy`, `ρ ≤ G e^{-c|y|²}`, whose factor `Φ`
is dominated by a radial profile `Ψ(|x-y|)` on a small ball and by a constant outside it.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HRS.MS.S82N

open HRS HRS.Whole

variable {d : ℕ}

lemma s82n_lintegral_ball_translate (x : Euc d) (r0 : ℝ) (f : ℝ → ℝ≥0∞) :
    ∫⁻ y in Metric.ball x r0, f ‖x - y‖ = ∫⁻ u in Metric.ball (0 : Euc d) r0, f ‖u‖ := by
  have h1 : ∫⁻ y in Metric.ball x r0, f ‖x - y‖ =
      ∫⁻ y, (Metric.ball (0 : Euc d) r0).indicator (fun u => f ‖u‖) (x - y) := by
    rw [← lintegral_indicator Metric.isOpen_ball.measurableSet]
    refine lintegral_congr fun y => ?_
    by_cases hy : y ∈ Metric.ball x r0
    · have : x - y ∈ Metric.ball (0 : Euc d) r0 := by
        rw [mem_ball_zero_iff, ← dist_eq_norm, dist_comm]; simpa [dist_eq_norm] using hy
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem this]
    · have : x - y ∉ Metric.ball (0 : Euc d) r0 := by
        intro h; apply hy
        rw [mem_ball_zero_iff] at h
        rw [Metric.mem_ball, dist_comm, dist_eq_norm]; exact h
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem this]
  rw [h1, lintegral_sub_left_eq_self (fun u => (Metric.ball (0 : Euc d) r0).indicator (fun u => f ‖u‖) u) x,
    lintegral_indicator Metric.isOpen_ball.measurableSet]

/-- Master estimate for a weighted radial row. -/
theorem s82n_master (hd : 1 ≤ d) (M G c Mom r0 K0 : ℝ) (hM : 0 ≤ M) (hG : 0 ≤ G) (hc : 0 ≤ c)
    (hr0 : 0 < r0) (hr1 : r0 ≤ 1) (hK0 : 0 ≤ K0) (hMom0 : 0 ≤ Mom)
    (hMom : ∫⁻ y : Euc d, ENNReal.ofReal (G * Real.exp (-c * ‖y‖ ^ 2) * jbracket y ^ M) ≤
      ENNReal.ofReal Mom)
    (ρ : Euc d → ℝ) (hρm : Measurable ρ) (hρ0 : ∀ y, 0 ≤ ρ y)
    (hρG : ∀ y, ρ y ≤ G * Real.exp (-c * ‖y‖ ^ 2))
    (x : Euc d) (Φ : Euc d → ℝ) (hΦm : Measurable Φ) (Ψ g : ℝ → ℝ)
    (hΨ0 : ∀ r, 0 ≤ r → 0 ≤ Ψ r) (hΨm : Measurable Ψ) (hg : IntervalIntegrable g volume 0 r0)
    (hle : ∀ r ∈ Ioo (0 : ℝ) r0, r ^ (d - 1) * Ψ r ≤ g r)
    (near : ∀ y, ‖x - y‖ < r0 → Φ y ≤ Ψ ‖x - y‖) (far : ∀ y, r0 ≤ ‖x - y‖ → Φ y ≤ K0) :
    ∫⁻ y, ENNReal.ofReal (jbracket y ^ M * Φ y) ∂(HRS.Whole.withDensityReal ρ) ≤
      ENNReal.ofReal (jbracket x ^ M * (4 ^ M * G * ((d : ℝ) *
        (volume : Measure (Euc d)).real (Metric.ball (0 : Euc d) 1) * ∫ r in (0 : ℝ)..r0, g r) +
        K0 * Mom)) := by
  set A : Set (Euc d) := Metric.ball x r0 with hA
  have hAm : MeasurableSet A := Metric.isOpen_ball.measurableSet
  set κ : ℝ := (d : ℝ) * (volume : Measure (Euc d)).real (Metric.ball (0 : Euc d) 1) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  have hjx := s82n_jb_one_le x
  have hjxM : 1 ≤ jbracket x ^ M := Real.one_le_rpow hjx hM
  have hjxM0 : 0 ≤ jbracket x ^ M := by linarith
  have hfm : Measurable (fun y : Euc d => ENNReal.ofReal (jbracket y ^ M * Φ y)) := by
    refine ENNReal.measurable_ofReal.comp (Measurable.mul ?_ hΦm)
    exact (Measurable.pow_const (by unfold jbracket; fun_prop) _)
  have hρm' : Measurable (fun y : Euc d => ENNReal.ofReal (ρ y)) := ENNReal.measurable_ofReal.comp hρm
  -- reduce to Lebesgue measure
  have hwd : ∀ B : Set (Euc d), MeasurableSet B →
      ∫⁻ y in B, ENNReal.ofReal (jbracket y ^ M * Φ y) ∂(HRS.Whole.withDensityReal ρ) =
      ∫⁻ y in B, ENNReal.ofReal (ρ y) * ENNReal.ofReal (jbracket y ^ M * Φ y) := by
    intro B hB
    unfold HRS.Whole.withDensityReal
    rw [restrict_withDensity hB, lintegral_withDensity_eq_lintegral_mul _ hρm' hfm]
    rfl
  rw [← lintegral_add_compl _ hAm, hwd A hAm, hwd Aᶜ hAm.compl]
  -- near part
  have hexp1 : ∀ y : Euc d, Real.exp (-c * ‖y‖ ^ 2) ≤ 1 := fun y => by
    rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg ‖y‖]
  have hnear : ∫⁻ y in A, ENNReal.ofReal (ρ y) * ENNReal.ofReal (jbracket y ^ M * Φ y) ≤
      ENNReal.ofReal (4 ^ M * G * jbracket x ^ M) *
        ∫⁻ y in A, ENNReal.ofReal (Ψ ‖x - y‖) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' hAm fun y hy => ?_
    have hy' : ‖x - y‖ < r0 := by
      rw [hA, Metric.mem_ball, dist_comm, dist_eq_norm] at hy; exact hy
    have h1 : ρ y ≤ G := (hρG y).trans (by nlinarith [hexp1 y])
    have h2 : jbracket y ^ M ≤ 4 ^ M * jbracket x ^ M := s82n_jb_rpow_near M hM x y (by linarith)
    have h3 : Φ y ≤ Ψ ‖x - y‖ := near y hy'
    have hj0 : 0 ≤ jbracket y ^ M := Real.rpow_nonneg (s82n_jb_pos y).le _
    have h4 : jbracket y ^ M * Φ y ≤ 4 ^ M * jbracket x ^ M * Ψ ‖x - y‖ :=
      calc jbracket y ^ M * Φ y ≤ jbracket y ^ M * Ψ ‖x - y‖ := by gcongr
        _ ≤ 4 ^ M * jbracket x ^ M * Ψ ‖x - y‖ := by gcongr; exact hΨ0 _ (norm_nonneg _)
    have h4' : 0 ≤ 4 ^ M * jbracket x ^ M * Ψ ‖x - y‖ :=
      mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hjxM0) (hΨ0 _ (norm_nonneg _))
    rw [← ENNReal.ofReal_mul (hρ0 y), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc ρ y * (jbracket y ^ M * Φ y) ≤ ρ y * (4 ^ M * jbracket x ^ M * Ψ ‖x - y‖) := by
          gcongr; exact hρ0 y
      _ ≤ G * (4 ^ M * jbracket x ^ M * Ψ ‖x - y‖) := by gcongr
      _ = 4 ^ M * G * jbracket x ^ M * Ψ ‖x - y‖ := by ring
  have hpol : ∫⁻ y in A, ENNReal.ofReal (Ψ ‖x - y‖) ≤ ENNReal.ofReal (κ * ∫ r in (0 : ℝ)..r0, g r) := by
    rw [hA, s82n_lintegral_ball_translate x r0 (fun r => ENNReal.ofReal (Ψ r))]
    exact s82n_polar_ub hd r0 hr0 Ψ g hΨ0 hΨm hg hle
  -- far part
  have hfar : ∫⁻ y in Aᶜ, ENNReal.ofReal (ρ y) * ENNReal.ofReal (jbracket y ^ M * Φ y) ≤
      ENNReal.ofReal (K0 * Mom) := by
    calc ∫⁻ y in Aᶜ, ENNReal.ofReal (ρ y) * ENNReal.ofReal (jbracket y ^ M * Φ y)
        ≤ ∫⁻ y in Aᶜ, ENNReal.ofReal K0 *
            ENNReal.ofReal (G * Real.exp (-c * ‖y‖ ^ 2) * jbracket y ^ M) := by
          refine setLIntegral_mono' hAm.compl fun y hy => ?_
          have hy' : r0 ≤ ‖x - y‖ := by
            rw [Set.mem_compl_iff, hA, Metric.mem_ball, not_lt, dist_comm, dist_eq_norm] at hy
            exact hy
          have hj0 : 0 ≤ jbracket y ^ M := Real.rpow_nonneg (s82n_jb_pos y).le _
          have h3 := far y hy'
          rw [← ENNReal.ofReal_mul (hρ0 y), ← ENNReal.ofReal_mul hK0]
          refine ENNReal.ofReal_le_ofReal ?_
          calc ρ y * (jbracket y ^ M * Φ y) ≤ ρ y * (jbracket y ^ M * K0) := by
                gcongr; exact hρ0 y
            _ ≤ (G * Real.exp (-c * ‖y‖ ^ 2)) * (jbracket y ^ M * K0) :=
                mul_le_mul_of_nonneg_right (hρG y) (mul_nonneg hj0 hK0)
            _ = K0 * (G * Real.exp (-c * ‖y‖ ^ 2) * jbracket y ^ M) := by ring
      _ ≤ ∫⁻ y, ENNReal.ofReal K0 *
            ENNReal.ofReal (G * Real.exp (-c * ‖y‖ ^ 2) * jbracket y ^ M) :=
          setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal K0 * ∫⁻ y, ENNReal.ofReal (G * Real.exp (-c * ‖y‖ ^ 2) * jbracket y ^ M) := by
          rw [lintegral_const_mul'' _ ?_]
          refine ENNReal.measurable_ofReal.comp ?_ |>.aemeasurable
          exact (by fun_prop : Measurable fun y : Euc d =>
            G * Real.exp (-c * ‖y‖ ^ 2) * Real.sqrt (1 + ‖y‖ ^ 2) ^ M)
      _ ≤ ENNReal.ofReal K0 * ENNReal.ofReal Mom := by gcongr
      _ = ENNReal.ofReal (K0 * Mom) := (ENNReal.ofReal_mul hK0).symm
  -- combine
  have hg0 : 0 ≤ ∫ r in (0 : ℝ)..r0, g r := by
    rw [intervalIntegral.integral_of_le hr0.le, integral_Ioc_eq_integral_Ioo]
    exact setIntegral_nonneg measurableSet_Ioo
      (fun r hr => (mul_nonneg (pow_nonneg hr.1.le _) (hΨ0 r hr.1.le)).trans (hle r hr))
  calc _ ≤ ENNReal.ofReal (4 ^ M * G * jbracket x ^ M) * ENNReal.ofReal (κ * ∫ r in (0 : ℝ)..r0, g r) +
        ENNReal.ofReal (K0 * Mom) := by
        gcongr
        exact hnear.trans (by gcongr)
    _ = ENNReal.ofReal (4 ^ M * G * jbracket x ^ M * (κ * ∫ r in (0 : ℝ)..r0, g r) + K0 * Mom) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have : 0 ≤ 4 ^ M * G * (κ * ∫ r in (0 : ℝ)..r0, g r) := by positivity
        have hKM : 0 ≤ K0 * Mom := by positivity
        nlinarith

end HRS.MS.S82N
