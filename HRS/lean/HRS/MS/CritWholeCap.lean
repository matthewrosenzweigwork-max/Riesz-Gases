import HRS.Whole.Critical
import HRS.Whole.Q34Aux3

/-!
# S8.1.K1 -- critical logarithmic coefficient of the capped squared pole

Worker S81, namespace `HRS.Whole.BreakdownS81`, helper prefix `s81bd_`.

`s81bd_cap_square_log`: at `s = d/2`, the integral of `min(g, H)^2` against a bounded Lipschitz
probability density equals `(2 |S^{d-1}|/d) ρ(x) log H` up to `|S^{d-1}|/d M + |S^{d-1}| Λ + 1`.
Helpers `s81bd_integral_conv` (change of variables) and `s81bd_integral_radial_real` (real radial
integrals) are shared with the later packets.
-/

set_option autoImplicit false

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff
open HRS HRS.Whole

namespace HRS.Whole.BreakdownS81

theorem s81bd_sphereArea_pos' {d : ℕ} (hd : 1 ≤ d) : 0 < sphereArea d := by
  unfold sphereArea
  have h0 : (0 : ℝ) < (d : ℝ) / 2 := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    positivity
  have : 0 < Real.Gamma ((d : ℝ) / 2) := Real.Gamma_pos_of_pos h0
  have := Real.pi_pos
  positivity

/-- `∫ G(x - y) d(ρ dy) = ∫ ρ(x - z) G(z) dz`. -/
theorem s81bd_integral_conv {d : ℕ} {ρ : Euc d → ℝ} (hρ : IsProbDensity ρ) (G : Euc d → ℝ)
    (x : Euc d) :
    ∫ y, G (x - y) ∂(withDensityReal ρ) = ∫ z, ρ (x - z) * G z := by
  unfold withDensityReal
  have hm : Measurable fun y => ENNReal.ofReal (ρ y) := ENNReal.measurable_ofReal.comp hρ.measurable
  rw [integral_withDensity_eq_integral_toReal_smul₀ hm.aemeasurable
    (Filter.Eventually.of_forall fun y => ENNReal.ofReal_lt_top)]
  have h1 : ∀ y, (ENNReal.ofReal (ρ y)).toReal • G (x - y) = ρ y * G (x - y) := fun y => by
    rw [ENNReal.toReal_ofReal (hρ.nonneg y), smul_eq_mul]
  simp_rw [h1]
  rw [← integral_sub_left_eq_self (fun y => ρ y * G (x - y)) volume x]
  simp only [sub_sub_cancel]

theorem s81bd_integrable_conv {d : ℕ} {ρ : Euc d → ℝ} (hρ : IsProbDensity ρ) (x : Euc d) :
    Integrable (fun z => ρ (x - z)) := 
  (HRS.Whole.Q34.integrable_of_isProbDensity hρ).comp_sub_left x

/-- Radial integral of `‖z‖^p` over a shell `R ≤ ‖z‖ < r₁`. -/
theorem s81bd_lintegral_shell_pow {d : ℕ} (hd : 1 ≤ d) {R r₁ : ℝ} (hR : 0 < R) (p : ℝ) :
    ∫⁻ z in {z : Euc d | ‖z‖ ∈ Set.Ico R r₁}, ENNReal.ofReal (‖z‖ ^ p) =
      ENNReal.ofReal (sphereArea d) *
        ∫⁻ t in Set.Ico R r₁, ENNReal.ofReal (t ^ ((d : ℝ) - 1 + p)) := by
  rw [Q34.lintegral_radial_set hd (Set.Ico R r₁) measurableSet_Ico
    (fun t => ENNReal.ofReal (t ^ p)) (by fun_prop)]
  congr 1
  have h1 : Set.Ioi (0 : ℝ) ∩ Set.Ico R r₁ = Set.Ico R r₁ := by
    ext t; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ico]
    exact ⟨fun h => h.2, fun h => ⟨hR.trans_le h.1, h⟩⟩
  rw [h1]
  refine setLIntegral_congr_fun measurableSet_Ico fun t ht => ?_
  have ht0 : 0 < t := hR.trans_le ht.1
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub hd]; simp
  rw [← Real.rpow_natCast, this, ← Real.rpow_add ht0]

theorem s81bd_lintegral_shell_inv {d : ℕ} (hd : 1 ≤ d) {R : ℝ} (hR : 0 < R) (hR1 : R ≤ 1) :
    ∫⁻ z in {z : Euc d | ‖z‖ ∈ Set.Ico R 1}, ENNReal.ofReal (‖z‖ ^ (-(d : ℝ))) =
      ENNReal.ofReal (sphereArea d * Real.log (1 / R)) := by
  have hA := s81bd_sphereArea_pos' hd
  rw [s81bd_lintegral_shell_pow hd hR, ENNReal.ofReal_mul hA.le]
  congr 1
  have h1 : ∀ t ∈ Set.Ico R 1, ENNReal.ofReal (t ^ ((d : ℝ) - 1 + -(d : ℝ))) =
      ENNReal.ofReal (t⁻¹) := by
    intro t ht
    congr 1
    have : (d : ℝ) - 1 + -(d : ℝ) = -1 := by ring
    rw [this, Real.rpow_neg_one]
  rw [setLIntegral_congr_fun measurableSet_Ico h1, setLIntegral_congr Ico_ae_eq_Ioc]
  have hint : IntegrableOn (fun t : ℝ => t⁻¹) (Set.Ioc R 1) := by
    have hc : ContinuousOn (fun t : ℝ => t⁻¹) (Set.Icc R 1) :=
      continuousOn_inv₀.mono fun t ht => (hR.trans_le ht.1).ne'
    exact (hc.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint]
  · congr 1
    rw [← intervalIntegral.integral_of_le hR1, integral_inv_of_pos hR one_pos]
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact (inv_pos.2 (hR.trans ht.1)).le

theorem s81bd_lintegral_shell_one {d : ℕ} (hd : 1 ≤ d) {R : ℝ} (hR : 0 < R) :
    ∫⁻ z in {z : Euc d | ‖z‖ ∈ Set.Ico R 1}, ENNReal.ofReal (‖z‖ ^ (1 - (d : ℝ))) =
      ENNReal.ofReal (sphereArea d * (1 - R)) := by
  have hA := s81bd_sphereArea_pos' hd
  rw [s81bd_lintegral_shell_pow hd hR, ENNReal.ofReal_mul hA.le]
  congr 1
  have h1 : ∀ t ∈ Set.Ico R 1, ENNReal.ofReal (t ^ ((d : ℝ) - 1 + (1 - (d : ℝ)))) = 1 := by
    intro t ht
    have : (d : ℝ) - 1 + (1 - (d : ℝ)) = 0 := by ring
    rw [this, Real.rpow_zero, ENNReal.ofReal_one]
  rw [setLIntegral_congr_fun measurableSet_Ico h1, lintegral_const, one_mul,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ico]

theorem s81bd_cap_square_log {d : ℕ} (hd : 2 ≤ d) (M : ℝ) (Λ : ℝ≥0)
    (ρ : Euc d → ℝ) (hρ : IsProbDensity ρ) (hbound : ∀ x, ρ x ≤ M)
    (hlip : LipschitzWith Λ ρ) (H : ℝ) (hH : 1 ≤ H) (x : Euc d) :
    Integrable (fun y => truncKernel d ((d : ℝ) / 2) H (x - y) ^ 2)
      (withDensityReal ρ) ∧
    |(∫ y, truncKernel d ((d : ℝ) / 2) H (x - y) ^ 2 ∂(withDensityReal ρ)) -
        (2 * sphereArea d / (d : ℝ)) * ρ x * Real.log H| ≤
      sphereArea d / (d : ℝ) * M + sphereArea d * (Λ : ℝ) + 1 := by
  have hd1 : 1 ≤ d := by omega
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
  have hA := s81bd_sphereArea_pos' hd1
  have hprob := Q34.isProbabilityMeasure_nu hρ
  have hM0 : 0 ≤ M := (hρ.nonneg 0).trans (hbound 0)
  have hH0 : 0 < H := by linarith
  have hs0 : ((d : ℝ) / 2) ≠ 0 := by positivity
  have hkern : ∀ z : Euc d, rieszKernel d ((d : ℝ) / 2) z = ‖z‖ ^ (-((d : ℝ) / 2)) :=
    Q34.rieszKernel_eq hs0
  set U : Euc d → ℝ := fun z => truncKernel d ((d : ℝ) / 2) H z ^ 2 with hU
  have hUmeas : Measurable U := by
    have : Measurable (truncKernel d ((d : ℝ) / 2) H) :=
      (Q34.measurable_rieszKernel hs0).min measurable_const
    exact this.pow_const 2
  have hk0 : ∀ z : Euc d, 0 ≤ rieszKernel d ((d : ℝ) / 2) z := fun z => by
    rw [hkern]; exact Real.rpow_nonneg (norm_nonneg _) _
  have hT0 : ∀ z : Euc d, 0 ≤ truncKernel d ((d : ℝ) / 2) H z := fun z =>
    le_min (hk0 z) hH0.le
  have hTH : ∀ z : Euc d, truncKernel d ((d : ℝ) / 2) H z ≤ H := fun z => min_le_right _ _
  have hU0 : ∀ z, 0 ≤ U z := fun z => sq_nonneg _
  have hUH : ∀ z, U z ≤ H ^ 2 := fun z =>
    pow_le_pow_left₀ (hT0 z) (hTH z) 2
  have hint1 : Integrable (fun y => U (x - y)) (withDensityReal ρ) :=
    Integrable.of_bound (hUmeas.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
      (H ^ 2) (ae_of_all _ fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hU0 _)]; exact hUH _)
  refine ⟨hint1, ?_⟩
  have hconv : ∫ y, truncKernel d ((d : ℝ) / 2) H (x - y) ^ 2 ∂(withDensityReal ρ) =
      ∫ z, ρ (x - z) * U z := s81bd_integral_conv hρ U x
  rw [hconv]
  -- the cutoff radius
  set R : ℝ := H ^ (-(2 : ℝ) / d) with hRdef
  have hRpos : 0 < R := Real.rpow_pos_of_pos hH0 _
  have hR1 : R ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hH (by
      have : 0 ≤ (2 : ℝ) / d := by positivity
      have e : -(2 : ℝ) / d = -((2 : ℝ) / d) := by ring
      linarith)
  have hRd : R ^ d * H ^ 2 = 1 := by
    have h1 : R ^ d = H ^ (-(2 : ℝ)) := by
      rw [hRdef, ← Real.rpow_natCast, ← Real.rpow_mul hH0.le]
      congr 1
      field_simp
    rw [h1, show H ^ 2 = H ^ (2 : ℝ) by norm_cast, ← Real.rpow_add hH0]
    simp
  have hRs : R ^ (-((d : ℝ) / 2)) = H := by
    rw [hRdef, ← Real.rpow_mul hH0.le]
    have : -(2 : ℝ) / d * -((d : ℝ) / 2) = 1 := by field_simp
    rw [this, Real.rpow_one]
  have hlogR : Real.log (1 / R) = (2 / (d : ℝ)) * Real.log H := by
    rw [one_div, Real.log_inv, hRdef, Real.log_rpow hH0]
    ring
  -- the three regions
  set S : Set (Euc d) := {z | ‖z‖ ∈ Set.Ico R 1} with hS
  have hSm : MeasurableSet S := measurable_norm measurableSet_Ico
  set B3 : Set (Euc d) := {z | 1 ≤ ‖z‖} with hB3
  have hB3m : MeasurableSet B3 := measurable_norm measurableSet_Ici
  -- values of `U`
  have hU_S : ∀ z ∈ S, U z = ‖z‖ ^ (-(d : ℝ)) := by
    intro z hz
    have hz' : R ≤ ‖z‖ ∧ ‖z‖ < 1 := hz
    have hzpos : 0 < ‖z‖ := hRpos.trans_le hz'.1
    have hle : ‖z‖ ^ (-((d : ℝ) / 2)) ≤ H := by
      rw [← hRs]
      exact Real.rpow_le_rpow_of_nonpos hRpos hz'.1 (by linarith)
    simp only [hU, truncKernel, hkern, min_eq_left hle]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hzpos.le]
    congr 1
    push_cast
    ring
  have hU_B3 : ∀ z ∈ B3, U z ≤ 1 := by
    intro z hz
    have hz' : 1 ≤ ‖z‖ := hz
    have hle : ‖z‖ ^ (-((d : ℝ) / 2)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hz' (by linarith)
    have h1 : truncKernel d ((d : ℝ) / 2) H z ≤ 1 := by
      simp only [truncKernel, hkern]
      exact (min_le_left _ _).trans hle
    calc U z = truncKernel d ((d : ℝ) / 2) H z ^ 2 := rfl
      _ ≤ 1 ^ 2 := pow_le_pow_left₀ (hT0 z) h1 2
      _ = 1 := one_pow 2
  -- the model function
  set h : Euc d → ℝ := S.indicator (fun z => ρ x * ‖z‖ ^ (-(d : ℝ))) with hh
  have hh_nn : ∀ z, 0 ≤ h z := fun z => by
    simp only [hh, Set.indicator]
    split_ifs
    · exact mul_nonneg (hρ.nonneg x) (Real.rpow_nonneg (norm_nonneg _) _)
    · exact le_rfl
  have hh_meas : Measurable h :=
    (measurable_const.mul (measurable_norm.pow_const _)).indicator hSm
  have hhL : ∫⁻ z, ENNReal.ofReal (h z) = ENNReal.ofReal (ρ x * (sphereArea d * Real.log (1 / R))) := by
    have e1 : ∀ z, ENNReal.ofReal (h z) =
        S.indicator (fun z => ENNReal.ofReal (ρ x) * ENNReal.ofReal (‖z‖ ^ (-(d : ℝ)))) z := by
      intro z
      by_cases hz : z ∈ S
      · simp only [hh, Set.indicator_of_mem hz]
        rw [ENNReal.ofReal_mul (hρ.nonneg x)]
      · simp [hh, Set.indicator_of_notMem hz]
    simp_rw [e1]
    rw [lintegral_indicator hSm, lintegral_const_mul _ (by fun_prop),
      s81bd_lintegral_shell_inv hd1 hRpos hR1, ← ENNReal.ofReal_mul (hρ.nonneg x)]
  have hlogpos : 0 ≤ Real.log (1 / R) := Real.log_nonneg (by rw [le_div_iff₀ hRpos]; linarith)
  have hh_int : Integrable h ∧ ∫ z, h z = ρ x * (sphereArea d * Real.log (1 / R)) := by
    have hc : 0 ≤ ρ x * (sphereArea d * Real.log (1 / R)) :=
      mul_nonneg (hρ.nonneg x) (mul_nonneg hA.le hlogpos)
    refine ⟨(Q34.integrable_of_lintegral_le hh_meas hh_nn hc (hhL.le)).1, ?_⟩
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hh_nn)
      hh_meas.aestronglyMeasurable, hhL, ENNReal.toReal_ofReal hc]
  -- the integrand
  set f : Euc d → ℝ := fun z => ρ (x - z) * U z with hf
  have hf_meas : Measurable f :=
    (hρ.measurable.comp (measurable_const.sub measurable_id)).mul hUmeas
  have hf_int : Integrable f := by
    refine Integrable.mono' ((s81bd_integrable_conv hρ x).const_mul (H ^ 2))
      hf_meas.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hρ.nonneg _) (hU0 z))]
    rw [mul_comm (H ^ 2)]
    exact mul_le_mul_of_nonneg_left (hUH z) (hρ.nonneg _)
  -- pointwise bound
  set e : Euc d → ℝ≥0∞ := fun z =>
    (Metric.ball (0 : Euc d) R).indicator (fun _ => ENNReal.ofReal (M * H ^ 2)) z +
    S.indicator (fun z => ENNReal.ofReal (Λ : ℝ) * ENNReal.ofReal (‖z‖ ^ (1 - (d : ℝ)))) z +
    B3.indicator (fun z => ENNReal.ofReal (ρ (x - z))) z with he
  have hpt : ∀ z, ENNReal.ofReal ‖f z - h z‖ ≤ e z := by
    intro z
    by_cases hz1 : ‖z‖ < R
    · have hzS : z ∉ S := fun hz => absurd hz.1 (not_le.2 hz1)
      have hzB : z ∈ Metric.ball (0 : Euc d) R := by simpa using hz1
      have hh0 : h z = 0 := by simp [hh, Set.indicator_of_notMem hzS]
      have : ‖f z - h z‖ ≤ M * H ^ 2 := by
        rw [hh0, sub_zero, hf]
        simp only
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hρ.nonneg _) (hU0 z))]
        exact mul_le_mul (hbound _) (hUH z) (hU0 z) hM0
      calc ENNReal.ofReal ‖f z - h z‖ ≤ ENNReal.ofReal (M * H ^ 2) := ENNReal.ofReal_le_ofReal this
        _ = (Metric.ball (0 : Euc d) R).indicator (fun _ => ENNReal.ofReal (M * H ^ 2)) z := by
            rw [Set.indicator_of_mem hzB]
        _ ≤ e z := by
            simp only [he]
            exact le_trans (le_add_right le_rfl) (le_add_right le_rfl)
    · replace hz1 := not_lt.1 hz1
      by_cases hz2 : ‖z‖ < 1
      · have hzS : z ∈ S := ⟨hz1, hz2⟩
        have hzpos : 0 < ‖z‖ := hRpos.trans_le hz1
        have hnotB : z ∉ Metric.ball (0 : Euc d) R := by simpa using hz1
        have hfh : f z - h z = (ρ (x - z) - ρ x) * ‖z‖ ^ (-(d : ℝ)) := by
          simp only [hf, hh, Set.indicator_of_mem hzS, hU_S z hzS]
          ring
        have hlz : |ρ (x - z) - ρ x| ≤ (Λ : ℝ) * ‖z‖ := by
          have := hlip.dist_le_mul (x - z) x
          rw [Real.dist_eq, dist_eq_norm] at this
          simpa using this
        have hpow : ‖z‖ * ‖z‖ ^ (-(d : ℝ)) = ‖z‖ ^ (1 - (d : ℝ)) := by
          have e1 : ‖z‖ ^ (1 - (d : ℝ)) = ‖z‖ ^ ((1 : ℝ) + -(d : ℝ)) := by ring_nf
          rw [e1, Real.rpow_add hzpos, Real.rpow_one]
        have hbd : ‖f z - h z‖ ≤ (Λ : ℝ) * ‖z‖ ^ (1 - (d : ℝ)) := by
          rw [hfh, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
          calc |ρ (x - z) - ρ x| * ‖z‖ ^ (-(d : ℝ)) ≤ ((Λ : ℝ) * ‖z‖) * ‖z‖ ^ (-(d : ℝ)) :=
                mul_le_mul_of_nonneg_right hlz (Real.rpow_nonneg (norm_nonneg _) _)
            _ = (Λ : ℝ) * (‖z‖ * ‖z‖ ^ (-(d : ℝ))) := by ring
            _ = _ := by rw [hpow]
        calc ENNReal.ofReal ‖f z - h z‖ ≤ ENNReal.ofReal ((Λ : ℝ) * ‖z‖ ^ (1 - (d : ℝ))) :=
              ENNReal.ofReal_le_ofReal hbd
          _ = S.indicator (fun z => ENNReal.ofReal (Λ : ℝ) * ENNReal.ofReal (‖z‖ ^ (1 - (d : ℝ)))) z := by
              rw [Set.indicator_of_mem hzS, ENNReal.ofReal_mul (NNReal.coe_nonneg Λ)]
          _ ≤ e z := by
              simp only [he]
              exact le_trans (le_add_left le_rfl) (le_add_right le_rfl)
      · replace hz2 := not_lt.1 hz2
        have hzS : z ∉ S := fun hz => absurd hz.2 (not_lt.2 hz2)
        have hzB : z ∈ B3 := hz2
        have hh0 : h z = 0 := by simp [hh, Set.indicator_of_notMem hzS]
        have : ‖f z - h z‖ ≤ ρ (x - z) := by
          rw [hh0, sub_zero, hf]
          simp only
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hρ.nonneg _) (hU0 z))]
          calc ρ (x - z) * U z ≤ ρ (x - z) * 1 :=
                mul_le_mul_of_nonneg_left (hU_B3 z hzB) (hρ.nonneg _)
            _ = ρ (x - z) := mul_one _
        calc ENNReal.ofReal ‖f z - h z‖ ≤ ENNReal.ofReal (ρ (x - z)) := ENNReal.ofReal_le_ofReal this
          _ = B3.indicator (fun z => ENNReal.ofReal (ρ (x - z))) z := by
              rw [Set.indicator_of_mem hzB]
          _ ≤ e z := by
              simp only [he]
              exact le_add_left le_rfl
  -- the integral of the bound
  have he1 : ∫⁻ z, e z ≤ ENNReal.ofReal (sphereArea d / (d : ℝ) * M + sphereArea d * (Λ : ℝ) + 1) := by
    set a : Euc d → ℝ≥0∞ := (Metric.ball (0 : Euc d) R).indicator
      (fun _ => ENNReal.ofReal (M * H ^ 2)) with ha
    set b : Euc d → ℝ≥0∞ := S.indicator
      (fun z => ENNReal.ofReal (Λ : ℝ) * ENNReal.ofReal (‖z‖ ^ (1 - (d : ℝ)))) with hb
    set c : Euc d → ℝ≥0∞ := B3.indicator (fun z => ENNReal.ofReal (ρ (x - z))) with hc
    have ma : Measurable a := measurable_const.indicator Metric.isOpen_ball.measurableSet
    have mb : Measurable b :=
      (measurable_const.mul (ENNReal.measurable_ofReal.comp
        (measurable_norm.pow_const _))).indicator hSm
    have heabc : ∫⁻ z, e z = (∫⁻ z, a z) + (∫⁻ z, b z) + ∫⁻ z, c z := by
      show ∫⁻ z, (a z + b z + c z) = _
      refine (lintegral_add_left (ma.add mb) c).trans ?_
      congr 1
      exact lintegral_add_left ma b
    have k1 : ∫⁻ z, a z = ENNReal.ofReal (sphereArea d / (d : ℝ) * M) := by
      rw [ha, lintegral_indicator Metric.isOpen_ball.measurableSet, setLIntegral_const,
        Q34.volume_ball_eq hd1 hRpos, ← ENNReal.ofReal_mul (mul_nonneg hM0 (sq_nonneg H))]
      congr 1
      have : R ^ d = (H ^ 2)⁻¹ := by
        exact eq_inv_of_mul_eq_one_left hRd
      rw [this]
      field_simp
    have k2 : ∫⁻ z, b z ≤ ENNReal.ofReal (sphereArea d * (Λ : ℝ)) := by
      rw [hb, lintegral_indicator hSm,
        lintegral_const_mul (f := fun z : Euc d => ENNReal.ofReal (‖z‖ ^ (1 - (d : ℝ)))) _
          (ENNReal.measurable_ofReal.comp (measurable_norm.pow_const _)),
        s81bd_lintegral_shell_one hd1 hRpos, ← ENNReal.ofReal_mul (NNReal.coe_nonneg Λ)]
      refine ENNReal.ofReal_le_ofReal ?_
      have := NNReal.coe_nonneg Λ
      nlinarith [mul_nonneg hA.le hRpos.le, mul_nonneg this hA.le]
    have k3 : ∫⁻ z, c z ≤ ENNReal.ofReal 1 := by
      rw [hc, lintegral_indicator hB3m]
      refine (setLIntegral_le_lintegral _ _).trans (le_of_eq ?_)
      rw [← ofReal_integral_eq_lintegral_ofReal (s81bd_integrable_conv hρ x)
        (Filter.Eventually.of_forall fun z => hρ.nonneg _)]
      congr 1
      rw [integral_sub_left_eq_self (fun z => ρ z) volume x]
      exact hρ.integral_one
    rw [heabc]
    calc _ ≤ ENNReal.ofReal (sphereArea d / (d : ℝ) * M) +
          ENNReal.ofReal (sphereArea d * (Λ : ℝ)) + ENNReal.ofReal 1 :=
          add_le_add (add_le_add k1.le k2) k3
      _ = _ := by
          have h1 : 0 ≤ sphereArea d / (d : ℝ) * M := by positivity
          have h2 : 0 ≤ sphereArea d * (Λ : ℝ) := mul_nonneg hA.le (NNReal.coe_nonneg Λ)
          rw [← ENNReal.ofReal_add h1 h2, ← ENNReal.ofReal_add (add_nonneg h1 h2) zero_le_one]
  have hfin : |(∫ z, f z) - ∫ z, h z| ≤ sphereArea d / (d : ℝ) * M + sphereArea d * (Λ : ℝ) + 1 := by
    rw [← integral_sub hf_int hh_int.1, ← Real.norm_eq_abs]
    refine (norm_integral_le_lintegral_norm _).trans ?_
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    exact (lintegral_mono hpt).trans he1
  rw [hh_int.2, hlogR] at hfin
  have : (2 * sphereArea d / (d : ℝ)) * ρ x * Real.log H =
      ρ x * (sphereArea d * (2 / (d : ℝ) * Real.log H)) := by ring
  rw [this]
  exact hfin

end HRS.Whole.BreakdownS81
