import HRS.MS.ShiftFldAux17

/-!
# S79P: the generator in `L²(μ)`: `L u = -β⁻¹ 𝒜u - K̃ 𝒜u` a.e., continuity of the nonlocal term
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S79G

open HRS.Whole HRS.MS.UniqT3 HRS.MS.S21 HRS.MH.DualityRd
open HRS (Euc)

variable {d : ℕ}

/-- The stationary coefficient. -/
abbrev Cst (d : ℕ) (s a β : ℝ) : WholeCoeff d :=
  (quadraticGradientDyn d s a β).coeff (fun _ => thermalDensity d s a β)

theorem s79g_memLp_lin {s a β : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (ha : 0 < a) (hβ : 0 < β)
    {f : Euc d → ℝ} (hf : Continuous f) {K : ℝ} (hK : ∀ x, |f x| ≤ K * (1 + ‖x‖)) :
    MemLp f 2 (thermalMeasure d s a β) := by
  obtain ⟨C, c, BU, hT⟩ := S45.s45_thermal_data hd hs0 hsd ha hβ
  haveI : IsProbabilityMeasure (thermalMeasure d s a β) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  have h2 := s21_thermal_second_integrable hd hs0 hsd ha hβ
  rw [memLp_two_iff_integrable_sq hf.aestronglyMeasurable]
  refine Integrable.mono' ((integrable_const (2 * K ^ 2)).add (h2.const_mul (2 * K ^ 2)))
    (hf.pow 2).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  have hn := norm_nonneg x
  rw [Real.norm_eq_abs, abs_pow]
  have := hK x
  have h0 : 0 ≤ |f x| := abs_nonneg _
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (by simpa using hK 0)
  calc |f x| ^ 2 ≤ (K * (1 + ‖x‖)) ^ 2 := pow_le_pow_left₀ h0 this 2
    _ ≤ 2 * K ^ 2 + 2 * K ^ 2 * ‖x‖ ^ 2 := by nlinarith [sq_nonneg (K * (1 - ‖x‖)), sq_nonneg K]
    _ = _ := by simp only [Pi.add_apply]

theorem s79g_nl_cont (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) (hρ : IsThermalEquilibrium d s a β (thermalDensity d s a β))
    {u : Euc d → ℝ} (hu : HRS.MemCb 2 u) (hLc : Continuous (generatorW (Cst d s a β) 0 u)) :
    Continuous (nlTermRd (quadraticGradientDyn d s a β) (thermalDensity d s a β) u) := by
  obtain ⟨C, c, BU, hT⟩ := S45.s45_thermal_data hd hs0 hsd ha hβ
  have hU2 : ContDiff ℝ 2 (HRS.Whole.convMeasure (rieszKernel d s) (thermalMeasure d s a β)) := by
    exact_mod_cast contDiff_infty.1 hT.Usmooth 2
  have hbc : Continuous (bdr d s a β (thermalDensity d s a β)) := by
    have : bdr d s a β (thermalDensity d s a β) = fun x =>
        -(a • x + gradient (HRS.Whole.convMeasure (rieszKernel d s) (thermalMeasure d s a β)) x) :=
      funext fun x => s79g_drift hd hs0 hsd ha hβ hρ x
    rw [this]
    exact ((continuous_id.const_smul a).add (S45.s45_contDiff_gradient hU2).continuous).neg
  have hgc : Continuous (gradient u) := (S45.s45_contDiff_gradient hu.1).continuous
  have : nlTermRd (quadraticGradientDyn d s a β) (thermalDensity d s a β) u = fun x =>
      (quadraticGradientDyn d s a β).invβ * Laplacian.laplacian u x +
        inner ℝ (bdr d s a β (thermalDensity d s a β) x) (gradient u x) -
        generatorW (Cst d s a β) 0 u x := by
    funext x
    rw [s79g_gen]
    ring
  rw [this]
  exact ((continuous_const.mul (s21_lap_continuous hu.1)).add (hbc.inner hgc)).sub hLc

/-- `L u = -β⁻¹ 𝒜u - ∫ g(x-y) 𝒜u(y) dμ(y)` a.e. (with respect to `volume`). -/
theorem s79g_L_eq (hd : 2 ≤ d) {s : ℝ} (hs : 0 < s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) (hρ : IsThermalEquilibrium d s a β (thermalDensity d s a β))
    {u : Euc d → ℝ} (hu : HRS.MemCb 2 u) (hLc : Continuous (generatorW (Cst d s a β) 0 u)) :
    ∀ᵐ x ∂(volume : Measure (Euc d)), generatorW (Cst d s a β) 0 u x =
      -(β⁻¹ * Aop d s a β (thermalDensity d s a β) u x) -
        ∫ y, rieszKernel d s (x - y) * (thermalDensity d s a β y *
          Aop d s a β (thermalDensity d s a β) u y) := by
  have hnl := s79g_nl_ae hd hs hsd ha hβ hρ hu (s79g_nl_cont hd hs.le hsd ha hβ hρ hu hLc)
  filter_upwards [hnl] with x hx
  rw [s79g_gen, hx]
  unfold Aop
  have hb : β⁻¹ * β = 1 := inv_mul_cancel₀ hβ.ne'
  have : (quadraticGradientDyn d s a β).invβ = β⁻¹ := rfl
  rw [this]
  have e : β⁻¹ * (-(Laplacian.laplacian u x) - β * inner ℝ (bdr d s a β (thermalDensity d s a β) x) (gradient u x)) =
      -(β⁻¹ * Laplacian.laplacian u x) - inner ℝ (bdr d s a β (thermalDensity d s a β) x) (gradient u x) := by
    linear_combination (-(inner ℝ (bdr d s a β (thermalDensity d s a β) x) (gradient u x))) * hb
  rw [e]
  show _ = _ - _
  ring

end HRS.MS.S79G
