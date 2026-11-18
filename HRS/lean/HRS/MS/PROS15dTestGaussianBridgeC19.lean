import HRS.MS.PROS15dGaussianLimitB18
import HRS.MS.PROS15dPhysicalTiltConvergence
import HRS.MS.S21T4ProdC
import HRS.MS.S21T4ProdZ

/-!
# S15d: closure of a physical Gaussian test law under a spectral L² approximation

The approximation is in the physical spatial L² space, not under the tilted
law. The fourth-moment bound transfers it to the actual tilted Gaussian
probability space. This is a bridge to the spectral ONB reconstruction,
and does not assert the frozen S15d conclusion without that reconstruction.
-/
set_option autoImplicit false
noncomputable section
open HRS MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3

theorem s15d_physical_tilted_gaussian_of_spatial_approximation
    {d : ℕ} {μ : Measure (HRS.Euc d)} [IsProbabilityMeasure μ]
    (I : ProductGaussian μ)
    (V : I.Ω → ℝ) (hV : AEMeasurable V I.P)
    (hExp1 : Integrable (fun ω => Real.exp (-V ω)) I.P)
    (hExp2 : Integrable (fun ω => Real.exp (-(2 * V ω))) I.P)
    (f : HRS.Euc d → ℝ) (hf : MemLp f 2 μ)
    (u : ℕ → HRS.Euc d → ℝ) (hu : ∀ n, MemLp (u n) 2 μ)
    (hGaussian : ∀ n, HRS.IsCenteredGaussian
      ((r26t3_tilt I.P V).map (I.η (u n))))
    (hApprox : Tendsto (fun n => ∫ x, (u n x - f x) ^ 2 ∂μ)
      atTop (𝓝 0)) :
    HRS.IsCenteredGaussian ((r26t3_tilt I.P V).map (I.η f)) := by
  letI := I.mΩ
  letI := I.prob
  let Pt := r26t3_tilt I.P V
  letI : IsProbabilityMeasure Pt := r26t3_tilt_isProb I.P hV hExp1
  have hAC : Pt ≪ I.P := by
    unfold Pt r26t3_tilt
    intro s hs
    simp [withDensity_absolutelyContinuous I.P _ hs]
  let D : ℕ → I.Ω → ℝ := fun n ω => I.η (u n) ω - I.η f ω
  have hMem : ∀ n, MemLp (D n) 2 Pt := by
    intro n
    have hUn := s15d_L4_to_tilted_L2 (V := V) hV hExp1 hExp2
      (s15d_physical_first_chaos_L4 I (u n) (hu n))
    have hF := s15d_L4_to_tilted_L2 (V := V) hV hExp1 hExp2
      (s15d_physical_first_chaos_L4 I f hf)
    exact hUn.sub hF
  have hDifference : ∀ n,
      D n =ᵐ[Pt] I.η (fun x => u n x - f x) := by
    intro n
    have hlinear := s21t4_eta_linear I f (u n - f) (1 : ℝ)
      hf ((hu n).sub hf)
    have hfun : f + (1 : ℝ) • (u n - f) = u n := by
      ext x
      simp [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [hfun] at hlinear
    have hlinear' : D n =ᵐ[I.P] I.η (fun x => u n x - f x) := by
      filter_upwards [hlinear] with ω hw
      change I.η (u n) ω - I.η f ω = I.η (u n - f) ω
      simp only [one_smul, Pi.add_apply] at hw
      linarith
    exact hAC hlinear'
  have hSp : ∀ n, MemLp (fun x => u n x - f x) 2 μ :=
    fun n => (hu n).sub hf
  have hSecond :=
    s15d_physical_tilted_second_tendsto_of_spatial_second
      I V hV hExp1 hExp2 (fun n x => u n x - f x) hSp hApprox
  have hIntegral : ∀ n,
      (∫ ω, (D n ω) ^ 2 ∂Pt) =
      ∫ ω, I.η (fun x => u n x - f x) ω ^ 2 ∂Pt := by
    intro n
    refine integral_congr_ae ?_
    filter_upwards [hDifference n] with ω hw
    rw [hw]
  have hReal : Tendsto (fun n => ∫ ω, (D n ω) ^ 2 ∂Pt)
      atTop (𝓝 0) := by
    simpa only [hIntegral] using hSecond
  have hNormEq : ∀ n,
      eLpNorm (D n) 2 Pt =
        ENNReal.ofReal (Real.sqrt (∫ ω, (D n ω) ^ 2 ∂Pt)) := by
    intro n
    rw [s21t4_integral_sq_of_eLpNorm (D n) (hMem n)]
    rw [Real.sqrt_sq (ENNReal.toReal_nonneg)]
    exact (ENNReal.ofReal_toReal (hMem n).eLpNorm_ne_top).symm
  have hNorm : Tendsto (fun n => eLpNorm (D n) 2 Pt)
      atTop (𝓝 0) := by
    simp_rw [hNormEq]
    have hsqrt : Tendsto
        (fun n => Real.sqrt (∫ ω, (D n ω) ^ 2 ∂Pt))
        atTop (𝓝 0) := by
      simpa only [Function.comp_def, Real.sqrt_zero] using
        (Real.continuous_sqrt.tendsto 0).comp hReal
    simpa using ENNReal.tendsto_ofReal hsqrt
  have hX : ∀ n, AEStronglyMeasurable (I.η (u n)) Pt := by
    intro n
    exact (s15d_L4_to_tilted_L2 (V := V) hV hExp1 hExp2
      (s15d_physical_first_chaos_L4 I (u n) (hu n))).aestronglyMeasurable
  have hL2 : Tendsto
      (fun n => eLpNorm ((fun ω => I.η (u n) ω) - I.η f) 2 Pt)
      atTop (𝓝 0) := by
    change Tendsto (fun n => eLpNorm (D n) 2 Pt) atTop (𝓝 0)
    exact hNorm
  exact s15d_centered_gaussian_L2_limit Pt
    (fun n => I.η (u n)) (I.η f) hX hGaussian hL2

#print axioms s15d_physical_tilted_gaussian_of_spatial_approximation
end HRS.MS.R26T3
