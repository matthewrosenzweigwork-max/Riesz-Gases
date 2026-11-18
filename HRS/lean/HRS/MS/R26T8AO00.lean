import HRS.MS.R26T8AO00d
import HRS.MS.R26T8AF11
import HRS.MS.FeatDecAux3

/-!
# S8.2 observed-time layer, packet T8A.O00: the actual `aSource` is bounded in `L²(ρ dx)`

`aSource μ f x = (1/2) ∫ hSource f x y dμ(y)` with `hSource f x y = ⟨∇f x - ∇f y, ∇K(x-y)⟩`.  At the unique thermal
density `ρ₀` (a Schwartz density, hence bounded), the commutator-kernel bound of helper c and the density bound of
helper d give `|aSource f x| ≤ C A` uniformly in `x`; the measure is a probability measure, so `L²` follows.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_aSource_bound (d : ℕ) (hd : 2 ≤ d) (a beta : ℝ) (ha : 0 < a) (hbeta : 0 < beta) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ rho : Euc d → ℝ, IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ f : Euc d → ℝ, ∀ A : ℝ, 0 ≤ A → TestBound (testOrder d) A f →
      MemLp (aSource (HRS.Whole.withDensityReal rho) f) 2 (HRS.Whole.withDensityReal rho) ∧
      eLpNorm (aSource (HRS.Whole.withDensityReal rho) f) 2 (HRS.Whole.withDensityReal rho) ≤
        ENNReal.ofReal (C * A) := by
  have hd1 : 1 ≤ d := by omega
  have hs0 : 0 < criticalS d := HRS.MS.S82R.s82r_criticalS_pos hd1
  have hsd : criticalS d < (d : ℝ) := HRS.MS.S82R.s82r_criticalS_lt hd1
  by_cases hex : ∃ ρ, IsThermalEquilibrium d (criticalS d) a beta ρ
  swap
  · exact ⟨0, le_rfl, fun rho hrho => (hex ⟨rho, hrho⟩).elim⟩
  obtain ⟨ρ₀, hρ₀eq, hρ₀, hS⟩ : ∃ ρ₀ : Euc d → ℝ,
      (∀ rho : Euc d → ℝ, IsThermalEquilibrium d (criticalS d) a beta rho → rho = ρ₀) ∧
      IsThermalEquilibrium d (criticalS d) a beta ρ₀ ∧ IsSchwartzDensity ρ₀ := by
    obtain ⟨r, hr⟩ := hex
    exact ⟨thermalDensity d (criticalS d) a beta,
      fun rho h => (HRS.MS.S85.s85_thermal_eq hd hs0 hsd ha hbeta h).1,
      (HRS.MS.S85.s85_thermal_eq hd hs0 hsd ha hbeta hr).2,
      HRS.MS.S85.s85_thermal_schwartz hd hs0 hsd ha hbeta⟩
  obtain ⟨ψ, hψ⟩ := hS.2
  have hρm : Measurable ρ₀ := by
    rw [← hψ]
    exact ψ.continuous.measurable
  have hρ0 : ∀ y, 0 ≤ ρ₀ y := hS.1.nonneg
  set M : ℝ := ‖ψ.toBoundedContinuousFunction‖ with hMdef
  have hM0 : 0 ≤ M := norm_nonneg _
  have hρM : ∀ y, ρ₀ y ≤ M := by
    intro y
    have h := BoundedContinuousFunction.norm_coe_le_norm ψ.toBoundedContinuousFunction y
    rw [Real.norm_eq_abs] at h
    rw [← hψ, ← SchwartzMap.toBoundedContinuousFunction_apply]
    exact le_trans (le_abs_self _) h
  haveI hprob : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ₀) :=
    HRS.Whole.Q09A.measure_isProb hρ₀.2.1
  have hmass : ∫⁻ y, ENNReal.ofReal (ρ₀ y) = 1 := by
    rw [← measure_univ (μ := HRS.Whole.withDensityReal ρ₀)]
    unfold HRS.Whole.withDensityReal
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  set ind : Euc d → ℝ := (Metric.ball (0 : Euc d) 1).indicator (fun z => ‖z‖ ^ (-criticalS d)) with hind
  have hindm : Measurable ind :=
    ((measurable_norm.pow_const (-criticalS d))).indicator measurableSet_ball
  have hJ : (∫⁻ z, ENNReal.ofReal (ind z)) < ⊤ :=
    r26t8a_o00d_ball_lt_top hsd hd1
  set Jr : ℝ := (∫⁻ z, ENNReal.ofReal (ind z)).toReal with hJr
  have hJr0 : 0 ≤ Jr := ENNReal.toReal_nonneg
  have hJE : ENNReal.ofReal (M * Jr + 2) = ENNReal.ofReal M * (∫⁻ z, ENNReal.ofReal (ind z)) + 2 := by
    rw [ENNReal.ofReal_add (mul_nonneg hM0 hJr0) (by norm_num), ENNReal.ofReal_mul hM0,
      hJr, ENNReal.ofReal_toReal hJ.ne, ENNReal.ofReal_ofNat]
  refine ⟨criticalS d * (M * Jr + 2) / 2, by positivity, ?_⟩
  intro rho hrho f A hA hT
  rw [hρ₀eq rho hrho]
  have hind0 : ∀ z, 0 ≤ ind z := fun z =>
    indicator_nonneg (fun z _ => Real.rpow_nonneg (norm_nonneg _) _) z
  have hf : ContDiff ℝ ∞ f := hT.1
  have h1 : ∀ y, ‖iteratedFDeriv ℝ 1 f y‖ ≤ A := fun y => hT.2 1 le_rfl (by unfold testOrder; omega) y
  have h2 : ∀ y, ‖iteratedFDeriv ℝ 2 f y‖ ≤ A :=
    fun y => hT.2 2 (by norm_num) (by unfold testOrder; omega) y
  -- measurability of the commutator kernel and of `aSource`
  have hG : Measurable (gradient f) := by
    unfold gradient
    exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.measurable.comp (measurable_fderiv ℝ f)
  have hK : Measurable (rieszKernelGrad d (criticalS d)) := by
    unfold rieszKernelGrad gradient
    exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.measurable.comp
      (measurable_fderiv ℝ (rieszKernel d (criticalS d)))
  have hHm : Measurable (fun p : Euc d × Euc d =>
      commutatorKernel d (criticalS d) (gradient f) p.1 p.2) := by
    unfold commutatorKernel
    exact ((hG.comp measurable_fst).sub (hG.comp measurable_snd)).inner
      (hK.comp (measurable_fst.sub measurable_snd))
  have hAm : StronglyMeasurable (fun x => ∫ y, commutatorKernel d (criticalS d) (gradient f) x y
      ∂(HRS.Whole.withDensityReal ρ₀)) :=
    hHm.stronglyMeasurable.integral_prod_right'
  have hAs : StronglyMeasurable (aSource (HRS.Whole.withDensityReal ρ₀) f) := by
    unfold aSource hSource
    exact hAm.const_mul (1 / 2)
  -- pointwise bound of the kernel in `ENNReal`
  have hpt : ∀ x y, ‖commutatorKernel d (criticalS d) (gradient f) x y‖ₑ ≤
      ENNReal.ofReal (A * criticalS d) * (ENNReal.ofReal (ind (x - y)) + 2) := by
    intro x y
    have h := r26t8a_o00c_pt hs0 f hf A hA h1 h2 x y
    rw [← ofReal_norm_eq_enorm]
    calc ENNReal.ofReal ‖commutatorKernel d (criticalS d) (gradient f) x y‖
        ≤ ENNReal.ofReal (A * criticalS d * (ind (x - y) + 2)) := ENNReal.ofReal_le_ofReal h
      _ = ENNReal.ofReal (A * criticalS d) * (ENNReal.ofReal (ind (x - y)) + 2) := by
          rw [ENNReal.ofReal_mul (mul_nonneg hA hs0.le), ENNReal.ofReal_add (hind0 _) (by norm_num),
            ENNReal.ofReal_ofNat]
  -- the `L¹(μ)` bound in `ENNReal`, uniformly in `x`
  have hdens : ∀ x, ∫⁻ y, ‖commutatorKernel d (criticalS d) (gradient f) x y‖ₑ ∂(HRS.Whole.withDensityReal ρ₀) ≤
      ENNReal.ofReal (A * criticalS d) * (ENNReal.ofReal M * (∫⁻ z, ENNReal.ofReal (ind z)) + 2) := by
    intro x
    have hHx : Measurable (fun y => ‖commutatorKernel d (criticalS d) (gradient f) x y‖ₑ) :=
      (hHm.comp (measurable_const.prodMk measurable_id)).enorm
    have hρE : Measurable (fun y : Euc d => ENNReal.ofReal (ρ₀ y)) :=
      ENNReal.measurable_ofReal.comp hρm
    rw [show HRS.Whole.withDensityReal ρ₀ = volume.withDensity (fun y => ENNReal.ofReal (ρ₀ y)) from rfl,
      lintegral_withDensity_eq_lintegral_mul volume hρE hHx]
    calc ∫⁻ y, (fun y => ENNReal.ofReal (ρ₀ y)) y * ‖commutatorKernel d (criticalS d) (gradient f) x y‖ₑ
        ≤ ∫⁻ y, ENNReal.ofReal (ρ₀ y) * (ENNReal.ofReal (A * criticalS d) *
            (ENNReal.ofReal (ind (x - y)) + 2)) := by
          refine lintegral_mono fun y => ?_
          gcongr
          exact hpt x y
      _ = ENNReal.ofReal (A * criticalS d) * ∫⁻ y, ENNReal.ofReal (ρ₀ y) *
            (ENNReal.ofReal (ind (x - y)) + 2) := by
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          congr 1
          funext y
          ring
      _ ≤ ENNReal.ofReal (A * criticalS d) * (ENNReal.ofReal M * (∫⁻ z, ENNReal.ofReal (ind z)) + 2) := by
          gcongr
          exact r26t8a_o00d_dens_bound ρ₀ hρm M hρM hmass ind hindm x
  -- the real bound of `∫ hSource ∂μ`
  have hreal : ∀ x, ‖∫ y, commutatorKernel d (criticalS d) (gradient f) x y ∂(HRS.Whole.withDensityReal ρ₀)‖ ≤
      A * criticalS d * (M * Jr + 2) := by
    intro x
    have hq0 : 0 ≤ A * criticalS d * (M * Jr + 2) := by
      have : 0 ≤ M * Jr + 2 := by positivity
      exact mul_nonneg (mul_nonneg hA hs0.le) this
    have hle : ENNReal.ofReal ‖∫ y, commutatorKernel d (criticalS d) (gradient f) x y ∂(HRS.Whole.withDensityReal ρ₀)‖ ≤
        ENNReal.ofReal (A * criticalS d * (M * Jr + 2)) := by
      rw [ofReal_norm_eq_enorm]
      refine (enorm_integral_le_lintegral_enorm _).trans ((hdens x).trans (le_of_eq ?_))
      rw [ENNReal.ofReal_mul (mul_nonneg hA hs0.le), hJE]
    exact (ENNReal.ofReal_le_ofReal_iff hq0).1 hle
  have hbound : ∀ x, ‖aSource (HRS.Whole.withDensityReal ρ₀) f x‖ ≤ criticalS d * (M * Jr + 2) / 2 * A := by
    intro x
    have e : aSource (HRS.Whole.withDensityReal ρ₀) f x =
        (1 / 2) * ∫ y, commutatorKernel d (criticalS d) (gradient f) x y ∂(HRS.Whole.withDensityReal ρ₀) :=
      rfl
    rw [e, norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    exact (mul_le_mul_of_nonneg_left (hreal x) (by norm_num : (0 : ℝ) ≤ 1 / 2)).trans (le_of_eq (by ring))
  refine ⟨MemLp.of_bound hAs.aestronglyMeasurable _ (Filter.Eventually.of_forall hbound), ?_⟩
  have h := eLpNorm_le_of_ae_bound (μ := HRS.Whole.withDensityReal ρ₀) (p := 2)
    (f := aSource (HRS.Whole.withDensityReal ρ₀) f) hAs.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)
  rw [measure_univ, ENNReal.one_rpow, one_mul] at h
  exact h

end HRS.MS.R26T8A

end
