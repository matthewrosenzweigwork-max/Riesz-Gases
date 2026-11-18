import HRS.MS.QsfAsm3

/-!
# S4.5 packet B5 (assembly), part 4: integrability of the Stein remainder
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace ContDiff

noncomputable section

namespace S45

open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

theorem s45_Rp_integrable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β C c BU Cs : ℝ}
    (hT : ThermalData d s a β C c BU) (hN : 2 ≤ N) (hS : S45Static d s a β Cs N) {χ : Euc d → ℝ}
    (hχ : ContDiff ℝ 2 χ) {B2 : ℝ} (hB2 : ∀ x, ‖fderiv ℝ (gradient χ) x‖ ≤ B2) :
    Integrable (s45_Rp (thermalMeasure d s a β) (s45_nu d s a β N) (s45_P d s a β N)
      (commutatorKernel d s (gradient χ))) (s45_P d s a β N) := by
  have hN1 : 1 ≤ N := by omega
  haveI hP : IsProbabilityMeasure (s45_P d s a β N) := hS.prob
  set P := s45_P d s a β N with hPdef
  set μ := thermalMeasure d s a β with hμdef
  set v := gradient χ with hvdef
  set h := commutatorKernel d s v with hhdef
  set ν := s45_nu d s a β N with hνdef
  haveI hνprob : IsProbabilityMeasure ν := by
    have : ν = P.map (fun X : EucConfig d N => X ⟨0, by omega⟩) := by
      rw [hνdef]; unfold s45_nu firstMarginal; rw [dif_pos (by omega)]
    rw [this]
    constructor
    rw [Measure.map_apply (measurable_pi_apply _) MeasurableSet.univ]
    simp
  haveI hμprob : IsProbabilityMeasure μ := HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  have hv1 : ContDiff ℝ 1 v := s45_contDiff_gradient hχ
  have hvd : Differentiable ℝ v := hv1.differentiable one_ne_zero
  have hB20 : 0 ≤ B2 := (norm_nonneg _).trans (hB2 0)
  set Λ : ℝ≥0 := ⟨B2, hB20⟩ with hΛdef
  have hLip : LipschitzWith Λ v := lipschitzWith_of_nnnorm_fderiv_le hvd (fun x => by
    have := hB2 x
    rw [← NNReal.coe_le_coe, coe_nnnorm]; exact this)
  have hhm : Measurable (Function.uncurry h) :=
    HRS.MS.Comm.comm_meas (s := s) v hv1.continuous.measurable
  obtain ⟨φN, hφNm, hνeq, hφNb, hφN2, hφNn⟩ := hS.marg
  obtain ⟨Bh, hBh0, hBh⟩ := s45_Hbounds hd hs0 hsd hT hLip hφNb hφNm ν hνeq
  have hHd_meas : Measurable fun x => (∫ y, h x y ∂μ) - ∫ y, h x y ∂ν :=
    ((hhm.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable).sub
      (hhm.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
  have hHd_bd : ∀ x, |(∫ y, h x y ∂μ) - ∫ y, h x y ∂ν| ≤ 2 * Bh := fun x => by
    obtain ⟨h1, h2⟩ := hBh x
    calc _ ≤ |∫ y, h x y ∂μ| + |∫ y, h x y ∂ν| := abs_sub _ _
      _ ≤ 2 * Bh := by linarith
  have hDm : Measurable fun X : EucConfig d N => centeredPairFunctional h X ν :=
    HRS.MS.Wr.wr14a_measurable_D hhm ν
  obtain ⟨-, hq⟩ := hS.comm Λ v hLip
  have hDi : Integrable (fun X : EucConfig d N => centeredPairFunctional h X ν) P := by
    have hlt : evariance (fun X : EucConfig d N => centeredPairFunctional h X ν) P < ⊤ :=
      lt_of_le_of_lt hq.2.2 ENNReal.ofReal_lt_top
    exact ((evariance_lt_top_iff_memLp hDm.aestronglyMeasurable).1 hlt).integrable one_le_two
  have hYi : Integrable (fun X : EucConfig d N => pair (empirical X) (fun x => (∫ y, h x y ∂μ) -
      ∫ y, h x y ∂ν)) P :=
    Integrable.of_bound (s45_measurable_pair_empirical hN1 hHd_meas).aestronglyMeasurable (2 * Bh)
      (Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs]; exact s45_abs_pair_empirical_le hN1 hHd_bd X)
  unfold s45_Rp
  exact (hYi.sub (integrable_const _)).sub ((hDi.sub (integrable_const _)).const_mul _)

end S45

end
