import HRS.MS.Fp81S21InitialStein
import HRS.MS.R2SeAux4

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open S45
open HRS.Whole
open HRS (Euc)

/-- The generic S4.7 Stein remainder is the centered pair energy at its own reference law. -/
theorem fp81s21_s47_Rp_eq
    {d N : ℕ} (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    {ρ : Euc d → ℝ} {q γ C c BU BB Cs : ℝ} {Bd : Euc d → Euc d}
    (hT : S47.TRef d s ρ q C c BU BB Bd) (hN : 2 ≤ N)
    (hS : S47.S47Static d s ρ γ Cs N)
    {χ : Euc d → ℝ} (hχ : ContDiff ℝ 2 χ) {B2 : ℝ}
    (hB2 : ∀ x, ‖fderiv ℝ (gradient χ) x‖ ≤ B2) (X : EucConfig d N) :
    s45_Rp (HRS.Whole.withDensityReal ρ) (S47.s47_nu d s ρ γ N) (S47.s47_P d s ρ γ N)
        (commutatorKernel d s (gradient χ)) X =
      -(HRS.Whole.pairEnergy (commutatorKernel d s (gradient χ)) X (HRS.Whole.withDensityReal ρ) -
        ∫ Y, HRS.Whole.pairEnergy (commutatorKernel d s (gradient χ)) Y (HRS.Whole.withDensityReal ρ)
          ∂(S47.s47_P d s ρ γ N)) := by
  have hN1 : 1 ≤ N := by omega
  haveI hP : IsProbabilityMeasure (S47.s47_P d s ρ γ N) := hS.prob
  set P := S47.s47_P d s ρ γ N with hPdef
  set μ := HRS.Whole.withDensityReal ρ with hμdef
  set v := gradient χ with hvdef
  set h := commutatorKernel d s v with hhdef
  set ν := S47.s47_nu d s ρ γ N with hνdef
  haveI hνprob : IsProbabilityMeasure ν := S47.s47_nu_prob hN hP
  haveI hμprob : IsProbabilityMeasure μ := HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  have hv1 : ContDiff ℝ 1 v := s45_contDiff_gradient hχ
  have hvd : Differentiable ℝ v := hv1.differentiable one_ne_zero
  have hB20 : 0 ≤ B2 := (norm_nonneg _).trans (hB2 0)
  set Λ : ℝ≥0 := ⟨B2, hB20⟩ with hΛdef
  have hLip : LipschitzWith Λ v := lipschitzWith_of_nnnorm_fderiv_le hvd (fun x => by
    have := hB2 x
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    exact this)
  have hhm : Measurable (Function.uncurry h) :=
    HRS.MS.Comm.comm_meas (s := s) v hv1.continuous.measurable
  obtain ⟨φN, hφNm, hνeq, hφNb, hφN2, hφNn⟩ := hS.marg
  obtain ⟨Bh, hBh0, hBh⟩ :=
    S47.s47_Hbounds hd hs0 hsd hT hLip hφNb hφNm ν hνeq
  set Hd : Euc d → ℝ := fun x => (∫ y, h x y ∂μ) - ∫ y, h x y ∂ν with hHd
  have hHd_meas : Measurable Hd :=
    ((hhm.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable).sub
      (hhm.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
  have hHd_bd : ∀ x, |Hd x| ≤ 2 * Bh := fun x => by
    obtain ⟨h1, h2⟩ := hBh x
    calc |Hd x| ≤ |∫ y, h x y ∂μ| + |∫ y, h x y ∂ν| := abs_sub _ _
      _ ≤ 2 * Bh := by linarith
  have hDm : Measurable fun X : EucConfig d N => HRS.Whole.centeredPairFunctional h X ν :=
    HRS.MS.Wr.wr14a_measurable_D hhm ν
  obtain ⟨-, hq⟩ := hS.comm Λ v hLip
  have hDi : Integrable (fun X : EucConfig d N => HRS.Whole.centeredPairFunctional h X ν) P := by
    have hlt : evariance (fun X : EucConfig d N => HRS.Whole.centeredPairFunctional h X ν) P < ⊤ :=
      lt_of_le_of_lt hq.2.2 ENNReal.ofReal_lt_top
    exact ((evariance_lt_top_iff_memLp hDm.aestronglyMeasurable).1 hlt).integrable one_le_two
  have hYi : Integrable (fun X : EucConfig d N => HRS.Whole.pair (HRS.Whole.empirical X) Hd) P :=
    Integrable.of_bound (s45_measurable_pair_empirical hN1 hHd_meas).aestronglyMeasurable (2 * Bh)
      (Filter.Eventually.of_forall fun X => by
        rw [Real.norm_eq_abs]
        exact s45_abs_pair_empirical_le hN1 hHd_bd X)
  have hEY : ∫ X, HRS.Whole.pair (HRS.Whole.empirical X) Hd ∂P = HRS.Whole.pair ν Hd :=
    s45_E_pair_empirical hN1 hS.exch hHd_meas hHd_bd
  set K0 : ℝ := (1 / 2) * ((∫ x, ∫ y, h x y ∂μ ∂μ) - ∫ x, ∫ y, h x y ∂ν ∂ν) with hK0
  have hpe : ∀ X : EucConfig d N, HRS.Whole.pairEnergy h X μ =
      (1 / 2) * HRS.Whole.centeredPairFunctional h X ν -
        HRS.Whole.pair (HRS.Whole.empirical X) Hd + K0 :=
    fun X => S99.s99_pairE_decomp hN1 h X μ ν
  have h1 : Integrable (fun Y : EucConfig d N =>
      (1 / 2) * HRS.Whole.centeredPairFunctional h Y ν) P :=
    hDi.const_mul _
  have e1 : ∫ Y : EucConfig d N,
      ((1 / 2) * HRS.Whole.centeredPairFunctional h Y ν -
        HRS.Whole.pair (HRS.Whole.empirical Y) Hd + K0) ∂P =
      (∫ Y : EucConfig d N, (1 / 2) * HRS.Whole.centeredPairFunctional h Y ν ∂P) -
        ∫ Y : EucConfig d N, HRS.Whole.pair (HRS.Whole.empirical Y) Hd ∂P + K0 := by
    have h2 : Integrable (fun Y : EucConfig d N =>
        (1 / 2) * HRS.Whole.centeredPairFunctional h Y ν -
          HRS.Whole.pair (HRS.Whole.empirical Y) Hd) P := h1.sub hYi
    rw [integral_add h2 (integrable_const _), integral_sub h1 hYi]
    simp
  have hint : ∫ Y, HRS.Whole.pairEnergy h Y μ ∂P =
      (1 / 2) * ∫ Y, HRS.Whole.centeredPairFunctional h Y ν ∂P -
        HRS.Whole.pair ν Hd + K0 := by
    simp_rw [hpe]
    rw [e1, integral_const_mul, hEY]
  rw [hint, hpe X]
  unfold s45_Rp
  ring

#print axioms fp81s21_s47_Rp_eq

end HRS.Fp81.S21

end
