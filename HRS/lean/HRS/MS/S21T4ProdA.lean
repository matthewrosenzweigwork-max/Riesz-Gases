import HRS.MS.S21G2_S11a
import HRS.MS.S21L_G11
import HRS.MS.S21H2_S14aD1

/-! S2.1(iii): scalar Gaussian properties of the common product-Gaussian realization. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3
open HRS.MC.E213U13 HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (HRS.Euc d)} [IsProbabilityMeasure μ]

theorem s21t4_eta_memLp (I : ProductGaussian μ) (f : HRS.Euc d → ℝ) (hf : MemLp f 2 μ) :
    MemLp (I.η f) 2 I.P := by
  letI := I.mΩ
  letI := I.prob
  let ξ' : ℕ → I.Ω → ℝ := fun i => (I.standard.aemeasurable i).mk (I.ξ i)
  have hm' : ∀ i, Measurable (ξ' i) := fun i => (I.standard.aemeasurable i).measurable_mk
  have hae : ∀ i, I.ξ i =ᵐ[I.P] ξ' i := fun i => (I.standard.aemeasurable i).ae_eq_mk
  have hξ'G : HRS.IsStdGaussianSeq I.P ξ' := by
    refine ⟨(ProbabilityTheory.iIndepFun_congr hae).1 I.standard.1, fun i => ?_⟩
    have h1 : I.P.map (I.ξ i) = gaussianReal 0 1 := I.standard.2 i
    show I.P.map (ξ' i) = gaussianReal 0 1
    rw [← Measure.map_congr (hae i)]
    exact h1
  have hfirst := s21l_first_congr hae (I.first f hf)
  exact InQ1.memLp hξ'G hm' (s21l_inQ1_of_first hξ'G hm' hfirst) 2

theorem s21t4_eta_const (I : ProductGaussian μ) :
    I.η (fun _ : HRS.Euc d => (1 : ℝ)) =ᵐ[I.P] 0 := by
  let c : HRS.Euc d → ℝ := fun _ => 1
  have hc : MemLp c 2 μ := memLp_const _
  have hcov := I.covariance c c hc hc
  have hzero : ∀ x : HRS.Euc d, HRS.Whole.projMean μ c x = 0 := by
    intro x
    simp [HRS.Whole.projMean, HRS.Whole.pair, c]
  have hsq : ∫ ω, (I.η c ω) ^ 2 ∂I.P = 0 := by
    simpa only [sq, hzero, zero_mul, integral_zero] using hcov
  have hmem : Integrable (fun ω => (I.η c ω) ^ 2) I.P :=
    (s21t4_eta_memLp I c hc).integrable_sq
  have heq := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg (I.η c ω)) hmem).1 hsq
  filter_upwards [heq] with ω hω
  have hz : I.η c ω = 0 := by
    have hmul : I.η c ω * I.η c ω = 0 := by simpa only [pow_two, Pi.zero_apply] using hω
    exact (mul_self_eq_zero.mp hmul)
  exact hz

/-- The product Gaussian field has the exact centered covariance and therefore its second moment contracts L². -/
theorem s21t4_eta_contract (I : ProductGaussian μ) (f : HRS.Euc d → ℝ) (hf : MemLp f 2 μ) :
    ∫ ω, I.η f ω ^ 2 ∂I.P ≤ ∫ x, f x ^ 2 ∂μ := by
  letI := I.mΩ
  letI := I.prob
  have hcov := I.covariance f f hf hf
  have hvariance : (∫ x, HRS.Whole.projMean μ f x * HRS.Whole.projMean μ f x ∂μ) =
      variance f μ := by
    rw [variance_eq_integral hf.aemeasurable]
    simp only [HRS.Whole.projMean, HRS.Whole.pair, pow_two]
  have hv : variance f μ ≤ ∫ x, f x ^ 2 ∂μ := by
    rw [variance_eq_sub hf]
    simp only [Pi.pow_apply]
    nlinarith [sq_nonneg (∫ x, f x ∂μ)]
  calc
    (∫ ω, I.η f ω ^ 2 ∂I.P) = ∫ x, HRS.Whole.projMean μ f x * HRS.Whole.projMean μ f x ∂μ := by
      simpa only [pow_two] using hcov
    _ = variance f μ := hvariance
    _ ≤ ∫ x, f x ^ 2 ∂μ := hv

end HRS.MS.R26T3
