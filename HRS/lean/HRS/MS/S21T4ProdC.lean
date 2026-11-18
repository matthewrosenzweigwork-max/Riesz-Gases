import HRS.MS.S21T4ProdB

/-! Product Gaussian: L²-linearity forced by the covariance identity. -/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS.MC.E213U13 HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (HRS.Euc d)} [IsProbabilityMeasure μ]

theorem s21t4_eta_linear (I : ProductGaussian μ) (f g : HRS.Euc d → ℝ) (c : ℝ)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    I.η (f + c • g) =ᵐ[I.P] I.η f + c • I.η g := by
  letI := I.mΩ
  letI := I.prob
  let h : HRS.Euc d → ℝ := f + c • g
  have hh : MemLp h 2 μ := hf.add (hg.const_mul c)
  have hu := s21t4_eta_memLp I h hh
  have hv := s21t4_eta_memLp I f hf
  have hw := s21t4_eta_memLp I g hg
  have hp : HRS.Whole.projMean μ h = HRS.Whole.projMean μ f + c • HRS.Whole.projMean μ g :=
    s21t4_proj_linear f g hf hg c
  have hpf : MemLp (HRS.Whole.projMean μ f) 2 μ := hf.sub (memLp_const _)
  have hpg : MemLp (HRS.Whole.projMean μ g) 2 μ := hg.sub (memLp_const _)
  have hph : MemLp (HRS.Whole.projMean μ h) 2 μ := hh.sub (memLp_const _)
  have hsq : (∫ ω, (I.η h ω - I.η f ω - c * I.η g ω) ^ 2 ∂I.P) =
      (∫ x, (HRS.Whole.projMean μ h x - HRS.Whole.projMean μ f x -
        c * HRS.Whole.projMean μ g x) ^ 2 ∂μ) := by
    rw [s21t4_sq_three I.P (I.η h) (I.η f) (I.η g) hu hv hw c,
      s21t4_sq_three μ (HRS.Whole.projMean μ h) (HRS.Whole.projMean μ f)
        (HRS.Whole.projMean μ g) hph hpf hpg c]
    rw [I.covariance h h hh hh, I.covariance f f hf hf,
      I.covariance g g hg hg, I.covariance h f hh hf,
      I.covariance h g hh hg, I.covariance f g hf hg]
  have hsq0 : (∫ ω, (I.η h ω - I.η f ω - c * I.η g ω) ^ 2 ∂I.P) = 0 := by
    rw [hsq]
    have heq : (fun x : HRS.Euc d =>
      (HRS.Whole.projMean μ h x - HRS.Whole.projMean μ f x -
        c * HRS.Whole.projMean μ g x) ^ 2) = fun _ => (0 : ℝ) := by
      funext x
      have heval := congrArg (fun p : HRS.Euc d → ℝ => p x) hp
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at heval
      rw [heval]; ring
    rw [heq]
    exact integral_zero _ _
  have hmem : Integrable (fun ω => (I.η h ω - I.η f ω - c * I.η g ω) ^ 2) I.P :=
    ((hu.sub hv).sub (hw.const_mul c)).integrable_sq
  have hae := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg _) hmem).1 hsq0
  filter_upwards [hae] with ω hω
  have hz : I.η h ω - I.η f ω - c * I.η g ω = 0 := by
    have hmult : (I.η h ω - I.η f ω - c * I.η g ω) *
        (I.η h ω - I.η f ω - c * I.η g ω) = 0 := by
      simpa only [pow_two, Pi.zero_apply] using hω
    exact mul_self_eq_zero.mp hmult
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change I.η h ω = I.η f ω + c * I.η g ω
  linarith

end HRS.MS.R26T3
