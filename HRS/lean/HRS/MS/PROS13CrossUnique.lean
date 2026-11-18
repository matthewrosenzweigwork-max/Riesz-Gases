import HRS.MS.PROS13CrossStability

/-! Generic S13: approximation-independent uniqueness of the actual quadratic
Gaussian witness in L² on its original ProductGaussian probability space. -/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem pro_s13_generic_actual_quadratic_unique
    (I : ProductGaussian μ)
    (h : Euc d → Euc d → ℝ)
    (hh : MemLp (fun z : Euc d × Euc d => h z.1 z.2) 2 (μ.prod μ))
    (r s : ℕ → ℕ)
    (c : (j : ℕ) → Fin (r j) → Fin (r j) → ℝ)
    (u : (j : ℕ) → Fin (r j) → Euc d → ℝ)
    (c' : (j : ℕ) → Fin (s j) → Fin (s j) → ℝ)
    (v : (j : ℕ) → Fin (s j) → Euc d → ℝ)
    (hd : ∀ j, IsR2FiniteRankData (c j) (u j))
    (hd' : ∀ j, IsR2FiniteRankData (c' j) (v j))
    (Q Q' : I.Ω → ℝ) (hQ : MemLp Q 2 I.P) (hQ' : MemLp Q' 2 I.P)
    (hK : Tendsto (fun j => eLpNorm
      (fun z : Euc d × Euc d =>
        r2FiniteRankKernel (c j) (u j) z.1 z.2 - h z.1 z.2)
      2 (μ.prod μ)) atTop (𝓝 0))
    (hK' : Tendsto (fun j => eLpNorm
      (fun z : Euc d × Euc d =>
        r2FiniteRankKernel (c' j) (v j) z.1 z.2 - h z.1 z.2)
      2 (μ.prod μ)) atTop (𝓝 0))
    (hlim : Tendsto (fun j : ℕ => ∫ ω : I.Ω,
      (((1 / 2 : ℝ) * ∑ a : Fin (r j), ∑ b : Fin (r j), c j a b *
          (I.η (u j a) ω * I.η (u j b) ω -
            ∫ ζ, I.η (u j a) ζ * I.η (u j b) ζ ∂I.P)) -
         Q ω) ^ 2 ∂I.P) atTop (𝓝 0))
    (hlim' : Tendsto (fun j : ℕ => ∫ ω : I.Ω,
      (((1 / 2 : ℝ) * ∑ a : Fin (s j), ∑ b : Fin (s j), c' j a b *
          (I.η (v j a) ω * I.η (v j b) ω -
            ∫ ζ, I.η (v j a) ζ * I.η (v j b) ζ ∂I.P)) -
         Q' ω) ^ 2 ∂I.P) atTop (𝓝 0)) :
    Q =ᵐ[I.P] Q' := by
  letI := I.mΩ
  letI := I.prob
  have hbound := pro_s13_generic_two_actual_quadratics_L2_bound
    I h h hh hh r s c u c' v hd hd' Q Q' hQ hQ'
    hK hK' hlim hlim'
  have hle : (∫ ω : I.Ω, (Q ω - Q' ω) ^ 2 ∂I.P) ≤ 0 := by
    simpa only [sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      integral_zero, mul_zero] using hbound
  have hnonneg : 0 ≤ ∫ ω : I.Ω, (Q ω - Q' ω) ^ 2 ∂I.P :=
    integral_nonneg (fun ω => sq_nonneg (Q ω - Q' ω))
  have hzero : ∫ ω : I.Ω, (Q ω - Q' ω) ^ 2 ∂I.P = 0 :=
    le_antisymm hle hnonneg
  have hsq : (fun ω : I.Ω => (Q ω - Q' ω) ^ 2) =ᵐ[I.P] 0 :=
    (integral_eq_zero_iff_of_nonneg
      (fun ω => sq_nonneg (Q ω - Q' ω))
      ((hQ.sub hQ').integrable_sq)).mp hzero
  filter_upwards [hsq] with ω hω
  have hhq : (Q ω - Q' ω) ^ 2 = 0 := hω
  nlinarith

end HRS.MS.R26T3
