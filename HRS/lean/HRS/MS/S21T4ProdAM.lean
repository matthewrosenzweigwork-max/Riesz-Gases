import HRS.MS.S21T4ProdAL

/-! S13: half-Wick Gaussian error is bounded by eight times kernel error. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ}

theorem s21t4_round2_gaussian_half_sq_bound {s M L B C : ℝ}
    {ρ : Euc d → ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (hρ : IsRound2Density d s M L ρ)
    {h : Euc d → Euc d → ℝ} (hh : IsBoundedPairKernel s B h)
    {hj : ℕ → Euc d → Euc d → ℝ}
    (hA : IsRound2Approx s C B (HRS.Whole.withDensityReal ρ) h hj)
    (I : ProductGaussian (HRS.Whole.withDensityReal ρ))
    (a : ℕ → Euc d → ℝ)
    (ha : IsR2ZeroMeanONB (HRS.Whole.withDensityReal ρ) a)
    (Q : I.Ω → ℝ) (Qj : ℕ → I.Ω → ℝ)
    (hQ : s94WickL2 I.P (HRS.Whole.withDensityReal ρ) a
      (fun i ω => I.η (a i) ω)
      (r2CenterKernel (HRS.Whole.withDensityReal ρ) h) Q)
    (hQj : ∀ j, s94WickL2 I.P (HRS.Whole.withDensityReal ρ) a
      (fun i ω => I.η (a i) ω)
      (r2CenterKernel (HRS.Whole.withDensityReal ρ) (hj j)) (Qj j))
    (j : ℕ) :
    (∫ ω, ((1 / 2 : ℝ) * (Qj j ω - Q ω)) ^ 2 ∂I.P) ≤
      8 * ∫ z : Euc d × Euc d,
        (hj j z.1 z.2 - h z.1 z.2) ^ 2
          ∂((HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ)) := by
  letI := I.mΩ
  letI := I.prob
  have hbase := s21t4_round2_gaussian_sq_bound hd hs0 hs hρ hh hA I a ha
    Q Qj hQ hQj j
  have h1 : (∫ ω, ((1 / 2 : ℝ) * (Qj j ω - Q ω)) ^ 2 ∂I.P) =
      (1 / 4 : ℝ) * (∫ ω, (Qj j ω - Q ω) ^ 2 ∂I.P) := by
    have hp : ∀ ω, ((1 / 2 : ℝ) * (Qj j ω - Q ω)) ^ 2 =
      (1 / 4 : ℝ) * (Qj j ω - Q ω) ^ 2 := fun ω => by ring
    simp_rw [hp, integral_const_mul]
  rw [h1]
  linarith

end HRS.MS.R26T3
