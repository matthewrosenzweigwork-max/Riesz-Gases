import HRS.MS.S21T4ProdAN

/-! S13: Gaussian half-Wick error in the pair norm, with common constant 18. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ}

theorem s21t4_round2_gaussian_pair_L2_bound {s M L B C : ℝ}
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
    {n : ℕ} (j : ℕ) :
    (∫⁻ ω : I.Ω, ‖(((0 : Fin n → ℝ),
        (1 / 2 : ℝ) * (Qj j ω - Q ω)))‖ₑ ^ 2 ∂I.P) ≤
      ENNReal.ofReal (18 * ∫ z : Euc d × Euc d,
        (hj j z.1 z.2 - h z.1 z.2) ^ 2
        ∂((HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ))) := by
  letI := I.mΩ
  letI := I.prob
  have hmem : MemLp (fun ω : I.Ω => (1 / 2 : ℝ) * (Qj j ω - Q ω)) 2 I.P :=
    ((hQj j).1.sub hQ.1).const_mul (1 / 2 : ℝ)
  have h8 := s21t4_round2_gaussian_half_sq_bound hd hs0 hs hρ hh hA I a ha
    Q Qj hQ hQj j
  have hint : 0 ≤ (∫ z : Euc d × Euc d,
    (hj j z.1 z.2 - h z.1 z.2) ^ 2
      ∂((HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ))) :=
    integral_nonneg (fun z => sq_nonneg _)
  have h18 : (∫ ω, ((1 / 2 : ℝ) * (Qj j ω - Q ω)) ^ 2 ∂I.P) ≤
      18 * ∫ z : Euc d × Euc d,
        (hj j z.1 z.2 - h z.1 z.2) ^ 2
        ∂((HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ)) := by
    linarith
  rw [s21t4_pair_second_lintegral (n := n)
    (fun ω : I.Ω => (1 / 2 : ℝ) * (Qj j ω - Q ω)) hmem]
  exact ENNReal.ofReal_le_ofReal h18

end HRS.MS.R26T3
