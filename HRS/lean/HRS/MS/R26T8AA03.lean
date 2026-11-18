import HRS.MS.S82VS5

/-!
# S8.2 observed-time layer, packet T8A.A03: the native stationary singular section removes the local projection

Packet statement `r26t8a_local_generator_rows`: for every row `y`, the thermal-density integral of
`β⁻¹ Δ_x Q(·,y) + ⟪b₀, ∇_x Q(·,y)⟫` vanishes (and the integrand is integrable).  This is the merged
`s82v_row_stat` with `ν = β⁻¹` and `pairGradX Q x y = ∇ (Q · y) x`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_local_generator_rows (d : ℕ) (hd : 2 ≤ d) (a beta M A : ℝ)
    (ha : 0 < a) (hbeta : 0 < beta) (rho : Euc d → ℝ)
    (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (f : Euc d → ℝ) (Q : Euc d → Euc d → ℝ) (hQ : PairCorrector a beta rho M A f Q) :
    ∀ y, Integrable (fun x => beta⁻¹*Laplacian.laplacian (fun z => Q z y) x +
      inner ℝ ((critCoeff d a beta rho).drift 0 x) (HRS.MS.Phase2S82.pairGradX Q x y))
        (HRS.Whole.withDensityReal rho) ∧
      ∫ x, beta⁻¹*Laplacian.laplacian (fun z => Q z y) x +
        inner ℝ ((critCoeff d a beta rho).drift 0 x) (HRS.MS.Phase2S82.pairGradX Q x y)
          ∂HRS.Whole.withDensityReal rho = 0 := by
  intro y
  exact HRS.MS.S82V.s82v_row_stat hd ha hbeta hrho hQ y

end HRS.MS.R26T8A

end
