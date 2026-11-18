import HRS.MS.R26T8AW2
import HRS.MS.R26T8AZ7c

/-!
# S8.2 T8A W3 (= P13 same-k): exact Newton nonlocal producer interface (Pro contract verbatim, every `σ < d`)
`r26t8a_newton_nonlocal_two_pole_same`: P10 (the potential identity) and P11 (the `Conormal k (b+2) (M+2) (σ - criticalS d)` bound of
`pairJ (localNewton F)`) together, with `Conormal (k+2) b M σ A F` and no `0 ≤ σ`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

theorem r26t8a_newton_nonlocal_two_pole_same (d : ℕ) (hd : 2 ≤ d) (k b : ℕ)
    (a beta M sigma : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (hM : 0 ≤ M) (hsigma : sigma < d)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ rho : Euc d → ℝ,
      IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ F : Euc d → Euc d → ℝ, ∀ A : ℝ, 0 ≤ A →
      Conormal (k + 2) b M sigma A F →
      let mu := HRS.Whole.withDensityReal rho
      let Q := localNewton mu beta⁻¹ chi F
      let C0 := critCoeff d a beta rho
      (∀ x y, x ≠ y →
        Integrable (fun z => rieszKernel d (criticalS d) (x - z) *
          (rho z * Laplacian.laplacian (fun w => Q w y) z +
            inner ℝ (gradient rho z) (pairGradX Q z y))) ∧
        oneJ C0 (fun w => Q w y) x =
          ∫ z, rieszKernel d (criticalS d) (x - z) *
            (rho z * Laplacian.laplacian (fun w => Q w y) z +
              inner ℝ (gradient rho z) (pairGradX Q z y))) ∧
      Conormal k (b + 2) (M + 2) (sigma - criticalS d) (C * A)
        (pairJ C0 mu Q) := by
  obtain ⟨C, hC0, hC⟩ := r26t8a_newton_nonlocal_bound_same d hd k b a beta M sigma ha hbeta hM hsigma chi hchi
  refine ⟨C, hC0, fun rho hrho F A hA hF => ⟨fun x y hxy => ?_, hC rho hrho F A hA hF⟩⟩
  exact r26t8a_newton_potential_ibp_same d hd k b a beta M sigma ha hbeta hM hsigma chi hchi rho hrho F A hA hF
    x y hxy

end HRS.MS.R26T8A
