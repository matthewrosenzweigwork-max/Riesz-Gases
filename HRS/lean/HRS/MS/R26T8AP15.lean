import HRS.MS.R26T8AP15u

/-!
# S8.2 T8A packet P15 (Pro contract): `r26t8a_local_defect_bound_nonneg`
The Pro contract verbatim plus `0 ≤ sigma`; `r26t8a_local_defect_bound_full` (P15u) is the version for every `sigma < d` with the corrected
regularity hypothesis (`Conormal (rawGainReg (k+2) sigma) 0 M sigma A F`; for `sigma < 0` the same-`k` contract is not provable by the route of P07/P09).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

theorem r26t8a_local_defect_bound_nonneg (d : ℕ) (hd : 2 ≤ d) (k : ℕ)
    (a beta M sigma : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M) (hσ : 0 ≤ sigma)
    (hsd : sigma < d) (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ rho : Euc d → ℝ,
      IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ F : Euc d → Euc d → ℝ, ∀ A : ℝ, 0 ≤ A →
      CanonicalPair (HRS.Whole.withDensityReal rho) F → Conormal (k + 2) 0 M sigma A F →
      Conormal k 1 (M + 2) (sigma - 2) (C * A)
        (fun x y => newtonDefect (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi F x y -
          pairJ (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho)
            (localNewton (HRS.Whole.withDensityReal rho) beta⁻¹ chi F) x y) := by
  obtain ⟨C, hC0, hC⟩ := r26t8a_local_defect_bound_full d hd k a beta M sigma ha hbeta hM hsd chi hchi
  refine ⟨C, hC0, fun rho hrho F A hA _ hF => hC rho hrho F A hA ?_⟩
  simpa only [r26t8a_rawGainReg, if_pos hσ] using hF

end HRS.MS.R26T8A
