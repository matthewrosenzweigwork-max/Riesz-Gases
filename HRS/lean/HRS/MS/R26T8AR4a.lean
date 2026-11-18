import HRS.MS.R26T8AR2
import HRS.MS.R26T8AP11eP

/-!
# S8.2 T8A R4a: uniform (in the thermal density) version of the smooth centring correction
`r26t8a_R4_center_smooth`: `∃ C, ∀ ρ thermal, Conormal k b M σ A R → Conormal k b' M σ' (C A) (r2CenterKernel μ_ρ R - R)` for all `b', σ'`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_R4_center_smooth {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (hd : 2 ≤ d) (a beta : ℝ)
    (ha : 0 < a) (hbeta : 0 < beta) (k b : ℕ) {σ M : ℝ} (hM : 0 ≤ M) (hσd : σ < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ rho : Euc d → ℝ, IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ {A : ℝ}, 0 ≤ A → ∀ {R : Euc d → Euc d → ℝ}, Conormal k b M σ A R → ∀ (b' : ℕ) (σ' : ℝ),
      Conormal k b' M σ' (C * A) (fun x y => r2CenterKernel (HRS.Whole.withDensityReal rho) R x y - R x y) := by
  classical
  by_cases hex : ∃ ρ0 : Euc d → ℝ, IsThermalEquilibrium d (criticalS d) a beta ρ0
  swap
  · exact ⟨0, le_rfl, fun rho hrho => absurd ⟨rho, hrho⟩ hex⟩
  obtain ⟨ρ0, h0⟩ := hex
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨hρs, hg⟩ := HRS.MS.Mov0.mv0_hgauss hd (by unfold criticalS; linarith) (by unfold criticalS; linarith)
    ha hbeta h0
  obtain ⟨Cρ, cρ, hCρ, hcρ, hρb⟩ := r26t8a_f23_rho_unif hg k
  obtain ⟨Kp, hKp0, hKp⟩ := r26t8a_f25_rho_poly hCρ hcρ hρb (M + (d : ℝ) + 1)
  have hρk : ContDiff ℝ (k : WithTop ℕ∞) ρ0 := hρs.of_le (by exact_mod_cast le_top)
  obtain ⟨C, hC0, hC⟩ := r26t8a_R2_center_smooth hchi hd k b hM hσd h0.1.1 hρk hρs.continuous hKp0 hKp
  refine ⟨C, hC0, fun rho hrho A hA R hR b' σ' => ?_⟩
  have hρeq : rho = ρ0 :=
    (critical_thermal_eq d hd a beta ha hbeta hrho).trans (critical_thermal_eq d hd a beta ha hbeta h0).symm
  subst hρeq
  exact hC hA hR b' σ'

end HRS.MS.R26T8A
