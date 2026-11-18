import HRS.MS.R26T8AP16e
import HRS.MS.R26T8AP16d

/-!
# S8.2 T8A P16f1: integrability of the local-operator row in the second variable
`r26t8a_local_row_int`: `Q` conormal `(0+2) b M (σ-2)`, `σ < d` gives `∀ x, y ↦ Lop Q(.,y)(x)` is `μ`-integrable
(`Lop Q(.,y)(x)` is conormal of order `σ`, and rows of conormal functions of order `< d` are integrable).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

theorem r26t8a_local_row_int (d : ℕ) (hd : 2 ≤ d) (b : ℕ) (a beta M sigma A : ℝ)
    (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M) (hsd : sigma < d) (hA : 0 ≤ A) {rho : Euc d → ℝ}
    (hrho : IsThermalEquilibrium d (criticalS d) a beta rho) {Q : Euc d → Euc d → ℝ}
    (hQ : Conormal (0 + 2) b M (sigma - 2) A Q) (x : Euc d) :
    Integrable (fun y => r26t8a_Lop (critCoeff d a beta rho) (fun w => Q w y) x) (HRS.Whole.withDensityReal rho) := by
  obtain ⟨chi, hchi⟩ := r26t8a_p10a_exists_cutoff d
  have hprob : HRS.Whole.IsProbDensity rho := hrho.1.1
  obtain ⟨Bα, hBα0, hBα⟩ := r26t8a_drift_coord hd a beta ha hbeta hrho 0
  obtain ⟨cK, hcK0, hKc⟩ := r26t8a_Kx_conormal hchi (critCoeff d a beta rho)
    (fun i x => -(forceMean rho x i) - a * x i) (fun i x => r26t8a_drift_coord_eq a beta rho i x) 0 b M (sigma - 2)
    Bα hBα0 (fun i => (hBα i).1) (fun i => (hBα i).2)
  have hKc0 : Conormal 0 b (M + 1) sigma (cK * A) (fun x y => r26t8a_Lop (critCoeff d a beta rho) (fun w => Q w y) x) :=
    r26t8a_conormal_mono_sA (by positivity) le_rfl (le_of_eq (by ring)) (hKc Q A hA hQ)
  obtain ⟨Kρ, hKρ0, hρ0, hKρ⟩ := r26t8a_p15_rho_weight hd 0 (M + 1) ha hbeta hrho
  exact (r26t8a_f25_wd_integrable hprob _).2
    (r26t8a_row_integrable hd 0 b (by linarith) sigma hsd Kρ hKρ0 hρ0 hKρ (by positivity) hKc0 x)

end HRS.MS.R26T8A
