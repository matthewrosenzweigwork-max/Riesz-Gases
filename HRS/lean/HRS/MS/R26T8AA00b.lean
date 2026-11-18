import HRS.MS.R26T8AA00a

/-!
# S8.2 T8A A00 (part b): derivative of the `x`-gradient of a `PairCorrector`
`pairGradX Q · y` is differentiable at `w ≠ y` with `‖D‖ ≤ ‖Rz‖ A pw (1 + r^(-s))`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_a00_grad_deriv {a beta M A : ℝ} {rho : Euc d → ℝ} {f : Euc d → ℝ} {Q : Euc d → Euc d → ℝ}
    (hQ : PairCorrector a beta rho M A f Q) {w y : Euc d} (hwy : w ≠ y) :
    DifferentiableAt ℝ (fun w' => pairGradX Q w' y) w ∧
    ‖fderiv ℝ (fun w' => pairGradX Q w' y) w‖ ≤
      ‖r26t8a_Rz d‖ * (A * HRS.MS.Phase2S82.pairWeight M w y * (1 + smallRadius w y ^ (-criticalS d))) := by
  have hQ2 : ContDiffOn ℝ 2 (Function.uncurry Q) {p : Euc d × Euc d | p.1 ≠ p.2} :=
    hQ.smooth.of_le (by norm_num)
  have hopen : IsOpen ({y}ᶜ : Set (Euc d)) := isClosed_singleton.isOpen_compl
  have hf2 : ContDiffOn ℝ 2 (fun v => Q v y) {y}ᶜ := by
    have hg : ContDiff ℝ 2 (fun v : Euc d => (v, y)) := contDiff_id.prodMk contDiff_const
    have hmaps : Set.MapsTo (fun v : Euc d => (v, y)) {y}ᶜ {p : Euc d × Euc d | p.1 ≠ p.2} :=
      fun v hv => by simpa using hv
    exact hQ2.comp hg.contDiffOn hmaps
  have hfat : ContDiffAt ℝ 2 (fun v => Q v y) w := hf2.contDiffAt (hopen.mem_nhds (by simpa using hwy))
  set g : Euc d → ℝ := fun v => Q v y with hg
  have hDD : DifferentiableAt ℝ (fderiv ℝ g) w :=
    (hfat.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have hgrad : (fun w' => pairGradX Q w' y) = gradient g := rfl
  rw [hgrad]
  refine ⟨?_, ?_⟩
  · rw [r26t8a_gradient_eq_Rz]
    exact (r26t8a_Rz d).differentiableAt.comp w hDD
  · refine (r26t8a_fderiv_gradient_le g w hDD).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg (r26t8a_Rz d))
    have e : ‖fderiv ℝ (fderiv ℝ g) w‖ = ‖iteratedFDeriv ℝ 2 g w‖ := by
      rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]
    rw [e]
    exact (r26t8a_a00_slice_hess hQ2 hwy).trans (hQ.hessian w y hwy)

end HRS.MS.R26T8A
