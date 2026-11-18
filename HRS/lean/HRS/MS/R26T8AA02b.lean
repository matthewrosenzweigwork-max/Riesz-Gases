import HRS.MS.R26T8AA02a

/-!
# S8.2 T8A A02 (part b): joint continuity of `pairGradX` and `Stil` off the diagonal
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_a02_gradX_cont {Q : Euc d → Euc d → ℝ}
    (hQ : ContDiffOn ℝ 2 (Function.uncurry Q) {p : Euc d × Euc d | p.1 ≠ p.2}) :
    ContinuousOn (fun p : Euc d × Euc d => pairGradX Q p.1 p.2) {p : Euc d × Euc d | p.1 ≠ p.2} := by
  have hU : IsOpen {p : Euc d × Euc d | p.1 ≠ p.2} := isOpen_ne_fun continuous_fst continuous_snd
  have hD : ContinuousOn (fderiv ℝ (Function.uncurry Q)) {p : Euc d × Euc d | p.1 ≠ p.2} :=
    hQ.continuousOn_fderiv_of_isOpen hU (by norm_num)
  set L : Euc d →L[ℝ] Euc d × Euc d := ContinuousLinearMap.inl ℝ (Euc d) (Euc d) with hL
  have hprec : Continuous (fun T : (Euc d × Euc d) →L[ℝ] ℝ => T.comp L) :=
    ((ContinuousLinearMap.compL ℝ (Euc d) (Euc d × Euc d) ℝ).flip L).continuous
  have h2 : ContinuousOn (fun p : Euc d × Euc d => (fderiv ℝ (Function.uncurry Q) p).comp L)
      {p : Euc d × Euc d | p.1 ≠ p.2} := hprec.comp_continuousOn hD
  have e : ∀ p ∈ {p : Euc d × Euc d | p.1 ≠ p.2},
      pairGradX Q p.1 p.2 = r26t8a_Rz d ((fderiv ℝ (Function.uncurry Q) p).comp L) := by
    intro p hp
    have hdiff : DifferentiableAt ℝ (Function.uncurry Q) p :=
      ((hQ.contDiffAt (hU.mem_nhds hp)).differentiableAt (by norm_num))
    have hι : HasFDerivAt (fun v : Euc d => (v, p.2)) L p.1 := by
      have : HasFDerivAt (fun v : Euc d => (v, p.2)) (ContinuousLinearMap.inl ℝ (Euc d) (Euc d)) p.1 :=
        (hasFDerivAt_id p.1).prodMk (hasFDerivAt_const p.2 p.1)
      exact this
    have hcomp := (show DifferentiableAt ℝ (Function.uncurry Q) (p.1, p.2) from hdiff).hasFDerivAt.comp p.1 hι
    have : fderiv ℝ (fun x' => Q x' p.2) p.1 = (fderiv ℝ (Function.uncurry Q) p).comp L := hcomp.fderiv
    unfold pairGradX
    rw [r26t8a_gradient_eq_Rz]
    show r26t8a_Rz d (fderiv ℝ (fun x' => Q x' p.2) p.1) = _
    rw [this]
  exact ((r26t8a_Rz d).continuous.comp_continuousOn h2).congr e

end HRS.MS.R26T8A
