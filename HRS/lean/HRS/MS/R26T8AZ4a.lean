import HRS.MS.R26T8AZ3m
import HRS.MS.R26T8AP15c

/-!
# S8.2 T8A Z4a: `midPair (pdir (0,e) F)` is the `e`-derivative of the slice `w ↦ midPair F X w`
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_Z4a_slice {F : Euc d → Euc d → ℝ}
    (hF : ContDiffOn ℝ 1 (Function.uncurry F) {p : Euc d × Euc d | p.1 ≠ p.2}) (X v : Euc d) (hv : v ≠ 0)
    (e : Euc d) :
    midPair (r26t8a_pdir (0, e) F) X v = fderiv ℝ (fun w => midPair F X w) v e := by
  have hopen : IsOpen {Yw : Euc d × Euc d | Yw.2 ≠ 0} := isOpen_ne.preimage continuous_snd
  have hΦ : ContDiffOn ℝ 1 (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2) {Yw | Yw.2 ≠ 0} :=
    r26t8a_midPair_contDiffOn hF
  have hd : DifferentiableAt ℝ (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2) (X, v) :=
    (hΦ.contDiffAt (hopen.mem_nhds hv)).differentiableAt (by norm_num)
  rw [r26t8a_midPair_pdir]
  have h2 := hd.hasFDerivAt.comp v ((hasFDerivAt_const X v).prodMk (hasFDerivAt_id v))
  have e1 : (fun w : Euc d => midPair F X w) =
      (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2) ∘ (fun w => (X, w)) := rfl
  rw [e1, h2.fderiv]
  simp

end HRS.MS.R26T8A
