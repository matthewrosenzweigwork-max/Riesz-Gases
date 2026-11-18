import HRS.MS.R26T8AZ5c
import HRS.MS.R26T8AP11f7

/-!
# S8.2 T8A Y3b0: `pdir` in pair coordinates
`r26t8a_Y3b0_pdir_eq`: `pdir u F x y = DF(x,y)(u.1 + u.2/2, u.1 - u.2/2)` for `x ≠ y`.
`r26t8a_Y3b0_dx_split`: `dx_i F = pdir (0,e_i) F + pdir (e_i/2, 0) F` off the diagonal.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_Y3b0_pdir_eq {F : Euc d → Euc d → ℝ}
    (hF : ContDiffOn ℝ 1 (Function.uncurry F) {p : Euc d × Euc d | p.1 ≠ p.2}) (u : Euc d × Euc d)
    {x y : Euc d} (hxy : x ≠ y) :
    r26t8a_pdir u F x y = fderiv ℝ (Function.uncurry F) (x, y)
      (u.1 + (1 / 2 : ℝ) • u.2, u.1 - (1 / 2 : ℝ) • u.2) := by
  have hopen : IsOpen {p : Euc d × Euc d | p.1 ≠ p.2} := isOpen_ne_fun continuous_fst continuous_snd
  have hdiff : DifferentiableAt ℝ (Function.uncurry F) (x, y) :=
    (hF.contDiffAt (hopen.mem_nhds hxy)).differentiableAt (by norm_num)
  set p : Euc d × Euc d := ((1 / 2 : ℝ) • (x + y), x - y) with hp
  have hpT : (p.1 + (1 / 2 : ℝ) • p.2, p.1 - (1 / 2 : ℝ) • p.2) = (x, y) :=
    Prod.ext (by simp only [hp]; module) (by simp only [hp]; module)
  set T0 : (Euc d × Euc d) →L[ℝ] (Euc d × Euc d) :=
    (ContinuousLinearMap.fst ℝ (Euc d) (Euc d) + (1 / 2 : ℝ) • ContinuousLinearMap.snd ℝ (Euc d) (Euc d)).prod
        (ContinuousLinearMap.fst ℝ (Euc d) (Euc d) - (1 / 2 : ℝ) • ContinuousLinearMap.snd ℝ (Euc d) (Euc d)) with hT0
  have hT : HasFDerivAt (fun Yw : Euc d × Euc d => (Yw.1 + (1 / 2 : ℝ) • Yw.2, Yw.1 - (1 / 2 : ℝ) • Yw.2)) T0 p := by
    convert T0.hasFDerivAt (x := p) using 1
    funext Yw
    simp [hT0]
  have hd' : HasFDerivAt (Function.uncurry F) (fderiv ℝ (Function.uncurry F) (x, y))
      (p.1 + (1 / 2 : ℝ) • p.2, p.1 - (1 / 2 : ℝ) • p.2) := by
    rw [hpT]; exact hdiff.hasFDerivAt
  have hc := hd'.comp p hT
  unfold r26t8a_pdir
  have e : (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2) =
      Function.uncurry F ∘ (fun Yw : Euc d × Euc d => (Yw.1 + (1 / 2 : ℝ) • Yw.2, Yw.1 - (1 / 2 : ℝ) • Yw.2)) := rfl
  rw [e, hc.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  congr 1

theorem r26t8a_Y3b0_dx_split {k : ℕ} {F : Euc d → Euc d → ℝ}
    (hF : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (Function.uncurry F) {p : Euc d × Euc d | p.1 ≠ p.2})
    (i : Fin d) {x y : Euc d} (hxy : x ≠ y) :
    r26t8a_dx i F x y = r26t8a_pdir (0, r26t8a_e d i) F x y +
      r26t8a_pdir (((1 / 2 : ℝ) • r26t8a_e d i), 0) F x y := by
  have hF1 : ContDiffOn ℝ 1 (Function.uncurry F) {p : Euc d × Euc d | p.1 ≠ p.2} :=
    hF.of_le (by exact_mod_cast (by omega : 1 ≤ k + 1))
  rw [r26t8a_Y3b0_pdir_eq hF1 _ hxy, r26t8a_Y3b0_pdir_eq hF1 _ hxy,
    r26t8a_f7_dx_eq hF i (x, y) hxy, ← map_add]
  congr 1
  refine Prod.ext ?_ ?_
  · simp only [r26t8a_e, zero_add, Prod.fst_add, zero_add, smul_zero, add_zero]
    module
  · simp only [r26t8a_e, Prod.snd_add, smul_zero, zero_add, add_zero]
    module

end HRS.MS.R26T8A
