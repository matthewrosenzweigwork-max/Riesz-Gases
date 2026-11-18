import HRS.MS.Fp81S21IntervalRSBV
import Mathlib.Topology.Order.ProjIcc

/-! Continuous paths of bounded variation anchored at the left endpoint. -/
set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section
open Set
open scoped ENNReal
namespace HRS.Fp81.S21

variable {E : Type*} [NormedAddCommGroup E] {H : ℝ} (hH : 0 ≤ H)

/-- Continuous cumulative paths on `[0,H]`, anchored at zero and of bounded variation. -/
structure fp81s21_BV0 where
  path : C(Icc (0 : ℝ) H, E)
  zero_at_left : path ⟨0, ⟨le_rfl, hH⟩⟩ = 0
  bv : BoundedVariationOn (fun t : ℝ => path (projIcc 0 H hH t)) (Icc 0 H)

/-- Extend the cumulative path constantly outside the interval. -/
def fp81s21_bvExt (v : fp81s21_BV0 (E := E) hH) : ℝ → E :=
  fun t => v.path (projIcc 0 H hH t)

theorem fp81s21_bvExt_apply (v : fp81s21_BV0 (E := E) hH) (t : Icc (0 : ℝ) H) :
    fp81s21_bvExt hH v t = v.path t := by
  simp [fp81s21_bvExt, projIcc_val]

theorem fp81s21_bvExt_continuous (v : fp81s21_BV0 (E := E) hH) :
    Continuous (fp81s21_bvExt hH v) :=
  v.path.continuous.comp continuous_projIcc

theorem fp81s21_bvExt_bv (v : fp81s21_BV0 (E := E) hH) :
    BoundedVariationOn (fp81s21_bvExt hH v) (Icc 0 H) := v.bv

theorem fp81s21_bvExt_left (v : fp81s21_BV0 (E := E) hH) :
    fp81s21_bvExt hH v 0 = 0 := by
  simpa [fp81s21_bvExt] using v.zero_at_left

theorem fp81s21_bvPath_norm_le_variation (v : fp81s21_BV0 (E := E) hH)
    (t : Icc (0 : ℝ) H) :
    ‖v.path t‖ ≤ (eVariationOn (fp81s21_bvExt hH v) (Icc 0 H)).toReal := by
  have hv := (fp81s21_bvExt_bv hH v).dist_le t.property (show (0 : ℝ) ∈ Icc 0 H from ⟨le_rfl, hH⟩)
  simpa only [fp81s21_bvExt_apply, fp81s21_bvExt_left, dist_eq_norm, sub_zero] using hv

#print axioms fp81s21_bvExt_apply
#print axioms fp81s21_bvExt_continuous
#print axioms fp81s21_bvExt_bv
#print axioms fp81s21_bvExt_left
#print axioms fp81s21_bvPath_norm_le_variation
end HRS.Fp81.S21
end
