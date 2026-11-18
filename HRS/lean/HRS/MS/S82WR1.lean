import HRS.MS.S82WQ3

/-!
# S8.2 A05 (S82W), part 8: centered `L²` norms of combinations, numerical inequalities for `logN`
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.S82W
open HRS HRS.Whole HRS.MS.Phase2S82

section center
variable {α : Type*} [MeasurableSpace α] {P : Measure α} [IsProbabilityMeasure P]

lemma w_center_sqrt {G : α → ℝ} (hG : AEStronglyMeasurable G P) {V : ℝ} (hV : 0 ≤ V)
    (h : evariance G P ≤ ENNReal.ofReal V) : eLpNorm (centerUnder P G) 2 P ≤ ENNReal.ofReal (Real.sqrt V) := by
  have hc : AEStronglyMeasurable (centerUnder P G) P := hG.sub aestronglyMeasurable_const
  rw [w_eLp_two hc]
  have h1 : ∫⁻ x, ‖centerUnder P G x‖ₑ ^ (2 : ℝ) ∂P = evariance G P := by
    unfold evariance centerUnder
    simp_rw [ENNReal.rpow_two]
  rw [h1, Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg hV (by norm_num)]
  exact ENNReal.rpow_le_rpow h (by norm_num)

lemma w_center_comb {u v w : α → ℝ} (hu : MemLp u 2 P) (hv : MemLp v 2 P) (hw : MemLp w 2 P) (c : ℝ)
    {a b e : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (he0 : 0 ≤ e)
    (ha : eLpNorm (centerUnder P u) 2 P ≤ ENNReal.ofReal a)
    (hb : eLpNorm (centerUnder P v) 2 P ≤ ENNReal.ofReal b)
    (he : eLpNorm (centerUnder P w) 2 P ≤ ENNReal.ofReal e) :
    eLpNorm (centerUnder P (fun X => c * u X + v X - w X)) 2 P ≤ ENNReal.ofReal (|c| * a + b + e) := by
  have iu := hu.integrable (by norm_num)
  have iv := hv.integrable (by norm_num)
  have iw := hw.integrable (by norm_num)
  have hcen : centerUnder P (fun X => c * u X + v X - w X) =
      (c • centerUnder P u + centerUnder P v) + (-1 : ℝ) • centerUnder P w := by
    funext X
    have : ∫ Y, (c * u Y + v Y - w Y) ∂P = c * ∫ Y, u Y ∂P + ∫ Y, v Y ∂P - ∫ Y, w Y ∂P := by
      have i1 : Integrable (fun Y => c * u Y + v Y) P := (iu.const_mul c).add iv
      have e1 := integral_sub i1 iw
      have e2 := integral_add (iu.const_mul c) iv
      rw [e1, e2, integral_const_mul]
    simp only [centerUnder, Pi.add_apply, Pi.smul_apply, smul_eq_mul, this]
    ring
  rw [hcen]
  refine (eLpNorm_add_le (by norm_num)).trans ?_
  have h1 : eLpNorm (c • centerUnder P u + centerUnder P v) 2 P ≤ ENNReal.ofReal (|c| * a + b) := by
    refine (eLpNorm_add_le (by norm_num)).trans ?_
    rw [eLpNorm_const_smul, ENNReal.ofReal_add (by positivity) hb0]
    refine add_le_add ?_ hb
    rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_mul (abs_nonneg c)]
    exact mul_le_mul' le_rfl ha
  have h2 : eLpNorm ((-1 : ℝ) • centerUnder P w) 2 P ≤ ENNReal.ofReal e := by
    rw [eLpNorm_const_smul]
    simpa using he
  calc _ ≤ ENNReal.ofReal (|c| * a + b) + ENNReal.ofReal e := add_le_add h1 h2
    _ = _ := by rw [← ENNReal.ofReal_add (by positivity) he0]

end center

lemma w_logN_le (N : ℕ) (hN : 1 ≤ N) : Real.log (Real.exp 1 * N) ≤ 2 * Real.sqrt N := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hpos
  rw [Real.log_mul (Real.exp_pos 1).ne' hpos.ne', Real.log_exp]
  have h1 : Real.log (N : ℝ) = 2 * Real.log (Real.sqrt N) := by
    rw [← Real.log_rpow hs]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hpos.le]; norm_num
  have h2 := Real.log_le_sub_one_of_pos hs
  linarith

end HRS.MS.S82W
