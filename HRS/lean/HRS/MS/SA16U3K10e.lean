import HRS.MS.SA16U3K10d
import HRS.MS.CzHlsAux2

/-!
# S.A.16 K10, part (e): `L^2` bookkeeping (worker SA16U3)

Cauchy-Schwarz pairing in `eLpNorm` form, the squares of the `L^2` norms of a Schwartz function and its
gradient, the weak norm `wNormE 1 2 Z`, and `‖∂_v a‖_{C_b^1} ≤ ‖a‖_{C_b^2}`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16Cutoff
open HRS HRS.Whole HRS.Whole.AppendixA HRS.CZ.Pv HRS.CZ.ElemA HRS.CZ.Hls Phase2SA16

section K10e
variable {d : ℕ}

/-- real `L^2` norm -/
def sa16u3_N (f : Euc d → ℝ) : ℝ := (eLpNorm f 2 volume).toReal

lemma sa16u3_pair {f g : Euc d → ℝ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    |∫ x, f x * g x| ≤ sa16u3_N f * sa16u3_N g := by
  have h1 := hlsg_holder (d := d) (r := 2) (p := 2) (q := 1) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hf.aestronglyMeasurable hg.aestronglyMeasurable
  rw [ENNReal.ofReal_one, ENNReal.ofReal_ofNat] at h1
  have hm : AEStronglyMeasurable (fun x => f x * g x) volume :=
    hf.aestronglyMeasurable.mul hg.aestronglyMeasurable
  have hfin : eLpNorm f 2 volume * eLpNorm g 2 volume ≠ ⊤ :=
    ENNReal.mul_ne_top hf.eLpNorm_ne_top hg.eLpNorm_ne_top
  calc |∫ x, f x * g x| = ‖∫ x, f x * g x‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ x, ‖f x * g x‖ := norm_integral_le_integral_norm _
    _ = (∫⁻ x, ‖f x * g x‖ₑ).toReal := by rw [integral_norm_eq_lintegral_enorm hm]
    _ = (eLpNorm (fun x => f x * g x) 1 volume).toReal := by
        rw [eLpNorm_one_eq_lintegral_enorm] <;> exact hm
    _ ≤ (eLpNorm f 2 volume * eLpNorm g 2 volume).toReal := ENNReal.toReal_mono hfin h1
    _ = sa16u3_N f * sa16u3_N g := by
        unfold sa16u3_N; rw [ENNReal.toReal_mul]

lemma sa16u3_sq_eq {f : Euc d → ℝ} (hf : MemLp f 2 volume) :
    ∫ x, ‖f x‖ ^ 2 = (sa16u3_N f) ^ 2 := by
  have h := hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
  have hnn : 0 ≤ ∫ x, ‖f x‖ ^ (ENNReal.toReal 2) := integral_nonneg fun x => by positivity
  unfold sa16u3_N
  rw [h, ENNReal.toReal_ofReal (by positivity)]
  have e2 : ENNReal.toReal 2 = 2 := by norm_num
  rw [e2] at hnn ⊢
  have : (∫ x, ‖f x‖ ^ (2 : ℝ)) = ∫ x, ‖f x‖ ^ 2 := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    exact Real.rpow_two _
  rw [this] at hnn ⊢
  rw [← Real.rpow_natCast, ← Real.rpow_mul hnn]
  norm_num

lemma sa16u3_N_nonneg (f : Euc d → ℝ) : 0 ≤ sa16u3_N f := ENNReal.toReal_nonneg

lemma sa16u3_memLp_schwartz (S : SchwartzMap (Euc d) ℝ) : MemLp (⇑S) 2 volume := S.memLp 2 volume

lemma sa16u3_memLp_gradnorm (Z : SchwartzMap (Euc d) ℝ) :
    MemLp (fun x => ‖fderiv ℝ Z x‖) 2 volume := by
  have := ((SchwartzMap.fderivCLM ℝ (Euc d) ℝ Z).memLp 2 volume).norm
  exact this

lemma sa16u3_dir_le (Z : SchwartzMap (Euc d) ℝ) (v : Euc d) (hv : ‖v‖ = 1) (x : Euc d) :
    ‖fderiv ℝ Z x v‖ ≤ ‖fderiv ℝ Z x‖ := by
  calc ‖fderiv ℝ Z x v‖ ≤ ‖fderiv ℝ Z x‖ * ‖v‖ := (fderiv ℝ Z x).le_opNorm v
    _ = ‖fderiv ℝ Z x‖ := by rw [hv, mul_one]

/-- `‖∂_v Z‖_2 ≤ ‖∇Z‖_2` for a unit vector `v` -/
lemma sa16u3_N_dir_le (Z : SchwartzMap (Euc d) ℝ) (v : Euc d) (hv : ‖v‖ = 1) :
    sa16u3_N (fun x => fderiv ℝ Z x v) ≤ sa16u3_N (fun x => ‖fderiv ℝ Z x‖) := by
  unfold sa16u3_N
  refine ENNReal.toReal_mono (sa16u3_memLp_gradnorm Z).eLpNorm_ne_top ?_
  have hcont : Continuous (fun x => fderiv ℝ Z x v) :=
    (sa16u3_fderiv_cont Z).clm_apply continuous_const
  refine eLpNorm_mono_real hcont.aestronglyMeasurable fun x => ?_
  exact sa16u3_dir_le Z v hv x

end K10e
end HRS.Whole.AppendixA.Phase2SA16Cutoff
