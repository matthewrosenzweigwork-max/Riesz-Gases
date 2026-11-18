import HRS.MC.S7S7dAux13

/-!
# Packet `s7_S7d_uniform_limits`, helper 14: Lipschitz estimates for the Stein class and an AM-GM integral bound
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7d

open HRS HRS.Sec7 HRS.MC.SEdge

section Lip

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem s7d_iter_lip {f : E → ℝ} (hf : s7d_Cl f) {n : ℕ} (hn : n ≤ 3) :
    LipschitzWith 1 (iteratedFDeriv ℝ n f) := by
  refine lipschitzWith_of_nnnorm_fderiv_le (𝕜 := ℝ) (fun x => ?_) (fun x => ?_)
  · exact (hf.1.differentiable_iteratedFDeriv (by exact_mod_cast (by omega : n < 4))) x
  · have h := hf.2 (n + 1) (by omega) (by omega) x
    rw [← norm_fderiv_iteratedFDeriv] at h
    rw [← NNReal.coe_le_coe]
    simpa using h

theorem s7d_D2_diff {f : E → ℝ} (hf : s7d_Cl f) (x y u u' : E) :
    |iteratedFDeriv ℝ 2 f x ![u, u'] - iteratedFDeriv ℝ 2 f y ![u, u']| ≤ ‖x - y‖ * (‖u‖ * ‖u'‖) := by
  have h1 := (s7d_iter_lip hf (n := 2) (by norm_num)).dist_le_mul x y
  rw [dist_eq_norm, dist_eq_norm] at h1
  have h2 := (iteratedFDeriv ℝ 2 f x - iteratedFDeriv ℝ 2 f y).le_opNorm ![u, u']
  rw [ContinuousMultilinearMap.sub_apply, Real.norm_eq_abs] at h2
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h2
  calc _ ≤ _ := h2
    _ ≤ (‖x - y‖) * (‖u‖ * ‖u'‖) := by
        refine mul_le_mul (by simpa using h1) le_rfl (by positivity) (norm_nonneg _)

theorem s7d_D3_diff {f : E → ℝ} (hf : s7d_Cl f) (x y u u' e : E) :
    |iteratedFDeriv ℝ 3 f x ![u, u', e] - iteratedFDeriv ℝ 3 f y ![u, u', e]| ≤
      ‖x - y‖ * (‖u‖ * ‖u'‖ * ‖e‖) := by
  have h1 := (s7d_iter_lip hf (n := 3) (by norm_num)).dist_le_mul x y
  rw [dist_eq_norm, dist_eq_norm] at h1
  have h2 := (iteratedFDeriv ℝ 3 f x - iteratedFDeriv ℝ 3 f y).le_opNorm ![u, u', e]
  rw [ContinuousMultilinearMap.sub_apply, Real.norm_eq_abs] at h2
  simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons] at h2
  calc _ ≤ _ := h2
    _ ≤ (‖x - y‖) * (‖u‖ * ‖u'‖ * ‖e‖) := by
        refine mul_le_mul (by simpa using h1) le_rfl (by positivity) (norm_nonneg _)

theorem s7d_D2_abs {f : E → ℝ} (hf : s7d_Cl f) (x u u' : E) :
    |iteratedFDeriv ℝ 2 f x ![u, u']| ≤ ‖u‖ * ‖u'‖ :=
  s7d_D2_bound (hf.2 2 (by norm_num) (by norm_num) x) u u'

theorem s7d_D3_abs {f : E → ℝ} (hf : s7d_Cl f) (x u u' e : E) :
    |iteratedFDeriv ℝ 3 f x ![u, u', e]| ≤ ‖u‖ * ‖u'‖ * ‖e‖ :=
  s7d_D3_bound (hf.2 3 (by norm_num) (by norm_num) x) u u' e

/-- `|D²f(x)[u,u'] - D²f(y)[u,u']| ≤ min(2, ‖x-y‖)` for unit-ball `u, u'`. -/
theorem s7d_D2_min {f : E → ℝ} (hf : s7d_Cl f) (x y u u' : E) (hu : ‖u‖ ≤ 1) (hu' : ‖u'‖ ≤ 1) :
    |iteratedFDeriv ℝ 2 f x ![u, u'] - iteratedFDeriv ℝ 2 f y ![u, u']| ≤ min 2 ‖x - y‖ := by
  have hp : ‖u‖ * ‖u'‖ ≤ 1 := by
    calc ‖u‖ * ‖u'‖ ≤ 1 * 1 := mul_le_mul hu hu' (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  refine le_min ?_ ?_
  · calc _ ≤ |iteratedFDeriv ℝ 2 f x ![u, u']| + |iteratedFDeriv ℝ 2 f y ![u, u']| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add ((s7d_D2_abs hf x u u').trans hp) ((s7d_D2_abs hf y u u').trans hp)
      _ = 2 := by norm_num
  · refine (s7d_D2_diff hf x y u u').trans ?_
    calc ‖x - y‖ * (‖u‖ * ‖u'‖) ≤ ‖x - y‖ * 1 := mul_le_mul_of_nonneg_left hp (norm_nonneg _)
      _ = ‖x - y‖ := mul_one _

theorem s7d_D3_min {f : E → ℝ} (hf : s7d_Cl f) (x y u u' e : E) (hu : ‖u‖ ≤ 1) (hu' : ‖u'‖ ≤ 1)
    (he : ‖e‖ ≤ 1) :
    |iteratedFDeriv ℝ 3 f x ![u, u', e] - iteratedFDeriv ℝ 3 f y ![u, u', e]| ≤ min 2 ‖x - y‖ := by
  have hp : ‖u‖ * ‖u'‖ * ‖e‖ ≤ 1 := by
    calc ‖u‖ * ‖u'‖ * ‖e‖ ≤ 1 * 1 * 1 :=
          mul_le_mul (mul_le_mul hu hu' (norm_nonneg _) zero_le_one) he (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  refine le_min ?_ ?_
  · calc _ ≤ |iteratedFDeriv ℝ 3 f x ![u, u', e]| + |iteratedFDeriv ℝ 3 f y ![u, u', e]| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add ((s7d_D3_abs hf x u u' e).trans hp) ((s7d_D3_abs hf y u u' e).trans hp)
      _ = 2 := by norm_num
  · refine (s7d_D3_diff hf x y u u' e).trans ?_
    calc ‖x - y‖ * (‖u‖ * ‖u'‖ * ‖e‖) ≤ ‖x - y‖ * 1 := mul_le_mul_of_nonneg_left hp (norm_nonneg _)
      _ = ‖x - y‖ := mul_one _

end Lip

section AMGM

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `∫ |Y| m ≤ (λ C₂ + 2 T / λ) / 2` when `0 ≤ m ≤ 2`, `∫ Y² ≤ C₂`, `∫ m ≤ T`. -/
theorem s7d_amgm_int (P : Measure Ω) [IsProbabilityMeasure P] {Y m : Ω → ℝ} (hY : Measurable Y)
    (hm : Measurable m) (hm0 : ∀ ω, 0 ≤ m ω) (hm2 : ∀ ω, m ω ≤ 2)
    (hY2 : Integrable (fun ω => Y ω ^ 2) P) {C2 T lam : ℝ} (hC : ∫ ω, Y ω ^ 2 ∂P ≤ C2)
    (hT : ∫ ω, m ω ∂P ≤ T) (hlam : 0 < lam) :
    Integrable (fun ω => |Y ω| * m ω) P ∧
      ∫ ω, |Y ω| * m ω ∂P ≤ (lam * C2 + 2 * T / lam) / 2 := by
  have hmi : Integrable m P :=
    Integrable.of_bound hm.aestronglyMeasurable 2 (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hm0 ω)]; exact hm2 ω)
  have hpt : ∀ ω, |Y ω| * m ω ≤ (lam * Y ω ^ 2 + 2 * m ω / lam) / 2 := by
    intro ω
    have h1 : m ω ^ 2 ≤ 2 * m ω := by nlinarith [hm0 ω, hm2 ω]
    have hy2 : Y ω ^ 2 = |Y ω| ^ 2 := (sq_abs _).symm
    have h4 : lam * Y ω ^ 2 + m ω ^ 2 / lam - 2 * (|Y ω| * m ω) = (lam * |Y ω| - m ω) ^ 2 / lam := by
      rw [hy2]; field_simp; ring
    have h6 : 0 ≤ lam * Y ω ^ 2 + m ω ^ 2 / lam - 2 * (|Y ω| * m ω) := by
      rw [h4]; positivity
    have h5 : m ω ^ 2 / lam ≤ 2 * m ω / lam := div_le_div_of_nonneg_right h1 hlam.le
    linarith
  have hbd : Integrable (fun ω => (lam * Y ω ^ 2 + 2 * m ω / lam) / 2) P :=
    ((hY2.const_mul lam).add ((hmi.const_mul 2).div_const lam)).div_const 2
  have hI : Integrable (fun ω => |Y ω| * m ω) P :=
    hbd.mono' (hY.abs.mul hm).aestronglyMeasurable (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (hm0 ω))]; exact hpt ω)
  refine ⟨hI, ?_⟩
  calc ∫ ω, |Y ω| * m ω ∂P ≤ ∫ ω, (lam * Y ω ^ 2 + 2 * m ω / lam) / 2 ∂P :=
        integral_mono hI hbd hpt
    _ = (lam * ∫ ω, Y ω ^ 2 ∂P + 2 * (∫ ω, m ω ∂P) / lam) / 2 := by
        rw [integral_div, integral_add (hY2.const_mul lam) ((hmi.const_mul 2).div_const lam),
          integral_const_mul, integral_div, integral_const_mul]
    _ ≤ (lam * C2 + 2 * T / lam) / 2 := by
        have : 2 * (∫ ω, m ω ∂P) / lam ≤ 2 * T / lam :=
          div_le_div_of_nonneg_right (by linarith) hlam.le
        have : lam * ∫ ω, Y ω ^ 2 ∂P ≤ lam * C2 := mul_le_mul_of_nonneg_left hC hlam.le
        linarith

end AMGM

end HRS.MC.Sec7.S7d

end
