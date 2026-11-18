import HRS.Commutator.Whole.XNRSAux25

/-!
# Packet X-NRS, part 26: properties of the kernel profile `Φ`
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv Convolution

noncomputable section

namespace HRS.Commutator.Whole.XNRS

variable {d : ℕ}

lemma xΦ_eq_re (z : Euc d) : xΦ z = (xΦS d z).re := by rw [xΦS_apply]; simp

lemma xΦ_continuous : Continuous (xΦ : Euc d → ℝ) := by
  have : (xΦ : Euc d → ℝ) = fun z => (xΦS d z).re := funext xΦ_eq_re
  rw [this]; exact Complex.continuous_re.comp (xΦS d).continuous

lemma xΦ_integrable : Integrable (xΦ : Euc d → ℝ) := by
  have : (xΦ : Euc d → ℝ) = fun z => (xΦS d z).re := funext xΦ_eq_re
  rw [this]; exact (xΦS d).integrable.re

lemma xΦ_bdd : ∃ M : ℝ, ∀ z : Euc d, |xΦ z| ≤ M := by
  obtain ⟨M, _, hM⟩ := xhbdd (xΦS d)
  refine ⟨M, fun z => ?_⟩
  have := hM z
  rwa [xΦS_apply, Complex.norm_real, Real.norm_eq_abs] at this

lemma xΦ_mul_integrable : Integrable (fun z : Euc d => |xΦ z| * ‖z‖) := by
  have h := (xΦS d).integrable_pow_mul volume 1
  refine h.congr (Eventually.of_forall fun z => ?_)
  simp only [pow_one, xΦS_apply, Complex.norm_real, Real.norm_eq_abs]
  ring

/-- `Ψ_n(z) = n^d Φ(n z)`. -/
def xΨn (n : ℝ) (z : Euc d) : ℝ := n ^ d * xΦ (n • z)

/-- `Λ_n(z) = n^{-d} Φ(z/n)`. -/
def xΛn (n : ℝ) (z : Euc d) : ℝ := (n⁻¹) ^ d * xΦ (n⁻¹ • z)

lemma xKr_xσ' {n : ℝ} (hn : 2 ≤ n) (z : Euc d) : xKr (xσ n) z = xΨn n z - xΛn n z :=
  xKr_xσ hn z

lemma xΨn_continuous (n : ℝ) : Continuous (xΨn n : Euc d → ℝ) :=
  continuous_const.mul (xΦ_continuous.comp (continuous_const_smul _))

lemma xΛn_continuous (n : ℝ) : Continuous (xΛn n : Euc d → ℝ) :=
  continuous_const.mul (xΦ_continuous.comp (continuous_const_smul _))

lemma xΨn_integrable {n : ℝ} (hn : n ≠ 0) : Integrable (xΨn n : Euc d → ℝ) :=
  (xΦ_integrable.comp_smul hn).const_mul _

lemma xΛn_integrable {n : ℝ} (hn : n ≠ 0) : Integrable (xΛn n : Euc d → ℝ) :=
  (xΦ_integrable.comp_smul (inv_ne_zero hn)).const_mul _

lemma xΨn_bdd (n : ℝ) : ∃ M : ℝ, ∀ z : Euc d, |xΨn n z| ≤ M := by
  obtain ⟨M, hM⟩ := xΦ_bdd (d := d)
  refine ⟨|n ^ d| * M, fun z => ?_⟩
  unfold xΨn
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hM _) (abs_nonneg _)

lemma xΛn_bdd (n : ℝ) : ∃ M : ℝ, ∀ z : Euc d, |xΛn n z| ≤ M := by
  obtain ⟨M, hM⟩ := xΦ_bdd (d := d)
  refine ⟨|(n⁻¹) ^ d| * M, fun z => ?_⟩
  unfold xΛn
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hM _) (abs_nonneg _)

lemma xΨn_integral {n : ℝ} (hn : 0 < n) : ∫ z : Euc d, xΨn n z = 1 := by
  unfold xΨn
  rw [integral_const_mul]
  have h := Measure.integral_comp_smul (μ := (volume : Measure (Euc d))) (xΦ : Euc d → ℝ) n
  have hfr : Module.finrank ℝ (Euc d) = d := by simp [Euc]
  rw [hfr, abs_of_pos (by positivity), smul_eq_mul, xΦ_integral, mul_one] at h
  rw [h]
  field_simp

lemma xΛn_integral_abs {n : ℝ} (hn : 0 < n) : ∫ z : Euc d, |xΛn n z| = ∫ z : Euc d, |xΦ z| := by
  have e : ∀ z : Euc d, |xΛn n z| = (n⁻¹) ^ d * |xΦ (n⁻¹ • z)| := by
    intro z; unfold xΛn; rw [abs_mul, abs_of_pos (by positivity)]
  simp_rw [e]
  rw [integral_const_mul]
  have h := Measure.integral_comp_smul (μ := (volume : Measure (Euc d))) (fun z : Euc d => |xΦ z|) n⁻¹
  have hfr : Module.finrank ℝ (Euc d) = d := by simp [Euc]
  rw [hfr, smul_eq_mul, inv_pow, inv_inv, abs_of_pos (by positivity)] at h
  rw [h, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hn.ne', one_pow, one_mul]

lemma xΨn_mul_integral {n : ℝ} (hn : 0 < n) :
    ∫ w : Euc d, |xΨn n w| * ‖w‖ = n⁻¹ * ∫ u : Euc d, |xΦ u| * ‖u‖ := by
  have e : ∀ w : Euc d, |xΨn n w| * ‖w‖ = n ^ d * (n⁻¹ * (|xΦ (n • w)| * ‖n • w‖)) := by
    intro w
    unfold xΨn
    rw [abs_mul, abs_of_pos (by positivity), norm_smul, Real.norm_eq_abs, abs_of_pos hn]
    field_simp
  simp_rw [e]
  rw [integral_const_mul, integral_const_mul]
  have h := Measure.integral_comp_smul (μ := (volume : Measure (Euc d)))
    (fun z : Euc d => |xΦ z| * ‖z‖) n
  have hfr : Module.finrank ℝ (Euc d) = d := by simp [Euc]
  rw [hfr, abs_of_pos (by positivity), smul_eq_mul] at h
  rw [h]
  field_simp

lemma xΨn_mul_integrable {n : ℝ} (hn : 0 < n) :
    Integrable (fun w : Euc d => |xΨn n w| * ‖w‖) := by
  have e : ∀ w : Euc d, |xΨn n w| * ‖w‖ = n ^ d * (n⁻¹ * (|xΦ (n • w)| * ‖n • w‖)) := by
    intro w
    unfold xΨn
    rw [abs_mul, abs_of_pos (by positivity), norm_smul, Real.norm_eq_abs, abs_of_pos hn]
    field_simp
  simp_rw [e]
  exact ((xΦ_mul_integrable.comp_smul hn.ne').const_mul _).const_mul _

end HRS.Commutator.Whole.XNRS
