import HRS.MS.SA12NN2G
import HRS.Commutator.Whole.Energy

/-!
# S.A.12 N2 (SA12N), part H: Fourier calculus for compactly supported functions; the symbol `m_q`

* `sa12n_fourier_deriv`: for `u ∈ C_c`, `∂_l û(ξ) = -2πi · 𝓕(x_l u)(ξ)`.
* `sa12n_mq`: `m_q(ξ) = κ ⟨q,ξ⟩² ‖ξ‖^{-1}` is continuous, `C¹` off `0`, `|m_q| ≤ κ ‖q‖² ‖ξ‖`,
  and `|∂_l m_q| ≤ 3 κ ‖q‖²` off `0`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff ComplexConjugate FourierTransform

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.MS.UniqN1a HRS.Whole.AppendixA

variable {d : ℕ}

theorem sa12n_cc_integrable {u : Euc d → ℝ} (hu : Continuous u) (hc : HasCompactSupport u) :
    Integrable (fun x => ((u x : ℝ) : ℂ)) volume :=
  (Complex.continuous_ofReal.comp hu).integrable_of_hasCompactSupport
    (hc.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp))

theorem sa12n_xl_cc {u : Euc d → ℝ} (hu : Continuous u) (hc : HasCompactSupport u) (l : Fin d) :
    Continuous (fun x : Euc d => x l * u x) ∧ HasCompactSupport (fun x : Euc d => x l * u x) :=
  ⟨((EuclideanSpace.proj l : Euc d →L[ℝ] ℝ).continuous).mul hu, hc.mul_left⟩

/-- `∂_l û = -2πi 𝓕(x_l u)`. -/
theorem sa12n_fourier_deriv {u : Euc d → ℝ} (hu : Continuous u) (hc : HasCompactSupport u)
    (l : Fin d) (ξ : Euc d) :
    fderiv ℝ (𝓕 (fun x : Euc d => ((u x : ℝ) : ℂ))) ξ (EuclideanSpace.single l 1) =
      -(2 * Real.pi * Complex.I) * 𝓕 (fun x : Euc d => (((x l * u x : ℝ)) : ℂ)) ξ := by
  set f : Euc d → ℂ := fun x => ((u x : ℝ) : ℂ) with hf
  have hfc : Continuous f := Complex.continuous_ofReal.comp hu
  have hcf : HasCompactSupport f := hc.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
  have hf1 : Integrable f volume := hfc.integrable_of_hasCompactSupport hcf
  have hf2 : Integrable (fun x : Euc d => ‖x‖ * ‖f x‖) volume :=
    (continuous_norm.mul hfc.norm).integrable_of_hasCompactSupport hcf.norm.mul_left
  have hD := Real.hasFDerivAt_fourier hf1 hf2 ξ
  have hG : Integrable (VectorFourier.fourierSMulRight (innerSL ℝ) f) volume := by
    refine (hf2.const_mul (2 * Real.pi * ‖(innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ)‖)).mono'
      hf1.1.fourierSMulRight (Eventually.of_forall fun x => ?_)
    have := VectorFourier.norm_fourierSMulRight_le (innerSL ℝ) f x
    calc _ ≤ _ := this
      _ = _ := by ring
  rw [hD.fderiv]
  have h3 : (𝓕 (VectorFourier.fourierSMulRight (innerSL ℝ) f) ξ) (EuclideanSpace.single l 1) =
      𝓕 (fun x => VectorFourier.fourierSMulRight (innerSL ℝ) f x (EuclideanSpace.single l 1)) ξ :=
    Real.fourierIntegral_continuousLinearMap_apply' (L := innerSL ℝ) (μ := volume) hG
  rw [h3]
  rw [Real.fourier_eq', Real.fourier_eq', ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  have hin : innerSL ℝ x (EuclideanSpace.single l (1 : ℝ)) = x l := by
    rw [innerSL_apply_apply, EuclideanSpace.inner_single_right]; simp
  simp only [VectorFourier.fourierSMulRight_apply, hin, hf]
  simp only [smul_eq_mul, Complex.real_smul, conj_trivial, one_mul]
  push_cast
  ring

/-- The symbol `m_q(ξ) = κ ⟨q,ξ⟩² ‖ξ‖^{-1}`. -/
def sa12n_mq (κ : ℝ) (q : Euc d) (ξ : Euc d) : ℝ := κ * (inner ℝ q ξ ^ 2 * ‖ξ‖ ^ (-1 : ℝ))

theorem sa12n_mq_bound {κ : ℝ} (hκ : 0 ≤ κ) (q ξ : Euc d) :
    |sa12n_mq κ q ξ| ≤ κ * ‖q‖ ^ 2 * ‖ξ‖ := by
  unfold sa12n_mq
  by_cases hξ : ξ = 0
  · subst hξ; simp
  · have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
    rw [Real.rpow_neg_one, abs_mul, abs_of_nonneg hκ, abs_mul, abs_of_nonneg (inv_nonneg.2 hn.le),
      abs_pow]
    have h1 : |inner ℝ q ξ| ≤ ‖q‖ * ‖ξ‖ := abs_real_inner_le_norm q ξ
    have h2 : |inner ℝ q ξ| ^ 2 ≤ (‖q‖ * ‖ξ‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
    calc κ * (|inner ℝ q ξ| ^ 2 * ‖ξ‖⁻¹) ≤ κ * ((‖q‖ * ‖ξ‖) ^ 2 * ‖ξ‖⁻¹) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 (inv_nonneg.2 hn.le)) hκ
      _ = κ * ‖q‖ ^ 2 * ‖ξ‖ := by field_simp

theorem sa12n_mq_continuous {κ : ℝ} (hκ : 0 ≤ κ) (q : Euc d) : Continuous (sa12n_mq κ q) := by
  refine continuous_iff_continuousAt.2 fun ξ => ?_
  by_cases hξ : ξ = 0
  · subst hξ
    have h0 : sa12n_mq κ q 0 = 0 := by simp [sa12n_mq]
    rw [ContinuousAt, h0]
    refine squeeze_zero_norm (fun ξ => ?_) (a := fun ξ : Euc d => κ * ‖q‖ ^ 2 * ‖ξ‖) ?_
    · rw [Real.norm_eq_abs]; exact sa12n_mq_bound hκ q ξ
    · have : Continuous (fun ξ : Euc d => κ * ‖q‖ ^ 2 * ‖ξ‖) := continuous_const.mul continuous_norm
      simpa using this.tendsto 0
  · have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.2 hξ
    unfold sa12n_mq
    refine continuousAt_const.mul (ContinuousAt.mul ?_ ?_)
    · exact (continuous_const.inner continuous_id).pow 2 |>.continuousAt
    · exact continuous_norm.continuousAt.rpow_const (Or.inl hn)

theorem sa12n_mq_deriv {κ : ℝ} (hκ : 0 ≤ κ) (q : Euc d) {ξ : Euc d} (hξ : ξ ≠ 0) (l : Fin d) :
    DifferentiableAt ℝ (sa12n_mq κ q) ξ ∧
      |fderiv ℝ (sa12n_mq κ q) ξ (EuclideanSpace.single l 1)| ≤ 3 * κ * ‖q‖ ^ 2 := by
  have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  have h1 : HasFDerivAt (fun ξ : Euc d => inner ℝ q ξ) (innerSL ℝ q) ξ :=
    (innerSL ℝ q).hasFDerivAt
  have h2 := h1.pow 2
  have h3 := q09_norm_rpow_hasFDerivAt hξ (-1)
  have h4 := (h2.mul h3).const_mul κ
  have h5 : HasFDerivAt (sa12n_mq κ q) _ ξ := h4
  refine ⟨h5.differentiableAt, ?_⟩
  have e3 : ‖ξ‖ ^ ((-1 : ℝ) - 2) = (‖ξ‖ ^ 3)⁻¹ := by
    rw [show (-1 : ℝ) - 2 = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg hn.le, Real.rpow_natCast]
  have e1 : ‖ξ‖ ^ (-1 : ℝ) = ‖ξ‖⁻¹ := Real.rpow_neg_one _
  have hE : fderiv ℝ (sa12n_mq κ q) ξ (EuclideanSpace.single l 1) =
      κ * (inner ℝ q ξ ^ 2 * (-(‖ξ‖ ^ 3)⁻¹ * ξ l) + ‖ξ‖⁻¹ * (2 * inner ℝ q ξ * q l)) := by
    rw [h5.fderiv]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, smul_eq_mul,
      innerSL_apply_apply, EuclideanSpace.inner_single_right, e3, e1]
    simp only [conj_trivial, nsmul_eq_mul, Nat.cast_ofNat]
    norm_num
  rw [hE]
  have ha : |inner ℝ q ξ| ≤ ‖q‖ * ‖ξ‖ := abs_real_inner_le_norm q ξ
  have hxl : |ξ l| ≤ ‖ξ‖ := HRS.MS.UniqN0.n0_coord_le ξ l
  have hql : |q l| ≤ ‖q‖ := HRS.MS.UniqN0.n0_coord_le q l
  have hq0 : 0 ≤ ‖q‖ := norm_nonneg _
  have hr3 : 0 < ‖ξ‖ ^ 3 := by positivity
  have b1 : |inner ℝ q ξ ^ 2 * (-(‖ξ‖ ^ 3)⁻¹ * ξ l)| ≤ ‖q‖ ^ 2 := by
    simp only [abs_mul, abs_neg, abs_inv, abs_pow, abs_of_pos hn]
    have h2 : |inner ℝ q ξ| ^ 2 ≤ (‖q‖ * ‖ξ‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) ha 2
    calc |inner ℝ q ξ| ^ 2 * ((‖ξ‖ ^ 3)⁻¹ * |ξ l|) ≤ (‖q‖ * ‖ξ‖) ^ 2 * ((‖ξ‖ ^ 3)⁻¹ * ‖ξ‖) :=
          mul_le_mul h2 (mul_le_mul_of_nonneg_left hxl (inv_nonneg.2 hr3.le)) (by positivity)
            (by positivity)
      _ = ‖q‖ ^ 2 := by field_simp
  have b2 : |‖ξ‖⁻¹ * (2 * inner ℝ q ξ * q l)| ≤ 2 * ‖q‖ ^ 2 := by
    rw [abs_mul, abs_mul, abs_mul, abs_inv, abs_of_pos hn, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc ‖ξ‖⁻¹ * (2 * |inner ℝ q ξ| * |q l|) ≤ ‖ξ‖⁻¹ * (2 * (‖q‖ * ‖ξ‖) * ‖q‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul_of_nonneg_left ha (by norm_num)) hql
            (abs_nonneg _) (by positivity)) (inv_nonneg.2 hn.le)
      _ = 2 * ‖q‖ ^ 2 := by field_simp
  rw [abs_mul, abs_of_nonneg hκ]
  calc κ * |inner ℝ q ξ ^ 2 * (-(‖ξ‖ ^ 3)⁻¹ * ξ l) + ‖ξ‖⁻¹ * (2 * inner ℝ q ξ * q l)|
      ≤ κ * (‖q‖ ^ 2 + 2 * ‖q‖ ^ 2) :=
        mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add b1 b2)) hκ
    _ = 3 * κ * ‖q‖ ^ 2 := by ring

end HRS.MH.AdjointRd.Phase2SA12Near
