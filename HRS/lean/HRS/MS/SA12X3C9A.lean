import HRS.MS.SA12X3C7D3
import HRS.MS.SA12CellC8

/-!
# S.A.12 C9 (SA12X3), part A: the two integration by parts identities of the local energy rate

For `w ∈ C¹_c`, `W ∈ C¹`, `b ∈ C¹`:
* transport: `∫ 2w²W ∂_bW + 2w ∂_bw W² = -∫ (div b) w²W²`;
* diffusion: `∫ 2w²W ∂_i∂_iW = -2∫ w²(∂_iW)² - 4∫ w ∂_iw W ∂_iW`.
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12 HRS.MH.AdjointRdP

variable {d : ℕ}

theorem sa12x3_ibp_transport {w W : Euc d → ℝ} {b : Euc d → Euc d} (hw : ContDiff ℝ 1 w)
    (hwc : HasCompactSupport w) (hW : ContDiff ℝ 1 W) (hb : ContDiff ℝ 1 b) :
    ∫ x, (2 * w x ^ 2 * (W x * fderiv ℝ W x (b x)) + 2 * w x * fderiv ℝ w x (b x) * W x ^ 2) =
      -∫ x, (∑ i : Fin d, fderiv ℝ (fun y => b y i) x (EuclideanSpace.single i (1 : ℝ))) * (w x ^ 2 * W x ^ 2) := by
  set φ : Euc d → ℝ := fun x => w x ^ 2 * W x ^ 2 with hφ
  have hφ1 : ContDiff ℝ 1 φ := (hw.pow 2).mul (hW.pow 2)
  have hφc : HasCompactSupport φ := (hwc.comp_left (g := fun t : ℝ => t ^ 2) (by simp)).mul_right
  have hbi : ∀ i : Fin d, ContDiff ℝ 1 (fun y => b y i) := fun i =>
    (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).contDiff.comp hb
  have hderφ : ∀ x, fderiv ℝ φ x (b x) =
      2 * w x ^ 2 * (W x * fderiv ℝ W x (b x)) + 2 * w x * fderiv ℝ w x (b x) * W x ^ 2 := by
    intro x
    have hwd : DifferentiableAt ℝ w x := (hw.differentiable one_ne_zero) x
    have hWd : DifferentiableAt ℝ W x := (hW.differentiable one_ne_zero) x
    have h1 := (hwd.hasFDerivAt.pow 2).mul (hWd.hasFDerivAt.pow 2)
    have h2 : fderiv ℝ φ x = _ := h1.fderiv
    rw [h2]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  -- `fderiv φ x (b x) = ∑ i, b_i ∂_i φ`
  have hsum : ∀ x, fderiv ℝ φ x (b x) = ∑ i : Fin d, b x i * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)) := by
    intro x
    have : b x = ∑ i : Fin d, b x i • (EuclideanSpace.single i (1 : ℝ) : Euc d) := by
      ext k; simp [Finset.sum_apply, EuclideanSpace.single_apply, Pi.single_apply]
    conv_lhs => rw [this]
    simp [map_sum, mul_comm]
  have hcont : ∀ i : Fin d, Continuous (fun x => b x i * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) := fun i =>
    (hbi i).continuous.mul ((hφ1.continuous_fderiv one_ne_zero).clm_apply continuous_const)
  have h1 : (fun x => 2 * w x ^ 2 * (W x * fderiv ℝ W x (b x)) + 2 * w x * fderiv ℝ w x (b x) * W x ^ 2) =
      fun x => ∑ i : Fin d, b x i * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)) :=
    funext fun x => by rw [← hderφ, hsum]
  rw [h1]
  have hint1 : ∀ i : Fin d, Integrable (fun x => b x i * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))) := fun i =>
    (hcont i).integrable_of_hasCompactSupport ((hφc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i (1 : ℝ))).mul_left)
  rw [integral_finsetSum _ fun i _ => hint1 i]
  have hib : ∀ i : Fin d, ∫ x, b x i * fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ)) =
      -∫ x, fderiv ℝ (fun y => b y i) x (EuclideanSpace.single i (1 : ℝ)) * φ x := fun i =>
    r3_ibp_cs' _ (hbi i) hφ1 hφc
  simp_rw [hib]
  rw [Finset.sum_neg_distrib]
  congr 1
  have hint2 : ∀ i : Fin d, Integrable (fun x => fderiv ℝ (fun y => b y i) x (EuclideanSpace.single i (1 : ℝ)) * φ x) :=
    fun i => (((hbi i).continuous_fderiv one_ne_zero).clm_apply continuous_const |>.mul hφ1.continuous).integrable_of_hasCompactSupport
      hφc.mul_left
  rw [← integral_finsetSum _ fun i _ => hint2 i]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [Finset.sum_mul]
  rfl

theorem sa12x3_ibp_diffusion {w W : Euc d → ℝ} (hw : ContDiff ℝ 1 w) (hwc : HasCompactSupport w)
    (hW : ContDiff ℝ 2 W) (i : Fin d) :
    ∫ x, 2 * w x ^ 2 * W x * fderiv ℝ (fun y => fderiv ℝ W y (EuclideanSpace.single i (1 : ℝ))) x
        (EuclideanSpace.single i (1 : ℝ)) =
      -(2 * ∫ x, w x ^ 2 * (fderiv ℝ W x (EuclideanSpace.single i (1 : ℝ))) ^ 2) -
        4 * ∫ x, w x * fderiv ℝ w x (EuclideanSpace.single i (1 : ℝ)) * W x *
          fderiv ℝ W x (EuclideanSpace.single i (1 : ℝ)) := by
  set e : Euc d := EuclideanSpace.single i (1 : ℝ) with he
  have hW1 : ContDiff ℝ 1 W := hW.of_le (by norm_num)
  have hDW : ContDiff ℝ 1 (fun y => fderiv ℝ W y e) :=
    (hW.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  set f : Euc d → ℝ := fun x => w x ^ 2 * W x with hf
  have hf1 : ContDiff ℝ 1 f := (hw.pow 2).mul hW1
  have hfc : HasCompactSupport f := (hwc.comp_left (g := fun t : ℝ => t ^ 2) (by simp)).mul_right
  have h1 := r3_ibp_cs (g := fun y => fderiv ℝ W y e) e hf1 hDW hfc
  have hder : ∀ x, fderiv ℝ f x e = 2 * w x * fderiv ℝ w x e * W x + w x ^ 2 * fderiv ℝ W x e := by
    intro x
    have hwd : DifferentiableAt ℝ w x := (hw.differentiable one_ne_zero) x
    have hWd : DifferentiableAt ℝ W x := (hW1.differentiable one_ne_zero) x
    have h2 := (hwd.hasFDerivAt.pow 2).mul hWd.hasFDerivAt
    have h3 : fderiv ℝ f x = _ := h2.fderiv
    rw [h3]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have hc1 : Continuous (fun x => w x ^ 2 * (fderiv ℝ W x e) ^ 2) :=
    (hw.continuous.pow 2).mul (((hW1.continuous_fderiv one_ne_zero).clm_apply continuous_const).pow 2)
  have hc2 : Continuous (fun x => w x * fderiv ℝ w x e * W x * fderiv ℝ W x e) :=
    ((hw.continuous.mul ((hw.continuous_fderiv one_ne_zero).clm_apply continuous_const)).mul hW1.continuous).mul
      ((hW1.continuous_fderiv one_ne_zero).clm_apply continuous_const)
  have hcs1 : HasCompactSupport (fun x => w x ^ 2 * (fderiv ℝ W x e) ^ 2) :=
    (hwc.comp_left (g := fun t : ℝ => t ^ 2) (by simp)).mul_right
  have hcs2 : HasCompactSupport (fun x => w x * fderiv ℝ w x e * W x * fderiv ℝ W x e) :=
    HasCompactSupport.intro hwc fun x hx => by
      have : w x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [this]
  have hi1 := Continuous.integrable_of_hasCompactSupport (μ := (volume : Measure (Euc d))) hc1 hcs1
  have hi2 := Continuous.integrable_of_hasCompactSupport (μ := (volume : Measure (Euc d))) hc2 hcs2
  have e1 : (fun x => 2 * w x ^ 2 * W x * fderiv ℝ (fun y => fderiv ℝ W y e) x e) =
      fun x => 2 * (f x * fderiv ℝ (fun y => fderiv ℝ W y e) x e) := funext fun x => by simp only [hf]; ring
  have e2 : (fun x => fderiv ℝ f x e * fderiv ℝ W x e) = fun x => 2 * (w x * fderiv ℝ w x e * W x * fderiv ℝ W x e) +
      w x ^ 2 * (fderiv ℝ W x e) ^ 2 := funext fun x => by rw [hder]; ring
  rw [e1, integral_const_mul, h1, e2, integral_add (hi2.const_mul 2) hi1, integral_const_mul]
  ring

end HRS.MH.AdjointRd.Phase2SA12Near
