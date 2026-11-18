import HRS.MS.S111X1E5

/-!
# S11.1 X2, packet E02 (part 1): the bilinear weighted integration by parts

`s111x2_ibp_bilinear`: for `u ∈ C¹`, `v ∈ C²` bounded with bounded derivatives, an integrable weight `ρ ∈ C²` with
integrable gradient, `∫ u (ρ Δv + ⟨∇ρ,∇v⟩) = -∫ ρ ⟨∇u,∇v⟩`  (the bilinear version of `S111X1.ibp_weighted`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111X2

open HRS HRS.Whole

variable {d : ℕ}

theorem s111x2_ibp_bilinear {ρ u v : Euc d → ℝ} (hρ : ContDiff ℝ 2 ρ) (hρi : Integrable ρ)
    (hρ' : Integrable (fun x => ‖gradient ρ x‖)) (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 2 v)
    {B0 B1 C1 C2 : ℝ} (h0 : ∀ x, ‖u x‖ ≤ B0) (h1 : ∀ x, ‖fderiv ℝ u x‖ ≤ B1)
    (g1 : ∀ x, ‖fderiv ℝ v x‖ ≤ C1) (g2 : ∀ x, ‖fderiv ℝ (fderiv ℝ v) x‖ ≤ C2) :
    ∫ x, u x * (ρ x * Laplacian.laplacian v x + inner ℝ (gradient ρ x) (gradient v x)) =
      -∫ x, ρ x * inner ℝ (gradient u x) (gradient v x) := by
  set b := stdOrthonormalBasis ℝ (Euc d) with hb
  have hud : Differentiable ℝ u := hu.differentiable (by norm_num)
  have hρd : Differentiable ℝ ρ := hρ.differentiable (by norm_num)
  have hv1 : ContDiff ℝ 1 (fderiv ℝ v) := hv.fderiv_right (by norm_num)
  have hvd1 : Differentiable ℝ (fderiv ℝ v) := hv1.differentiable (by norm_num)
  have hcu : Continuous u := hu.continuous
  have hcρ : Continuous ρ := hρ.continuous
  have hcu1 : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by norm_num)
  have hcρ1 : Continuous (fderiv ℝ ρ) := hρ.continuous_fderiv (by norm_num)
  have hcv1 : Continuous (fderiv ℝ v) := hv.continuous_fderiv (by norm_num)
  have hcv2 : Continuous (fderiv ℝ (fderiv ℝ v)) := hv1.continuous_fderiv (by norm_num)
  have hnρ : ∀ x, ‖fderiv ℝ ρ x‖ = ‖gradient ρ x‖ := fun x => by simp [gradient]
  have hdG : ∀ i, ∀ x, fderiv ℝ (fun y => u y * ρ y) x (b i) =
      fderiv ℝ u x (b i) * ρ x + u x * fderiv ℝ ρ x (b i) := by
    intro i x
    rw [fderiv_fun_mul (hud x) (hρd x)]
    simp
    ring
  have hdu : ∀ i, ∀ x, fderiv ℝ (fun y => fderiv ℝ v y (b i)) x (b i) =
      fderiv ℝ (fderiv ℝ v) x (b i) (b i) := by
    intro i x
    have := (hvd1 x).hasFDerivAt.clm_apply (hasFDerivAt_const (b i) x)
    rw [this.fderiv]
    simp
  have hbu : ∀ i x, |fderiv ℝ u x (b i)| ≤ B1 := fun i x => by
    have := (fderiv ℝ u x).le_opNorm (b i)
    rw [b.norm_eq_one i, mul_one] at this
    rw [← Real.norm_eq_abs]
    exact this.trans (h1 x)
  have hbv : ∀ i x, |fderiv ℝ v x (b i)| ≤ C1 := fun i x => by
    have := (fderiv ℝ v x).le_opNorm (b i)
    rw [b.norm_eq_one i, mul_one] at this
    rw [← Real.norm_eq_abs]
    exact this.trans (g1 x)
  have hbv2 : ∀ i x, |fderiv ℝ (fderiv ℝ v) x (b i) (b i)| ≤ C2 := fun i x => by
    have h3 := (fderiv ℝ (fderiv ℝ v) x).le_opNorm₂ (b i) (b i)
    rw [b.norm_eq_one i, mul_one, mul_one] at h3
    rw [← Real.norm_eq_abs]
    exact h3.trans (g2 x)
  have hb0 : 0 ≤ B0 := (norm_nonneg (u 0)).trans (h0 0)
  have hbd0 : ∀ x, |u x| ≤ B0 := fun x => by rw [← Real.norm_eq_abs]; exact h0 x
  have cu : ∀ i, Continuous fun x => fderiv ℝ u x (b i) := fun i => hcu1.clm_apply continuous_const
  have cv : ∀ i, Continuous fun x => fderiv ℝ v x (b i) := fun i => hcv1.clm_apply continuous_const
  have cv' : ∀ i, Continuous fun x => fderiv ℝ (fderiv ℝ v) x (b i) (b i) := fun i =>
    (hcv2.clm_apply continuous_const).clm_apply continuous_const
  have cρ' : ∀ i, Continuous fun x => fderiv ℝ ρ x (b i) := fun i => hcρ1.clm_apply continuous_const
  have key : ∀ i, Integrable (fun x => u x * ρ x * fderiv ℝ (fderiv ℝ v) x (b i) (b i)) ∧
      Integrable (fun x => (fderiv ℝ u x (b i) * ρ x + u x * fderiv ℝ ρ x (b i)) * fderiv ℝ v x (b i)) ∧
      ∫ x, u x * ρ x * fderiv ℝ (fderiv ℝ v) x (b i) (b i) =
      -∫ x, (fderiv ℝ u x (b i) * ρ x + u x * fderiv ℝ ρ x (b i)) * fderiv ℝ v x (b i) := by
    intro i
    have hρnn : ∀ x, ‖ρ x‖ = |ρ x| := fun x => Real.norm_eq_abs _
    have hbρ : ∀ x, |fderiv ℝ ρ x (b i)| ≤ ‖gradient ρ x‖ := fun x => by
      have := (fderiv ℝ ρ x).le_opNorm (b i)
      rw [b.norm_eq_one i, mul_one, hnρ] at this
      rwa [← Real.norm_eq_abs]
    have I1 : Integrable (fun x => u x * ρ x * fderiv ℝ v x (b i)) := by
      refine (hρi.norm.const_mul (B0 * C1)).mono' (((hcu.mul hcρ).mul (cv i)).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_mul, hρnn]
      have := hbv i x
      have := hbd0 x
      have : 0 ≤ |ρ x| := abs_nonneg _
      calc |u x| * |ρ x| * |fderiv ℝ v x (b i)| ≤ B0 * |ρ x| * C1 := by gcongr
        _ = B0 * C1 * |ρ x| := by ring
    have I2 : Integrable (fun x => u x * ρ x * fderiv ℝ (fderiv ℝ v) x (b i) (b i)) := by
      refine (hρi.norm.const_mul (B0 * C2)).mono' (((hcu.mul hcρ).mul (cv' i)).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_mul, hρnn]
      have := hbv2 i x
      have := hbd0 x
      have : 0 ≤ |ρ x| := abs_nonneg _
      calc |u x| * |ρ x| * |fderiv ℝ (fderiv ℝ v) x (b i) (b i)| ≤ B0 * |ρ x| * C2 := by gcongr
        _ = B0 * C2 * |ρ x| := by ring
    have I3 : Integrable (fun x => (fderiv ℝ u x (b i) * ρ x + u x * fderiv ℝ ρ x (b i)) *
        fderiv ℝ v x (b i)) := by
      refine (((hρi.norm.const_mul B1).add (hρ'.const_mul B0)).const_mul C1).mono'
        ((((cu i).mul hcρ).add (hcu.mul (cρ' i))).mul (cv i)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      have h1' := hbu i x
      have h0' := hbd0 x
      have h3 := hbρ x
      have hρ0 : 0 ≤ |ρ x| := abs_nonneg _
      have : |fderiv ℝ u x (b i) * ρ x + u x * fderiv ℝ ρ x (b i)| ≤ B1 * |ρ x| + B0 * ‖gradient ρ x‖ := by
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul]; exact mul_le_mul_of_nonneg_right h1' hρ0
        · rw [abs_mul]; exact mul_le_mul h0' h3 (abs_nonneg _) (by linarith)
      calc |fderiv ℝ u x (b i) * ρ x + u x * fderiv ℝ ρ x (b i)| * |fderiv ℝ v x (b i)|
          ≤ (B1 * |ρ x| + B0 * ‖gradient ρ x‖) * C1 :=
            mul_le_mul this (hbv i x) (abs_nonneg _)
              (add_nonneg (mul_nonneg ((norm_nonneg _).trans (h1 0)) (abs_nonneg _)) (mul_nonneg hb0 (norm_nonneg _)))
        _ = C1 * (B1 * ‖ρ x‖ + B0 * ‖gradient ρ x‖) := by rw [hρnn]; ring
    have e := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
      (f := fun y => u y * ρ y) (g := fun y => fderiv ℝ v y (b i)) (v := b i)
      (by simp_rw [hdG]; exact I3) (by simp_rw [hdu]; exact I2) (by exact I1)
      (fun x _ => (hud x).mul (hρd x)) (fun x _ => (hvd1 x).clm_apply (differentiableAt_const _))
    simp_rw [hdu, hdG] at e
    exact ⟨I2, I3, e⟩
  have hsum1 : ∀ x, ∑ i, u x * ρ x * fderiv ℝ (fderiv ℝ v) x (b i) (b i) =
      u x * ρ x * Laplacian.laplacian v x := by
    intro x
    rw [← Finset.mul_sum, InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
    simp [iteratedFDeriv_two_apply, hb]
  have hsum2 : ∀ x, ∑ i, (fderiv ℝ u x (b i) * ρ x + u x * fderiv ℝ ρ x (b i)) * fderiv ℝ v x (b i) =
      ρ x * inner ℝ (gradient u x) (gradient v x) + u x * inner ℝ (gradient ρ x) (gradient v x) := by
    intro x
    have e1 : ∀ i, fderiv ℝ v x (b i) = inner ℝ (b i) (gradient v x) := fun i => by
      rw [HRS.MS.PoisKolm.kl_inner_gradient]
    have e2 : ∀ i, fderiv ℝ ρ x (b i) = inner ℝ (b i) (gradient ρ x) := fun i => by
      rw [HRS.MS.PoisKolm.kl_inner_gradient]
    have e3 : ∀ i, fderiv ℝ u x (b i) = inner ℝ (b i) (gradient u x) := fun i => by
      rw [HRS.MS.PoisKolm.kl_inner_gradient]
    simp_rw [e1, e2, e3]
    have h1 := b.sum_inner_mul_inner (gradient u x) (gradient v x)
    have h2 := b.sum_inner_mul_inner (gradient ρ x) (gradient v x)
    have : ∀ i, (inner ℝ (b i) (gradient u x) * ρ x + u x * inner ℝ (b i) (gradient ρ x)) *
        inner ℝ (b i) (gradient v x) =
        ρ x * (inner ℝ (gradient u x) (b i) * inner ℝ (b i) (gradient v x)) +
          u x * (inner ℝ (gradient ρ x) (b i) * inner ℝ (b i) (gradient v x)) := fun i => by
      rw [real_inner_comm (gradient u x) (b i), real_inner_comm (gradient ρ x) (b i)]; ring
    simp_rw [this, Finset.sum_add_distrib, ← Finset.mul_sum, h1, h2]
  have hI2 := fun i => (key i).1
  have hI3 := fun i => (key i).2.1
  have hsumI : ∫ x, u x * ρ x * Laplacian.laplacian v x =
      -∫ x, (ρ x * inner ℝ (gradient u x) (gradient v x) + u x * inner ℝ (gradient ρ x) (gradient v x)) := by
    have l1 : ∫ x, ∑ i, u x * ρ x * fderiv ℝ (fderiv ℝ v) x (b i) (b i) =
        ∑ i, ∫ x, u x * ρ x * fderiv ℝ (fderiv ℝ v) x (b i) (b i) :=
      integral_finset_sum _ fun i _ => hI2 i
    have l2 : ∫ x, ∑ i, (fderiv ℝ u x (b i) * ρ x + u x * fderiv ℝ ρ x (b i)) * fderiv ℝ v x (b i) =
        ∑ i, ∫ x, (fderiv ℝ u x (b i) * ρ x + u x * fderiv ℝ ρ x (b i)) * fderiv ℝ v x (b i) :=
      integral_finset_sum _ fun i _ => hI3 i
    simp_rw [hsum1] at l1
    simp_rw [hsum2] at l2
    rw [l1, l2, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => (key i).2.2
  have P1 : Integrable (fun x => u x * ρ x * Laplacian.laplacian v x) := by
    have := integrable_finset_sum Finset.univ (fun i _ => hI2 i)
    simpa [hsum1] using this
  have S3 : Integrable (fun x => ρ x * inner ℝ (gradient u x) (gradient v x) +
      u x * inner ℝ (gradient ρ x) (gradient v x)) := by
    have := integrable_finset_sum Finset.univ (fun i _ => hI3 i)
    simpa [hsum2] using this
  have hcgu : Continuous (gradient u) := by
    have : Continuous fun x => (InnerProductSpace.toDual ℝ (Euc d)).symm (fderiv ℝ u x) :=
      (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp hcu1
    exact this
  have hcgv : Continuous (gradient v) := by
    have : Continuous fun x => (InnerProductSpace.toDual ℝ (Euc d)).symm (fderiv ℝ v x) :=
      (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp hcv1
    exact this
  have P3 : Integrable (fun x => ρ x * inner ℝ (gradient u x) (gradient v x)) := by
    refine (hρi.norm.mul_const (B1 * C1)).mono' (hcρ.mul (hcgu.inner hcgv)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    have hg1 : ‖gradient u x‖ ≤ B1 := by simpa [gradient] using h1 x
    have hg2 : ‖gradient v x‖ ≤ C1 := by simpa [gradient] using g1 x
    rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
    have := abs_real_inner_le_norm (gradient u x) (gradient v x)
    have h5 : |inner ℝ (gradient u x) (gradient v x)| ≤ B1 * C1 :=
      this.trans (mul_le_mul hg1 hg2 (norm_nonneg _) ((norm_nonneg _).trans hg1))
    rw [mul_comm (|ρ x|)]
    exact mul_le_mul_of_nonneg_right h5 (abs_nonneg _) |>.trans_eq (by ring)
  have P2 : Integrable (fun x => u x * inner ℝ (gradient ρ x) (gradient v x)) := by
    have := S3.sub P3
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp
  have hsplit : ∀ x, u x * (ρ x * Laplacian.laplacian v x + inner ℝ (gradient ρ x) (gradient v x)) =
      u x * ρ x * Laplacian.laplacian v x + u x * inner ℝ (gradient ρ x) (gradient v x) := fun x => by ring
  simp_rw [hsplit]
  rw [integral_add P1 P2, hsumI, integral_add P3 P2]
  ring

end HRS.MS.S111X2
