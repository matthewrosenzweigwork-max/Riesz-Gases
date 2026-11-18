import HRS.MS.S111X1E3

/-!
# S11.1 X1 (energy), part 4: whole-space integration by parts against the thermal weight
-/

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111X1

open HRS HRS.Whole

variable {d : ℕ}

/-- `∫ f (ρ Δf + ⟨∇ρ,∇f⟩) = -∫ ρ |∇f|²` for bounded `C²` data and an integrable weight with integrable
gradient. -/
theorem ibp_weighted {ρ f : Euc d → ℝ} (hρ : ContDiff ℝ 2 ρ) (hρi : Integrable ρ)
    (hρ' : Integrable (fun x => ‖gradient ρ x‖)) (hf : ContDiff ℝ 2 f)
    {B0 B1 B2 : ℝ} (h0 : ∀ x, ‖f x‖ ≤ B0) (h1 : ∀ x, ‖fderiv ℝ f x‖ ≤ B1)
    (h2 : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ B2) :
    ∫ x, f x * (ρ x * Laplacian.laplacian f x + inner ℝ (gradient ρ x) (gradient f x)) =
      -∫ x, ρ x * ‖gradient f x‖ ^ 2 := by
  set b := stdOrthonormalBasis ℝ (Euc d) with hb
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hρd : Differentiable ℝ ρ := hρ.differentiable (by norm_num)
  have hf1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hfd1 : Differentiable ℝ (fderiv ℝ f) := hf1.differentiable (by norm_num)
  have hcf : Continuous f := hf.continuous
  have hcρ : Continuous ρ := hρ.continuous
  have hcf1 : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  have hcρ1 : Continuous (fderiv ℝ ρ) := hρ.continuous_fderiv (by norm_num)
  have hcf2 : Continuous (fderiv ℝ (fderiv ℝ f)) := hf1.continuous_fderiv (by norm_num)
  have hnρ : ∀ x, ‖fderiv ℝ ρ x‖ = ‖gradient ρ x‖ := fun x => by simp [gradient]
  have hρ'' : Integrable (fun x => ‖fderiv ℝ ρ x‖) := by simpa [hnρ] using hρ'
  have hdG : ∀ i, ∀ x, fderiv ℝ (fun y => f y * ρ y) x (b i) =
      fderiv ℝ f x (b i) * ρ x + f x * fderiv ℝ ρ x (b i) := by
    intro i x
    rw [fderiv_fun_mul (hfd x) (hρd x)]
    simp
    ring
  have hdu : ∀ i, ∀ x, fderiv ℝ (fun y => fderiv ℝ f y (b i)) x (b i) =
      fderiv ℝ (fderiv ℝ f) x (b i) (b i) := by
    intro i x
    have := (hfd1 x).hasFDerivAt.clm_apply (hasFDerivAt_const (b i) x)
    rw [this.fderiv]
    simp
  have hb1 : ∀ i x, |fderiv ℝ f x (b i)| ≤ B1 := fun i x => by
    have := (fderiv ℝ f x).le_opNorm (b i)
    rw [b.norm_eq_one i, mul_one] at this
    rw [← Real.norm_eq_abs]
    exact this.trans (h1 x)
  have hb2 : ∀ i x, |fderiv ℝ (fderiv ℝ f) x (b i) (b i)| ≤ B2 := fun i x => by
    have h3 := (fderiv ℝ (fderiv ℝ f) x).le_opNorm₂ (b i) (b i)
    rw [b.norm_eq_one i, mul_one, mul_one] at h3
    rw [← Real.norm_eq_abs]
    exact h3.trans (h2 x)
  have hb0 : 0 ≤ B0 := (norm_nonneg (f 0)).trans (h0 0)
  have hb1' : 0 ≤ B1 := (norm_nonneg (fderiv ℝ f 0)).trans (h1 0)
  have hb2' : 0 ≤ B2 := (norm_nonneg (fderiv ℝ (fderiv ℝ f) 0)).trans (h2 0)
  have cu : ∀ i, Continuous fun x => fderiv ℝ f x (b i) := fun i => hcf1.clm_apply continuous_const
  have cu' : ∀ i, Continuous fun x => fderiv ℝ (fderiv ℝ f) x (b i) (b i) := fun i =>
    (hcf2.clm_apply continuous_const).clm_apply continuous_const
  have cρ' : ∀ i, Continuous fun x => fderiv ℝ ρ x (b i) := fun i => hcρ1.clm_apply continuous_const
  have key : ∀ i, Integrable (fun x => f x * ρ x * fderiv ℝ (fderiv ℝ f) x (b i) (b i)) ∧
      Integrable (fun x => (fderiv ℝ f x (b i) * ρ x + f x * fderiv ℝ ρ x (b i)) * fderiv ℝ f x (b i)) ∧
      ∫ x, f x * ρ x * fderiv ℝ (fderiv ℝ f) x (b i) (b i) =
      -∫ x, (fderiv ℝ f x (b i) * ρ x + f x * fderiv ℝ ρ x (b i)) * fderiv ℝ f x (b i) := by
    intro i
    have hρnn : ∀ x, ‖ρ x‖ = |ρ x| := fun x => Real.norm_eq_abs _
    have hbd0 : ∀ x, |f x| ≤ B0 := fun x => by rw [← Real.norm_eq_abs]; exact h0 x
    have hbρ : ∀ x, |fderiv ℝ ρ x (b i)| ≤ ‖gradient ρ x‖ := fun x => by
      have := (fderiv ℝ ρ x).le_opNorm (b i)
      rw [b.norm_eq_one i, mul_one, hnρ] at this
      rwa [← Real.norm_eq_abs]
    have I1 : Integrable (fun x => f x * ρ x * fderiv ℝ f x (b i)) := by
      refine (hρi.norm.const_mul (B0 * B1)).mono' (((hcf.mul hcρ).mul (cu i)).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_mul, hρnn]
      have := hb1 i x
      have := hbd0 x
      have : 0 ≤ |ρ x| := abs_nonneg _
      calc |f x| * |ρ x| * |fderiv ℝ f x (b i)| ≤ B0 * |ρ x| * B1 := by gcongr
        _ = B0 * B1 * |ρ x| := by ring
    have I2 : Integrable (fun x => f x * ρ x * fderiv ℝ (fderiv ℝ f) x (b i) (b i)) := by
      refine (hρi.norm.const_mul (B0 * B2)).mono' (((hcf.mul hcρ).mul (cu' i)).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_mul, hρnn]
      have := hb2 i x
      have := hbd0 x
      have : 0 ≤ |ρ x| := abs_nonneg _
      calc |f x| * |ρ x| * |fderiv ℝ (fderiv ℝ f) x (b i) (b i)| ≤ B0 * |ρ x| * B2 := by gcongr
        _ = B0 * B2 * |ρ x| := by ring
    have I3 : Integrable (fun x => (fderiv ℝ f x (b i) * ρ x + f x * fderiv ℝ ρ x (b i)) *
        fderiv ℝ f x (b i)) := by
      refine (((hρi.norm.const_mul B1).add (hρ'.const_mul B0)).const_mul B1).mono'
        ((((cu i).mul hcρ).add (hcf.mul (cρ' i))).mul (cu i)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      have h1' := hb1 i x
      have h0' := hbd0 x
      have h3 := hbρ x
      have hρ0 : 0 ≤ |ρ x| := abs_nonneg _
      have : |fderiv ℝ f x (b i) * ρ x + f x * fderiv ℝ ρ x (b i)| ≤ B1 * |ρ x| + B0 * ‖gradient ρ x‖ := by
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul]; exact mul_le_mul_of_nonneg_right h1' hρ0
        · rw [abs_mul]; exact mul_le_mul h0' h3 (abs_nonneg _) (by linarith)
      calc |fderiv ℝ f x (b i) * ρ x + f x * fderiv ℝ ρ x (b i)| * |fderiv ℝ f x (b i)|
          ≤ (B1 * |ρ x| + B0 * ‖gradient ρ x‖) * B1 := by gcongr
        _ = B1 * (B1 * ‖ρ x‖ + B0 * ‖gradient ρ x‖) := by rw [hρnn]; ring
    have e := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
      (f := fun y => f y * ρ y) (g := fun y => fderiv ℝ f y (b i)) (v := b i)
      (by simp_rw [hdG]; exact I3) (by simp_rw [hdu]; exact I2) (by exact I1)
      (fun x _ => (hfd x).mul (hρd x)) (fun x _ => (hfd1 x).clm_apply (differentiableAt_const _))
    simp_rw [hdu, hdG] at e
    exact ⟨I2, I3, e⟩
  have hsum1 : ∀ x, ∑ i, f x * ρ x * fderiv ℝ (fderiv ℝ f) x (b i) (b i) =
      f x * ρ x * Laplacian.laplacian f x := by
    intro x
    rw [← Finset.mul_sum, InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
    simp [iteratedFDeriv_two_apply, hb]
  have hsum2 : ∀ x, ∑ i, (fderiv ℝ f x (b i) * ρ x + f x * fderiv ℝ ρ x (b i)) * fderiv ℝ f x (b i) =
      ρ x * ‖gradient f x‖ ^ 2 + f x * inner ℝ (gradient ρ x) (gradient f x) := by
    intro x
    have e1 : ∀ i, fderiv ℝ f x (b i) = inner ℝ (b i) (gradient f x) := fun i => by
      rw [HRS.MS.PoisKolm.kl_inner_gradient]
    have e2 : ∀ i, fderiv ℝ ρ x (b i) = inner ℝ (b i) (gradient ρ x) := fun i => by
      rw [HRS.MS.PoisKolm.kl_inner_gradient]
    simp_rw [e1, e2]
    have h1 := b.sum_inner_mul_inner (gradient f x) (gradient f x)
    have h2 := b.sum_inner_mul_inner (gradient ρ x) (gradient f x)
    have : ∀ i, (inner ℝ (b i) (gradient f x) * ρ x + f x * inner ℝ (b i) (gradient ρ x)) *
        inner ℝ (b i) (gradient f x) =
        ρ x * (inner ℝ (gradient f x) (b i) * inner ℝ (b i) (gradient f x)) +
          f x * (inner ℝ (gradient ρ x) (b i) * inner ℝ (b i) (gradient f x)) := fun i => by
      rw [real_inner_comm (gradient f x) (b i), real_inner_comm (gradient ρ x) (b i)]; ring
    simp_rw [this, Finset.sum_add_distrib, ← Finset.mul_sum, h1, h2, real_inner_self_eq_norm_sq]
  have hI2 := fun i => (key i).1
  have hI3 := fun i => (key i).2.1
  have hsumI : ∫ x, f x * ρ x * Laplacian.laplacian f x =
      -∫ x, (ρ x * ‖gradient f x‖ ^ 2 + f x * inner ℝ (gradient ρ x) (gradient f x)) := by
    have l1 : ∫ x, ∑ i, f x * ρ x * fderiv ℝ (fderiv ℝ f) x (b i) (b i) =
        ∑ i, ∫ x, f x * ρ x * fderiv ℝ (fderiv ℝ f) x (b i) (b i) :=
      integral_finset_sum _ fun i _ => hI2 i
    have l2 : ∫ x, ∑ i, (fderiv ℝ f x (b i) * ρ x + f x * fderiv ℝ ρ x (b i)) * fderiv ℝ f x (b i) =
        ∑ i, ∫ x, (fderiv ℝ f x (b i) * ρ x + f x * fderiv ℝ ρ x (b i)) * fderiv ℝ f x (b i) :=
      integral_finset_sum _ fun i _ => hI3 i
    simp_rw [hsum1] at l1
    simp_rw [hsum2] at l2
    rw [l1, l2, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => (key i).2.2
  -- integrability of the two pieces
  have P1 : Integrable (fun x => f x * ρ x * Laplacian.laplacian f x) := by
    have := integrable_finset_sum Finset.univ (fun i _ => hI2 i)
    simpa [hsum1] using this
  have S3 : Integrable (fun x => ρ x * ‖gradient f x‖ ^ 2 + f x * inner ℝ (gradient ρ x) (gradient f x)) := by
    have := integrable_finset_sum Finset.univ (fun i _ => hI3 i)
    simpa [hsum2] using this
  have hcg : Continuous (gradient f) := by
    have : Continuous fun x => (InnerProductSpace.toDual ℝ (Euc d)).symm (fderiv ℝ f x) :=
      (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp hcf1
    exact this
  have P3 : Integrable (fun x => ρ x * ‖gradient f x‖ ^ 2) := by
    refine (hρi.norm.mul_const (B1 ^ 2)).mono' (hcρ.mul (hcg.norm.pow 2)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    have hg1 : ‖gradient f x‖ ≤ B1 := by simpa [gradient] using h1 x
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_norm, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hg1 2) (abs_nonneg _)
  have P2 : Integrable (fun x => f x * inner ℝ (gradient ρ x) (gradient f x)) := by
    have := S3.sub P3
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp
  have hsplit : ∀ x, f x * (ρ x * Laplacian.laplacian f x + inner ℝ (gradient ρ x) (gradient f x)) =
      f x * ρ x * Laplacian.laplacian f x + f x * inner ℝ (gradient ρ x) (gradient f x) := fun x => by ring
  simp_rw [hsplit]
  rw [integral_add P1 P2, hsumI, integral_add P3 P2]
  ring

end HRS.MS.S111X1
