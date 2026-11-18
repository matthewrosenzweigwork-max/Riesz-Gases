import HRS.MS.MfeConfAux81

/-!
# S.B.1, packet F8 (part 14): bounds and Lipschitz constants of the components `a_j = ∂_jG`, `F_j`, `∂_jV` at one density
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace HRS.MS.MfeConf

variable {d : ℕ}

theorem sb1_lv_cv_abs_bdd {f φ : Euc d → ℝ} {A : ℝ} (hf : ∀ z, |f z| ≤ A) (hφ : Integrable φ)
    (hm : AEStronglyMeasurable (fun y => f y) volume) (x : Euc d) (hfm : Measurable f) :
    |sb1_lv_cv f φ x| ≤ A * ∫ y, |φ y| := by
  unfold sb1_lv_cv
  have hpt : ∀ y, ‖φ y * f (x - y)‖ ≤ |φ y| * A := fun y => by
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hf _) (abs_nonneg _)
  have := norm_integral_le_of_norm_le (hφ.abs.mul_const A) (Eventually.of_forall hpt)
  rw [integral_mul_const, Real.norm_eq_abs] at this
  linarith [mul_comm (∫ y, |φ y|) A]

section Dens

variable {D : Whole.WholeDyn d} {s r₀ : ℝ} {k : Euc d → ℝ} {h : Euc d → ℝ} {Cρ M1 Lg L2 C B : ℝ}

theorem sb1_lv_a_bound (hk4 : IsP4Kernel d D.s r₀ k) (hd : 1 ≤ d) (hs0 : 0 ≤ D.s) (hsd : D.s < d)
    (hR : Sb1KerR d k Lg) (hL : ∀ z, ‖fderiv ℝ k z‖ ≤ Lg) (R : Sb1Rho h Cρ M1) (j : Fin d) (x : Euc d) :
    |sb1_lv_a k h j x| ≤ Lg := by
  have e := sb1_lv_dG_eq hk4 hd hs0 hsd hR R j x
  unfold sb1_lv_a
  rw [e]
  have := sb1_lv_cv_abs_bdd (f := sb1_lv_dk k j) (φ := h) (fun z => sb1_lv_dk_bound hL j z) R.integrable
    ((sb1_lv_dk_cont hk4.smooth j).aestronglyMeasurable) x (sb1_lv_dk_cont hk4.smooth j).measurable
  have h1 : ∫ y, |h y| = 1 := by
    rw [← R.dens.integral_one]
    exact integral_congr_ae (Eventually.of_forall fun y => abs_of_nonneg (R.dens.nonneg y))
  rw [h1, mul_one] at this
  exact this

theorem sb1_lv_a_lip (hk4 : IsP4Kernel d D.s r₀ k) (hd : 1 ≤ d) (hs0 : 0 ≤ D.s) (hsd : D.s < d)
    (hR : Sb1KerR d k Lg) (hL : ∀ z, ‖fderiv ℝ k z‖ ≤ Lg) (hL2 : ∀ z, ‖fderiv ℝ (fderiv ℝ k) z‖ ≤ L2)
    (R : Sb1Rho h Cρ M1) (j : Fin d) (x y : Euc d) :
    |sb1_lv_a k h j x - sb1_lv_a k h j y| ≤ L2 * ‖x - y‖ := by
  have hdiff : Differentiable ℝ (sb1_lv_a k h j) := fun z =>
    (sb1_lv_dG_hasFDerivAt hk4 hd hs0 hsd hR hL hL2 R j z).differentiableAt
  have hb : ∀ z ∈ (Set.univ : Set (Euc d)), ‖fderiv ℝ (sb1_lv_a k h j) z‖ ≤ L2 := by
    intro z _
    have e : fderiv ℝ (sb1_lv_a k h j) z = ∫ y, h y • fderiv ℝ (sb1_lv_dk k j) (z - y) :=
      (sb1_lv_dG_hasFDerivAt hk4 hd hs0 hsd hR hL hL2 R j z).fderiv
    rw [e]
    have hn := norm_integral_le_of_norm_le (R.integrable.norm.mul_const L2)
      (Eventually.of_forall fun y => by
        have : ‖h y • fderiv ℝ (sb1_lv_dk k j) (z - y)‖ ≤ ‖h y‖ * L2 := by
          rw [norm_smul]
          exact mul_le_mul_of_nonneg_left (sb1_lv_dk_fderiv_bound hk4.smooth hL2 j _) (norm_nonneg _)
        exact this)
    rw [integral_mul_const] at hn
    have h1 : ∫ y, ‖h y‖ = 1 := by
      rw [← R.dens.integral_one]
      exact integral_congr_ae (Eventually.of_forall fun y => by
        show ‖h y‖ = h y
        rw [Real.norm_eq_abs]; exact abs_of_nonneg (R.dens.nonneg y))
    rw [h1, one_mul] at hn
    exact hn
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (f := sb1_lv_a k h j) (s := Set.univ) (C := L2)
    (fun z _ => hdiff z) hb convex_univ (Set.mem_univ y) (Set.mem_univ x)
  rw [← Real.norm_eq_abs]
  exact this

theorem sb1_lv_F_bound (hd : 1 ≤ d) (hs0 : 0 ≤ D.s) (hsd : D.s < d) (S : Sb1Slice d C h) (j : Fin d) (x : Euc d) :
    |sb1F d D.s h j x| ≤ sb1BF d D.s C := by
  have := (sb1F_contDiff hd hs0 hsd S j).2 0 (by norm_num) x
  rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this

theorem sb1_lv_dF_bound' (hd : 1 ≤ d) (hs0 : 0 ≤ D.s) (hsd : D.s < d) (S : Sb1Slice d C h) (j : Fin d) (x : Euc d) :
    ‖fderiv ℝ (sb1F d D.s h j) x‖ ≤ sb1BF d D.s C := by
  have := (sb1F_contDiff hd hs0 hsd S j).2 1 le_rfl x
  rwa [norm_iteratedFDeriv_one] at this

theorem sb1_lv_F_lip (hd : 1 ≤ d) (hs0 : 0 ≤ D.s) (hsd : D.s < d) (S : Sb1Slice d C h) (j : Fin d) (x y : Euc d) :
    |sb1F d D.s h j x - sb1F d D.s h j y| ≤ sb1BF d D.s C * ‖x - y‖ := by
  have hdiff : Differentiable ℝ (sb1F d D.s h j) := ((sb1F_contDiff hd hs0 hsd S j).1.differentiable (by norm_num))
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (f := sb1F d D.s h j) (s := Set.univ) (C := sb1BF d D.s C)
    (fun z _ => hdiff z) (fun z _ => sb1_lv_dF_bound' hd hs0 hsd S j z) convex_univ (Set.mem_univ y) (Set.mem_univ x)
  rw [← Real.norm_eq_abs]
  exact this

theorem sb1_lv_dV_bound (P : Sb1Pot D.V B) (j : Fin d) (x : Euc d) :
    |fderiv ℝ D.V x (sb1e j)| ≤ ‖fderiv ℝ D.V 0‖ + B * ‖x‖ :=
  (sb1_apply_single_le _ j).trans (sb1_gradV_bound P x)

theorem sb1_lv_dV_lip (P : Sb1Pot D.V B) (j : Fin d) (x y : Euc d) :
    |fderiv ℝ D.V x (sb1e j) - fderiv ℝ D.V y (sb1e j)| ≤ B * ‖x - y‖ := by
  have hd : Differentiable ℝ (fun z => fderiv ℝ D.V z (sb1e j)) := (sb1_dV_k_contDiff P j).differentiable (by norm_num)
  have hb : ∀ z ∈ (Set.univ : Set (Euc d)), ‖fderiv ℝ (fun z => fderiv ℝ D.V z (sb1e j)) z‖ ≤ B := by
    intro z _
    have hdd : DifferentiableAt ℝ (fderiv ℝ D.V) z :=
      ((P.c3.fderiv_right (m := 2) (by norm_num)).differentiable (by norm_num)) z
    have e : fderiv ℝ (fun z => fderiv ℝ D.V z (sb1e j)) z = (fderiv ℝ (fderiv ℝ D.V) z).flip (sb1e j) := by
      rw [fderiv_clm_apply hdd (differentiableAt_const _)]; simp
    rw [e]
    have h4 : ‖fderiv ℝ (fderiv ℝ D.V) z‖ ≤ B := by rw [sb1_norm_fderiv_fderiv]; exact P.bd z
    refine ContinuousLinearMap.opNorm_le_bound _ ((norm_nonneg (fderiv ℝ (fderiv ℝ D.V) z)).trans h4) fun v => ?_
    simp only [ContinuousLinearMap.flip_apply]
    have h1 := (fderiv ℝ (fderiv ℝ D.V) z v).le_opNorm (sb1e j)
    have h2 := (fderiv ℝ (fderiv ℝ D.V) z).le_opNorm v
    have h3 : ‖sb1e j‖ = 1 := by simp [sb1e]
    rw [h3, mul_one] at h1
    calc ‖fderiv ℝ (fderiv ℝ D.V) z v (sb1e j)‖ ≤ ‖fderiv ℝ (fderiv ℝ D.V) z v‖ := h1
      _ ≤ ‖fderiv ℝ (fderiv ℝ D.V) z‖ * ‖v‖ := h2
      _ ≤ B * ‖v‖ := mul_le_mul_of_nonneg_right h4 (norm_nonneg _)
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (f := fun z => fderiv ℝ D.V z (sb1e j)) (s := Set.univ)
    (C := B) (fun z _ => hd z) hb convex_univ (Set.mem_univ y) (Set.mem_univ x)
  rw [← Real.norm_eq_abs]
  exact this

end Dens

end HRS.MS.MfeConf
