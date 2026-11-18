import HRS.MS.MfeConfAux83

/-!
# S.B.1, packet F8 (part 16): growth and weighted Lipschitz bounds of the one-body source `Θ`

`sb1_lv_Theta_bounds`: `|Θ(x)| ≤ cΘ (1+|x|²)` and `Θ` is weighted Lipschitz with constant `DΘ`, where the constants are
affine in the Lipschitz constant `Kv` of the exact transport `v = mfeTransportW D h` (and depend on nothing else
time-dependent).  The terms quadratic in the transport field cancelled exactly in `sb1_lv_Theta_eq`.
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace HRS.MS.MfeConf

variable {d : ℕ}

theorem sb1_lv_cdF_nonneg {s : ℝ} (hs0 : 0 ≤ s) {C : ℝ} (hC : 0 ≤ C) : 0 ≤ sb1_lv_cdF d s C :=
  sb1BF_nonneg hs0 hC

theorem sb1_lv_affine_le {c0 c1 t : ℝ} (h0 : 0 ≤ c0) (h1 : 0 ≤ c1) (ht : 0 ≤ t) : c0 + c1 * t ≤ (c0 + c1) * (1 + t ^ 2) := by
  nlinarith [mul_nonneg h0 (sq_nonneg t), mul_nonneg h1 (sq_nonneg (t - 1))]

section Dens

variable {D : Whole.WholeDyn d} {r₀ : ℝ} {k : Euc d → ℝ} {h : Euc d → ℝ} {Cρ M1 Lg L2 C B : ℝ}

/-- the constants of the bounds of `Θ` -/
def sb1_lv_B1 (d : ℕ) (D : Whole.WholeDyn d) (C Lg V0 : ℝ) : ℝ := V0 + d * (Lg + sb1BF d D.s C)

def sb1_lv_cTheta (d : ℕ) (D : Whole.WholeDyn d) (C B Lg L2 V0 G0 G1 Kv : ℝ) : ℝ :=
  (D.invβ * (d * (L2 + sb1BF d D.s C)) + d * (Lg + sb1BF d D.s C) * (sb1_lv_B1 d D C Lg V0 + G0) + d * Lg * V0 + G1) +
    (d * (Lg + sb1BF d D.s C) * (Kv + B) + d * Lg * Kv + G1)

def sb1_lv_DTheta (d : ℕ) (D : Whole.WholeDyn d) (C B Lg L2 V0 G0 LG I1 Kv : ℝ) : ℝ :=
  |D.invβ| * (d * L2 * I1 + d * sb1_lv_cdF d D.s C) +
    d * ((L2 + sb1BF d D.s C) * ((sb1_lv_B1 d D C Lg V0 + G0) + (Kv + B)) +
      (Lg + sb1BF d D.s C) * ((Kv + d * (L2 + sb1BF d D.s C)) + B)) +
    d * (L2 * (V0 + Kv) + Lg * Kv) + LG

theorem sb1_lv_Theta_bounds (hθ : 0 < D.invβ) (P : Sb1Pot D.V B) (hk4 : IsP4Kernel d D.s r₀ k) (hd : 1 ≤ d)
    (hs0 : 0 ≤ D.s) (hsd : D.s < d) (hR : Sb1KerR d k Lg) (hL : ∀ z, ‖fderiv ℝ k z‖ ≤ Lg)
    (hL2 : ∀ z, ‖fderiv ℝ (fderiv ℝ k) z‖ ≤ L2) (R : Sb1Rho h Cρ M1) (S : Sb1Slice d C h)
    (hpos : ∀ y, 0 < h y) {Kv V0 : ℝ} (hKv : 0 ≤ Kv)
    (hv : ∀ x y, ‖Whole.mfeTransportW D h x - Whole.mfeTransportW D h y‖ ≤ Kv * ‖x - y‖)
    (hV0' : ‖Whole.mfeTransportW D h 0‖ ≤ V0)
    {gd : Euc d → ℝ} {G1 LG I1 : ℝ} (hG1 : 0 ≤ G1) (hLG : 0 ≤ LG) (hgd : ∀ x, |gd x| ≤ G1 * (1 + ‖x‖))
    (hgdl : ∀ x y, |gd x - gd y| ≤ LG * ‖x - y‖)
    (hdh_int : ∀ j : Fin d, Integrable (fun y => fderiv ℝ h y (sb1e j)))
    (hdh_mom : ∀ j : Fin d, Integrable (fun y => |fderiv ℝ h y (sb1e j)| * ‖y‖))
    (hI1 : ∀ j : Fin d, ∫ y, |fderiv ℝ h y (sb1e j)| ≤ I1) :
    (∀ x, |sb1_lv_Theta D k h gd x| ≤
      sb1_lv_cTheta d D C B Lg L2 V0 ‖fderiv ℝ D.V 0‖ G1 Kv * (1 + ‖x‖ ^ 2)) ∧
    Sb1WL (sb1_lv_Theta D k h gd)
      (sb1_lv_DTheta d D C B Lg L2 V0 ‖fderiv ℝ D.V 0‖ LG I1 Kv) := by
  obtain ⟨hu1, hu2⟩ := sb1_lv_u_bounds hk4 hd hs0 hsd hR hL hL2 P R S hpos hv
  have hθ0 : 0 ≤ D.invβ := hθ.le
  have hBF : 0 ≤ sb1BF d D.s C := sb1BF_nonneg hs0 S.C_nonneg
  have hLg : 0 ≤ Lg := (norm_nonneg _).trans (hL 0)
  have hL2' : 0 ≤ L2 := (norm_nonneg (fderiv ℝ (fderiv ℝ k) 0)).trans (hL2 0)
  have hB : 0 ≤ B := P.B_nonneg
  set BF := sb1BF d D.s C with hBFdef
  have hV00 : 0 ≤ V0 := (norm_nonneg _).trans hV0'
  set G0 := ‖fderiv ℝ D.V 0‖ with hG0
  have hG00 : 0 ≤ G0 := norm_nonneg _
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hcdF := sb1_lv_cdF_nonneg (d := d) hs0 S.C_nonneg
  -- component facts
  have hvj_b : ∀ x j, |Whole.mfeTransportW D h x j| ≤ V0 + Kv * ‖x‖ := by
    intro x j
    have h1 : ‖Whole.mfeTransportW D h x‖ ≤ V0 + Kv * ‖x‖ := by
      have h2 := hv x 0
      rw [sub_zero] at h2
      have := norm_le_insert' (Whole.mfeTransportW D h x) (Whole.mfeTransportW D h 0)
      linarith
    have h3 : |Whole.mfeTransportW D h x j| ≤ ‖Whole.mfeTransportW D h x‖ := by
      simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (Whole.mfeTransportW D h x) j
    exact h3.trans h1
  have hvj_l : ∀ x y j, |Whole.mfeTransportW D h x j - Whole.mfeTransportW D h y j| ≤ Kv * ‖x - y‖ := by
    intro x y j
    have := PiLp.norm_apply_le (Whole.mfeTransportW D h x - Whole.mfeTransportW D h y) j
    simp only [PiLp.sub_apply, Real.norm_eq_abs] at this
    exact this.trans (hv x y)
  have huj_b : ∀ x j, |sb1_lv_u D k h x j| ≤ sb1_lv_B1 d D C Lg V0 + Kv * ‖x‖ := by
    intro x j
    have := PiLp.norm_apply_le (sb1_lv_u D k h x) j
    simp only [Real.norm_eq_abs] at this
    refine this.trans ((hu1 x).trans ?_)
    unfold sb1_lv_B1
    linarith
  have huj_l : ∀ x y j, |sb1_lv_u D k h x j - sb1_lv_u D k h y j| ≤ (Kv + d * (L2 + BF)) * ‖x - y‖ := by
    intro x y j
    have := PiLp.norm_apply_le (sb1_lv_u D k h x - sb1_lv_u D k h y) j
    simp only [PiLp.sub_apply, Real.norm_eq_abs] at this
    exact this.trans (hu2 x y)
  have hg_b : ∀ x j, |sb1_lv_u D k h x j - fderiv ℝ D.V x (sb1e j)| ≤
      (sb1_lv_B1 d D C Lg V0 + G0) + (Kv + B) * ‖x‖ := by
    intro x j
    refine (abs_sub _ _).trans ?_
    have := huj_b x j
    have := sb1_lv_dV_bound P j x
    nlinarith
  have hg_l : ∀ x y j, |(sb1_lv_u D k h x j - fderiv ℝ D.V x (sb1e j)) -
      (sb1_lv_u D k h y j - fderiv ℝ D.V y (sb1e j))| ≤ ((Kv + d * (L2 + BF)) + B) * ‖x - y‖ := by
    intro x y j
    have e : (sb1_lv_u D k h x j - fderiv ℝ D.V x (sb1e j)) - (sb1_lv_u D k h y j - fderiv ℝ D.V y (sb1e j)) =
        (sb1_lv_u D k h x j - sb1_lv_u D k h y j) - (fderiv ℝ D.V x (sb1e j) - fderiv ℝ D.V y (sb1e j)) := by ring
    rw [e]
    refine (abs_sub _ _).trans ?_
    have := huj_l x y j
    have := sb1_lv_dV_lip P j x y
    nlinarith
  have he_b : ∀ x j, |sb1_lv_a k h j x - sb1F d D.s h j x| ≤ Lg + BF := fun x j =>
    (abs_sub _ _).trans (add_le_add (sb1_lv_a_bound hk4 hd hs0 hsd hR hL R j x) (sb1_lv_F_bound hd hs0 hsd S j x))
  have he_l : ∀ x y j, |(sb1_lv_a k h j x - sb1F d D.s h j x) - (sb1_lv_a k h j y - sb1F d D.s h j y)| ≤
      (L2 + BF) * ‖x - y‖ := by
    intro x y j
    have e : (sb1_lv_a k h j x - sb1F d D.s h j x) - (sb1_lv_a k h j y - sb1F d D.s h j y) =
        (sb1_lv_a k h j x - sb1_lv_a k h j y) - (sb1F d D.s h j x - sb1F d D.s h j y) := by ring
    rw [e]
    refine (abs_sub _ _).trans ?_
    have := sb1_lv_a_lip hk4 hd hs0 hsd hR hL hL2 R j x y
    have := sb1_lv_F_lip hd hs0 hsd S j x y
    nlinarith
  have hI : ∫ y, |h y| = 1 := by
    rw [← R.dens.integral_one]
    exact integral_congr_ae (Eventually.of_forall fun y => abs_of_nonneg (R.dens.nonneg y))
  -- the three parts
  have hcv_b : ∀ x j, |sb1_lv_cv (sb1_lv_hjj k j) h x| ≤ L2 := by
    intro x j
    have := sb1_lv_cv_abs_bdd (f := sb1_lv_hjj k j) (φ := h) (fun z => sb1_lv_hjj_bound hk4.smooth hL2 j z)
      R.integrable (sb1_lv_hjj_cont hk4.smooth j).aestronglyMeasurable x (sb1_lv_hjj_cont hk4.smooth j).measurable
    rwa [hI, mul_one] at this
  have hcv_l : ∀ x y j, |sb1_lv_cv (sb1_lv_hjj k j) h x - sb1_lv_cv (sb1_lv_hjj k j) h y| ≤ L2 * I1 * ‖x - y‖ := by
    intro x y j
    have hdh : Differentiable ℝ h := S.decay.1.differentiable (by norm_num)
    have hdc : Continuous (fderiv ℝ h) := S.decay.1.continuous_fderiv (by norm_num)
    have := sb1_lv_hjj_lip hk4 hL hL2 R hdh hdc j (hdh_int j) (hdh_mom j) x y
    refine this.trans ?_
    have h1 := hI1 j
    have h2 := norm_nonneg (x - y)
    nlinarith [mul_nonneg hL2' h2]
  have hdF_b : ∀ x, |∑ j, fderiv ℝ (sb1F d D.s h j) x (sb1e j)| ≤ d * BF := by
    intro x
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ j : Fin d, BF := Finset.sum_le_sum fun j _ => (sb1_apply_single_le _ j).trans (sb1_lv_dF_bound' hd hs0 hsd S j x)
      _ = _ := by simp
  have hcvs_b : ∀ x, |∑ j, sb1_lv_cv (sb1_lv_hjj k j) h x| ≤ d * L2 := by
    intro x
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ j : Fin d, L2 := Finset.sum_le_sum fun j _ => hcv_b x j
      _ = _ := by simp
  have hcvs_l : ∀ x y, |∑ j, sb1_lv_cv (sb1_lv_hjj k j) h x - ∑ j, sb1_lv_cv (sb1_lv_hjj k j) h y| ≤
      d * (L2 * I1) * ‖x - y‖ := by
    intro x y
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ j : Fin d, L2 * I1 * ‖x - y‖ := Finset.sum_le_sum fun j _ => hcv_l x y j
      _ = _ := by simp; ring
  have hA1_b : ∀ x, |D.invβ * (∑ j, sb1_lv_cv (sb1_lv_hjj k j) h x - ∑ j, fderiv ℝ (sb1F d D.s h j) x (sb1e j))| ≤
      D.invβ * (d * (L2 + BF)) := by
    intro x
    rw [abs_mul, abs_of_nonneg hθ0]
    refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans ?_) hθ0
    have := hcvs_b x
    have := hdF_b x
    nlinarith
  have hA1_l : ∀ x y, |D.invβ * (∑ j, sb1_lv_cv (sb1_lv_hjj k j) h x - ∑ j, fderiv ℝ (sb1F d D.s h j) x (sb1e j)) -
      D.invβ * (∑ j, sb1_lv_cv (sb1_lv_hjj k j) h y - ∑ j, fderiv ℝ (sb1F d D.s h j) y (sb1e j))| ≤
      (|D.invβ| * (d * L2 * I1 + d * sb1_lv_cdF d D.s C)) * ‖x - y‖ := by
    intro x y
    rw [← mul_sub, abs_mul]
    have e : (∑ j, sb1_lv_cv (sb1_lv_hjj k j) h x - ∑ j, fderiv ℝ (sb1F d D.s h j) x (sb1e j)) -
        (∑ j, sb1_lv_cv (sb1_lv_hjj k j) h y - ∑ j, fderiv ℝ (sb1F d D.s h j) y (sb1e j)) =
        (∑ j, sb1_lv_cv (sb1_lv_hjj k j) h x - ∑ j, sb1_lv_cv (sb1_lv_hjj k j) h y) -
        (∑ j, fderiv ℝ (sb1F d D.s h j) x (sb1e j) - ∑ j, fderiv ℝ (sb1F d D.s h j) y (sb1e j)) := by ring
    rw [e]
    have h1 := hcvs_l x y
    have h2 := sb1_lv_divF_lip hd hs0 hsd S x y
    have h3 := (abs_sub (∑ j, sb1_lv_cv (sb1_lv_hjj k j) h x - ∑ j, sb1_lv_cv (sb1_lv_hjj k j) h y)
      (∑ j, fderiv ℝ (sb1F d D.s h j) x (sb1e j) - ∑ j, fderiv ℝ (sb1F d D.s h j) y (sb1e j)))
    have h4 := mul_le_mul_of_nonneg_left (h3.trans (add_le_add h1 h2)) (abs_nonneg D.invβ)
    nlinarith
  have hΘeq : ∀ x, sb1_lv_Theta D k h gd x =
      D.invβ * (∑ j, sb1_lv_cv (sb1_lv_hjj k j) h x - ∑ j, fderiv ℝ (sb1F d D.s h j) x (sb1e j)) +
      ∑ j, (sb1_lv_a k h j x - sb1F d D.s h j x) * (sb1_lv_u D k h x j - fderiv ℝ D.V x (sb1e j)) +
      ((∑ j, sb1_lv_a k h j x * Whole.mfeTransportW D h x j) - gd x) := fun x =>
    sb1_lv_Theta_eq P hk4 hd hs0 hsd hR hL hL2 R S hpos gd x
  have hI10 : 0 ≤ I1 := (integral_nonneg fun y => abs_nonneg _).trans (hI1 ⟨0, by omega⟩)
  have hB1 : 0 ≤ sb1_lv_B1 d D C Lg V0 := by unfold sb1_lv_B1; positivity
  have hCe : 0 ≤ Lg + BF := by positivity
  constructor
  · intro x
    rw [hΘeq x]
    have h2 : |∑ j, (sb1_lv_a k h j x - sb1F d D.s h j x) * (sb1_lv_u D k h x j - fderiv ℝ D.V x (sb1e j))| ≤
        d * ((Lg + BF) * ((sb1_lv_B1 d D C Lg V0 + G0) + (Kv + B) * ‖x‖)) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc _ ≤ ∑ j : Fin d, (Lg + BF) * ((sb1_lv_B1 d D C Lg V0 + G0) + (Kv + B) * ‖x‖) := by
            refine Finset.sum_le_sum fun j _ => ?_
            rw [abs_mul]
            exact mul_le_mul (he_b x j) (hg_b x j) (abs_nonneg _) hCe
        _ = _ := by simp
    have h3 : |(∑ j, sb1_lv_a k h j x * Whole.mfeTransportW D h x j) - gd x| ≤
        d * (Lg * (V0 + Kv * ‖x‖)) + G1 * (1 + ‖x‖) := by
      refine (abs_sub _ _).trans (add_le_add ?_ (hgd x))
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc _ ≤ ∑ j : Fin d, Lg * (V0 + Kv * ‖x‖) := by
            refine Finset.sum_le_sum fun j _ => ?_
            rw [abs_mul]
            exact mul_le_mul (sb1_lv_a_bound hk4 hd hs0 hsd hR hL R j x) (hvj_b x j) (abs_nonneg _) hLg
        _ = _ := by simp
    have h1 := hA1_b x
    have hx := norm_nonneg x
    have hx1 : ‖x‖ ≤ 1 + ‖x‖ ^ 2 := by nlinarith [sq_nonneg (‖x‖ - 1)]
    have hx2 : (1 : ℝ) ≤ 1 + ‖x‖ ^ 2 := by nlinarith [sq_nonneg ‖x‖]
    have c0 : 0 ≤ D.invβ * (d * (L2 + BF)) + d * (Lg + BF) * (sb1_lv_B1 d D C Lg V0 + G0) + d * Lg * V0 + G1 := by
      positivity
    have c1 : 0 ≤ d * (Lg + BF) * (Kv + B) + d * Lg * Kv + G1 := by positivity
    unfold sb1_lv_cTheta
    have e2 : (d : ℝ) * ((Lg + BF) * ((sb1_lv_B1 d D C Lg V0 + G0) + (Kv + B) * ‖x‖)) =
        d * (Lg + BF) * (sb1_lv_B1 d D C Lg V0 + G0) + d * (Lg + BF) * (Kv + B) * ‖x‖ := by ring
    have e3 : (d : ℝ) * (Lg * (V0 + Kv * ‖x‖)) + G1 * (1 + ‖x‖) = d * Lg * V0 + G1 + (d * Lg * Kv + G1) * ‖x‖ := by ring
    have e4 : (D.invβ * (d * (L2 + BF)) + d * (Lg + BF) * (sb1_lv_B1 d D C Lg V0 + G0) + d * Lg * V0 + G1) +
        (d * (Lg + BF) * (Kv + B) + d * Lg * Kv + G1) * ‖x‖ =
        (D.invβ * (d * (L2 + BF)) + d * (Lg + BF) * (sb1_lv_B1 d D C Lg V0 + G0) + d * Lg * V0 + G1) +
        (d * (Lg + BF) * (Kv + B) + d * Lg * Kv + G1) * ‖x‖ := rfl
    have key := sb1_lv_affine_le c0 c1 hx
    refine (abs_add_three _ _ _).trans (le_trans ?_ key)
    rw [e2] at h2
    rw [e3] at h3
    linarith

  · rw [show sb1_lv_Theta D k h gd = fun x => (D.invβ * (∑ j, sb1_lv_cv (sb1_lv_hjj k j) h x -
        ∑ j, fderiv ℝ (sb1F d D.s h j) x (sb1e j)) +
      ∑ j, (sb1_lv_a k h j x - sb1F d D.s h j x) * (sb1_lv_u D k h x j - fderiv ℝ D.V x (sb1e j))) +
      ((∑ j, sb1_lv_a k h j x * Whole.mfeTransportW D h x j) - gd x) from funext hΘeq]
    have w1 : Sb1WL (fun x => D.invβ * (∑ j, sb1_lv_cv (sb1_lv_hjj k j) h x -
        ∑ j, fderiv ℝ (sb1F d D.s h j) x (sb1e j))) (|D.invβ| * (d * L2 * I1 + d * sb1_lv_cdF d D.s C)) :=
      Sb1WL.of_lip (by positivity) hA1_l
    have w2 : Sb1WL (fun x => ∑ j, (sb1_lv_a k h j x - sb1F d D.s h j x) *
        (sb1_lv_u D k h x j - fderiv ℝ D.V x (sb1e j)))
        (∑ j : Fin d, ((L2 + BF) * ((sb1_lv_B1 d D C Lg V0 + G0) + (Kv + B)) +
          (Lg + BF) * ((Kv + d * (L2 + BF)) + B))) := by
      refine Sb1WL.sum Finset.univ fun j _ => ?_
      exact Sb1WL.mul hCe (by positivity) (by positivity) (by positivity) (by positivity)
        (fun x => he_b x j) (fun x y => he_l x y j) (fun x => hg_b x j) (fun x y => hg_l x y j)
    have w3 : Sb1WL (fun x => (∑ j, sb1_lv_a k h j x * Whole.mfeTransportW D h x j) - gd x)
        ((∑ j : Fin d, (L2 * (V0 + Kv) + Lg * Kv)) + LG) := by
      refine Sb1WL.sub (Sb1WL.sum Finset.univ fun j _ => ?_) (Sb1WL.of_lip hLG hgdl)
      exact Sb1WL.mul hLg hL2' hV00 hKv hKv (fun x => sb1_lv_a_bound hk4 hd hs0 hsd hR hL R j x)
        (fun x y => sb1_lv_a_lip hk4 hd hs0 hsd hR hL hL2 R j x y) (fun x => hvj_b x j) (fun x y => hvj_l x y j)
    refine ((w1.add w2).add w3).mono (le_of_eq ?_)
    unfold sb1_lv_DTheta
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring

end Dens

end HRS.MS.MfeConf
