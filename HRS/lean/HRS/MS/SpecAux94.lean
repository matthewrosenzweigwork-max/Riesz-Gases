import HRS.MS.SpecAux93

/-!
# S8M: uniform bounds for the commutator term `g*(w ∇ρ)` (S8.7, R4)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  `s8p_Gt ρ φ = |w| ‖∇ρ‖` (`w = φ/√ρ`) is bounded, integrable, with
`∫ Gt² ≤ B₀ W₂` and `∫ Gt ≤ (W₂ + L₀)/2` where `W₂ = ∫ ρ w²`.  With `s8p_master` this gives a bound
`∫ T_v² dμ ≤ τ` for `T_v = g*(w D_vρ)`, uniform in `φ` as long as `W₂ ≤ β` (`s8p_T_unif`).
-/

noncomputable section

open MeasureTheory
open scoped ENNReal RealInnerProductSpace ContDiff

namespace HRS.MS.Spec

open HRS HRS.Whole HRS.MS.MovDec

variable {d : ℕ} {s : ℝ} {ρ : Euc d → ℝ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

theorem s8p_norm_fderiv_rho_le (hρ : Mov2eRho d ρ) (x : Euc d) :
    ‖fderiv ℝ ρ x‖ ≤ ρ x * ‖s8p_lgr ρ x‖ := by
  have hpos := hρ.pos x
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [s8p_fderiv_rho hρ, Real.norm_eq_abs, abs_mul, abs_of_pos hpos]
  calc ρ x * |inner ℝ (s8p_lgr ρ x) v| ≤ ρ x * (‖s8p_lgr ρ x‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) hpos.le
    _ = _ := by ring

/-- `|w| ‖∇ρ‖`. -/
def s8p_Gt (ρ : Euc d → ℝ) (φ : Euc d → ℝ) (y : Euc d) : ℝ := |s8p_ws ρ φ y| * ‖fderiv ℝ ρ y‖

theorem s8p_Gt_nonneg (ρ φ : Euc d → ℝ) (y : Euc d) : 0 ≤ s8p_Gt ρ φ y :=
  mul_nonneg (abs_nonneg _) (norm_nonneg _)

theorem s8p_Gt_le (hρ : Mov2eRho d ρ) (φ : 𝓢R) (y : Euc d) :
    s8p_Gt ρ φ y ≤ |φ y| * Real.sqrt (ρ y) * ‖s8p_lgr ρ y‖ := by
  have hs := hρ.psi_pos y
  have hss := hρ.psi_sq y
  unfold s8p_Gt s8p_ws
  calc |φ y / Real.sqrt (ρ y)| * ‖fderiv ℝ ρ y‖
      ≤ |φ y / Real.sqrt (ρ y)| * (ρ y * ‖s8p_lgr ρ y‖) :=
        mul_le_mul_of_nonneg_left (s8p_norm_fderiv_rho_le hρ y) (abs_nonneg _)
    _ = |φ y| * Real.sqrt (ρ y) * ‖s8p_lgr ρ y‖ := by
        rw [abs_div, abs_of_pos hs]
        generalize Real.sqrt (ρ y) = p at hs hss ⊢
        rw [← hss]
        field_simp

theorem s8p_Gt_gauss (hρ : Mov2eRho d ρ) (hE : Mov2eEll d ρ) (φ : 𝓢R) :
    ∃ C c : ℝ, 0 < c ∧ ∀ y, s8p_Gt ρ φ y ≤ C * Real.exp (-c * ‖y‖ ^ 2) := by
  obtain ⟨c, a, M0, hc, ha, hM0, hψb, hfs, hM0b, -⟩ := hE.ex
  obtain ⟨C, hC⟩ := hψb 0
  obtain ⟨mφ, hmφ⟩ := HRS.MS.MovForce.mv1_schwartz_bdd φ 0
  have hC' : ∀ x, Real.sqrt (ρ x) ≤ C * Real.exp (-c * ‖x‖ ^ 2) := fun x => by
    have := hC x
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] at this
  have hφ : ∀ x, |φ x| ≤ mφ := fun x => by
    have := hmφ x
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hmφ0 : 0 ≤ mφ := (abs_nonneg _).trans (hφ 0)
  have hC0 : 0 ≤ C := by
    have h1 := hC' 0
    have h2 : 0 < Real.sqrt (ρ 0) := Real.sqrt_pos.2 (hρ.pos 0)
    by_contra hneg
    push Not at hneg
    have : C * Real.exp (-c * ‖(0 : Euc d)‖ ^ 2) < 0 := mul_neg_of_neg_of_pos hneg (Real.exp_pos _)
    linarith
  refine ⟨mφ * C * (a / c + a / 2 + M0), c / 2, by positivity, fun y => ?_⟩
  refine (s8p_Gt_le hρ φ y).trans ?_
  set r := ‖y‖ with hr
  have h2 := s8p_lin_gauss hc ha hM0 r (norm_nonneg y)
  have h3 : Real.sqrt (ρ y) ≤ C * Real.exp (-c * r ^ 2) := hC' y
  have hp : 0 ≤ Real.exp (-c * r ^ 2) := (Real.exp_pos _).le
  have hLn : 0 ≤ a * r + M0 := by positivity
  calc |φ y| * Real.sqrt (ρ y) * ‖s8p_lgr ρ y‖
      ≤ mφ * (C * Real.exp (-c * r ^ 2)) * (a * r + M0) := by
        gcongr
        · exact hφ y
        · exact hM0b y
    _ = mφ * C * ((a * r + M0) * Real.exp (-c * r ^ 2)) := by ring
    _ ≤ mφ * C * ((a / c + a / 2 + M0) * Real.exp (-(c / 2) * r ^ 2)) := by gcongr
    _ = _ := by ring

theorem s8p_Gt_cont (hρ : Mov2eRho d ρ) (φ : 𝓢R) : Continuous (s8p_Gt ρ φ) := by
  unfold s8p_Gt
  exact (s8p_ws_smooth hρ φ).continuous.abs.mul
    ((hρ.data.smooth.continuous_fderiv (by simp)).norm)

theorem s8p_Gt_good (hρ : Mov2eRho d ρ) (hE : Mov2eEll d ρ) (φ : 𝓢R) : s8p_Good (s8p_Gt ρ φ) := by
  obtain ⟨C, c, hc, h⟩ := s8p_Gt_gauss hρ hE φ
  exact s8p_good_of_gauss (s8p_Gt_cont hρ φ) hc fun y => by
    rw [abs_of_nonneg (s8p_Gt_nonneg _ _ _)]; exact h y

/-- `W₂ = ∫ ρ w²`. -/
def s8p_W2 (ρ φ : Euc d → ℝ) : ℝ := ∫ x, ρ x * s8p_ws ρ φ x ^ 2

theorem s8p_W2_int (hρ : Mov2eRho d ρ) (φ : 𝓢R) :
    Integrable (fun x => ρ x * s8p_ws ρ φ x ^ 2) := by
  have h := (memLp_two_iff_integrable_sq (mov2e_f_data hρ φ).1.aestronglyMeasurable).1
    (mov2e_f_data hρ φ).2.1
  exact (mov2e_integrable_mu hρ).1 h

theorem s8p_W2_nonneg (hρ : Mov2eRho d ρ) (φ : 𝓢R) : 0 ≤ s8p_W2 ρ φ :=
  integral_nonneg fun x => mul_nonneg (hρ.pos x).le (sq_nonneg _)

theorem s8p_Gt_sq (hρ : Mov2eRho d ρ) (hE : Mov2eEll d ρ) (φ : 𝓢R) {B0 : ℝ} (hB0 : 0 ≤ B0)
    (hB : ∀ x, ρ x * ‖s8p_lgr ρ x‖ ^ 2 ≤ B0) :
    Integrable (fun y => s8p_Gt ρ φ y ^ 2) ∧ ∫ y, s8p_Gt ρ φ y ^ 2 ≤ B0 * s8p_W2 ρ φ := by
  have hpt : ∀ y, s8p_Gt ρ φ y ^ 2 ≤ B0 * (ρ y * s8p_ws ρ φ y ^ 2) := by
    intro y
    have h1 : s8p_Gt ρ φ y ≤ |s8p_ws ρ φ y| * (ρ y * ‖s8p_lgr ρ y‖) :=
      mul_le_mul_of_nonneg_left (s8p_norm_fderiv_rho_le hρ y) (abs_nonneg _)
    have h2 : s8p_Gt ρ φ y ^ 2 ≤ (|s8p_ws ρ φ y| * (ρ y * ‖s8p_lgr ρ y‖)) ^ 2 :=
      pow_le_pow_left₀ (s8p_Gt_nonneg _ _ _) h1 2
    have h3 : (|s8p_ws ρ φ y| * (ρ y * ‖s8p_lgr ρ y‖)) ^ 2 =
        (ρ y * s8p_ws ρ φ y ^ 2) * (ρ y * ‖s8p_lgr ρ y‖ ^ 2) := by
      rw [mul_pow, mul_pow, sq_abs]; ring
    have h4 := hB y
    have h5 : 0 ≤ ρ y * s8p_ws ρ φ y ^ 2 := mul_nonneg (hρ.pos y).le (sq_nonneg _)
    calc s8p_Gt ρ φ y ^ 2 ≤ _ := h2
      _ = _ := h3
      _ ≤ (ρ y * s8p_ws ρ φ y ^ 2) * B0 := mul_le_mul_of_nonneg_left h4 h5
      _ = _ := by ring
  have hint : Integrable (fun y => s8p_Gt ρ φ y ^ 2) := by
    refine Integrable.mono' ((s8p_W2_int hρ φ).const_mul B0)
      ((s8p_Gt_cont hρ φ).pow 2).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpt y
  refine ⟨hint, ?_⟩
  unfold s8p_W2
  rw [← integral_const_mul]
  exact integral_mono hint ((s8p_W2_int hρ φ).const_mul B0) hpt

theorem s8p_Gt_int_le (hρ : Mov2eRho d ρ) (hE : Mov2eEll d ρ) (φ : 𝓢R)
    (hL : Integrable (fun x => ρ x * ‖s8p_lgr ρ x‖ ^ 2)) :
    ∫ y, s8p_Gt ρ φ y ≤ (s8p_W2 ρ φ + ∫ x, ρ x * ‖s8p_lgr ρ x‖ ^ 2) / 2 := by
  have hG := (s8p_Gt_good hρ hE φ).2.1
  have hpt : ∀ y, s8p_Gt ρ φ y ≤ (ρ y * s8p_ws ρ φ y ^ 2 + ρ y * ‖s8p_lgr ρ y‖ ^ 2) / 2 := by
    intro y
    have h1 : s8p_Gt ρ φ y ≤ |s8p_ws ρ φ y| * (ρ y * ‖s8p_lgr ρ y‖) :=
      mul_le_mul_of_nonneg_left (s8p_norm_fderiv_rho_le hρ y) (abs_nonneg _)
    have hp := hρ.pos y
    have h2 : |s8p_ws ρ φ y| * (ρ y * ‖s8p_lgr ρ y‖) ≤
        (ρ y * s8p_ws ρ φ y ^ 2 + ρ y * ‖s8p_lgr ρ y‖ ^ 2) / 2 := by
      have := sq_nonneg (|s8p_ws ρ φ y| - ‖s8p_lgr ρ y‖)
      have h6 := sq_abs (s8p_ws ρ φ y)
      nlinarith [mul_nonneg hp.le this]
    exact h1.trans h2
  have hint : Integrable (fun y => (ρ y * s8p_ws ρ φ y ^ 2 + ρ y * ‖s8p_lgr ρ y‖ ^ 2) / 2) :=
    ((s8p_W2_int hρ φ).add hL).div_const 2
  calc ∫ y, s8p_Gt ρ φ y ≤ ∫ y, (ρ y * s8p_ws ρ φ y ^ 2 + ρ y * ‖s8p_lgr ρ y‖ ^ 2) / 2 :=
        integral_mono hG hint hpt
    _ = _ := by
        rw [integral_div, integral_add (s8p_W2_int hρ φ) hL]; rfl

theorem s8p_T_unif (hd : 1 ≤ d) (hs0 : 0 < s) (hsd : s < d) (h32 : 3 * s / 2 < d) (hρ : Mov2eRho d ρ)
    (hE : Mov2eEll d ρ) {M : ℝ} (hM : S8pRho d s ρ M) {β : ℝ} (hβ : 0 ≤ β) :
    ∃ τ : ℝ, 0 ≤ τ ∧ ∀ φ : 𝓢R, s8p_W2 ρ φ ≤ β → ∀ v : Euc d, ‖v‖ ≤ 1 →
      ∫ x, (HRS.Whole.convFun (rieszKernel d s)
        (fun y => s8p_ws ρ φ y * fderiv ℝ ρ y v) x) ^ 2 ∂(HRS.Whole.withDensityReal ρ) ≤ τ := by
  obtain ⟨A, hA0, hAm⟩ := s8p_master hM h32
  obtain ⟨B0, hB00, hB0, hLint⟩ := s8p_lgr_bounds hρ hE
  set L0 : ℝ := ∫ x, ρ x * ‖s8p_lgr ρ x‖ ^ 2 with hL0
  have hL00 : 0 ≤ L0 := integral_nonneg fun x => mul_nonneg (hρ.pos x).le (sq_nonneg _)
  refine ⟨1 + A * ((B0 * β) ^ 2 + ((β + L0) / 2) ^ 4), by positivity, fun φ hW v hv => ?_⟩
  have hGg := s8p_Gt_good hρ hE φ
  have hGt := s8p_wDrho_good hρ hE φ v
  set G := s8p_Gt ρ φ with hG
  set F : Euc d → ℝ := HRS.Whole.convFun (rieszKernel d s) (fun y => s8p_ws ρ φ y * fderiv ℝ ρ y v)
    with hF
  have hFm : Measurable F := s8p_convFun_meas hGt.1
  have hFle : ∀ x, ENNReal.ofReal |F x| ≤ ∫⁻ y, ENNReal.ofReal (rieszKernel d s (x - y) * G y) := by
    intro x
    have hI := hGg.conv_int hs0 hsd x
    have hnn : 0 ≤ᵐ[volume] fun y => rieszKernel d s (x - y) * G y :=
      Filter.Eventually.of_forall fun y => mul_nonneg (s8p_riesz_nonneg hs0 _) (s8p_Gt_nonneg _ _ _)
    have h1 : |F x| ≤ ∫ y, rieszKernel d s (x - y) * G y := by
      rw [hF]
      unfold HRS.Whole.convFun
      rw [← Real.norm_eq_abs]
      refine norm_integral_le_of_norm_le hI (Filter.Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (s8p_riesz_nonneg hs0 _), abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (s8p_riesz_nonneg hs0 _)
      rw [hG]; unfold s8p_Gt
      calc |s8p_ws ρ φ y| * |fderiv ℝ ρ y v| ≤ |s8p_ws ρ φ y| * (‖fderiv ℝ ρ y‖ * ‖v‖) := by
            gcongr
            rw [← Real.norm_eq_abs]; exact (fderiv ℝ ρ y).le_opNorm v
        _ ≤ |s8p_ws ρ φ y| * (‖fderiv ℝ ρ y‖ * 1) := by gcongr
        _ = _ := by ring
    rw [← ofReal_integral_eq_lintegral_ofReal hI hnn]
    exact ENNReal.ofReal_le_ofReal h1
  obtain ⟨hI4, hbd⟩ := hAm G F hGg.1 (s8p_Gt_nonneg ρ φ) hGg.2.1 (s8p_Gt_sq hρ hE φ hB00 hB0).1 hFm hFle
  have hG2 := (s8p_Gt_sq hρ hE φ hB00 hB0).2
  have hG1 := s8p_Gt_int_le hρ hE φ hLint
  have hG20 : 0 ≤ ∫ y, G y ^ 2 := integral_nonneg fun y => sq_nonneg _
  have hG10 : 0 ≤ ∫ y, G y := integral_nonneg (s8p_Gt_nonneg ρ φ)
  have hW0 := s8p_W2_nonneg hρ φ
  have hb1 : ∫ y, G y ^ 2 ≤ B0 * β := hG2.trans (mul_le_mul_of_nonneg_left hW hB00)
  have hb2 : ∫ y, G y ≤ (β + L0) / 2 := hG1.trans (by linarith)
  have hb3 : (∫ y, G y ^ 2) ^ 2 + (∫ y, G y) ^ 4 ≤ (B0 * β) ^ 2 + ((β + L0) / 2) ^ 4 :=
    add_le_add (pow_le_pow_left₀ hG20 hb1 2) (pow_le_pow_left₀ hG10 hb2 4)
  have hb4 := hbd.trans (mul_le_mul_of_nonneg_left hb3 hA0)
  rw [mov2e_integral_mu hρ]
  have hint : Integrable (fun x => ρ x + ρ x * F x ^ 4) := hM.int.add hI4
  have hle : ∫ x, ρ x * F x ^ 2 ≤ ∫ x, (ρ x + ρ x * F x ^ 4) := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => ?_) hint
      (Filter.Eventually.of_forall fun x => ?_)
    · exact mul_nonneg (hM.nonneg x) (sq_nonneg _)
    · simp only
      have hp := hM.nonneg x
      nlinarith [mul_nonneg hp (sq_nonneg (F x ^ 2 - 1)), mul_nonneg hp (sq_nonneg (F x))]
  rw [integral_add hM.int hI4, hM.one] at hle
  linarith

end HRS.MS.Spec
