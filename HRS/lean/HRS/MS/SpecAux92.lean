import HRS.MS.SpecAux91

/-!
# S8M: the nonlocal term `U = g * h` splits into `g*(ρ ∂w)` and `g*(w ∂ρ)` (S8.7, R4)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  For a Schwartz `φ`, `w = φ/√ρ`, `h = √ρ φ = ρ w`, `U = g * h`: the functions
`D_v h`, `w D_vρ`, `ρ D_v w` are bounded and integrable (`s8p_Good`), `D_v h = ρ D_v w + w D_vρ`, and
`D_v U = g*(ρ D_v w) + g*(w D_vρ)` (`s8p_DU_split`).
-/

noncomputable section

open MeasureTheory
open scoped ENNReal RealInnerProductSpace ContDiff

namespace HRS.MS.Spec

open HRS HRS.Whole HRS.MS.MovDec

variable {d : ℕ} {s : ℝ} {ρ : Euc d → ℝ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

/-- `w = φ / √ρ`. -/
def s8p_ws (ρ : Euc d → ℝ) (φ : Euc d → ℝ) (x : Euc d) : ℝ := φ x / Real.sqrt (ρ x)

theorem s8p_ws_smooth (hρ : Mov2eRho d ρ) (φ : 𝓢R) : ContDiff ℝ ∞ (s8p_ws ρ φ) :=
  (φ.smooth ⊤).div hρ.data.sqrt_smooth (fun x => (hρ.psi_pos x).ne')

theorem s8p_rho_ws (hρ : Mov2eRho d ρ) (φ : 𝓢R) (x : Euc d) : ρ x * s8p_ws ρ φ x = mov2eH ρ φ x := by
  have := mov2e_rho_div hρ φ x
  simpa [s8p_ws, mov2eH] using this

theorem s8p_h_bounds (hρ : Mov2eRho d ρ) (φ : 𝓢R) :
    ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ (∀ y, |mov2eH ρ φ y| ≤ C * Real.exp (-c * ‖y‖ ^ 2)) ∧
      (∀ y, ‖fderiv ℝ (mov2eH ρ φ) y‖ ≤ C * Real.exp (-c * ‖y‖ ^ 2)) :=
  HRS.MS.MovForce.mv1_gauss01 (HRS.MS.MovForce.mv1_h_movGauss hρ.data φ 1)

theorem s8p_h_smooth (hρ : Mov2eRho d ρ) (φ : 𝓢R) : ContDiff ℝ ∞ (mov2eH ρ φ) :=
  (HRS.MS.MovForce.mv1_h_gauss hρ.data φ).1

theorem s8p_Dh_good (hρ : Mov2eRho d ρ) (φ : 𝓢R) (v : Euc d) :
    s8p_Good (fun y => fderiv ℝ (mov2eH ρ φ) y v) := by
  obtain ⟨C, c, hC, hc, -, h1⟩ := s8p_h_bounds hρ φ
  have hcont : Continuous fun y => fderiv ℝ (mov2eH ρ φ) y v :=
    ((s8p_h_smooth hρ φ).continuous_fderiv (by simp)).clm_apply continuous_const
  refine s8p_good_of_gauss hcont (C := C * ‖v‖) hc fun y => ?_
  rw [mul_assoc, mul_comm ‖v‖, ← mul_assoc]
  calc |fderiv ℝ (mov2eH ρ φ) y v| ≤ ‖fderiv ℝ (mov2eH ρ φ) y‖ * ‖v‖ := by
        rw [← Real.norm_eq_abs]; exact (fderiv ℝ (mov2eH ρ φ) y).le_opNorm v
    _ ≤ _ := mul_le_mul_of_nonneg_right (h1 y) (norm_nonneg _)

theorem s8p_wDrho_good (hρ : Mov2eRho d ρ) (hE : Mov2eEll d ρ) (φ : 𝓢R) (v : Euc d) :
    s8p_Good (fun y => s8p_ws ρ φ y * fderiv ℝ ρ y v) := by
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
  have hcont : Continuous fun y => s8p_ws ρ φ y * fderiv ℝ ρ y v :=
    (s8p_ws_smooth hρ φ).continuous.mul
      (((hρ.data.smooth.continuous_fderiv (by simp)).clm_apply continuous_const))
  refine s8p_good_of_gauss hcont (C := mφ * C * (a / c + a / 2 + M0) * ‖v‖) (c := c / 2) (by positivity)
    fun y => ?_
  have e : s8p_ws ρ φ y * fderiv ℝ ρ y v = φ y * Real.sqrt (ρ y) * inner ℝ (s8p_lgr ρ y) v := by
    rw [s8p_fderiv_rho hρ]
    have hs := hρ.psi_pos y
    have hss := hρ.psi_sq y
    unfold s8p_ws
    generalize Real.sqrt (ρ y) = p at hs hss ⊢
    rw [← hss]
    field_simp
  rw [e, abs_mul, abs_mul]
  set r := ‖y‖ with hr
  have h1 : |inner ℝ (s8p_lgr ρ y) v| ≤ (a * r + M0) * ‖v‖ := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    exact mul_le_mul_of_nonneg_right (hM0b y) (norm_nonneg _)
  have h2 := s8p_lin_gauss hc ha hM0 r (norm_nonneg y)
  have h3 : |Real.sqrt (ρ y)| ≤ C * Real.exp (-c * r ^ 2) := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]; exact hC' y
  have hp : 0 ≤ Real.exp (-c * r ^ 2) := (Real.exp_pos _).le
  have hLn : 0 ≤ a * r + M0 := by positivity
  calc |φ y| * |Real.sqrt (ρ y)| * |inner ℝ (s8p_lgr ρ y) v|
      ≤ mφ * (C * Real.exp (-c * r ^ 2)) * ((a * r + M0) * ‖v‖) := by
        gcongr
        · exact hφ y
    _ = mφ * C * ‖v‖ * ((a * r + M0) * Real.exp (-c * r ^ 2)) := by ring
    _ ≤ mφ * C * ‖v‖ * ((a / c + a / 2 + M0) * Real.exp (-(c / 2) * r ^ 2)) := by
        gcongr
    _ = _ := by ring

theorem s8p_h_fderiv (hρ : Mov2eRho d ρ) (φ : 𝓢R) (x v : Euc d) :
    fderiv ℝ (mov2eH ρ φ) x v =
      ρ x * fderiv ℝ (s8p_ws ρ φ) x v + s8p_ws ρ φ x * fderiv ℝ ρ x v := by
  have hfun : mov2eH ρ φ = fun y => ρ y * s8p_ws ρ φ y :=
    funext fun y => (s8p_rho_ws hρ φ y).symm
  have hρd : DifferentiableAt ℝ ρ x := (hρ.data.smooth.differentiable (by simp)) x
  have hwd : DifferentiableAt ℝ (s8p_ws ρ φ) x := ((s8p_ws_smooth hρ φ).differentiable (by simp)) x
  have h2 : HasFDerivAt (fun y => ρ y * s8p_ws ρ φ y)
      (ρ x • fderiv ℝ (s8p_ws ρ φ) x + s8p_ws ρ φ x • fderiv ℝ ρ x) x :=
    hρd.hasFDerivAt.mul hwd.hasFDerivAt
  rw [hfun, h2.fderiv]
  simp

theorem s8p_rhoDw_good (hρ : Mov2eRho d ρ) (hE : Mov2eEll d ρ) (φ : 𝓢R) (v : Euc d) :
    s8p_Good (fun y => ρ y * fderiv ℝ (s8p_ws ρ φ) y v) := by
  have h := (s8p_Dh_good hρ φ v).sub (s8p_wDrho_good hρ hE φ v)
  refine (show (fun y => ρ y * fderiv ℝ (s8p_ws ρ φ) y v) =
    fun y => fderiv ℝ (mov2eH ρ φ) y v - s8p_ws ρ φ y * fderiv ℝ ρ y v from ?_) ▸ h
  funext y
  rw [s8p_h_fderiv hρ φ y v]; ring

theorem s8p_DU_split (hd : 1 ≤ d) (hs0 : 0 < s) (hsd : s < d) (hρ : Mov2eRho d ρ) (hE : Mov2eEll d ρ)
    (φ : 𝓢R) (x v : Euc d) :
    fderiv ℝ (s8p_U d s ρ φ) x v =
      HRS.Whole.convFun (rieszKernel d s) (fun y => ρ y * fderiv ℝ (s8p_ws ρ φ) y v) x +
      HRS.Whole.convFun (rieszKernel d s) (fun y => s8p_ws ρ φ y * fderiv ℝ ρ y v) x := by
  obtain ⟨C, c, hC, hc, h0, h1⟩ := s8p_h_bounds hρ φ
  have hh : ContDiff ℝ 1 (mov2eH ρ φ) := (s8p_h_smooth hρ φ).of_le (by exact_mod_cast le_top)
  obtain ⟨L, hL, hLe, -⟩ := HRS.MS.MovForce.mv1_hasFDerivAt_convFun hd hs0.le hsd hc hC hh h0 h1 x
  have e1 : fderiv ℝ (s8p_U d s ρ φ) x v = HRS.Whole.convFun (rieszKernel d s)
      (fun y => fderiv ℝ (mov2eH ρ φ) y v) x := by
    show fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) (mov2eH ρ φ)) x v = _
    rw [hL.fderiv, hLe v, HRS.MS.MovForce.mv1_convFun_eq]
  rw [e1]
  have hA := s8p_rhoDw_good hρ hE φ v
  have hB := s8p_wDrho_good hρ hE φ v
  unfold HRS.Whole.convFun
  rw [← integral_add (hA.conv_int hs0 hsd x) (hB.conv_int hs0 hsd x)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  rw [s8p_h_fderiv hρ φ y v]; ring

end HRS.MS.Spec
