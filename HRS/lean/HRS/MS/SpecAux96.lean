import HRS.MS.SpecAux95

/-!
# S8M: operator-level identities for `∇w`, `∇h`, `∇U` and the pointwise bound `‖∇U‖ ≤ g * ‖∇h‖` (S8.7, R4)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  `∇w = β (∇e - ∇U)`, `∇h = ρ ∇w + w ∇ρ` (as continuous linear maps),
`‖∇h‖ ≤ ρ ‖∇w‖ + |w| ‖∇ρ‖`, and `‖∇U(x)‖ ≤ ∫ g(x-y) ‖∇h(y)‖ dy`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal RealInnerProductSpace ContDiff

namespace HRS.MS.Spec

open HRS HRS.Whole HRS.MS.MovDec

variable {d : ℕ} {s : ℝ} {ρ : Euc d → ℝ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

theorem s8p_fderiv_ws_eq (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : Mov2eRho d ρ) (hE : Mov2eEll d ρ)
    {β : ℝ} (hβ : 0 < β) (φ : 𝓢R) (x : Euc d) :
    fderiv ℝ (s8p_ws ρ φ) x = β • (fderiv ℝ (s8p_E d s β ρ φ) x - fderiv ℝ (s8p_U d s ρ φ) x) := by
  ext v
  have := s8p_E_fderiv_split hd hs0 hsd hρ hE β φ x v
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, smul_eq_mul]
  rw [this]
  field_simp
  ring

theorem s8p_Dh_eq (hρ : Mov2eRho d ρ) (φ : 𝓢R) (x : Euc d) :
    fderiv ℝ (mov2eH ρ φ) x = ρ x • fderiv ℝ (s8p_ws ρ φ) x + s8p_ws ρ φ x • fderiv ℝ ρ x := by
  ext v
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  exact s8p_h_fderiv hρ φ x v

theorem s8p_Gh_le (hρ : Mov2eRho d ρ) (φ : 𝓢R) (x : Euc d) :
    ‖fderiv ℝ (mov2eH ρ φ) x‖ ≤ ρ x * ‖fderiv ℝ (s8p_ws ρ φ) x‖ + s8p_Gt ρ φ x := by
  rw [s8p_Dh_eq hρ φ x]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_of_nonneg (hρ.pos x).le, Real.norm_eq_abs]
  rfl

theorem s8p_Gh_good (hρ : Mov2eRho d ρ) (φ : 𝓢R) : s8p_Good (fun y => ‖fderiv ℝ (mov2eH ρ φ) y‖) := by
  obtain ⟨C, c, hC, hc, -, h1⟩ := s8p_h_bounds hρ φ
  have hcont : Continuous fun y => ‖fderiv ℝ (mov2eH ρ φ) y‖ :=
    ((s8p_h_smooth hρ φ).continuous_fderiv (by simp)).norm
  exact s8p_good_of_gauss hcont hc fun y => by
    rw [abs_of_nonneg (norm_nonneg _)]; exact h1 y

theorem s8p_DU_norm_le (hd : 1 ≤ d) (hs0 : 0 < s) (hsd : s < d) (hρ : Mov2eRho d ρ) (φ : 𝓢R) (x : Euc d) :
    ‖fderiv ℝ (s8p_U d s ρ φ) x‖ ≤ ∫ y, rieszKernel d s (x - y) * ‖fderiv ℝ (mov2eH ρ φ) y‖ := by
  obtain ⟨C, c, hC, hc, h0, h1⟩ := s8p_h_bounds hρ φ
  have hh : ContDiff ℝ 1 (mov2eH ρ φ) := (s8p_h_smooth hρ φ).of_le (by exact_mod_cast le_top)
  obtain ⟨L, hL, hLe, hint⟩ := HRS.MS.MovForce.mv1_hasFDerivAt_convFun hd hs0.le hsd hc hC hh h0 h1 x
  have hfd : fderiv ℝ (s8p_U d s ρ φ) x = L := hL.fderiv
  rw [hfd]
  have hI := (s8p_Gh_good hρ φ).conv_int hs0 hsd x
  have hI' : Integrable (fun z => rieszKernel d s z * ‖fderiv ℝ (mov2eH ρ φ) (x - z)‖) := by
    have := hI.comp_sub_left x
    simpa using this
  have hcv : ∫ y, rieszKernel d s (x - y) * ‖fderiv ℝ (mov2eH ρ φ) y‖ =
      ∫ z, rieszKernel d s z * ‖fderiv ℝ (mov2eH ρ φ) (x - z)‖ :=
    (integral_sub_left_eq_self (fun y => rieszKernel d s (x - y) * ‖fderiv ℝ (mov2eH ρ φ) y‖) volume x).symm.trans
      (by simp)
  rw [hcv]
  have hnn : 0 ≤ ∫ z, rieszKernel d s z * ‖fderiv ℝ (mov2eH ρ φ) (x - z)‖ :=
    integral_nonneg fun z => mul_nonneg (s8p_riesz_nonneg hs0 _) (norm_nonneg _)
  refine ContinuousLinearMap.opNorm_le_bound _ hnn fun v => ?_
  rw [hLe v]
  have bound : ∀ z, ‖rieszKernel d s z * fderiv ℝ (mov2eH ρ φ) (x - z) v‖ ≤
      rieszKernel d s z * ‖fderiv ℝ (mov2eH ρ φ) (x - z)‖ * ‖v‖ := fun z => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (s8p_riesz_nonneg hs0 _)]
    calc rieszKernel d s z * |fderiv ℝ (mov2eH ρ φ) (x - z) v|
        ≤ rieszKernel d s z * (‖fderiv ℝ (mov2eH ρ φ) (x - z)‖ * ‖v‖) := by
          refine mul_le_mul_of_nonneg_left ?_ (s8p_riesz_nonneg hs0 _)
          rw [← Real.norm_eq_abs]; exact (fderiv ℝ (mov2eH ρ φ) (x - z)).le_opNorm v
      _ = _ := by ring
  have key := norm_integral_le_of_norm_le (hI'.mul_const ‖v‖)
    (f := fun z => rieszKernel d s z * fderiv ℝ (mov2eH ρ φ) (x - z) v)
    (Filter.Eventually.of_forall bound)
  rw [integral_mul_const] at key
  exact key

end HRS.MS.Spec
