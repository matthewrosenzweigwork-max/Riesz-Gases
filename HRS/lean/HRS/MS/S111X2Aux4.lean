import HRS.MS.S111X2Aux3

/-!
# S11.1 X2, packet E01: the response form `ResponseForm` (generic part)
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology

namespace HRS.MS.S111X2

open HRS.Whole HRS.Whole.Q34
open HRS (Euc)

/-- Finite, coercive response calculus on the native function representatives (linearity is a.e.). -/
structure ResponseForm {d : ℕ} (g : Euc d → ℝ) (mu : Measure (Euc d)) (theta eta : ℝ) : Prop where
  solution : ∀ f : Euc d → ℝ, MemLp f 2 mu →
    HRS.Whole.IsResponse g mu theta f (HRS.Whole.responseInverse g mu theta f)
  linear : ∀ f h : Euc d → ℝ, MemLp f 2 mu → MemLp h 2 mu → ∀ c : ℝ,
    HRS.Whole.responseInverse g mu theta (f + c • h) =ᵐ[mu]
      HRS.Whole.responseInverse g mu theta f + c • HRS.Whole.responseInverse g mu theta h
  symmetry : ∀ f h : Euc d → ℝ, MemLp f 2 mu → MemLp h 2 mu →
    HRS.Whole.susceptibilityCov g mu theta f h = HRS.Whole.susceptibilityCov g mu theta h f
  coercive : ∀ f : Euc d → ℝ, MemLp f 2 mu →
    eta * s111x2_centeredSquare mu f ≤ HRS.Whole.susceptibilityCov g mu theta f f ∧
      HRS.Whole.susceptibilityCov g mu theta f f ≤ s111x2_centeredSquare mu f
  schwarz : ∀ f h : Euc d → ℝ, MemLp f 2 mu → MemLp h 2 mu →
    |HRS.Whole.susceptibilityCov g mu theta f h| ≤
      Real.sqrt (s111x2_centeredSquare mu f) * Real.sqrt (s111x2_centeredSquare mu h)

section

variable {d : ℕ} {ν : Measure (Euc d)} [IsProbabilityMeasure ν] {g : Euc d → ℝ}

theorem s111x2_projMean_lin {f h : Euc d → ℝ} (hf : MemLp f 2 ν) (hh : MemLp h 2 ν) (c : ℝ) (x : Euc d) :
    HRS.Whole.projMean ν (f + c • h) x =
      HRS.Whole.projMean ν f x + c * HRS.Whole.projMean ν h x := by
  have h1 : Integrable f ν := hf.integrable (by norm_num)
  have h2 : Integrable h ν := hh.integrable (by norm_num)
  simp only [HRS.Whole.projMean, HRS.Whole.pair, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [integral_add h1 (h2.const_mul c), integral_const_mul]
  ring

theorem s111x2_cl_lin {f h : Euc d → ℝ} (hf : MemLp f 2 ν) (hh : MemLp h 2 ν) (c : ℝ) :
    s111x2_cl (hf.add (hh.const_smul c)) = s111x2_cl hf + c • s111x2_cl hh := by
  apply Lp.ext
  filter_upwards [s111x2_cl_ae (hf.add (hh.const_smul c)), s111x2_cl_ae hf, s111x2_cl_ae hh,
    Lp.coeFn_add (s111x2_cl hf) (c • s111x2_cl hh), Lp.coeFn_smul c (s111x2_cl hh)]
    with x h1 h2 h3 h4 h5
  rw [← h1, h4, Pi.add_apply, h5, Pi.smul_apply, smul_eq_mul, ← h2, ← h3]
  exact s111x2_projMean_lin hf hh c x

variable {K : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν} {Mg : ℝ}

/-- **E01 (generic part).** -/
theorem s111x2_responseForm (hK : KRep g ν K Mg) {θ Γ : ℝ} (hθ : 0 ≤ θ) (hθΓ : θ ≤ Γ) :
    ResponseForm g ν θ (1 + Γ * Mg)⁻¹ := by
  have hMg := hK.nonneg
  have hΓ : 0 ≤ Γ := hθ.trans hθΓ
  refine ⟨fun f hf => ?_, fun f h hf hh c => ?_, fun f h hf hh => ?_, fun f hf => ?_, fun f h hf hh => ?_⟩
  · have hex : ∃ h, HRS.Whole.IsResponse g ν θ f h := ⟨_, s111x2_resp_exists hK hθ hf⟩
    unfold HRS.Whole.responseInverse
    rw [dif_pos hex]
    exact hex.choose_spec
  · have e1 := s111x2_responseInverse_ae hK hθ (hf.add (hh.const_smul c))
    have e2 := s111x2_responseInverse_ae hK hθ hf
    have e3 := s111x2_responseInverse_ae hK hθ hh
    have hcl := s111x2_cl_lin hf hh c
    have hR : s111x2_Res hK.posOp hθ (s111x2_cl (hf.add (hh.const_smul c))) =
        s111x2_Res hK.posOp hθ (s111x2_cl hf) + c • s111x2_Res hK.posOp hθ (s111x2_cl hh) := by
      rw [hcl, s111x2_Res_add, s111x2_Res_smul]
    filter_upwards [e1, e2, e3,
      Lp.coeFn_add (s111x2_Res hK.posOp hθ (s111x2_cl hf)) (c • s111x2_Res hK.posOp hθ (s111x2_cl hh)),
      Lp.coeFn_smul c (s111x2_Res hK.posOp hθ (s111x2_cl hh))] with x h1 h2 h3 h4 h5
    rw [h1, hR, h4, Pi.add_apply, h5, Pi.smul_apply, smul_eq_mul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, h2, h3]
  · rw [s111x2_susc_eq hK hθ hf hh, s111x2_susc_eq hK hθ hh hf]
    rw [← s111x2_Res_symm hK.posOp hθ, real_inner_comm]
  · rw [s111x2_susc_eq hK hθ hf hf, ← s111x2_cl_norm_sq hf]
    obtain ⟨b1, b2, -⟩ := s111x2_Res_bounds hK.posOp hθ (s111x2_cl hf)
    refine ⟨?_, b2⟩
    refine le_trans ?_ b1
    have h1 : 0 < 1 + Γ * Mg := by positivity
    have h2 : 1 + θ * Mg ≤ 1 + Γ * Mg := by nlinarith
    have h3 : 0 < 1 + θ * Mg := by positivity
    rw [inv_mul_eq_div]
    exact div_le_div_of_nonneg_left (sq_nonneg _) h3 h2
  · rw [s111x2_susc_eq hK hθ hf hh, ← s111x2_cl_norm_sq hf, ← s111x2_cl_norm_sq hh,
      Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]
    obtain ⟨-, -, b3⟩ := s111x2_Res_bounds hK.posOp hθ (s111x2_cl hh)
    calc |inner ℝ (s111x2_cl hf) (s111x2_Res hK.posOp hθ (s111x2_cl hh))|
        ≤ ‖s111x2_cl hf‖ * ‖s111x2_Res hK.posOp hθ (s111x2_cl hh)‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖s111x2_cl hf‖ * ‖s111x2_cl hh‖ := by gcongr

end

end HRS.MS.S111X2
