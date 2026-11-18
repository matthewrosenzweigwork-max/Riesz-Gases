import HRS.MC.L2C3Aux9
import HRS.MC.L2C1

/-!
# Packet L2C-3, helper 10: stage 3 -- comparison with the frozen semigroup (conjunct (2))

The difference `w = Q_β F(t-τ) - S_β(τ) Q_β φ` is controlled by the same Lyapunov functional (`S` = the
frozen semigroup path); its differential inequality has the forcing `C e^{-2κ(t-τ)} ∫ρ_β|∇F|²`, which is
integrated against the weighted energy estimate of stage 1 (Duhamel).
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Sec7 HRS.PDE HRS.PDE.MFAdjoint HRS.PDE.MFLinear

namespace HRS.MC.L2C3

variable {d : ℕ}

theorem l2c3_exp_ineq {a κ σ τ r : ℝ} (ha : 0 ≤ a) (hκ : 0 ≤ κ) (hσ : 0 ≤ σ) (hστ : σ ≤ τ)
    (hr : 0 ≤ r) :
    Real.exp (a * σ) * Real.exp (-2 * κ * (r + τ - σ)) ≤
      Real.exp (-κ * r) * Real.exp (a / 2 * τ) * Real.exp (a / 2 * σ) := by
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  nlinarith [mul_nonneg ha (sub_nonneg.2 hστ), mul_nonneg hκ (sub_nonneg.2 hστ), mul_nonneg hκ hr]

theorem l2c3_E1_nonneg (R : Regime d) (Cx : Ctx R) (t : ℝ) (F : ℝ → Torus d → ℝ) (τ : ℝ) :
    0 ≤ l2c3_E1 R t F τ :=
  integral_nonneg fun x => mul_nonneg (le_trans Cx.hc₀.le (Cx.hlow' x)) (sq_nonneg _)

theorem l2c3_stage3 (R : Regime d) (Cx : Ctx R) {Cm κ : ℝ} (hCm : 0 ≤ Cm) (hκ : 0 < κ)
    (hL : L2C3Lyap R Cx Cm κ) {K2 : ℝ} (hK2 : 0 ≤ K2) :
    ∃ K3 : ℝ, 0 < K3 ∧ ∀ {t : ℝ}, 0 < t → ∀ {φ : Torus d → ℝ}, Torus.IsSmooth φ →
      ∀ {F : ℝ → Torus d → ℝ}, IsClassicalAdjointSolution R.D R.ρ t φ F →
      (∀ r ∈ Set.Icc (0 : ℝ) t, Torus.IsSmooth (F r)) → ∀ τ ∈ Set.Icc (0 : ℝ) t,
      R.β⁻¹ * ∫ σ in (0 : ℝ)..τ, Real.exp (l2c3_rate R Cx / 2 * σ) * l2c3_E1 R t F σ ≤
        K2 * PDE.l2NormSq (projMean (withDensityReal R.ρβ) φ) →
      PDE.l2NormSq (fun x => projMean (withDensityReal R.ρβ) (F (t - τ)) x -
          PDE.equilibriumSemigroup R.D R.ρβ τ (projMean (withDensityReal R.ρβ) φ) x) ≤
        K3 * Real.exp (-κ * (t - τ)) * Real.exp (-(l2c3_rate R Cx / 2) * τ) *
          PDE.l2NormSq (projMean (withDensityReal R.ρβ) φ) := by
  have hν : 0 < R.β⁻¹ := inv_pos.2 R.hβ
  have ha := l2c3_rate_pos R Cx
  have hc₀ := Cx.hc₀
  have hκ₁ := Cx.hκ₁
  have hκ₂ := Cx.hκ₂
  have hcP := Cx.hcP
  set a : ℝ := l2c3_rate R Cx with ha_def
  set C₄ : ℝ := Cm ^ 2 / (R.β⁻¹ * Cx.cP) * Cx.c₀⁻¹ with hC₄
  have hC₄0 : 0 ≤ C₄ := by positivity
  refine ⟨Cx.c₀⁻¹ * Cx.κ₁ * (C₄ * K2 / R.β⁻¹) + 1, by positivity, ?_⟩
  intro t ht φ hφ F hF hFs τ hτ hW
  have hmem : ∀ τ ∈ Set.Icc (0 : ℝ) t, t - τ ∈ Set.Icc (0 : ℝ) t := fun τ hτ =>
    ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
  have hd1 := Cx.hd1
  -- the frozen path
  have hψs : Torus.IsSmooth (projMean (withDensityReal R.ρβ) φ) :=
    (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift φ) from hφ).sub contDiff_const
  have hψc : Continuous (projMean (withDensityReal R.ρβ) φ) :=
    Torus.continuous_of_continuous_lift (PDE.MFPair.isCk_of_smooth_ps hψs 0).continuous
  have hψm : MemSobolev ((PDE.mStar d : ℝ) + 4) (projMean (withDensityReal R.ρβ) φ) :=
    PDE.MFSemigroup.memSobolev_of_isSmooth hψs _
  have hD := (HRS.MC.L2C1.l2c1_dyn_eq R).symm
  have hpath := frozen_path_data hd1 Cx.H hψc hψm ht
  rw [hD] at hpath
  obtain ⟨hS2, hS0, hSc, hSg, hSd⟩ := hpath
  have hSz := frozen_zero hd1 Cx.H hψc hψm
  unfold Sg at hSz
  rw [hD] at hSz
  obtain ⟨hA, hB, hC⟩ := hL ht hF hFs
    (S := fun τ => equilibriumSemigroup R.D R.ρβ τ (projMean (withDensityReal R.ρβ) φ))
    hS2 hS0 hSc hSg hSd
  have hcF : ∀ τ ∈ Set.Icc (0 : ℝ) t, Continuous (F (t - τ)) := fun τ hτ =>
    ClassicalAux.continuous_f_apply hF (hmem τ hτ)
  have hcS : ∀ τ ∈ Set.Icc (0 : ℝ) t, Continuous
      (equilibriumSemigroup R.D R.ρβ τ (projMean (withDensityReal R.ρβ) φ)) := fun τ hτ =>
    MFAux.continuous_of_isCk ((hS2 τ hτ).of_le (by norm_num))
  have hFnn : ∀ τ ∈ Set.Icc (0 : ℝ) t, 0 ≤ l2c3_Fv Cx t F
      (fun τ => equilibriumSemigroup R.D R.ρβ τ (projMean (withDensityReal R.ρβ) φ)) τ := by
    intro τ _
    have h1 := (Cx.hform (l2c3_y R t F (fun τ => equilibriumSemigroup R.D R.ρβ τ
      (projMean (withDensityReal R.ρβ) φ)) τ)).1
    have h0 := sq_nonneg ‖l2c3_y R t F (fun τ => equilibriumSemigroup R.D R.ρβ τ
      (projMean (withDensityReal R.ρβ) φ)) τ‖
    by_contra h
    push Not at h
    unfold l2c3_Fv at h
    nlinarith [mul_neg_of_pos_of_neg hκ₁ h]
  choose! f hf using hB
  have hpw : ∀ σ ∈ Set.Ioo (0 : ℝ) t, f σ ≤ -a * l2c3_Fv Cx t F
      (fun τ => equilibriumSemigroup R.D R.ρβ τ (projMean (withDensityReal R.ρβ) φ)) σ +
      C₄ * Real.exp (-2 * κ * (t - σ)) * l2c3_E1 R t F σ := by
    intro σ hσ
    have hσ' : σ ∈ Set.Icc (0 : ℝ) t := Set.Ioo_subset_Icc_self hσ
    have hb := (hf σ hσ).2
    have hF1 : Torus.IsCk 1 (F (t - σ)) := l2c3_isCk_of_smooth (hFs _ (hmem σ hσ')) 1
    have h := l2c3_pw3 (ν := R.β⁻¹) (cP := Cx.cP) hν hcP hCm hb (hC σ hσ').2
      (l2c3_Nn_nonneg R t F σ)
    have he : Real.exp (-κ * (t - σ)) ^ 2 = Real.exp (-2 * κ * (t - σ)) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [he] at h
    have h2 := (hC σ hσ').2
    have h3 : l2c3_Fv Cx t F (fun τ => equilibriumSemigroup R.D R.ρβ τ
        (projMean (withDensityReal R.ρβ) φ)) σ ≤
        Cx.κ₂ * ‖l2c3_y R t F (fun τ => equilibriumSemigroup R.D R.ρβ τ
          (projMean (withDensityReal R.ρβ) φ)) σ‖ ^ 2 := (Cx.hform _).2
    have h4 : a * l2c3_Fv Cx t F (fun τ => equilibriumSemigroup R.D R.ρβ τ
        (projMean (withDensityReal R.ρβ) φ)) σ ≤ R.β⁻¹ * l2c3_Ev R t F
        (fun τ => equilibriumSemigroup R.D R.ρβ τ (projMean (withDensityReal R.ρβ) φ)) σ := by
      calc _ ≤ a * (Cx.κ₂ * ‖l2c3_y R t F (fun τ => equilibriumSemigroup R.D R.ρβ τ
              (projMean (withDensityReal R.ρβ) φ)) σ‖ ^ 2) := mul_le_mul_of_nonneg_left h3 ha.le
        _ = R.β⁻¹ * (Cx.cP * ‖l2c3_y R t F (fun τ => equilibriumSemigroup R.D R.ρβ τ
              (projMean (withDensityReal R.ρβ) φ)) σ‖ ^ 2) := by
          rw [← mul_assoc, ha_def, l2c3_rate_mul]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h2 hν.le
    have h5 : Cm ^ 2 / (R.β⁻¹ * Cx.cP) * Real.exp (-2 * κ * (t - σ)) * l2c3_Nn R t F σ ≤
        C₄ * Real.exp (-2 * κ * (t - σ)) * l2c3_E1 R t F σ := by
      have hN := l2c3_Nn_le R Cx hF1
      have hN' : l2c3_Nn R t F σ ≤ Cx.c₀⁻¹ * l2c3_E1 R t F σ := by
        rw [← div_eq_inv_mul, le_div_iff₀ hc₀]; linarith
      have hA0 : 0 ≤ Cm ^ 2 / (R.β⁻¹ * Cx.cP) * Real.exp (-2 * κ * (t - σ)) := by positivity
      calc _ ≤ Cm ^ 2 / (R.β⁻¹ * Cx.cP) * Real.exp (-2 * κ * (t - σ)) *
            (Cx.c₀⁻¹ * l2c3_E1 R t F σ) := mul_le_mul_of_nonneg_left hN' hA0
        _ = _ := by rw [hC₄]; ring
    linarith
  have hd : ∀ σ ∈ Set.Ioo (0 : ℝ) t, HasDerivAt (l2c3_Fv Cx t F
      (fun τ => equilibriumSemigroup R.D R.ρβ τ (projMean (withDensityReal R.ρβ) φ))) (f σ) σ :=
    fun σ hσ => (hf σ hσ).1
  have hhc : ContinuousOn (fun σ => C₄ * Real.exp (-2 * κ * (t - σ)) * l2c3_E1 R t F σ)
      (Set.Icc 0 t) := by
    refine ContinuousOn.mul (continuous_const.mul ?_).continuousOn (l2c3_E1_cont R Cx hF)
    exact Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))
  have hdu := l2c3_duhamel (a := a) ht.le hA hhc hd hpw hτ
  -- the initial value vanishes
  have hF0 : l2c3_Fv Cx t F (fun τ => equilibriumSemigroup R.D R.ρβ τ
      (projMean (withDensityReal R.ρβ) φ)) 0 ≤ 0 := by
    have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) t := ⟨le_rfl, ht.le⟩
    have h1 : l2c3_Fv Cx t F (fun τ => equilibriumSemigroup R.D R.ρβ τ
        (projMean (withDensityReal R.ρβ) φ)) 0 ≤ Cx.κ₂ * ‖l2c3_y R t F (fun τ =>
          equilibriumSemigroup R.D R.ρβ τ (projMean (withDensityReal R.ρβ) φ)) 0‖ ^ 2 :=
      (Cx.hform _).2
    have h2 := (hC 0 h0).1
    have hz : (fun x => projMean (withDensityReal R.ρβ) (F (t - 0)) x -
        equilibriumSemigroup R.D R.ρβ 0 (projMean (withDensityReal R.ρβ) φ) x) = fun _ => 0 := by
      funext x
      rw [sub_zero, hF.terminal, hSz]
      have := MFSemigroup.pair_projMean (withDensityReal R.ρβ) φ
      simp only [projMean, pair] at this ⊢
      linarith
    rw [hz] at h2
    have h3 : l2Inner (withDensityReal R.ρβ) (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) = 0 := by
      simp [l2Inner]
    rw [h3] at h2
    rw [h2] at h1
    simpa using h1
  -- the integral bound
  have hE1c := l2c3_E1_cont R Cx hF
  have hτt : τ ≤ t := hτ.2
  have hcontL : ContinuousOn (fun σ => Real.exp (a * σ) *
      (C₄ * Real.exp (-2 * κ * (t - σ)) * l2c3_E1 R t F σ)) (Set.Icc 0 τ) :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul hhc).mono
      (Set.Icc_subset_Icc le_rfl hτt)
  have hcontR : ContinuousOn (fun σ => Real.exp (a / 2 * σ) * l2c3_E1 R t F σ) (Set.Icc 0 τ) :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul hE1c).mono
      (Set.Icc_subset_Icc le_rfl hτt)
  set B : ℝ := C₄ * Real.exp (-κ * (t - τ)) * Real.exp (a / 2 * τ) with hB_def
  have hB0 : 0 ≤ B := by positivity
  have hint : ∫ σ in (0 : ℝ)..τ, Real.exp (a * σ) *
      (C₄ * Real.exp (-2 * κ * (t - σ)) * l2c3_E1 R t F σ) ≤
      B * ∫ σ in (0 : ℝ)..τ, Real.exp (a / 2 * σ) * l2c3_E1 R t F σ := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hτ.1
      (by rw [intervalIntegrable_iff_integrableOn_Icc_of_le hτ.1]; exact hcontL.integrableOn_Icc)
      (by rw [intervalIntegrable_iff_integrableOn_Icc_of_le hτ.1]
          exact (continuousOn_const.mul hcontR).integrableOn_Icc) fun σ hσ => ?_
    have hE := l2c3_E1_nonneg R Cx t F σ
    have hex := l2c3_exp_ineq (a := a) (κ := κ) ha.le hκ.le hσ.1 hσ.2 (sub_nonneg.2 hτt)
    have hr : t - τ + τ - σ = t - σ := by ring
    rw [hr] at hex
    have hCE : 0 ≤ C₄ * l2c3_E1 R t F σ := mul_nonneg hC₄0 hE
    calc Real.exp (a * σ) * (C₄ * Real.exp (-2 * κ * (t - σ)) * l2c3_E1 R t F σ)
        = (C₄ * l2c3_E1 R t F σ) * (Real.exp (a * σ) * Real.exp (-2 * κ * (t - σ))) := by ring
      _ ≤ (C₄ * l2c3_E1 R t F σ) * (Real.exp (-κ * (t - τ)) * Real.exp (a / 2 * τ) *
            Real.exp (a / 2 * σ)) := mul_le_mul_of_nonneg_left hex hCE
      _ = B * (Real.exp (a / 2 * σ) * l2c3_E1 R t F σ) := by rw [hB_def]; ring
  have hI0 : 0 ≤ ∫ σ in (0 : ℝ)..τ, Real.exp (a / 2 * σ) * l2c3_E1 R t F σ :=
    intervalIntegral.integral_nonneg hτ.1 fun σ _ =>
      mul_nonneg (Real.exp_pos _).le (l2c3_E1_nonneg R Cx t F σ)
  have hIK : ∫ σ in (0 : ℝ)..τ, Real.exp (a / 2 * σ) * l2c3_E1 R t F σ ≤
      K2 * PDE.l2NormSq (projMean (withDensityReal R.ρβ) φ) / R.β⁻¹ := by
    rw [le_div_iff₀ hν]; linarith
  have hQ0 : 0 ≤ PDE.l2NormSq (projMean (withDensityReal R.ρβ) φ) :=
    integral_nonneg fun x => sq_nonneg _
  set Fw := l2c3_Fv Cx t F
    (fun τ => equilibriumSemigroup R.D R.ρβ τ (projMean (withDensityReal R.ρβ) φ)) with hFw
  -- bound for `Fw τ`
  have hFwτ : Fw τ ≤ C₄ * K2 * PDE.l2NormSq (projMean (withDensityReal R.ρβ) φ) / R.β⁻¹ *
      Real.exp (-κ * (t - τ)) * Real.exp (-(a / 2) * τ) := by
    have h1 : Real.exp (a * τ) * Fw τ ≤ B * (K2 * PDE.l2NormSq (projMean (withDensityReal R.ρβ) φ) /
        R.β⁻¹) := by
      calc Real.exp (a * τ) * Fw τ ≤ Fw 0 + ∫ σ in (0 : ℝ)..τ, Real.exp (a * σ) *
            (C₄ * Real.exp (-2 * κ * (t - σ)) * l2c3_E1 R t F σ) := hdu
        _ ≤ 0 + B * ∫ σ in (0 : ℝ)..τ, Real.exp (a / 2 * σ) * l2c3_E1 R t F σ :=
          add_le_add hF0 hint
        _ ≤ _ := by rw [zero_add]; exact mul_le_mul_of_nonneg_left hIK hB0
    have e1 : Real.exp (a * τ) * Real.exp (-(a / 2) * τ) = Real.exp (a / 2 * τ) := by
      rw [← Real.exp_add]; congr 1; ring
    refine le_of_mul_le_mul_left ?_ (Real.exp_pos (a * τ))
    calc Real.exp (a * τ) * Fw τ ≤ _ := h1
      _ = Real.exp (a * τ) * (C₄ * K2 * PDE.l2NormSq (projMean (withDensityReal R.ρβ) φ) / R.β⁻¹ *
            Real.exp (-κ * (t - τ)) * Real.exp (-(a / 2) * τ)) := by
        rw [hB_def, ← e1]; ring
  -- conclusion
  have hcv : Continuous (fun x => projMean (withDensityReal R.ρβ) (F (t - τ)) x -
      equilibriumSemigroup R.D R.ρβ τ (projMean (withDensityReal R.ρβ) φ) x) :=
    ((hcF τ hτ).sub continuous_const).sub (hcS τ hτ)
  have hb := (HRS.MC.L2C1.l2c1_l2Inner_bounds Cx.hprob Cx.hρc Cx.hlow' Cx.hup hcv).1
  have hy2 := (hC τ hτ).1
  have hyF : ‖l2c3_y R t F (fun τ => equilibriumSemigroup R.D R.ρβ τ
      (projMean (withDensityReal R.ρβ) φ)) τ‖ ^ 2 ≤ Cx.κ₁ * Fw τ := (Cx.hform _).1
  have hnorm : Cx.c₀ * PDE.l2NormSq (fun x => projMean (withDensityReal R.ρβ) (F (t - τ)) x -
      equilibriumSemigroup R.D R.ρβ τ (projMean (withDensityReal R.ρβ) φ) x) ≤ Cx.κ₁ * Fw τ := by
    unfold PDE.l2NormSq
    exact hb.trans (hy2 ▸ hyF)
  have hnorm' : PDE.l2NormSq (fun x => projMean (withDensityReal R.ρβ) (F (t - τ)) x -
      equilibriumSemigroup R.D R.ρβ τ (projMean (withDensityReal R.ρβ) φ) x) ≤
      Cx.c₀⁻¹ * (Cx.κ₁ * Fw τ) := by
    rw [← div_eq_inv_mul, le_div_iff₀ hc₀]; linarith
  have hpos1 : 0 ≤ Real.exp (-κ * (t - τ)) * Real.exp (-(a / 2) * τ) * 
      PDE.l2NormSq (projMean (withDensityReal R.ρβ) φ) := by positivity
  calc _ ≤ Cx.c₀⁻¹ * (Cx.κ₁ * Fw τ) := hnorm'
    _ ≤ Cx.c₀⁻¹ * (Cx.κ₁ * (C₄ * K2 * PDE.l2NormSq (projMean (withDensityReal R.ρβ) φ) / R.β⁻¹ *
          Real.exp (-κ * (t - τ)) * Real.exp (-(a / 2) * τ))) := by
        gcongr
    _ = (Cx.c₀⁻¹ * Cx.κ₁ * (C₄ * K2 / R.β⁻¹)) * (Real.exp (-κ * (t - τ)) *
          Real.exp (-(a / 2) * τ) * PDE.l2NormSq (projMean (withDensityReal R.ρβ) φ)) := by ring
    _ ≤ (Cx.c₀⁻¹ * Cx.κ₁ * (C₄ * K2 / R.β⁻¹) + 1) * (Real.exp (-κ * (t - τ)) *
          Real.exp (-(a / 2) * τ) * PDE.l2NormSq (projMean (withDensityReal R.ρβ) φ)) := by
        nlinarith
    _ = _ := by ring

end HRS.MC.L2C3
