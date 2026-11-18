import HRS.MC.L2C3Aux8
import HRS.MC.L2C3Aux1

/-!
# Packet L2C-3, helper 9: stage 1 theorem
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Sec7 HRS.PDE HRS.PDE.MFAdjoint HRS.PDE.MFLinear

namespace HRS.MC.L2C3

variable {d : ℕ}

theorem l2c3_E1_cont (R : Regime d) (Cx : Ctx R) {t : ℝ} {φ : Torus d → ℝ} {F : ℝ → Torus d → ℝ}
    (hF : IsClassicalAdjointSolution R.D R.ρ t φ F) :
    ContinuousOn (l2c3_E1 R t F) (Set.Icc 0 t) := by
  have h := l2c3_energy_cont hF Cx.hρc
  have hc : ContinuousOn (fun σ : ℝ => t - σ) (Set.Icc 0 t) :=
    (continuous_const.sub continuous_id).continuousOn
  have := ContinuousOn.comp (g := fun r => ∫ x, R.ρβ x * ‖Torus.grad (F r) x‖ ^ 2) h hc
    (fun σ hσ => (⟨by linarith [hσ.2], by linarith [hσ.1]⟩ : t - σ ∈ Set.Icc (0 : ℝ) t))
  exact this

theorem l2c3_stage1 (R : Regime d) (Cx : Ctx R) {Cm κ : ℝ} (hCm : 0 ≤ Cm) (hκ : 0 < κ)
    (hL : L2C3Lyap R Cx Cm κ) :
    ∃ K1 K2 : ℝ, 0 < K1 ∧ 0 < K2 ∧ ∀ {t : ℝ}, 0 < t → ∀ {φ : Torus d → ℝ} {F : ℝ → Torus d → ℝ},
      IsClassicalAdjointSolution R.D R.ρ t φ F → (∀ r ∈ Set.Icc (0 : ℝ) t, Torus.IsSmooth (F r)) →
      (∀ τ ∈ Set.Icc (0 : ℝ) t,
        PDE.l2NormSq (projMean (withDensityReal R.ρβ) (F (t - τ))) ≤
          K1 * Real.exp (-l2c3_rate R Cx * τ) * PDE.l2NormSq (projMean (withDensityReal R.ρβ) φ)) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) t,
        R.β⁻¹ * ∫ σ in (0 : ℝ)..τ, Real.exp (l2c3_rate R Cx / 2 * σ) * l2c3_E1 R t F σ ≤
          K2 * PDE.l2NormSq (projMean (withDensityReal R.ρβ) φ)) := by
  have hν : 0 < R.β⁻¹ := inv_pos.2 R.hβ
  have ha := l2c3_rate_pos R Cx
  have hc₀ := Cx.hc₀
  have hΛ := Cx.hΛ₀
  have hκ₁ := Cx.hκ₁
  have hκ₂ := Cx.hκ₂
  have hcP := Cx.hcP
  set Cc : ℝ := Cm ^ 2 * Cx.κ₁ / (R.β⁻¹ * Cx.c₀) with hCc
  have hCc0 : 0 ≤ Cc := by positivity
  set G : ℝ := Real.exp (Cc / (2 * κ)) with hG
  have hG0 : 0 < G := Real.exp_pos _
  set a : ℝ := l2c3_rate R Cx with ha_def
  refine ⟨Cx.c₀⁻¹ * Cx.κ₁ * G * (Cx.κ₂ * Cx.Λ₀),
    (1 + (a / 2 + Cc) * G / (a / 2)) * (Cx.κ₂ * Cx.Λ₀), by positivity, by positivity, ?_⟩
  intro t ht φ F hF hFs
  have hmem : ∀ τ ∈ Set.Icc (0 : ℝ) t, t - τ ∈ Set.Icc (0 : ℝ) t := fun τ hτ =>
    ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
  obtain ⟨hS2, hS0, hSc, hSg, hSd⟩ := l2c3_zero_hyps R t
  obtain ⟨hA, hB, hC⟩ := hL ht hF hFs hS2 hS0 hSc hSg hSd
  have hcF : ∀ τ ∈ Set.Icc (0 : ℝ) t, Continuous (F (t - τ)) := fun τ hτ =>
    ClassicalAux.continuous_f_apply hF (hmem τ hτ)
  have hQc : ∀ τ ∈ Set.Icc (0 : ℝ) t, Continuous (projMean (withDensityReal R.ρβ) (F (t - τ))) :=
    fun τ hτ => (hcF τ hτ).sub continuous_const
  have hy2 : ∀ τ ∈ Set.Icc (0 : ℝ) t, ‖l2c3_y R t F (fun _ _ => 0) τ‖ ^ 2 =
      l2Inner (withDensityReal R.ρβ) (projMean (withDensityReal R.ρβ) (F (t - τ)))
        (projMean (withDensityReal R.ρβ) (F (t - τ))) := by
    intro τ hτ
    have := (hC τ hτ).1
    simpa only [sub_zero] using this
  have hEp : ∀ τ ∈ Set.Icc (0 : ℝ) t,
      Cx.cP * ‖l2c3_y R t F (fun _ _ => 0) τ‖ ^ 2 ≤ l2c3_E1 R t F τ := by
    intro τ hτ
    rw [← l2c3_Ev_zero]
    exact (hC τ hτ).2
  have hFnn : ∀ τ ∈ Set.Icc (0 : ℝ) t, 0 ≤ l2c3_Fv Cx t F (fun _ _ => 0) τ := by
    intro τ _
    have h1 := (Cx.hform (l2c3_y R t F (fun _ _ => 0) τ)).1
    have h0 : 0 ≤ ‖l2c3_y R t F (fun _ _ => 0) τ‖ ^ 2 := sq_nonneg _
    by_contra h
    push Not at h
    unfold l2c3_Fv at h
    nlinarith [mul_neg_of_pos_of_neg hκ₁ h]
  choose! f hf using hB
  -- the pointwise differential inequality
  have hpw : ∀ σ ∈ Set.Ioo (0 : ℝ) t, f σ ≤ -R.β⁻¹ * l2c3_E1 R t F σ +
      Cc * Real.exp (-2 * κ * (t - σ)) * l2c3_Fv Cx t F (fun _ _ => 0) σ := by
    intro σ hσ
    have hσ' : σ ∈ Set.Icc (0 : ℝ) t := Set.Ioo_subset_Icc_self hσ
    have hb := (hf σ hσ).2
    rw [l2c3_Ev_zero] at hb
    have hF1 : Torus.IsCk 1 (F (t - σ)) := l2c3_isCk_of_smooth (hFs _ (hmem σ hσ')) 1
    have h := l2c3_pw1 (ν := R.β⁻¹) (c0 := Cx.c₀) (κ1 := Cx.κ₁) hν hc₀ hκ₁ hCm
      (Real.exp_pos (-κ * (t - σ))).le hb (l2c3_Nn_le R Cx hF1)
      (Cx.hform (l2c3_y R t F (fun _ _ => 0) σ)).1 (l2c3_Nn_nonneg R t F σ)
    have he : Real.exp (-κ * (t - σ)) ^ 2 = Real.exp (-2 * κ * (t - σ)) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [he] at h
    exact h
  have hpw2 : ∀ σ ∈ Set.Ioo (0 : ℝ) t, f σ ≤
      (-a + Cc * Real.exp (-2 * κ * (t - σ))) * l2c3_Fv Cx t F (fun _ _ => 0) σ := by
    intro σ hσ
    have hσ' : σ ∈ Set.Icc (0 : ℝ) t := Set.Ioo_subset_Icc_self hσ
    have h1 := hpw σ hσ
    have h2 := hEp σ hσ'
    have h3 : l2c3_Fv Cx t F (fun _ _ => 0) σ ≤ Cx.κ₂ * ‖l2c3_y R t F (fun _ _ => 0) σ‖ ^ 2 :=
      (Cx.hform _).2
    have h4 : a * l2c3_Fv Cx t F (fun _ _ => 0) σ ≤ R.β⁻¹ * l2c3_E1 R t F σ := by
      calc a * l2c3_Fv Cx t F (fun _ _ => 0) σ
          ≤ a * (Cx.κ₂ * ‖l2c3_y R t F (fun _ _ => 0) σ‖ ^ 2) := mul_le_mul_of_nonneg_left h3 ha.le
        _ = R.β⁻¹ * (Cx.cP * ‖l2c3_y R t F (fun _ _ => 0) σ‖ ^ 2) := by
          rw [← mul_assoc, l2c3_rate_mul]; ring
        _ ≤ R.β⁻¹ * l2c3_E1 R t F σ := mul_le_mul_of_nonneg_left h2 hν.le
    have h5 : (-a + Cc * Real.exp (-2 * κ * (t - σ))) * l2c3_Fv Cx t F (fun _ _ => 0) σ =
        -(a * l2c3_Fv Cx t F (fun _ _ => 0) σ) +
          Cc * Real.exp (-2 * κ * (t - σ)) * l2c3_Fv Cx t F (fun _ _ => 0) σ := by ring
    rw [h5]
    linarith
  have hpw3 : ∀ σ ∈ Set.Ioo (0 : ℝ) t, f σ ≤
      -R.β⁻¹ * l2c3_E1 R t F σ + Cc * l2c3_Fv Cx t F (fun _ _ => 0) σ := by
    intro σ hσ
    have hσ' : σ ∈ Set.Icc (0 : ℝ) t := Set.Ioo_subset_Icc_self hσ
    have h1 := hpw σ hσ
    have h2 : Real.exp (-2 * κ * (t - σ)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ t - σ := by linarith [hσ.2]
      nlinarith
    have h3 := hFnn σ hσ'
    have : Cc * Real.exp (-2 * κ * (t - σ)) * l2c3_Fv Cx t F (fun _ _ => 0) σ ≤
        Cc * l2c3_Fv Cx t F (fun _ _ => 0) σ := by
      have := mul_le_mul_of_nonneg_left h2 hCc0
      nlinarith [mul_le_mul_of_nonneg_right this h3]
    linarith
  have hd : ∀ σ ∈ Set.Ioo (0 : ℝ) t, HasDerivAt (l2c3_Fv Cx t F (fun _ _ => 0)) (f σ) σ :=
    fun σ hσ => (hf σ hσ).1
  -- initial value
  have hF0 : l2c3_Fv Cx t F (fun _ _ => 0) 0 ≤ Cx.κ₂ * (Cx.Λ₀ * PDE.l2NormSq
      (projMean (withDensityReal R.ρβ) φ)) := by
    have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) t := ⟨le_rfl, ht.le⟩
    have h1 : l2c3_Fv Cx t F (fun _ _ => 0) 0 ≤ Cx.κ₂ * ‖l2c3_y R t F (fun _ _ => 0) 0‖ ^ 2 :=
      (Cx.hform _).2
    have h2 := hy2 0 h0
    rw [sub_zero, hF.terminal] at h2
    have h3 := (HRS.MC.L2C1.l2c1_l2Inner_bounds Cx.hprob Cx.hρc Cx.hlow' Cx.hup
      (f := projMean (withDensityReal R.ρβ) φ) (by
        have := hQc 0 h0
        rwa [sub_zero, hF.terminal] at this)).2
    rw [h2] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left h3 hκ₂.le)
  have hQ0 : 0 ≤ PDE.l2NormSq (projMean (withDensityReal R.ρβ) φ) :=
    integral_nonneg fun x => sq_nonneg _
  have hFv0nn := hFnn 0 ⟨le_rfl, ht.le⟩
  -- decay of `Fv`
  have hgron : ∀ τ ∈ Set.Icc (0 : ℝ) t, l2c3_Fv Cx t F (fun _ _ => 0) τ ≤
      G * Real.exp (-a * τ) * l2c3_Fv Cx t F (fun _ _ => 0) 0 := fun τ hτ =>
    l2c3_gronwall_rate ht.le le_rfl hCc0 hκ hA hd hpw2 hFv0nn hτ
  refine ⟨fun τ hτ => ?_, fun τ hτ => ?_⟩
  · -- conjunct (1)
    have hb := (HRS.MC.L2C1.l2c1_l2Inner_bounds Cx.hprob Cx.hρc Cx.hlow' Cx.hup (hQc τ hτ)).1
    have hyτ : ‖l2c3_y R t F (fun _ _ => 0) τ‖ ^ 2 ≤ Cx.κ₁ * l2c3_Fv Cx t F (fun _ _ => 0) τ :=
      (Cx.hform _).1
    have hexp : 0 < Real.exp (-a * τ) := Real.exp_pos _
    have step1 : Cx.c₀ * PDE.l2NormSq (projMean (withDensityReal R.ρβ) (F (t - τ))) ≤
        Cx.κ₁ * (G * Real.exp (-a * τ) * l2c3_Fv Cx t F (fun _ _ => 0) 0) := by
      have := hy2 τ hτ
      unfold PDE.l2NormSq
      calc Cx.c₀ * ∫ x, projMean (withDensityReal R.ρβ) (F (t - τ)) x ^ 2
          ≤ l2Inner (withDensityReal R.ρβ) (projMean (withDensityReal R.ρβ) (F (t - τ)))
              (projMean (withDensityReal R.ρβ) (F (t - τ))) := hb
        _ = ‖l2c3_y R t F (fun _ _ => 0) τ‖ ^ 2 := this.symm
        _ ≤ Cx.κ₁ * l2c3_Fv Cx t F (fun _ _ => 0) τ := hyτ
        _ ≤ Cx.κ₁ * (G * Real.exp (-a * τ) * l2c3_Fv Cx t F (fun _ _ => 0) 0) :=
          mul_le_mul_of_nonneg_left (hgron τ hτ) hκ₁.le
    have step2 : G * Real.exp (-a * τ) * l2c3_Fv Cx t F (fun _ _ => 0) 0 ≤
        G * Real.exp (-a * τ) * (Cx.κ₂ * (Cx.Λ₀ * PDE.l2NormSq (projMean (withDensityReal R.ρβ) φ))) :=
      mul_le_mul_of_nonneg_left hF0 (by positivity)
    have step3 := le_trans step1 (mul_le_mul_of_nonneg_left step2 hκ₁.le)
    have hinv : Cx.c₀⁻¹ * Cx.c₀ = 1 := inv_mul_cancel₀ hc₀.ne'
    have step4 : PDE.l2NormSq (projMean (withDensityReal R.ρβ) (F (t - τ))) ≤
        Cx.c₀⁻¹ * (Cx.κ₁ * (G * Real.exp (-a * τ) * (Cx.κ₂ * (Cx.Λ₀ *
          PDE.l2NormSq (projMean (withDensityReal R.ρβ) φ))))) := by
      have := mul_le_mul_of_nonneg_left step3 (inv_nonneg.2 hc₀.le)
      rwa [← mul_assoc, hinv, one_mul] at this
    calc _ ≤ _ := step4
      _ = _ := by ring
  · -- conjunct (2)
    have hτt : τ ≤ t := hτ.2
    have hmono := l2c3_weighted_energy (a' := a / 2) (b := Cc) (ν := R.β⁻¹) ht.le hA
      (l2c3_E1_cont R Cx hF) hd hpw3 hFnn hτ
    -- bound of the weighted integral of `Fv`
    have hint : ∫ σ in (0 : ℝ)..τ, Real.exp (a / 2 * σ) * l2c3_Fv Cx t F (fun _ _ => 0) σ ≤
        G * l2c3_Fv Cx t F (fun _ _ => 0) 0 * (1 / (a / 2)) := by
      have hcont : ContinuousOn (fun σ => Real.exp (a / 2 * σ) * l2c3_Fv Cx t F (fun _ _ => 0) σ)
          (Set.Icc 0 τ) :=
        (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul
          (hA.mono (Set.Icc_subset_Icc le_rfl hτt))
      have hle : ∫ σ in (0 : ℝ)..τ, Real.exp (a / 2 * σ) * l2c3_Fv Cx t F (fun _ _ => 0) σ ≤
          ∫ σ in (0 : ℝ)..τ, G * l2c3_Fv Cx t F (fun _ _ => 0) 0 * Real.exp (-(a / 2) * σ) := by
        refine intervalIntegral.integral_mono_on hτ.1
          (by rw [intervalIntegrable_iff_integrableOn_Icc_of_le hτ.1]
              exact hcont.integrableOn_Icc)
          ((continuous_const.mul (Real.continuous_exp.comp
            (continuous_const.mul continuous_id))).intervalIntegrable _ _) fun σ hσ => ?_
        have hσt : σ ∈ Set.Icc (0 : ℝ) t := ⟨hσ.1, hσ.2.trans hτt⟩
        have h1 := mul_le_mul_of_nonneg_left (hgron σ hσt) (Real.exp_pos (a / 2 * σ)).le
        have h2 : Real.exp (a / 2 * σ) * (G * Real.exp (-a * σ) * l2c3_Fv Cx t F (fun _ _ => 0) 0) =
            G * l2c3_Fv Cx t F (fun _ _ => 0) 0 * Real.exp (-(a / 2) * σ) := by
          have : Real.exp (a / 2 * σ) * Real.exp (-a * σ) = Real.exp (-(a / 2) * σ) := by
            rw [← Real.exp_add]; congr 1; ring
          calc _ = G * l2c3_Fv Cx t F (fun _ _ => 0) 0 *
                (Real.exp (a / 2 * σ) * Real.exp (-a * σ)) := by ring
            _ = _ := by rw [this]
        linarith
      rw [intervalIntegral.integral_const_mul] at hle
      have := l2c3_int_exp_le (b := a / 2) hτ.1 (by positivity)
      have h0 : 0 ≤ G * l2c3_Fv Cx t F (fun _ _ => 0) 0 := by positivity
      exact hle.trans (mul_le_mul_of_nonneg_left this h0)
    have hFv0 := hF0
    have hpos : 0 ≤ a / 2 + Cc := by positivity
    have h1 : R.β⁻¹ * ∫ σ in (0 : ℝ)..τ, Real.exp (a / 2 * σ) * l2c3_E1 R t F σ ≤
        l2c3_Fv Cx t F (fun _ _ => 0) 0 * (1 + (a / 2 + Cc) * G / (a / 2)) := by
      have h2 := mul_le_mul_of_nonneg_left hint hpos
      have h3 : (a / 2 + Cc) * (G * l2c3_Fv Cx t F (fun _ _ => 0) 0 * (1 / (a / 2))) =
          l2c3_Fv Cx t F (fun _ _ => 0) 0 * ((a / 2 + Cc) * G / (a / 2)) := by
        field_simp
      have h4 := hmono
      nlinarith
    have h5 : l2c3_Fv Cx t F (fun _ _ => 0) 0 * (1 + (a / 2 + Cc) * G / (a / 2)) ≤
        (Cx.κ₂ * (Cx.Λ₀ * PDE.l2NormSq (projMean (withDensityReal R.ρβ) φ))) *
          (1 + (a / 2 + Cc) * G / (a / 2)) :=
      mul_le_mul_of_nonneg_right hF0 (by positivity)
    calc _ ≤ _ := h1.trans h5
      _ = _ := by ring

end HRS.MC.L2C3
