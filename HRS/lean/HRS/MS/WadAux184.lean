import HRS.MS.WadAux183

/-!
# S8.3, packet S8H2-10: linearity of the projected generator on the weighted `C^2` class (continued)
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8h2_gen_pt (hd : 2 ≤ d) {a β M : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) (hM : 0 ≤ M) :
    ∃ C1 : ℝ, 0 ≤ C1 ∧ ∀ {g : Euc d → ℝ} {V W : ℝ}, 0 ≤ V → 0 ≤ W → S8hCls M V W g → ∀ x,
      |generatorW (critCoeff d a β ρβ) 0 g x| ≤ C1 * (V + W) * (jbracket x ^ M * (1 + ‖x‖)) := by
  have hP : HRS.Whole.IsProbDensity ρβ := hρ.1.1
  have hgr : s84_GaussReg ρβ := s84_thermal_gaussReg hd ha hβ hρ
  obtain ⟨CB, hCB0, hCB⟩ := s84_B_bound hd hgr hM
  have hi1 : Integrable (fun y : Euc d => jbracket y ^ M) (HRS.Whole.withDensityReal ρβ) :=
    s85_jb_integrable hP hgr hM
  have hi2 : Integrable (fun y : Euc d => jbracket y ^ (M + 1)) (HRS.Whole.withDensityReal ρβ) :=
    s85_jb_integrable hP hgr (by linarith)
  set m1 : ℝ := ∫ y, jbracket y ^ M ∂(HRS.Whole.withDensityReal ρβ) with hm1
  set m2 : ℝ := ∫ y, jbracket y ^ (M + 1) ∂(HRS.Whole.withDensityReal ρβ) with hm2
  have hm10 : 0 ≤ m1 := integral_nonneg fun y => Real.rpow_nonneg (s83_jb_pos y).le _
  have hm20 : 0 ≤ m2 := integral_nonneg fun y => Real.rpow_nonneg (s83_jb_pos y).le _
  set C1 : ℝ := β⁻¹ * d + |a| + CB * (1 + 2 ^ M) with hC1
  have hC10 : 0 ≤ C1 := by positivity
  refine ⟨C1, hC10, fun {g} {V W} hV hW hcls x => ?_⟩
  obtain ⟨hg, hDg, hD2g⟩ := hcls
  have h2M : 0 ≤ (2 : ℝ) ^ M := Real.rpow_nonneg (by norm_num) M
  -- pointwise bound of the generator
  have hpt : ∀ x : Euc d, |generatorW (critCoeff d a β ρβ) 0 g x| ≤
      C1 * (V + W) * (jbracket x ^ M * (1 + ‖x‖)) := by
    intro x
    rw [s84_generator_decomp]
    have hjx := Real.rpow_nonneg (s83_jb_pos x).le M
    have hn1 : 1 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
    have hHolder : ∀ x x' : Euc d, ‖x' - x‖ ≤ 1 / 4 →
        ‖fderiv ℝ g x' - fderiv ℝ g x‖ ≤ (W * 2 ^ M) * ‖x' - x‖ ^ (1 / 2 : ℝ) * jbracket x ^ M := by
      intro x x' hxx
      have hdiff : Differentiable ℝ (fderiv ℝ g) :=
        (hg.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
      have hjx0 := Real.rpow_nonneg (s83_jb_pos x).le M
      have hb : ∀ z ∈ Metric.closedBall x ‖x' - x‖, ‖fderiv ℝ (fderiv ℝ g) z‖ ≤ W * 2 ^ M * jbracket x ^ M := by
        intro z hz
        have hz' : ‖z - x‖ ≤ ‖x' - x‖ := mem_closedBall_iff_norm.1 hz
        have h1 : jbracket z ≤ 2 * jbracket x := by
          have := s83_jb_lipschitz z x
          have h2 := abs_le.1 this
          have h3 := s83_one_le_jb x
          linarith [h2.2]
        have h4 : jbracket z ^ M ≤ (2 * jbracket x) ^ M :=
          Real.rpow_le_rpow (s83_jb_pos z).le h1 hM
        rw [Real.mul_rpow (by norm_num) (s83_jb_pos x).le] at h4
        calc ‖fderiv ℝ (fderiv ℝ g) z‖ ≤ W * jbracket z ^ M := hD2g z
          _ ≤ W * (2 ^ M * jbracket x ^ M) := mul_le_mul_of_nonneg_left h4 hW
          _ = _ := by ring
      have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := fderiv ℝ g)
        (C := W * 2 ^ M * jbracket x ^ M) (s := Metric.closedBall x ‖x' - x‖) (fun y _ => hdiff y) hb
        (convex_closedBall _ _) (mem_closedBall_self (norm_nonneg _)) (x := x) (y := x')
        (by rw [mem_closedBall_iff_norm, norm_sub_rev])
      have hr : ‖x' - x‖ ≤ ‖x' - x‖ ^ (1 / 2 : ℝ) := by
        by_cases h0 : ‖x' - x‖ = 0
        · rw [h0]; simp
        · have hpos : 0 < ‖x' - x‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
          have hs : ‖x' - x‖ ^ (1 / 2 : ℝ) * ‖x' - x‖ ^ (1 / 2 : ℝ) = ‖x' - x‖ := by
            rw [← Real.rpow_add hpos]; norm_num
          have hs1 : ‖x' - x‖ ^ (1 / 2 : ℝ) ≤ 1 := by
            have : ‖x' - x‖ ^ (1 / 2 : ℝ) ≤ (1 : ℝ) ^ (1 / 2 : ℝ) :=
              Real.rpow_le_rpow (norm_nonneg _) (by linarith) (by norm_num)
            simpa using this
          nlinarith [Real.rpow_nonneg (norm_nonneg (x' - x)) (1 / 2 : ℝ)]
      calc ‖fderiv ℝ g x' - fderiv ℝ g x‖ ≤ W * 2 ^ M * jbracket x ^ M * ‖x' - x‖ := hmv
        _ ≤ W * 2 ^ M * jbracket x ^ M * ‖x' - x‖ ^ (1 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_left hr (mul_nonneg (mul_nonneg hW h2M) hjx0)
        _ = _ := by ring
    have hB := hCB hV (mul_nonneg hW h2M) hDg hHolder x
    unfold s83_L0
    have e1 : |β⁻¹ * s83_lap g x| ≤ β⁻¹ * (d * (W * jbracket x ^ M)) := by
      rw [abs_mul, abs_of_pos (inv_pos.2 hβ)]
      exact mul_le_mul_of_nonneg_left ((s8g_lap_pt g x).trans
        (mul_le_mul_of_nonneg_left (hD2g x) (Nat.cast_nonneg d))) (inv_pos.2 hβ).le
    have e2 : |a * fderiv ℝ g x x| ≤ |a| * (V * jbracket x ^ M * ‖x‖) := by
      rw [abs_mul]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rw [← Real.norm_eq_abs]
      exact ((fderiv ℝ g x).le_opNorm x).trans (mul_le_mul_of_nonneg_right (hDg x) (norm_nonneg _))
    have hxn := norm_nonneg x
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    calc |β⁻¹ * s83_lap g x - a * fderiv ℝ g x x + s84_Bop ρβ g x|
        ≤ |β⁻¹ * s83_lap g x - a * fderiv ℝ g x x| + |s84_Bop ρβ g x| := abs_add_le _ _
      _ ≤ |β⁻¹ * s83_lap g x| + |a * fderiv ℝ g x x| + |s84_Bop ρβ g x| := by
          have := abs_sub (β⁻¹ * s83_lap g x) (a * fderiv ℝ g x x)
          linarith
      _ ≤ β⁻¹ * (d * (W * jbracket x ^ M)) + |a| * (V * jbracket x ^ M * ‖x‖) +
            CB * (V + W * 2 ^ M) * jbracket x ^ M := by linarith
      _ ≤ C1 * (V + W) * (jbracket x ^ M * (1 + ‖x‖)) := by
          have hVW : W * 2 ^ M ≤ W * 2 ^ M := le_rfl
          have t1 : β⁻¹ * (d * (W * jbracket x ^ M)) ≤ β⁻¹ * d * (V + W) * (jbracket x ^ M * (1 + ‖x‖)) := by
            have : W * jbracket x ^ M ≤ (V + W) * (jbracket x ^ M * (1 + ‖x‖)) := by
              nlinarith [mul_nonneg hV hjx, mul_nonneg hW hjx, mul_nonneg (mul_nonneg hW hjx) hxn,
                mul_nonneg (mul_nonneg hV hjx) hxn]
            have h5 : 0 ≤ β⁻¹ * d := mul_nonneg (inv_pos.2 hβ).le hd0
            calc β⁻¹ * (d * (W * jbracket x ^ M)) = β⁻¹ * d * (W * jbracket x ^ M) := by ring
              _ ≤ β⁻¹ * d * ((V + W) * (jbracket x ^ M * (1 + ‖x‖))) := mul_le_mul_of_nonneg_left this h5
              _ = _ := by ring
          have t2 : |a| * (V * jbracket x ^ M * ‖x‖) ≤ |a| * (V + W) * (jbracket x ^ M * (1 + ‖x‖)) := by
            have : V * jbracket x ^ M * ‖x‖ ≤ (V + W) * (jbracket x ^ M * (1 + ‖x‖)) := by
              nlinarith [mul_nonneg hV hjx, mul_nonneg hW hjx, mul_nonneg (mul_nonneg hW hjx) hxn,
                mul_nonneg (mul_nonneg hV hjx) hxn]
            calc |a| * (V * jbracket x ^ M * ‖x‖) ≤ |a| * ((V + W) * (jbracket x ^ M * (1 + ‖x‖))) :=
                  mul_le_mul_of_nonneg_left this (abs_nonneg _)
              _ = _ := by ring
          have t3 : CB * (V + W * 2 ^ M) * jbracket x ^ M ≤ CB * (1 + 2 ^ M) * (V + W) * (jbracket x ^ M * (1 + ‖x‖)) := by
            have h6 : V + W * 2 ^ M ≤ (1 + 2 ^ M) * (V + W) := by
              nlinarith [mul_nonneg hV h2M, mul_nonneg hW h2M]
            have h7 : jbracket x ^ M ≤ jbracket x ^ M * (1 + ‖x‖) := by nlinarith
            calc CB * (V + W * 2 ^ M) * jbracket x ^ M ≤ CB * ((1 + 2 ^ M) * (V + W)) * (jbracket x ^ M * (1 + ‖x‖)) := by
                  refine mul_le_mul (mul_le_mul_of_nonneg_left h6 hCB0) h7 hjx
                    (mul_nonneg hCB0 (mul_nonneg (by positivity) (add_nonneg hV hW)))
              _ = _ := by ring
          calc _ ≤ β⁻¹ * d * (V + W) * (jbracket x ^ M * (1 + ‖x‖)) + |a| * (V + W) * (jbracket x ^ M * (1 + ‖x‖)) +
                CB * (1 + 2 ^ M) * (V + W) * (jbracket x ^ M * (1 + ‖x‖)) := by linarith
            _ = _ := by rw [hC1]; ring
  exact hpt x

theorem s8h2_conv_meas {G : Euc d → Euc d} (hG : Measurable G) {φ : Euc d → ℝ} (hφ : Measurable φ) :
    Measurable (convGradConvW G φ) := by
  unfold convGradConvW
  have hF : Measurable (fun p : Euc d × Euc d => if ‖p.1 - p.2‖ ≤ 1 / 4 then (φ p.2 - φ p.1) • G (p.1 - p.2)
      else φ p.2 • G (p.1 - p.2)) := by
    refine Measurable.ite (measurableSet_le (measurable_fst.sub measurable_snd).norm measurable_const) ?_ ?_
    · exact ((hφ.comp measurable_snd).sub (hφ.comp measurable_fst)).smul (hG.comp (measurable_fst.sub measurable_snd))
    · exact (hφ.comp measurable_snd).smul (hG.comp (measurable_fst.sub measurable_snd))
  exact (hF.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

theorem s8h2_gen_meas {a β : ℝ} {ρβ : Euc d → ℝ} (hρd : Differentiable ℝ ρβ) {g : Euc d → ℝ}
    (hg : ContDiff ℝ 2 g) : Measurable (generatorW (critCoeff d a β ρβ) 0 g) := by
  have hgc : Continuous (gradient g) := by
    have : gradient g = fun y => (InnerProductSpace.toDual ℝ (Euc d)).symm (fderiv ℝ g y) := rfl
    rw [this]
    exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp (hg.continuous_fderiv (by norm_num))
  have hK : Measurable (rieszKernelGrad d ((d : ℝ) / 2)) := movtr_rieszKernelGrad_measurable _
  have hb0 : Measurable (convGradConvW (rieszKernelGrad d ((d : ℝ) / 2)) ρβ) :=
    s8h2_conv_meas hK hρd.continuous.measurable
  have hu : ∀ j : Fin d, Measurable (fun y => ρβ y *
      (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose (gradient g y)) j) := fun j => by
    refine hρd.continuous.measurable.mul ?_
    simp only [s84_matVec_neg_T]
    exact ((EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).continuous.comp hgc.neg).measurable
  have e : generatorW (critCoeff d a β ρβ) 0 g = fun y => s83_L0 a β⁻¹ g y + s84_Bop ρβ g y := by
    funext y; exact s84_generator_decomp a β ρβ 0 g y
  rw [e]
  refine Measurable.add ?_ ?_
  · unfold s83_L0
    have h1 : Continuous (fun y => β⁻¹ * s83_lap g y - a * fderiv ℝ g y y) :=
      (continuous_const.mul (s83_lap_continuous hg)).sub
        (continuous_const.mul ((hg.continuous_fderiv (by norm_num)).clm_apply continuous_id))
    exact h1.measurable
  · unfold s84_Bop
    refine Measurable.sub ?_ ?_
    · simp only [s84_matVec_neg]
      exact (hb0.neg).inner hgc.measurable
    · refine Finset.measurable_sum _ fun j _ => ?_
      exact ((EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).continuous.measurable.comp
        (s8h2_conv_meas hK (hu j)))

theorem s8h2_gen_integrable (hd : 2 ≤ d) {a β M : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) (hM : 0 ≤ M) {g : Euc d → ℝ} {V W : ℝ}
    (hV : 0 ≤ V) (hW : 0 ≤ W) (hcls : S8hCls M V W g) :
    Integrable (generatorW (critCoeff d a β ρβ) 0 g) (HRS.Whole.withDensityReal ρβ) := by
  have hP : HRS.Whole.IsProbDensity ρβ := hρ.1.1
  have hgr : s84_GaussReg ρβ := s84_thermal_gaussReg hd ha hβ hρ
  obtain ⟨C1, hC10, hC1⟩ := s8h2_gen_pt hd ha hβ hρ hM
  have hi1 : Integrable (fun y : Euc d => jbracket y ^ M) (HRS.Whole.withDensityReal ρβ) :=
    s85_jb_integrable hP hgr hM
  have hi2 : Integrable (fun y : Euc d => jbracket y ^ (M + 1)) (HRS.Whole.withDensityReal ρβ) :=
    s85_jb_integrable hP hgr (by linarith)
  have hpt2 : ∀ y : Euc d, jbracket y ^ M * (1 + ‖y‖) ≤ jbracket y ^ M + jbracket y ^ (M + 1) := by
    intro y
    have hjy := Real.rpow_nonneg (s83_jb_pos y).le M
    have e : jbracket y ^ (M + 1) = jbracket y ^ M * jbracket y := by
      rw [Real.rpow_add (s83_jb_pos y), Real.rpow_one]
    rw [e]
    have := s83_norm_le_jb y
    nlinarith
  have hVW : 0 ≤ C1 * (V + W) := by positivity
  refine Integrable.mono' ((hi1.add hi2).const_mul (C1 * (V + W)))
    (s8h2_gen_meas hgr.1 hcls.1).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs]
  exact (hC1 hV hW hcls y).trans (mul_le_mul_of_nonneg_left (hpt2 y) hVW)

theorem s8h2_L0_sub {a ν : ℝ} {g₁ g₂ : Euc d → ℝ} (h₁ : ContDiff ℝ 2 g₁) (h₂ : ContDiff ℝ 2 g₂) (y : Euc d) :
    s83_L0 a ν (fun y => g₁ y - g₂ y) y = s83_L0 a ν g₁ y - s83_L0 a ν g₂ y := by
  have d1 : Differentiable ℝ g₁ := h₁.differentiable (by norm_num)
  have d2 : Differentiable ℝ g₂ := h₂.differentiable (by norm_num)
  have hf1 : fderiv ℝ (fun y => g₁ y - g₂ y) = fun y => fderiv ℝ g₁ y - fderiv ℝ g₂ y :=
    funext fun y => fderiv_sub (d1 y) (d2 y)
  have dd1 : Differentiable ℝ (fderiv ℝ g₁) := (h₁.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have dd2 : Differentiable ℝ (fderiv ℝ g₂) := (h₂.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have hf2 : fderiv ℝ (fderiv ℝ (fun y => g₁ y - g₂ y)) y =
      fderiv ℝ (fderiv ℝ g₁) y - fderiv ℝ (fderiv ℝ g₂) y := by
    rw [hf1]; exact fderiv_sub (dd1 y) (dd2 y)
  unfold s83_L0 s83_lap
  rw [hf2, hf1]
  simp only [ContinuousLinearMap.sub_apply, Finset.sum_sub_distrib]
  ring

theorem s8h2_Bop_sub (hd : 2 ≤ d) {ρ : Euc d → ℝ} (hρ : s84_GaussReg ρ) {M : ℝ} (hM : 0 ≤ M)
    {h₁ h₂ : Euc d → ℝ} {V₁ W₁ V₂ W₂ : ℝ} (hV₁ : 0 ≤ V₁) (hW₁ : 0 ≤ W₁) (hV₂ : 0 ≤ V₂) (hW₂ : 0 ≤ W₂)
    (h1 : S8hCls M V₁ W₁ h₁) (h2 : S8hCls M V₂ W₂ h₂) (x : Euc d) :
    s84_Bop ρ (fun y => h₁ y - h₂ y) x = s84_Bop ρ h₁ x - s84_Bop ρ h₂ x := by
  obtain ⟨Lu, hLu0, hLu⟩ := s8h2_u_facts hd hρ hM
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : (0 : ℝ) < (d : ℝ) / 2 := by positivity
  have hs1 : (d : ℝ) / 2 + 1 / 2 < (d : ℝ) := by linarith
  have dd1 : Differentiable ℝ h₁ := h1.1.differentiable (by norm_num)
  have dd2 : Differentiable ℝ h₂ := h2.1.differentiable (by norm_num)
  unfold s84_Bop
  have e1 : inner ℝ (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ)
      (convGradConvW (rieszKernelGrad d ((d : ℝ) / 2)) ρ x)) (gradient (fun y => h₁ y - h₂ y) x) =
      inner ℝ (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ)
        (convGradConvW (rieszKernelGrad d ((d : ℝ) / 2)) ρ x)) (gradient h₁ x) -
      inner ℝ (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ)
        (convGradConvW (rieszKernelGrad d ((d : ℝ) / 2)) ρ x)) (gradient h₂ x) := by
    rw [s84_gradient_sub dd1 dd2, inner_sub_right]
  have e2 : ∀ j : Fin d, (convGradConvW (rieszKernelGrad d ((d : ℝ) / 2))
      (fun y => ρ y * (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose
        (gradient (fun y => h₁ y - h₂ y) y)) j) x) j =
      (convGradConvW (rieszKernelGrad d ((d : ℝ) / 2))
        (fun y => ρ y * (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose (gradient h₁ y)) j) x) j -
      (convGradConvW (rieszKernelGrad d ((d : ℝ) / 2))
        (fun y => ρ y * (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose (gradient h₂ y)) j) x) j := by
    intro j
    obtain ⟨m1, a1, hh1⟩ := hLu hV₁ hW₁ h1 j
    obtain ⟨m2, a2, hh2⟩ := hLu hV₂ hW₂ h2 j
    have hi1 := s84_conv_integrable hd hs0 hs1 (mul_nonneg hLu0 (add_nonneg hV₁ hW₁))
      (mul_nonneg hLu0 (add_nonneg hV₁ hW₁)) m1 a1 hh1 x
    have hi2 := s84_conv_integrable hd hs0 hs1 (mul_nonneg hLu0 (add_nonneg hV₂ hW₂))
      (mul_nonneg hLu0 (add_nonneg hV₂ hW₂)) m2 a2 hh2 x
    have hfun : (fun y => ρ y * (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose
        (gradient (fun y => h₁ y - h₂ y) y)) j) =
        (fun y => ρ y * (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose (gradient h₁ y)) j -
          ρ y * (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose (gradient h₂ y)) j) := by
      funext y
      rw [s84_gradient_sub dd1 dd2, s84_matVec_neg_T, s84_matVec_neg_T, s84_matVec_neg_T]
      simp only [PiLp.neg_apply, PiLp.sub_apply]
      ring
    rw [hfun, s84_conv_sub (u₁ := fun y => ρ y * (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose
        (gradient h₁ y)) j) (u₂ := fun y => ρ y * (Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ).transpose
        (gradient h₂ y)) j) x hi1 hi2, PiLp.sub_apply]
  rw [e1, Finset.sum_congr rfl fun j _ => e2 j, Finset.sum_sub_distrib]
  ring

theorem s8h2_proj_sub (hd : 2 ≤ d) {a β M : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) (hM : 0 ≤ M) {g₁ g₂ : Euc d → ℝ}
    {V₁ W₁ V₂ W₂ : ℝ} (hV₁ : 0 ≤ V₁) (hW₁ : 0 ≤ W₁) (hV₂ : 0 ≤ V₂) (hW₂ : 0 ≤ W₂)
    (h1 : S8hCls M V₁ W₁ g₁) (h2 : S8hCls M V₂ W₂ g₂) (x : Euc d) :
    projGeneratorW (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) 0 (fun y => g₁ y - g₂ y) x =
      projGeneratorW (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) 0 g₁ x -
      projGeneratorW (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) 0 g₂ x := by
  have hgr : s84_GaussReg ρβ := s84_thermal_gaussReg hd ha hβ hρ
  have hgen : ∀ y, generatorW (critCoeff d a β ρβ) 0 (fun y => g₁ y - g₂ y) y =
      generatorW (critCoeff d a β ρβ) 0 g₁ y - generatorW (critCoeff d a β ρβ) 0 g₂ y := by
    intro y
    rw [s84_generator_decomp, s84_generator_decomp, s84_generator_decomp, s8h2_L0_sub h1.1 h2.1,
      s8h2_Bop_sub hd hgr hM hV₁ hW₁ hV₂ hW₂ h1 h2]
    ring
  unfold projGeneratorW
  simp only [hgen]
  rw [integral_sub (s8h2_gen_integrable hd ha hβ hρ hM hV₁ hW₁ h1)
    (s8h2_gen_integrable hd ha hβ hρ hM hV₂ hW₂ h2)]
  ring

theorem S8hCls.smul {M V W : ℝ} {g : Euc d → ℝ} (h : S8hCls M V W g) (c : ℝ) :
    S8hCls M (|c| * V) (|c| * W) (fun y => c * g y) := by
  refine ⟨contDiff_const.mul h.1, fun y => ?_, fun y => ?_⟩
  · have d1 : Differentiable ℝ g := h.1.differentiable (by norm_num)
    rw [fderiv_const_mul (d1 y) c, norm_smul, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h.2.1 y) (abs_nonneg c)
  · have d1 : Differentiable ℝ g := h.1.differentiable (by norm_num)
    have hf : fderiv ℝ (fun y => c * g y) = fun y => c • fderiv ℝ g y :=
      funext fun y => by rw [fderiv_const_mul (d1 y) c]
    have dd1 : Differentiable ℝ (fderiv ℝ g) :=
      (h.1.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
    have hh : fderiv ℝ (fun y => c • fderiv ℝ g y) y = c • fderiv ℝ (fderiv ℝ g) y :=
      ((dd1 y).hasFDerivAt.const_smul c).fderiv
    rw [hf, hh]
    refine (ContinuousLinearMap.opNorm_smul_le c _).trans ?_
    rw [Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left (h.2.2 y) (abs_nonneg c)

theorem S8hCls.add {M V₁ W₁ V₂ W₂ : ℝ} {g₁ g₂ : Euc d → ℝ} (h1 : S8hCls M V₁ W₁ g₁) (h2 : S8hCls M V₂ W₂ g₂) :
    S8hCls M (V₁ + V₂) (W₁ + W₂) (fun y => g₁ y + g₂ y) := by
  have d1 : Differentiable ℝ g₁ := h1.1.differentiable (by norm_num)
  have d2 : Differentiable ℝ g₂ := h2.1.differentiable (by norm_num)
  have dd1 : Differentiable ℝ (fderiv ℝ g₁) := (h1.1.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have dd2 : Differentiable ℝ (fderiv ℝ g₂) := (h2.1.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have hf : fderiv ℝ (fun y => g₁ y + g₂ y) = fun y => fderiv ℝ g₁ y + fderiv ℝ g₂ y :=
    funext fun y => fderiv_add (d1 y) (d2 y)
  refine ⟨h1.1.add h2.1, fun y => ?_, fun y => ?_⟩
  · rw [hf]
    refine (norm_add_le _ _).trans ?_
    have := add_le_add (h1.2.1 y) (h2.2.1 y)
    linarith
  · have hh : fderiv ℝ (fun y => fderiv ℝ g₁ y + fderiv ℝ g₂ y) y =
        fderiv ℝ (fderiv ℝ g₁) y + fderiv ℝ (fderiv ℝ g₂) y :=
      ((dd1 y).hasFDerivAt.add (dd2 y).hasFDerivAt).fderiv
    rw [hf, hh]
    refine (norm_add_le (fderiv ℝ (fderiv ℝ g₁) y) (fderiv ℝ (fderiv ℝ g₂) y)).trans ?_
    have := add_le_add (h1.2.2 y) (h2.2.2 y)
    linarith

theorem S8hCls.sum {M : ℝ} {ι : Type} (c : ι → ℝ) (g : ι → Euc d → ℝ) {V W : ι → ℝ} (s : Finset ι)
    (hcls : ∀ k ∈ s, S8hCls M (V k) (W k) (g k)) :
    S8hCls M (∑ k ∈ s, |c k| * V k) (∑ k ∈ s, |c k| * W k) (fun y => ∑ k ∈ s, c k * g k y) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨contDiff_const, fun y => by simp, fun y => by
      rw [show fderiv ℝ (fun _ : Euc d => (0 : ℝ)) = fun _ => 0 from fderiv_fun_const (0 : ℝ)]
      simp <;> exact (ContinuousLinearMap.opNorm_zero).le⟩
  | insert l s hl ih =>
    simp only [Finset.sum_insert hl]
    exact (S8hCls.smul (hcls l (Finset.mem_insert_self l s)) (c l)).add
      (ih fun k hk => hcls k (Finset.mem_insert_of_mem hk))

theorem s8h2_proj_smul (hd : 2 ≤ d) {a β : ℝ} {ρβ : Euc d → ℝ} {g : Euc d → ℝ} (hg : ContDiff ℝ 2 g) (c : ℝ)
    (x : Euc d) :
    projGeneratorW (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) 0 (fun y => c * g y) x =
      c * projGeneratorW (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) 0 g x := by
  have d1 : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hf : fderiv ℝ (fun y => c * g y) = fun y => c • fderiv ℝ g y :=
    funext fun y => by rw [fderiv_const_mul (d1 y) c]
  have dd1 : Differentiable ℝ (fderiv ℝ g) := (hg.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  have hgen : ∀ y, generatorW (critCoeff d a β ρβ) 0 (fun y => c * g y) y =
      c * generatorW (critCoeff d a β ρβ) 0 g y := by
    intro y
    rw [s84_generator_decomp, s84_generator_decomp, s85_Bop_smul d1 c y]
    have : s83_L0 a β⁻¹ (fun y => c * g y) y = c * s83_L0 a β⁻¹ g y := by
      unfold s83_L0 s83_lap
      have hh : fderiv ℝ (fun y => c • fderiv ℝ g y) y = c • fderiv ℝ (fderiv ℝ g) y :=
        ((dd1 y).hasFDerivAt.const_smul c).fderiv
      rw [hf, hh]
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, ← Finset.mul_sum]
      ring
    rw [this]; ring
  unfold projGeneratorW
  simp only [hgen, integral_const_mul]
  ring

theorem s8h2_proj_sum (hd : 2 ≤ d) {a β M : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) (hM : 0 ≤ M) {ι : Type} (c : ι → ℝ)
    (g : ι → Euc d → ℝ) (V W : ι → ℝ) (x : Euc d) (s : Finset ι) (hV : ∀ k ∈ s, 0 ≤ V k)
    (hW : ∀ k ∈ s, 0 ≤ W k) (hcls : ∀ k ∈ s, S8hCls M (V k) (W k) (g k)) :
    projGeneratorW (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) 0
        (fun y => ∑ k ∈ s, c k * g k y) x =
      ∑ k ∈ s, c k * projGeneratorW (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) 0 (g k) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have h0 := s8h2_proj_smul (a := a) (β := β) (ρβ := ρβ) hd (g := fun _ => (0 : ℝ)) contDiff_const 0 x
    simpa using h0
  | insert l s hl ih =>
    simp only [Finset.sum_insert hl]
    have hcl := S8hCls.sum c g s (fun k hk => hcls k (Finset.mem_insert_of_mem hk))
    have e : (fun y => c l * g l y + ∑ k ∈ s, c k * g k y) =
        fun y => (fun y => c l * g l y) y - (fun y => (-1 : ℝ) * ∑ k ∈ s, c k * g k y) y := by
      funext y; ring
    have hVl := hV l (Finset.mem_insert_self l s)
    have hWl := hW l (Finset.mem_insert_self l s)
    have hcll := hcls l (Finset.mem_insert_self l s)
    have hs0 : 0 ≤ ∑ k ∈ s, |c k| * V k :=
      Finset.sum_nonneg fun k hk => mul_nonneg (abs_nonneg _) (hV k (Finset.mem_insert_of_mem hk))
    have hs1 : 0 ≤ ∑ k ∈ s, |c k| * W k :=
      Finset.sum_nonneg fun k hk => mul_nonneg (abs_nonneg _) (hW k (Finset.mem_insert_of_mem hk))
    rw [e, s8h2_proj_sub hd ha hβ hρ hM (mul_nonneg (abs_nonneg _) hVl) (mul_nonneg (abs_nonneg _) hWl)
      (mul_nonneg (abs_nonneg _) hs0) (mul_nonneg (abs_nonneg _) hs1)
      (S8hCls.smul hcll (c l)) (S8hCls.smul hcl (-1)), s8h2_proj_smul hd hcl.1 (-1) x,
      s8h2_proj_smul hd hcll.1 (c l) x,
      ih (fun k hk => hV k (Finset.mem_insert_of_mem hk)) (fun k hk => hW k (Finset.mem_insert_of_mem hk))
        (fun k hk => hcls k (Finset.mem_insert_of_mem hk))]
    ring

end HRS.MS.Wad
