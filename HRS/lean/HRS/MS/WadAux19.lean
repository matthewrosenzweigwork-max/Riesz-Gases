import HRS.MS.WadAux18

/-!
# S8.3, packet D2^5 (Route A): Hölder-1/2 smoothing of the gradient of the Mehler semigroup

`s84_P_fderiv_holder`: there is `K = K(d, M, a, ν, T)` with, for `0 < τ ≤ T`, `g` continuous with
`|g| ≤ C⟨·⟩^M` and `‖x'-x‖ ≤ 1/4`,
`‖D P_τ g(x') - D P_τ g(x)‖ ≤ K C τ^{-3/4} ‖x'-x‖^{1/2} ⟨x⟩^M`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s84_G_clm_apply {F : Euc d → (Euc d →L[ℝ] ℝ)} {c σ : ℝ} {x : Euc d}
    (hint : Integrable (fun z : Euc d => F (c • x + σ • z)) (stdGaussian (Euc d))) (v : Euc d) :
    (s83_G c σ F x) v = s83_G c σ (fun y => F y v) x := by
  unfold s83_G
  exact ContinuousLinearMap.integral_apply hint v

theorem s84_inv_sqrt_mul (τ : ℝ) (hτ : 0 < τ) :
    (Real.sqrt τ)⁻¹ * (Real.sqrt (Real.sqrt τ))⁻¹ = τ ^ (-(3 / 4 : ℝ)) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hτ.le, ← Real.rpow_neg hτ.le,
    ← Real.rpow_neg hτ.le, ← Real.rpow_add hτ]
  norm_num

/-- **Lipschitz regime** for the derivative of a Gaussian average of a `C¹` function. -/
theorem s84_clm_lip {f : Euc d → ℝ} (hfC1 : ContDiff ℝ 1 f) {M C₁ C₂ : ℝ} (hM : 0 ≤ M)
    (hfw : Wt M C₁ f) (hfDw : Wt M C₂ (fderiv ℝ f)) {c σ σ₀ : ℝ} (hc : |c| ≤ 1) (hσ : |σ| ≤ σ₀)
    (hσ0 : σ ≠ 0) (x x' : Euc d) (hκ : (|c| / |σ|) * ‖x' - x‖ ≤ 1) :
    ‖fderiv ℝ (s83_G c σ f) x' - fderiv ℝ (s83_G c σ f) x‖ ≤
      C₂ * 2 ^ M * jbracket x ^ M * Real.sqrt (mom d (2 * M) σ₀) * (2 * ((|c| / |σ|) * ‖x' - x‖)) := by
  have hfDc : Continuous (fderiv ℝ f) := hfC1.continuous_fderiv one_ne_zero
  have hC₂ := hfDw.nonneg
  have hD : ∀ y, fderiv ℝ (s83_G c σ f) y = c • s83_G c σ (fderiv ℝ f) y := fun y =>
    (s83_G_hasFDerivAt hfC1 hM hfw hfDw hc hσ y).fderiv
  have hDint : ∀ y, Integrable (fun z : Euc d => fderiv ℝ f (c • y + σ • z)) (stdGaussian (Euc d)) :=
    fun y => s83_int_shift hfDc hM hfDw hσ y
  have hact : ∀ y v, fderiv ℝ (s83_G c σ f) y v = c * s83_G c σ (fun z => fderiv ℝ f z v) y := by
    intro y v
    rw [hD y, smul_apply, s84_G_clm_apply (hDint y) v, smul_eq_mul]
  have hκ0 : 0 ≤ (|c| / |σ|) * ‖x' - x‖ := by positivity
  have hexp : Real.exp (((|c| / |σ|) * ‖x' - x‖) ^ 2 / 2) ≤ 2 := by
    refine le_trans ?_ s83_exp_half_le
    apply Real.exp_le_exp.2
    have : ((|c| / |σ|) * ‖x' - x‖) ^ 2 ≤ 1 := by nlinarith
    linarith
  have hPm : 0 ≤ Real.sqrt (mom d (2 * M) σ₀) := Real.sqrt_nonneg _
  have hjb : 0 ≤ jbracket x ^ M := Real.rpow_nonneg (s83_jb_pos _).le _
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  have hv0 := norm_nonneg v
  have hgv : Continuous (fun z => fderiv ℝ f z v) := hfDc.clm_apply continuous_const
  have hwv : Wt M (C₂ * ‖v‖) (fun z => fderiv ℝ f z v) := fun z => by
    rw [Real.norm_eq_abs, ← Real.norm_eq_abs]
    calc ‖fderiv ℝ f z v‖ ≤ ‖fderiv ℝ f z‖ * ‖v‖ := (fderiv ℝ f z).le_opNorm v
      _ ≤ (C₂ * jbracket z ^ M) * ‖v‖ := mul_le_mul_of_nonneg_right (hfDw z) hv0
      _ = C₂ * ‖v‖ * jbracket z ^ M := by ring
  have lip := s83_G_lip hgv hM hwv hc hσ hσ0 x x'
  rw [sub_apply, hact x' v, hact x v, ← mul_sub, Real.norm_eq_abs, abs_mul]
  have hA : 0 ≤ (C₂ * ‖v‖) * 2 ^ M * jbracket x ^ M * Real.sqrt (mom d (2 * M) σ₀) := by positivity
  have hlip2 : |s83_G c σ (fun z => fderiv ℝ f z v) x' - s83_G c σ (fun z => fderiv ℝ f z v) x| ≤
      ((C₂ * ‖v‖) * 2 ^ M * jbracket x ^ M * Real.sqrt (mom d (2 * M) σ₀)) *
        (2 * ((|c| / |σ|) * ‖x' - x‖)) := by
    refine lip.trans ?_
    calc (C₂ * ‖v‖) * 2 ^ M * jbracket x ^ M * Real.sqrt (mom d (2 * M) σ₀) *
          ((|c| / |σ|) * ‖x' - x‖) * Real.exp (((|c| / |σ|) * ‖x' - x‖) ^ 2 / 2)
        = ((C₂ * ‖v‖) * 2 ^ M * jbracket x ^ M * Real.sqrt (mom d (2 * M) σ₀)) *
          (((|c| / |σ|) * ‖x' - x‖) * Real.exp (((|c| / |σ|) * ‖x' - x‖) ^ 2 / 2)) := by ring
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left ?_ hA
          nlinarith [Real.exp_pos (((|c| / |σ|) * ‖x' - x‖) ^ 2 / 2)]
  calc |c| * |s83_G c σ (fun z => fderiv ℝ f z v) x' - s83_G c σ (fun z => fderiv ℝ f z v) x|
      ≤ 1 * (((C₂ * ‖v‖) * 2 ^ M * jbracket x ^ M * Real.sqrt (mom d (2 * M) σ₀)) *
        (2 * ((|c| / |σ|) * ‖x' - x‖))) := mul_le_mul hc hlip2 (abs_nonneg _) zero_le_one
    _ = _ := by ring

/-- **Hölder-1/2 smoothing of `D P_τ`.** -/
theorem s84_P_fderiv_holder {a ν T M : ℝ} (ha : 0 < a) (hν : 0 < ν) (hM : 0 ≤ M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {C : ℝ} {g : Euc d → ℝ}, Continuous g → Wt M C g → ∀ {τ : ℝ}, 0 < τ → τ ≤ T →
      ∀ {x x' : Euc d}, ‖x' - x‖ ≤ 1 / 4 →
      ‖fderiv ℝ (s83_P a ν τ g) x' - fderiv ℝ (s83_P a ν τ g) x‖ ≤
        K * C * τ ^ (-(3 / 4 : ℝ)) * ‖x' - x‖ ^ (1 / 2 : ℝ) * jbracket x ^ M := by
  set σ₀ : ℝ := Real.sqrt (ν / a) with hσ₀
  set K₁ : ℝ := s84_K1 d M a ν T with hK₁
  have hK₁0 : 0 ≤ K₁ := s84_K1_nonneg M ha hν
  set Pm : ℝ := Real.sqrt (mom d (2 * M) σ₀) with hPm
  have hPm0 : 0 ≤ Pm := Real.sqrt_nonneg _
  set sT : ℝ := s84_sT a ν T with hsT
  have hsT0 : 0 < sT := s84_sT_pos hν
  set s' : ℝ := sT / Real.sqrt 2 with hs'
  have hs'0 : 0 < s' := by positivity
  set R1 : ℝ := K₁ * Real.sqrt 2 * 2 ^ M * Pm * 2 with hR1
  set R2 : ℝ := K₁ * (3 ^ M + 1) with hR2
  have hR10 : 0 ≤ R1 := by positivity
  have hR20 : 0 ≤ R2 := by positivity
  refine ⟨(R1 + R2) * (Real.sqrt s')⁻¹, by positivity, ?_⟩
  intro C g hg hw τ hτ0 hτT x x' hxx
  have hC := hw.nonneg
  set δ : ℝ := ‖x' - x‖ with hδ
  have hδ0 : 0 ≤ δ := norm_nonneg _
  have hh0 : 0 < τ / 2 := by positivity
  have hhT : τ / 2 ≤ T := by linarith
  have hsqτ : 0 < Real.sqrt τ := Real.sqrt_pos.2 hτ0
  have hsqh : Real.sqrt (τ / 2) = Real.sqrt τ / Real.sqrt 2 := Real.sqrt_div hτ0.le 2
  -- the datum `f = P_h g`
  obtain ⟨hfC1, hfD⟩ := s84_P_fderiv (T := T) ha hν hM hg hw hh0 hhT
  have hfw : Wt M (C * 2 ^ M * mom d M σ₀) (s83_P a ν (τ / 2) g) :=
    s83_P_wt hg hM hw ha hν.le hh0.le
  have hfDw : Wt M (K₁ * C * (Real.sqrt (τ / 2))⁻¹) (fderiv ℝ (s83_P a ν (τ / 2) g)) := hfD
  have hsplit : s83_P a ν τ g = s83_G (s83_mc a (τ / 2)) (s83_ms a ν (τ / 2)) (s83_P a ν (τ / 2) g) := by
    have := s83_P_add hg hM hw ha hν.le hh0.le hh0.le (a := a) (ν := ν)
    rw [show τ / 2 + τ / 2 = τ by ring] at this
    exact this
  -- constants of the half-step
  have hc1 : |s83_mc a (τ / 2)| ≤ 1 := s83_abs_mc_le_one ha.le hh0.le
  have hσ1 : |s83_ms a ν (τ / 2)| ≤ σ₀ := s83_abs_ms_le ha hν.le hh0.le
  have hσ0 : s83_ms a ν (τ / 2) ≠ 0 := (s83_ms_pos ha hν hh0).ne'
  have hσlow : sT * Real.sqrt (τ / 2) ≤ s83_ms a ν (τ / 2) := s84_ms_lower ha hν hh0.le hhT
  have hς0 : 0 < s' * Real.sqrt τ := by positivity
  have hςeq : sT * Real.sqrt (τ / 2) = s' * Real.sqrt τ := by
    rw [hsqh, hs']; field_simp
  have hςσ : s' * Real.sqrt τ ≤ s83_ms a ν (τ / 2) := by rw [← hςeq]; exact hσlow
  have hσpos : 0 < s83_ms a ν (τ / 2) := lt_of_lt_of_le hς0 hςσ
  rw [hsplit]
  have hjbx : 0 < jbracket x := s83_jb_pos x
  set u : ℝ := δ / (s' * Real.sqrt τ) with hu
  have hu0 : 0 ≤ u := by positivity
  have hcommon : 0 ≤ C * (Real.sqrt τ)⁻¹ * jbracket x ^ M := by positivity
  have hkey : ‖fderiv ℝ (s83_G (s83_mc a (τ / 2)) (s83_ms a ν (τ / 2)) (s83_P a ν (τ / 2) g)) x' -
        fderiv ℝ (s83_G (s83_mc a (τ / 2)) (s83_ms a ν (τ / 2)) (s83_P a ν (τ / 2) g)) x‖ ≤
      (R1 + R2) * C * (Real.sqrt τ)⁻¹ * jbracket x ^ M * Real.sqrt u := by
    by_cases hcase : δ ≤ s' * Real.sqrt τ
    · -- Lipschitz regime
      have hσe : |s83_ms a ν (τ / 2)| = s83_ms a ν (τ / 2) := abs_of_pos hσpos
      have hκ : (|s83_mc a (τ / 2)| / |s83_ms a ν (τ / 2)|) * ‖x' - x‖ ≤ u := by
        rw [hσe, hu, hδ]
        calc |s83_mc a (τ / 2)| / s83_ms a ν (τ / 2) * ‖x' - x‖ ≤ 1 / (s' * Real.sqrt τ) * ‖x' - x‖ := by
              refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
              calc |s83_mc a (τ / 2)| / s83_ms a ν (τ / 2) ≤ 1 / s83_ms a ν (τ / 2) :=
                    div_le_div_of_nonneg_right hc1 hσpos.le
                _ ≤ 1 / (s' * Real.sqrt τ) := one_div_le_one_div_of_le hς0 hςσ
          _ = ‖x' - x‖ / (s' * Real.sqrt τ) := by ring
      have hu1 : u ≤ 1 := by rw [hu, div_le_one hς0]; exact hcase
      have hlip := s84_clm_lip hfC1 hM hfw hfDw hc1 hσ1 hσ0 x x' (hκ.trans hu1)
      refine hlip.trans ?_
      have hus : u ≤ Real.sqrt u := by
        have h1 : Real.sqrt u ≤ 1 := Real.sqrt_le_one.2 hu1 |> fun h => h
        nlinarith [Real.sqrt_nonneg u, Real.sq_sqrt hu0]
      have hmono : (K₁ * C * (Real.sqrt (τ / 2))⁻¹) * 2 ^ M * jbracket x ^ M * Pm *
            (2 * ((|s83_mc a (τ / 2)| / |s83_ms a ν (τ / 2)|) * ‖x' - x‖)) ≤
          (K₁ * C * (Real.sqrt (τ / 2))⁻¹) * 2 ^ M * jbracket x ^ M * Pm * (2 * u) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith
      refine hmono.trans ?_
      have e : (K₁ * C * (Real.sqrt (τ / 2))⁻¹) * 2 ^ M * jbracket x ^ M * Pm * (2 * u) =
          R1 * C * (Real.sqrt τ)⁻¹ * jbracket x ^ M * u := by
        rw [hsqh, hR1]; field_simp
      rw [e]
      have h1 : R1 * C * (Real.sqrt τ)⁻¹ * jbracket x ^ M * u ≤
          R1 * C * (Real.sqrt τ)⁻¹ * jbracket x ^ M * Real.sqrt u :=
        mul_le_mul_of_nonneg_left hus (by positivity)
      refine h1.trans ?_
      have : R1 * (C * (Real.sqrt τ)⁻¹ * jbracket x ^ M) ≤ (R1 + R2) * (C * (Real.sqrt τ)⁻¹ * jbracket x ^ M) :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hR20) hcommon
      calc R1 * C * (Real.sqrt τ)⁻¹ * jbracket x ^ M * Real.sqrt u
          = (R1 * (C * (Real.sqrt τ)⁻¹ * jbracket x ^ M)) * Real.sqrt u := by ring
        _ ≤ ((R1 + R2) * (C * (Real.sqrt τ)⁻¹ * jbracket x ^ M)) * Real.sqrt u :=
            mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg u)
        _ = _ := by ring
    · -- sup regime
      push Not at hcase
      have hu1 : 1 ≤ u := by rw [hu, one_le_div hς0]; exact hcase.le
      have hus : 1 ≤ Real.sqrt u := Real.one_le_sqrt.2 hu1
      obtain ⟨-, hDτ⟩ := s84_P_fderiv (T := T) ha hν hM hg hw hτ0 hτT
      have hj3 : jbracket x' ^ M ≤ 3 ^ M * jbracket x ^ M := by
        have : jbracket x' ≤ 3 * jbracket x := by
          refine s83_jb_le_three ?_
          rw [show ‖x' - x‖ = δ from rfl]; linarith
        calc jbracket x' ^ M ≤ (3 * jbracket x) ^ M := Real.rpow_le_rpow (s83_jb_pos _).le this hM
          _ = 3 ^ M * jbracket x ^ M := Real.mul_rpow (by norm_num) (s83_jb_pos _).le
      have hn1 : ‖fderiv ℝ (s83_P a ν τ g) x'‖ ≤ K₁ * C * (Real.sqrt τ)⁻¹ * (3 ^ M * jbracket x ^ M) :=
        (hDτ x').trans (mul_le_mul_of_nonneg_left hj3 (by positivity))
      have hn2 := hDτ x
      rw [← hsplit]
      calc ‖fderiv ℝ (s83_P a ν τ g) x' - fderiv ℝ (s83_P a ν τ g) x‖
          ≤ ‖fderiv ℝ (s83_P a ν τ g) x'‖ + ‖fderiv ℝ (s83_P a ν τ g) x‖ := norm_sub_le _ _
        _ ≤ K₁ * C * (Real.sqrt τ)⁻¹ * (3 ^ M * jbracket x ^ M) +
              K₁ * C * (Real.sqrt τ)⁻¹ * jbracket x ^ M := add_le_add hn1 hn2
        _ = R2 * (C * (Real.sqrt τ)⁻¹ * jbracket x ^ M) := by rw [hR2]; ring
        _ ≤ (R1 + R2) * (C * (Real.sqrt τ)⁻¹ * jbracket x ^ M) :=
            mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hR10) hcommon
        _ ≤ ((R1 + R2) * (C * (Real.sqrt τ)⁻¹ * jbracket x ^ M)) * Real.sqrt u := by
            have h0 : 0 ≤ (R1 + R2) * (C * (Real.sqrt τ)⁻¹ * jbracket x ^ M) := by positivity
            nlinarith [mul_le_mul_of_nonneg_left hus h0]
        _ = _ := by ring
  refine hkey.trans (le_of_eq ?_)
  have hsu : Real.sqrt u = ‖x' - x‖ ^ (1 / 2 : ℝ) * ((Real.sqrt s')⁻¹ * (Real.sqrt (Real.sqrt τ))⁻¹) := by
    rw [hu, Real.sqrt_div hδ0, hδ, Real.sqrt_eq_rpow (‖x' - x‖), Real.sqrt_mul hs'0.le, div_eq_mul_inv, mul_inv]
  rw [hsu, ← s84_inv_sqrt_mul τ hτ0]
  ring

end HRS.MS.Wad
