import HRS.MC.S7S7fAux3

/-!
# Packet S7f, helper 4: the exact identity `√N (E Φ(W_N) - E Φ(G)) = R1 - T_A + γ T_B`
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7f

open HRS HRS.Sec7 HRS.MC.SEdge HRS.StaticLimitAux HRS.MC.Sec7.S7d HRS.MC.Sec7.S7c

variable {d : ℕ} {s : ℝ} {r : ℝ}

theorem s7f_D2_cont {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    (hf : ContDiff ℝ 4 f) (u w : E) : Continuous (fun x => iteratedFDeriv ℝ 2 f x ![u, w]) :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => E) ℝ ![u, w]).continuous.comp
    (hf.continuous_iteratedFDeriv (m := 2) (by norm_num))

theorem s7f_stein_cl_c2b {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    (hf : s7d_Cl f) : HRS.MC.Sec7.S7c.s7_C2b f :=
  ⟨hf.1.of_le (by norm_num), ⟨1, by rintro _ ⟨x, rfl⟩; exact hf.2 1 le_rfl (by norm_num) x⟩,
    ⟨1, by rintro _ ⟨x, rfl⟩; exact hf.2 2 (by norm_num) (by norm_num) x⟩⟩

theorem s7f_exact_identity (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hr : r = 2 * (d : ℝ) + 6)
    {γ : ℝ} (hγ : 0 ≤ γ) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ)
    {a : NonzeroLattice d → Torus d → ℝ} {v : NonzeroLattice d → Fin d → Torus d → ℝ} {C₀ : ℝ}
    (hmode : s7_ModeData d s γ ρ r a v C₀)
    (G : Measure (NegSobolev d r)) [IsProbabilityMeasure G]
    (hG : IsCenteredGaussianWithCov r G fun φ ψ =>
      ∫ x, φ x * responseRep (periodicRiesz d s) (withDensityReal ρ) γ ψ x ∂(withDensityReal ρ))
    {N : ℕ} (hN : 1 ≤ N) {Φ : NegSobolev d r → ℝ} (hΦ : Φ ∈ CbUnitBall (NegSobolev d r) 5) :
    Real.sqrt N * (∫ X, Φ (zetaE r (sed_Q d s N γ ρ) X) ∂(sed_Q d s N γ ρ) - ∫ F, Φ F ∂G) =
      (∑' k, ∑' l, Real.sqrt N * (s7_Cmode r ρ a l k -
            ∫ X, sed_A (v k) (s7_phi r l) X ∂(sed_Q d s N γ ρ)) *
          ∫ X, iteratedFDeriv ℝ 2 (steinSolG G Φ) (zetaE r (sed_Q d s N γ ρ) X)
            ![s7_eps r k, s7_eps r l] ∂(sed_Q d s N γ ρ)) -
      (∑' k, ∑' l, ∫ X, Real.sqrt N * (sed_A (v k) (s7_phi r l) X -
              ∫ Y, sed_A (v k) (s7_phi r l) Y ∂(sed_Q d s N γ ρ)) *
            iteratedFDeriv ℝ 2 (steinSolG G Φ) (zetaE r (sed_Q d s N γ ρ) X)
              ![s7_eps r k, s7_eps r l] ∂(sed_Q d s N γ ρ)) +
      γ * ∑' k, ∫ X, sed_B d s ρ γ (v k) X *
            fderiv ℝ (steinSolG G Φ) (zetaE r (sed_Q d s N γ ρ) X) (s7_eps r k)
            ∂(sed_Q d s N γ ρ) := by
  classical
  have hr' : (d : ℝ) < 2 * r := by rw [hr]; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  have hQ : IsProbabilityMeasure (sed_Q d s N γ ρ) :=
    HRS.MC.SEdge.B4b.b4b_isProb hd hs0 hs hγ hρ N hN
  have hNpos : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
  have hWint := s7c_W_integrable hd hs0 hs hγ hρ hr hN
  have hWm := s7c_zeta_meas hN hr' (sed_Q d s N γ ρ)
  have hcl : s7d_Cl (steinSolG G Φ) := s7d_stein_cl G hG.1 hΦ
  have hS7c := HRS.MC.Sec7.S7c.s7_S7c_hilbert_stein_proof hd hs0 hs r hr hγ hρ hmode hN
    (F := steinSolG G Φ) (s7f_stein_cl_c2b hcl)
  have hexp := fun x => s7f_stein_expand hd hs0 hs hr hγ hρ hmode G hG hΦ x
  have hmem : MemCb 5 Φ := ⟨hΦ.1, hΦ.2.1⟩
  have hb := s7d_b_summable (d := d)
  have hb0 := s7f_b_nonneg (d := d)
  obtain ⟨Cc, hCc0, hCc⟩ := s7f_cmode_bound hr hρ hmode
  obtain ⟨CA, hCA0, hCA⟩ := s7c_A_bound hr hmode
  set Q := sed_Q d s N γ ρ with hQdef
  set W := zetaE r Q with hWdef
  set f := steinSolG G Φ with hfdef
  set c := ∫ F, Φ F ∂G with hcdef
  set sN := Real.sqrt N with hsN
  -- the integrands
  have hD2m : ∀ k l : NonzeroLattice d,
      Measurable (fun X => iteratedFDeriv ℝ 2 f (W X) ![s7_eps r k, s7_eps r l]) :=
    fun k l => (s7f_D2_cont hcl.1 _ _).measurable.comp hWm
  have hD2b : ∀ (k l : NonzeroLattice d) X,
      |iteratedFDeriv ℝ 2 f (W X) ![s7_eps r k, s7_eps r l]| ≤ 1 := by
    intro k l X
    have := s7d_D2_bound (hcl.2 2 (by norm_num) (by norm_num) (W X)) (s7_eps r k) (s7_eps r l)
    rwa [HRS.MC.Sec7.S7e.s7e_eps_norm, HRS.MC.Sec7.S7e.s7e_eps_norm, mul_one] at this
  have hD2i : ∀ k l : NonzeroLattice d,
      Integrable (fun X => iteratedFDeriv ℝ 2 f (W X) ![s7_eps r k, s7_eps r l]) Q := fun k l =>
    Integrable.of_bound (hD2m k l).aestronglyMeasurable 1
      (Eventually.of_forall fun X => by rw [Real.norm_eq_abs]; exact hD2b k l X)
  have hAm : ∀ k l : NonzeroLattice d, Measurable (sed_A (v k) (s7_phi r l) : Config d N → ℝ) :=
    fun k l => s7c_A_meas hN k l hmode.smooth_v
  have hAb : ∀ (k l : NonzeroLattice d) (X : Config d N),
      |sed_A (v k) (s7_phi r l) X| ≤ CA * (s7_b k * s7_b l) := by
    intro k l X; have := hCA N hN k l X; rwa [mul_assoc] at this
  have hAi : ∀ k l : NonzeroLattice d, Integrable (sed_A (v k) (s7_phi r l)) Q := fun k l =>
    Integrable.of_bound (hAm k l).aestronglyMeasurable (CA * (s7_b k * s7_b l))
      (Eventually.of_forall fun X => by rw [Real.norm_eq_abs]; exact hAb k l X)
  -- notation for the means
  set M : NonzeroLattice d → NonzeroLattice d → ℝ := fun k l =>
    ∫ X, iteratedFDeriv ℝ 2 f (W X) ![s7_eps r k, s7_eps r l] ∂Q with hMdef
  set Ab : NonzeroLattice d → NonzeroLattice d → ℝ := fun k l =>
    ∫ X, sed_A (v k) (s7_phi r l) X ∂Q with hAbdef
  have hM1 : ∀ k l, |M k l| ≤ 1 := fun k l => s7f_abs_integral_le _ (hD2b k l)
  have hAbb : ∀ k l, |Ab k l| ≤ CA * (s7_b k * s7_b l) := fun k l =>
    s7f_abs_integral_le _ (hAb k l)
  -- bounds for the four double series
  have hu1 : ∀ k l, |s7_Cmode r ρ a l k * M k l| ≤ Cc * (s7_b k * s7_b l) := by
    intro k l
    rw [abs_mul]
    calc |s7_Cmode r ρ a l k| * |M k l| ≤ (Cc * (s7_b l * s7_b k)) * 1 :=
          mul_le_mul (hCc l k) (hM1 k l) (abs_nonneg _) (mul_nonneg hCc0 (mul_nonneg (hb0 l) (hb0 k)))
      _ = _ := by ring
  have hu3 : ∀ k l, |Ab k l * M k l| ≤ CA * (s7_b k * s7_b l) := by
    intro k l
    rw [abs_mul]
    calc |Ab k l| * |M k l| ≤ (CA * (s7_b k * s7_b l)) * 1 :=
          mul_le_mul (hAbb k l) (hM1 k l) (abs_nonneg _) (mul_nonneg hCA0 (mul_nonneg (hb0 k) (hb0 l)))
      _ = _ := by ring
  have hu2 : ∀ k l, |∫ X, sed_A (v k) (s7_phi r l) X *
      iteratedFDeriv ℝ 2 f (W X) ![s7_eps r k, s7_eps r l] ∂Q| ≤ CA * (s7_b k * s7_b l) := by
    intro k l
    refine s7f_abs_integral_le _ (fun X => ?_)
    rw [abs_mul]
    calc |sed_A (v k) (s7_phi r l) X| * |iteratedFDeriv ℝ 2 f (W X) ![s7_eps r k, s7_eps r l]|
        ≤ (CA * (s7_b k * s7_b l)) * 1 :=
          mul_le_mul (hAb k l X) (hD2b k l X) (abs_nonneg _) (mul_nonneg hCA0 (mul_nonneg (hb0 k) (hb0 l)))
      _ = _ := by ring
  have hu4 : ∀ k l, |∫ X, sN * (sed_A (v k) (s7_phi r l) X - Ab k l) *
      iteratedFDeriv ℝ 2 f (W X) ![s7_eps r k, s7_eps r l] ∂Q| ≤
      (sN * (2 * CA)) * (s7_b k * s7_b l) := by
    intro k l
    have hbd : 0 ≤ CA * (s7_b k * s7_b l) := mul_nonneg hCA0 (mul_nonneg (hb0 k) (hb0 l))
    have := s7f_abs_integral_le (μ := Q) (C := (sN * (2 * CA)) * (s7_b k * s7_b l))
      (f := fun X => sN * (sed_A (v k) (s7_phi r l) X - Ab k l) *
        iteratedFDeriv ℝ 2 f (W X) ![s7_eps r k, s7_eps r l]) (fun X => by
        rw [abs_mul, abs_mul, abs_of_pos hNpos]
        have h1 : |sed_A (v k) (s7_phi r l) X - Ab k l| ≤ 2 * (CA * (s7_b k * s7_b l)) :=
          (abs_sub _ _).trans (by linarith [hAb k l X, hAbb k l])
        calc sN * |sed_A (v k) (s7_phi r l) X - Ab k l| *
              |iteratedFDeriv ℝ 2 f (W X) ![s7_eps r k, s7_eps r l]|
            ≤ sN * (2 * (CA * (s7_b k * s7_b l))) * 1 :=
              mul_le_mul (mul_le_mul_of_nonneg_left h1 hNpos.le) (hD2b k l X) (abs_nonneg _)
                (by positivity)
          _ = _ := by ring)
    exact this
  -- splitting u2 = Ab * M + sN⁻¹ * u4
  have hsplit : ∀ k l, ∫ X, sed_A (v k) (s7_phi r l) X *
      iteratedFDeriv ℝ 2 f (W X) ![s7_eps r k, s7_eps r l] ∂Q =
      Ab k l * M k l + sN⁻¹ * ∫ X, sN * (sed_A (v k) (s7_phi r l) X - Ab k l) *
        iteratedFDeriv ℝ 2 f (W X) ![s7_eps r k, s7_eps r l] ∂Q := by
    intro k l
    have e : ∀ X, sed_A (v k) (s7_phi r l) X *
        iteratedFDeriv ℝ 2 f (W X) ![s7_eps r k, s7_eps r l] =
        Ab k l * iteratedFDeriv ℝ 2 f (W X) ![s7_eps r k, s7_eps r l] +
        sN⁻¹ * (sN * (sed_A (v k) (s7_phi r l) X - Ab k l) *
          iteratedFDeriv ℝ 2 f (W X) ![s7_eps r k, s7_eps r l]) := by
      intro X; field_simp; ring
    simp_rw [e]
    have hi4 : Integrable (fun X => sN * (sed_A (v k) (s7_phi r l) X - Ab k l) *
        iteratedFDeriv ℝ 2 f (W X) ![s7_eps r k, s7_eps r l]) Q := by
      refine (((hAi k l).sub (integrable_const (Ab k l))).const_mul sN).mul_bdd
        (hD2m k l).aestronglyMeasurable (c := 1) (Eventually.of_forall fun X => ?_)
      rw [Real.norm_eq_abs]; exact hD2b k l X
    rw [integral_add ((hD2i k l).const_mul _) (hi4.const_mul _), integral_const_mul,
      integral_const_mul]
  -- the Stein equation integrated against `Q`
  have hΦb : ∀ x, |Φ x| ≤ 1 := fun x =>
    (HRS.abs_le_cbSup hmem x).trans (s7d_cbSup_le_one hΦ (by norm_num))
  have hΦWi : Integrable (fun X => Φ (W X)) Q :=
    Integrable.of_bound ((hmem.1.continuous.measurable.comp hWm).aestronglyMeasurable) 1
      (Eventually.of_forall fun X => by rw [Real.norm_eq_abs]; exact hΦb _)
  have hF1c : Continuous (fun x : NegSobolev d r => fderiv ℝ f x x) :=
    (hcl.1.continuous_fderiv (by norm_num)).clm_apply continuous_id
  have hF1 : Integrable (fun X => fderiv ℝ f (W X) (W X)) Q := by
    refine Integrable.mono' hWint (hF1c.measurable.comp hWm).aestronglyMeasurable
      (Eventually.of_forall fun X => ?_)
    have h1 := (fderiv ℝ f (W X)).le_opNorm (W X)
    have h2 : ‖fderiv ℝ f (W X)‖ ≤ 1 := by
      have := hcl.2 1 le_rfl (by norm_num) (W X)
      rwa [norm_iteratedFDeriv_one] at this
    calc ‖fderiv ℝ f (W X) (W X)‖ ≤ ‖fderiv ℝ f (W X)‖ * ‖W X‖ := h1
      _ ≤ 1 * ‖W X‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ = ‖W X‖ := one_mul _
  have hpt : ∀ X, ∑' k, ∑' l, s7_Cmode r ρ a k l *
      iteratedFDeriv ℝ 2 f (W X) ![s7_eps r k, s7_eps r l] =
      Φ (W X) - c + fderiv ℝ f (W X) (W X) := fun X => by
    have := hexp (W X); linarith
  have hSval : ∫ X, ∑' k, ∑' l, s7_Cmode r ρ a k l *
      iteratedFDeriv ℝ 2 f (W X) ![s7_eps r k, s7_eps r l] ∂Q =
      ∑' k, ∑' l, s7_Cmode r ρ a k l * M k l := by
    rw [s7f_integral_tsum2 Q hb hb0 Cc (fun k l X => s7_Cmode r ρ a k l *
        iteratedFDeriv ℝ 2 f (W X) ![s7_eps r k, s7_eps r l]) (fun k l => (hD2i k l).const_mul _)
      (fun k l X => by
        rw [abs_mul]
        calc _ ≤ (Cc * (s7_b k * s7_b l)) * 1 :=
              mul_le_mul (hCc k l) (hD2b k l X) (abs_nonneg _)
                (mul_nonneg hCc0 (mul_nonneg (hb0 k) (hb0 l)))
          _ = _ := by ring)]
    simp_rw [integral_const_mul]
    rfl
  have hSval2 : ∫ X, ∑' k, ∑' l, s7_Cmode r ρ a k l *
      iteratedFDeriv ℝ 2 f (W X) ![s7_eps r k, s7_eps r l] ∂Q =
      (∫ X, Φ (W X) ∂Q) - c + ∫ X, fderiv ℝ f (W X) (W X) ∂Q := by
    have hi : Integrable (fun X => Φ (W X) - c) Q := hΦWi.sub (integrable_const c)
    rw [integral_congr_ae (Eventually.of_forall hpt), integral_add hi hF1,
      integral_sub hΦWi (integrable_const c)]
    simp
  -- symmetry of the covariance
  have hsymm : ∀ k l, s7_Cmode r ρ a k l = s7_Cmode r ρ a l k := fun k l =>
    s7f_cmode_symm hd hs0 hs hγ hρ hmode G hG k l
  have hu1' : ∀ k l, |s7_Cmode r ρ a k l * M k l| ≤ Cc * (s7_b k * s7_b l) := by
    intro k l; rw [hsymm k l]; exact hu1 k l
  -- the S7c side
  have hc2 : ∑' k, ∑' l, ∫ X, sed_A (v k) (s7_phi r l) X *
      iteratedFDeriv ℝ 2 f (W X) ![s7_eps r k, s7_eps r l] ∂Q =
      (∑' k, ∑' l, Ab k l * M k l) + sN⁻¹ * ∑' k, ∑' l, ∫ X, sN * (sed_A (v k) (s7_phi r l) X - Ab k l) *
        iteratedFDeriv ℝ 2 f (W X) ![s7_eps r k, s7_eps r l] ∂Q := by
    simp_rw [hsplit]
    have e4 := s7f_tsum2_const_mul hb hb0 hu4 sN⁻¹
    have e5 := s7f_tsum2_add hb hb0 hu3 (w := fun k l => sN⁻¹ * ∫ X, sN * (sed_A (v k) (s7_phi r l) X - Ab k l) *
        iteratedFDeriv ℝ 2 f (W X) ![s7_eps r k, s7_eps r l] ∂Q) (M₂ := |sN⁻¹| * ((sN * (2 * CA))))
      (fun k l => by
        rw [abs_mul, mul_assoc]
        exact mul_le_mul_of_nonneg_left (hu4 k l) (abs_nonneg _))
    rw [e5, e4]
  have hbig : (∫ X, Φ (W X) ∂Q) - c = (∑' k, ∑' l, s7_Cmode r ρ a l k * M k l) -
      ((∑' k, ∑' l, Ab k l * M k l) + sN⁻¹ * (∑' k, ∑' l, ∫ X, sN * (sed_A (v k) (s7_phi r l) X - Ab k l) *
        iteratedFDeriv ℝ 2 f (W X) ![s7_eps r k, s7_eps r l] ∂Q) -
        γ / sN * ∑' k, ∫ X, sed_B d s ρ γ (v k) X * fderiv ℝ f (W X) (s7_eps r k) ∂Q) := by
    have h1 : ∑' k, ∑' l, s7_Cmode r ρ a l k * M k l = ∑' k, ∑' l, s7_Cmode r ρ a k l * M k l := by
      refine tsum_congr fun k => tsum_congr fun l => ?_
      rw [hsymm l k]
    rw [h1, ← hSval]
    have h2 := hSval2
    rw [← hc2]
    rw [hS7c] at h2
    linarith
  -- the right-hand side
  have e1 := s7f_tsum2_const_mul hb hb0 hu1 sN
  have e3 := s7f_tsum2_const_mul hb hb0 hu3 sN
  have e13 := s7f_tsum2_sub hb hb0 (u := fun k l => sN * (s7_Cmode r ρ a l k * M k l))
    (w := fun k l => sN * (Ab k l * M k l)) (M₁ := |sN| * Cc) (M₂ := |sN| * CA)
    (fun k l => by
      rw [abs_mul, mul_assoc]; exact mul_le_mul_of_nonneg_left (hu1 k l) (abs_nonneg _))
    (fun k l => by
      rw [abs_mul, mul_assoc]; exact mul_le_mul_of_nonneg_left (hu3 k l) (abs_nonneg _))
  have hrhs : ∑' k, ∑' l, sN * (s7_Cmode r ρ a l k - Ab k l) * M k l =
      sN * (∑' k, ∑' l, s7_Cmode r ρ a l k * M k l) - sN * ∑' k, ∑' l, Ab k l * M k l := by
    have : ∀ k l, sN * (s7_Cmode r ρ a l k - Ab k l) * M k l =
        sN * (s7_Cmode r ρ a l k * M k l) - sN * (Ab k l * M k l) := fun k l => by ring
    simp_rw [this]
    rw [e13, e1, e3]
  rw [hrhs]
  have hNne : sN ≠ 0 := hNpos.ne'
  rw [hbig]
  field_simp
  ring

end HRS.MC.Sec7.S7f

end
