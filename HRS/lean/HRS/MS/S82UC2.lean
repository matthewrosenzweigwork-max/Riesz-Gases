import HRS.MS.S82UC1

/-!
# S8.2 A01 (S82U): product integrability of the pole envelopes and integrability of `ψ_y = ∇_1 Q(·,y)`
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.S82U
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82P2 HRS.MS.S82T HRS.MH.PairingRd

lemma u_int_dens {d : ℕ} {rho : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity rho) {g : Euc d → ℝ}
    (hg : Integrable g (HRS.Whole.withDensityReal rho)) :
    Integrable (fun z => rho z * g z) := by
  unfold HRS.Whole.withDensityReal at hg
  have hm : Measurable (fun z => ENNReal.ofReal (rho z)) := ENNReal.measurable_ofReal.comp hρ.measurable
  have := (integrable_withDensity_iff_integrable_smul' hm (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).1 hg
  refine this.congr (Eventually.of_forall fun z => ?_)
  simp only [ENNReal.toReal_ofReal (hρ.nonneg z), smul_eq_mul]

/-- `ρ(x)ρ(z) ⟨x⟩^a ⟨z⟩^a pole(x,z) pole(x,y)` is integrable on the product. -/
lemma u_prod_int {d : ℕ} (hd : 2 ≤ d) {a Gc c : ℝ} (ha : 0 ≤ a) (hG : 0 ≤ Gc) (hc : 0 < c)
    {rho : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity rho) (hρG : HRS.Whole.HasR2GaussianUpper Gc c rho)
    (y : Euc d) :
    Integrable (fun p : Euc d × Euc d => rho p.1 * rho p.2 *
      (jbracket p.1 ^ a * jbracket p.2 ^ a * (pole p.1 p.2 * pole p.1 y)))
      ((volume : Measure (Euc d)).prod volume) := by
  have hρm := hρ.measurable
  have hρ0 := hρ.nonneg
  obtain ⟨C, hC, hrow⟩ := u_row_pole hd ha hG hc hρ hρG
  obtain ⟨C2, hC2, hrow2⟩ := u_row_pole hd (by linarith : 0 ≤ 2 * a) hG hc hρ hρG
  have hpm : Measurable (fun p : Euc d × Euc d => pole p.1 p.2) := by
    unfold pole smallRadius
    exact measurable_const.add ((measurable_const.min (measurable_fst.sub measurable_snd).norm).pow_const _)
  have hpy : Measurable (fun p : Euc d × Euc d => pole p.1 y) := by
    have : Measurable (fun x : Euc d => pole x y) := by
      unfold pole smallRadius
      exact measurable_const.add ((measurable_const.min (measurable_id.sub measurable_const).norm).pow_const _)
    exact this.comp measurable_fst
  have hjm : ∀ b : ℝ, Measurable (fun x : Euc d => jbracket x ^ b) := s82q_measurable_jb
  have hf : Measurable (fun p : Euc d × Euc d => rho p.1 * rho p.2 *
      (jbracket p.1 ^ a * jbracket p.2 ^ a * (pole p.1 p.2 * pole p.1 y))) :=
    ((hρm.comp measurable_fst).mul (hρm.comp measurable_snd)).mul
      ((((hjm a).comp measurable_fst).mul ((hjm a).comp measurable_snd)).mul (hpm.mul hpy))
  have hnn : ∀ p : Euc d × Euc d, 0 ≤ rho p.1 * rho p.2 *
      (jbracket p.1 ^ a * jbracket p.2 ^ a * (pole p.1 p.2 * pole p.1 y)) := fun p =>
    mul_nonneg (mul_nonneg (hρ0 _) (hρ0 _)) (mul_nonneg (mul_nonneg (u_jb_rpow_pos a _).le
      (u_jb_rpow_pos a _).le) (mul_nonneg (by linarith [u_pole_pos p.1 p.2]) (by linarith [u_pole_pos p.1 y])))
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hnn)]
  refine lt_of_eq_of_lt (lintegral_prod _ (ENNReal.measurable_ofReal.comp hf).aemeasurable) ?_
  -- inner integral
  have hinner : ∀ x : Euc d, ∫⁻ z, ENNReal.ofReal (rho x * rho z *
      (jbracket x ^ a * jbracket z ^ a * (pole x z * pole x y))) ≤
      ENNReal.ofReal (rho x * (C * (jbracket x ^ (2 * a) * pole x y))) := by
    intro x
    have hpt : ∀ z : Euc d, ENNReal.ofReal (rho x * rho z *
        (jbracket x ^ a * jbracket z ^ a * (pole x z * pole x y))) =
        ENNReal.ofReal (rho x * (jbracket x ^ a * pole x y)) *
          ENNReal.ofReal (rho z * (jbracket z ^ a * pole x z)) := by
      intro z
      rw [← ENNReal.ofReal_mul (mul_nonneg (hρ0 _) (mul_nonneg (u_jb_rpow_pos a _).le
        (by linarith [u_pole_pos x y])))]
      congr 1; ring
    simp_rw [hpt]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hmj : Measurable (fun z : Euc d => jbracket z ^ a * pole x z) :=
      (hjm a).mul (s82q_measurable_pole x)
    rw [u_lint_dens hρ hmj]
    refine le_trans (mul_le_mul' le_rfl (hrow x)) ?_
    rw [← ENNReal.ofReal_mul (mul_nonneg (hρ0 _) (mul_nonneg (u_jb_rpow_pos a _).le
        (by linarith [u_pole_pos x y])))]
    refine ENNReal.ofReal_le_ofReal ?_
    have e : jbracket x ^ (2 * a) = jbracket x ^ a * jbracket x ^ a := by
      rw [two_mul, Real.rpow_add (HRS.MS.S82N.s82n_jb_pos x)]
    rw [e]
    have := hρ0 x
    nlinarith [mul_nonneg this (mul_nonneg (u_jb_rpow_pos a x).le (by linarith [u_pole_pos x y] : (0:ℝ) ≤ pole x y)),
      u_jb_rpow_pos a x]
  refine lt_of_le_of_lt (lintegral_mono hinner) ?_
  have hm2 : Measurable (fun x : Euc d => C * (jbracket x ^ (2 * a) * pole x y)) :=
    measurable_const.mul ((hjm (2 * a)).mul (by
      unfold pole smallRadius
      exact measurable_const.add ((measurable_const.min (measurable_id.sub measurable_const).norm).pow_const _)))
  rw [u_lint_dens hρ hm2]
  have h2 : ∫⁻ x, ENNReal.ofReal (C * (jbracket x ^ (2 * a) * pole x y)) ∂(HRS.Whole.withDensityReal rho) ≤
      ENNReal.ofReal C * ENNReal.ofReal (C2 * jbracket y ^ (2 * a)) := by
    have : ∀ x : Euc d, ENNReal.ofReal (C * (jbracket x ^ (2 * a) * pole x y)) =
        ENNReal.ofReal C * ENNReal.ofReal (jbracket x ^ (2 * a) * pole y x) := by
      intro x
      rw [← ENNReal.ofReal_mul hC, u_pole_symm x y]
    simp_rw [this]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact mul_le_mul' le_rfl (hrow2 y)
  exact lt_of_le_of_lt h2 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)

end HRS.MS.S82U
