import HRS.MC.S7S7aAux2

/-!
# Packet `s7_S7a_mode_data`, helper 3: the `L^2` bound for the response equation
For continuous `a`, `phi` with `a + gamma K a = P phi` everywhere and `mu(a) = 0`:
`int a^2 dmu <= int phi^2 dmu` (positivity of `K`), hence `||a||_{H^0}^2 <= c0^{-1} T^2` if `|phi| <= T`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ComplexConjugate

noncomputable section

namespace HRS.MC.Sec7.S7a

open HRS HRS.PDE HRS.PDE.MFApriori HRS.PDE.MFPair HRS.PDE.MFThermalReg HRS.PDE.ClassicalPart

variable {d : ℕ} {s : ℝ}

theorem s7a_int_cont {f : Torus d → ℝ} (hf : Continuous f) (ν : Measure (Torus d))
    [IsFiniteMeasure ν] : Integrable f ν :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem s7a_kop_eq {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) (a : Torus d → ℝ) (x : Torus d) :
    Kop (periodicRiesz d s) (withDensityReal ρ) a x =
      convFun (periodicRiesz d s) (fun y => ρ y * a y) x -
        pair (withDensityReal ρ) (convFun (periodicRiesz d s) (fun y => ρ y * a y)) := by
  have hE1 : ∀ x, ∫ y, periodicRiesz d s (x - y) * a y ∂(withDensityReal ρ) =
      convFun (periodicRiesz d s) (fun y => ρ y * a y) x := by
    intro x
    rw [integral_withDensityReal_eq ρ hρ.density.measurable (fun x => (hρ.pos x).le)]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [convFun]
    ring
  have : (fun x => ∫ y, periodicRiesz d s (x - y) * a y ∂(withDensityReal ρ)) =
      convFun (periodicRiesz d s) (fun y => ρ y * a y) := funext hE1
  rw [HRS.Q66.q66_kop_eq, this, hE1]

theorem s7a_G_cont (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {ρ : Torus d → ℝ}
    (hρ : SmoothPosDensity ρ) {a : Torus d → ℝ} (ha : Continuous a) :
    Continuous (convFun (periodicRiesz d s) (fun y => ρ y * a y)) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < d := by linarith
  have F : MFInputs.MFKernelFacts d s := MFInputs.mfKernelFacts_of_two hd s hs0 hsd
  exact MFAux.continuous_convFun F.integrable ((HRS.Q66.q66_cont_of_smooth hρ.smooth).mul ha)

theorem s7a_L2 (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {γ : ℝ} (hγ : 0 ≤ γ)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) :
    ∃ A0 : ℝ, 0 ≤ A0 ∧ ∀ (a φ : Torus d → ℝ) (T : ℝ), Continuous a → Continuous φ →
      (∀ x, |φ x| ≤ T) →
      (∀ x, a x + γ * Kop (periodicRiesz d s) (withDensityReal ρ) a x =
        projMean (withDensityReal ρ) φ x) →
      ∫ x, a x ∂(withDensityReal ρ) = 0 →
      hsNormSq 0 (coeffOf a) ≤ A0 * T ^ 2 := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < d := by linarith
  haveI : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  have hρc : Continuous ρ := HRS.Q66.q66_cont_of_smooth hρ.smooth
  have hρm : Measurable ρ := hρ.density.measurable
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x => (hρ.pos x).le
  obtain ⟨Λ, hΛ'⟩ := HRS.Q66.q66_bound_of_smooth hρ.smooth
  have hΛ : ∀ x, ρ x ≤ Λ := fun x => (le_abs_self _).trans (hΛ' x)
  obtain ⟨x0, -, hx0⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty (α := Torus d))
    hρc.continuousOn
  set c0 : ℝ := ρ x0 with hc0
  have hc0pos : 0 < c0 := hρ.pos x0
  have hc0le : ∀ x, c0 ≤ ρ x := fun x => hx0 (Set.mem_univ x)
  refine ⟨c0⁻¹, inv_nonneg.2 hc0pos.le, fun a φ T ha hφ hT heq hmean => ?_⟩
  set μ := withDensityReal ρ with hμ
  set G : Torus d → ℝ := convFun (periodicRiesz d s) (fun y => ρ y * a y) with hG
  have hGc : Continuous G := s7a_G_cont hd hs0 hs hρ ha
  set m : ℝ := pair μ G with hm
  set c : ℝ := pair μ φ with hcdef
  have hKop : ∀ x, Kop (periodicRiesz d s) μ a x = G x - m := fun x => s7a_kop_eq hρ a x
  -- positivity of the energy form
  have hKt : ∀ x, ResponseAux.Kt (periodicRiesz d s) μ a x = G x := by
    intro x
    unfold ResponseAux.Kt
    rw [hμ, integral_withDensityReal_eq ρ hρm hρ0]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [hG, convFun]
    ring
  have hpos : 0 ≤ ∫ x, G x * a x ∂μ := by
    have h1 := ResponseAux.Kt_form_nonneg (ρ := ρ) (Λ := Λ) hρ.density hΛ
      (PoleCavityAux.measurable_periodicRiesz hd hs0 hsd) (integral_periodicRiesz hd hs0 hsd).1
      (rieszCoeff d s)
      (fun n => by
        by_cases hn : n = 0
        · simp [rieszCoeff, hn]
        · exact (rieszCoeff_pos hd hs0 hsd n hn).le)
      (ResponseAux.hcoef_of_funFourierCoeff (periodicRiesz_fourierCoeff hd hs0 hsd))
      (f := a) (ha.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    have h1' : ∫ x, G x * a x ∂μ = ∫ x, ResponseAux.Kt (periodicRiesz d s) μ a x * a x ∂μ :=
      integral_congr_ae (Eventually.of_forall fun x => congrArg (· * a x) (hKt x).symm)
    rw [h1']
    exact h1
  -- the energy identity
  have hint_a : Integrable a μ := s7a_int_cont ha μ
  have hint_a2 : Integrable (fun x => a x ^ 2) μ := s7a_int_cont (ha.pow 2) μ
  have hint_Ga : Integrable (fun x => G x * a x) μ := s7a_int_cont (hGc.mul ha) μ
  have hint_pa : Integrable (fun x => φ x * a x) μ := s7a_int_cont (hφ.mul ha) μ
  have hint_p2 : Integrable (fun x => φ x ^ 2) μ := s7a_int_cont (hφ.pow 2) μ
  have hpt : ∀ x, a x ^ 2 = φ x * a x - c * a x - γ * (G x * a x) + γ * m * a x := by
    intro x
    have h := heq x
    rw [hKop x] at h
    simp only [projMean] at h
    have : a x = φ x - c - γ * (G x - m) := by linarith
    calc a x ^ 2 = a x * a x := sq _
      _ = (φ x - c - γ * (G x - m)) * a x := by rw [← this]
      _ = _ := by ring
  have hE : ∫ x, a x ^ 2 ∂μ = ∫ x, φ x * a x ∂μ - γ * ∫ x, G x * a x ∂μ := by
    have i1 : Integrable (fun x => c * a x) μ := hint_a.const_mul c
    have i2 : Integrable (fun x => γ * (G x * a x)) μ := hint_Ga.const_mul γ
    have i3 : Integrable (fun x => γ * m * a x) μ := hint_a.const_mul _
    have i4 : Integrable (fun x => φ x * a x - c * a x) μ := hint_pa.sub i1
    have i5 : Integrable (fun x => φ x * a x - c * a x - γ * (G x * a x)) μ := i4.sub i2
    have : (fun x => a x ^ 2) = fun x => (φ x * a x - c * a x - γ * (G x * a x)) + γ * m * a x :=
      funext fun x => by rw [hpt x]
    rw [this, integral_add i5 i3, integral_sub i4 i2, integral_sub hint_pa i1, integral_const_mul,
      integral_const_mul, integral_const_mul, hmean]
    ring
  have h1 : ∫ x, a x ^ 2 ∂μ ≤ ∫ x, φ x * a x ∂μ := by
    have : 0 ≤ γ * ∫ x, G x * a x ∂μ := mul_nonneg hγ hpos
    linarith
  have h2 : ∫ x, φ x * a x ∂μ ≤ (1 / 2) * ∫ x, a x ^ 2 ∂μ + (1 / 2) * ∫ x, φ x ^ 2 ∂μ := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hint_a2.const_mul _)
      (hint_p2.const_mul _)]
    refine integral_mono hint_pa ((hint_a2.const_mul _).add (hint_p2.const_mul _)) fun x => ?_
    nlinarith [sq_nonneg (a x - φ x)]
  have h3 : ∫ x, φ x ^ 2 ∂μ ≤ T ^ 2 := by
    have : ∫ x, φ x ^ 2 ∂μ ≤ ∫ _x, T ^ 2 ∂μ := by
      refine integral_mono hint_p2 (integrable_const _) fun x => ?_
      have := hT x
      have h0 : 0 ≤ T := (abs_nonneg _).trans this
      calc φ x ^ 2 = |φ x| ^ 2 := (sq_abs _).symm
        _ ≤ T ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
    simpa using this
  have h4 : ∫ x, a x ^ 2 ∂μ ≤ T ^ 2 := by linarith
  -- pass to Lebesgue measure
  have h5 : c0 * ∫ x, a x ^ 2 ≤ ∫ x, a x ^ 2 ∂μ := by
    rw [hμ, integral_withDensityReal_eq ρ hρm hρ0, ← integral_const_mul]
    refine integral_mono (s7a_int_cont ((ha.pow 2).const_mul c0) _)
      (s7a_int_cont (hρc.mul (ha.pow 2)) _) fun x => ?_
    exact mul_le_mul_of_nonneg_right (hc0le x) (sq_nonneg _)
  rw [parseval_real ha]
  rw [inv_mul_eq_div, le_div_iff₀ hc0pos]
  linarith

end HRS.MC.Sec7.S7a

end
