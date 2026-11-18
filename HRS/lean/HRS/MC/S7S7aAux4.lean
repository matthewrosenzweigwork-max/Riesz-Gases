import HRS.MC.S7S7aAux3

/-!
# Packet `s7_S7a_mode_data`, helper 4: `H^n` bounds for the response equation
By induction on `n`: `||a||_{H^n} <= A_n T` whenever `|phi| <= T` and `||phi||_{H^n} <= T`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ComplexConjugate

noncomputable section

namespace HRS.MC.Sec7.S7a

open HRS HRS.PDE HRS.PDE.MFApriori HRS.PDE.MFPair HRS.PDE.MFThermalReg HRS.PDE.ClassicalPart

variable {d : ℕ} {s : ℝ}

theorem s7a_abs_pair_le {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {f : Torus d → ℝ} {T : ℝ}
    (hT : ∀ x, |f x| ≤ T) : |pair μ f| ≤ T := by
  unfold pair
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := f) (C := T)
    (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hT x)
  simpa [Real.norm_eq_abs] using this

theorem s7a_abs_pair_G_le (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {ρ : Torus d → ℝ}
    (hρ : SmoothPosDensity ρ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ G : Torus d → ℝ, Continuous G →
      |pair (withDensityReal ρ) G| ≤ L * HRS.PDE.hsNorm 0 (coeffOf G) := by
  haveI : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  have hρm : Measurable ρ := hρ.density.measurable
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x => (hρ.pos x).le
  obtain ⟨Λ, hΛ'⟩ := HRS.Q66.q66_bound_of_smooth hρ.smooth
  have hΛ0 : 0 ≤ Λ := (abs_nonneg _).trans (hΛ' 0)
  have hρc : Continuous ρ := HRS.Q66.q66_cont_of_smooth hρ.smooth
  refine ⟨Real.sqrt Λ, Real.sqrt_nonneg _, fun G hG => ?_⟩
  set μ := withDensityReal ρ with hμ
  set m : ℝ := pair μ G with hm
  have iG : Integrable G μ := s7a_int_cont hG μ
  have iG2 : Integrable (fun x => G x ^ 2) μ := s7a_int_cont (hG.pow 2) μ
  have i1 : Integrable (fun x => (2 * m) * G x) μ := iG.const_mul _
  have i2 : Integrable (fun x => G x ^ 2 - (2 * m) * G x) μ := iG2.sub i1
  have h0 : 0 ≤ ∫ x, (G x - m) ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have e : ∫ x, (G x - m) ^ 2 ∂μ = ∫ x, G x ^ 2 ∂μ - m ^ 2 := by
    have : (fun x => (G x - m) ^ 2) = fun x => (G x ^ 2 - (2 * m) * G x) + m ^ 2 :=
      funext fun x => by ring
    rw [this, integral_add i2 (integrable_const _), integral_sub iG2 i1, integral_const_mul]
    have hmm : ∫ x, G x ∂μ = m := rfl
    rw [hmm]
    simp
    ring
  have h1 : m ^ 2 ≤ ∫ x, G x ^ 2 ∂μ := by linarith
  have h2 : ∫ x, G x ^ 2 ∂μ ≤ Λ * ∫ x, G x ^ 2 := by
    rw [hμ, integral_withDensityReal_eq ρ hρm hρ0, ← integral_const_mul]
    refine integral_mono (s7a_int_cont (hρc.mul (hG.pow 2)) _)
      (s7a_int_cont ((hG.pow 2).const_mul Λ) _) fun x => ?_
    have : ρ x ≤ Λ := (le_abs_self _).trans (hΛ' x)
    exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  have h3 : m ^ 2 ≤ Λ * hsNormSq 0 (coeffOf G) := by
    rw [parseval_real hG]; linarith
  calc |m| = Real.sqrt (m ^ 2) := (Real.sqrt_sq_eq_abs m).symm
    _ ≤ Real.sqrt (Λ * hsNormSq 0 (coeffOf G)) := Real.sqrt_le_sqrt h3
    _ = Real.sqrt Λ * HRS.PDE.hsNorm 0 (coeffOf G) := by
        rw [Real.sqrt_mul hΛ0]; rfl

theorem s7a_hs_bound (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {γ : ℝ} (hγ : 0 ≤ γ)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) (n : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (a φ : Torus d → ℝ) (T : ℝ), Torus.IsSmooth a → Torus.IsSmooth φ →
      (∀ x, |φ x| ≤ T) → HRS.PDE.hsNorm (n : ℝ) (coeffOf φ) ≤ T →
      (∀ x, a x + γ * Kop (periodicRiesz d s) (withDensityReal ρ) a x =
        projMean (withDensityReal ρ) φ x) →
      ∫ x, a x ∂(withDensityReal ρ) = 0 →
      HRS.PDE.hsNorm (n : ℝ) (coeffOf a) ≤ A * T := by
  haveI : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  have hd0 : 0 < d := by omega
  induction n with
  | zero =>
    obtain ⟨A0, hA00, hA0⟩ := s7a_L2 hd hs0 hs hγ hρ
    refine ⟨Real.sqrt A0, Real.sqrt_nonneg _, fun a φ T ha hφ hT _ heq hmean => ?_⟩
    have hT0 : 0 ≤ T := (abs_nonneg _).trans (hT 0)
    have := hA0 a φ T (HRS.Q66.q66_cont_of_smooth ha) (HRS.Q66.q66_cont_of_smooth hφ) hT heq hmean
    simp only [Nat.cast_zero]
    unfold HRS.PDE.hsNorm
    calc Real.sqrt (hsNormSq 0 (coeffOf a)) ≤ Real.sqrt (A0 * T ^ 2) := Real.sqrt_le_sqrt this
      _ = Real.sqrt A0 * T := by rw [Real.sqrt_mul hA00, Real.sqrt_sq hT0]
  | succ n ih =>
    obtain ⟨A, hA0, hA⟩ := ih
    obtain ⟨C0, hC00, hC0⟩ := s7a_conv_step hd hs0 hs
    obtain ⟨Cp, hCp0, hCp⟩ := s7a_mul_smooth hd0 hρ.smooth n
    obtain ⟨L, hL0, hL⟩ := s7a_abs_pair_G_le hd hs0 hs hρ
    refine ⟨2 + γ * (1 + L) * (C0 * Cp * A), by positivity, fun a φ T ha hφ hT hN heq hmean => ?_⟩
    have hT0 : 0 ≤ T := (abs_nonneg _).trans (hT 0)
    have hac : Continuous a := HRS.Q66.q66_cont_of_smooth ha
    have hφc : Continuous φ := HRS.Q66.q66_cont_of_smooth hφ
    have hρc : Continuous ρ := HRS.Q66.q66_cont_of_smooth hρ.smooth
    have hn1 : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    rw [hn1] at hN ⊢
    have hφn1 : MemHs ((n : ℝ) + 1) (coeffOf φ) := by
      have := memHs_of_isCk (n + 1) φ (HRS.Q66.q66_isCk_of_smooth hφ _)
      rwa [hn1] at this
    have hφn : MemHs (n : ℝ) (coeffOf φ) := memHs_of_isCk n φ (HRS.Q66.q66_isCk_of_smooth hφ _)
    have hamem : MemHs (n : ℝ) (coeffOf a) := memHs_of_isCk n a (HRS.Q66.q66_isCk_of_smooth ha _)
    -- induction hypothesis at level `n`
    have hIH : HRS.PDE.hsNorm (n : ℝ) (coeffOf a) ≤ A * T :=
      hA a φ T ha hφ hT ((hsNorm_mono_idx (by linarith) hφn1).trans hN) heq hmean
    set G : Torus d → ℝ := convFun (periodicRiesz d s) (fun y => ρ y * a y) with hG
    have hGc : Continuous G := s7a_G_cont hd hs0 hs hρ hac
    obtain ⟨hu1, hu2⟩ := hCp a hac hamem
    have hρac : Continuous (fun y => ρ y * a y) := hρc.mul hac
    obtain ⟨hG1, hG2⟩ := hC0 n _ hρac hu1
    have hGbound : HRS.PDE.hsNorm ((n : ℝ) + 1) (coeffOf G) ≤ C0 * Cp * (A * T) := by
      calc _ ≤ C0 * HRS.PDE.hsNorm (n : ℝ) (coeffOf (fun y => ρ y * a y)) := hG2
        _ ≤ C0 * (Cp * HRS.PDE.hsNorm (n : ℝ) (coeffOf a)) :=
            mul_le_mul_of_nonneg_left hu2 hC00
        _ ≤ C0 * (Cp * (A * T)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hIH hCp0) hC00
        _ = _ := by ring
    set m : ℝ := pair (withDensityReal ρ) G with hm
    set c : ℝ := pair (withDensityReal ρ) φ with hc
    have hcb : |c| ≤ T := s7a_abs_pair_le hT
    have hmb : |m| ≤ L * HRS.PDE.hsNorm ((n : ℝ) + 1) (coeffOf G) :=
      (hL G hGc).trans (mul_le_mul_of_nonneg_left (hsNorm_mono_idx (by positivity) hG1) hL0)
    have hpt : coeffOf a = coeffOf (fun x => 1 * φ x + (-γ) * G x + (-c + γ * m)) := by
      congr 1
      funext x
      have h := heq x
      rw [s7a_kop_eq hρ a x] at h
      simp only [projMean] at h
      simp only [hG, hm, hc] at h ⊢
      linarith
    rw [hpt]
    refine (s7a_hs_lincomb hφc hGc hφn1 hG1 1 (-γ) (-c + γ * m)).trans ?_
    have e1 : |(-c + γ * m)| ≤ T + γ * (L * (C0 * Cp * (A * T))) := by
      calc |(-c + γ * m)| ≤ |-c| + |γ * m| := abs_add_le _ _
        _ = |c| + γ * |m| := by rw [abs_neg, abs_mul, abs_of_nonneg hγ]
        _ ≤ T + γ * (L * (C0 * Cp * (A * T))) := by
            gcongr
            exact hmb.trans (mul_le_mul_of_nonneg_left hGbound hL0)
    have e2 : |(-γ)| * HRS.PDE.hsNorm ((n : ℝ) + 1) (coeffOf G) ≤ γ * (C0 * Cp * (A * T)) := by
      rw [abs_neg, abs_of_nonneg hγ]
      exact mul_le_mul_of_nonneg_left hGbound hγ
    have e3 : |(1 : ℝ)| * HRS.PDE.hsNorm ((n : ℝ) + 1) (coeffOf φ) ≤ T := by
      rw [abs_one, one_mul]; exact hN
    nlinarith [e1, e2, e3]

end HRS.MC.Sec7.S7a

end
