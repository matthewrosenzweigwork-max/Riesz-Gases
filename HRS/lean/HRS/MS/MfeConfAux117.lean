import HRS.MS.MfeConfAux116

/-!
# S.B.1, packet F9 (part 20): uniform bounds of envelope-controlled means under the dominated laws

`sb1_env_mean_le`: if `0 ≤ F ≤ K (A (P_M + ℓ) + A₂)` is measurable then `∫ F dμ^M ≤ c · τ · J` uniformly in `M`, where
`J = ∫ e^{βN(|Z|+1/2)} e^{-βΣV}` is a fixed Gaussian integral (canonical-Gibbs domination `μ^M ≤ c e^{-βH_M} dX`).
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d N : ℕ}

section Main

variable {D : Whole.WholeDyn d} {T C B C3 : ℝ} {ρ : ℝ → Euc d → ℝ} (H : Sb1Tr3 D T C B C3 ρ)

include H

/-- uniform mean bound for envelope-controlled functions: integrable, and `∫ F dμ^M ≤ C_b K` -/
theorem sb1_env_mean_le (hN : 1 ≤ N) (hβ : 0 < D.invβ) {cV CV : ℝ} (hcV : 0 < cV)
    (hV : ∀ x, cV * ‖x‖ ^ 2 - CV ≤ D.V x) {A1 A2 : ℝ} (hA1 : 0 < A1) (hA2 : 0 ≤ A2)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ι : Type*} (κ : ι → ℕ) (Y : ι → Ω → Whole.EucConfig d N) (hY : ∀ i, Measurable (Y i)) (c : ℝ)
    (hdom : ∀ i, P.map (Y i) ≤ ENNReal.ofReal c •
      sb1Dm (fun Z => Real.exp (-D.invβ⁻¹ * sb1Hs D (sb1kM d D.s (κ i)) N Z))) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ {Kr : ℝ}, 0 < Kr → ∀ (i : ι) (F : Whole.EucConfig d N → ℝ), Measurable F →
      (∀ Z, 0 ≤ F Z) → (∀ Z, F Z ≤ Kr * (A1 * (sb1PM (sb1kM d D.s (κ i)) N Z + sb1ell d N Z) + A2)) →
      Integrable F (P.map (Y i)) ∧ ∫ Z, F Z ∂(P.map (Y i)) ≤ Cb * Kr := by
  have hs0 := H.tr.hs0
  have hβ0 : 0 < D.invβ⁻¹ := inv_pos.2 hβ
  set β := D.invβ⁻¹ with hβdef
  set Nr : ℝ := (N : ℝ) with hNr
  have hNr0 : 0 < Nr := Nat.cast_pos.2 (by omega)
  have hVm : Measurable D.V := H.tr.V.c3.continuous.measurable
  set Φ0 : Whole.EucConfig d N → ℝ := fun Z => Real.exp (β * Nr * (‖Z‖ + 1 / 2)) * Real.exp (-β * ∑ i, D.V (Z i)) with hΦ0
  have hΦi : Integrable Φ0 volume := sb1_Phi_int hVm hcV hV hβ0 hN
  set J : ℝ≥0∞ := ∫⁻ Z, ENNReal.ofReal (Φ0 Z) with hJ
  have hJtop : J < ⊤ := hΦi.lintegral_lt_top
  set τ1 : ℝ := (2 / (β * Nr / A1)) * Real.exp (β * Nr * A2 / A1) with hτ1
  have hτ10 : 0 ≤ τ1 := by positivity
  refine ⟨|c| * τ1 * J.toReal, by positivity, fun {Kr} hKr i F hFm hF0 hFb => ?_⟩
  set τ : ℝ := Kr * τ1 with hτ
  have hτ0 : 0 ≤ τ := by positivity
  have hpt : ∀ Z, F Z * Real.exp (-D.invβ⁻¹ * sb1Hs D (sb1kM d D.s (κ i)) N Z) ≤ τ * Φ0 Z := by
    intro Z
    have := sb1_real_tail (β := β) (Nr := Nr) (A1 := A1) (A2 := A2) (Kr := Kr) (L := 0)
      (PM := sb1PM (sb1kM d D.s (κ i)) N Z) (ell := sb1ell d N Z) (SV := ∑ i, D.V (Z i)) (zn := ‖Z‖)
      (Cabs := F Z) hβ0 hNr0 hA1 hA2 hKr (hF0 Z) (hFb Z) (sb1_ell_le hN Z) (hF0 Z) le_rfl
    rw [← sb1_Hs_eq D (sb1kM d D.s (κ i)) hN Z] at this
    have e : Kr * (2 / (β * Nr / A1)) * Real.exp (β * Nr * A2 / A1) * Real.exp (-(β * Nr / A1) * (0 / Kr) / 2) = τ := by
      simp [hτ, hτ1]; ring
    rw [e] at this
    exact this
  have hmeas : Measurable fun Z : Whole.EucConfig d N =>
      ENNReal.ofReal (Real.exp (-D.invβ⁻¹ * sb1Hs D (sb1kM d D.s (κ i)) N Z)) :=
    (Real.measurable_exp.comp (measurable_const.mul
      (sb1_Hs_cont D (sb1kM_isKernel D.s hs0 (κ i)) H.tr.V N).measurable)).ennreal_ofReal
  have hl : ∫⁻ Z, ENNReal.ofReal (F Z) ∂(P.map (Y i)) ≤ ENNReal.ofReal c * (ENNReal.ofReal τ * J) := by
    calc ∫⁻ Z, ENNReal.ofReal (F Z) ∂(P.map (Y i)) ≤
          ∫⁻ Z, ENNReal.ofReal (F Z) ∂(ENNReal.ofReal c • sb1Dm (fun Z => Real.exp (-D.invβ⁻¹ * sb1Hs D (sb1kM d D.s (κ i)) N Z))) :=
            lintegral_mono' (hdom i) le_rfl
      _ = ENNReal.ofReal c * ∫⁻ Z, ENNReal.ofReal (F Z) *
            ENNReal.ofReal (Real.exp (-D.invβ⁻¹ * sb1Hs D (sb1kM d D.s (κ i)) N Z)) := by
            rw [lintegral_smul_measure, smul_eq_mul]
            congr 1
            unfold sb1Dm
            rw [lintegral_withDensity_eq_lintegral_mul (f := fun z => ENNReal.ofReal
              (Real.exp (-D.invβ⁻¹ * sb1Hs D (sb1kM d D.s (κ i)) N z))) _ hmeas hFm.ennreal_ofReal]
            refine lintegral_congr fun z => ?_
            simp [mul_comm]
      _ ≤ ENNReal.ofReal c * ∫⁻ Z, ENNReal.ofReal (τ * Φ0 Z) := by
            gcongr with Z
            rw [← ENNReal.ofReal_mul (hF0 Z)]
            exact ENNReal.ofReal_le_ofReal (hpt Z)
      _ = ENNReal.ofReal c * (ENNReal.ofReal τ * J) := by
            congr 1
            have : ∀ z, ENNReal.ofReal (τ * Φ0 z) = ENNReal.ofReal τ * ENNReal.ofReal (Φ0 z) := fun z =>
              ENNReal.ofReal_mul hτ0
            simp_rw [this]
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hfin : ENNReal.ofReal c * (ENNReal.ofReal τ * J) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hJtop.ne)
  refine ⟨⟨hFm.aestronglyMeasurable, ?_⟩, ?_⟩
  · unfold HasFiniteIntegral
    refine lt_of_le_of_lt (le_of_eq ?_) (lt_of_le_of_lt hl hfin.lt_top)
    refine lintegral_congr fun Z => ?_
    rw [Real.enorm_eq_ofReal (hF0 Z)]
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hF0) hFm.aestronglyMeasurable]
  calc (∫⁻ Z, ENNReal.ofReal (F Z) ∂(P.map (Y i))).toReal ≤ (ENNReal.ofReal c * (ENNReal.ofReal τ * J)).toReal :=
        ENNReal.toReal_mono hfin hl
    _ = max c 0 * (τ * J.toReal) := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal', ENNReal.toReal_ofReal hτ0]
    _ ≤ |c| * τ1 * J.toReal * Kr := by
        have h1 : max c 0 ≤ |c| := max_le (le_abs_self c) (abs_nonneg c)
        have h2 : 0 ≤ τ * J.toReal := mul_nonneg hτ0 ENNReal.toReal_nonneg
        have : max c 0 * (τ * J.toReal) ≤ |c| * (τ * J.toReal) := mul_le_mul_of_nonneg_right h1 h2
        refine this.trans (le_of_eq ?_)
        simp only [hτ]; ring

end Main

end HRS.MS.MfeConf
