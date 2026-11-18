import HRS.MS.R2GenInitAux9

/-!
# S10.5 input `hmom` for the stationary trajectory (assembly)

`s105_hmom_stat`: `∫⁻ ofReal (N⁻¹∑|x_i(t)|²) ≤ C_m (1 + B_N/N)` uniformly in `t ≥ 0`, `B_N = 1 + H_{N,0} + Nδ_N`, along the stationary dynamics
from an initial law of finite entropy (clause `S105Moment` for `ρ = fun _ => ρ_β`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Function Set
open scoped ENNReal NNReal

namespace HRS.MS.R2GenInit

open HRS.Whole

variable {d : ℕ}

theorem s105_hmom_stat (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) :
    ∃ Cm : ℝ, 0 ≤ Cm ∧ ∀ ρβ : Euc d → ℝ, IsThermalEquilibrium d s a β ρβ → ∀ N : ℕ, 2 ≤ N →
      GibbsEntropyContraction d s a β N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N),
      IsR2Realization d s a β P X₀ W X →
      HRS.relEntropy (HRS.law P X₀) (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β
        (HRS.Whole.withDensityReal ((fun _ : ℝ => ρβ) 0))) < ⊤ →
      ∀ t : ℝ, 0 ≤ t → ∫⁻ ζ, ENNReal.ofReal (movSecondMoment (X t.toNNReal ζ)) ∂P ≤
        ENNReal.ofReal (Cm * (1 + (1 + (HRS.relEntropy (HRS.law P X₀)
          (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β
            (HRS.Whole.withDensityReal ((fun _ : ℝ => ρβ) 0)))).toReal + N * deltaN d s N) / N)) := by
  by_cases hex : ∃ ρ0 : Euc d → ℝ, IsThermalEquilibrium d s a β ρ0
  swap
  · exact ⟨0, le_rfl, fun ρβ h => absurd ⟨ρβ, h⟩ hex⟩
  obtain ⟨ρ0, hρ0⟩ := hex
  obtain ⟨Λ, hΛ⟩ := HRS.MS.S21.s21_thermal_bounded hd hs0 hsd ha hβ
  obtain ⟨hp0, hb0, hl0⟩ := hΛ ρ0 hρ0
  have hρeq : ρ0 = thermalDensity d s a β := HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρ0
  obtain ⟨C, c, BU, hT⟩ := S45.s45_thermal_data hd hs0 hsd ha hβ
  set L : ℝ := ∫ x, Real.log (2 + ‖x‖) ∂(HRS.Whole.withDensityReal ρ0) with hL
  obtain ⟨C₁, hC₁0, hkl⟩ := s105_kl_product hd s hs0 hsd Λ L β hβ
  have hc2 : 0 < c / 2 := by have := hT.hc; positivity
  have hbd : ∀ x, ρ0 x ≤ C * Real.exp (-(c * ‖x‖ ^ 2)) := fun x => by
    rw [hρeq]
    have := (le_abs_self _).trans (hT.h0 x)
    simpa [neg_mul] using this
  have hexp := s105_exp_moment_gauss hp0 hT.C0 hT.hc hbd
  set Z : ℝ := max 1 (C * ∫ x : Euc d, Real.exp (-((c / 2) * ‖x‖ ^ 2))) with hZ
  have hZ1 : 1 ≤ Z := le_max_left _ _
  refine ⟨(c / 2)⁻¹ * max (2 * C₁) Z, by positivity, ?_⟩
  intro ρβ hρβ N hN hGib Ω _ P _ X₀ W X hreal hfin t ht
  have hρβeq : ρβ = ρ0 := by
    rw [HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρβ, hρeq]
  subst hρβeq
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hδ : 0 ≤ deltaN d s N := HRS.MS.S53.s53_deltaN_nonneg s (by omega)
  have hNδ : 0 ≤ (N : ℝ) * deltaN d s N := mul_nonneg hN0.le hδ
  have hXm : Measurable (X t.toNNReal) := (hreal.solution t).adapted _
  haveI : IsProbabilityMeasure (P.map (X t.toNNReal)) :=
    ⟨by rw [Measure.map_apply hXm MeasurableSet.univ]; simp⟩
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρβ) := Q34.isProbabilityMeasure_nu hp0
  set h0 : ℝ := (HRS.relEntropy (HRS.law P X₀) (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β
    (HRS.Whole.withDensityReal ((fun _ : ℝ => ρβ) 0)))).toReal with hh0
  have hh00 : 0 ≤ h0 := ENNReal.toReal_nonneg
  have hent := s105_hent_stat hd hs0 hsd ha hβ hρβ hN hGib P hreal hfin t ht
  have hlogm : s = 0 → HasLogMoment (HRS.Whole.withDensityReal ρβ) L := fun _ => ⟨hl0, le_rfl⟩
  obtain ⟨hπne, hπ⟩ := hkl ρβ hp0 hb0 hlogm N hN (P.map (X t.toNNReal)) inferInstance (h0 + N * deltaN d s N)
    (by linarith) (by rw [one_mul] at hent; exact hent)
  have hsm := s105_second_moment_of_kl (μ := HRS.Whole.withDensityReal ρβ) (by omega : 0 < N) hc2 hZ1 hexp P
    (X t.toNNReal) hXm hπne
  refine hsm.trans (ENNReal.ofReal_le_ofReal ?_)
  set q : ℝ := (1 + h0 + N * deltaN d s N) / N with hq
  have hq0 : 0 ≤ q := by positivity
  have hkq : (InformationTheory.klDiv (P.map (X t.toNNReal))
      (Measure.pi fun _ : Fin N => HRS.Whole.withDensityReal ρβ)).toReal / N ≤ 2 * C₁ * q := by
    rw [div_le_iff₀ hN0, hq]
    have : (1 + h0 + N * deltaN d s N) / N * N = 1 + h0 + N * deltaN d s N := by field_simp
    nlinarith [hπ, mul_nonneg hC₁0 hNδ, mul_nonneg hC₁0 hh00, hC₁0]
  have hmx : 2 * C₁ ≤ max (2 * C₁) Z := le_max_left _ _
  have hmz : Z ≤ max (2 * C₁) Z := le_max_right _ _
  have hm0 : 0 ≤ max (2 * C₁) Z := (by positivity : 0 ≤ 2 * C₁).trans hmx
  have : 2 * C₁ * q + Z ≤ max (2 * C₁) Z * (1 + q) := by nlinarith
  have hpos : 0 ≤ (c / 2)⁻¹ := by positivity
  calc (c / 2)⁻¹ * ((InformationTheory.klDiv (P.map (X t.toNNReal))
        (Measure.pi fun _ : Fin N => HRS.Whole.withDensityReal ρβ)).toReal / N + Z)
      ≤ (c / 2)⁻¹ * (2 * C₁ * q + Z) := mul_le_mul_of_nonneg_left (by linarith) hpos
    _ ≤ (c / 2)⁻¹ * (max (2 * C₁) Z * (1 + q)) := mul_le_mul_of_nonneg_left this hpos
    _ = (c / 2)⁻¹ * max (2 * C₁) Z * (1 + q) := by ring

end HRS.MS.R2GenInit
