import HRS.MS.R2GenInitAux2

/-!
# S10.5 packet G1a: the expected corrected energy from the entropy bound

`s105_energy_moment`: if `H(f | Q_{N,β}(ρ dx)) ≤ H_b` then `E_f (F_N + o_N)_+ ≤ C (H_b/N + δ_N) + o_N` (`E 𝖾_N^t ≤ E_N`, S L8460-8466), from
`euclidean_pair_entropy_self` (`|F_N| = N⁻¹ · N|F_N|`, `F_N + o_N ≤ |F_N| + o_N`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Function Set
open scoped ENNReal NNReal

namespace HRS.MS.R2GenInit

open HRS.Whole HRS.MS.Wr HRS.MS.R2WinErr

variable {d : ℕ}

theorem s105_energy_moment (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (M L β : ℝ) (hβ : 0 < β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      (s = 0 → HasLogMoment (HRS.Whole.withDensityReal ρ) L) → ∀ N : ℕ, 2 ≤ N →
      ∀ f : Measure (EucConfig d N), IsProbabilityMeasure f → ∀ Hb : ℝ, 0 ≤ Hb →
      HRS.relEntropy f (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β
        (HRS.Whole.withDensityReal ρ)) ≤ ENNReal.ofReal Hb →
      ∀ C₀ : ℝ, 0 ≤ C₀ →
        ∫⁻ Z, ENNReal.ofReal (rieszModulatedEnergy d s Z (HRS.Whole.withDensityReal ρ) +
            HRS.oN d s C₀ N) ∂f ≤
          ENNReal.ofReal (C * (Hb / N + deltaN d s N) + HRS.oN d s C₀ N) := by
  obtain ⟨c, hc, CE, hS⟩ := euclidean_pair_entropy_self_proof hd hs0 hsd M L β (β + 1) hβ (by linarith)
  set CE' : ℝ := max CE 0 with hCE'
  have hCE'0 : 0 ≤ CE' := le_max_right _ _
  refine ⟨CE', hCE'0, ?_⟩
  intro ρ hρ hρM hlog N hN f hf Hb hHb0 hH C₀ hC₀
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := Q34.isProbabilityMeasure_nu hρ
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hHfin : HRS.relEntropy f (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β
      (HRS.Whole.withDensityReal ρ)) < ⊤ := lt_of_le_of_lt hH ENNReal.ofReal_lt_top
  obtain ⟨hint, hbd⟩ := (hS ρ hρ hρM hlog N hN β ⟨le_rfl, by linarith⟩).2 f hf hHfin
  have hT1 : (0 : ℝ) ≤ (N : ℝ) * deltaN d s N :=
    mul_nonneg hN0.le (HRS.MS.S53.s53_deltaN_nonneg s (by omega))
  have hKL : (HRS.relEntropy f (HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β
      (HRS.Whole.withDensityReal ρ))).toReal ≤ Hb := ENNReal.toReal_le_of_le_ofReal hHb0 hH
  have hint' : Integrable (fun Z : EucConfig d N =>
      |rieszModulatedEnergy d s Z (HRS.Whole.withDensityReal ρ)|) f := by
    refine (hint.const_mul ((N : ℝ)⁻¹)).congr (Filter.Eventually.of_forall fun Z => ?_)
    simp only
    rw [← mul_assoc, inv_mul_cancel₀ hN0.ne', one_mul]
    rfl
  have hI : ∫ Z, |rieszModulatedEnergy d s Z (HRS.Whole.withDensityReal ρ)| ∂f ≤
      CE' * (Hb / N + deltaN d s N) := by
    have h1 : ∫ Z, |rieszModulatedEnergy d s Z (HRS.Whole.withDensityReal ρ)| ∂f =
        (N : ℝ)⁻¹ * ∫ Z, (N : ℝ) * |rieszModulatedEnergy d s Z (HRS.Whole.withDensityReal ρ)| ∂f := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun Z => ?_)
      simp only
      rw [← mul_assoc, inv_mul_cancel₀ hN0.ne', one_mul]
    rw [h1]
    have h2 : ∫ Z, (N : ℝ) * |rieszModulatedEnergy d s Z (HRS.Whole.withDensityReal ρ)| ∂f ≤
        CE' * (Hb + (N : ℝ) * deltaN d s N) :=
      hbd.trans (mul_le_mul (le_max_left _ _) (by linarith) (add_nonneg ENNReal.toReal_nonneg hT1) hCE'0)
    calc (N : ℝ)⁻¹ * ∫ Z, (N : ℝ) * |rieszModulatedEnergy d s Z (HRS.Whole.withDensityReal ρ)| ∂f
        ≤ (N : ℝ)⁻¹ * (CE' * (Hb + (N : ℝ) * deltaN d s N)) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = CE' * (Hb / N + deltaN d s N) := by field_simp
  have hoN0 := s104_oN_nonneg d s C₀ hC₀ N
  have hmeas : AEMeasurable (fun Z : EucConfig d N =>
      ENNReal.ofReal |rieszModulatedEnergy d s Z (HRS.Whole.withDensityReal ρ)|) f :=
    hint'.aemeasurable.ennreal_ofReal
  calc ∫⁻ Z, ENNReal.ofReal (rieszModulatedEnergy d s Z (HRS.Whole.withDensityReal ρ) +
          HRS.oN d s C₀ N) ∂f
      ≤ ∫⁻ Z, (ENNReal.ofReal |rieszModulatedEnergy d s Z (HRS.Whole.withDensityReal ρ)| +
          ENNReal.ofReal (HRS.oN d s C₀ N)) ∂f := by
        refine lintegral_mono fun Z => ?_
        rw [← ENNReal.ofReal_add (abs_nonneg _) hoN0]
        exact ENNReal.ofReal_le_ofReal (by linarith [le_abs_self (rieszModulatedEnergy d s Z (HRS.Whole.withDensityReal ρ))])
    _ = ∫⁻ Z, ENNReal.ofReal |rieszModulatedEnergy d s Z (HRS.Whole.withDensityReal ρ)| ∂f +
          ENNReal.ofReal (HRS.oN d s C₀ N) := by
        rw [lintegral_add_right' _ aemeasurable_const, lintegral_const, measure_univ, mul_one]
    _ ≤ ENNReal.ofReal (CE' * (Hb / N + deltaN d s N)) + ENNReal.ofReal (HRS.oN d s C₀ N) := by
        refine add_le_add ?_ le_rfl
        rw [← ofReal_integral_eq_lintegral_ofReal hint' (Filter.Eventually.of_forall fun Z => abs_nonneg _)]
        exact ENNReal.ofReal_le_ofReal hI
    _ = _ := by
        rw [← ENNReal.ofReal_add (mul_nonneg hCE'0 (add_nonneg (div_nonneg hHb0 hN0.le) (HRS.MS.S53.s53_deltaN_nonneg s (by omega)))) hoN0]

end HRS.MS.R2GenInit
