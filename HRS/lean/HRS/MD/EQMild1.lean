import HRS.MD.EQRemInt13
import HRS.MD.EQRemBridge

/-!
# EQ-MILD, part 1: the stationary remainder as a centred modulated energy, and a pathwise bound for the modulated energy

* `eqmild_stat_formula`: for `C²` `φ` and EVERY configuration `X`,
  `𝓡_stat(φ)(X) = -√N (F_N^{h_φ}(X; μ_β) - E_{ℙ_{N,β}} F_N^{h_φ}(·; μ_β))` (the everywhere version of the bridge
  `eq_statRemainder_eq_neg_forcing_proof`, which is only stated almost everywhere).
* `eqmild_mE_bound`: `|F_N^h(Y; μ_β)| ≤ B 𝔅(Y)` for every `EnvGood s B h`, with `𝔅 ≥ 0` measurable and
  `ℙ_{N,β}`-integrable, independent of `h`.
* `eqmild_mE_meas`: measurability of `Y ↦ F_N^{h_φ}(Y; μ_β)`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MD.EQMild

open HRS HRS.MD.EQ29 HRS.MD.EQRem HRS.Quad

variable {d : ℕ} {s : ℝ}

/-- Everywhere version of the bridge: the stationary remainder is minus the centred modulated energy. -/
theorem eqmild_stat_formula (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ)
    (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) {ρβ : Torus d → ℝ}
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) {N : ℕ} (hN : 2 ≤ N) {φ : Torus d → ℝ}
    (hφ : Torus.IsCk 2 φ) (X : Config d N) :
    statRemainder d s V β ρβ (N := N) φ X =
      -(Real.sqrt N * (modulatedEnergy (pairKernel d s φ) X (withDensityReal ρβ) -
        ∫ Y, modulatedEnergy (pairKernel d s φ) Y (withDensityReal ρβ)
          ∂(canonicalGibbs (periodicRiesz d s) V N β))) := by
  obtain ⟨hprob, hμm, hmm, ⟨B, hB⟩, hqint⟩ := eqrem_context hd hs0 hsd V hV hβ hρβ hN hφ
  obtain ⟨hρs, Λ, hΛ0, hΛ, hP⟩ := eqrem_setup hd hs0 hsd V hV hβ hρβ
  have hN0 : 0 < N := by omega
  set G := canonicalGibbs (periodicRiesz d s) V N β with hG
  set μ := withDensityReal ρβ with hμdef
  set m := firstMarginal G with hmdef
  set h := pairKernel d s φ with hh
  set ψ : Torus d → ℝ := fun x => kernelField h μ x - kernelField h m x with hψ
  have hψm : Measurable ψ := hμm.sub hmm
  have hψint : ∀ i : Fin N, Integrable (fun X : Config d N => ψ (X i)) G := fun i =>
    Integrable.of_bound (hψm.comp (measurable_pi_apply i)).aestronglyMeasurable B
      (ae_of_all _ fun X => by simpa using hB (X i))
  have hmi : ∀ i : Fin N, G.map (fun X : Config d N => X i) = m := by
    intro i
    have := eqrem_marginal_eq hN0 (periodicRiesz d s) (fun x => periodicRiesz_neg x) β μ i
    rw [← hP N] at this
    exact this
  have hA : ∫ X, (1 / (N : ℝ)) * ∑ i, ψ (X i) ∂G = ∫ x, ψ x ∂m := by
    rw [integral_const_mul, integral_finset_sum _ (fun i _ => hψint i)]
    have : ∀ i : Fin N, ∫ X, ψ (X i) ∂G = ∫ x, ψ x ∂m := fun i => by
      rw [← hmi i]
      exact (integral_map (measurable_pi_apply i).aemeasurable hψm.aestronglyMeasurable).symm
    simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have hAint : Integrable (fun X : Config d N => (1 / (N : ℝ)) * ∑ i, ψ (X i)) G :=
    (integrable_finset_sum _ fun i _ => hψint i).const_mul _
  set c0 : ℝ := (∫ x, ∫ y, h x y ∂μ ∂μ) - ∫ x, ∫ y, h x y ∂m ∂m with hc0
  have hE : ∀ X : Config d N, modulatedEnergy h X μ =
      (1 / 2) * (quadStat h m X - 2 * ((1 / (N : ℝ)) * ∑ i, ψ (X i)) + c0) := by
    intro X
    rw [eqrem_modulatedEnergy_eq, eqrem_quadStat_split h μ m X]
  have hEint : ∫ X, modulatedEnergy h X μ ∂G =
      (1 / 2) * (∫ X, quadStat h m X ∂G - 2 * ∫ x, ψ x ∂m + c0) := by
    simp_rw [hE]
    have i2 : Integrable (fun X : Config d N => 2 * ((1 / (N : ℝ)) * ∑ i, ψ (X i))) G := hAint.const_mul 2
    have i1 : Integrable (fun X : Config d N => quadStat h m X - 2 * ((1 / (N : ℝ)) * ∑ i, ψ (X i))) G :=
      hqint.sub i2
    rw [integral_const_mul, integral_add i1 (integrable_const c0), integral_sub hqint i2,
      integral_const_mul, hA, integral_const]
    simp
  have e1 : ∫ x, (kernelField h μ x - kernelField h m x) ∂(empirical X) =
      (1 / (N : ℝ)) * ∑ i, ψ (X i) := by
    have := pair_empirical hN0 X ψ
    unfold pair at this
    rw [one_div]
    exact this
  show statRemainder d s V β ρβ (N := N) φ X =
    -(Real.sqrt N * (modulatedEnergy h X μ - ∫ ω', modulatedEnergy h ω' μ ∂G))
  rw [hEint, hE X]
  unfold statRemainder
  rw [e1]
  ring

/-- Measurability of the modulated energy against `μ_β` as a function of the configuration. -/
theorem eqmild_mE_meas (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ)
    (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) {ρβ : Torus d → ℝ}
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) {N : ℕ} (hN : 2 ≤ N) {φ : Torus d → ℝ}
    (hφ : Torus.IsCk 2 φ) :
    Measurable (fun Y : Config d N => modulatedEnergy (pairKernel d s φ) Y (withDensityReal ρβ)) := by
  obtain ⟨hprob, hμm, hmm, ⟨B, hB⟩, hqint⟩ := eqrem_context hd hs0 hsd V hV hβ hρβ hN hφ
  have hq := eqrem_quadStat_meas (N := N) (eqrem_pairKernel_meas hsd hφ) hμm
  have : (fun Y : Config d N => modulatedEnergy (pairKernel d s φ) Y (withDensityReal ρβ)) =
      fun Y => (1 / 2) * quadStat (pairKernel d s φ) (withDensityReal ρβ) Y := by
    funext Y; exact eqrem_modulatedEnergy_eq _ _ Y
  rw [this]
  exact measurable_const.mul hq

/-- `Qenv` is measurable. -/
theorem eqmild_Qenv_meas {N : ℕ} : Measurable (fun Y : Config d N => Qenv s Y) := by
  unfold Qenv
  refine measurable_const.mul (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_)
  have h1 : Measurable (fun X : Config d N => ((X i, X j) : Torus d × Torus d)) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply j)
  exact (envK_good (d := d) (s := s)).meas.comp h1

/-- Pathwise bound for the modulated energy against `μ_β` of an envelope-bounded kernel, with a dominating function that
does not depend on the kernel and is `ℙ_{N,β}`-integrable. -/
theorem eqmild_mE_bound (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ)
    (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) {ρβ : Torus d → ℝ}
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρβ) {N : ℕ} (hN : 2 ≤ N) :
    ∃ 𝔅 : Config d N → ℝ, Measurable 𝔅 ∧ (∀ Y, 0 ≤ 𝔅 Y) ∧
      Integrable 𝔅 (canonicalGibbs (periodicRiesz d s) V N β) ∧
      ∀ (B : ℝ) (h : Torus d → Torus d → ℝ), EnvGood s B h → ∀ Y : Config d N,
        |modulatedEnergy h Y (withDensityReal ρβ)| ≤ B * 𝔅 Y := by
  obtain ⟨hprob, hmprob, Λ, Λm, hΛ, hΛm, hμ, hm⟩ := eqrem_meas_bounds hd hs0 hsd V hV hβ hρ hN
  have hN0 : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  have hN1 : (0 : ℝ) < 1 / N := one_div_pos.2 hNR
  have hN2 : (0 : ℝ) < 1 / (N : ℝ) ^ 2 := one_div_pos.2 (pow_pos hNR 2)
  set G := canonicalGibbs (periodicRiesz d s) V N β with hG
  set m := firstMarginal G with hmdef
  set μ := withDensityReal ρβ with hμdef
  haveI hμprob : IsProbabilityMeasure μ := isProb_withDensityReal hρ.1
  set Ie : ℝ := ∫ z : Torus d, envT s z with hIe
  have hIe0 : 0 ≤ Ie := integral_nonneg fun z => show (0 : ℝ) ≤ envT s z by
    linarith [one_le_envT (s := s) z]
  have hQi := eqrem_Qenv_integrable hd hs0 hsd V hV hβ hρ hN
  refine ⟨fun Y => (1 / 2) * (Qenv s Y + 3 * Λm * Ie) + (3 / 2) * ((Λ + Λm) * Ie), ?_, ?_, ?_, ?_⟩
  · exact (measurable_const.mul (eqmild_Qenv_meas.add measurable_const)).add measurable_const
  · intro Y
    have := Qenv_nonneg (s := s) Y
    have h1 : 0 ≤ Λm * Ie := mul_nonneg hΛm hIe0
    have h2 : 0 ≤ Λ * Ie := mul_nonneg hΛ hIe0
    have h3 : 0 ≤ Λm * Ie := h1
    show 0 ≤ (1 / 2) * (Qenv s Y + 3 * Λm * Ie) + (3 / 2) * ((Λ + Λm) * Ie)
    nlinarith
  · exact (((hQi.add (integrable_const _)).const_mul (1 / 2)).add (integrable_const _))
  intro B h hg Y
  have hB := hg.hB
  have hemp : ∀ f : Torus d → ℝ, ∫ x, f x ∂(empirical Y) = (1 / (N : ℝ)) * ∑ i, f (Y i) := by
    intro f
    have := pair_empirical hN0 Y f
    unfold pair at this
    rw [one_div]; exact this
  have fμ : ∀ x, |∫ y, h x y ∂μ| ≤ Λ * (B * Ie) := fun x => (hg.fibre hd hs0 hsd hΛ hμ x).2
  have fm : ∀ x, |∫ y, h x y ∂m| ≤ Λm * (B * Ie) := fun x => (hg.fibre hd hs0 hsd hΛm hm x).2
  have hψ : ∀ x, |kernelField h μ x - kernelField h m x| ≤ B * ((Λ + Λm) * Ie) := by
    intro x
    refine (abs_sub _ _).trans ?_
    have := add_le_add (fμ x) (fm x)
    refine this.trans (le_of_eq ?_)
    ring
  have hN1' : (0 : ℝ) < 1 / N := hN1
  have hav : |(1 / (N : ℝ)) * ∑ i, (kernelField h μ (Y i) - kernelField h m (Y i))| ≤
      B * ((Λ + Λm) * Ie) := by
    rw [abs_mul, abs_of_pos hN1]
    have h1 : |∑ i, (kernelField h μ (Y i) - kernelField h m (Y i))| ≤ N * (B * ((Λ + Λm) * Ie)) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun i _ => hψ (Y i)).trans ?_
      simp
    calc 1 / (N : ℝ) * |∑ i, (kernelField h μ (Y i) - kernelField h m (Y i))|
        ≤ 1 / (N : ℝ) * (N * (B * ((Λ + Λm) * Ie))) := mul_le_mul_of_nonneg_left h1 hN1.le
      _ = _ := by field_simp
  have hq : |quadStat h m Y| ≤ B * (Qenv s Y + 3 * Λm * Ie) := by
    unfold quadStat
    have t1 : |(1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, h (Y i) (Y j)| ≤ B * Qenv s Y := by
      rw [abs_mul, abs_of_pos hN2]
      have h1 : |∑ i, ∑ j ∈ Finset.univ.erase i, h (Y i) (Y j)| ≤
          B * ∑ i, ∑ j ∈ Finset.univ.erase i, envK s (Y i) (Y j) := by
        calc |∑ i, ∑ j ∈ Finset.univ.erase i, h (Y i) (Y j)|
            ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, |h (Y i) (Y j)| := by
              refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
              exact Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, B * envK s (Y i) (Y j) :=
              Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hg.le_envK _ _
          _ = B * ∑ i, ∑ j ∈ Finset.univ.erase i, envK s (Y i) (Y j) := by
              simp only [← Finset.mul_sum]
      calc 1 / (N : ℝ) ^ 2 * |∑ i, ∑ j ∈ Finset.univ.erase i, h (Y i) (Y j)|
          ≤ 1 / (N : ℝ) ^ 2 * (B * ∑ i, ∑ j ∈ Finset.univ.erase i, envK s (Y i) (Y j)) :=
            mul_le_mul_of_nonneg_left h1 hN2.le
        _ = B * Qenv s Y := by unfold Qenv; ring
    have t2 : |2 * ((1 / (N : ℝ)) * ∑ i, ∫ y, h (Y i) y ∂m)| ≤ 2 * (Λm * (B * Ie)) := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_mul, abs_of_pos hN1]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      have h1 : |∑ i, ∫ y, h (Y i) y ∂m| ≤ N * (Λm * (B * Ie)) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine (Finset.sum_le_sum fun i _ => fm (Y i)).trans ?_
        simp
      calc 1 / (N : ℝ) * |∑ i, ∫ y, h (Y i) y ∂m| ≤ 1 / (N : ℝ) * (N * (Λm * (B * Ie))) :=
            mul_le_mul_of_nonneg_left h1 hN1.le
        _ = _ := by field_simp
    have t3 : |∫ x, ∫ y, h x y ∂m ∂m| ≤ Λm * (B * Ie) := by
      have := norm_integral_le_of_norm_le_const (μ := m) (f := fun x => ∫ y, h x y ∂m)
        (C := Λm * (B * Ie)) (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact fm x)
      rw [Real.norm_eq_abs, probReal_univ, mul_one] at this
      exact this
    calc |(1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, h (Y i) (Y j) -
          2 * ((1 / (N : ℝ)) * ∑ i, ∫ y, h (Y i) y ∂m) + ∫ x, ∫ y, h x y ∂m ∂m|
        ≤ |(1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, h (Y i) (Y j) -
          2 * ((1 / (N : ℝ)) * ∑ i, ∫ y, h (Y i) y ∂m)| + |∫ x, ∫ y, h x y ∂m ∂m| := abs_add_le _ _
      _ ≤ (|(1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, h (Y i) (Y j)| +
          |2 * ((1 / (N : ℝ)) * ∑ i, ∫ y, h (Y i) y ∂m)|) + |∫ x, ∫ y, h x y ∂m ∂m| :=
          add_le_add (abs_sub _ _) le_rfl
      _ ≤ (B * Qenv s Y + 2 * (Λm * (B * Ie))) + Λm * (B * Ie) :=
          add_le_add (add_le_add t1 t2) t3
      _ = _ := by ring
  have hc0 : |(∫ x, ∫ y, h x y ∂μ ∂μ) - ∫ x, ∫ y, h x y ∂m ∂m| ≤ B * ((Λ + Λm) * Ie) := by
    have a1 : |∫ x, ∫ y, h x y ∂μ ∂μ| ≤ Λ * (B * Ie) := by
      have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun x => ∫ y, h x y ∂μ)
        (C := Λ * (B * Ie)) (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact fμ x)
      rw [Real.norm_eq_abs, probReal_univ, mul_one] at this
      exact this
    have a2 : |∫ x, ∫ y, h x y ∂m ∂m| ≤ Λm * (B * Ie) := by
      have := norm_integral_le_of_norm_le_const (μ := m) (f := fun x => ∫ y, h x y ∂m)
        (C := Λm * (B * Ie)) (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact fm x)
      rw [Real.norm_eq_abs, probReal_univ, mul_one] at this
      exact this
    refine (abs_sub _ _).trans ?_
    have := add_le_add a1 a2
    refine this.trans (le_of_eq ?_)
    ring
  -- assemble
  rw [eqrem_modulatedEnergy_eq, eqrem_quadStat_split h μ m Y]
  set q := quadStat h m Y
  set a := (1 / (N : ℝ)) * ∑ i, (kernelField h μ (Y i) - kernelField h m (Y i)) with ha
  set c := (∫ x, ∫ y, h x y ∂μ ∂μ) - ∫ x, ∫ y, h x y ∂m ∂m with hc
  have hq' := abs_le.1 hq
  have ha' := abs_le.1 hav
  have hc' := abs_le.1 hc0
  rw [abs_le]
  constructor <;> nlinarith [hq'.1, hq'.2, ha'.1, ha'.2, hc'.1, hc'.2]

end HRS.MD.EQMild

end
