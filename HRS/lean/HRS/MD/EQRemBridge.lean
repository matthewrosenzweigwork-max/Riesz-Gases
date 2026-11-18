import HRS.MD.EQRemSetup
import HRS.Equilibrium.Q32cAux2

/-!
# EQ-REM bridge: `statRemainder φ = - centeredCommutatorForcing` (`eq_statRemainder_eq_neg_forcing_proof`)
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MD.EQRem

open HRS HRS.MD.EQ29

variable {d : ℕ} {s : ℝ}

/-- `quadStat` is measurable in the configuration. -/
theorem eqrem_quadStat_meas {N : ℕ} {h : Torus d → Torus d → ℝ} (hh : Measurable (Function.uncurry h))
    {ν : Measure (Torus d)} (hk : Measurable (kernelField h ν)) :
    Measurable (fun X : Config d N => quadStat h ν X) := by
  unfold quadStat
  have h1 : Measurable (fun X : Config d N => ∑ i, ∑ j ∈ Finset.univ.erase i, h (X i) (X j)) := by
    refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
    exact (hh.comp ((measurable_pi_apply i).prodMk (measurable_pi_apply j)) :
      Measurable fun X : Config d N => Function.uncurry h (X i, X j))
  have h2 : Measurable (fun X : Config d N => ∑ i, ∫ y, h (X i) y ∂ν) :=
    Finset.measurable_sum _ fun i _ => hk.comp (measurable_pi_apply i)
  exact ((measurable_const.mul h1).sub (measurable_const.mul (measurable_const.mul h2))).add measurable_const

/-- Pointwise algebra: `D_N(h;μ) = D_N(h;m) - 2 N⁻¹ ∑ ψ(x_i) + c` with `ψ = H_μ - H_m`. -/
theorem eqrem_quadStat_split {N : ℕ} (h : Torus d → Torus d → ℝ) (μ m : Measure (Torus d)) (X : Config d N) :
    quadStat h μ X = quadStat h m X
      - 2 * ((1 / (N : ℝ)) * ∑ i, (kernelField h μ (X i) - kernelField h m (X i)))
      + ((∫ x, ∫ y, h x y ∂μ ∂μ) - ∫ x, ∫ y, h x y ∂m ∂m) := by
  unfold quadStat
  simp only [kernelField, Finset.sum_sub_distrib]
  ring

theorem eqrem_modulatedEnergy_eq {N : ℕ} (h : Torus d → Torus d → ℝ) (μ : Measure (Torus d)) (X : Config d N) :
    modulatedEnergy h X μ = (1 / 2) * quadStat h μ X := by
  unfold modulatedEnergy quadStat
  ring

/-- Exchangeability: every coordinate has the first-marginal law. -/
theorem eqrem_marginal_eq {N : ℕ} (hN : 0 < N) (g : Torus d → ℝ) (hg : ∀ x, g (-x) = g x) (β : ℝ)
    (μ : Measure (Torus d)) (i : Fin N) :
    (modulatedGibbs g N β μ).map (fun X : Config d N => X i) = firstMarginal (modulatedGibbs g N β μ) := by
  have hex := modulatedGibbs_isExchangeable (N := N) g β μ hg
  unfold firstMarginal
  rw [dif_pos hN]
  exact External.Entropy.IsExchangeable.marginal_eq hex i ⟨0, hN⟩


/-- Common context for a thermal density at one `β`, `N ≥ 2` and a `C²` test function: the Gibbs law is a probability measure,
both kernel fields are measurable and bounded, and `D_N(h_φ; m_N)` is integrable. -/
theorem eqrem_context (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ) (hV : Torus.IsSmooth V)
    {β : ℝ} (hβ : 0 < β) {ρβ : Torus d → ℝ} (hρ : IsThermalDensity (periodicRiesz d s) V β ρβ)
    {N : ℕ} (hN : 2 ≤ N) {φ : Torus d → ℝ} (hφ : Torus.IsCk 2 φ) :
    IsProbabilityMeasure (canonicalGibbs (periodicRiesz d s) V N β) ∧
    Measurable (kernelField (pairKernel d s φ) (withDensityReal ρβ)) ∧
    Measurable (kernelField (pairKernel d s φ) (firstMarginal (canonicalGibbs (periodicRiesz d s) V N β))) ∧
    (∃ B : ℝ, ∀ x, |kernelField (pairKernel d s φ) (withDensityReal ρβ) x -
      kernelField (pairKernel d s φ) (firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)) x| ≤ B) ∧
    Integrable (fun X : Config d N => quadStat (pairKernel d s φ)
      (firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)) X)
      (canonicalGibbs (periodicRiesz d s) V N β) := by
  obtain ⟨hρs, Λ, hΛ0, hΛ, hP⟩ := eqrem_setup hd hs0 hsd V hV hβ hρ
  obtain ⟨Mp, hMp0, hMp⟩ := eqrem_marginal_le hd hs0 hsd V hV hβ hρ
  obtain ⟨C₁, hC₁, hkf⟩ := eqrem_kernelField_bdd hd hs0 hsd
  have hN0 : 0 < N := by omega
  have hμ : withDensityReal ρβ ≤ ENNReal.ofReal Λ • (volume : Measure (Torus d)) := eqrem_mu_le_vol hΛ
  have hm : firstMarginal (canonicalGibbs (periodicRiesz d s) V N β) ≤
      ENNReal.ofReal (Mp * Λ) • (volume : Measure (Torus d)) := by
    refine (hMp N hN).trans ?_
    calc ENNReal.ofReal Mp • withDensityReal ρβ ≤ ENNReal.ofReal Mp • (ENNReal.ofReal Λ • (volume : Measure (Torus d))) := by
          refine Measure.le_iff'.2 fun A => ?_
          have := Measure.le_iff'.1 hμ A
          rw [Measure.smul_apply, smul_eq_mul] at this
          rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
          exact mul_le_mul' le_rfl this
      _ = ENNReal.ofReal (Mp * Λ) • (volume : Measure (Torus d)) := by
          rw [smul_smul, ENNReal.ofReal_mul hMp0]
  obtain ⟨hμm, hμb⟩ := hkf φ hφ _ Λ hΛ0 hμ
  obtain ⟨hmm, hmb⟩ := hkf φ hφ _ (Mp * Λ) (mul_nonneg hMp0 hΛ0) hm
  have hprob : IsProbabilityMeasure (canonicalGibbs (periodicRiesz d s) V N β) := by
    rw [hP N]
    exact Q32c.q32c_Q_isProb hd hs0 hsd hβ (Λ := max Λ 1) (le_max_right _ _) hρs.density
      (fun x => (hΛ x).trans (le_max_left _ _)) hN0
  refine ⟨hprob, hμm, hmm, ⟨Λ * (C₁ * Torus.cbNorm 2 φ) + Mp * Λ * (C₁ * Torus.cbNorm 2 φ), fun x => ?_⟩, ?_⟩
  · exact (abs_sub _ _).trans (add_le_add (hμb x) (hmb x))
  · -- integrability from the finite variance
    obtain ⟨Cq, hCq0, hCq⟩ := EQStat.eq_static_quadratic_proof hd hs0 hsd V hV β β hβ le_rfl
    obtain ⟨B₀, hB₀0, hB₀⟩ := eqrem_pairKernel_env hd hs0 hsd
    have hmeas := eqrem_quadStat_meas (N := N) (eqrem_pairKernel_meas hsd hφ) hmm
    have hvar := hCq β ⟨le_rfl, le_rfl⟩ ρβ hρ (B₀ * Torus.cbNorm 2 φ) (pairKernel d s φ)
      (eqrem_pairKernel_meas hsd hφ) (eqrem_pairKernel_symm hsd φ)
      (fun x y hxy => hB₀ φ hφ x y hxy) N hN _ (Or.inr rfl)
    have hlt : evariance (fun X : Config d N => quadStat (pairKernel d s φ)
        (firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)) X)
        (canonicalGibbs (periodicRiesz d s) V N β) < ⊤ := by
      refine lt_of_le_of_lt ?_ (lt_of_le_of_lt hvar ENNReal.ofReal_lt_top)
      refine le_mul_of_one_le_left bot_le ?_
      exact_mod_cast (by omega : 1 ≤ N)
    have := hprob
    exact ((evariance_lt_top_iff_memLp hmeas.aestronglyMeasurable).1 hlt).integrable one_le_two


/-- (Bridge for EQ-REM; TeX L4009-4017 versus `Q:eq:normal-form` L4914-4918.)  The stationary remainder is minus the centered commutator
forcing of Proposition 4.17. -/
theorem eq_statRemainder_eq_neg_forcing_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (β : ℝ) (hβ : 0 < β) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) {N : ℕ} (hN : 2 ≤ N)
    (φ : Torus d → ℝ) (hφ : Torus.IsCk 2 φ) :
    ∀ᵐ X ∂(canonicalGibbs (periodicRiesz d s) V N β),
      statRemainder d s V β ρβ (N := N) φ X =
        -centeredCommutatorForcing d s (canonicalGibbs (periodicRiesz d s) V N β)
          (fun _ => withDensityReal ρβ) (fun (_ : ℝ≥0) (Y : Config d N) => Y) φ 0 X := by
  obtain ⟨hprob, hμm, hmm, ⟨B, hB⟩, hqint⟩ := eqrem_context hd hs0 hsd V hV hβ hρβ hN hφ
  obtain ⟨hρs, Λ, hΛ0, hΛ, hP⟩ := eqrem_setup hd hs0 hsd V hV hβ hρβ
  have hN0 : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
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
  have hE : ∀ X : Config d N, modulatedEnergy (commKernel (periodicRieszGrad d s) (Torus.grad φ)) X μ =
      (1 / 2) * (quadStat h m X - 2 * ((1 / (N : ℝ)) * ∑ i, ψ (X i)) + c0) := by
    intro X
    rw [show commKernel (periodicRieszGrad d s) (Torus.grad φ) = h from rfl,
      eqrem_modulatedEnergy_eq, eqrem_quadStat_split h μ m X]
  have hEint : ∫ X, modulatedEnergy (commKernel (periodicRieszGrad d s) (Torus.grad φ)) X μ ∂G =
      (1 / 2) * (∫ X, quadStat h m X ∂G - 2 * ∫ x, ψ x ∂m + c0) := by
    simp_rw [hE]
    have i2 : Integrable (fun X : Config d N => 2 * ((1 / (N : ℝ)) * ∑ i, ψ (X i))) G := hAint.const_mul 2
    have i1 : Integrable (fun X : Config d N => quadStat h m X - 2 * ((1 / (N : ℝ)) * ∑ i, ψ (X i))) G :=
      hqint.sub i2
    rw [integral_const_mul, integral_add i1 (integrable_const c0), integral_sub hqint i2,
      integral_const_mul, hA, integral_const]
    simp
  refine Filter.Eventually.of_forall fun X => ?_
  have e1 : ∫ x, (kernelField h μ x - kernelField h m x) ∂(empirical X) =
      (1 / (N : ℝ)) * ∑ i, ψ (X i) := by
    have := pair_empirical hN0 X ψ
    unfold pair at this
    rw [one_div]
    exact this
  show statRemainder d s V β ρβ (N := N) φ X =
    -(Real.sqrt N * (modulatedEnergy (commKernel (periodicRieszGrad d s) (Torus.grad φ)) X μ -
      ∫ ω', modulatedEnergy (commKernel (periodicRieszGrad d s) (Torus.grad φ)) ω' μ ∂G))
  rw [hEint, hE X]
  unfold statRemainder
  rw [e1]
  ring

end HRS.MD.EQRem

end
