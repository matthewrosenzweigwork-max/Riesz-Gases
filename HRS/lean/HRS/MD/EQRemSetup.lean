import HRS.MD.EQRemKernel
import HRS.MD.EQStatQuadratic
import HRS.Equilibrium.MarginalDensity
import HRS.Equilibrium.Q32cAux2

/-!
# EQ-REM, part 2: the thermal setup at fixed `β`, density bound of the first marginal, bounded kernel fields
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MD.EQRem

open HRS HRS.MD.EQ29 HRS.PoleCavityAux HRS.MarginalAux

variable {d : ℕ} {s : ℝ}

/-- Thermal setup at one `β`: smooth positive density, `canonicalGibbs = modulatedGibbs`. -/
theorem eqrem_setup (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ) (hV : Torus.IsSmooth V)
    {β : ℝ} (hβ : 0 < β) {ρβ : Torus d → ℝ} (hρ : IsThermalDensity (periodicRiesz d s) V β ρβ) :
    ∃ hρs : SmoothPosDensity ρβ, ∃ Λ : ℝ, 0 ≤ Λ ∧ (∀ x, ρβ x ≤ Λ) ∧
      ∀ N : ℕ, canonicalGibbs (periodicRiesz d s) V N β =
        modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρβ) := by
  obtain ⟨Lam, hLam⟩ := EQStat.eqstat_thermal_setup hd hs0 hsd V hV β β hβ le_rfl
  obtain ⟨hρs, hΛ, hP⟩ := hLam β ⟨le_rfl, le_rfl⟩ ρβ hρ
  refine ⟨hρs, max Lam 0, le_max_right _ _, fun x => (hΛ x).trans (le_max_left _ _), hP⟩

/-- `withDensityReal ρ ≤ Λ · dx` for `ρ ≤ Λ`. -/
theorem eqrem_mu_le_vol {ρ : Torus d → ℝ} {Λ : ℝ} (hΛ : ∀ x, ρ x ≤ Λ) :
    withDensityReal ρ ≤ ENNReal.ofReal Λ • (volume : Measure (Torus d)) :=
  Commutator.absConv_withDensityReal_le hΛ

/-- The first marginal of the Gibbs law has a bounded density w.r.t. `μ_β` (for every `N ≥ 2`). -/
theorem eqrem_marginal_le (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ) (hV : Torus.IsSmooth V)
    {β : ℝ} (hβ : 0 < β) {ρβ : Torus d → ℝ} (hρ : IsThermalDensity (periodicRiesz d s) V β ρβ) :
    ∃ Mp : ℝ, 0 ≤ Mp ∧ ∀ N : ℕ, 2 ≤ N →
      firstMarginal (canonicalGibbs (periodicRiesz d s) V N β) ≤
        ENNReal.ofReal Mp • withDensityReal ρβ := by
  obtain ⟨hρs, Λ, hΛ0, hΛ, hP⟩ := eqrem_setup hd hs0 hsd V hV hβ hρ
  obtain ⟨Mp, hMp1, hMp⟩ := pDens_bounds hd hs0 hsd hβ hρs
  refine ⟨Mp, by linarith, fun N hN => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 0 < n := by omega
  obtain ⟨hlam, hln, -⟩ := lam_facts hd hs0 hsd hβ hρs hn (lam := β / ((n + 1 : ℕ) : ℝ)) rfl
  rw [hP, modulatedGibbs_eq_cavity hd hs0 hsd hβ hρs (n + 1) (Nat.succ_pos n),
    firstMarginal_eq_withDensity hd hs0 hsd hρs hlam hln]
  refine Measure.le_iff'.2 fun A => ?_
  have hpm := measurable_pDens hd hs0 hsd hρs hlam hln
  have hb : ∀ y, ENNReal.ofReal (pDens (periodicRiesz d s) (withDensityReal ρβ) n
      (β / ((n + 1 : ℕ) : ℝ)) β y) ≤ ENNReal.ofReal Mp := by
    intro y
    have h2 := (hMp (n + 1) hN y).2
    simp only [Nat.add_sub_cancel] at h2
    exact ENNReal.ofReal_le_ofReal h2
  rw [withDensity_apply' _ A, Measure.smul_apply, smul_eq_mul]
  calc ∫⁻ a in A, ENNReal.ofReal (pDens (periodicRiesz d s) (withDensityReal ρβ) n
          (β / ((n + 1 : ℕ) : ℝ)) β a) ∂(withDensityReal ρβ)
      ≤ ∫⁻ _ in A, ENNReal.ofReal Mp ∂(withDensityReal ρβ) := lintegral_mono hb
    _ = ENNReal.ofReal Mp * withDensityReal ρβ A := setLIntegral_const _ _

/-- Bounded, measurable kernel field for a measure with bounded density. -/
theorem eqrem_kernelField_bdd (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ φ : Torus d → ℝ, Torus.IsCk 2 φ → ∀ (ν : Measure (Torus d)) (Λ : ℝ), 0 ≤ Λ →
      ν ≤ ENNReal.ofReal Λ • (volume : Measure (Torus d)) →
      Measurable (kernelField (pairKernel d s φ) ν) ∧
      (∀ x, |kernelField (pairKernel d s φ) ν x| ≤ Λ * (C₁ * Torus.cbNorm 2 φ)) := by
  obtain ⟨C₁, hC₁, hC⟩ := eqrem_kernel_L1 hd hs0 hsd
  refine ⟨C₁, hC₁, fun φ hφ ν Λ hΛ hν => ⟨?_, fun x => ?_⟩⟩
  · have hνfin : IsFiniteMeasure ν := by
      refine ⟨?_⟩
      have h := Measure.le_iff'.1 hν Set.univ
      rw [Measure.smul_apply, smul_eq_mul] at h
      exact lt_of_le_of_lt h (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _))
    exact (eqrem_pairKernel_meas hsd hφ).stronglyMeasurable.integral_prod_right'.measurable
  · obtain ⟨-, h2⟩ := hC φ hφ ν Λ hΛ hν x
    exact (abs_integral_le_integral_abs).trans h2


/-- The average `N⁻¹ ∑ ψ(x_i)` of a bounded measurable function is integrable. -/
theorem eqrem_avg_integrable {N : ℕ} {G : Measure (Config d N)} [IsProbabilityMeasure G] {ψ : Torus d → ℝ}
    (hψm : Measurable ψ) {B : ℝ} (hB : ∀ x, |ψ x| ≤ B) :
    Integrable (fun X : Config d N => (1 / (N : ℝ)) * ∑ i, ψ (X i)) G := by
  refine Integrable.const_mul (integrable_finset_sum _ fun i _ => ?_) _
  exact Integrable.of_bound (hψm.comp (measurable_pi_apply i)).aestronglyMeasurable B
    (ae_of_all _ fun X => by simpa using hB (X i))

/-- Exchangeability: `E[N⁻¹ ∑ ψ(x_i)] = ∫ ψ dm`. -/
theorem eqrem_avg_integral {N : ℕ} (hN : 0 < N) {G : Measure (Config d N)} [IsProbabilityMeasure G]
    {m : Measure (Torus d)} (hmi : ∀ i : Fin N, G.map (fun X : Config d N => X i) = m) {ψ : Torus d → ℝ}
    (hψm : Measurable ψ) {B : ℝ} (hB : ∀ x, |ψ x| ≤ B) :
    ∫ X, (1 / (N : ℝ)) * ∑ i, ψ (X i) ∂G = ∫ x, ψ x ∂m := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hψint : ∀ i : Fin N, Integrable (fun X : Config d N => ψ (X i)) G := fun i =>
    Integrable.of_bound (hψm.comp (measurable_pi_apply i)).aestronglyMeasurable B
      (ae_of_all _ fun X => by simpa using hB (X i))
  rw [integral_const_mul, integral_finset_sum _ (fun i _ => hψint i)]
  have : ∀ i : Fin N, ∫ X, ψ (X i) ∂G = ∫ x, ψ x ∂m := fun i => by
    rw [← hmi i]
    exact (integral_map (measurable_pi_apply i).aemeasurable hψm.aestronglyMeasurable).symm
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp


/-- The Gibbs law is a probability measure (thermal density, `N ≥ 1`). -/
theorem eqrem_gibbs_prob (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ) (hV : Torus.IsSmooth V)
    {β : ℝ} (hβ : 0 < β) {ρβ : Torus d → ℝ} (hρ : IsThermalDensity (periodicRiesz d s) V β ρβ)
    {N : ℕ} (hN : 0 < N) : IsProbabilityMeasure (canonicalGibbs (periodicRiesz d s) V N β) := by
  obtain ⟨hρs, Λ, hΛ0, hΛ, hP⟩ := eqrem_setup hd hs0 hsd V hV hβ hρ
  rw [hP N]
  exact Q32c.q32c_Q_isProb hd hs0 hsd hβ (Λ := max Λ 1) (le_max_right _ _) hρs.density
    (fun x => (hΛ x).trans (le_max_left _ _)) hN

end HRS.MD.EQRem

end
