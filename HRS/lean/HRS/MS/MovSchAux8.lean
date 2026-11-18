import HRS.MS.MovSchAux7

/-!
# S64 (S6.9), part 3: the density of the moving reference

Namespace `HRS.MS.MovSch`, prefix `s64_`.  For `ρ₀` a thermal density (`IsThermalDensity g V β ρ₀`, `g` even, `N ≥ 1`):
* `s64_thermal_data`: `∏ ρ₀(x_i) e^{-βN F_N} = k e^{-βH_N}` and `K_{N,β}(μ₀) = k Z_can`, with `k > 0` (a copy of the relevant steps of
  `HRS.MS.Canon.canonicalGibbs_eq_modulatedGibbs_proof`, whose integrability hypothesis `hint` is unused and is not needed here);
* `s64_K_pos`: `0 < K_{N,β}(μ₀)` (from `s64_Zpos`);
* `s64_movQ_thermal`: `movQDensity ρ₀ X = Z_can⁻¹ e^{-βH_N(X)}`;
* `s64_movQ_translate`: `movQDensity (ρ₀(· - a)) X = movQDensity ρ₀ (X - a)`;
* `s64_modGibbs_density`: `Q_{N,β}(ρ dx) = Lebesgue.withDensity (movQ ρ)` whenever `0 < K`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovSch

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

theorem s64_thermal_data (g V : Euc d → ℝ) (β : ℝ) (ρ : Euc d → ℝ) (hρ : HRS.Whole.IsThermalDensity g V β ρ)
    (hg : ∀ x, g (-x) = g x) (N : ℕ) :
    ∃ k : ℝ, 0 < k ∧
      (∀ X : HRS.Whole.EucConfig d N, (∏ i, ρ (X i)) * Real.exp (-β * (N : ℝ) * HRS.Whole.modulatedEnergy g X (HRS.Whole.withDensityReal ρ))
          = k * Real.exp (-β * HRS.Whole.canonicalHamiltonian g V X)) ∧
      HRS.Whole.gibbsNormalizer g N β (HRS.Whole.withDensityReal ρ) = k * HRS.Whole.canonicalPartition g V N β := by
  have hZ := HRS.MS.Canon.cn_Z_pos g V β ρ hρ
  unfold HRS.Whole.IsThermalDensity at hρ
  obtain ⟨hprob, hfix⟩ := hρ
  have hρ0 : ∀ x, 0 ≤ ρ x := hprob.nonneg
  have hρi : Integrable ρ := HRS.MS.Canon.cn_integrable_of_prob ρ hprob
  have hP := HRS.MS.Canon.cn_pi_withDensityReal (N := N) ρ hρ0 hρi
  generalize hZdef : (∫ y, Real.exp (-β * (V y + HRS.Whole.convMeasure g (HRS.Whole.withDensityReal ρ) y))) = Z at hZ hfix
  have hR : ∀ X : Fin N → Euc d,
      (∏ i, ρ (X i)) * Real.exp (-β * (N : ℝ) * HRS.Whole.modulatedEnergy g X (HRS.Whole.withDensityReal ρ))
        = Real.exp (-(β * (N : ℝ) / 2) * HRS.Whole.energyPairing g (HRS.Whole.withDensityReal ρ) (HRS.Whole.withDensityReal ρ))
          / Z ^ N * Real.exp (-β * HRS.Whole.canonicalHamiltonian g V X) :=
    fun X => HRS.MS.Canon.cn_pointwise g V β (HRS.Whole.withDensityReal ρ) ρ Z hg hfix X
  have hkpos : 0 < Real.exp (-(β * (N : ℝ) / 2) * HRS.Whole.energyPairing g (HRS.Whole.withDensityReal ρ) (HRS.Whole.withDensityReal ρ))
      / Z ^ N :=
    div_pos (Real.exp_pos _) (pow_pos hZ N)
  generalize hk : Real.exp (-(β * (N : ℝ) / 2) * HRS.Whole.energyPairing g (HRS.Whole.withDensityReal ρ) (HRS.Whole.withDensityReal ρ))
      / Z ^ N = k at hR hkpos
  have hpm : Measurable (fun X : Fin N → Euc d => ENNReal.ofReal (∏ i, ρ (X i))) :=
    Measurable.ennreal_ofReal (Finset.measurable_prod _ fun i _ =>
      hprob.measurable.comp (measurable_pi_apply i))
  refine ⟨k, hkpos, hR, ?_⟩
  unfold HRS.Whole.gibbsNormalizer HRS.Whole.canonicalPartition
  rw [hP, integral_withDensity_eq_integral_toReal_smul₀ hpm.aemeasurable
    (ae_of_all _ fun X => ENNReal.ofReal_lt_top), ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun X => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (Finset.prod_nonneg fun i _ => hρ0 (X i))]
  exact hR X

lemma s64_even_rieszKernel (d : ℕ) (s : ℝ) (x : Euc d) : HRS.Whole.rieszKernel d s (-x) = HRS.Whole.rieszKernel d s x := by
  unfold HRS.Whole.rieszKernel
  simp [norm_neg]

theorem s64_K_pos {s q β : ℝ} (hs0 : 0 ≤ s) (hq : 0 < q) (hβ : 0 < β) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsThermalDensity (HRS.Whole.rieszKernel d s) (HRS.Whole.confinement q) β ρ) {N : ℕ} (hN : 1 ≤ N) :
    0 < HRS.Whole.gibbsNormalizer (HRS.Whole.rieszKernel d s) N β (HRS.Whole.withDensityReal ρ) := by
  obtain ⟨k, hk, -, hK⟩ := s64_thermal_data (HRS.Whole.rieszKernel d s) (HRS.Whole.confinement q) β ρ hρ (s64_even_rieszKernel d s) N
  rw [hK]
  exact mul_pos hk (s64_Zpos hs0 hq hβ hN)

theorem s64_movQ_thermal {s q β : ℝ} (hs0 : 0 ≤ s) (hq : 0 < q) (hβ : 0 < β) {ρ : Euc d → ℝ}
    (hρ : HRS.Whole.IsThermalDensity (HRS.Whole.rieszKernel d s) (HRS.Whole.confinement q) β ρ) {N : ℕ} (hN : 1 ≤ N)
    (X : HRS.Whole.EucConfig d N) :
    movQDensity d s β N ρ X = (HRS.Whole.canonicalPartition (HRS.Whole.rieszKernel d s) (HRS.Whole.confinement q) N β)⁻¹ *
      Real.exp (-β * HRS.Whole.canonicalHamiltonian (HRS.Whole.rieszKernel d s) (HRS.Whole.confinement q) X) := by
  obtain ⟨k, hk, hpt, hK⟩ := s64_thermal_data (HRS.Whole.rieszKernel d s) (HRS.Whole.confinement q) β ρ hρ (s64_even_rieszKernel d s) N
  have hZ := s64_Zpos (d := d) hs0 hq hβ hN
  unfold movQDensity HRS.Whole.rieszModulatedEnergy
  have e : ∀ (K a b : ℝ), K⁻¹ * a * b = K⁻¹ * (b * a) := fun K a b => by ring
  rw [e, hpt X, hK, mul_inv]
  have hk0 := hk.ne'
  have hZ0 := hZ.ne'
  field_simp

lemma s64_withDensityReal_translate (ρ : Euc d → ℝ) (a : Euc d) :
    HRS.Whole.withDensityReal (fun x => ρ (x - a)) = (HRS.Whole.withDensityReal ρ).map (fun y => y + a) := by
  unfold HRS.Whole.withDensityReal
  have h := movtr_map_withDensity (MeasurableEquiv.addRight a) (volume : Measure (Euc d))
    (fun x => ENNReal.ofReal (ρ (x - a)))
  simp only [Function.comp_def, MeasurableEquiv.coe_addRight, add_sub_cancel_right] at h
  have hv : (volume : Measure (Euc d)).map (fun y => y + a) = volume :=
    (measurePreserving_add_right (volume : Measure (Euc d)) a).map_eq
  rw [hv] at h
  rw [← h]

theorem s64_movQ_translate {s β : ℝ} {ρ : Euc d → ℝ} (hprob : HRS.Whole.IsProbDensity ρ) {N : ℕ} (a : Euc d)
    (X : HRS.Whole.EucConfig d N) :
    movQDensity d s β N (fun x => ρ (x - a)) X = movQDensity d s β N ρ (fun i => X i - a) := by
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := HRS.MS.Wr.wr13a_isProb_density hprob
  unfold movQDensity HRS.Whole.rieszModulatedEnergy
  rw [s64_withDensityReal_translate, movtr_gibbsNormalizer_translate]
  have h2 := movtr_modulatedEnergy_translate (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) a (fun i => X i - a)
  simp only [sub_add_cancel] at h2
  rw [h2]

theorem s64_modGibbs_density {s β : ℝ} {ρ : Euc d → ℝ} (hprob : HRS.Whole.IsProbDensity ρ) {N : ℕ}
    (hK : 0 < HRS.Whole.gibbsNormalizer (HRS.Whole.rieszKernel d s) N β (HRS.Whole.withDensityReal ρ)) :
    HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β (HRS.Whole.withDensityReal ρ) =
      (volume : Measure (HRS.Whole.EucConfig d N)).withDensity (fun X => ENNReal.ofReal (movQDensity d s β N ρ X)) := by
  have hρ0 := hprob.nonneg
  have hρi := HRS.MS.Canon.cn_integrable_of_prob ρ hprob
  have hpm : Measurable (fun X : Fin N → Euc d => ENNReal.ofReal (∏ i, ρ (X i))) :=
    Measurable.ennreal_ofReal (Finset.measurable_prod _ fun i _ =>
      hprob.measurable.comp (measurable_pi_apply i))
  unfold HRS.Whole.modulatedGibbs
  rw [HRS.MS.Canon.cn_pi_withDensityReal (N := N) ρ hρ0 hρi,
    HRS.MS.Canon.cn_withDensity_withDensity _ _ hpm (fun _ => ENNReal.ofReal_lt_top)]
  have hfun : (fun X : HRS.Whole.EucConfig d N => ENNReal.ofReal (∏ i, ρ (X i)) *
      ENNReal.ofReal (Real.exp (-β * N * HRS.Whole.modulatedEnergy (HRS.Whole.rieszKernel d s) X (HRS.Whole.withDensityReal ρ)))) =
      fun X => ENNReal.ofReal ((∏ i, ρ (X i)) *
        Real.exp (-β * N * HRS.Whole.modulatedEnergy (HRS.Whole.rieszKernel d s) X (HRS.Whole.withDensityReal ρ))) := by
    funext X
    rw [ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => hρ0 (X i))]
  rw [hfun, ← HRS.MS.Canon.cn_withDensity_const_mul _ _ (ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hK).ne')]
  congr 1
  funext X
  rw [← ENNReal.ofReal_inv_of_pos hK, ← ENNReal.ofReal_mul (inv_pos.2 hK).le]
  congr 1
  unfold movQDensity HRS.Whole.rieszModulatedEnergy
  ring

end HRS.MS.MovSch

end
