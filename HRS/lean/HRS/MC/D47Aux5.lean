import HRS.MC.D47Aux4

/-!
# Packet D47, auxiliary facts 5: the decomposition identity
`F_N = F_{N,η} + ½ (N⁻² ∑_{i≠j} w_η(x_i - x_j) + E)` with `-2Λκ_η ≤ E ≤ Λκ_η`, `κ_η = ∫ w_η`.
-/

noncomputable section

open MeasureTheory Filter Topology Set

namespace HRS.MC.D47

open HRS HRS.MC.FDLE HRS.MC.Per HRS.MC.D3T1 HRS.MC.D3T3 HRS.StaticLimitAux

variable {d : ℕ}

lemma d47_decomp (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) {η : ℝ} (hη : 0 < η)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) {N : ℕ} (hN : 1 ≤ N) {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ)
    (hρΛ : ∀ x, ρ x ≤ Λ) {X : Config d N} (hX : X ∉ collisionSet d N) :
    ∃ E : ℝ, -2 * (Λ * d47_kappa ψ s b η) ≤ E ∧ E ≤ Λ * d47_kappa ψ s b η ∧
      rieszEnergy d s X (withDensityReal ρ) =
        fdlEnergy ψ s b η X (withDensityReal ρ) + (1 / 2) * (fdlPairW ψ s b η X + E) := by
  haveI := isProb_withDensityReal hρ
  have hΛ0 : 0 ≤ Λ := by linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hGηc : Continuous (fdlTruncT ψ s b η) := d3f_trunc_continuous hd hs0 hsd hψ hb hη
  have hWm0 : ∀ z, 0 ≤ d47_Wm ψ s b η z := d47_Wm_nonneg hψ hb.1.le
  have hWmm : Measurable (d47_Wm ψ s b η) := d47_Wm_measurable hd hs0 hsd hψ hb hη
  have hWmi : Integrable (d47_Wm ψ s b η) := d47_Wm_integrable hd hs0 hsd hψ hb hη
  have hWmint : ∫ z, d47_Wm ψ s b η z = d47_kappa ψ s b η := d47_Wm_integral hd hs0 hsd hψ hb hη
  have hκ0 : 0 ≤ d47_kappa ψ s b η := d47_kappa_nonneg hsd hψ hb.1.le hη
  have hdist : ∀ i j : Fin N, i ≠ j → X i - X j ≠ 0 := fun i j hij h => hX ⟨i, j, hij, sub_eq_zero.mp h⟩
  have hne : ∀ x : Torus d, ∀ᵐ y ∂(withDensityReal ρ), x - y ≠ 0 := by
    intro x
    have h0 : ∀ᵐ y ∂(volume : Measure (Torus d)), y ≠ x := by
      rw [ae_iff]; simpa using volume_singleton_torus hd x
    have h1 : ∀ᵐ y ∂(withDensityReal ρ), y ≠ x := withDensity_absolutelyContinuous _ _ h0
    filter_upwards [h1] with y hy
    exact sub_ne_zero.mpr (Ne.symm hy)
  set μ := withDensityReal ρ with hμ
  set κ := d47_kappa ψ s b η with hκ
  set Cw : Torus d → ℝ := fun x => ∫ y, d47_Wm ψ s b η (x - y) ∂μ with hCw
  have hCw0 : ∀ x, 0 ≤ Cw x := fun x => integral_nonneg (fun y => hWm0 _)
  have hCwle : ∀ x, Cw x ≤ Λ * κ := by
    intro x
    have := CoercAux.integral_conv_density_le hΛ0 hρΛ hWm0 hWmm hWmi x
    rwa [hWmint] at this
  have hsm : StronglyMeasurable (Function.uncurry fun x y : Torus d => d47_Wm ψ s b η (x - y)) :=
    (hWmm.comp (measurable_fst.sub measurable_snd)).stronglyMeasurable
  have hCwm : Measurable Cw := (hsm.integral_prod_right (ν := μ)).measurable
  have hCwi : Integrable Cw μ :=
    Integrable.mono' (integrable_const (Λ * κ)) hCwm.aestronglyMeasurable
      (ae_of_all _ (fun x => by rw [Real.norm_eq_abs, abs_of_nonneg (hCw0 x)]; exact hCwle x))
  set Φ : Torus d → ℝ := fun x => ∫ y, fdlTruncT ψ s b η (x - y) ∂μ with hΦ
  have hΦc : Continuous Φ := HRS.continuous_conv0 hGηc μ
  have hΦi : Integrable Φ μ :=
    hΦc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hGηint : ∀ x : Torus d, Integrable (fun y => fdlTruncT ψ s b η (x - y)) μ := fun x =>
    (hGηc.comp (continuous_const.sub continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hsplit : ∀ x : Torus d, ∫ y, periodicRiesz d s (x - y) ∂μ = Φ x + Cw x := by
    intro x
    have hae : ∀ᵐ y ∂μ, periodicRiesz d s (x - y) =
        fdlTruncT ψ s b η (x - y) + d47_Wm ψ s b η (x - y) := by
      filter_upwards [hne x] with y hy
      exact d47_Wm_eq hy
    rw [integral_congr_ae hae, integral_add (hGηint x)
      (CoercAux.integrable_conv_density hρΛ hWmm hWmi x)]
  have hsplit2 : ∫ x, ∫ y, periodicRiesz d s (x - y) ∂μ ∂μ = ∫ x, Φ x ∂μ + ∫ x, Cw x ∂μ := by
    have : (fun x : Torus d => ∫ y, periodicRiesz d s (x - y) ∂μ) = fun x => Φ x + Cw x :=
      funext hsplit
    rw [this, integral_add hΦi hCwi]
  have hT1 : ∑ i, ∑ j ∈ Finset.univ.erase i, periodicRiesz d s (X i - X j) =
      ∑ i, ∑ j ∈ Finset.univ.erase i, fdlTruncT ψ s b η (X i - X j) +
        ∑ i, ∑ j ∈ Finset.univ.erase i, fdlWT ψ s b η (X i - X j) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hij : i ≠ j := fun h => (Finset.ne_of_mem_erase hj) h.symm
    have hz := hdist i j hij
    have := d47_Wm_eq (ψ := ψ) (s := s) (b := b) (η := η) hz
    simpa [d47_Wm, hz] using this
  have hsumC : ∑ i, Cw (X i) ≤ N * (Λ * κ) := by
    calc ∑ i, Cw (X i) ≤ ∑ _i : Fin N, (Λ * κ) := Finset.sum_le_sum (fun i _ => hCwle _)
      _ = N * (Λ * κ) := by simp
  have hsumC0 : 0 ≤ ∑ i, Cw (X i) := Finset.sum_nonneg (fun i _ => hCw0 _)
  have hvol : μ.real Set.univ = 1 := by simp [Measure.real]
  have hint1 : ∫ x, Cw x ∂μ ≤ Λ * κ := by
    calc ∫ x, Cw x ∂μ ≤ ∫ _x, Λ * κ ∂μ := integral_mono hCwi (integrable_const _) hCwle
      _ = Λ * κ := by rw [integral_const, hvol]; simp
  have hint0 : 0 ≤ ∫ x, Cw x ∂μ := integral_nonneg hCw0
  refine ⟨-(2 / (N : ℝ)) * ∑ i, Cw (X i) + ∫ x, Cw x ∂μ, ?_, ?_, ?_⟩
  · have : (2 / (N : ℝ)) * ∑ i, Cw (X i) ≤ 2 * (Λ * κ) := by
      calc (2 / (N : ℝ)) * ∑ i, Cw (X i) ≤ (2 / (N : ℝ)) * (N * (Λ * κ)) :=
            mul_le_mul_of_nonneg_left hsumC (by positivity)
        _ = 2 * (Λ * κ) := by field_simp
    nlinarith
  · have : 0 ≤ (2 / (N : ℝ)) * ∑ i, Cw (X i) := mul_nonneg (by positivity) hsumC0
    nlinarith
  · unfold rieszEnergy fdlEnergy fdlPairW modulatedEnergyKernel modulatedEnergy
    have hI : ∀ i : Fin N, ∫ y, periodicRiesz d s (X i - y) ∂μ = Φ (X i) + Cw (X i) :=
      fun i => hsplit (X i)
    simp only [hI, hsplit2, hT1, Finset.sum_add_distrib]
    have hΦdef : ∀ i : Fin N, Φ (X i) = ∫ y, fdlTruncT ψ s b η (X i - y) ∂μ := fun i => rfl
    simp only [hΦdef]
    field_simp
    ring

end HRS.MC.D47
