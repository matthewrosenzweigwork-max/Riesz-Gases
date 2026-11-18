import HRS.MC.D47Aux3

/-!
# Packet D47, auxiliary facts 4: the decomposition `F_N = F_{N,η} + ½(N⁻² ∑_{i≠j} w_η + E)`.
-/

noncomputable section

open MeasureTheory Filter Topology Set

namespace HRS.MC.D47

open HRS HRS.MC.FDLE HRS.MC.Per HRS.MC.D3T1 HRS.MC.D3T3 HRS.StaticLimitAux

variable {d : ℕ}

/-- `w_η` with the (junk) value at `0` replaced by `0`. -/
def d47_Wm (ψ : Euc d → ℝ) (s b η : ℝ) (z : Torus d) : ℝ :=
  if z = 0 then 0 else fdlWT ψ s b η z

lemma d47_fdlWT_nonneg {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {s b η : ℝ} (hb0 : 0 ≤ b)
    (z : Torus d) : 0 ≤ fdlWT ψ s b η z := by
  unfold fdlWT
  refine mul_nonneg hb0 (setIntegral_nonneg measurableSet_Ioc (fun t ht => ?_))
  exact div_nonneg (mul_nonneg (Real.rpow_nonneg ht.1.le _) (d3t_per_nonneg hψ ht.1 z)) ht.1.le

lemma d47_Wm_nonneg {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {s b η : ℝ} (hb0 : 0 ≤ b)
    (z : Torus d) : 0 ≤ d47_Wm ψ s b η z := by
  unfold d47_Wm
  split_ifs
  · exact le_rfl
  · exact d47_fdlWT_nonneg hψ hb0 z

lemma d47_Wm_eq {ψ : Euc d → ℝ} {s b η : ℝ} {z : Torus d} (hz : z ≠ 0) :
    periodicRiesz d s z = fdlTruncT ψ s b η z + d47_Wm ψ s b η z := by
  unfold fdlTruncT d47_Wm
  rw [if_neg hz, if_neg hz]
  ring

lemma d47_Wm_eq' {ψ : Euc d → ℝ} {s b η : ℝ} :
    d47_Wm ψ s b η = fun z => if z = 0 then 0 else periodicRiesz d s z - fdlTruncT ψ s b η z := by
  funext z
  by_cases hz : z = 0
  · simp [d47_Wm, hz]
  · have := d47_Wm_eq (ψ := ψ) (s := s) (b := b) (η := η) hz
    simp only [hz, if_false]
    linarith

lemma d47_ae_ne_zero (hd : 1 ≤ d) : ∀ᵐ z ∂(volume : Measure (Torus d)), z ≠ 0 := by
  rw [ae_iff]
  simpa using volume_singleton_torus hd (0 : Torus d)

lemma d47_Wm_measurable (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) {η : ℝ} (hη : 0 < η) :
    Measurable (d47_Wm ψ s b η) := by
  rw [d47_Wm_eq']
  exact Measurable.ite (measurableSet_singleton (0 : Torus d)) measurable_const
    ((CoercAux.measurable_periodicRiesz_one hd hs0 hsd).sub
      (d3f_trunc_continuous hd hs0 hsd hψ hb hη).measurable)

lemma d47_Wm_ae (hd : 1 ≤ d) {ψ : Euc d → ℝ} {s b η : ℝ} :
    (fun z => periodicRiesz d s z - fdlTruncT ψ s b η z) =ᵐ[volume] d47_Wm ψ s b η := by
  filter_upwards [d47_ae_ne_zero hd] with z hz
  have := d47_Wm_eq (ψ := ψ) (s := s) (b := b) (η := η) hz
  linarith

lemma d47_Wm_integrable (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) {η : ℝ} (hη : 0 < η) :
    Integrable (d47_Wm ψ s b η) := by
  have hGi : Integrable (periodicRiesz d s) := (CoercAux.integral_periodicRiesz_one hd hs0 hsd).1
  have hGηi : Integrable (fdlTruncT ψ s b η) :=
    (d3f_trunc_continuous hd hs0 hsd hψ hb hη).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  exact (hGi.sub hGηi).congr (d47_Wm_ae hd)

lemma d47_integral_Hs (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) {η : ℝ} (hη : 0 < η) :
    ∫ x, Hs ψ s b η x = 0 := by
  have h := d3f_fcoef_Hs hd hs0 hsd hψ hb hη 0
  simp only [if_true] at h
  unfold Torus.fcoef at h
  simp only [neg_zero, Torus.mode_zero, one_mul] at h
  rw [integral_complex_ofReal] at h
  exact_mod_cast h

lemma d47_Wm_integral (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) {η : ℝ} (hη : 0 < η) :
    ∫ z, d47_Wm ψ s b η z = d47_kappa ψ s b η := by
  have hGi : Integrable (periodicRiesz d s) := (CoercAux.integral_periodicRiesz_one hd hs0 hsd).1
  have hG0 : ∫ x, periodicRiesz d s x = 0 := (CoercAux.integral_periodicRiesz_one hd hs0 hsd).2
  have hGηc := d3f_trunc_continuous hd hs0 hsd hψ hb hη
  have hGηi : Integrable (fdlTruncT ψ s b η) :=
    hGηc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hHc := d3f_Hs_continuous hd hs0 hψ hb.1 hη
  have hHi : Integrable (Hs ψ s b η) :=
    hHc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hvol : (volume : Measure (Torus d)).real Set.univ = 1 := by simp [Measure.real]
  have h1 : ∫ x, fdlTruncT ψ s b η x = - d47_kappa ψ s b η := by
    rw [d3f_truncT_eq hd hs0 hsd hψ hb hη]
    simp only
    rw [integral_sub hHi (integrable_const _), d47_integral_Hs hd hs0 hsd hψ hb hη, integral_const,
      hvol]
    simp [d47_kappa]
  rw [← integral_congr_ae (d47_Wm_ae hd), integral_sub hGi hGηi, hG0, h1]
  ring

lemma d47_kappa_eq (ψ : Euc d → ℝ) (s b η : ℝ) :
    d47_kappa ψ s b η = (b * (∫ y, fdlPhi ψ y) / ((d : ℝ) - s)) * η ^ ((d : ℝ) - s) := by
  unfold d47_kappa
  ring

end HRS.MC.D47
