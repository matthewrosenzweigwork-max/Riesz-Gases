import HRS.Whole.Basic

/-!
# U10a: the space-time measure `ρ_r(x) dx dr` on `[0,t] × ℝ^d` and iterated integrals

For a family of probability densities `ρ_r` (`r ∈ [0,t]`) the finite measure
`μρ = (1_{[0,t]} dr ⊗ dx).withDensity ρ` has total mass `t`, and for bounded measurable `g`,
`∫ g dμρ = ∫_{[0,t]} ∫ g(r,x) ρ_r(x) dx dr`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace HRS.MS.U10

open HRS HRS.Whole

variable {d : ℕ}

/-- `1_{[0,t]}(r) dr ⊗ dx` on `ℝ × ℝ^d`. -/
def u10_m (d : ℕ) (t : ℝ) : Measure (ℝ × Euc d) :=
  (volume.restrict (Set.Icc (0 : ℝ) t)).prod volume

/-- `ρ_r(x) 1_{[0,t]}(r) dr dx`. -/
def u10_mu (d : ℕ) (t : ℝ) (ρ : ℝ → Euc d → ℝ) : Measure (ℝ × Euc d) :=
  (u10_m d t).withDensity fun p => ENNReal.ofReal (ρ p.1 p.2)

lemma u10_ae_mem (t : ℝ) : ∀ᵐ p ∂(u10_m d t), p.1 ∈ Set.Icc (0 : ℝ) t :=
  (Measure.quasiMeasurePreserving_fst (μ := volume.restrict (Set.Icc (0 : ℝ) t))
    (ν := (volume : Measure (Euc d)))).ae (ae_restrict_mem measurableSet_Icc)

lemma u10_ae_rho_nonneg {t : ℝ} {ρ : ℝ → Euc d → ℝ}
    (hρ : ∀ r ∈ Set.Icc (0 : ℝ) t, HRS.Whole.IsProbDensity (ρ r)) :
    ∀ᵐ p ∂(u10_m d t), 0 ≤ ρ p.1 p.2 := by
  filter_upwards [u10_ae_mem (d := d) t] with p hp using (hρ _ hp).nonneg _

lemma u10_mu_univ {t : ℝ} (ht : 0 ≤ t) {ρ : ℝ → Euc d → ℝ}
    (hρ : ∀ r ∈ Set.Icc (0 : ℝ) t, HRS.Whole.IsProbDensity (ρ r))
    (hρm : Measurable (Function.uncurry ρ)) :
    u10_mu d t ρ Set.univ = ENNReal.ofReal t := by
  unfold u10_mu u10_m
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rw [lintegral_prod (fun p : ℝ × Euc d => ENNReal.ofReal (ρ p.1 p.2))
    (ENNReal.measurable_ofReal.comp hρm).aemeasurable]
  have h1 : ∀ r ∈ Set.Icc (0 : ℝ) t, ∫⁻ x, ENNReal.ofReal (ρ r x) = 1 := by
    intro r hr
    have hint : Integrable (ρ r) volume :=
      Integrable.of_integral_ne_zero (by rw [(hρ r hr).integral_one]; exact one_ne_zero)
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ (hρ r hr).nonneg),
      (hρ r hr).integral_one, ENNReal.ofReal_one]
  rw [setLIntegral_congr_fun measurableSet_Icc h1]
  simp

lemma u10_isFinite {t : ℝ} (ht : 0 ≤ t) {ρ : ℝ → Euc d → ℝ}
    (hρ : ∀ r ∈ Set.Icc (0 : ℝ) t, HRS.Whole.IsProbDensity (ρ r))
    (hρm : Measurable (Function.uncurry ρ)) : IsFiniteMeasure (u10_mu d t ρ) :=
  ⟨by rw [u10_mu_univ ht hρ hρm]; exact ENNReal.ofReal_lt_top⟩

lemma u10_real_univ {t : ℝ} (ht : 0 ≤ t) {ρ : ℝ → Euc d → ℝ}
    (hρ : ∀ r ∈ Set.Icc (0 : ℝ) t, HRS.Whole.IsProbDensity (ρ r))
    (hρm : Measurable (Function.uncurry ρ)) : (u10_mu d t ρ).real Set.univ = t := by
  rw [Measure.real, u10_mu_univ ht hρ hρm, ENNReal.toReal_ofReal ht]

lemma u10_ae_bound {t : ℝ} {ρ : ℝ → Euc d → ℝ} {g : ℝ × Euc d → ℝ} {c : ℝ}
    (hc : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ x, ‖g (r, x)‖ ≤ c) :
    ∀ᵐ p ∂(u10_mu d t ρ), ‖g p‖ ≤ c := by
  have h : ∀ᵐ p ∂(u10_m d t), ‖g p‖ ≤ c := by
    filter_upwards [u10_ae_mem (d := d) t] with p hp using hc p.1 hp p.2
  exact (withDensity_absolutelyContinuous _ _).ae_le h

lemma u10_integral_eq {t : ℝ} (ht : 0 ≤ t) {ρ : ℝ → Euc d → ℝ}
    (hρ : ∀ r ∈ Set.Icc (0 : ℝ) t, HRS.Whole.IsProbDensity (ρ r))
    (hρm : Measurable (Function.uncurry ρ)) {g : ℝ × Euc d → ℝ} (hg : Measurable g) {c : ℝ}
    (hc : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ x, ‖g (r, x)‖ ≤ c) :
    Integrable g (u10_mu d t ρ) ∧
      ∫ p, g p ∂(u10_mu d t ρ) = ∫ r in Set.Icc (0 : ℝ) t, ∫ x, g (r, x) * ρ r x := by
  haveI := u10_isFinite ht hρ hρm
  have hint : Integrable g (u10_mu d t ρ) :=
    Integrable.of_bound hg.aestronglyMeasurable c (u10_ae_bound hc)
  refine ⟨hint, ?_⟩
  have hmeas : Measurable fun p : ℝ × Euc d => ENNReal.ofReal (ρ p.1 p.2) :=
    ENNReal.measurable_ofReal.comp hρm
  have hlt : ∀ᵐ p ∂(u10_m d t), ENNReal.ofReal (ρ p.1 p.2) < ∞ :=
    ae_of_all _ fun _ => ENNReal.ofReal_lt_top
  have e : ∀ᵐ p ∂(u10_m d t),
      (ENNReal.ofReal (ρ p.1 p.2)).toReal • g p = g p * ρ p.1 p.2 := by
    filter_upwards [u10_ae_rho_nonneg (d := d) hρ] with p hp
    rw [ENNReal.toReal_ofReal hp, smul_eq_mul, mul_comm]
  have hI : Integrable (fun p => g p * ρ p.1 p.2) (u10_m d t) :=
    ((integrable_withDensity_iff_integrable_smul' hmeas hlt).1 hint).congr e
  unfold u10_mu
  rw [integral_withDensity_eq_integral_toReal_smul hmeas hlt, integral_congr_ae e]
  unfold u10_m at hI ⊢
  rw [integral_prod _ hI]

end HRS.MS.U10
