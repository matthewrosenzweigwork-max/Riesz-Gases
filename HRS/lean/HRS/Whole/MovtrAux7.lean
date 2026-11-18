import HRS.Whole.MovtrAux6

/-!
# MOVTR auxiliary 7: free energy of a translate of the thermal equilibrium
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole

variable {d : ℕ}

lemma movtr_integrable_of_prob {ρ : Euc d → ℝ} (hρ : IsProbDensity ρ) : Integrable ρ := by
  by_contra h
  have := hρ.integral_one
  rw [integral_undef h] at this
  norm_num at this

/-- The potential term of a translate. -/
lemma movtr_potential_translate {q : ℝ} (hq : 0 < q) {ρ : Euc d → ℝ} (hρ : IsProbDensity ρ)
    (hV : Integrable (fun x => confinement q x * ρ x)) (a : Euc d) :
    Integrable (fun y => confinement q (y + a) * ρ y) ∧
    ∫ y, confinement q (y + a) * ρ y =
      (∫ y, confinement q y * ρ y) + q * (∫ y, inner ℝ y a * ρ y) + q / 2 * ‖a‖ ^ 2 := by
  have hρi := movtr_integrable_of_prob hρ
  have hsq : Integrable (fun y => ‖y‖ ^ 2 * ρ y) := by
    have := hV.const_mul (2 / q)
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [confinement]
    field_simp
  have hin : Integrable (fun y => inner ℝ y a * ρ y) := by
    have hb : Integrable (fun y => ‖a‖ * (‖y‖ ^ 2 * ρ y + ρ y)) := (hsq.add hρi).const_mul _
    refine Integrable.mono' hb ?_ (Filter.Eventually.of_forall fun y => ?_)
    · exact ((continuous_id.inner continuous_const).aestronglyMeasurable).mul hρi.aestronglyMeasurable
    · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hρ.nonneg y)]
      have h1 : |inner ℝ y a| ≤ ‖y‖ * ‖a‖ := abs_real_inner_le_norm _ _
      have h2 : ‖y‖ ≤ ‖y‖ ^ 2 + 1 := by nlinarith [sq_nonneg (‖y‖ - 1)]
      have h3 := hρ.nonneg y
      calc |inner ℝ y a| * ρ y ≤ (‖y‖ * ‖a‖) * ρ y := mul_le_mul_of_nonneg_right h1 h3
        _ ≤ ((‖y‖ ^ 2 + 1) * ‖a‖) * ρ y := by
            apply mul_le_mul_of_nonneg_right _ h3
            exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
        _ = _ := by ring
  have hpt : (fun y => confinement q (y + a) * ρ y) =
      fun y => confinement q y * ρ y + q * (inner ℝ y a * ρ y) + q / 2 * ‖a‖ ^ 2 * ρ y := by
    funext y
    simp only [confinement]
    rw [norm_add_sq_real]
    ring
  have hint : Integrable (fun y => confinement q y * ρ y + q * (inner ℝ y a * ρ y) +
      q / 2 * ‖a‖ ^ 2 * ρ y) :=
    (hV.add (hin.const_mul q)).add (hρi.const_mul _)
  rw [hpt]
  refine ⟨hint, ?_⟩
  have hA : Integrable (fun y => confinement q y * ρ y + q * (inner ℝ y a * ρ y)) :=
    hV.add (hin.const_mul q)
  have hB : Integrable (fun y => q / 2 * ‖a‖ ^ 2 * ρ y) := hρi.const_mul _
  have e1 := integral_add hA hB
  have e2 := integral_add hV (hin.const_mul q)
  have e3 : ∫ y, q * (inner ℝ y a * ρ y) = q * ∫ y, inner ℝ y a * ρ y := integral_const_mul _ _
  have e4 : ∫ y, q / 2 * ‖a‖ ^ 2 * ρ y = q / 2 * ‖a‖ ^ 2 * ∫ y, ρ y := integral_const_mul _ _
  rw [e1, e2, e3, e4, hρ.integral_one]
  ring


/-- Finiteness and the exact free energy of a translate (before using minimality). -/
lemma movtr_free_translate {s q β : ℝ} (hq : 0 < q) {ρ : Euc d → ℝ} (hprob : IsProbDensity ρ)
    (hfin : HasFiniteFreeEnergy (rieszKernel d s) (confinement q) ρ) (a : Euc d) :
    IsProbDensity (fun x => ρ (x - a)) ∧
    HasFiniteFreeEnergy (rieszKernel d s) (confinement q) (fun x => ρ (x - a)) ∧
    freeEnergy (rieszKernel d s) (confinement q) β (fun x => ρ (x - a)) =
      freeEnergy (rieszKernel d s) (confinement q) β ρ +
        (q * (∫ y, inner ℝ y a * ρ y) + q / 2 * ‖a‖ ^ 2) := by
  obtain ⟨hV1, hV2⟩ := movtr_potential_translate hq hprob hfin.2.1 a
  refine ⟨⟨fun x => hprob.nonneg _,
    hprob.measurable.comp (measurable_id.sub_const a), ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [integral_sub_right_eq_self ρ a]; exact hprob.integral_one
  · exact hfin.1.comp_sub_right a
  · refine (hV1.comp_sub_right a).congr (Filter.Eventually.of_forall fun x => ?_)
    simp
  · have mp : MeasurePreserving (fun p : Euc d × Euc d => (p.1 - a, p.2 - a))
        ((volume : Measure (Euc d)).prod volume) ((volume : Measure (Euc d)).prod volume) :=
      (measurePreserving_sub_right volume a).prod (measurePreserving_sub_right volume a)
    have := mp.integrable_comp_of_integrable hfin.2.2
    refine this.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.comp, sub_sub_sub_cancel_right]
  · unfold freeEnergy
    have E1 : ∫ x, ρ (x - a) * Real.log (ρ (x - a)) = ∫ x, ρ x * Real.log (ρ x) :=
      integral_sub_right_eq_self (fun x => ρ x * Real.log (ρ x)) a
    have E2 : ∫ x, confinement q x * ρ (x - a) = ∫ y, confinement q (y + a) * ρ y := by
      rw [← integral_sub_right_eq_self (fun y => confinement q (y + a) * ρ y) a]
      simp
    have E3 : ∫ x, ∫ y, rieszKernel d s (x - y) * ρ (x - a) * ρ (y - a) =
        ∫ x, ∫ y, rieszKernel d s (x - y) * ρ x * ρ y := by
      have inner : ∀ x : Euc d, ∫ y, rieszKernel d s (x - y) * ρ (x - a) * ρ (y - a) =
          ∫ y, rieszKernel d s ((x - a) - y) * ρ (x - a) * ρ y := by
        intro x
        rw [← integral_sub_right_eq_self (fun y => rieszKernel d s ((x - a) - y) * ρ (x - a) * ρ y) a]
        simp only [sub_sub_sub_cancel_right]
      simp_rw [inner]
      exact integral_sub_right_eq_self (fun x => ∫ y, rieszKernel d s (x - y) * ρ x * ρ y) a
    rw [E1, E2, E3, hV2]
    ring

/-- The first moment of the equilibrium vanishes, and the free-energy gap of a translate is
`(q/2)|a|²`. -/
theorem movtr_freeEnergy_translate {s q β : ℝ} (hq : 0 < q) {ρ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d s q β ρ) (a : Euc d) :
    HasFiniteFreeEnergy (rieszKernel d s) (confinement q) (fun x => ρ (x - a)) ∧
    HasFiniteFreeEnergy (rieszKernel d s) (confinement q) ρ ∧
    freeEnergy (rieszKernel d s) (confinement q) β (fun x => ρ (x - a)) -
      freeEnergy (rieszKernel d s) (confinement q) β ρ = q / 2 * ‖a‖ ^ 2 := by
  obtain ⟨⟨hprob, hfin, hmin⟩, _⟩ := hρ
  have key : ∀ b : Euc d, 0 ≤ q * (∫ y, inner ℝ y b * ρ y) + q / 2 * ‖b‖ ^ 2 := by
    intro b
    obtain ⟨hp, hf, hF⟩ := movtr_free_translate (s := s) (β := β) hq hprob hfin b
    have := hmin _ hp hf
    rw [hF] at this
    linarith
  have hlin : ∀ (c : ℝ) (b : Euc d), (∫ y, inner ℝ y (c • b) * ρ y) = c * ∫ y, inner ℝ y b * ρ y := by
    intro c b
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [inner_smul_right]
    ring
  have hzero : ∀ b : Euc d, (∫ y, inner ℝ y b * ρ y) = 0 := by
    intro b
    by_cases hb : b = 0
    · subst hb; simp
    set L := ∫ y, inner ℝ y b * ρ y with hL
    have hbn : 0 < ‖b‖ ^ 2 := by positivity
    have h := key ((-(L / ‖b‖ ^ 2)) • b)
    rw [hlin, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, ← hL] at h
    have h2 : q * (-(L / ‖b‖ ^ 2) * L) + q / 2 * ((-(L / ‖b‖ ^ 2)) ^ 2 * ‖b‖ ^ 2) =
        -(q * L ^ 2 / (2 * ‖b‖ ^ 2)) := by
      field_simp
      ring
    rw [h2] at h
    have h3 : q * L ^ 2 / (2 * ‖b‖ ^ 2) ≤ 0 := by linarith
    have h4 : 0 ≤ q * L ^ 2 / (2 * ‖b‖ ^ 2) := by positivity
    have h5 : q * L ^ 2 / (2 * ‖b‖ ^ 2) = 0 := le_antisymm h3 h4
    have h6 : L ^ 2 = 0 := by
      have hne : (2 * ‖b‖ ^ 2) ≠ 0 := by positivity
      rw [div_eq_zero_iff] at h5
      rcases h5 with h5 | h5
      · rcases mul_eq_zero.mp h5 with h7 | h7
        · exact absurd h7 hq.ne'
        · exact h7
      · exact absurd h5 hne
    exact pow_eq_zero_iff (two_ne_zero) |>.mp h6
  obtain ⟨hp, hf, hF⟩ := movtr_free_translate (s := s) (β := β) hq hprob hfin a
  refine ⟨hf, hfin, ?_⟩
  rw [hF, hzero a]
  ring

end HRS.Whole
