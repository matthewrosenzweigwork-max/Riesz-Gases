import HRS.MS.S113EndAux32

/-!
# S11.3 X2 wiring (worker S11W), C1: the barrier lemma and the integrated one-sided power chain bound

`s113c_barrier`: if `M(t) - M(s) ≤ ∫_s^t g` for all `0 ≤ s ≤ t ≤ T` (`g` interval integrable) and `g ≤ 0` almost everywhere on
`{M > B}`, then `M ≤ B` on `[0,T]` as soon as `M(0) ≤ B` (no positivity of `M`, no absolute continuity of `M`).
`s113c_chain_bound_int`: the localized power bound `M(T) ≤ max(M(0), e^{C₀})` from the integrated form of the power chain
inequality (the form delivered by the subsolution route of part B).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.MS.S113BD

open HRS.Whole

/-- **Barrier lemma.** -/
theorem s113c_barrier {M g : ℝ → ℝ} {T B : ℝ} (hT : 0 ≤ T) (hg : IntervalIntegrable g volume 0 T)
    (hM : ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T → M t - M s ≤ ∫ τ in s..t, g τ)
    (hneg : ∀ᵐ τ : ℝ, τ ∈ Set.Ioo 0 T → B < M τ → g τ ≤ 0) (h0 : M 0 ≤ B) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, M t ≤ B := by
  intro t1 ht1
  by_contra hcon
  rw [not_le] at hcon
  set φ : ℝ → ℝ := fun x => ∫ τ in (0 : ℝ)..x, g τ with hφ
  have hφc : ContinuousOn φ (Set.Icc 0 T) := by
    have := intervalIntegral.continuousOn_primitive_interval' hg (a := 0) (by simp [Set.uIcc_of_le hT, hT])
    rwa [Set.uIcc_of_le hT] at this
  have hdiff : ∀ x y : ℝ, x ∈ Set.Icc (0 : ℝ) T → y ∈ Set.Icc (0 : ℝ) T →
      ∫ τ in x..y, g τ = φ y - φ x := by
    intro x y hx hy
    have hix : IntervalIntegrable g volume 0 x := hg.mono_set (by
      rw [Set.uIcc_of_le hT, Set.uIcc_of_le hx.1]; exact Set.Icc_subset_Icc le_rfl hx.2)
    have hiy : IntervalIntegrable g volume 0 y := hg.mono_set (by
      rw [Set.uIcc_of_le hT, Set.uIcc_of_le hy.1]; exact Set.Icc_subset_Icc le_rfl hy.2)
    rw [hφ]
    simp only
    rw [← intervalIntegral.integral_interval_sub_left hiy hix]
  have hMφ : ∀ s t : ℝ, s ∈ Set.Icc (0 : ℝ) T → t ∈ Set.Icc (0 : ℝ) T → s ≤ t →
      M t - M s ≤ φ t - φ s := by
    intro s t hs ht hst
    have := hM s t hs.1 hst ht.2
    rwa [hdiff s t hs ht] at this
  set S : Set ℝ := {τ | τ ∈ Set.Icc (0 : ℝ) t1 ∧ M τ ≤ B} with hS
  have h0S : (0 : ℝ) ∈ S := ⟨⟨le_rfl, ht1.1⟩, h0⟩
  have hbdd : BddAbove S := ⟨t1, fun τ hτ => hτ.1.2⟩
  set s : ℝ := sSup S with hs
  have hs0 : 0 ≤ s := le_csSup hbdd h0S
  have hst1 : s ≤ t1 := csSup_le ⟨0, h0S⟩ fun τ hτ => hτ.1.2
  have hsI : s ∈ Set.Icc (0 : ℝ) T := ⟨hs0, hst1.trans ht1.2⟩
  -- M s ≤ B
  have hMs : M s ≤ B := by
    by_contra hMs
    rw [not_le] at hMs
    have hε : 0 < M s - B := by linarith
    have hcs := hφc s hsI
    rw [Metric.continuousWithinAt_iff] at hcs
    obtain ⟨δ, hδ, hδ'⟩ := hcs (M s - B) hε
    obtain ⟨σ, hσS, hσ⟩ := exists_lt_of_lt_csSup ⟨0, h0S⟩ (show s - δ < s by linarith)
    have hσI : σ ∈ Set.Icc (0 : ℝ) T := ⟨hσS.1.1, hσS.1.2.trans ht1.2⟩
    have hσs : σ ≤ s := le_csSup hbdd hσS
    have h1 := hMφ σ s hσI hsI hσs
    have h2 := hδ' hσI (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    rw [Real.dist_eq, abs_lt] at h2
    have := hσS.2
    linarith [h2.1, h2.2]
  have hslt : s < t1 := by
    rcases hst1.lt_or_eq with h | h
    · exact h
    · rw [h] at hMs; linarith
  -- for τ ∈ (s, t1], B < M τ
  have hbig : ∀ τ ∈ Set.Ioc s t1, B < M τ := by
    intro τ hτ
    by_contra hle
    rw [not_lt] at hle
    have : τ ∈ S := ⟨⟨hs0.trans hτ.1.le, hτ.2⟩, hle⟩
    exact absurd (le_csSup hbdd this) (not_le.2 hτ.1)
  have hup : ∀ τ ∈ Set.Ioc s t1, M t1 ≤ B + (φ τ - φ s) := by
    intro τ hτ
    have hτI : τ ∈ Set.Icc (0 : ℝ) T := ⟨hs0.trans hτ.1.le, hτ.2.trans ht1.2⟩
    have hneg' : ∀ᵐ x ∂(volume.restrict (Set.Ioc τ t1)), g x ≤ 0 := by
      have h2 : ∀ᵐ x : ℝ ∂volume, x ≠ t1 := by
        have : (volume : Measure ℝ) {t1} = 0 := Real.volume_singleton
        exact (measure_eq_zero_iff_ae_notMem.1 this).mono fun x hx => by simpa using hx
      filter_upwards [ae_restrict_of_ae hneg, ae_restrict_of_ae h2, ae_restrict_mem measurableSet_Ioc]
        with x hx hxne hxm
      have hx1 : x ∈ Set.Ioo 0 T := ⟨lt_of_le_of_lt (hs0.trans hτ.1.le) hxm.1,
        lt_of_lt_of_le (lt_of_le_of_ne hxm.2 hxne) ht1.2⟩
      exact hx hx1 (hbig x ⟨lt_of_lt_of_le hτ.1 hxm.1.le, hxm.2⟩)
    have hint : ∫ x in τ..t1, g x ≤ 0 := by
      rw [intervalIntegral.integral_of_le hτ.2]
      exact setIntegral_nonpos_of_ae_restrict hneg'
    have h3 := hM τ t1 (hs0.trans hτ.1.le) hτ.2 ht1.2
    have h4 := hMφ s τ hsI hτI hτ.1.le
    linarith
  -- pass to the limit τ ↓ s
  have hε : 0 < M t1 - B := by linarith
  have hcs := hφc s hsI
  rw [Metric.continuousWithinAt_iff] at hcs
  obtain ⟨δ, hδ, hδ'⟩ := hcs (M t1 - B) hε
  set τ : ℝ := min t1 (s + δ / 2) with hτdef
  have hτ : τ ∈ Set.Ioc s t1 := ⟨lt_min hslt (by linarith), min_le_left _ _⟩
  have hτI : τ ∈ Set.Icc (0 : ℝ) T := ⟨hs0.trans hτ.1.le, hτ.2.trans ht1.2⟩
  have h5 := hδ' hτI (by
    rw [Real.dist_eq, abs_lt]; constructor
    · linarith [hτ.1]
    · have := min_le_right t1 (s + δ / 2); linarith)
  rw [Real.dist_eq, abs_lt] at h5
  have := hup τ hτ
  linarith [h5.2]

section Chain

variable {α : Type*} [MeasurableSpace α]

/-- The right-hand side density of the power chain inequality. -/
def s113c_Gp (Q : ℝ → Measure α) (rr R : ℝ → α → ℝ) (p : ℝ → ℝ) (τ : ℝ) : ℝ :=
  (p τ - 1) * s113_powerMass (Q τ) (rr τ) (p τ) * (∫ x, R τ x ∂(s113_powerTilt (Q τ) (rr τ) (p τ))) +
    deriv p τ * s113_powerMass (Q τ) (rr τ) (p τ) * (∫ x, Real.log (rr τ x) ∂(s113_powerTilt (Q τ) (rr τ) (p τ)))

/-- The localized power bound from the integrated one-sided chain inequality. -/
theorem s113c_chain_bound_int (Q : ℝ → Measure α) (hQ : ∀ t, 0 ≤ t → IsProbabilityMeasure (Q t))
    (rr R : ℝ → α → ℝ) (L : ℝ → ℝ) (cL C₀ p₀ : ℝ)
    (hcL : 0 < cL) (hC₀ : 0 ≤ C₀) (hp₀ : 1 < p₀)
    (hL0 : ∀ t, 0 ≤ t → 0 ≤ L t) (hLi : Integrable L (volume.restrict (Set.Ioi (0 : ℝ))))
    (hrm : ∀ t, Measurable (rr t)) (hr0 : ∀ t x, 0 ≤ rr t x)
    (hB : ∀ T : ℝ, ∃ B, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, rr t x ≤ B)
    (hsrc : ∀ᵐ t : ℝ, 0 < t → Measurable (R t) ∧ (L t = 0 → ∀ x, R t x = 0) ∧ (0 < L t →
      ∫⁻ x, ENNReal.ofReal (Real.exp ((cL / L t) * |R t x|)) ∂(Q t) ≤ ENNReal.ofReal (Real.exp C₀)))
    (hint : ∀ T : ℝ, 0 ≤ T →
      IntervalIntegrable (s113c_Gp Q rr R (r2MovExponent cL p₀ L)) volume 0 T ∧
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
        s113_powerMass (Q t) (rr t) (r2MovExponent cL p₀ L t) -
            s113_powerMass (Q s) (rr s) (r2MovExponent cL p₀ L s) ≤
          ∫ τ in s..t, s113c_Gp Q rr R (r2MovExponent cL p₀ L) τ)
    {T : ℝ} (hT : 0 ≤ T) :
    s113_powerMass (Q T) (rr T) (r2MovExponent cL p₀ L T) ≤
      max (s113_powerMass (Q 0) (rr 0) p₀) (Real.exp C₀) := by
  set p : ℝ → ℝ := r2MovExponent cL p₀ L with hp
  set M : ℝ → ℝ := fun t => s113_powerMass (Q t) (rr t) (p t) with hMdef
  set Bd : ℝ := max (s113_powerMass (Q 0) (rr 0) p₀) (Real.exp C₀) with hBd
  have hp1 : ∀ t ∈ Set.Icc (0 : ℝ) T, 1 < p t := fun t ht =>
    (s113x_exponent_bounds hcL hp₀ hL0 ht.1).1
  obtain ⟨B, hBT⟩ := hB T
  have hdp := s113x_exponent_deriv hcL hp₀ hL0 hLi hT
  have h0 : p 0 = p₀ := s113x_exponent_zero L
  have hM0 : M 0 ≤ Bd := by
    simp only [hMdef, h0]; exact le_max_left _ _
  obtain ⟨hGi, hGM⟩ := hint T hT
  refine s113c_barrier (M := M) (g := s113c_Gp Q rr R p) (T := T) (B := Bd) hT hGi
    (fun s t hs hst htT => hGM s t hs hst htT) ?_ hM0 T ⟨hT, le_rfl⟩
  filter_upwards [hdp, hsrc] with t h2 h4 ht hbig
  have htc : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1.le, ht.2.le⟩
  have hexpC : Real.exp C₀ ≤ Bd := le_max_right _ _
  have hMt : 0 < M t := lt_of_lt_of_le (Real.exp_pos C₀) (hexpC.trans hbig.le)
  have hpt : 1 < p t := hp1 t htc
  have hLt := hL0 t ht.1.le
  have := hQ t ht.1.le
  have hpd : deriv p t = -(L t / cL) * p t * (p t - 1) := (h2 ht).deriv
  obtain ⟨hint', hE3⟩ := s113_power_source_bound (Q t) (rr t) (R t) (hrm t) (h4 ht.1).1 (hr0 t)
    (p t) B cL C₀ (L t) hpt (hBT t htc) hMt hcL hC₀ hLt (h4 ht.1).2.1 (h4 ht.1).2.2
  set E : ℝ := ∫ x, R t x ∂(s113_powerTilt (Q t) (rr t) (p t)) with hE
  set G : ℝ := ∫ x, Real.log (rr t x) ∂(s113_powerTilt (Q t) (rr t) (p t)) with hG
  have hE3' : E ≤ (L t / cL) * (p t * G - Real.log (M t) + C₀) := hE3
  have hlogM : C₀ < Real.log (M t) := by
    rw [Real.lt_log_iff_exp_lt hMt]; exact lt_of_le_of_lt hexpC hbig
  have hp1' : 0 ≤ p t - 1 := by linarith
  have hstep : (p t - 1) * E ≤ (p t - 1) * ((L t / cL) * (p t * G - Real.log (M t) + C₀)) :=
    mul_le_mul_of_nonneg_left hE3' hp1'
  have hGp : s113c_Gp Q rr R p t = (p t - 1) * M t * E + deriv p t * M t * G := rfl
  rw [hGp, hpd]
  have hLc : 0 ≤ L t / cL := div_nonneg hLt hcL.le
  have hMt' : M t * ((p t - 1) * E) ≤ M t * ((p t - 1) * ((L t / cL) * (p t * G - Real.log (M t) + C₀))) :=
    mul_le_mul_of_nonneg_left hstep hMt.le
  have hneg : (p t - 1) * ((L t / cL) * (C₀ - Real.log (M t))) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hp1' (mul_nonpos_of_nonneg_of_nonpos hLc (by linarith))
  have hMn : M t * ((p t - 1) * ((L t / cL) * (C₀ - Real.log (M t)))) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hMt.le hneg
  nlinarith

end Chain

end HRS.MS.S113BD

end
