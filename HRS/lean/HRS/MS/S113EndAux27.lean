import HRS.MS.S113EndAux26

/-!
# S11.3 endpoint (worker S11X), part 27: the localized power bound with the source moment for almost every time

Copies of `s113x_chain_bound` (part 3) and `s113x_power_bound` (part 5) in which the three hypotheses on the source are
required only for almost every `t > 0` (they are used only inside the almost-everywhere differential inequality).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.MS.S113BD

open HRS.Whole
open HRS (Euc)

section Chain

variable {α : Type*} [MeasurableSpace α]

theorem s113x_chain_bound_ae (Q : ℝ → Measure α) (hQ : ∀ t, 0 ≤ t → IsProbabilityMeasure (Q t))
    (rr R : ℝ → α → ℝ) (L : ℝ → ℝ) (cL C₀ p₀ : ℝ)
    (hcL : 0 < cL) (hC₀ : 0 ≤ C₀) (hp₀ : 1 < p₀)
    (hL0 : ∀ t, 0 ≤ t → 0 ≤ L t) (hLi : Integrable L (volume.restrict (Set.Ioi (0 : ℝ))))
    (hrm : ∀ t, Measurable (rr t)) (hr0 : ∀ t x, 0 ≤ rr t x)
    (hB : ∀ T : ℝ, ∃ B, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, rr t x ≤ B)
    (hsrc : ∀ᵐ t : ℝ, 0 < t → Measurable (R t) ∧ (L t = 0 → ∀ x, R t x = 0) ∧ (0 < L t →
      ∫⁻ x, ENNReal.ofReal (Real.exp ((cL / L t) * |R t x|)) ∂(Q t) ≤ ENNReal.ofReal (Real.exp C₀)))
    (hmass : ∀ t, 0 ≤ t → 0 < s113_powerMass (Q t) (rr t) (r2MovExponent cL p₀ L t))
    (hac : ∀ T : ℝ, 0 ≤ T → AbsolutelyContinuousOnInterval
      (fun t => s113_powerMass (Q t) (rr t) (r2MovExponent cL p₀ L t)) 0 T)
    (hode : ∀ T : ℝ, 0 ≤ T → ∀ᵐ t : ℝ, t ∈ Set.Ioo 0 T →
      deriv (fun u => s113_powerMass (Q u) (rr u) (r2MovExponent cL p₀ L u)) t ≤
        (r2MovExponent cL p₀ L t - 1) * s113_powerMass (Q t) (rr t) (r2MovExponent cL p₀ L t) *
            (∫ x, R t x ∂(s113_powerTilt (Q t) (rr t) (r2MovExponent cL p₀ L t))) +
          deriv (r2MovExponent cL p₀ L) t * s113_powerMass (Q t) (rr t) (r2MovExponent cL p₀ L t) *
            (∫ x, Real.log (rr t x) ∂(s113_powerTilt (Q t) (rr t) (r2MovExponent cL p₀ L t))))
    {T : ℝ} (hT : 0 ≤ T) :
    s113_powerMass (Q T) (rr T) (r2MovExponent cL p₀ L T) ≤
      max (s113_powerMass (Q 0) (rr 0) p₀) (Real.exp C₀) := by
  set p : ℝ → ℝ := r2MovExponent cL p₀ L with hp
  set M : ℝ → ℝ := fun t => s113_powerMass (Q t) (rr t) (p t) with hMdef
  have hp1 : ∀ t ∈ Set.Icc (0 : ℝ) T, 1 < p t := fun t ht =>
    (s113x_exponent_bounds hcL hp₀ hL0 ht.1).1
  have hpac := s113x_exponent_ac hcL hp₀ hL0 hLi hT
  have hMac := hac T hT
  have hMpos : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 < M t := fun t ht => hmass t ht.1
  have hΨac := s113x_log_ac hT hMac hMpos
  obtain ⟨B, hBT⟩ := hB T
  have hae := hode T hT
  have hdp := s113x_exponent_deriv hcL hp₀ hL0 hLi hT
  have hMd := hMac.ae_differentiableAt
  have hder : ∀ᵐ t : ℝ, t ∈ Set.Ioo 0 T →
      deriv (fun u => Real.log (M u)) t ≤ deriv p t / p t * (Real.log (M t) - C₀) := by
    filter_upwards [hae, hdp, hMd, hsrc] with t h1 h2 h3 h4 ht
    have htI : t ∈ Set.uIcc (0 : ℝ) T := by rw [Set.uIcc_of_le hT]; exact ⟨ht.1.le, ht.2.le⟩
    have htc : t ∈ Set.Icc (0 : ℝ) T := ⟨ht.1.le, ht.2.le⟩
    have hMt : 0 < M t := hMpos t htc
    have hpt : 1 < p t := hp1 t htc
    have hLt := hL0 t ht.1.le
    have := hQ t ht.1.le
    have hMdiff := (h3 htI).hasDerivAt
    have hlog : deriv (fun u => Real.log (M u)) t = deriv M t / M t := (hMdiff.log hMt.ne').deriv
    have hpd : deriv p t = -(L t / cL) * p t * (p t - 1) := (h2 ht).deriv
    have h1' := h1 ht
    -- E3 at time t
    obtain ⟨hint, hE3⟩ := s113_power_source_bound (Q t) (rr t) (R t) (hrm t) (h4 ht.1).1 (hr0 t)
      (p t) B cL C₀ (L t) hpt (hBT t htc) hMt hcL hC₀ hLt (h4 ht.1).2.1
      (h4 ht.1).2.2
    set E : ℝ := ∫ x, R t x ∂(s113_powerTilt (Q t) (rr t) (p t)) with hE
    set G : ℝ := ∫ x, Real.log (rr t x) ∂(s113_powerTilt (Q t) (rr t) (p t)) with hG
    have hM' : deriv M t ≤ (p t - 1) * M t * E + deriv p t * M t * G := h1'
    have hdiv : deriv M t / M t ≤ (p t - 1) * E + deriv p t * G := by
      rw [div_le_iff₀ hMt]
      nlinarith
    have hmassE : s113_powerMass (Q t) (rr t) (p t) = M t := rfl
    have hE3' : E ≤ (L t / cL) * (p t * G - Real.log (M t) + C₀) := by
      rw [hmassE] at hE3
      exact hE3
    have hp1' : 0 ≤ p t - 1 := by linarith
    have hstep : (p t - 1) * E ≤ (p t - 1) * ((L t / cL) * (p t * G - Real.log (M t) + C₀)) :=
      mul_le_mul_of_nonneg_left hE3' hp1'
    rw [hlog]
    have hp0 : p t ≠ 0 := by linarith
    have heq : deriv p t / p t = -(L t / cL) * (p t - 1) := by
      rw [hpd]; field_simp
    rw [heq]
    rw [hpd] at hdiv
    nlinarith
  have hG := s113x_gronwall hT hΨac hpac hp1 hder
  have h0 : p 0 = p₀ := s113x_exponent_zero L
  have hpT : 0 < p T := by linarith [hp1 T ⟨hT, le_rfl⟩]
  have hle : p T ≤ p 0 := by
    rw [h0]; exact (s113x_exponent_bounds hcL hp₀ hL0 hT).2
  have hb := s113x_exp_bound hpT hle hG
  have hMT : 0 < M T := hMpos T ⟨hT, le_rfl⟩
  have hM0 : 0 < M 0 := hMpos 0 ⟨le_rfl, hT⟩
  have hM0' : M 0 = s113_powerMass (Q 0) (rr 0) p₀ := by simp only [hMdef, h0]
  calc M T = Real.exp (Real.log (M T)) := (Real.exp_log hMT).symm
    _ ≤ Real.exp (max (Real.log (M 0)) C₀) := Real.exp_le_exp.2 hb
    _ = max (M 0) (Real.exp C₀) := by
      rcases le_total (Real.log (M 0)) C₀ with h | h
      · rw [max_eq_right h, max_eq_right]
        rw [← Real.exp_log hM0]; exact Real.exp_le_exp.2 h
      · rw [max_eq_left h, max_eq_left]
        · exact Real.exp_log hM0
        · rw [← Real.exp_log hM0]; exact Real.exp_le_exp.2 h
    _ = _ := by rw [hM0']

end Chain

section Bound

variable {d : ℕ}

/-- The power bound for one particle setup, from the cores X1 (specialized to the trajectory) and X2. -/
theorem s113x_power_bound_ae {s q β : ℝ} {ρ₀ : Euc d → ℝ} {j m : ℕ} {εstar r c₀ : ℝ}
    (hX2 : S113XLocalized d s q β ρ₀ j m εstar r c₀) {f0 : Euc d → ℝ}
    (hf0 : MovInitialClass ρ₀ j m εstar f0) {ρ : ℝ → Euc d → ℝ}
    (hρ : MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ) {cL C₀ : ℝ} (hcL : 0 < cL) (hC₀ : 0 ≤ C₀)
    (hLi : Integrable (r2MovL d s q β ρ) (volume.restrict (Set.Ioi (0 : ℝ))))
    (hsrc : ∀ N : ℕ, 2 ≤ N → ∀ᵐ t : ℝ, 0 < t →
        Measurable (s113x_source d s q β N ρ t) ∧
        (r2MovL d s q β ρ t = 0 → ∀ X, s113x_source d s q β N ρ t X = 0) ∧
        (0 < r2MovL d s q β ρ t →
          ∫⁻ X, ENNReal.ofReal (Real.exp ((cL / r2MovL d s q β ρ t) * |s113x_source d s q β N ρ t X|))
              ∂(s113x_Q d s β ρ N t) ≤ ENNReal.ofReal (Real.exp C₀)))
    {N : ℕ} (hN : 2 ≤ N) (hQ : ∀ t : ℝ, 0 ≤ t → IsProbabilityMeasure (s113x_Q d s β ρ N t))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
    (hsetup : MovParticleSetup P d s q β N X₀ W X)
    (hac0 : P.map X₀ ≪ s113x_Q d s β ρ N 0) {p₀ : ℝ} (hp₀ : 1 < p₀) {K₀ : ℝ}
    (hM0 : r2MovPowerMoment d s β ρ N (P.map X₀) 0 p₀ ≤ ENNReal.ofReal K₀) (t : ℝ) (ht : 0 ≤ t) :
    P.map (X t.toNNReal) ≪ s113x_Q d s β ρ N t ∧
      r2MovPowerMoment d s β ρ N (P.map (X t.toNNReal)) t
        (r2MovExponent cL p₀ (r2MovL d s q β ρ) t) ≤
        ENNReal.ofReal (max (max K₀ 0 + 1) (Real.exp C₀)) := by
  have hfin : r2MovPowerMoment d s β ρ N (P.map X₀) 0 p₀ < ⊤ :=
    lt_of_le_of_lt hM0 ENNReal.ofReal_lt_top
  obtain ⟨rr, hrm, hr0, hrB, hconv, hinit, hode⟩ :=
    hX2 f0 hf0 ρ hρ N hN P X₀ W X hsetup hac0 p₀ hp₀ hfin
  obtain ⟨hacT, hL1⟩ := hconv t ht
  refine ⟨hacT, ?_⟩
  set L : ℝ → ℝ := r2MovL d s q β ρ with hL
  have hL0 : ∀ u, 0 ≤ u → 0 ≤ L u := fun u _ => ENNReal.toReal_nonneg
  set p : ℝ → ℝ := r2MovExponent cL p₀ L with hp
  have hpb : ∀ u, 0 ≤ u → 1 < p u := fun u hu => (s113x_exponent_bounds hcL hp₀ hL0 hu).1
  have hpac : ∀ T, 0 ≤ T → AbsolutelyContinuousOnInterval p 0 T := fun T hT =>
    s113x_exponent_ac hcL hp₀ hL0 hLi hT
  set K : ℝ := max (max K₀ 0 + 1) (Real.exp C₀) with hK
  -- the bound for every localization
  have hbound : ∀ n : ℕ, ∫⁻ x, ENNReal.ofReal (rr n t x ^ p t) ∂(s113x_Q d s β ρ N t) ≤ ENNReal.ofReal K := by
    intro n
    obtain ⟨hmass, hmain⟩ := hode p hpac hpb n
    have := hQ t ht
    obtain ⟨B, hBt⟩ := hrB n t
    rw [s113x_lintegral_eq_mass (s113x_Q d s β ρ N t) (rr n t) (hrm n t) (hr0 n t) (p t) B (hpb t ht) (hBt t ⟨ht, le_rfl⟩)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hch := s113x_chain_bound_ae (fun u => s113x_Q d s β ρ N u) hQ (fun u => rr n u)
      (fun u => s113x_source d s q β N ρ u) L cL C₀ p₀ hcL hC₀ hp₀ hL0 hLi (hrm n) (hr0 n) (hrB n)
      (hsrc N hN) hmass (fun T hT => (hmain T hT).1) (fun T hT => (hmain T hT).2)
      ht
    refine hch.trans (max_le_max ?_ le_rfl)
    -- initial mass
    have := hQ 0 le_rfl
    obtain ⟨B0, hB0⟩ := hrB n 0
    have h0 := hinit n
    have hl := s113x_lintegral_eq_mass (s113x_Q d s β ρ N 0) (rr n 0) (hrm n 0) (hr0 n 0) p₀ B0 hp₀ (hB0 0 ⟨le_rfl, le_rfl⟩)
    rw [hl] at h0
    have hMfin : r2MovPowerMoment d s β ρ N (P.map X₀) 0 p₀ + ENNReal.ofReal (1 / ((n : ℝ) + 1)) ≠ ⊤ :=
      ENNReal.add_ne_top.2 ⟨hfin.ne, ENNReal.ofReal_ne_top⟩
    have h1 := ENNReal.toReal_mono hMfin h0
    rw [ENNReal.toReal_ofReal (s113x_mass_nonneg _ _ _ (hr0 n 0))] at h1
    rw [ENNReal.toReal_add hfin.ne ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (by positivity)] at h1
    have h2 : (r2MovPowerMoment d s β ρ N (P.map X₀) 0 p₀).toReal ≤ max K₀ 0 := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hM0
      rwa [ENNReal.toReal_ofReal'] at this
    have h3 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    linarith
  -- Fatou along an a.e. subsequence
  have := hQ t ht
  have hhm : Measurable (r2MovRatio d s β ρ N (P.map (X t.toNNReal)) t) :=
    (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hh0 : ∀ x, 0 ≤ r2MovRatio d s β ρ N (P.map (X t.toNNReal)) t x := fun x => ENNReal.toReal_nonneg
  have := s113x_limit_bound (s113x_Q d s β ρ N t) (fun n => rr n t)
    (r2MovRatio d s β ρ N (P.map (X t.toNNReal)) t) (fun n => hrm n t) (fun n => hr0 n t) hhm hh0
    (p t) K (hpb t ht) hL1 hbound
  exact this

end Bound

end HRS.MS.S113BD
