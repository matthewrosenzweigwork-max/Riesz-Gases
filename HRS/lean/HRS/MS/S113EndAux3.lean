import HRS.MS.S113EndAux2
import HRS.MS.S113PowerAux3

/-!
# S11.3 endpoint (worker S113X), part 3: the localized power bound `M_n(t) ≤ max(M_n(0), e^{C₀})`

Abstract chain argument (no particle system): given probability measures `Q_t`, bounded measurable nonnegative ratios `r_t`, a
source `R_t` with the exponential moment of `W:eq:r2-moving-source-exponential`, and the power-chain differential inequality
`M' ≤ (p-1) M E_P R + p' M E_P log r` (`P` the power tilt) for the mass `M(t) = ∫ r_t^{p(t)} dQ_t` with the exponent
`p = r2MovExponent` of `W:eq:r2-moving-power`, the mass satisfies `M(t) ≤ max(M(0), e^{C₀})`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.MS.S113BD

open HRS.Whole

theorem s113x_log_ac {M : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T) (hM : AbsolutelyContinuousOnInterval M 0 T)
    (hpos : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 < M t) :
    AbsolutelyContinuousOnInterval (fun t => Real.log (M t)) 0 T := by
  have hcont : ContinuousOn M (Set.Icc 0 T) := by
    have := hM.continuousOn
    rwa [Set.uIcc_of_le hT] at this
  obtain ⟨t₁, ht₁, hmin⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 hT) hcont
  obtain ⟨t₂, ht₂, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 hT) hcont
  have hm : 0 < M t₁ := hpos t₁ ht₁
  have hcd : ContDiffOn ℝ 1 Real.log (Set.Icc (M t₁) (M t₂)) :=
    (Real.contDiffOn_log (n := 1)).mono (fun x hx => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact (lt_of_lt_of_le hm hx.1).ne')
  obtain ⟨K, hK⟩ := hcd.exists_lipschitzOnWith (by decide) (convex_Icc _ _) isCompact_Icc
  exact hK.comp_absolutelyContinuousOnInterval (a := 0) (b := T) (g := M)
    (fun t ht => by
      rw [Set.uIcc_of_le hT] at ht
      exact ⟨hmin ht, hmax ht⟩) hM

section Chain

variable {α : Type*} [MeasurableSpace α]

theorem s113x_chain_bound (Q : ℝ → Measure α) (hQ : ∀ t, 0 ≤ t → IsProbabilityMeasure (Q t))
    (rr R : ℝ → α → ℝ) (L : ℝ → ℝ) (cL C₀ p₀ : ℝ)
    (hcL : 0 < cL) (hC₀ : 0 ≤ C₀) (hp₀ : 1 < p₀)
    (hL0 : ∀ t, 0 ≤ t → 0 ≤ L t) (hLi : Integrable L (volume.restrict (Set.Ioi (0 : ℝ))))
    (hrm : ∀ t, Measurable (rr t)) (hr0 : ∀ t x, 0 ≤ rr t x)
    (hB : ∀ T : ℝ, ∃ B, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x, rr t x ≤ B)
    (hRm : ∀ t, 0 ≤ t → Measurable (R t))
    (hzero : ∀ t, 0 ≤ t → L t = 0 → ∀ x, R t x = 0)
    (hexp : ∀ t, 0 ≤ t → 0 < L t →
      ∫⁻ x, ENNReal.ofReal (Real.exp ((cL / L t) * |R t x|)) ∂(Q t) ≤ ENNReal.ofReal (Real.exp C₀))
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
    filter_upwards [hae, hdp, hMd] with t h1 h2 h3 ht
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
    obtain ⟨hint, hE3⟩ := s113_power_source_bound (Q t) (rr t) (R t) (hrm t) (hRm t ht.1.le) (hr0 t)
      (p t) B cL C₀ (L t) hpt (hBT t htc) hMt hcL hC₀ hLt (hzero t ht.1.le)
      (hexp t ht.1.le)
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

end HRS.MS.S113BD
