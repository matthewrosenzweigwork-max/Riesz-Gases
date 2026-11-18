import HRS.MS.R2ChaosAux45

/-!
# HRS.MS.R2ChaosAux46 -- (e) part 1: interpolation of `W_r` between `W_2` and a higher moment

Packet S94, namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.

`s94_wass_interp`: for `r ≥ 2` and laws with `∫ ‖x‖^{2r-2} ≤ M`, `W_r(P,Q) ≤ ((W_2(P,Q) + ε) K)^{1/r}` with
`K = √(2^{2r-1} M)` (Cauchy-Schwarz on a near-optimal `W_2`-coupling).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.deprecated false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2Chaos

section Interp

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]

theorem s94_cost_le {π : Measure (B × B)} [IsProbabilityMeasure π] {P Q : Measure B}
    (hπ : HRS.IsCoupling π P Q) {r : ℝ} (hr : 2 ≤ r) {M : ℝ} (hM : 0 ≤ M)
    (hP : ∫⁻ x, ENNReal.ofReal (‖x‖ ^ (2 * r - 2)) ∂P ≤ ENNReal.ofReal M)
    (hQ : ∫⁻ x, ENNReal.ofReal (‖x‖ ^ (2 * r - 2)) ∂Q ≤ ENNReal.ofReal M) :
    ∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ r) ∂π ≤
      (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ)) ∂π) ^ (1 / (2 : ℝ)) *
        ENNReal.ofReal (Real.sqrt (2 ^ (2 * r - 1) * M)) := by
  have hm : Measurable fun z : B × B => ‖z.1 - z.2‖ :=
    (measurable_fst.sub measurable_snd).norm
  have hr1 : 0 ≤ r - 1 := by linarith
  -- pointwise factorisation
  have hfac : ∀ z : B × B, ENNReal.ofReal (‖z.1 - z.2‖ ^ r) =
      ENNReal.ofReal ‖z.1 - z.2‖ * ENNReal.ofReal (‖z.1 - z.2‖ ^ (r - 1)) := by
    intro z
    rw [← ENNReal.ofReal_mul (norm_nonneg _)]
    congr 1
    rw [← Real.rpow_one_add' (norm_nonneg _) (by linarith)]
    congr 1; ring
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq π (Real.HolderConjugate.two_two)
    (f := fun z : B × B => ENNReal.ofReal ‖z.1 - z.2‖) (g := fun z : B × B => ENNReal.ofReal (‖z.1 - z.2‖ ^ (r - 1)))
    (ENNReal.measurable_ofReal.comp hm).aemeasurable
    (ENNReal.measurable_ofReal.comp (hm.pow_const (r - 1))).aemeasurable
  refine (le_of_eq (lintegral_congr hfac)).trans (hholder.trans ?_)
  have e1 : ∫⁻ z, ENNReal.ofReal ‖z.1 - z.2‖ ^ (2 : ℝ) ∂π =
      ∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ)) ∂π := by
    refine lintegral_congr fun z => ?_
    rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
  have e2 : ∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ (r - 1)) ^ (2 : ℝ) ∂π =
      ∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 * r - 2)) ∂π := by
    refine lintegral_congr fun z => ?_
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (by norm_num),
      ← Real.rpow_mul (norm_nonneg _)]
    congr 2; ring
  rw [e1, e2]
  gcongr
  -- bound the higher moment of the difference
  have hq : (2 : ℝ) ≤ 2 * r - 2 := by linarith
  have hpt : ∀ z : B × B, ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 * r - 2)) ≤
      ENNReal.ofReal (2 ^ (2 * r - 2)) * (ENNReal.ofReal (‖z.1‖ ^ (2 * r - 2)) +
        ENNReal.ofReal (‖z.2‖ ^ (2 * r - 2))) := by
    intro z
    have hq0 : 0 ≤ 2 * r - 2 := by linarith
    rw [← ENNReal.ofReal_add (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (norm_nonneg _) _),
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : ‖z.1 - z.2‖ ≤ 2 * max ‖z.1‖ ‖z.2‖ := by
      calc ‖z.1 - z.2‖ ≤ ‖z.1‖ + ‖z.2‖ := norm_sub_le _ _
        _ ≤ 2 * max ‖z.1‖ ‖z.2‖ := by linarith [le_max_left ‖z.1‖ ‖z.2‖, le_max_right ‖z.1‖ ‖z.2‖]
    calc ‖z.1 - z.2‖ ^ (2 * r - 2) ≤ (2 * max ‖z.1‖ ‖z.2‖) ^ (2 * r - 2) :=
          Real.rpow_le_rpow (norm_nonneg _) h1 hq0
      _ = 2 ^ (2 * r - 2) * max ‖z.1‖ ‖z.2‖ ^ (2 * r - 2) :=
          Real.mul_rpow (by norm_num) (le_max_of_le_left (norm_nonneg _))
      _ ≤ 2 ^ (2 * r - 2) * (‖z.1‖ ^ (2 * r - 2) + ‖z.2‖ ^ (2 * r - 2)) := by
          gcongr
          rcases le_total ‖z.1‖ ‖z.2‖ with h | h
          · rw [max_eq_right h]
            have := Real.rpow_nonneg (norm_nonneg z.1) (2 * r - 2)
            linarith
          · rw [max_eq_left h]
            have := Real.rpow_nonneg (norm_nonneg z.2) (2 * r - 2)
            linarith
  have h1 : ∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 * r - 2)) ∂π ≤
      ENNReal.ofReal (2 ^ (2 * r - 2)) * (∫⁻ z, ENNReal.ofReal (‖z.1‖ ^ (2 * r - 2)) ∂π +
        ∫⁻ z, ENNReal.ofReal (‖z.2‖ ^ (2 * r - 2)) ∂π) := by
    refine (lintegral_mono hpt).trans ?_
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left]
    exact (ENNReal.measurable_ofReal.comp (measurable_fst.norm.pow_const _))
  have hfm : Measurable fun x : B => ENNReal.ofReal (‖x‖ ^ (2 * r - 2)) :=
    ENNReal.measurable_ofReal.comp (continuous_norm.measurable.pow_const _)
  have hm1 : ∫⁻ z, ENNReal.ofReal (‖z.1‖ ^ (2 * r - 2)) ∂π = ∫⁻ x, ENNReal.ofReal (‖x‖ ^ (2 * r - 2)) ∂P := by
    have := lintegral_map (μ := π) hfm measurable_fst
    rw [hπ.1] at this
    exact this.symm
  have hm2 : ∫⁻ z, ENNReal.ofReal (‖z.2‖ ^ (2 * r - 2)) ∂π = ∫⁻ x, ENNReal.ofReal (‖x‖ ^ (2 * r - 2)) ∂Q := by
    have := lintegral_map (μ := π) hfm measurable_snd
    rw [hπ.2] at this
    exact this.symm
  rw [hm1, hm2] at h1
  have h2 : ∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 * r - 2)) ∂π ≤ ENNReal.ofReal (2 ^ (2 * r - 1) * M) := by
    refine h1.trans ?_
    have : ENNReal.ofReal (2 ^ (2 * r - 1) * M) = ENNReal.ofReal (2 ^ (2 * r - 2)) * (ENNReal.ofReal M + ENNReal.ofReal M) := by
      rw [← ENNReal.ofReal_add hM hM, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [show 2 * r - 1 = (2 * r - 2) + 1 by ring, Real.rpow_add (by norm_num), Real.rpow_one]
      ring
    rw [this]
    gcongr
  have hsq : (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 * r - 2)) ∂π) ^ (1 / (2 : ℝ)) ≤
      ENNReal.ofReal (Real.sqrt (2 ^ (2 * r - 1) * M)) := by
    refine (ENNReal.rpow_le_rpow h2 (by norm_num)).trans (le_of_eq ?_)
    rw [Real.sqrt_eq_rpow, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
  exact hsq

theorem s94_wass_interp (P Q : Measure B) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] {r : ℝ}
    (hr : 2 ≤ r) {M : ℝ} (hM : 0 ≤ M)
    (hP : ∫⁻ x, ENNReal.ofReal (‖x‖ ^ (2 * r - 2)) ∂P ≤ ENNReal.ofReal M)
    (hQ : ∫⁻ x, ENNReal.ofReal (‖x‖ ^ (2 * r - 2)) ∂Q ≤ ENNReal.ofReal M)
    (hW : HRS.wassersteinE 2 P Q ≠ ⊤) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    HRS.wassersteinE r P Q ≤ ((HRS.wassersteinE 2 P Q + ε) * ENNReal.ofReal (Real.sqrt (2 ^ (2 * r - 1) * M))) ^ (1 / r) := by
  have hlt : HRS.wassersteinE 2 P Q < HRS.wassersteinE 2 P Q + ε := ENNReal.lt_add_right hW hε
  have hlt' := hlt
  unfold HRS.wassersteinE at hlt'
  obtain ⟨π, hπ⟩ := (iInf_lt_iff.1 (lt_of_le_of_lt le_rfl hlt'))
  have hπc : HRS.IsCoupling π.1 P Q := π.2
  haveI : IsProbabilityMeasure π.1 := by
    refine ⟨?_⟩
    have := congrArg (fun m : Measure B => m Set.univ) hπc.1
    simp only [Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ] at this
    rw [this]; exact measure_univ
  have h1 : HRS.wassersteinE r P Q ≤ (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ r) ∂π.1) ^ (1 / r) :=
    iInf_le (fun π : HRS.couplings P Q => (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ r) ∂π.1) ^ (1 / r)) π
  refine h1.trans (ENNReal.rpow_le_rpow ?_ (by positivity))
  refine (s94_cost_le hπc hr hM hP hQ).trans ?_
  exact mul_le_mul_left hπ.le _

end Interp

end HRS.MS.R2Chaos
