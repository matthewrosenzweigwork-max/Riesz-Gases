import HRS.MS.R26T8AR09a
import HRS.MS.WadAux22

/-!
# S8.2 observed-time layer, packet T8A.R10: conditional repulsion bound (corrected version)
The Pro packet statement has no hypothesis `0 < a`; the integrability of `q (. - x)` against the thermal law (hence the
Jensen lower bound for the one-site partition function) needs the Gaussian bound of the thermal density, which needs
`0 < a`.  Corrected version: `r26t8a_conditional_repulsion_pos` with the extra hypothesis `(ha : 0 < a)`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.MS.R26T8A
open HRS.MS.Phase2S82

theorem r26t8a_conditional_repulsion_pos {d p n : ℕ} (hd : 2 ≤ d) {a beta C0 : ℝ} (ha : 0 < a)
    (hbeta : 0 < beta) {rho q : Euc d → ℝ} {h : ℕ → Euc d → ℝ}
    (hrho : HRS.Whole.IsThermalEquilibrium d (criticalS d) a beta rho)
    (hcal : CalibratedReferenceData d a beta rho q h C0) (N : ℕ) (hN : 2 ≤ N)
    (hnp : n + p ≤ N) (pins : Fin p → Euc d) (i : Fin n) (X : HRS.Whole.EucConfig d n) :
    resampleLaw q h (HRS.Whole.withDensityReal rho) beta N pins i X ≤
      ENNReal.ofReal (Real.exp (2 + 2 / 1000)) •
        (HRS.Whole.withDensityReal rho).withDensity (fun y => ENNReal.ofReal
          (Real.exp (-(beta / N) * ((∑ j ∈ Finset.univ.erase i, q (y - X j)) +
            ∑ j, q (y - pins j))))) := by
  haveI hμ : IsProbabilityMeasure (HRS.Whole.withDensityReal rho) :=
    HRS.Whole.Q09A.measure_isProb hrho.2.1
  set μ : Measure (Euc d) := HRS.Whole.withDensityReal rho with hμdef
  have hq := hcal.short
  have hqm : Measurable q := hq.measurable
  have hhm : Measurable (h N) := hcal.hmeas N
  have hconv := HRS.MS.S82P2.s82p2_conv_measurable hqm μ
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  -- Gaussian upper bound and integrability of q(. - x)
  obtain ⟨-, C, c, hC, hc, hb⟩ := HRS.MS.Wad.s84_thermal_gaussReg hd ha hbeta hrho
  have hG : HRS.Whole.HasR2GaussianUpper (C + 1) c rho := ⟨hc, fun x => by
    have h1 := (le_abs_self (rho x)).trans (hb x).1
    nlinarith [Real.exp_pos (-c * ‖x‖ ^ 2)]⟩
  have hint : ∀ x : Euc d, Integrable (fun z => q (z - x)) μ := fun x =>
    HRS.MS.S82P2.s82p2_q_integrable hd hq (C + 1) c (by linarith) hc rho hrho.2.1 hG x
  have hmass : ∀ x : Euc d, ∫ z, q (z - x) ∂μ ≤ 1 / (1000 * beta) := by
    intro x
    have h1 := hcal.small_row x
    have e : ∫ z, q (z - x) ∂μ = HRS.Whole.convMeasure q μ x := by
      unfold HRS.Whole.convMeasure
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      show q (z - x) = q (x - z)
      rw [← hq.even (x - z), neg_sub]
    rw [e, le_div_iff₀ (by positivity)]
    nlinarith
  -- the pair/pin interaction
  set S : Euc d → ℝ := fun y => (∑ j ∈ Finset.univ.erase i, q (y - X j)) + ∑ j, q (y - pins j) with hS
  have hSnn : ∀ y, 0 ≤ S y := fun y => add_nonneg (Finset.sum_nonneg fun j _ => hq.nonneg _)
    (Finset.sum_nonneg fun j _ => hq.nonneg _)
  have hSm : Measurable S := by
    simp only [hS]
    exact (Finset.measurable_sum _ fun j _ => hqm.comp (measurable_id.sub_const _)).add
      (Finset.measurable_sum _ fun j _ => hqm.comp (measurable_id.sub_const _))
  have hSint : Integrable S μ :=
    (integrable_finset_sum _ fun j _ => hint (X j)).add (integrable_finset_sum _ fun j _ => hint (pins j))
  have hSmass : ∫ y, S y ∂μ ≤ (N : ℝ) * (1 / (1000 * beta)) := by
    simp only [hS]
    rw [integral_add (integrable_finset_sum _ fun j _ => hint (X j))
      (integrable_finset_sum _ fun j _ => hint (pins j)),
      integral_finset_sum _ fun j _ => hint (X j), integral_finset_sum _ fun j _ => hint (pins j)]
    have e1 := Finset.sum_le_card_nsmul (Finset.univ.erase i) (fun j => ∫ y, q (y - X j) ∂μ)
      (1 / (1000 * beta)) fun j _ => hmass (X j)
    have e2 := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin p)) (fun j => ∫ y, q (y - pins j) ∂μ)
      (1 / (1000 * beta)) fun j _ => hmass (pins j)
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at e1
    rw [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at e2
    have hB : (0 : ℝ) ≤ 1 / (1000 * beta) := by positivity
    have hn : ((n - 1 : ℕ) : ℝ) + p ≤ N := by
      have : n - 1 + p ≤ N := by omega
      exact_mod_cast this
    nlinarith
  -- the one-site exponent
  set ψ : Euc d → ℝ := fun y => beta * HRS.Whole.convMeasure q μ y + h N y - (beta / N) * S y with hψ
  have hψm : Measurable ψ := by
    simp only [hψ]
    exact ((measurable_const.mul hconv).add hhm).sub (measurable_const.mul hSm)
  have hψb : ∀ y, ψ y ≤ (1 + 1 / 1000) + (-(beta / N) * S y) := fun y => by
    have : beta * HRS.Whole.convMeasure q μ y + h N y - (beta / N) * 0 ≤ 1 + 1 / 1000 :=
      r26t8a_r09_psi_le hbeta hcal hN y le_rfl
    simp only [hψ]; linarith
  obtain ⟨hψi, hψpos, -⟩ := r26t8a_r09_tilt_bdd μ ψ hψm _ fun y =>
    r26t8a_r09_psi_le hbeta hcal hN y (hSnn y)
  set u : Euc d → ℝ := fun y => -(beta / N) * S y with hu
  have hum : Measurable u := measurable_const.mul hSm
  obtain ⟨hui, -, -⟩ := r26t8a_r09_tilt_bdd μ u hum 0 fun y => by
    have : 0 ≤ (beta / N) * S y := by have := hSnn y; positivity
    simp only [hu]; linarith
  -- Jensen
  have hjen : Real.exp (∫ y, u y ∂μ) ≤ ∫ y, Real.exp (u y) ∂μ :=
    convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
      (ae_of_all _ fun _ => Set.mem_univ _) (hSint.const_mul (-(beta / N))) hui
  have hum' : ∫ y, u y ∂μ = -(beta / N) * ∫ y, S y ∂μ := by
    simp only [hu]; rw [integral_const_mul]
  have hmu : -(1 / 1000 : ℝ) ≤ ∫ y, u y ∂μ := by
    rw [hum']
    have h1 : (beta / N) * ∫ y, S y ∂μ ≤ (beta / N) * ((N : ℝ) * (1 / (1000 * beta))) :=
      mul_le_mul_of_nonneg_left hSmass (by positivity)
    have h2 : (beta / N) * ((N : ℝ) * (1 / (1000 * beta))) = 1 / 1000 := by field_simp
    linarith
  -- lower bound of the partition function
  have hψlow : ∀ y, Real.exp (-1) * Real.exp (u y) ≤ Real.exp (ψ y) := fun y => by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have h1 : 0 ≤ beta * HRS.Whole.convMeasure q μ y :=
      mul_nonneg hbeta.le (integral_nonneg fun z => hq.nonneg _)
    have h2 := (abs_le.1 (hcal.hsmall N hN y)).1
    simp only [hψ, hu]
    linarith
  have hZlow : Real.exp (-1) * Real.exp (-(1 / 1000)) ≤ ∫ y, Real.exp (ψ y) ∂μ := by
    calc Real.exp (-1) * Real.exp (-(1 / 1000))
        ≤ Real.exp (-1) * ∫ y, Real.exp (u y) ∂μ :=
          mul_le_mul_of_nonneg_left ((Real.exp_le_exp.2 hmu).trans hjen) (Real.exp_pos _).le
      _ = ∫ y, Real.exp (-1) * Real.exp (u y) ∂μ := (integral_const_mul _ _).symm
      _ ≤ _ := integral_mono (hui.const_mul _) hψi hψlow
  -- assemble
  unfold resampleLaw exponentialTilt
  refine Measure.le_iff.2 fun s hs => ?_
  rw [Measure.smul_apply, Measure.smul_apply, withDensity_apply _ hs, withDensity_apply _ hs, smul_eq_mul,
    smul_eq_mul]
  set e1 : ℝ := Real.exp (1 + 1 / 1000) with he1
  have hinv : (ENNReal.ofReal (∫ y, Real.exp (ψ y) ∂μ))⁻¹ ≤ ENNReal.ofReal e1 := by
    have h1 : ENNReal.ofReal (Real.exp (-1) * Real.exp (-(1 / 1000))) ≤
        ENNReal.ofReal (∫ y, Real.exp (ψ y) ∂μ) := ENNReal.ofReal_le_ofReal hZlow
    have h2 : (ENNReal.ofReal (Real.exp (-1) * Real.exp (-(1 / 1000))))⁻¹ = ENNReal.ofReal e1 := by
      rw [← ENNReal.ofReal_inv_of_pos (by positivity), ← Real.exp_add, ← Real.exp_neg, he1]
      congr 2; ring
    rw [← h2]
    exact ENNReal.inv_le_inv.2 h1
  have hpt : ∫⁻ y in s, ENNReal.ofReal (Real.exp (ψ y)) ∂μ ≤
      ENNReal.ofReal e1 * ∫⁻ y in s, ENNReal.ofReal (Real.exp (-(beta / N) * S y)) ∂μ := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun y => ?_
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by have := hψb y; linarith))
  calc (ENNReal.ofReal (∫ y, Real.exp (ψ y) ∂μ))⁻¹ * ∫⁻ y in s, ENNReal.ofReal (Real.exp (ψ y)) ∂μ
      ≤ ENNReal.ofReal e1 * (ENNReal.ofReal e1 *
          ∫⁻ y in s, ENNReal.ofReal (Real.exp (-(beta / N) * S y)) ∂μ) := mul_le_mul' hinv hpt
    _ = ENNReal.ofReal (Real.exp (2 + 2 / 1000)) *
          ∫⁻ y in s, ENNReal.ofReal (Real.exp (-(beta / N) * S y)) ∂μ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, he1, ← Real.exp_add]
      congr 3; ring

end HRS.MS.R26T8A
