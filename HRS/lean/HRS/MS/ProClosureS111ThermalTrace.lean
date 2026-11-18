import HRS.MS.ProClosureS111CommutatorTrace
import HRS.MS.R2ChaosAux52

/-!
Integrating the physical chart traces. The squared singular envelope is
integrable by the accepted polynomial-kernel theorem with exponent two,
using precisely `2*s < d`. Thermal uniqueness puts the final constant
before the density and chart. No chart covariance or trace assumption is
introduced.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.FixEq

variable {d r : ℕ} {Pw : ℝ}

/-- A pointwise trace majorant may be integrated before taking the
infinite coefficient sum. This formulation needs no measurable choice
of individual representatives. -/
theorem summable_integral_sq_of_finite_trace {X : Type*} [MeasurableSpace X]
    (nu : Measure X) (f : ℕ → X → ℝ) (G : X → ℝ)
    (hf : ∀ i, Measurable (f i)) (hG : Integrable G nu)
    (hb : ∀ S : Finset ℕ, ∀ x, (∑ i ∈ S, f i x ^ 2) ≤ G x) :
    (∀ i, MemLp (f i) 2 nu) ∧
      Summable (fun i => ∫ x, f i x ^ 2 ∂nu) ∧
      (∑' i, ∫ x, f i x ^ 2 ∂nu) ≤ ∫ x, G x ∂nu := by
  have hi : ∀ i, Integrable (fun x => f i x ^ 2) nu := by
    intro i
    refine hG.mono' ((hf i).pow_const 2).aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simpa only [Finset.sum_singleton] using hb {i} x
  have hsum : ∀ S : Finset ℕ,
      (∑ i ∈ S, ∫ x, f i x ^ 2 ∂nu) ≤ ∫ x, G x ∂nu := by
    intro S
    rw [← integral_finset_sum _ fun i _ => hi i]
    exact integral_mono (integrable_finset_sum _ fun i _ => hi i) hG (hb S)
  have hnon : ∀ i, 0 ≤ ∫ x, f i x ^ 2 ∂nu := fun _ => integral_nonneg fun _ => sq_nonneg _
  exact ⟨fun i => (memLp_two_iff_integrable_sq (hf i).aestronglyMeasurable).2 (hi i),
    summable_of_sum_le hnon hsum, Real.tsum_le_of_sum_le hnon hsum⟩

theorem chartKernelEnvelope_poly (s Pw : ℝ) :
    HRS.Whole.IsR2PolyPairKernel s Pw 1 (chartKernelEnvelope (d := d) s Pw) where
  measurable := by
    unfold chartKernelEnvelope
    exact (((HRS.MS.R2Poly.s95_jb_meas.comp measurable_fst).add
      (HRS.MS.R2Poly.s95_jb_meas.comp measurable_snd)).pow_const Pw).mul
      (measurable_const.add ((HRS.MS.Wr.wr3_measurable_rieszWeight s).comp
        (measurable_fst.sub measurable_snd)))
  symm x y := by
    simp only [chartKernelEnvelope, HRS.Whole.rieszWeight, norm_sub_rev x y, add_comm]
  bound x y _ := by
    rw [abs_of_nonneg (chartKernelEnvelope_nonneg s Pw x y)]
    simp only [chartKernelEnvelope, one_mul]
    exact le_rfl

theorem thermal_polynomial_weight_integrable {rho : Euc d → ℝ}
    {C0 c0 a : ℝ} (hrho : HRS.Whole.IsProbDensity rho)
    (hG : HRS.Whole.HasR2GaussianUpper C0 c0 rho) (ha : 0 ≤ a) :
    Integrable (fun x => jbracket x ^ a) (HRS.Whole.withDensityReal rho) := by
  obtain ⟨C, hC⟩ := HRS.MS.R2Chaos.s94_moment_rpow hrho hG ha
  refine ⟨(HRS.MS.R2Poly.s95_jb_meas.pow_const a).aestronglyMeasurable, ?_⟩
  change (∫⁻ x, ‖jbracket x ^ a‖ₑ ∂HRS.Whole.withDensityReal rho) < ⊤
  have he : ∀ x : Euc d, ‖jbracket x ^ a‖ₑ = ENNReal.ofReal (jbracket x ^ a) := by
    intro x
    rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (s57p_jbracket_pos x).le _)]
  simp_rw [he]
  exact lt_of_le_of_lt hC ENNReal.ofReal_lt_top

/-- Both actual spatial trace series are finite for a thermal density.
The same bound works for every valid chart at the specified order and
weight. -/
theorem physical_chart_thermal_traces_at_density (hd : 2 ≤ d)
    (s a beta Pw : ℝ) (r : ℕ)
    (hs0 : 0 ≤ s) (hs : s < (d : ℝ)/2) (ha : 0 < a) (hbeta : 0 < beta)
    (hr : (2 : ℝ)+(d : ℝ)/2 < r) (hP : (d : ℝ) < 2*Pw)
    (rho : Euc d → ℝ) (hrho : HRS.Whole.IsThermalEquilibrium d s a beta rho) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ E : r26t6_WeightedChart d r Pw,
      ((∀ j, MemLp (E.test j) 2 (HRS.Whole.withDensityReal rho)) ∧
       Summable (fun j => ∫ x, E.test j x ^ 2 ∂HRS.Whole.withDensityReal rho) ∧
       (∑' j, ∫ x, E.test j x ^ 2 ∂HRS.Whole.withDensityReal rho) ≤ B) ∧
      ((∀ j, MemLp (fun xy : Euc d × Euc d =>
          HRS.Whole.commutatorKernel d s (gradient (E.test j)) xy.1 xy.2) 2
          ((HRS.Whole.withDensityReal rho).prod (HRS.Whole.withDensityReal rho))) ∧
       Summable (fun j => ∫ xy : Euc d × Euc d,
          HRS.Whole.commutatorKernel d s (gradient (E.test j)) xy.1 xy.2 ^ 2
          ∂((HRS.Whole.withDensityReal rho).prod (HRS.Whole.withDensityReal rho))) ∧
       (∑' j, ∫ xy : Euc d × Euc d,
          HRS.Whole.commutatorKernel d s (gradient (E.test j)) xy.1 xy.2 ^ 2
          ∂((HRS.Whole.withDensityReal rho).prod (HRS.Whole.withDensityReal rho))) ≤ B) := by
  obtain ⟨M, L, c, hR, hG⟩ := HRS.MS.R2S11.s11_thermal_round2 hd hs0 hs ha hbeta hrho
  have hPw : 0 ≤ Pw := by have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _; linarith
  obtain ⟨C, hC, hvalues⟩ := physical_chart_value_trace d r Pw hr hP
  obtain ⟨K, hK, hkernels⟩ := physical_chart_commutator_trace d r Pw s hr hP hs0
  let mu := HRS.Whole.withDensityReal rho
  let G1 : Euc d → ℝ := fun x => C^2 * jbracket x ^ (2*Pw)
  let G2 : Euc d × Euc d → ℝ := fun xy => K^2 * chartKernelEnvelope s Pw xy.1 xy.2 ^ 2
  have hi1 : Integrable G1 mu :=
    (thermal_polynomial_weight_integrable hR.prob hG (mul_nonneg (by norm_num) hPw)).const_mul _
  have henv : MemLp (fun xy : Euc d × Euc d => chartKernelEnvelope s Pw xy.1 xy.2)
      2 (mu.prod mu) := by
    simpa only [ENNReal.ofReal_ofNat] using HRS.MS.R2Chaos.s94_poly_memLp
      hd hs0 hs hR hG hPw zero_le_one (chartKernelEnvelope_poly (d := d) s Pw)
      (q := 2) (by norm_num) (by linarith)
  have hi2 : Integrable G2 (mu.prod mu) := henv.integrable_sq.const_mul _
  let B : ℝ := (∫ x, G1 x ∂mu) + (∫ xy, G2 xy ∂mu.prod mu)
  have hB1 : 0 ≤ ∫ x, G1 x ∂mu := integral_nonneg fun x =>
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (s57p_jbracket_pos x).le _)
  have hB2 : 0 ≤ ∫ xy, G2 xy ∂mu.prod mu := integral_nonneg fun _ =>
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  refine ⟨B, add_nonneg hB1 hB2, fun E => ?_⟩
  have h1 := summable_integral_sq_of_finite_trace mu E.test G1
    (fun j => (E.test_smooth j).1.continuous.measurable) hi1 (fun S x =>
      ((hvalues E x).1.sum_le_tsum S (fun _ _ => sq_nonneg _)).trans
        (hvalues E x).2)
  have h2 := summable_integral_sq_of_finite_trace (mu.prod mu)
    (fun j xy => HRS.Whole.commutatorKernel d s (gradient (E.test j)) xy.1 xy.2) G2
    (fun j => HRS.MS.Comm.comm_meas _
      (HRS.MH.DualityRd.db1_gradient_continuous ((E.test_smooth j).1.of_le (by norm_num))).measurable)
    hi2 (fun S xy =>
      ((hkernels E xy.1 xy.2).1.sum_le_tsum S (fun _ _ => sq_nonneg _)).trans
        (hkernels E xy.1 xy.2).2)
  exact ⟨⟨h1.1, h1.2.1, h1.2.2.trans (by dsimp [B]; linarith)⟩,
    ⟨h2.1, h2.2.1, h2.2.2.trans (by dsimp [B]; linarith)⟩⟩

/-- Quantifier order for the physical trace constant: the bound is chosen
before the thermal density and chart (and hence before preparation,
observation time, and window start). -/
theorem physical_chart_thermal_traces (hd : 2 ≤ d)
    (s a beta Pw : ℝ) (r : ℕ)
    (hs0 : 0 ≤ s) (hs : s < (d : ℝ)/2) (ha : 0 < a) (hbeta : 0 < beta)
    (hr : (2 : ℝ)+(d : ℝ)/2 < r) (hP : (d : ℝ) < 2*Pw) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ rho : Euc d → ℝ,
      HRS.Whole.IsThermalEquilibrium d s a beta rho →
      ∀ E : r26t6_WeightedChart d r Pw,
      ((∀ j, MemLp (E.test j) 2 (HRS.Whole.withDensityReal rho)) ∧
       Summable (fun j => ∫ x, E.test j x ^ 2 ∂HRS.Whole.withDensityReal rho) ∧
       (∑' j, ∫ x, E.test j x ^ 2 ∂HRS.Whole.withDensityReal rho) ≤ B) ∧
      ((∀ j, MemLp (fun xy : Euc d × Euc d =>
          HRS.Whole.commutatorKernel d s (gradient (E.test j)) xy.1 xy.2) 2
          ((HRS.Whole.withDensityReal rho).prod (HRS.Whole.withDensityReal rho))) ∧
       Summable (fun j => ∫ xy : Euc d × Euc d,
          HRS.Whole.commutatorKernel d s (gradient (E.test j)) xy.1 xy.2 ^ 2
          ∂((HRS.Whole.withDensityReal rho).prod (HRS.Whole.withDensityReal rho))) ∧
       (∑' j, ∫ xy : Euc d × Euc d,
          HRS.Whole.commutatorKernel d s (gradient (E.test j)) xy.1 xy.2 ^ 2
          ∂((HRS.Whole.withDensityReal rho).prod (HRS.Whole.withDensityReal rho))) ≤ B) := by
  by_cases hex : ∃ rho : Euc d → ℝ, HRS.Whole.IsThermalEquilibrium d s a beta rho
  · obtain ⟨rho0, hrho0⟩ := hex
    obtain ⟨B, hB, hbound⟩ := physical_chart_thermal_traces_at_density hd s a beta Pw r
      hs0 hs ha hbeta hr hP rho0 hrho0
    refine ⟨B, hB, fun rho hrho E => ?_⟩
    have hsd : s < (d : ℝ) := by have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _; linarith
    have heq : rho = rho0 := by
      rw [HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hbeta hrho,
        HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hbeta hrho0]
    simpa only [heq] using hbound E
  · exact ⟨0, le_rfl, fun rho hrho => False.elim (hex ⟨rho, hrho⟩)⟩

#print axioms physical_chart_thermal_traces

end HRS.MS.ProClosureS111
