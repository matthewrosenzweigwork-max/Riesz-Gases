import HRS.MS.R26T8AR05b

/-!
# S8.2 local Newton layer, packet T8A.R05: physical canonical Gibbs measure as an exponential tilt of the product thermal law
`r26t8a_canonical_exponent`: `canonicalP d N a beta = exponentialTilt (⊗ withDensityReal rho) (β ∑ U(X i) - β/(2N) pairSum g X)` with `U = g * μ`
(Euler–Lagrange identity `ρ = e^{-β(V+U)}/Z`, ordered pair sum `= 2 ∑_{i<j}`, cancellation of the positive constant `Z^{-N}`).
Statement as in the Pro packet with `HRS.Whole.withDensityReal`, `HRS.Whole.convMeasure`, `HRS.MS.Phase2S82.pairSum` (the unqualified names resolve to torus versions).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal

namespace HRS.MS.R26T8A
open HRS.MS.Phase2S82

theorem r26t8a_canonical_exponent (d N : ℕ) (hd : 2 ≤ d) (hN : 1 ≤ N)
    (a beta : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (rho : Euc d → ℝ)
    (hrho : HRS.Whole.IsThermalEquilibrium d (criticalS d) a beta rho) :
    canonicalP d N a beta = exponentialTilt (Measure.pi (fun _ : Fin N => HRS.Whole.withDensityReal rho))
      (fun X => beta * ∑ i, HRS.Whole.convMeasure (HRS.Whole.rieszKernel d (criticalS d)) (HRS.Whole.withDensityReal rho) (X i) -
        beta / (2 * N) * HRS.MS.Phase2S82.pairSum (fun x y => HRS.Whole.rieszKernel d (criticalS d) (x - y)) X) := by
  set s : ℝ := criticalS d with hs
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hs0 : s ≠ 0 := by
    have : 0 < criticalS d := by unfold criticalS; positivity
    exact this.ne'
  set g : Euc d → ℝ := HRS.Whole.rieszKernel d s with hg
  set V : Euc d → ℝ := HRS.Whole.confinement a with hV
  set μ : MeasureTheory.Measure (Euc d) := HRS.Whole.withDensityReal rho with hμ
  set U : Euc d → ℝ := HRS.Whole.convMeasure g μ with hU
  obtain ⟨hprob, heq⟩ := hrho.2
  set Zt : ℝ := ∫ y, Real.exp (-beta * (V y + U y)) with hZt
  have hZt0 : 0 < Zt := by
    have hnn : 0 ≤ Zt := integral_nonneg fun y => (Real.exp_pos _).le
    rcases hnn.lt_or_eq with h | h
    · exact h
    · exfalso
      have : ∀ x, rho x = 0 := fun x => by rw [heq x]; simp [← hZt, ← h]
      have h1 := hprob.integral_one
      simp [this] at h1
  have heq' : ∀ x, rho x * Zt = Real.exp (-beta * (V x + U x)) := fun x => by
    rw [heq x]; field_simp
    first | done | rfl
  have hgm : Measurable g := by
    have e : g = fun x : Euc d => ‖x‖ ^ (-s) := by
      funext x; simp [hg, HRS.Whole.rieszKernel, hs0]
    rw [e]; exact measurable_norm.pow_const _
  have hVm : Measurable V := by
    have e : V = fun x : Euc d => a * ‖x‖ ^ 2 / 2 := by funext x; rfl
    rw [e]; fun_prop
  have hρm := hprob.measurable
  have hUm : Measurable U := by
    have : U = fun x => -(Real.log (Zt * rho x)) / beta - V x := by
      funext x
      have h1 : Zt * rho x = Real.exp (-beta * (V x + U x)) := by rw [mul_comm]; exact heq' x
      rw [h1, Real.log_exp]
      field_simp
      ring
    rw [this]
    exact ((Real.measurable_log.comp (measurable_const.mul hρm)).neg.div_const _).sub hVm
  have hev : ∀ x : Euc d, g (-x) = g x := fun x => by simp [hg, HRS.Whole.rieszKernel]
  set W : HRS.Whole.EucConfig d N → ℝ := fun X => beta * ∑ i, U (X i) -
    beta / (2 * N) * HRS.MS.Phase2S82.pairSum (fun x y => g (x - y)) X with hW
  have hWm : Measurable W := by
    have h1 : Measurable (fun X : HRS.Whole.EucConfig d N => ∑ i, U (X i)) :=
      Finset.measurable_sum _ fun i _ => hUm.comp (measurable_pi_apply i)
    have h2 : Measurable (fun X : HRS.Whole.EucConfig d N => HRS.MS.Phase2S82.pairSum (fun x y => g (x - y)) X) := by
      unfold HRS.MS.Phase2S82.pairSum
      refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
      exact hgm.comp ((measurable_pi_apply i).sub (measurable_pi_apply j))
    exact (measurable_const.mul h1).sub (measurable_const.mul h2)
  have hNr : (N : ℝ) ≠ 0 := by positivity
  have hpt : ∀ X : HRS.Whole.EucConfig d N, (∏ i, rho (X i)) * Real.exp (W X) =
      (Zt⁻¹) ^ N * Real.exp (-beta * HRS.Whole.canonicalHamiltonian g V X) := by
    intro X
    have hr : ∀ x, rho x = Real.exp (-beta * (V x + U x)) * Zt⁻¹ := fun x => by
      rw [← heq' x]; field_simp
    have e1 : ∏ i, rho (X i) = Real.exp (∑ i, (-beta * (V (X i) + U (X i)))) * (Zt⁻¹) ^ N := by
      simp only [hr, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin, Real.exp_sum]
    have hs1 : ∑ i, (-beta * (V (X i) + U (X i))) =
        -beta * ∑ i, V (X i) + -beta * ∑ i, U (X i) := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum]
    have hPS := r26t8a_r05_pairSum_two hev X
    have hexp : (∑ i, (-beta * (V (X i) + U (X i)))) + W X =
        -beta * HRS.Whole.canonicalHamiltonian g V X := by
      rw [hs1]
      simp only [hW, HRS.Whole.canonicalHamiltonian]
      rw [hPS]
      field_simp
      ring
    calc (∏ i, rho (X i)) * Real.exp (W X)
        = (Zt⁻¹) ^ N * Real.exp ((∑ i, (-beta * (V (X i) + U (X i)))) + W X) := by
          rw [e1, Real.exp_add]; ring
      _ = _ := by rw [hexp]
  set c : ℝ := (Zt⁻¹) ^ N with hc_def
  have hc : 0 < c := by positivity
  have hPm : Measurable (fun X : HRS.Whole.EucConfig d N => ∏ i, ENNReal.ofReal (rho (X i))) :=
    Finset.measurable_prod _ fun i _ => ENNReal.measurable_ofReal.comp (hρm.comp (measurable_pi_apply i))
  have hEm : Measurable (fun X : HRS.Whole.EucConfig d N => ENNReal.ofReal (Real.exp (W X))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hWm)
  have hHm : Measurable (fun X : HRS.Whole.EucConfig d N =>
      ENNReal.ofReal (Real.exp (-beta * HRS.Whole.canonicalHamiltonian g V X))) := by
    refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ?_)
    refine measurable_const.mul ?_
    unfold HRS.Whole.canonicalHamiltonian
    refine (Finset.measurable_sum _ fun i _ => hVm.comp (measurable_pi_apply i)).add
      (measurable_const.mul (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_))
    exact hgm.comp ((measurable_pi_apply i).sub (measurable_pi_apply j))
  have hpi := r26t8a_r05_pi_wd (d := d) (N := N) rho hprob
  have hdens : ((fun X : HRS.Whole.EucConfig d N => ∏ i, ENNReal.ofReal (rho (X i))) *
      (fun X => ENNReal.ofReal (Real.exp (W X)))) =
      fun X => ENNReal.ofReal c * ENNReal.ofReal (Real.exp (-beta * HRS.Whole.canonicalHamiltonian g V X)) := by
    funext X
    simp only [Pi.mul_apply]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => hprob.nonneg _),
      ← ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => hprob.nonneg _), hpt X,
      ENNReal.ofReal_mul hc.le]
  have hm1 : (Measure.pi (fun _ : Fin N => μ)).withDensity (fun X => ENNReal.ofReal (Real.exp (W X))) =
      ENNReal.ofReal c • (volume : Measure (HRS.Whole.EucConfig d N)).withDensity
        (fun X => ENNReal.ofReal (Real.exp (-beta * HRS.Whole.canonicalHamiltonian g V X))) := by
    rw [hpi, ← withDensity_mul _ hPm hEm, hdens, ← withDensity_smul _ hHm]
    rfl
  have hint : ∫ X, Real.exp (W X) ∂(Measure.pi (fun _ : Fin N => μ)) =
      c * HRS.Whole.canonicalPartition g V N beta := by
    rw [hpi]
    have e : (fun X : HRS.Whole.EucConfig d N => ∏ i, ENNReal.ofReal (rho (X i))) =
        fun X => ((∏ i, rho (X i)).toNNReal : ENNReal) := by
      funext X
      rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => hprob.nonneg _)]
      rfl
    rw [e, integral_withDensity_eq_integral_smul]
    · unfold HRS.Whole.canonicalPartition
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
      simp only [NNReal.smul_def, smul_eq_mul]
      rw [Real.coe_toNNReal _ (Finset.prod_nonneg fun i _ => hprob.nonneg _)]
      exact hpt X
    · exact (Finset.measurable_prod _ fun i _ => hρm.comp (measurable_pi_apply i)).real_toNNReal
  show _ = (ENNReal.ofReal (∫ X, Real.exp (W X) ∂(Measure.pi (fun _ : Fin N => μ))))⁻¹ •
    (Measure.pi (fun _ : Fin N => μ)).withDensity (fun X => ENNReal.ofReal (Real.exp (W X)))
  rw [hint, hm1, ENNReal.ofReal_mul hc.le, smul_smul]
  have hc0 : ENNReal.ofReal c ≠ 0 := by simpa using hc
  have hct : ENNReal.ofReal c ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [ENNReal.mul_inv (Or.inl hc0) (Or.inl hct), mul_comm (ENNReal.ofReal c)⁻¹, mul_assoc,
    ENNReal.inv_mul_cancel hc0 hct, mul_one]
  rfl

end HRS.MS.R26T8A
