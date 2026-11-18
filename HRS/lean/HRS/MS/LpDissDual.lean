import HRS.MS.LpDissDefs
import HRS.MS.CzPvAux2

/-!
# S.A.16.C3: finite-cutoff duality with absolute integrability

`sa16bd_lapCut_duality`: for a bounded `C_b²` coefficient `μ` and a continuous, bounded, integrable
`f`, the positive-radius truncated fractional differences are dual:
`∫ μ * lapCut f = ∫ f * lapCut μ`, with both integrands integrable.  Proof: absolute Fubini on
`ℝ^d × ℝ^d` together with the measure preserving map `(x, z) ↦ (x - z, -z)`.
-/

set_option autoImplicit false

noncomputable section
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff
open HRS HRS.Whole HRS.Whole.AppendixA HRS.CZ.Pv

universe u

namespace HRS.Whole.AppendixA.BreakdownSA16

/-- the (even) cutoff kernel `1_{ε<|z|} |z|^{-(d+θ)}` -/
def sa16bd_K (d : ℕ) (θ ε : ℝ) : Euc d → ℝ :=
  Set.indicator {z : Euc d | ε < ‖z‖} (fun z => ‖z‖ ^ (-((d : ℝ) + θ)))

lemma sa16bd_K_measurable (d : ℕ) (θ ε : ℝ) : Measurable (sa16bd_K d θ ε) :=
  (measurable_norm.pow_const _).indicator (measurableSet_lt measurable_const measurable_norm)

lemma sa16bd_K_integrable {d : ℕ} (hd : 1 ≤ d) (θ : ℝ) (hθ0 : 0 < θ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (sa16bd_K d θ ε) := by
  unfold sa16bd_K
  rw [integrable_indicator_iff (measurableSet_lt measurable_const measurable_norm)]
  exact pvapi_integrableOn_rpow_outside hd (s := (d : ℝ) + θ) (by linarith) hε

lemma sa16bd_K_neg (d : ℕ) (θ ε : ℝ) (z : Euc d) : sa16bd_K d θ ε (-z) = sa16bd_K d θ ε z := by
  simp [sa16bd_K, Set.indicator, norm_neg]

lemma sa16bd_lapCut_eq (d : ℕ) (θ ε : ℝ) (f : Euc d → ℝ) (x : Euc d) :
    sa16bd_lapCut d θ ε f x = ∫ z, (f x - f (x - z)) * sa16bd_K d θ ε z := by
  have hS : MeasurableSet {z : Euc d | ε < ‖z‖} := measurableSet_lt measurable_const measurable_norm
  unfold sa16bd_lapCut sa16bd_K
  rw [← integral_indicator hS]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ {z : Euc d | ε < ‖z‖}
  · simp only [Set.indicator_of_mem hz]
    rw [Real.rpow_neg (norm_nonneg _), div_eq_mul_inv]
  · simp [Set.indicator_of_notMem hz]

theorem sa16bd_lapCut_duality {d : ℕ} (hd : 1 ≤ d) (θ ε : ℝ)
    (hθ0 : 0 < θ) (hε : 0 < ε) (μ f : Euc d → ℝ)
    (hμ : MemCb 2 μ) (hfcont : Continuous f)
    (hfbd : ∃ B : ℝ, ∀ x, |f x| ≤ B) (hfi : Integrable f) :
    Integrable (fun x : Euc d => μ x * sa16bd_lapCut d θ ε f x) ∧
      Integrable (fun x : Euc d => f x * sa16bd_lapCut d θ ε μ x) ∧
      (∫ x : Euc d, μ x * sa16bd_lapCut d θ ε f x) =
        ∫ x : Euc d, f x * sa16bd_lapCut d θ ε μ x := by
  have hμc : Continuous μ := by
    have : ContDiff ℝ 2 μ := by simpa using hμ.1
    exact this.continuous
  obtain ⟨Bμ, hBμ⟩ : ∃ B : ℝ, ∀ x, |μ x| ≤ B := by
    obtain ⟨B, hB⟩ := hμ.2 0 (by norm_num)
    exact ⟨B, fun x => by simpa [Real.norm_eq_abs] using hB ⟨x, rfl⟩⟩
  obtain ⟨Bf, hBf⟩ := hfbd
  set K := sa16bd_K d θ ε with hKdef
  have hKi : Integrable K := sa16bd_K_integrable hd θ hθ0 hε
  have hKm : Measurable K := sa16bd_K_measurable d θ ε
  have hKneg : ∀ z, K (-z) = K z := sa16bd_K_neg d θ ε
  -- integrability on the product
  have hμf : Integrable (fun x => μ x * f x) :=
    hfi.bdd_mul hμc.aestronglyMeasurable (Eventually.of_forall fun x => by simpa using hBμ x)
  have hfμ : Integrable (fun x => f x * μ x) := by
    refine hμf.congr (Eventually.of_forall fun x => ?_)
    simp only [mul_comm]
  have hA : Integrable (fun p : Euc d × Euc d => (μ p.1 * f p.1) * K p.2) (volume.prod volume) :=
    hμf.mul_prod hKi
  have hconv : Integrable (fun p : Euc d × Euc d => K p.2 * f (p.1 - p.2)) (volume.prod volume) := by
    have := Integrable.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hKi hfi
      (μ := (volume : Measure (Euc d))) (ν := (volume : Measure (Euc d)))
    simpa using this
  have hB : Integrable (fun p : Euc d × Euc d => μ p.1 * (K p.2 * f (p.1 - p.2)))
      (volume.prod volume) :=
    hconv.bdd_mul (hμc.comp continuous_fst).aestronglyMeasurable
      (Eventually.of_forall fun p => by simpa using hBμ p.1)
  have hT : MeasurePreserving (fun p : Euc d × Euc d => (p.1 - p.2, -p.2))
      (volume.prod volume) (volume.prod volume) :=
    (MeasurePreserving.prod (MeasurePreserving.id volume)
      (Measure.measurePreserving_neg (volume : Measure (Euc d)))).comp
      (measurePreserving_sub_prod volume volume)
  have hBT : Integrable (fun p : Euc d × Euc d => f p.1 * (μ (p.1 - p.2) * K p.2))
      (volume.prod volume) := by
    have := hT.integrable_comp_of_integrable hB
    refine this.congr (Eventually.of_forall fun p => ?_)
    simp only [Function.comp, hKneg, sub_neg_eq_add, sub_add_cancel]
    ring
  have hintBT : ∫ p : Euc d × Euc d, f p.1 * (μ (p.1 - p.2) * K p.2) ∂(volume.prod volume) =
      ∫ p : Euc d × Euc d, μ p.1 * (K p.2 * f (p.1 - p.2)) ∂(volume.prod volume) := by
    have h1 : ∫ p : Euc d × Euc d, μ p.1 * (K p.2 * f (p.1 - p.2)) ∂(volume.prod volume) =
        ∫ p : Euc d × Euc d, (fun q : Euc d × Euc d => μ q.1 * (K q.2 * f (q.1 - q.2)))
          ((p.1 - p.2, -p.2)) ∂(volume.prod volume) := by
      have := integral_map (μ := volume.prod volume) hT.measurable.aemeasurable
        (f := fun q : Euc d × Euc d => μ q.1 * (K q.2 * f (q.1 - q.2)))
        (by rw [hT.map_eq]; exact hB.aestronglyMeasurable)
      rw [hT.map_eq] at this
      exact this
    rw [h1]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only [hKneg, sub_neg_eq_add, sub_add_cancel]
    ring
  -- the two joint integrands
  have hΦ : Integrable (fun p : Euc d × Euc d => μ p.1 * ((f p.1 - f (p.1 - p.2)) * K p.2))
      (volume.prod volume) := by
    refine (hA.sub hB).congr (Eventually.of_forall fun p => ?_)
    simp only [Pi.sub_apply]
    ring
  have hΨ : Integrable (fun p : Euc d × Euc d => f p.1 * ((μ p.1 - μ (p.1 - p.2)) * K p.2))
      (volume.prod volume) := by
    refine (hA.sub hBT).congr (Eventually.of_forall fun p => ?_)
    simp only [Pi.sub_apply]
    ring
  have hΦeq : ∀ x, ∫ z, μ x * ((f x - f (x - z)) * K z) = μ x * sa16bd_lapCut d θ ε f x := by
    intro x
    rw [integral_const_mul, sa16bd_lapCut_eq]
  have hΨeq : ∀ x, ∫ z, f x * ((μ x - μ (x - z)) * K z) = f x * sa16bd_lapCut d θ ε μ x := by
    intro x
    rw [integral_const_mul, sa16bd_lapCut_eq]
  refine ⟨?_, ?_, ?_⟩
  · have := hΦ.integral_prod_left
    simpa only [hΦeq] using this
  · have := hΨ.integral_prod_left
    simpa only [hΨeq] using this
  · have e1 : ∫ x, μ x * sa16bd_lapCut d θ ε f x =
        ∫ p : Euc d × Euc d, μ p.1 * ((f p.1 - f (p.1 - p.2)) * K p.2) ∂(volume.prod volume) := by
      rw [integral_prod _ hΦ]
      simp only [hΦeq]
    have e2 : ∫ x, f x * sa16bd_lapCut d θ ε μ x =
        ∫ p : Euc d × Euc d, f p.1 * ((μ p.1 - μ (p.1 - p.2)) * K p.2) ∂(volume.prod volume) := by
      rw [integral_prod _ hΨ]
      simp only [hΨeq]
    rw [e1, e2]
    have f1 : ∫ p : Euc d × Euc d, μ p.1 * ((f p.1 - f (p.1 - p.2)) * K p.2) ∂(volume.prod volume) =
        ∫ p : Euc d × Euc d, (μ p.1 * f p.1) * K p.2 ∂(volume.prod volume) -
          ∫ p : Euc d × Euc d, μ p.1 * (K p.2 * f (p.1 - p.2)) ∂(volume.prod volume) := by
      rw [← integral_sub hA hB]
      refine integral_congr_ae (Eventually.of_forall fun p => ?_)
      ring
    have f2 : ∫ p : Euc d × Euc d, f p.1 * ((μ p.1 - μ (p.1 - p.2)) * K p.2) ∂(volume.prod volume) =
        ∫ p : Euc d × Euc d, (μ p.1 * f p.1) * K p.2 ∂(volume.prod volume) -
          ∫ p : Euc d × Euc d, f p.1 * (μ (p.1 - p.2) * K p.2) ∂(volume.prod volume) := by
      rw [← integral_sub hA hBT]
      refine integral_congr_ae (Eventually.of_forall fun p => ?_)
      ring
    rw [f1, f2, hintBT]

end HRS.Whole.AppendixA.BreakdownSA16
