import HRS.MS.SuppU1Aux6

/-!
# U1 aux 7: cut-off and mollification converge in `L^r(μ' ⊗ μ')`.
-/

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal ContDiff Convolution

namespace HRS.Whole.U1

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

lemma u1_ae_offdiag (hd : 1 ≤ Module.finrank ℝ E) : ∀ᵐ q ∂(μ.prod μ), q.1 ≠ q.2 := by
  have := u1_diag_null μ hd 0
  rw [ae_iff]
  have h : {q : E × E | ¬ q.1 ≠ q.2} = {t | t.1 - t.2 = 0} := by ext q; simp [sub_eq_zero]
  rw [h]; exact this

lemma u1_bd_int {s r M : ℝ} (hs : 0 ≤ s) (hr : 0 < r) (hrs : r * s < (Module.finrank ℝ E : ℝ))
    (μ' : Measure E) [IsProbabilityMeasure μ'] (hle : μ' ≤ ENNReal.ofReal M • μ) {c : ℝ} (hc : 0 ≤ c) :
    ∫⁻ p : E × E, ENNReal.ofReal ((c * u1Vs s ‖p.1 - p.2‖) ^ r) ∂(μ'.prod μ') ≠ ⊤ := by
  have h1 := u1_lintegral_prod_Vs μ hs hr hrs μ' hle
  have h2 : ∀ p : E × E, ENNReal.ofReal ((c * u1Vs s ‖p.1 - p.2‖) ^ r)
      = ENNReal.ofReal (c ^ r) * ENNReal.ofReal (u1Vs s ‖p.1 - p.2‖ ^ r) := by
    intro p
    rw [Real.mul_rpow hc (by linarith [u1Vs_ge_one (s := s) (norm_nonneg (p.1 - p.2))]),
      ENNReal.ofReal_mul (Real.rpow_nonneg hc r)]
  simp_rw [h2]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top h1

/-- cut-off of a kernel to `closedBall R × closedBall R`. -/
def u1Cut (R : ℕ) (h : E → E → ℝ) : E × E → ℝ :=
  (closedBall (0:E) R ×ˢ closedBall (0:E) R).indicator (fun p => h p.1 p.2)

lemma u1_cut_tendsto {s r M B : ℝ} (hs : 0 ≤ s) (hr : 0 < r)
    (hrs : r * s < (Module.finrank ℝ E : ℝ)) (hB : 0 ≤ B)
    (μ' : Measure E) [IsProbabilityMeasure μ'] (hle : μ' ≤ ENNReal.ofReal M • μ)
    (h : E → E → ℝ) (hm : Measurable fun p : E × E => h p.1 p.2)
    (hbd : ∀ x y, x ≠ y → |h x y| ≤ B * u1Vs s ‖x - y‖) :
    Tendsto (fun n : ℕ => eLpNorm (fun p : E × E => u1Cut n h p - h p.1 p.2)
      (ENNReal.ofReal r) (μ'.prod μ')) atTop (𝓝 0) := by
  have hd0 : (0:ℝ) < Module.finrank ℝ E := lt_of_le_of_lt (by positivity) hrs
  have hd : 1 ≤ Module.finrank ℝ E := by exact_mod_cast hd0
  have hμ'μ : μ' ≪ μ := Measure.absolutelyContinuous_of_le_smul hle
  have hPν : μ'.prod μ' ≪ μ.prod μ := Measure.AbsolutelyContinuous.prod hμ'μ hμ'μ
  have hoff : ∀ᵐ q ∂(μ'.prod μ'), q.1 ≠ q.2 := hPν.ae_le (u1_ae_offdiag μ hd)
  refine u1_tendsto_eLpNorm_of_dom (μ'.prod μ') hr (fun n p => u1Cut n h p)
    (fun p => h p.1 p.2) (fun p => B * u1Vs s ‖p.1 - p.2‖)
    (fun n => (hm.indicator (measurableSet_closedBall.prod measurableSet_closedBall)).aemeasurable)
    hm.aemeasurable ?_ (u1_bd_int μ hs hr hrs μ' hle hB) ?_
  · intro n
    filter_upwards [hoff] with q hq
    have hV := u1Vs_ge_one (s := s) (norm_nonneg (q.1 - q.2))
    by_cases hqS : q ∈ closedBall (0:E) n ×ˢ closedBall (0:E) n
    · simp only [u1Cut, indicator_of_mem hqS, sub_self, abs_zero]
      exact mul_nonneg hB (by linarith)
    · simp only [u1Cut, indicator_of_notMem hqS, zero_sub, abs_neg]
      exact hbd q.1 q.2 hq
  · refine ae_of_all _ fun q => ?_
    obtain ⟨N, hN⟩ := exists_nat_ge (max ‖q.1‖ ‖q.2‖)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hqS : q ∈ closedBall (0:E) n ×ˢ closedBall (0:E) n := by
      refine ⟨?_, ?_⟩ <;> simp only [mem_closedBall, dist_zero_right]
      · exact le_trans (le_max_left _ _) (hN.trans hn')
      · exact le_trans (le_max_right _ _) (hN.trans hn')
    simp only [u1Cut, indicator_of_mem hqS]

end HRS.Whole.U1
