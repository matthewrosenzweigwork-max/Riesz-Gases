import HRS.MC.E213U10J

/-!
# Packet e213u10, part K: generic coupling lemmas

* `u10_cs`: Cauchy--Schwarz for nonnegative `L²` functions with prescribed second moments;
* `u10_exists_coupling`: an almost optimal coupling for `wassersteinE 2`;
* `u10_cost_memLp`: the cost of a coupling gives `L²` control of `‖x - y‖`;
* `u10_coupling_diff`: `|∫F dμ₁ - ∫G dμ₂| ≤ ∫ H dπ` along a coupling `π`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E213U10

theorem u10_cs {Z : Type*} [MeasurableSpace Z] (π : Measure Z) (f g : Z → ℝ) (hf0 : ∀ z, 0 ≤ f z)
    (hg0 : ∀ z, 0 ≤ g z) (hf : MemLp f 2 π) (hg : MemLp g 2 π) (s M : ℝ) (hs0 : 0 ≤ s) (hM0 : 0 ≤ M)
    (hs : ∫ z, f z ^ 2 ∂π ≤ s ^ 2) (hM : ∫ z, g z ^ 2 ∂π ≤ M ^ 2) :
    ∫ z, f z * g z ∂π ≤ s * M := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := π) (p := 2) (q := 2) Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall hf0) (Filter.Eventually.of_forall hg0) (by simpa using hf) (by simpa using hg)
  simp only [Real.rpow_two] at h
  calc ∫ z, f z * g z ∂π ≤ (∫ z, f z ^ 2 ∂π) ^ (1 / (2 : ℝ)) * (∫ z, g z ^ 2 ∂π) ^ (1 / (2 : ℝ)) := h
    _ ≤ (s ^ 2) ^ (1 / (2 : ℝ)) * (M ^ 2) ^ (1 / (2 : ℝ)) := by
        refine mul_le_mul (Real.rpow_le_rpow (integral_nonneg fun z => sq_nonneg _) hs (by norm_num))
          (Real.rpow_le_rpow (integral_nonneg fun z => sq_nonneg _) hM (by norm_num))
          (Real.rpow_nonneg (integral_nonneg fun z => sq_nonneg _) _) (Real.rpow_nonneg (sq_nonneg _) _)
    _ = s * M := by
        rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_sq hs0, Real.sqrt_sq hM0]

section Coupling

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B] [BorelSpace B]
  [SecondCountableTopology B]

theorem u10_exists_coupling (μ₁ μ₂ : Measure B) (c : ℝ≥0∞) (h : HRS.wassersteinE 2 μ₁ μ₂ < c) :
    ∃ π : Measure (B × B), HRS.IsCoupling π μ₁ μ₂ ∧
      (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ)) ∂π) ^ (1 / (2 : ℝ)) < c := by
  unfold HRS.wassersteinE at h
  obtain ⟨π, hπ⟩ := iInf_lt_iff.1 h
  exact ⟨π.1, π.2, hπ⟩

theorem u10_cost_memLp (π : Measure (B × B)) (s : ℝ) (hs : 0 ≤ s)
    (h : (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ)) ∂π) ^ (1 / (2 : ℝ)) ≤ ENNReal.ofReal s) :
    MemLp (fun z : B × B => ‖z.1 - z.2‖) 2 π ∧ ∫ z, ‖z.1 - z.2‖ ^ 2 ∂π ≤ s ^ 2 := by
  set I := ∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ)) ∂π with hI
  have hI2 : I ≤ ENNReal.ofReal (s ^ 2) := by
    have h1 : I = (I ^ (1 / (2 : ℝ))) ^ (2 : ℝ) := by
      rw [← ENNReal.rpow_mul]; norm_num
    calc I = (I ^ (1 / (2 : ℝ))) ^ (2 : ℝ) := h1
      _ ≤ (ENNReal.ofReal s) ^ (2 : ℝ) := ENNReal.rpow_le_rpow h (by norm_num)
      _ = ENNReal.ofReal (s ^ 2) := by
          rw [ENNReal.ofReal_rpow_of_nonneg hs (by norm_num), Real.rpow_two]
  have hmeas : Measurable fun z : B × B => ‖z.1 - z.2‖ := (measurable_fst.sub measurable_snd).norm
  have hsq : ∀ z : B × B, ‖z.1 - z.2‖ ^ (2 : ℝ) = ‖z.1 - z.2‖ ^ 2 := fun z => Real.rpow_two _
  have hnn : 0 ≤ᵐ[π] fun z : B × B => ‖z.1 - z.2‖ ^ 2 := Filter.Eventually.of_forall fun z => sq_nonneg _
  have hmeas2 : Measurable fun z : B × B => ‖z.1 - z.2‖ ^ 2 := hmeas.pow_const 2
  have hI' : ∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ 2) ∂π ≤ ENNReal.ofReal (s ^ 2) := by
    simp only [hsq] at hI
    rw [← hI]
    exact hI2
  have hint : Integrable (fun z : B × B => ‖z.1 - z.2‖ ^ 2) π := by
    refine ⟨hmeas2.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hnn]
    exact lt_of_le_of_lt hI' ENNReal.ofReal_lt_top
  refine ⟨(memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).2 hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hmeas2.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (sq_nonneg _) hI'

theorem u10_coupling_diff (π : Measure (B × B)) (F G : B → ℝ) (hF : Measurable F) (hG : Measurable G)
    (H : B × B → ℝ) (hFi : Integrable (fun z : B × B => F z.1) π) (hGi : Integrable (fun z : B × B => G z.2) π)
    (hH : Integrable H π) (hle : ∀ z : B × B, |F z.1 - G z.2| ≤ H z) :
    |∫ x, F x ∂(π.map Prod.fst) - ∫ y, G y ∂(π.map Prod.snd)| ≤ ∫ z, H z ∂π := by
  rw [integral_map measurable_fst.aemeasurable hF.aestronglyMeasurable,
    integral_map measurable_snd.aemeasurable hG.aestronglyMeasurable, ← integral_sub hFi hGi,
    ← Real.norm_eq_abs]
  exact norm_integral_le_of_norm_le hH (Filter.Eventually.of_forall fun z => by
    simpa [Real.norm_eq_abs] using hle z)

end Coupling

end HRS.MC.E213U10

end
