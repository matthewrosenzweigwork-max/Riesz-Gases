import HRS.MH.ScreenedS4Aux3

/-!
# Packet S4, part 4: `L²` bounds for `m v̂` and `m φ̂`
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate FourierTransform ContDiff

namespace HRS.MH.Screened

open HRS HRS.Whole HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

/-- `m v̂ ∈ L²` with `‖m v̂‖₂ ≤ C ‖v‖_{H^σ}`. -/
lemma s4_M2 {c : ℝ} (hc : 0 < c) {s : ℝ} (hσ : 0 ≤ s + 1 - d) (i : Fin d) {v : Euc d → ℝ}
    (hMS : HRS.PDE.ToolboxRd.MemSobolev (s + 1 - d) v) :
    MemLp (fun ξ => s4m c s i ξ * fourierL2 v ξ) 2 volume ∧
    eLpNorm (fun ξ => s4m c s i ξ * fourierL2 v ξ) 2 volume ≤
      ENNReal.ofReal (Real.sqrt ((2 * Real.pi * c) ^ 2 * (4 * Real.pi ^ 2) ^ (-(s + 1 - d)))) *
        ENNReal.ofReal (Real.sqrt (sobolevNormSq (s + 1 - d) v)) := by
  obtain ⟨hv2, hint⟩ := hMS
  set K2 := (2 * Real.pi * c) ^ 2 * (4 * Real.pi ^ 2) ^ (-(s + 1 - d)) with hK2
  have hK2pos : 0 ≤ K2 := by positivity
  have hmeas : AEStronglyMeasurable (fun ξ => s4m c s i ξ * fourierL2 v ξ) volume :=
    (measurable_s4m c s i).aestronglyMeasurable.mul (aestronglyMeasurable_fourierL2 hv2)
  have hpt : ∀ ξ, ‖s4m c s i ξ * fourierL2 v ξ‖ ^ 2 ≤
      K2 * ((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (s + 1 - d) * ‖fourierL2 v ξ‖ ^ 2) := by
    intro ξ
    rw [norm_mul, mul_pow]
    calc ‖s4m c s i ξ‖ ^ 2 * ‖fourierL2 v ξ‖ ^ 2
        ≤ (K2 * (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (s + 1 - d)) * ‖fourierL2 v ξ‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (norm_s4m_sq_le hc hσ i ξ) (sq_nonneg _)
      _ = _ := by ring
  have hint2 : Integrable (fun ξ => ‖s4m c s i ξ * fourierL2 v ξ‖ ^ 2) volume := by
    refine (hint.const_mul K2).mono' (hmeas.norm.aemeasurable.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hpt ξ
  have hmem : MemLp (fun ξ => s4m c s i ξ * fourierL2 v ξ) 2 volume :=
    (memLp_two_iff_integrable_sq_norm hmeas).2 hint2
  refine ⟨hmem, ?_⟩
  rw [hmem.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  have hle : ∫ ξ, ‖s4m c s i ξ * fourierL2 v ξ‖ ^ 2 ≤ K2 * sobolevNormSq (s + 1 - d) v := by
    unfold sobolevNormSq
    rw [← integral_const_mul]
    exact integral_mono hint2 (hint.const_mul K2) hpt
  rw [show ((2 : ℝ)⁻¹) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow, ← Real.sqrt_mul hK2pos]
  exact Real.sqrt_le_sqrt hle

/-- `m φ̂ ∈ L²` for a Schwartz `φ` (given that it is integrable). -/
lemma s4_Mphi_memLp {c : ℝ} (hc : 0 < c) {s : ℝ} (hσ0 : 0 ≤ s + 1 - d) (hσ1 : s + 1 - d ≤ 1)
    (i : Fin d) (φ : SchwartzMap (Euc d) ℝ)
    (h1 : Integrable (fun ξ : Euc d => s4m c s i ξ * 𝓕 (fun x : Euc d => ((φ x : ℝ) : ℂ)) ξ)) :
    MemLp (fun ξ : Euc d => s4m c s i ξ * 𝓕 (fun x : Euc d => ((φ x : ℝ) : ℂ)) ξ) 2 volume := by
  set u : SchwartzMap (Euc d) ℂ := φ.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM with hu
  have hF : ⇑(𝓕 u : SchwartzMap (Euc d) ℂ) = 𝓕 (fun x : Euc d => ((φ x : ℝ) : ℂ)) :=
    SchwartzMap.fourier_coe u
  set F : SchwartzMap (Euc d) ℂ := 𝓕 u with hFdef
  set B : ℝ := SchwartzMap.seminorm ℝ 0 0 F + SchwartzMap.seminorm ℝ 1 0 F with hB
  have hb : ∀ ξ : Euc d, ‖ξ‖ ^ (s + 1 - d) * ‖F ξ‖ ≤ B := by
    intro ξ
    have h0 := SchwartzMap.norm_le_seminorm ℝ F ξ
    have h1' := SchwartzMap.le_seminorm ℝ 1 0 F ξ
    rw [norm_iteratedFDeriv_zero] at h1'
    have h2 : ‖ξ‖ ^ (s + 1 - d) ≤ 1 + ‖ξ‖ := by
      rcases le_or_gt ‖ξ‖ 1 with h | h
      · have := Real.rpow_le_one (norm_nonneg ξ) h hσ0
        linarith [norm_nonneg ξ]
      · have := Real.rpow_le_rpow_of_exponent_le h.le hσ1
        rw [Real.rpow_one] at this
        linarith
    calc ‖ξ‖ ^ (s + 1 - d) * ‖F ξ‖ ≤ (1 + ‖ξ‖) * ‖F ξ‖ :=
          mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ = ‖F ξ‖ + ‖ξ‖ ^ 1 * ‖F ξ‖ := by rw [pow_one]; ring
      _ ≤ B := by rw [hB]; linarith
  have hmeas : AEStronglyMeasurable
      (fun ξ : Euc d => s4m c s i ξ * 𝓕 (fun x : Euc d => ((φ x : ℝ) : ℂ)) ξ) volume := by
    rw [← hF]
    exact (measurable_s4m c s i).aestronglyMeasurable.mul F.continuous.aestronglyMeasurable
  have hbd : ∀ ξ : Euc d, ‖s4m c s i ξ * 𝓕 (fun x : Euc d => ((φ x : ℝ) : ℂ)) ξ‖ ≤
      2 * Real.pi * c * B := by
    intro ξ
    rw [← hF, norm_mul]
    calc ‖s4m c s i ξ‖ * ‖F ξ‖ ≤ (2 * Real.pi * c * ‖ξ‖ ^ (s + 1 - d)) * ‖F ξ‖ :=
          mul_le_mul_of_nonneg_right (norm_s4m_le hc s i ξ) (norm_nonneg _)
      _ = 2 * Real.pi * c * (‖ξ‖ ^ (s + 1 - d) * ‖F ξ‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hb ξ) (by positivity)
  refine (memLp_two_iff_integrable_sq_norm hmeas).2 ?_
  refine (h1.norm.const_mul (2 * Real.pi * c * B)).mono'
    (hmeas.norm.aemeasurable.pow_const 2).aestronglyMeasurable (Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _), sq]
  exact mul_le_mul_of_nonneg_right (hbd ξ) (norm_nonneg _) |>.trans_eq (by ring)

end HRS.MH.Screened
