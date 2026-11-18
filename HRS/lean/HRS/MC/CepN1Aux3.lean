import HRS.MC.CepN1Aux2

/-!
# Packet CEPN1, part 3: Gaussian lower bound and the one-piece estimate
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal Real

noncomputable section

namespace HRS.MC.CepN1

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- Lower bound for the Gaussian mass of a short interval. -/
theorem cepn1_gauss_lb (h : ℝ≥0) (hh : 0 < h) (a ε : ℝ) (hε : 0 < ε) :
    ENNReal.ofReal (2 * ε * ((√(2 * π * h))⁻¹ * Real.exp (-(|a| + ε) ^ 2 / (2 * h)))) ≤
      gaussianReal 0 h (Set.Ioo (a - ε) (a + ε)) := by
  rw [gaussianReal_apply 0 hh.ne' _]
  set c : ℝ := (√(2 * π * h))⁻¹ * Real.exp (-(|a| + ε) ^ 2 / (2 * h)) with hc
  have hmono : ∀ x ∈ Set.Ioo (a - ε) (a + ε), ENNReal.ofReal c ≤ gaussianPDF 0 h x := by
    intro x hx
    unfold gaussianPDF gaussianPDFReal
    apply ENNReal.ofReal_le_ofReal
    rw [hc]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
    have hx2 : x ^ 2 ≤ (|a| + ε) ^ 2 := by
      have : |x| ≤ |a| + ε := by
        rw [abs_le]
        constructor <;> cases abs_cases a <;> linarith [hx.1, hx.2]
      calc x ^ 2 = |x| ^ 2 := (sq_abs x).symm
        _ ≤ (|a| + ε) ^ 2 := by gcongr
    have hpos : (0 : ℝ) < 2 * h := by positivity
    rw [sub_zero]
    exact div_le_div_of_nonneg_right (neg_le_neg hx2) hpos.le
  calc ENNReal.ofReal (2 * ε * c) = ENNReal.ofReal c * ENNReal.ofReal (2 * ε) := by
        rw [mul_comm, ENNReal.ofReal_mul]
        have hcpos : 0 ≤ c := by positivity
        exact hcpos
    _ = ∫⁻ _ in Set.Ioo (a - ε) (a + ε), ENNReal.ofReal c := by
        rw [setLIntegral_const, Real.volume_Ioo]
        congr 2; ring
    _ ≤ _ := setLIntegral_mono' measurableSet_Ioo hmono


/-- One piece: the endpoint is within `ε` of `a` and the path stays within `ρ` on the dyadic grid. -/
theorem cepn1_piece [IsProbabilityMeasure P] {Z : ℝ≥0 → Ω → ℝ} (hZ : IsPreBrownianReal Z P)
    (h : ℝ≥0) (hh : 0 < h) (a : ℝ) {ε ρ : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) :
    ENNReal.ofReal (2 * ε * ((√(2 * π * h))⁻¹ * Real.exp (-(|a| + ε) ^ 2 / (2 * h))) - h / ρ ^ 2) ≤
      P {ω | |Z h ω - a| < ε ∧ ∀ n k : ℕ, k ≤ 2 ^ n → |Z (cepn1_dy h n k) ω| ≤ ρ} := by
  set q1 : ℝ := 2 * ε * ((√(2 * π * h))⁻¹ * Real.exp (-(|a| + ε) ^ 2 / (2 * h))) with hq1
  set B : Set Ω := {ω | |Z h ω - a| < ε} with hB
  set A : Set Ω := {ω | ∃ n k : ℕ, k ≤ 2 ^ n ∧ ρ < |Z (cepn1_dy h n k) ω|} with hA
  have hPB : ENNReal.ofReal q1 ≤ P B := by
    have e : B = Z h ⁻¹' Set.Ioo (a - ε) (a + ε) := by
      ext ω; simp only [hB, Set.mem_preimage, Set.mem_Ioo, abs_lt]
      constructor <;> intro hh <;> constructor <;> linarith [hh.1, hh.2]
    have hlaw := hZ.hasLaw_eval h
    have : P B = gaussianReal 0 h (Set.Ioo (a - ε) (a + ε)) := by
      rw [e, ← hlaw.map_eq, Measure.map_apply_of_aemeasurable hlaw.aemeasurable measurableSet_Ioo]
    rw [this]
    exact cepn1_gauss_lb h hh a ε hε
  have hPA : P A ≤ ENNReal.ofReal (h / ρ ^ 2) := by
    have := cepn1_max_dy hZ h hρ
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.2 (by positivity)).ne')
      (Or.inl ENNReal.ofReal_ne_top), mul_comm]
    exact this
  have hsub : B ⊆ {ω | |Z h ω - a| < ε ∧ ∀ n k : ℕ, k ≤ 2 ^ n → |Z (cepn1_dy h n k) ω| ≤ ρ} ∪ A := by
    intro ω hω
    by_cases hcase : ∀ n k : ℕ, k ≤ 2 ^ n → |Z (cepn1_dy h n k) ω| ≤ ρ
    · exact Or.inl ⟨hω, hcase⟩
    · right
      simp only [not_forall, not_le] at hcase
      obtain ⟨n, k, hk, hk2⟩ := hcase
      exact ⟨n, k, hk, hk2⟩
  have h1 : P B ≤ P {ω | |Z h ω - a| < ε ∧ ∀ n k : ℕ, k ≤ 2 ^ n → |Z (cepn1_dy h n k) ω| ≤ ρ} +
      ENNReal.ofReal (h / ρ ^ 2) :=
    (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add le_rfl hPA))
  have h2 : ENNReal.ofReal q1 ≤ P {ω | |Z h ω - a| < ε ∧ ∀ n k : ℕ, k ≤ 2 ^ n → |Z (cepn1_dy h n k) ω| ≤ ρ} +
      ENNReal.ofReal (h / ρ ^ 2) := hPB.trans h1
  have h3 := tsub_le_iff_right.2 h2
  refine le_trans ?_ h3
  exact (ENNReal.ofReal_sub q1 (by positivity : (0:ℝ) ≤ h / ρ ^ 2)).le

end HRS.MC.CepN1
