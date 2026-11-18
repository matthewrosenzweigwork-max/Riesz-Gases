import HRS.Commutator.Whole.XLIAux19

/-!
# X-LI part 20: synthesis estimate (reverse square function inequality)
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff Convolution Topology SchwartzMap

noncomputable section

namespace HRS.Commutator.Whole.XLI

open HRS.Commutator.Whole

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- the `L^p(ℓ²)`-estimate `∫ sqS(K ⋆ F)^s ≲ ∫ |F|^{2s}` for bounded integrable `F` -/
def E1At (K : ℤ → 𝔼 → ℂ) (s : ℝ) : Prop :=
  ∃ C : ℝ≥0, ∀ F : 𝔼 → ℂ, Measurable F → Integrable F → ∀ B : ℝ≥0∞, B ≠ ⊤ →
    (∀ x, ‖F x‖ₑ ≤ B) → ∫⁻ x, sqS (fun j => cv (K j) F) x ^ s ≤ C * ∫⁻ x, ‖F x‖ₑ ^ (2 * s)

lemma sum_apply_schwartz (S : Finset ℤ) (U : ℤ → SchwartzMap 𝔼 ℂ) (x : 𝔼) :
    (∑ k ∈ S, U k) x = ∑ k ∈ S, U k x := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, SchwartzMap.add_apply, ih]

lemma schwartz_rpow_integrable (V : SchwartzMap 𝔼 ℂ) {a : ℝ} (ha : 0 < a) :
    Integrable (fun x => ‖V x‖ ^ a) := by
  set M : ℕ := ⌈((d : ℝ) + 1) / a⌉₊ with hM
  obtain ⟨C0, hC0, h0⟩ := V.decay 0 0
  obtain ⟨C1, hC1, h1⟩ := V.decay M 0
  set D : ℝ := 2 ^ M * (C0 + C1) with hD
  have hD0 : 0 ≤ D := by positivity
  have hb : ∀ x : 𝔼, ‖V x‖ * (1 + ‖x‖) ^ M ≤ D := by
    intro x
    have e0 := h0 x
    have e1 := h1 x
    simp only [norm_iteratedFDeriv_zero, pow_zero, one_mul] at e0 e1
    have hb : (1 + ‖x‖) ^ M ≤ 2 ^ M * (1 + ‖x‖ ^ M) := by
      rcases le_total ‖x‖ 1 with h | h
      · have : (1 + ‖x‖) ^ M ≤ 2 ^ M := pow_le_pow_left₀ (by positivity) (by linarith) _
        nlinarith [pow_nonneg (norm_nonneg x) M, pow_pos (by norm_num : (0:ℝ) < 2) M]
      · have : (1 + ‖x‖) ^ M ≤ (2 * ‖x‖) ^ M := pow_le_pow_left₀ (by positivity) (by linarith) _
        rw [mul_pow] at this
        nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) M]
    calc ‖V x‖ * (1 + ‖x‖) ^ M ≤ ‖V x‖ * (2 ^ M * (1 + ‖x‖ ^ M)) := by gcongr
      _ = 2 ^ M * (‖V x‖ + ‖x‖ ^ M * ‖V x‖) := by ring
      _ ≤ 2 ^ M * (C0 + C1) := by gcongr
  have hMa : ((d : ℝ)) < (M : ℝ) * a := by
    have h1 : ((d : ℝ) + 1) / a ≤ M := Nat.le_ceil _
    have := (div_le_iff₀ ha).1 h1
    linarith
  have hfr : (Module.finrank ℝ 𝔼 : ℝ) < (M : ℝ) * a := by
    simpa [finrank_euclideanSpace] using hMa
  have hint := integrable_one_add_norm (μ := (volume : Measure 𝔼)) hfr
  refine (hint.const_mul (D ^ a)).mono' ?_ (Eventually.of_forall fun x => ?_)
  · exact (V.continuous.norm.rpow_const (fun _ => Or.inr ha.le)).aestronglyMeasurable
  · have hpos : 0 < (1 + ‖x‖) ^ M := by positivity
    have h2 : ‖V x‖ ≤ D * ((1 + ‖x‖) ^ M)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hpos]; exact hb x
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    calc ‖V x‖ ^ a ≤ (D * ((1 + ‖x‖) ^ M)⁻¹) ^ a := Real.rpow_le_rpow (norm_nonneg _) h2 ha.le
      _ = D ^ a * (1 + ‖x‖) ^ (-((M : ℝ) * a)) := by
          rw [Real.mul_rpow hD0 (by positivity), Real.rpow_neg (by positivity),
            Real.inv_rpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]

end HRS.Commutator.Whole.XLI
