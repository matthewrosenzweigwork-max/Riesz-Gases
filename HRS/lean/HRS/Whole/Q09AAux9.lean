import HRS.Whole.Q09AAux8
import HRS.Whole.Q09AAux2
open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate ContDiff

/-!
# Packet Q09-A, part 9: pieces of the cutoff estimate (Lemma S.A.19)

`hom_le` (`Ḣ^a ≤ H^m` on the Fourier side), `pair_far` (the far part is controlled by the second moment),
integrability facts for the empirical measure and `ρ dx`.
-/

noncomputable section

namespace HRS.Whole.Q09A
open HRS.Whole
open HRS.PDE.ToolboxRd

variable {d : ℕ}

theorem hom_le {u : Euc d → ℝ} {m : ℕ} {a : ℝ} (hu : HRS.PDE.ToolboxRd.MemSobolev (m : ℝ) u)
    (ha0 : 0 ≤ a) (ham : a ≤ m) :
    Integrable (fun ξ : Euc d => (2 * Real.pi * ‖ξ‖) ^ (2 * a) * ‖fourierL2 u ξ‖ ^ 2) volume ∧
      ∫ ξ, (2 * Real.pi * ‖ξ‖) ^ (2 * a) * ‖fourierL2 u ξ‖ ^ 2 ≤
        HRS.PDE.ToolboxRd.sobolevNormSq (m : ℝ) u := by
  have hF : AEStronglyMeasurable (fourierL2 u) volume :=
    HRS.PDE.ToolboxRd.FourierAux.aestronglyMeasurable_fourierL2 hu.1
  have hpt : ∀ ξ : Euc d, (2 * Real.pi * ‖ξ‖) ^ (2 * a) ≤ (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (m : ℝ) := by
    intro ξ
    have hw1 : 1 ≤ 1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 := by nlinarith [sq_nonneg Real.pi, sq_nonneg ‖ξ‖]
    have h0 : 0 ≤ 2 * Real.pi * ‖ξ‖ := by positivity
    calc (2 * Real.pi * ‖ξ‖) ^ (2 * a) = ((2 * Real.pi * ‖ξ‖) ^ (2 : ℝ)) ^ a := by
          rw [← Real.rpow_mul h0]
      _ ≤ (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ a := by
          apply Real.rpow_le_rpow (by positivity) _ ha0
          rw [Real.rpow_two]; nlinarith [sq_nonneg Real.pi, sq_nonneg ‖ξ‖]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hw1 ham
  have hmeas : AEStronglyMeasurable (fun ξ : Euc d => (2 * Real.pi * ‖ξ‖) ^ (2 * a) *
      ‖fourierL2 u ξ‖ ^ 2) volume := by
    have hc : Continuous fun ξ : Euc d => (2 * Real.pi * ‖ξ‖) ^ (2 * a) := by
      by_cases h : a = 0
      · simp [h]; exact continuous_const
      · exact (continuous_const.mul continuous_norm).rpow_const (fun _ => Or.inr (by
          have : 0 < a := lt_of_le_of_ne ha0 (Ne.symm h)
          linarith))
    exact hc.aestronglyMeasurable.mul (hF.norm.aemeasurable.pow_const 2).aestronglyMeasurable
  have hI : Integrable (fun ξ : Euc d => (2 * Real.pi * ‖ξ‖) ^ (2 * a) * ‖fourierL2 u ξ‖ ^ 2) volume := by
    refine hu.2.mono' hmeas (Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_right (hpt ξ) (sq_nonneg _)
  refine ⟨hI, ?_⟩
  unfold HRS.PDE.ToolboxRd.sobolevNormSq
  exact integral_mono hI hu.2 fun ξ => mul_le_mul_of_nonneg_right (hpt ξ) (sq_nonneg _)


theorem pair_far (μ : Measure (Euc d)) (h ψ : Euc d → ℝ) (b R : ℝ)
    (hfar : ∀ x, |h x - ψ x| ≤ b * ‖x‖ ^ 2 / R ^ 2)
    (ih : Integrable h μ) (iψ : Integrable ψ μ) (iq : Integrable (fun x : Euc d => ‖x‖ ^ 2) μ) :
    |pair μ h - pair μ ψ| ≤ b * pair μ (fun x => ‖x‖ ^ 2) / R ^ 2 := by
  unfold pair
  rw [← integral_sub ih iψ]
  calc |∫ x, (h x - ψ x) ∂μ| ≤ ∫ x, |h x - ψ x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, b * ‖x‖ ^ 2 / R ^ 2 ∂μ := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _) ?_
          (Eventually.of_forall hfar)
        simpa [mul_div_assoc] using (iq.const_mul b).div_const (R ^ 2)
    _ = _ := by
        rw [integral_div, integral_const_mul]

theorem integrable_sq_withDensityReal {ρ : Euc d → ℝ} (hρ : IsProbDensity ρ)
    (hmom : Integrable (fun x : Euc d => ‖x‖ ^ 2 * ρ x)) :
    Integrable (fun x : Euc d => ‖x‖ ^ 2) (withDensityReal ρ) := by
  unfold withDensityReal
  rw [integrable_withDensity_iff_integrable_smul' hρ.measurable.ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine hmom.congr (Eventually.of_forall fun x => ?_)
  simp [ENNReal.toReal_ofReal (hρ.nonneg x), mul_comm]


theorem integrable_empirical {N : ℕ} (hN : 0 < N) (X : EucConfig d N) (f : Euc d → ℝ) :
    Integrable f (empirical X) := by
  unfold empirical
  refine Integrable.smul_measure ?_ (by simpa using hN.ne')
  exact integrable_finsetSum_measure.mpr fun i _ => integrable_dirac (by simp)


theorem final_ineq (cc A K s0 n lam E0 P M R : ℝ) (hcc : 0 ≤ cc) (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hs0 : 0 ≤ s0) (hn : 0 ≤ n) (hlam : 0 ≤ lam) (hE0 : 0 ≤ E0) (hP : 1 ≤ P) (hM : 0 ≤ M) :
    cc * A * n * lam + cc * (K * s0) * P * n * E0 + n * M / R ^ 2 ≤
      (cc * A + cc * (K * s0) + 1) * n * (P * (lam + E0) + M / R ^ 2) := by
  obtain ⟨Pm, hPm0, hPm⟩ : ∃ Pm : ℝ, 0 ≤ Pm ∧ P = 1 + Pm := ⟨P - 1, by linarith, by ring⟩
  have hR2 : 0 ≤ M / R ^ 2 := by positivity
  have hK1 : 0 ≤ K * s0 := mul_nonneg hK hs0
  subst hPm
  have e : (cc * A + cc * (K * s0) + 1) * n * ((1 + Pm) * (lam + E0) + M / R ^ 2) -
      (cc * A * n * lam + cc * (K * s0) * (1 + Pm) * n * E0 + n * M / R ^ 2) =
      cc * A * n * lam * Pm + (cc * (K * s0) + 1) * n * (1 + Pm) * lam +
      (cc * A + 1) * n * (1 + Pm) * E0 + (cc * A + cc * (K * s0)) * n * (M / R ^ 2) := by
    ring
  have : 0 ≤ cc * A * n * lam * Pm + (cc * (K * s0) + 1) * n * (1 + Pm) * lam +
      (cc * A + 1) * n * (1 + Pm) * E0 + (cc * A + cc * (K * s0)) * n * (M / R ^ 2) := by
    positivity
  have h3 : n * M / R ^ 2 = n * (M / R ^ 2) := by ring
  nlinarith [this, e, h3]

end HRS.Whole.Q09A
