import HRS.MS.Fp81S21WeightedGenNL4

/-! The energy and integrability consequences of identifying cutoff output jets. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.Ul HRS.MS.ProClosureS111

/-- Once the nonlocal output is smooth and its weighted jets are the pointwise
limits of compact-cutoff outputs, the compact bound passes to the finite-norm
input with the same trajectory-uniform constant. -/
theorem fp81s21_b3_all_test_of_output_jets (p : Parameters) (B c : ℝ)
    (hB : 0 ≤ B) (hc : 0 < c) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {δ : ℝ} (R : Trajectory p δ),
      fp81s21_b3_Data R B c → ∀ u, 0 ≤ u → ∀ f : Euc p.d → ℝ,
      IsR2WeightedTest (fp81s21_b3_q p + 2) (fp81s21_b3_P p) f →
      ∀ h : ℕ → Euc p.d → ℝ,
      (∀ n, IsR2WeightedTest (fp81s21_b3_q p + 2) (fp81s21_b3_P p) (h n) ∧
        HasCompactSupport (h n)) →
      Tendsto (fun n => weightedSobolevE (fp81s21_b3_q p + 2) (fp81s21_b3_P p) (h n))
        atTop (𝓝 (weightedSobolevE (fp81s21_b3_q p + 2) (fp81s21_b3_P p) f)) →
      ContDiff ℝ (fp81s21_b3_q p) (fp81s21_g4N p R u f) →
      (∀ x, Tendsto (fun n => weightedJets (fp81s21_b3_q p) (fp81s21_b3_P p)
        (fp81s21_g4N p R u (h n)) x) atTop
        (𝓝 (weightedJets (fp81s21_b3_q p) (fp81s21_b3_P p)
          (fp81s21_g4N p R u f) x))) →
      (∀ j : Fin p.d, ∀ x : Euc p.d,
        Integrable (fun y =>
          if ‖x - y‖ ≤ (1 / 4 : ℝ) then
            (fp81s21_b3_source R u f j y - fp81s21_b3_source R u f j x) •
              rieszKernelGrad p.d p.s (x - y)
          else fp81s21_b3_source R u f j y • rieszKernelGrad p.d p.s (x - y))) ∧
      IsR2WeightedTest (fp81s21_b3_q p) (fp81s21_b3_P p) (fp81s21_g4N p R u f) ∧
      weightedSobolevE (fp81s21_b3_q p) (fp81s21_b3_P p) (fp81s21_g4N p R u f) ≤
        ENNReal.ofReal A * weightedSobolevE (fp81s21_b3_q p + 2) (fp81s21_b3_P p) f := by
  obtain ⟨A, hA, hcompact⟩ := fp81s21_b3_nonlocal_compact p B c hB hc
  refine ⟨A, hA, ?_⟩
  intro δ R hdata u hu f hf h hreg henergy hcd hjets
  have hb : ∀ n, IsR2WeightedTest (fp81s21_b3_q p) (fp81s21_b3_P p)
      (fp81s21_g4N p R u (h n)) ∧
      weightedSobolevE (fp81s21_b3_q p) (fp81s21_b3_P p) (fp81s21_g4N p R u (h n)) ≤
        ENNReal.ofReal A * weightedSobolevE (fp81s21_b3_q p + 2) (fp81s21_b3_P p) (h n) :=
    fun n => hcompact R hdata u hu (h n) (hreg n).1.1 (hreg n).2
  have hbound := fp81s21_b3_weighted_energy_fatou_varying
    (fun n => fp81s21_g4N p R u (h n)) (fp81s21_g4N p R u f)
    (fun n => ENNReal.ofReal A * weightedSobolevE (fp81s21_b3_q p + 2) (fp81s21_b3_P p) (h n))
    (ENNReal.ofReal A * weightedSobolevE (fp81s21_b3_q p + 2) (fp81s21_b3_P p) f)
    (fun n => (hb n).1.1) hcd hjets (fun n => (hb n).2)
    (ENNReal.Tendsto.const_mul henergy (Or.inr ENNReal.ofReal_ne_top))
  exact ⟨fp81s21_b3_all_test_integrable p R u hu f hf,
    ⟨hcd, lt_of_le_of_lt hbound (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.2)⟩, hbound⟩

#print axioms HRS.Fp81.S21.fp81s21_b3_all_test_of_output_jets
end HRS.Fp81.S21
