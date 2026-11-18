import HRS.MS.Fp81S21WeightedGenNL2
import HRS.MS.ProClosureS111WeightedCutoff

/-! The all-test nonlocal contract and its compact cutoff family. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.Ul HRS.MS.ProClosureS111

/-- Exact all-test contract, including genuine cancellation-integrand integrability. -/
def fp81s21_b3_nonlocal_all_tests_contract (p : Parameters) (B c : ℝ) : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∀ {δ : ℝ} (R : Trajectory p δ),
    fp81s21_b3_Data R B c → ∀ u, 0 ≤ u → ∀ f : Euc p.d → ℝ,
      IsR2WeightedTest (fp81s21_b3_q p + 2) (fp81s21_b3_P p) f →
      (∀ j : Fin p.d, ∀ x : Euc p.d,
        Integrable (fun y =>
          if ‖x - y‖ ≤ (1 / 4 : ℝ) then
            (fp81s21_b3_source R u f j y - fp81s21_b3_source R u f j x) •
              rieszKernelGrad p.d p.s (x - y)
          else fp81s21_b3_source R u f j y • rieszKernelGrad p.d p.s (x - y))) ∧
      IsR2WeightedTest (fp81s21_b3_q p) (fp81s21_b3_P p) (fp81s21_g4N p R u f) ∧
      weightedSobolevE (fp81s21_b3_q p) (fp81s21_b3_P p) (fp81s21_g4N p R u f) ≤
        ENNReal.ofReal A * weightedSobolevE (fp81s21_b3_q p + 2) (fp81s21_b3_P p) f

/-- Cutoffs of a finite weighted test agree locally with all its jets eventually,
while their weighted jet vectors admit a common integrable-square majorant. -/
theorem fp81s21_b3_all_test_cutoffs (p : Parameters) (f : Euc p.d → ℝ)
    (hf : IsR2WeightedTest (fp81s21_b3_q p + 2) (fp81s21_b3_P p) f) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ h : ℕ → Euc p.d → ℝ,
      (∀ n, ContDiff ℝ (fp81s21_b3_q p + 2) (h n) ∧ HasCompactSupport (h n)) ∧
      (∀ n x, ‖weightedJets (fp81s21_b3_q p + 2) (fp81s21_b3_P p) (h n) x‖ ≤
        K * ‖weightedJets (fp81s21_b3_q p + 2) (fp81s21_b3_P p) f x‖) ∧
      ∀ x, ∀ᶠ n in atTop, ∀ m : ℕ,
        iteratedFDeriv ℝ m (h n) x = iteratedFDeriv ℝ m f x := by
  obtain ⟨K, hK, h, hreg, hbound, hlocal⟩ :=
    weighted_cutoff_family (Pw := fp81s21_b3_P p) hf.1
  refine ⟨K, hK, h, hreg, hbound, ?_⟩
  intro x
  obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
  filter_upwards [eventually_ge_atTop N] with n hn
  have hn' : ‖x‖ < (n : ℝ) + 1 := by
    have hnn : (N : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  intro m
  exact (Filter.EventuallyEq.iteratedFDeriv ℝ (hlocal n x hn') m).self_of_nhds

#print axioms HRS.Fp81.S21.fp81s21_b3_nonlocal_all_tests_contract
#print axioms HRS.Fp81.S21.fp81s21_b3_all_test_cutoffs
end HRS.Fp81.S21
