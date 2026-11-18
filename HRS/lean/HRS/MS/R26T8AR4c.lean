import HRS.MS.R26T8AR4b
import HRS.MS.R26T8AT5
import HRS.MS.R26T8AP16a

/-!
# S8.2 T8A R4c: the higher Newton terms are of class `Conormal 8 0 M (s-2)` (no logarithm)
`r26t8a_R4_Qj_class`: for `1 ≤ j < L`, `localNewton F_j` (`F_j = parametrixTerm j`) is `Conormal 8 0 (2L) (s-2) (C A)`: it is `Conormal 8 1 (2j) (σ_j - 2)`
with `σ_j = s - j/2 ≤ s - 1/2`, and one half power of the pole absorbs the logarithm (`r26t8a_conormal_lower`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad HRS.MS.S82N

variable {d : ℕ}

set_option maxHeartbeats 3200000 in
theorem r26t8a_R4_Qj_class (hd : 2 ≤ d) (a beta : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (chi : Euc d → ℝ)
    (hchi : NewtonCutoff chi) (j : ℕ) (hj1 : 1 ≤ j) (hjL : j < iterationCount d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ rho : Euc d → ℝ, IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ (f : Euc d → ℝ) (A : ℝ), 0 ≤ A → TestBound (testOrder d) A f →
      Conormal 8 0 (2 * (iterationCount d : ℝ)) (criticalS d - 2) (C * A)
        (localNewton (HRS.Whole.withDensityReal rho) (critCoeff d a beta rho).ν chi
          (r26t8a_parametrixTerm (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi f j)) := by
  choose Cn hCn0 hCn using r26t8a_T4_iter d hd a beta ha hbeta chi hchi
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hj0 : (1 : ℝ) ≤ j := by exact_mod_cast hj1
  have hjL' : (j : ℝ) ≤ iterationCount d := by exact_mod_cast hjL.le
  have hσd : criticalS d - (j : ℝ) / 2 < d := by unfold criticalS; linarith
  obtain ⟨CZ, hCZ0, hCZ⟩ := r26t8a_local_newton_bound_same d hd 8 0 a beta (2 * (j : ℝ)) (criticalS d - (j : ℝ) / 2)
    ha hbeta (by linarith) hσd chi hchi
  obtain ⟨c, hc1, hc⟩ := r26t8a_conormal_lower (d := d) 8 (0 + 1) (2 * (j : ℝ)) (criticalS d - (j : ℝ) / 2 - 2)
  refine ⟨c * (CZ * Cn j), mul_nonneg (by linarith) (mul_nonneg hCZ0 (hCn0 j)), fun rho hrho f A hA hf => ?_⟩
  obtain ⟨-, hTj⟩ := hCn j hjL.le rho hrho f A hA hf
  have hT8 : Conormal 8 0 (2 * (j : ℝ)) (criticalS d - (j : ℝ) / 2) (Cn j * A)
      (r26t8a_parametrixTerm (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi f j) :=
    r26t8a_conormal_mono (by omega) hTj
  obtain ⟨-, -, hQ⟩ := hCZ rho hrho _ (Cn j * A) (mul_nonneg (hCn0 j) hA) hT8
  rw [r26t8a_critCoeff_nu a beta rho]
  have hCnA : 0 ≤ CZ * (Cn j * A) := mul_nonneg hCZ0 (mul_nonneg (hCn0 j) hA)
  have hlow := hc (CZ * (Cn j * A)) hCnA hQ
  have hM : 2 * (j : ℝ) ≤ 2 * (iterationCount d : ℝ) := by linarith
  have h1 := r26t8a_f23_conormal_M_mono (M' := 2 * (iterationCount d : ℝ)) hM
    (mul_nonneg (by linarith) hCnA) hlow
  refine r26t8a_conormal_mono_sA (mul_nonneg (by linarith) hCnA) (le_of_eq (by ring)) ?_ h1
  have : (criticalS d - (j : ℝ) / 2 - 2) + 1 / 2 ≤ criticalS d - 2 := by linarith
  exact this

end HRS.MS.R26T8A
