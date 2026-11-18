import HRS.MS.R26T8AT3
import HRS.MS.R26T8AP18

/-!
# S8.2 T8A T4a: the iteration data of P18 as a stand-alone statement (same proof as `iter` in `r26t8a_parametrix_telescope`)
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

set_option maxHeartbeats 6400000 in
theorem r26t8a_T4_iter (d : ℕ) (hd : 2 ≤ d) (a beta : ℝ)
    (ha : 0 < a) (hbeta : 0 < beta) (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) :
    ∀ n : ℕ, ∃ Cn : ℝ, 0 ≤ Cn ∧ (n ≤ iterationCount d → ∀ rho : Euc d → ℝ,
      IsThermalEquilibrium d (criticalS d) a beta rho → ∀ (f : Euc d → ℝ) (A : ℝ), 0 ≤ A →
      TestBound (testOrder d) A f →
      CanonicalPair (HRS.Whole.withDensityReal rho)
        (r26t8a_parametrixTerm (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi f n) ∧
      Conormal (2 * (iterationCount d - n) + 10) 0 (2 * (n : ℝ)) (criticalS d - (n : ℝ) / 2) (Cn * A)
        (r26t8a_parametrixTerm (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi f n)) := by
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hcrit_lt : criticalS d < d := by unfold criticalS; linarith
  have hcrit_nn : 0 ≤ criticalS d := by unfold criticalS; linarith
  obtain ⟨C17, hC170, hP17⟩ := r26t8a_source_conormal d hd a beta ha hbeta
  -- the iteration
  intro n
  induction n with
  | zero =>
    refine ⟨C17, hC170, fun _ rho hrho f A hA hf => ?_⟩
    obtain ⟨hcan, -, hcon⟩ := hP17 rho hrho f A hA hf
    have e : r26t8a_parametrixTerm (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi f 0 =
        HSource (HRS.Whole.withDensityReal rho) f := rfl
    rw [e]
    refine ⟨hcan, ?_⟩
    simpa using hcon
  | succ n ih =>
    obtain ⟨Cn, hCn0, hCn⟩ := ih
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    obtain ⟨CP, hCP0, hCP⟩ := r26t8a_defect_half_order_same d hd (2 * (iterationCount d - (n + 1)) + 10) a beta
      (2 * (n : ℝ)) (criticalS d - (n : ℝ) / 2) ha hbeta (by linarith) (by linarith) chi hchi
    refine ⟨CP * Cn, by positivity, fun hn rho hrho f A hA hf => ?_⟩
    obtain ⟨hcan, hcon⟩ := hCn (by omega) rho hrho f A hA hf
    have hcon' : Conormal (2 * (iterationCount d - (n + 1)) + 10 + 2) 0 (2 * (n : ℝ))
        (criticalS d - (n : ℝ) / 2) (Cn * A)
        (r26t8a_parametrixTerm (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi f n) := by
      have e : 2 * (iterationCount d - (n + 1)) + 10 + 2 = 2 * (iterationCount d - n) + 10 := by omega
      rw [e]; exact hcon
    obtain ⟨hcan', hcon''⟩ := hCP rho hrho _ (Cn * A) (mul_nonneg hCn0 hA) hcan hcon'
    have e1 : r26t8a_parametrixTerm (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi f (n + 1) =
        newtonDefect (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi
          (r26t8a_parametrixTerm (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) chi f n) :=
      Function.iterate_succ_apply' _ _ _
    rw [e1]
    refine ⟨hcan', ?_⟩
    have eM : 2 * (n : ℝ) + 2 = 2 * ((n + 1 : ℕ) : ℝ) := by push_cast; ring
    have eσ : criticalS d - (n : ℝ) / 2 - 1 / 2 = criticalS d - ((n + 1 : ℕ) : ℝ) / 2 := by push_cast; ring
    have eC : CP * (Cn * A) = (CP * Cn) * A := by ring
    rw [eM, eσ, eC] at hcon''
    exact hcon''

end HRS.MS.R26T8A
