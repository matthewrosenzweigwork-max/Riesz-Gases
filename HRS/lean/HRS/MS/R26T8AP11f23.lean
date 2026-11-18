import HRS.MS.R26T8AP11f22
import HRS.MS.R26T8AP10a
import HRS.MS.R26T8AG1

/-!
# S8.2 T8A P11f (part 23): uniform Gaussian jet constants, monotonicity of `Conormal` in the weight exponent
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_f23_rho_unif {ρ : Euc d → ℝ}
    (hg : ∀ j : ℕ, ∃ C c : ℝ, 0 < c ∧ ∀ x : Euc d, ‖iteratedFDeriv ℝ j ρ x‖ ≤ C * Real.exp (-c * ‖x‖ ^ 2))
    (K : ℕ) : ∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ j ≤ K, ∀ x : Euc d,
      ‖iteratedFDeriv ℝ j ρ x‖ ≤ C * Real.exp (-c * ‖x‖ ^ 2) := by
  induction K with
  | zero =>
    obtain ⟨C, c, hc, h⟩ := hg 0
    refine ⟨|C|, c, abs_nonneg _, hc, fun j hj x => ?_⟩
    have : j = 0 := by omega
    subst this
    exact (h x).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le)
  | succ K ih =>
    obtain ⟨C, c, hC, hc, h⟩ := ih
    obtain ⟨C', c', hc', h'⟩ := hg (K + 1)
    refine ⟨C + |C'|, min c c', add_nonneg hC (abs_nonneg _), lt_min hc hc', fun j hj x => ?_⟩
    have e1 : Real.exp (-c * ‖x‖ ^ 2) ≤ Real.exp (-min c c' * ‖x‖ ^ 2) :=
      Real.exp_le_exp.2 (by nlinarith [min_le_left c c', sq_nonneg ‖x‖])
    have e2 : Real.exp (-c' * ‖x‖ ^ 2) ≤ Real.exp (-min c c' * ‖x‖ ^ 2) :=
      Real.exp_le_exp.2 (by nlinarith [min_le_right c c', sq_nonneg ‖x‖])
    by_cases hjK : j ≤ K
    · refine (h j hjK x).trans ?_
      nlinarith [mul_le_mul_of_nonneg_left e1 hC, Real.exp_pos (-min c c' * ‖x‖ ^ 2), abs_nonneg C',
        mul_nonneg (abs_nonneg C') (Real.exp_pos (-min c c' * ‖x‖ ^ 2)).le]
    · have : j = K + 1 := by omega
      subst this
      refine (h' x).trans ?_
      nlinarith [mul_le_mul (le_abs_self C') e2 (Real.exp_pos _).le (abs_nonneg _),
        mul_nonneg hC (Real.exp_pos (-min c c' * ‖x‖ ^ 2)).le, Real.exp_pos (-min c c' * ‖x‖ ^ 2)]

theorem r26t8a_f23_conormal_M_mono {k b : ℕ} {M M' σ A : ℝ} (hM : M ≤ M') (hA : 0 ≤ A) {F : Euc d → Euc d → ℝ}
    (hF : Conormal k b M σ A F) : Conormal k b M' σ A F := by
  refine ⟨hF.1, fun p q hpq X z hz => ?_⟩
  refine (hF.2 p q hpq X z hz).trans ?_
  have hpw : HRS.MS.Phase2S82.pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) ≤
      HRS.MS.Phase2S82.pairWeight M' (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) := by
    unfold HRS.MS.Phase2S82.pairWeight
    refine mul_le_mul (Real.rpow_le_rpow_of_exponent_le (s83_one_le_jb _) hM)
      (Real.rpow_le_rpow_of_exponent_le (s83_one_le_jb _) hM) (Real.rpow_nonneg (s83_jb_pos _).le _)
      (Real.rpow_nonneg (s83_jb_pos _).le _)
  have hE : 0 ≤ 1 + (min 1 ‖z‖) ^ (-(σ + (q : ℝ))) * (1 + |Real.log (min 1 ‖z‖)|) ^ b := by
    have : 0 ≤ (min 1 ‖z‖) ^ (-(σ + (q : ℝ))) := Real.rpow_nonneg (le_min zero_le_one (norm_nonneg _)) _
    positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpw hA) hE

end HRS.MS.R26T8A
