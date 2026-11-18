import HRS.MS.MovEntAux11
import HRS.MS.MovEntAux8
import HRS.MS.SuppA0Aux2

/-!
# S6.6, packet P6 (part 6): hypotheses of `SuperDiss` for the quadratic confinement and the S6.3 class

* `s66_confinement_facts`: `V = q|x|²/2` is `C^∞`, has bounded Hessian and is coercive.
* `s66_int_K`: `K(t) = A e^{-ct}` is integrable on `[0,T]` with `∫_{[0,T]} K ≤ A/c`.
* `s66_regular_family`: weighted derivative bounds (the S6.4 Schwartz clause with `L = d+3`, `K = 3`) give `IsRegularDensityW 3 Λ` for `ρ_t`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovEnt

open HRS.Whole

variable {d : ℕ}

theorem s66_confinement_facts (q : ℝ) (hq : 0 < q) :
    ContDiff ℝ 3 (confinement q : Euc d → ℝ) ∧
      (∃ B : ℝ, ∀ x, ‖iteratedFDeriv ℝ 2 (confinement q : Euc d → ℝ) x‖ ≤ B) ∧
      (∃ cV CV : ℝ, 0 < cV ∧ ∀ x, cV * ‖x‖ ^ 2 - CV ≤ (confinement q : Euc d → ℝ) x) := by
  refine ⟨?_, ?_, ⟨q / 2, 0, by positivity, fun x => ?_⟩⟩
  · unfold confinement
    exact ((contDiff_const.mul (contDiff_norm_sq ℝ)).div_const 2)
  · obtain ⟨ΛV, -, h2, -⟩ := HRS.MS.A0.a0_vhyp (d := d) q
    exact ⟨ΛV, fun x => h2 2 le_rfl le_rfl x⟩
  · unfold confinement
    have : q / 2 * ‖x‖ ^ 2 - 0 = q * ‖x‖ ^ 2 / 2 := by ring
    linarith

theorem s66_int_K {A c : ℝ} (hA : 0 ≤ A) (hc : 0 < c) (T : ℝ) :
    IntegrableOn (fun t : ℝ => A * Real.exp (-c * t)) (Set.Icc 0 T) ∧
      ∫ t in Set.Icc 0 T, A * Real.exp (-c * t) ≤ A / c := by
  have hcont : Continuous (fun t : ℝ => A * Real.exp (-c * t)) := by fun_prop
  refine ⟨hcont.integrableOn_Icc, ?_⟩
  have hI : IntegrableOn (fun t : ℝ => A * Real.exp (-c * t)) (Set.Ioi 0) :=
    (integrableOn_exp_mul_Ioi (a := -c) (by linarith) 0).const_mul A
  rw [integral_Icc_eq_integral_Ioc]
  calc ∫ t in Set.Ioc 0 T, A * Real.exp (-c * t) ≤ ∫ t in Set.Ioi 0, A * Real.exp (-c * t) :=
        setIntegral_mono_set hI (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => by
          have : 0 < Real.exp (-c * t) := Real.exp_pos _
          positivity) (Eventually.of_forall Set.Ioc_subset_Ioi_self)
    _ = A / c := by
        rw [integral_const_mul, integral_exp_mul_Ioi (a := -c) (by linarith) 0]
        field_simp
        simp

end HRS.MS.MovEnt

end
