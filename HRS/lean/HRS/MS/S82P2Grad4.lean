import HRS.MS.S82P2Grad3
import HRS.MS.S82P2Grad2
import HRS.MS.S82P2Pair5

/-!
# S8.2 (S82P2): second moment of the site gradients of the pair statistic (UNCOMPILED DRAFT)
Conditional on the centering `∫ ∇_x Q(x,z) dmu(z) = 0` for mu-a.e. `x` (hypothesis `hcenter`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82P2
open HRS HRS.Whole HRS.MS.Phase2S82

lemma s82p2_enorm_sq_vec {d : ℕ} (v : Euc d) : ‖v‖ₑ ^ 2 = ENNReal.ofReal (‖v‖ ^ 2) := by
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]

/-- row facts for the measurable gradient model. -/
lemma s82p2_gt_row {d : ℕ} (hd : 2 ≤ d) (M : ℝ) (hM : 0 ≤ M) (G c : ℝ) (hG : 0 < G) (hc : 0 < c)
    (rho : Euc d → ℝ) (hρ : HRS.Whole.IsProbDensity rho)
    (hρG : HRS.Whole.HasR2GaussianUpper G c rho) :
    ∃ K0 : ℝ, 0 ≤ K0 ∧ ∀ (a beta A : ℝ), 0 ≤ A → ∀ (f : Euc d → ℝ) (Q : Euc d → Euc d → ℝ),
      PairCorrector a beta rho M A f Q → ∀ x : Euc d,
      Integrable (fun z => ‖s82p2_gt Q x z‖ ^ 2) (HRS.Whole.withDensityReal rho) ∧
      ∫ z, ‖s82p2_gt Q x z‖ ^ 2 ∂HRS.Whole.withDensityReal rho ≤
        A ^ 2 * K0 * jbracket x ^ (4 * M) := by
  obtain ⟨K0, hK0, hrow⟩ := s82p2_row_env hd M hM G c hG hc rho hρ hρG
  refine ⟨K0, hK0, fun a beta A hA f Q hQ x => ?_⟩
  have h := hrow A hA x (fun z => ‖s82p2_gt Q x z‖) (fun z hz => by
    rw [abs_of_nonneg (norm_nonneg _)]
    exact s82p2_gt_norm_le hQ x z (Ne.symm hz))
  beta_reduce at h
  have hm : Measurable (fun z => ‖s82p2_gt Q x z‖ ^ 2) :=
    (((s82p2_gt_measurable Q).comp (measurable_prodMk_left (x := x))).norm).pow_const 2
  have hint : Integrable (fun z => ‖s82p2_gt Q x z‖ ^ 2) (HRS.Whole.withDensityReal rho) :=
    ⟨hm.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun z => sq_nonneg _)).2
        (lt_of_le_of_lt h ENNReal.ofReal_lt_top)⟩
  refine ⟨hint, ?_⟩
  have h1 := ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun z => sq_nonneg _)
  have hpos : 0 ≤ A ^ 2 * K0 * jbracket x ^ (4 * M) :=
    mul_nonneg (by positivity) (s82p2_jb_rpow_nonneg _ x)
  have h2 : ENNReal.ofReal (∫ z, ‖s82p2_gt Q x z‖ ^ 2 ∂HRS.Whole.withDensityReal rho) ≤
      ENNReal.ofReal (A ^ 2 * K0 * jbracket x ^ (4 * M)) := by
    rw [h1]; exact h
  exact (ENNReal.ofReal_le_ofReal_iff hpos).1 h2

end HRS.MS.S82P2
