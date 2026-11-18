import HRS.MC.CepH2Aux24

/-!
# CEPH2, helper 25: integrability of the free-energy density and the limit `R → ∞` of `Fχ_R`
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators Pointwise

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ} [NeZero N]

theorem h2_integrable_u_weight {v : ℝ} (hv : 0 < v) (μ : Measure (Ch N)) [IsProbabilityMeasure μ]
    (hmom : Integrable (fun y => ‖h2_perp y‖ ^ 2) μ) :
    Integrable (fun x => h2_mu v μ x * (1 + ‖h2_perp x‖ ^ 2)) (volume.restrict (cep_cell N)) := by
  have hc : Continuous fun x : Ch N => h2_mu v μ x * (1 + ‖h2_perp x‖ ^ 2) :=
    (h2_continuous_mu hv μ).mul (continuous_const.add (h2_continuous_perp.norm.pow 2))
  refine ⟨hc.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => mul_nonneg (h2_mu_pos hv μ x).le (by positivity))]
  have hw : Measurable fun x : Ch N => ENNReal.ofReal (1 + ‖h2_perp x‖ ^ 2) :=
    ENNReal.measurable_ofReal.comp (measurable_const.add (h2_continuous_perp.norm.pow 2).measurable)
  have hper : ∀ x : Ch N, ENNReal.ofReal (1 + ‖h2_perp (x + cep_diag N)‖ ^ 2) = ENNReal.ofReal (1 + ‖h2_perp x‖ ^ 2) := by
    intro x; rw [h2_perp_periodic]
  have := h2_moment_transfer hv μ hw hper (φ := fun y => 1 + 2 * ‖h2_perp y‖ ^ 2) (fun y => by positivity)
    (b := 2) (by norm_num) (fun x y => by
      refine ENNReal.ofReal_le_ofReal ?_
      nlinarith [h2_sq_perp_le x y])
  refine lt_of_le_of_lt (le_of_eq_of_le ?_ this) ?_
  · refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_mul (h2_mu_pos hv μ x).le]
  · have hi : Integrable (fun y => 1 + 2 * ‖h2_perp y‖ ^ 2 + 2 * (N * v)) μ :=
      ((integrable_const 1).add (hmom.const_mul 2)).add (integrable_const _)
    have := hi.hasFiniteIntegral
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun y => by positivity)] at this
    refine lt_of_le_of_lt (le_of_eq ?_) this
    refine lintegral_congr fun y => ?_
    congr 1

section
variable {θ v : ℝ} {U : Ch N → ℝ} {K : ℝ≥0} {μ : ℝ → Measure (Ch N)} {T M : ℝ}

theorem H2Set.integrable_Phi (S : H2Set θ v U K μ T M) (s : ℝ) :
    Integrable (fun x => h2_Phi θ U (h2_mu v (μ s) x) x) (volume.restrict (cep_cell N)) := by
  haveI := S.hprob s
  obtain ⟨cL, hcL, hL⟩ := S.log_bound
  obtain ⟨a, b, ha, hb, hU⟩ := h2_U_growth S.hU1 S.hUper S.hK
  have hθ := S.hθ
  have hμc := h2_continuous_mu S.hv (μ s)
  have hUc := S.hU1.continuous
  have hG := h2_integrable_u_weight S.hv (μ s) (S.hmom s)
  have hmeas : Continuous fun x => h2_Phi θ U (h2_mu v (μ s) x) x := by
    unfold h2_Phi
    exact (hμc.mul (hμc.log fun x => (h2_mu_pos S.hv (μ s) x).ne')).add ((hμc.mul hUc).div_const θ)
  refine Integrable.mono' (hG.const_mul (cL + (a + b) / θ)) hmeas.aestronglyMeasurable (ae_of_all _ fun x => ?_)
  have hu := h2_mu_pos S.hv (μ s) x
  set r := ‖h2_perp x‖
  have hr2 : 0 ≤ r ^ 2 := by positivity
  rw [Real.norm_eq_abs]
  unfold h2_Phi
  have h1 : |h2_mu v (μ s) x * Real.log (h2_mu v (μ s) x)| ≤ h2_mu v (μ s) x * (cL * (1 + r ^ 2)) := by
    rw [abs_mul, abs_of_pos hu]
    exact mul_le_mul_of_nonneg_left (hL s x) hu.le
  have h2 : |h2_mu v (μ s) x * U x / θ| ≤ h2_mu v (μ s) x * ((a + b) / θ * (1 + r ^ 2)) := by
    rw [abs_div, abs_of_pos hθ, abs_mul, abs_of_pos hu, div_le_iff₀ hθ]
    have h3 : |U x| ≤ (a + b) * (1 + r ^ 2) := by
      refine (hU x).trans ?_
      nlinarith [mul_nonneg ha hr2, mul_nonneg hb hr2]
    calc h2_mu v (μ s) x * |U x| ≤ h2_mu v (μ s) x * ((a + b) * (1 + r ^ 2)) := mul_le_mul_of_nonneg_left h3 hu.le
      _ = _ := by field_simp
  refine (abs_add_le _ _).trans ?_
  calc _ ≤ h2_mu v (μ s) x * (cL * (1 + r ^ 2)) + h2_mu v (μ s) x * ((a + b) / θ * (1 + r ^ 2)) := add_le_add h1 h2
    _ = _ := by ring

theorem H2Set.tendsto_Fchi (S : H2Set θ v U K μ T M) (s : ℝ) :
    Tendsto (fun n : ℕ => h2_Fchi θ v U μ ((n : ℝ) + 1) s) atTop (𝓝 (h2_free θ U (h2_mu v (μ s)))) := by
  have hint := S.integrable_Phi s
  unfold h2_Fchi h2_free
  refine tendsto_integral_of_dominated_convergence (fun x => ‖h2_Phi θ U (h2_mu v (μ s) x) x‖) ?_ hint.norm ?_ ?_
  · intro n
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    haveI := S.hprob s
    have hμc := h2_continuous_mu S.hv (μ s)
    have hUc := S.hU1.continuous
    have : Continuous fun x => h2_chi ((n : ℝ) + 1) x * h2_Phi θ U (h2_mu v (μ s) x) x := by
      unfold h2_Phi
      exact (h2_contDiff_chi1 _).continuous.mul ((hμc.mul (hμc.log fun x => (h2_mu_pos S.hv (μ s) x).ne')).add
        ((hμc.mul hUc).div_const θ))
    exact this.aestronglyMeasurable
  · intro n
    refine ae_of_all _ fun x => ?_
    rw [norm_mul, Real.norm_of_nonneg (h2_chi_nonneg _ _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (h2_chi_le_one _ _)
  · refine ae_of_all _ fun x => ?_
    refine tendsto_const_nhds.congr' ?_
    rw [EventuallyEq, eventually_atTop]
    refine ⟨⌈‖h2_perp x‖⌉₊, fun n hn => ?_⟩
    have hn' : ‖h2_perp x‖ ≤ (n : ℝ) + 1 := by
      have := Nat.le_ceil ‖h2_perp x‖
      have h2 : (⌈‖h2_perp x‖⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    rw [h2_chi_eq_one (by positivity) hn', one_mul]
    rfl

end

end HRS.MC.CepH2
