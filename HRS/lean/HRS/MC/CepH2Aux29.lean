import HRS.MC.CepH2Aux28

/-!
# CEPH2, helper 29: the full dissipation `D∞(s) = ∫_cell u ‖dℓ‖²` and Fatou along the cut-offs
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators Pointwise

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ} [NeZero N]

/-- The dissipation density `u ‖dℓ‖²`. -/
def h2_dens (θ v : ℝ) (U : Ch N → ℝ) (μ : Measure (Ch N)) (x : Ch N) : ℝ :=
  h2_mu v μ x * ‖fderiv ℝ (h2_ell θ v U μ) x‖ ^ 2

/-- The full (uncut) dissipation, as an extended number. -/
def h2_Dinf (θ v : ℝ) (U : Ch N → ℝ) (μ : ℝ → Measure (Ch N)) (s : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in cep_cell N, ENNReal.ofReal (h2_dens θ v U (μ s) x)

section
variable {θ v : ℝ} {U : Ch N → ℝ} {K : ℝ≥0} {μ : ℝ → Measure (Ch N)} {T M : ℝ}

theorem h2_dens_nonneg (hv : 0 < v) (θ : ℝ) (U : Ch N → ℝ) (μ : Measure (Ch N)) [IsProbabilityMeasure μ]
    (x : Ch N) : 0 ≤ h2_dens θ v U μ x :=
  mul_nonneg (h2_mu_pos hv μ x).le (sq_nonneg _)

theorem H2Set.meas_dens (S : H2Set θ v U K μ T M) :
    Measurable (Function.uncurry fun (s : ℝ) (x : Ch N) => h2_dens θ v U (μ s) x) := by
  haveI : ∀ s, IsProbabilityMeasure (μ s) := S.hprob
  have hdU : ∀ k : Fin N, Measurable fun x : Ch N => fderiv ℝ U x (h2_e k) := fun k =>
    ((S.hU1.continuous_fderiv (by simp)).clm_apply continuous_const).measurable
  have hm : ∀ k : Fin N, Measurable (Function.uncurry fun (s : ℝ) (x : Ch N) =>
      ∫ y, h2_per1 v (x - y) (h2_e k) ∂μ s) := fun k =>
    h2_measurable_param S.hnar (h2_good_per1 S.hv U (h2_e k)) (fun s => (S.gradInt s).1)
  have hu : Measurable fun p : ℝ × Ch N => h2_mu v (μ p.1) p.2 := S.meas_u
  have hG : Measurable (fun p : ℝ × Ch N => h2_mu v (μ p.1) p.2 *
      ∑ k, ((h2_mu v (μ p.1) p.2)⁻¹ * (∫ y, h2_per1 v (p.2 - y) (h2_e k) ∂μ p.1) +
        (1 / θ) * fderiv ℝ U p.2 (h2_e k)) ^ 2) := by
    refine hu.mul (Finset.measurable_sum _ fun k _ => ?_)
    exact ((hu.inv.mul (hm k)).add (measurable_const.mul ((hdU k).comp measurable_snd))).pow_const 2
  have e : (Function.uncurry fun (s : ℝ) (x : Ch N) => h2_dens θ v U (μ s) x) = fun p : ℝ × Ch N =>
      h2_mu v (μ p.1) p.2 * ∑ k, ((h2_mu v (μ p.1) p.2)⁻¹ * (∫ y, h2_per1 v (p.2 - y) (h2_e k) ∂μ p.1) +
        (1 / θ) * fderiv ℝ U p.2 (h2_e k)) ^ 2 := by
    funext ⟨s, x⟩
    simp only [Function.uncurry_apply_pair, h2_dens, h2_norm_sq_fderiv_ell S.hv S.hU1 (μ s) x]
  rw [e]
  exact hG

theorem H2Set.meas_Dinf (S : H2Set θ v U K μ T M) : Measurable (h2_Dinf θ v U μ) := by
  have h : Measurable (fun p : ℝ × Ch N => ENNReal.ofReal (h2_dens θ v U (μ p.1) p.2)) :=
    ENNReal.measurable_ofReal.comp S.meas_dens
  exact h.lintegral_prod_right' (ν := volume.restrict (cep_cell N))

theorem H2Set.integrable_chi_dens (S : H2Set θ v U K μ T M) {R : ℝ} (hR : 0 < R) (s : ℝ) :
    Integrable (fun x => h2_chi R x * h2_dens θ v U (μ s) x) (volume.restrict (cep_cell N)) := by
  haveI := S.hprob s
  have hℓ := h2_contDiff_ell (θ := θ) S.hv S.hU1 (μ s)
  have hℓper := h2_ell_periodic (θ := θ) (v := v) S.hUper (μ s)
  refine h2_integrable_cell_of_far (R := 2 * R) ?_ (fun x => ?_) (fun x hx => ?_)
  · exact (h2_contDiff_chi1 R).continuous.mul ((h2_continuous_mu S.hv (μ s)).mul
      ((hℓ.continuous_fderiv (by simp)).norm.pow 2))
  · simp only [h2_dens, h2_chi_periodic, h2_mu_periodic, h2_fderiv_periodic hℓper]
  · simp [h2_chi_support hR x hx]

theorem H2Set.ofReal_Dchi (S : H2Set θ v U K μ T M) {R : ℝ} (hR : 0 < R) (s : ℝ) :
    ENNReal.ofReal (h2_Dchi θ v U μ R s) =
      ∫⁻ x in cep_cell N, ENNReal.ofReal (h2_chi R x * h2_dens θ v U (μ s) x) := by
  haveI := S.hprob s
  unfold h2_Dchi
  exact ofReal_integral_eq_lintegral_ofReal (S.integrable_chi_dens hR s)
    (ae_of_all _ fun x => mul_nonneg (h2_chi_nonneg R x) (h2_dens_nonneg S.hv θ U (μ s) x))

theorem H2Set.Dinf_le_liminf (S : H2Set θ v U K μ T M) (s : ℝ) :
    h2_Dinf θ v U μ s ≤ liminf (fun n : ℕ => ENNReal.ofReal (h2_Dchi θ v U μ ((n : ℝ) + 1) s)) atTop := by
  haveI := S.hprob s
  have hn : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hrw : ∀ n : ℕ, ENNReal.ofReal (h2_Dchi θ v U μ ((n : ℝ) + 1) s) =
      ∫⁻ x in cep_cell N, ENNReal.ofReal (h2_chi ((n : ℝ) + 1) x * h2_dens θ v U (μ s) x) :=
    fun n => S.ofReal_Dchi (hn n) s
  simp_rw [hrw]
  have hmeas : ∀ n : ℕ, Measurable fun x => ENNReal.ofReal (h2_chi ((n : ℝ) + 1) x * h2_dens θ v U (μ s) x) := by
    intro n
    have hℓ := h2_contDiff_ell (θ := θ) S.hv S.hU1 (μ s)
    exact ENNReal.measurable_ofReal.comp (((h2_contDiff_chi1 _).continuous.mul
      ((h2_continuous_mu S.hv (μ s)).mul ((hℓ.continuous_fderiv (by simp)).norm.pow 2))).measurable)
  refine le_trans ?_ (lintegral_liminf_le hmeas)
  unfold h2_Dinf
  refine lintegral_mono fun x => le_of_eq ?_
  symm
  refine Tendsto.liminf_eq ?_
  refine tendsto_const_nhds.congr' ?_
  rw [EventuallyEq, eventually_atTop]
  refine ⟨⌈‖h2_perp x‖⌉₊, fun n hn' => ?_⟩
  have h1 : ‖h2_perp x‖ ≤ (n : ℝ) + 1 := by
    have := Nat.le_ceil ‖h2_perp x‖
    have h2 : (⌈‖h2_perp x‖⌉₊ : ℝ) ≤ n := by exact_mod_cast hn'
    linarith
  rw [h2_chi_eq_one (hn n) h1, one_mul]

theorem H2Set.lintegral_Dinf_le (S : H2Set θ v U K μ T M) (t : ℝ) :
    ∫⁻ s in Icc (0 : ℝ) t, h2_Dinf θ v U μ s ≤
      liminf (fun n : ℕ => ∫⁻ s in Icc (0 : ℝ) t, ENNReal.ofReal (h2_Dchi θ v U μ ((n : ℝ) + 1) s)) atTop :=
  (lintegral_mono fun s => S.Dinf_le_liminf s).trans
    (lintegral_liminf_le fun n => ENNReal.measurable_ofReal.comp (S.meas_Dchi _))

end

end HRS.MC.CepH2
