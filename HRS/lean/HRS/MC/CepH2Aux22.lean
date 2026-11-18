import HRS.MC.CepH2Aux21

/-!
# CEPH2, helper 22: Fubini in time and the cut-off free energy

`Fχ(t) - Fχ(0) = ∫_0^t Tχ(s) ds` with `Tχ(s) = ∫_cell χ (ℓ_s + 1) a(s, ·)`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators Pointwise

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ} [NeZero N]

/-- Integrability on `cell × Icc 0 t` of a measurable function vanishing off a tube and bounded on it. -/
theorem h2_integrable_tube_prod {F : Ch N → ℝ → ℝ} (hF : Measurable (Function.uncurry F)) {R C : ℝ}
    (hout : ∀ x s, R < ‖h2_perp x‖ → F x s = 0) (hin : ∀ x s, |F x s| ≤ |C|) (t : ℝ) :
    Integrable (Function.uncurry F) ((volume.restrict (cep_cell N)).prod (volume.restrict (Icc (0 : ℝ) t))) := by
  have h1 := h2_integrable_tube_indicator (N := N) R |C|
  have h2 : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict (Icc (0 : ℝ) t)) :=
    integrableOn_const (by simp)
  have hb := h1.mul_prod h2
  refine Integrable.mono' hb hF.aestronglyMeasurable (ae_of_all _ fun z => ?_)
  rcases z with ⟨x, s⟩
  by_cases hx : ‖h2_perp x‖ ≤ R
  · simp only [Function.uncurry_apply_pair, Set.indicator_of_mem (show x ∈ {x : Ch N | ‖h2_perp x‖ ≤ R} from hx),
      mul_one, Real.norm_eq_abs]
    exact hin x s
  · simp only [Function.uncurry_apply_pair, hout x s (not_le.1 hx), norm_zero]
    exact mul_nonneg (Set.indicator_nonneg (fun _ _ => abs_nonneg C) x) zero_le_one

section
variable {θ v : ℝ} {U : Ch N → ℝ} {K : ℝ≥0} {μ : ℝ → Measure (Ch N)} {T M : ℝ}

theorem H2Set.meas_u (S : H2Set θ v U K μ T M) : Measurable (Function.uncurry fun (s : ℝ) (x : Ch N) => h2_mu v (μ s) x) :=
  haveI : ∀ s, IsProbabilityMeasure (μ s) := S.hprob
  h2_measurable_param S.hnar (h2_good_per S.hv U) (fun s => (S.gradInt s).1)

theorem H2Set.meas_a (S : H2Set θ v U K μ T M) :
    Measurable (Function.uncurry fun (s : ℝ) (x : Ch N) => ∫ y, h2_A θ v U x y ∂μ s) :=
  haveI : ∀ s, IsProbabilityMeasure (μ s) := S.hprob
  h2_measurable_param S.hnar (h2_good_A S.hv θ S.hU1 S.hUper S.hK) (fun s => (S.gradInt s).1)

theorem H2Set.meas_ell (S : H2Set θ v U K μ T M) :
    Measurable (Function.uncurry fun (s : ℝ) (x : Ch N) => h2_ell θ v U (μ s) x) := by
  have hU : Measurable U := S.hU1.continuous.measurable
  have := (Real.measurable_log.comp S.meas_u).add (measurable_const.mul (hU.comp measurable_snd) : Measurable
    fun p : ℝ × Ch N => (1 / θ) * U p.2)
  exact this

/-- Joint bound of the integrand of `Tχ` on the tube. -/
theorem H2Set.theta_bound (S : H2Set θ v U K μ T M) {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, ∀ s x, |h2_chi R x * ((h2_ell θ v U (μ s) x + 1) * ∫ y, h2_A θ v U x y ∂μ s)| ≤ |C| ∧
      (2 * R < ‖h2_perp x‖ → h2_chi R x * ((h2_ell θ v U (μ s) x + 1) * ∫ y, h2_A θ v U x y ∂μ s) = 0) := by
  obtain ⟨Ca, hCa0, hCa⟩ := S.bound_A
  obtain ⟨cE, hcE, hE⟩ := S.ell_bound
  refine ⟨(cE * (1 + (2 * R) ^ 2) + 1) * Ca, fun s x => ⟨?_, fun hx => by simp [h2_chi_support hR x hx]⟩⟩
  by_cases hx : ‖h2_perp x‖ ≤ 2 * R
  · rw [abs_mul, abs_mul]
    have h1 : |h2_chi R x| ≤ 1 := by rw [abs_of_nonneg (h2_chi_nonneg R x)]; exact h2_chi_le_one R x
    have h2 : |h2_ell θ v U (μ s) x + 1| ≤ cE * (1 + (2 * R) ^ 2) + 1 := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_one]
      have := hE s x
      have h3 : 1 + ‖h2_perp x‖ ^ 2 ≤ 1 + (2 * R) ^ 2 := by nlinarith [norm_nonneg (h2_perp x)]
      nlinarith [mul_le_mul_of_nonneg_left h3 hcE]
    have h4 := hCa s x
    have hC : 0 ≤ (cE * (1 + (2 * R) ^ 2) + 1) * Ca := by positivity
    rw [abs_of_nonneg hC]
    calc |h2_chi R x| * (|h2_ell θ v U (μ s) x + 1| * |∫ y, h2_A θ v U x y ∂μ s|)
        ≤ 1 * ((cE * (1 + (2 * R) ^ 2) + 1) * Ca) :=
          mul_le_mul h1 (mul_le_mul h2 h4 (abs_nonneg _) (by positivity)) (by positivity) zero_le_one
      _ = _ := one_mul _
  · simp [h2_chi_support hR x (not_le.1 hx)]
    positivity

theorem H2Set.integrable_chiPhi (S : H2Set θ v U K μ T M) {R : ℝ} (hR : 0 < R) (s : ℝ) :
    Integrable (fun x => h2_chi R x * h2_Phi θ U (h2_mu v (μ s) x) x) (volume.restrict (cep_cell N)) := by
  haveI := S.hprob s
  have hμc := h2_continuous_mu S.hv (μ s)
  have hUc := S.hU1.continuous
  refine h2_integrable_cell_of_far (R := 2 * R) ?_ ?_ (fun x hx => by simp [h2_chi_support hR x hx])
  · unfold h2_Phi
    exact (h2_contDiff_chi1 R).continuous.mul ((hμc.mul (hμc.log fun x => (h2_mu_pos S.hv (μ s) x).ne')).add
      ((hμc.mul hUc).div_const θ))
  · intro x
    simp only [h2_chi_periodic, h2_Phi, h2_mu_periodic, S.hUper]

/-- The cut-off free energy and the time-slice quantity. -/
def h2_Fchi (θ v : ℝ) (U : Ch N → ℝ) (μ : ℝ → Measure (Ch N)) (R t : ℝ) : ℝ :=
  ∫ x in cep_cell N, h2_chi R x * h2_Phi θ U (h2_mu v (μ t) x) x

def h2_Tchi (θ v : ℝ) (U : Ch N → ℝ) (μ : ℝ → Measure (Ch N)) (R s : ℝ) : ℝ :=
  ∫ x in cep_cell N, h2_chi R x * ((h2_ell θ v U (μ s) x + 1) * ∫ y, h2_A θ v U x y ∂μ s)

theorem H2Set.int_theta (S : H2Set θ v U K μ T M) {R : ℝ} (hR : 0 < R) (t : ℝ) :
    Integrable (Function.uncurry fun (x : Ch N) (s : ℝ) =>
      h2_chi R x * ((h2_ell θ v U (μ s) x + 1) * ∫ y, h2_A θ v U x y ∂μ s))
      ((volume.restrict (cep_cell N)).prod (volume.restrict (Icc (0 : ℝ) t))) := by
  obtain ⟨C, hC⟩ := S.theta_bound hR
  have hχm : Measurable (h2_chi (N := N) R) := (h2_contDiff_chi1 R).continuous.measurable
  have hF : Measurable (Function.uncurry fun (x : Ch N) (s : ℝ) =>
      h2_chi R x * ((h2_ell θ v U (μ s) x + 1) * ∫ y, h2_A θ v U x y ∂μ s)) := by
    have h1 : Measurable fun p : Ch N × ℝ => h2_chi R p.1 := hχm.comp measurable_fst
    have h2 : Measurable fun p : Ch N × ℝ => h2_ell θ v U (μ p.2) p.1 :=
      S.meas_ell.comp measurable_swap
    have h3 : Measurable fun p : Ch N × ℝ => ∫ y, h2_A θ v U p.1 y ∂μ p.2 :=
      S.meas_a.comp measurable_swap
    exact h1.mul ((h2.add measurable_const).mul h3)
  exact h2_integrable_tube_prod hF (R := 2 * R) (C := C) (fun x s hx => (hC s x).2 hx)
    (fun x s => (hC s x).1) t

theorem H2Set.int_Tchi (S : H2Set θ v U K μ T M) {R : ℝ} (hR : 0 < R) (t : ℝ) :
    Integrable (fun s => h2_Tchi θ v U μ R s) (volume.restrict (Icc (0 : ℝ) t)) :=
  (S.int_theta hR t).integral_prod_right

theorem H2Set.fchi_eq (S : H2Set θ v U K μ T M) {R : ℝ} (hR : 0 < R) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    h2_Fchi θ v U μ R t - h2_Fchi θ v U μ R 0 = ∫ s in Icc (0 : ℝ) t, h2_Tchi θ v U μ R s := by
  have hswap := integral_integral_swap (S.int_theta hR t)
  unfold h2_Fchi h2_Tchi
  rw [← integral_sub (S.integrable_chiPhi hR t) (S.integrable_chiPhi hR 0)]
  have h1 : ∀ x, h2_chi R x * h2_Phi θ U (h2_mu v (μ t) x) x - h2_chi R x * h2_Phi θ U (h2_mu v (μ 0) x) x =
      ∫ s in Icc (0 : ℝ) t, h2_chi R x * ((h2_ell θ v U (μ s) x + 1) * ∫ y, h2_A θ v U x y ∂μ s) := by
    intro x
    rw [integral_const_mul, ← S.pointwise_ftc x ht]
    ring
  simp_rw [h1]
  exact hswap

end

end HRS.MC.CepH2
