import HRS.MS.SA16SHw1

/-!
# S.A.16 (SA16S) Hw2: the time derivative of `∫ (g_a ⋆ φ) ψ`

`sa16sw_green`: `∫ (Δ f) ψ = ∫ f (Δ ψ)` for `f` smooth, `ψ ∈ C_c^∞`; `sa16sw_lap_cv`: `Δ (g_a ⋆ φ) = g_a ⋆ Δφ`;
`sa16sw_F_hasDerivAt`: `d/da ∫ (g_a ⋆ φ) ψ = ∫ (g_a ⋆ φ) Δψ`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Hw2
variable {d : ℕ}

lemma sa16sw_ibp {h : Euc d → ℝ} (hh : ContDiff ℝ ∞ h) {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ) (e : Euc d) :
    ∫ x, fderiv ℝ h x e * ψ x = -∫ x, h x * fderiv ℝ ψ x e := by
  have hdh : Continuous (fun x => fderiv ℝ h x e) :=
    (hh.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdψ := sa16s_cc_fderiv hψ e
  have h1 : Integrable (fun x => fderiv ℝ h x e * ψ x) :=
    (hdh.mul hψ.1.continuous).integrable_of_hasCompactSupport hψ.2.mul_left
  have h2 : Integrable (fun x => h x * fderiv ℝ ψ x e) :=
    (hh.continuous.mul hdψ.1.continuous).integrable_of_hasCompactSupport hdψ.2.mul_left
  have h3 : Integrable (fun x => h x * ψ x) :=
    (hh.continuous.mul hψ.1.continuous).integrable_of_hasCompactSupport hψ.2.mul_left
  have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (v := e) h1 h2 h3
    (fun x _ => (hh.differentiable (by simp)) x) (fun x _ => (hψ.1.differentiable (by simp)) x)
  linarith

lemma sa16sw_green {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ) :
    ∫ x, sa16r_lap f x * ψ x = ∫ x, f x * sa16r_lap ψ x := by
  have hu : ∀ i : Fin d, ContDiff ℝ ∞ (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) :=
    fun i => (hf.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
  have hv : ∀ i : Fin d, IsCcInfty (fun y => fderiv ℝ ψ y (EuclideanSpace.single i 1)) :=
    fun i => sa16s_cc_fderiv hψ _
  have hw : ∀ i : Fin d, IsCcInfty (fun y => fderiv ℝ (fun y => fderiv ℝ ψ y (EuclideanSpace.single i 1)) y
      (EuclideanSpace.single i 1)) := fun i => sa16s_cc_fderiv (hv i) _
  have hint1 : ∀ i : Fin d, Integrable (fun x => fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x
      (EuclideanSpace.single i 1) * ψ x) := by
    intro i
    have hc : Continuous (fun x => fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1)) := ((hu i).continuous_fderiv (by simp)).clm_apply continuous_const
    exact (hc.mul hψ.1.continuous).integrable_of_hasCompactSupport hψ.2.mul_left
  have hint2 : ∀ i : Fin d, Integrable (fun x => f x * fderiv ℝ (fun y => fderiv ℝ ψ y
      (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1)) := by
    intro i
    exact (hf.continuous.mul (hw i).1.continuous).integrable_of_hasCompactSupport (hw i).2.mul_left
  simp_rw [sa16r_lap, Finset.sum_mul, Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => hint1 i), integral_finsetSum _ (fun i _ => hint2 i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 := sa16sw_ibp (hu i) hψ (EuclideanSpace.single i 1)
  have h2 := sa16sw_ibp hf (hv i) (EuclideanSpace.single i 1)
  rw [h1]
  have h3 : ∫ x, f x * fderiv ℝ (fun y => fderiv ℝ ψ y (EuclideanSpace.single i 1)) x
      (EuclideanSpace.single i 1) = -∫ x, fderiv ℝ f x (EuclideanSpace.single i 1) *
        fderiv ℝ ψ x (EuclideanSpace.single i 1) := by
    linarith
  rw [h3]

lemma sa16sw_lap_cv {a : ℝ} (ha : 0 < a) {φ : Euc d → ℝ} (hφ : IsCcInfty φ) :
    sa16r_lap (sa16r_cv (sa16r_g d a) φ) = sa16r_cv (sa16r_g d a) (sa16r_lap φ) := by
  funext x
  have h1 : ∀ i : Fin d, (fun y => fderiv ℝ (sa16r_cv (sa16r_g d a) φ) y (EuclideanSpace.single i 1)) =
      sa16r_cv (sa16r_g d a) (fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)) :=
    fun i => funext fun y => sa16r_cv_fderiv ha hφ y _
  have h2 : ∀ i : Fin d, fderiv ℝ (sa16r_cv (sa16r_g d a) (fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)))
      x (EuclideanSpace.single i 1) = sa16r_cv (sa16r_g d a) (fun y => fderiv ℝ (fun y => fderiv ℝ φ y
        (EuclideanSpace.single i 1)) y (EuclideanSpace.single i 1)) x :=
    fun i => sa16r_cv_fderiv ha (sa16s_cc_fderiv hφ _) x _
  have hR : sa16r_lap φ = fun y => ∑ i : Fin d, fderiv ℝ (fun y => fderiv ℝ φ y
      (EuclideanSpace.single i 1)) y (EuclideanSpace.single i 1) := rfl
  have hL : sa16r_lap (sa16r_cv (sa16r_g d a) φ) x = ∑ i : Fin d, fderiv ℝ (fun y => fderiv ℝ
      (sa16r_cv (sa16r_g d a) φ) y (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1) := rfl
  rw [hL, hR]
  simp only [h1, h2]
  unfold sa16r_cv
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum]
  intro i _
  exact sa16r_cv_integrand (sa16r_g_int ha) (sa16s_cc_fderiv (sa16s_cc_fderiv hφ _) _) x

/-- the outer derivative: `d/da ∫ (g_a ⋆ φ) ψ = ∫ (g_a ⋆ Δφ) ψ` -/
lemma sa16sw_outer_hasDerivAt {a0 : ℝ} (ha0 : 0 < a0) {φ ψ : Euc d → ℝ} (hφ : IsCcInfty φ)
    (hψ : IsCcInfty ψ) :
    HasDerivAt (fun a => ∫ x, sa16r_cv (sa16r_g d a) φ x * ψ x)
      (∫ x, sa16r_cv (sa16r_g d a0) (sa16r_lap φ) x * ψ x) a0 := by
  obtain ⟨Bl, hBl⟩ := sa16r_cc_bdd (sa16sw_cc_lap hφ)
  have hψi : Integrable ψ := hψ.1.continuous.integrable_of_hasCompactSupport hψ.2
  have hs : Ioi (0 : ℝ) ∈ 𝓝 a0 := Ioi_mem_nhds ha0
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure (Euc d)))
    (F := fun a x => sa16r_cv (sa16r_g d a) φ x * ψ x)
    (F' := fun a x => sa16r_cv (sa16r_g d a) (sa16r_lap φ) x * ψ x) (bound := fun x => Bl * |ψ x|) hs
    ?_ ?_ ?_ ?_ (hψi.abs.const_mul Bl) ?_
  · exact key.2
  · filter_upwards [hs] with a ha
    exact ((sa16r_cv_contDiff ha hφ).continuous.mul hψ.1.continuous).aestronglyMeasurable
  · exact ((sa16r_cv_contDiff ha0 hφ).continuous.mul hψ.1.continuous).integrable_of_hasCompactSupport
      hψ.2.mul_left
  · exact ((sa16r_cv_contDiff ha0 (sa16sw_cc_lap hφ)).continuous.mul hψ.1.continuous).aestronglyMeasurable
  · refine Eventually.of_forall fun x a ha => ?_
    show ‖sa16r_cv (sa16r_g d a) (sa16r_lap φ) x * ψ x‖ ≤ Bl * |ψ x|
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (sa16sw_cv_abs_le ha hBl x) (abs_nonneg _)
  · refine Eventually.of_forall fun x a ha => ?_
    exact (sa16sw_cv_hasDerivAt ha hφ x).mul_const (ψ x)

end Hw2

end HRS.Whole.AppendixA.Phase2SA16R
