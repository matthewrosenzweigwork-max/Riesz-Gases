import HRS.MS.R26T8AP10a4
import HRS.MS.R26T8AP10a2

/-!
# S8.2 T8A P10a (part 5): the integration by parts with the cutoff `cut_δ`, for fixed `ε > 0`
For `h : E → E` of class `C^1` off `y`, `Hj = cut_δ · h_j` is `C^1` on `E`, with the explicit derivative `Dj`.
`r26t8a_p10a_ibp_j`: `∫ k_ε(x-u) Dj u = ∫ ∂_j k_ε(x-u) Hj u` (Mathlib's integration by parts).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

/-- The `j`-th cut-off component. -/
def r26t8a_Hj (chi : Euc d → ℝ) (y : Euc d) (δ : ℝ) (h : Euc d → Euc d) (j : Fin d) (u : Euc d) : ℝ :=
  r26t8a_cut chi y δ u * h u j

/-- Its `j`-th partial derivative (explicit formula). -/
def r26t8a_Dj (chi : Euc d → ℝ) (y : Euc d) (δ : ℝ) (h : Euc d → Euc d) (j : Fin d) (u : Euc d) : ℝ :=
  r26t8a_cut chi y δ u * (fderiv ℝ h u (EuclideanSpace.single j 1)) j +
    h u j * fderiv ℝ (r26t8a_cut chi y δ) u (EuclideanSpace.single j 1)

theorem r26t8a_hasFDerivAt_Hj {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {y : Euc d}
    {δ : ℝ} (hδ : 0 < δ) {h : Euc d → Euc d} (hC : ContDiffOn ℝ 1 h {y}ᶜ) (j : Fin d) (u : Euc d) :
    HasFDerivAt (r26t8a_Hj chi y δ h j)
      (r26t8a_cut chi y δ u • ((EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).comp (fderiv ℝ h u)) +
        h u j • fderiv ℝ (r26t8a_cut chi y δ) u) u := by
  by_cases hu : ‖u - y‖ < δ
  · have hz : r26t8a_Hj chi y δ h j =ᶠ[𝓝 u] fun _ => 0 := by
      have hm : ball y δ ∈ 𝓝 u :=
        isOpen_ball.mem_nhds (by simpa [mem_ball_iff_norm, dist_eq_norm] using hu)
      filter_upwards [hm] with v hv
      have := r26t8a_cut_eq_zero hchi y hδ (by simpa [mem_ball_iff_norm, dist_eq_norm] using hv.le)
      simp [r26t8a_Hj, this]
    have h0 := (hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) u).congr_of_eventuallyEq hz
    have e1 := r26t8a_cut_eq_zero hchi y hδ hu.le
    have e2 := r26t8a_cut_fderiv_zero_lt hchi y hδ hu
    rw [e1, e2]
    simpa using h0
  · have hne : u ≠ y := by
      intro h'; apply hu; rw [h']; simpa using hδ
    have hopen : IsOpen ({y}ᶜ : Set (Euc d)) := isClosed_singleton.isOpen_compl
    have hdiff : DifferentiableAt ℝ h u :=
      (hC.contDiffAt (hopen.mem_nhds (by simpa using hne))).differentiableAt (by simp)
    have hg : HasFDerivAt (fun v => h v j)
        ((EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).comp (fderiv ℝ h u)) u :=
      (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).hasFDerivAt.comp u hdiff.hasFDerivAt
    have hc := ((r26t8a_cut_contDiff hchi y δ).differentiable (by simp) u).hasFDerivAt
    exact hc.mul hg

theorem r26t8a_fderiv_Hj {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {y : Euc d}
    {δ : ℝ} (hδ : 0 < δ) {h : Euc d → Euc d} (hC : ContDiffOn ℝ 1 h {y}ᶜ) (j : Fin d) (u : Euc d) :
    fderiv ℝ (r26t8a_Hj chi y δ h j) u (EuclideanSpace.single j 1) = r26t8a_Dj chi y δ h j u := by
  rw [(r26t8a_hasFDerivAt_Hj hchi hδ hC j u).fderiv]
  simp [r26t8a_Dj]

theorem r26t8a_Hj_continuous {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {y : Euc d}
    {δ : ℝ} (hδ : 0 < δ) {h : Euc d → Euc d} (hC : ContDiffOn ℝ 1 h {y}ᶜ) (j : Fin d) :
    Continuous (r26t8a_Hj chi y δ h j) :=
  continuous_iff_continuousAt.2 fun u => (r26t8a_hasFDerivAt_Hj hchi hδ hC j u).continuousAt

theorem r26t8a_Dj_continuousOn {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (y : Euc d) (δ : ℝ)
    {h : Euc d → Euc d} (hC : ContDiffOn ℝ 1 h {y}ᶜ) (j : Fin d) :
    ContinuousOn (r26t8a_Dj chi y δ h j) {y}ᶜ := by
  have hopen : IsOpen ({y}ᶜ : Set (Euc d)) := isClosed_singleton.isOpen_compl
  have h1 : ContinuousOn (fderiv ℝ h) {y}ᶜ := hC.continuousOn_fderiv_of_isOpen hopen (by simp)
  have h2 : ContinuousOn h {y}ᶜ := hC.continuousOn
  have hc := (r26t8a_cut_contDiff hchi y δ).continuous
  have hfc := (r26t8a_cut_contDiff hchi y δ).continuous_fderiv (by simp)
  have hj : Continuous fun v : Euc d => v j := (EuclideanSpace.proj j).continuous
  unfold r26t8a_Dj
  refine (hc.continuousOn.mul ?_).add (?_)
  · exact hj.comp_continuousOn (h1.clm_apply continuousOn_const)
  · exact (hj.comp_continuousOn h2).mul (hfc.clm_apply continuous_const).continuousOn

theorem r26t8a_norm_single (j : Fin d) : ‖(EuclideanSpace.single j (1 : ℝ) : Euc d)‖ = 1 := by
  simp

/-- Bounds for `Hj` and `Dj`. -/
theorem r26t8a_Hj_bound {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (y : Euc d) (δ : ℝ)
    {h : Euc d → Euc d} (j : Fin d) (u : Euc d) : |r26t8a_Hj chi y δ h j u| ≤ ‖h u‖ := by
  unfold r26t8a_Hj
  have := r26t8a_cut_mem hchi y δ u
  rw [abs_mul, abs_of_nonneg this.1]
  calc r26t8a_cut chi y δ u * |h u j| ≤ 1 * ‖h u‖ :=
        mul_le_mul this.2 (r26t8a_abs_coord_le _ _) (abs_nonneg _) zero_le_one
    _ = _ := one_mul _

theorem r26t8a_Dj_bound {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (y : Euc d) {δ : ℝ}
    (hδ : 0 < δ) {Cχ : ℝ} (hCχ : ∀ u : Euc d, ‖fderiv ℝ (r26t8a_cut chi y δ) u‖ ≤ Cχ / δ)
    {h : Euc d → Euc d} (j : Fin d) (u : Euc d) :
    |r26t8a_Dj chi y δ h j u| ≤ ‖fderiv ℝ h u‖ + Cχ / δ * ‖h u‖ := by
  unfold r26t8a_Dj
  have hm := r26t8a_cut_mem hchi y δ u
  have e1 : |(fderiv ℝ h u (EuclideanSpace.single j 1)) j| ≤ ‖fderiv ℝ h u‖ := by
    refine (r26t8a_abs_coord_le _ _).trans ?_
    calc ‖fderiv ℝ h u (EuclideanSpace.single j 1)‖ ≤ ‖fderiv ℝ h u‖ * ‖(EuclideanSpace.single j (1 : ℝ) : Euc d)‖ :=
          (fderiv ℝ h u).le_opNorm _
      _ = _ := by rw [r26t8a_norm_single, mul_one]
  have e2 : |fderiv ℝ (r26t8a_cut chi y δ) u (EuclideanSpace.single j 1)| ≤ Cχ / δ := by
    rw [← Real.norm_eq_abs]
    calc ‖fderiv ℝ (r26t8a_cut chi y δ) u (EuclideanSpace.single j 1)‖
        ≤ ‖fderiv ℝ (r26t8a_cut chi y δ) u‖ * ‖(EuclideanSpace.single j (1 : ℝ) : Euc d)‖ :=
          (fderiv ℝ (r26t8a_cut chi y δ) u).le_opNorm _
      _ ≤ Cχ / δ := by rw [r26t8a_norm_single, mul_one]; exact hCχ u
  have hc0 : 0 ≤ Cχ / δ := (norm_nonneg _).trans (hCχ u)
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg hm.1]
  have h3 : |h u j| ≤ ‖h u‖ := r26t8a_abs_coord_le _ _
  have := mul_le_mul hm.2 e1 (abs_nonneg _) zero_le_one
  have := mul_le_mul h3 e2 (abs_nonneg _) (norm_nonneg _)
  nlinarith [norm_nonneg (h u), norm_nonneg (fderiv ℝ h u)]

end HRS.MS.R26T8A
