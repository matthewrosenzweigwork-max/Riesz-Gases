import HRS.MS.SA12V2

/-!
# S.A.12 C1, mollification toolkit

A normalised smooth bump `η_δ` supported in the closed ball of radius `δ`, the mollification
`moll η f (x) = ∫ η(u) f(x - u) du` of a continuous (vector valued) function, and its calculus:
norm bounds, periodicity, commutation of iterated derivatives with mollification, smoothness.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd

variable {d : ℕ}

/-- The properties of a mollifier of radius `δ`. -/
structure SA12KMoll (δ : ℝ) (η : Euc d → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ η x
  integral_one : ∫ x, η x = 1
  support : ∀ x, δ < ‖x‖ → η x = 0
  smooth : ContDiff ℝ ∞ η
  compact : HasCompactSupport η

/-- The normalised bump of radius `δ`. -/
def sa12k_bumpF (δ : ℝ) (hδ : 0 < δ) : ContDiffBump (0 : Euc d) :=
  ⟨δ / 2, δ, by linarith, by linarith⟩

def sa12k_eta (δ : ℝ) (hδ : 0 < δ) : Euc d → ℝ := (sa12k_bumpF (d := d) δ hδ).normed volume

theorem sa12k_eta_moll (δ : ℝ) (hδ : 0 < δ) : SA12KMoll δ (sa12k_eta (d := d) δ hδ) := by
  refine ⟨fun x => ContDiffBump.nonneg_normed _ x, ContDiffBump.integral_normed _, fun x hx => ?_,
    ContDiffBump.contDiff_normed _, ContDiffBump.hasCompactSupport_normed _⟩
  have h := ContDiffBump.support_normed_eq (sa12k_bumpF (d := d) δ hδ) (μ := volume)
  by_contra hne
  have hmem : x ∈ Function.support (sa12k_eta (d := d) δ hδ) := hne
  unfold sa12k_eta at hmem
  rw [h] at hmem
  have : ‖x‖ < δ := by
    have := hmem
    rw [Metric.mem_ball, dist_zero_right] at this
    exact this
  linarith

/-- The radius `1/max L 1`. -/
def sa12k_rad (L : ℝ) : ℝ := 1 / max L 1

theorem sa12k_rad_pos (L : ℝ) : 0 < sa12k_rad L := by
  unfold sa12k_rad
  have : (0 : ℝ) < max L 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  positivity

theorem sa12k_rad_le_one (L : ℝ) : sa12k_rad L ≤ 1 := by
  unfold sa12k_rad
  rw [div_le_one (lt_of_lt_of_le one_pos (le_max_right _ _))]
  exact le_max_right _ _

theorem sa12k_rad_le_inv {L : ℝ} (hL : 1 ≤ L) : sa12k_rad L ≤ 1 / L := by
  unfold sa12k_rad
  rw [max_eq_left hL]

/-- The mollifier of scale `1/max L 1`. -/
def sa12k_etaL (L : ℝ) : Euc d → ℝ := sa12k_eta (sa12k_rad L) (sa12k_rad_pos L)

theorem sa12k_etaL_moll (L : ℝ) : SA12KMoll (sa12k_rad L) (sa12k_etaL (d := d) L) :=
  sa12k_eta_moll _ _

/-- The mollification `∫ η(u) f(x-u) du`. -/
def sa12k_moll {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] (η : Euc d → ℝ) (f : Euc d → W)
    (x : Euc d) : W :=
  ∫ u, η u • f (x - u)

variable {δ : ℝ} {η : Euc d → ℝ}
variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

theorem SA12KMoll.integrable (hη : SA12KMoll δ η) : Integrable η :=
  (hη.smooth.continuous).integrable_of_hasCompactSupport hη.compact

theorem sa12k_integrand_integrable (hη : SA12KMoll δ η) {f : Euc d → W} (hf : Continuous f) (x : Euc d) :
    Integrable (fun u => η u • f (x - u)) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact hη.smooth.continuous.smul (hf.comp (continuous_const.sub continuous_id))
  · exact hη.compact.smul_right

theorem SA12KMoll.delta_nonneg (hη : SA12KMoll δ η) : 0 ≤ δ := by
  by_contra hneg
  have hneg' : δ < 0 := not_le.1 hneg
  have hz : ∀ y : Euc d, η y = 0 := fun y =>
    hη.support y (lt_of_lt_of_le hneg' (norm_nonneg y))
  have : ∫ x, η x = 0 := by simp [hz]
  have h1 := hη.integral_one
  linarith

theorem sa12k_moll_norm_le_local (hη : SA12KMoll δ η) {f : Euc d → W} (hf : Continuous f) (x : Euc d)
    {E : ℝ} (hE : ∀ u : Euc d, ‖u‖ ≤ δ → ‖f (x - u)‖ ≤ E) : ‖sa12k_moll η f x‖ ≤ E := by
  unfold sa12k_moll
  have h0 : 0 ≤ E := by
    have := hE 0 (by simpa using hη.delta_nonneg)
    exact (norm_nonneg _).trans this
  calc ‖∫ u, η u • f (x - u)‖ ≤ ∫ u, ‖η u • f (x - u)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u, η u * E := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => norm_nonneg _)
          (hη.integrable.mul_const E) (Filter.Eventually.of_forall fun u => ?_)
        show ‖η u • f (x - u)‖ ≤ η u * E
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hη.nonneg u)]
        by_cases hu : δ < ‖u‖
        · rw [hη.support u hu]; simp
        · exact mul_le_mul_of_nonneg_left (hE u (not_lt.1 hu)) (hη.nonneg u)
    _ = E := by rw [integral_mul_const, hη.integral_one, one_mul]

theorem sa12k_moll_norm_le (hη : SA12KMoll δ η) {f : Euc d → W} (hf : Continuous f) {B : ℝ}
    (hB : ∀ y, ‖f y‖ ≤ B) (x : Euc d) : ‖sa12k_moll η f x‖ ≤ B :=
  sa12k_moll_norm_le_local hη hf x fun u _ => hB _

theorem sa12k_moll_sub (hη : SA12KMoll δ η) {f g : Euc d → W} (hf : Continuous f) (hg : Continuous g)
    (x : Euc d) : sa12k_moll η (fun y => f y - g y) x = sa12k_moll η f x - sa12k_moll η g x := by
  unfold sa12k_moll
  rw [← integral_sub (sa12k_integrand_integrable hη hf x) (sa12k_integrand_integrable hη hg x)]
  congr 1
  funext u
  rw [smul_sub]

/-- The error of the mollification: `‖(η * f)(x) - f(x)‖ ≤ E` when `f` varies by at most `E` on the ball. -/
theorem sa12k_moll_err (hη : SA12KMoll δ η) {f : Euc d → W} (hf : Continuous f) (x : Euc d)
    {E : ℝ} (hE : ∀ u : Euc d, ‖u‖ ≤ δ → ‖f (x - u) - f x‖ ≤ E) :
    ‖sa12k_moll η f x - f x‖ ≤ E := by
  have h1 : sa12k_moll η f x - f x = sa12k_moll η (fun y => f y - f x) x := by
    rw [sa12k_moll_sub hη hf continuous_const]
    unfold sa12k_moll
    rw [integral_smul_const, hη.integral_one, one_smul]
  rw [h1]
  exact sa12k_moll_norm_le_local hη (hf.sub continuous_const) x hE

/-- Mollification of a periodic function is periodic. -/
theorem sa12k_moll_periodic (η : Euc d → ℝ) (L : ℝ) {f : Euc d → W}
    (hf : ∀ (x : Euc d) (k : Fin d → ℤ), f (x + L • latticePt k) = f x) :
    ∀ (x : Euc d) (k : Fin d → ℤ), sa12k_moll η f (x + L • latticePt k) = sa12k_moll η f x := by
  intro x k
  unfold sa12k_moll
  congr 1
  funext u
  rw [add_sub_right_comm, hf]

theorem sa12k_moll_contDiff (hη : SA12KMoll δ η) {f : Euc d → W} (hf : Continuous f) :
    ContDiff ℝ ∞ (sa12k_moll η f) := by
  have h := HasCompactSupport.contDiff_convolution_left (𝕜 := ℝ) (μ := (volume : Measure (Euc d)))
    (ContinuousLinearMap.lsmul ℝ ℝ (E := W)) (n := ⊤) hη.compact
    (by simpa using hη.smooth) hf.locallyIntegrable
  have e : sa12k_moll η f = convolution η f (ContinuousLinearMap.lsmul ℝ ℝ) volume := by
    funext x
    simp [sa12k_moll, convolution_def]
  rw [e]
  exact h

/-- Differentiation under the mollification integral. -/
theorem sa12k_moll_hasFDerivAt (hη : SA12KMoll δ η) {f : Euc d → W} (hf : ContDiff ℝ 1 f) {B : ℝ}
    (hB : ∀ y, ‖fderiv ℝ f y‖ ≤ B) (x : Euc d) :
    HasFDerivAt (sa12k_moll η f) (sa12k_moll η (fderiv ℝ f) x) x := by
  have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hfc : Continuous (fderiv ℝ f) := hf.continuous_fderiv one_ne_zero
  have h := hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := (volume : Measure (Euc d)))
    (s := Metric.ball x 1) (x₀ := x)
    (F := fun (x : Euc d) (u : Euc d) => η u • f (x - u))
    (F' := fun (x : Euc d) (u : Euc d) => η u • fderiv ℝ f (x - u))
    (bound := fun u => |η u| * B) (Metric.ball_mem_nhds x one_pos)
    (Filter.Eventually.of_forall fun y =>
      (sa12k_integrand_integrable hη hf.continuous y).aestronglyMeasurable)
    (sa12k_integrand_integrable hη hf.continuous x)
    (sa12k_integrand_integrable hη hfc x).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u y _ => by
      show ‖η u • fderiv ℝ f (y - u)‖ ≤ |η u| * B
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hB _) (abs_nonneg _))
    (hη.integrable.abs.mul_const B)
    (Filter.Eventually.of_forall fun u y _ => by
      have h1 : HasFDerivAt (fun y : Euc d => f (y - u)) (fderiv ℝ f (y - u)) y := by
        have h2 := (hfd (y - u)).hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const u)
        exact h2
      exact h1.const_smul (η u))
  exact h

/-- The derivative of the mollification is the mollification of the derivative; all orders. -/
theorem sa12k_moll_iter (hη : SA12KMoll δ η) {f : Euc d → W} {n : ℕ} (hf : ContDiff ℝ n f) {B : ℝ}
    (hB : ∀ i ≤ n, ∀ y, ‖iteratedFDeriv ℝ i f y‖ ≤ B) :
    ∀ i ≤ n, iteratedFDeriv ℝ i (sa12k_moll η f) = sa12k_moll η (iteratedFDeriv ℝ i f) := by
  intro i
  induction i with
  | zero =>
    intro _
    funext x
    rw [iteratedFDeriv_zero_eq_comp]
    simp only [Function.comp_apply]
    unfold sa12k_moll
    have key : (continuousMultilinearCurryFin0 ℝ (Euc d) W).symm (∫ u, η u • f (x - u)) =
        ∫ u, (continuousMultilinearCurryFin0 ℝ (Euc d) W).symm (η u • f (x - u)) :=
      (ContinuousLinearEquiv.integral_comp_comm (μ := (volume : Measure (Euc d)))
        (continuousMultilinearCurryFin0 ℝ (Euc d) W).symm.toContinuousLinearEquiv
        (fun u => η u • f (x - u))).symm
    rw [key]
    congr 1
  | succ i ih =>
    intro hi
    have hi' : i ≤ n := by omega
    have hfi : ContDiff ℝ 1 (iteratedFDeriv ℝ i f) := by
      have := hf.iteratedFDeriv_right (i := i) (m := 1) (by exact_mod_cast (by omega : 1 + i ≤ n))
      simpa using this
    have hnorm : ∀ y, ‖fderiv ℝ (iteratedFDeriv ℝ i f) y‖ ≤ B := fun y => by
      rw [norm_fderiv_iteratedFDeriv]
      exact hB (i + 1) hi y
    funext x
    have e1 : ∀ g : Euc d → W, iteratedFDeriv ℝ (i + 1) g x =
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => Euc d) W).symm
          (fderiv ℝ (iteratedFDeriv ℝ i g) x) := fun g => by
      rw [iteratedFDeriv_succ_eq_comp_left]; rfl
    rw [e1, ih hi']
    have hd := (sa12k_moll_hasFDerivAt hη hfi hnorm x).fderiv
    rw [hd]
    unfold sa12k_moll
    have key : (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => Euc d) W).symm
        (∫ u, η u • fderiv ℝ (iteratedFDeriv ℝ i f) (x - u)) =
        ∫ u, (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => Euc d) W).symm
          (η u • fderiv ℝ (iteratedFDeriv ℝ i f) (x - u)) :=
      (ContinuousLinearEquiv.integral_comp_comm (𝕜 := ℝ) (μ := (volume : Measure (Euc d)))
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) => Euc d) W).symm.toContinuousLinearEquiv
        (fun u => η u • fderiv ℝ (iteratedFDeriv ℝ i f) (x - u))).symm
    rw [key]
    congr 1

end HRS.MH.AdjointRd.Phase2SA12Construction
