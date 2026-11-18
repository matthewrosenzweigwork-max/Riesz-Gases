import HRS.MS.SA16SEn2
import HRS.MS.LpDissConvex

/-!
# S.A.16 (SA16S) En3: regularized vector calculus (packet P7, step 4)

For `W = (W_a)_{a ∈ ι}` of class `C_c^∞` and `η > 0`: `s_η = ∑ W_a² + η²`, `θ_η = s_η^{p/2} - η^p`.
* `sa16sy_diff_eta`: `∑_a ∫ s_η^{p/2-1} W_a ∂_e∂_e W_a ≤ 0`  (`p ≥ 2`);
* `sa16sy_transport_eta`: `∑_a ∫ s_η^{p/2-1} W_a (c ∂_e W_a) = -(1/p) ∫ (∂_e c) θ_η`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section En3
variable {d : ℕ} {ι : Type*} [Fintype ι]

/-- the regularized squared length -/
def sa16sy_s (W : ι → Euc d → ℝ) (η : ℝ) (x : Euc d) : ℝ := ∑ a, W a x ^ 2 + η ^ 2

lemma sa16sy_s_pos (W : ι → Euc d → ℝ) {η : ℝ} (hη : 0 < η) (x : Euc d) : 0 < sa16sy_s W η x := by
  unfold sa16sy_s
  have : 0 ≤ ∑ a, W a x ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  positivity

lemma sa16sy_s_smooth {W : ι → Euc d → ℝ} (hW : ∀ a, IsCcInfty (W a)) (η : ℝ) :
    ContDiff ℝ ∞ (sa16sy_s W η) := by
  unfold sa16sy_s
  exact (ContDiff.sum fun a _ => (hW a).1.pow 2).add contDiff_const

/-- directional derivative of `s_η`: `∂_e s = 2 ∑ W_a ∂_e W_a` -/
lemma sa16sy_s_hasFDerivAt {W : ι → Euc d → ℝ} (hW : ∀ a, IsCcInfty (W a)) (η : ℝ) (x : Euc d) :
    HasFDerivAt (sa16sy_s W η) (∑ a, (2 * W a x) • fderiv ℝ (W a) x) x := by
  unfold sa16sy_s
  have h : ∀ a ∈ (Finset.univ : Finset ι), HasFDerivAt (fun y => W a y ^ 2)
      ((2 * W a x) • fderiv ℝ (W a) x) x := by
    intro a _
    have := ((hW a).1.differentiable (by simp) x).hasFDerivAt.pow 2
    simpa [pow_one, mul_comm] using this
  exact (HasFDerivAt.fun_sum h).add_const (η ^ 2)

lemma sa16sy_s_fderiv {W : ι → Euc d → ℝ} (hW : ∀ a, IsCcInfty (W a)) (η : ℝ) (x e : Euc d) :
    fderiv ℝ (sa16sy_s W η) x e = 2 * ∑ a, W a x * fderiv ℝ (W a) x e := by
  rw [(sa16sy_s_hasFDerivAt hW η x).fderiv]
  simp [Finset.sum_apply, Finset.mul_sum, mul_assoc]

lemma sa16sy_rpow_smooth {W : ι → Euc d → ℝ} (hW : ∀ a, IsCcInfty (W a)) {η : ℝ} (hη : 0 < η) (r : ℝ) :
    ContDiff ℝ ∞ (fun x => sa16sy_s W η x ^ r) :=
  (sa16sy_s_smooth hW η).rpow_const_of_ne (fun x => (sa16sy_s_pos W hη x).ne')

lemma sa16sy_rpow_fderiv {W : ι → Euc d → ℝ} (hW : ∀ a, IsCcInfty (W a)) {η : ℝ} (hη : 0 < η) (r : ℝ)
    (x e : Euc d) :
    fderiv ℝ (fun y => sa16sy_s W η y ^ r) x e =
      r * sa16sy_s W η x ^ (r - 1) * (2 * ∑ a, W a x * fderiv ℝ (W a) x e) := by
  have h1 := (sa16sy_s_hasFDerivAt hW η x)
  have h2 := (Real.hasDerivAt_rpow_const (Or.inl (sa16sy_s_pos W hη x).ne') : HasDerivAt (fun t : ℝ => t ^ r)
    (r * sa16sy_s W η x ^ (r - 1)) (sa16sy_s W η x)).comp_hasFDerivAt x h1
  have h3 : HasFDerivAt (fun y => sa16sy_s W η y ^ r)
      ((r * sa16sy_s W η x ^ (r - 1)) • ∑ a, (2 * W a x) • fderiv ℝ (W a) x) x := h2
  rw [h3.fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, ContinuousLinearMap.sum_apply]
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

end En3

end HRS.Whole.AppendixA.Phase2SA16R
