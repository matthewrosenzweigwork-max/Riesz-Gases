import HRS.MS.SA16ZT1

/-!
# S.A.16 (SA16Z) T2: `∂_i (g ⋆ f) = -c_s · pvOdd f` for `f ∈ C_c^∞` (the first Riesz force as a principal value)

Setting `0 ≤ s < d`, `θ = s + 2 - d > 0`, `g = rieszKernel d s`, `c_s = hlsg_c s`.  Smooth radial cutoffs
`χ_ε` and integration by parts against `F = f(x - ·)`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution RealInnerProductSpace

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section T2
variable {d : ℕ} {s : ℝ}

/-- the explicit odd kernel `∂_i g(z) = -c_s z_i |z|^{-s-2}` -/
def sa16z_Kx (s : ℝ) (i : Fin d) (z : Euc d) : ℝ := -(HRS.CZ.Hls.hlsg_c s * ‖z‖ ^ (-s - 2) * z i)

lemma sa16z_Kx_neg (s : ℝ) (i : Fin d) (z : Euc d) : sa16z_Kx s i (-z) = -sa16z_Kx s i z := by
  simp [sa16z_Kx, norm_neg]

lemma sa16z_Kx_eq (s : ℝ) (i : Fin d) {z : Euc d} (hz : z ≠ 0) :
    fderiv ℝ (rieszKernel d s) z (sa16z_e i) = sa16z_Kx s i z := by
  rw [HRS.CZ.Hls.force_kernel_formula s hz]
  simp [sa16z_Kx, sa16z_e, EuclideanSpace.inner_single_right]

lemma sa16z_Kx_meas (s : ℝ) (i : Fin d) : Measurable (sa16z_Kx s i) := by
  unfold sa16z_Kx
  exact (((measurable_norm.pow_const _).const_mul _).mul
    (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable).neg

lemma sa16z_Kx_bound (hs0 : 0 ≤ s) (i : Fin d) {z : Euc d} (hz : z ≠ 0) :
    |sa16z_Kx s i z| ≤ HRS.CZ.Hls.hlsg_c s * ‖z‖ ^ (-s - 1) := by
  have h : |fderiv ℝ (rieszKernel d s) z (sa16z_e i)| ≤ HRS.CZ.Hls.hlsg_c s * ‖z‖ ^ (-s - 1) :=
    HRS.CZ.Hls.force_kernel_bound_coord hs0 hz i
  rwa [sa16z_Kx_eq s i hz] at h

lemma sa16z_Kx_bound_far (hs0 : 0 ≤ s) (i : Fin d) {ε : ℝ} (hε : 0 < ε) {z : Euc d} (hz : ε ≤ ‖z‖) :
    |sa16z_Kx s i z| ≤ HRS.CZ.Hls.hlsg_c s * ε ^ (-s - 1) := by
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz; linarith
  refine (sa16z_Kx_bound hs0 i hz0).trans ?_
  have hc := HRS.CZ.Hls.hlsg_c_nonneg hs0
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hε hz (by linarith)) hc

lemma sa16z_F_cc {f : Euc d → ℝ} (hf : IsCcInfty f) (x : Euc d) : IsCcInfty (fun z => f (x - z)) :=
  ⟨hf.1.comp (contDiff_const.sub contDiff_id), hf.2.comp_homeomorph (Homeomorph.subLeft x)⟩

lemma sa16z_F_fderiv {f : Euc d → ℝ} (hf : IsCcInfty f) (x z v : Euc d) :
    fderiv ℝ (fun z => f (x - z)) z v = -fderiv ℝ f (x - z) v := by
  have hd : DifferentiableAt ℝ f (x - z) := hf.1.differentiable (by simp) _
  have h := hd.hasFDerivAt.comp z ((hasFDerivAt_id z).const_sub x)
  rw [show (fun z => f (x - z)) = f ∘ fun z => x - z from rfl, h.fderiv]
  simp

lemma sa16z_g_mul_int {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {w : Euc d → ℝ} (hw : Continuous w)
    (hws : HasCompactSupport w) : Integrable (fun z => rieszKernel d s z * w z) := by
  have := (rieszKernel_locallyIntegrable (d := d) hs0 hsd).integrable_smul_left_of_hasCompactSupport hw hws
  simpa [smul_eq_mul, mul_comm] using this

end T2

end HRS.Whole.AppendixA.Phase2SA16R
