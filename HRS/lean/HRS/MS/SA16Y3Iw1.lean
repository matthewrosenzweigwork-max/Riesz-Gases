import HRS.MS.SA16Y3Hk1
import HRS.MS.SA16Y3Sk3
import HRS.MS.SA16ZP1

/-!
# S.A.16 (SA16Y3) Iw1: the weak (duality) identity of the iso nonlocal operator on `C_c^∞` (packet P7/P8, iso case)

`sa16z_P s μ φ = ∑_i Q^i (μ ∂_i φ)` with `Q^i = ∂_i (g ⋆ ·)`.
`sa16y3_ibp_dir`: one-direction integration by parts for `C_c^∞` against smooth functions.
`sa16y3_iso_dual`: `∫ (P_μ φ) ψ = ∫ φ · ∑_i ∂_i (μ Q^i ψ)` for `φ, ψ ∈ C_c^∞`, `μ` smooth (`0 ≤ s < d`, `1 ≤ d`).
The proof uses the skew-adjointness `sa16y3_Q_skew` (Hk1) and the 1-D integration by parts.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Iw1
variable {d : ℕ} {s : ℝ}

/-- dual side of the iso weak identity: `∑_i ∂_i (μ · Q^i ψ)` -/
def sa16y3_dualIW (s : ℝ) (μ ψ : Euc d → ℝ) (x : Euc d) : ℝ :=
  ∑ i : Fin d, fderiv ℝ (fun y => μ y * sa16y3_Q s i ψ y) x (sa16z_e i)

lemma sa16y3_ibp_dir {i : Fin d} {φ F : Euc d → ℝ} (hφ : IsCcInfty φ) (hF : ContDiff ℝ ∞ F) :
    ∫ x, fderiv ℝ φ x (sa16z_e i) * F x = -∫ x, φ x * fderiv ℝ F x (sa16z_e i) := by
  have hFc : Continuous (fun x => fderiv ℝ F x (sa16z_e i)) :=
    (hF.continuous_fderiv (by simp)).clm_apply continuous_const
  have hD : HasCompactSupport (fun x => fderiv ℝ φ x (sa16z_e i)) :=
    (hφ.2.fderiv ℝ).comp_left (g := fun L : Euc d →L[ℝ] ℝ => L (sa16z_e i)) (by simp)
  have I1 : Integrable (fun x => fderiv ℝ F x (sa16z_e i) * φ x) :=
    (hFc.mul hφ.1.continuous).integrable_of_hasCompactSupport hφ.2.mul_left
  have I2 : Integrable (fun x => F x * fderiv ℝ φ x (sa16z_e i)) :=
    (hF.continuous.mul ((hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport
      hD.mul_left
  have I3 : Integrable (fun x => F x * φ x) :=
    (hF.continuous.mul hφ.1.continuous).integrable_of_hasCompactSupport hφ.2.mul_left
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure (Euc d)))
    (f := F) (g := φ) (v := sa16z_e i) I1 I2 I3 (fun x _ => (hF.differentiable (by simp)) x)
    (fun x _ => (hφ.1.differentiable (by simp)) x)
  have e1 : (fun x => fderiv ℝ φ x (sa16z_e i) * F x) = fun x => F x * fderiv ℝ φ x (sa16z_e i) :=
    funext fun x => mul_comm _ _
  have e2 : (fun x => φ x * fderiv ℝ F x (sa16z_e i)) = fun x => fderiv ℝ F x (sa16z_e i) * φ x :=
    funext fun x => mul_comm _ _
  rw [e1, e2]
  exact key

theorem sa16y3_iso_dual (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {μ φ ψ : Euc d → ℝ}
    (hμ : ContDiff ℝ ∞ μ) (hφ : IsCcInfty φ) (hψ : IsCcInfty ψ) :
    ∫ x, sa16z_P s μ φ x * ψ x = ∫ x, φ x * sa16y3_dualIW s μ ψ x := by
  have hF : ∀ i : Fin d, ContDiff ℝ ∞ (fun y => μ y * sa16y3_Q s i ψ y) :=
    fun i => hμ.mul (sa16y3_Q_smooth hs0 hsd hψ i)
  have hQ : ∀ i : Fin d, IsCcInfty (sa16z_src μ φ i) := fun i => sa16z_src_cc hμ hφ i
  -- per-direction identity
  have hi : ∀ i : Fin d, ∫ x, sa16y3_Q s i (sa16z_src μ φ i) x * ψ x =
      ∫ x, φ x * fderiv ℝ (fun y => μ y * sa16y3_Q s i ψ y) x (sa16z_e i) := by
    intro i
    have h1 := sa16y3_Q_skew hd hs0 hsd (hQ i) hψ i
    have h2 : ∫ x, sa16z_src μ φ i x * sa16y3_Q s i ψ x =
        ∫ x, fderiv ℝ φ x (sa16z_e i) * (μ x * sa16y3_Q s i ψ x) := by
      congr 1; funext x; simp only [sa16z_src]; ring
    have h3 : ∫ x, fderiv ℝ φ x (sa16z_e i) * (μ x * sa16y3_Q s i ψ x) =
        -∫ x, φ x * fderiv ℝ (fun y => μ y * sa16y3_Q s i ψ y) x (sa16z_e i) :=
      sa16y3_ibp_dir hφ (hF i)
    linarith [h1, h2, h3]
  have hintL : ∀ i : Fin d, Integrable (fun x => sa16y3_Q s i (sa16z_src μ φ i) x * ψ x) := fun i =>
    ((sa16y3_Q_smooth hs0 hsd (hQ i) i).continuous.mul hψ.1.continuous).integrable_of_hasCompactSupport
      hψ.2.mul_left
  have hintR : ∀ i : Fin d, Integrable (fun x =>
      φ x * fderiv ℝ (fun y => μ y * sa16y3_Q s i ψ y) x (sa16z_e i)) := fun i =>
    (hφ.1.continuous.mul (((hF i).continuous_fderiv (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport
      hφ.2.mul_right
  have hPs : (fun x => sa16z_P s μ φ x * ψ x) =
      fun x => ∑ i : Fin d, sa16y3_Q s i (sa16z_src μ φ i) x * ψ x :=
    funext fun x => by rw [← Finset.sum_mul]; rfl
  rw [hPs]
  calc ∫ x, ∑ i : Fin d, sa16y3_Q s i (sa16z_src μ φ i) x * ψ x
      = ∑ i : Fin d, ∫ x, sa16y3_Q s i (sa16z_src μ φ i) x * ψ x :=
        integral_finsetSum _ (fun i _ => hintL i)
    _ = ∑ i : Fin d, ∫ x, φ x * fderiv ℝ (fun y => μ y * sa16y3_Q s i ψ y) x (sa16z_e i) :=
        Finset.sum_congr rfl fun i _ => hi i
    _ = ∫ x, ∑ i : Fin d, φ x * fderiv ℝ (fun y => μ y * sa16y3_Q s i ψ y) x (sa16z_e i) :=
        (integral_finsetSum _ (fun i _ => hintR i)).symm
    _ = ∫ x, φ x * sa16y3_dualIW s μ ψ x := by
        congr 1; funext x; simp only [sa16y3_dualIW, Finset.mul_sum]

end Iw1

end HRS.Whole.AppendixA.Phase2SA16R
