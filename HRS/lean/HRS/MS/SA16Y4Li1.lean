import HRS.MS.SA16Y3L5
import HRS.MS.SA16SHw4

/-!
# S.A.16 (SA16Y4) Li1: the weak identity of the truncated mild solution, with continuous bounded integrand

`sa16y4_weak_integrand`: for the mild solution `u` (hypotheses of `sa16y3_lip_trunc`), `ψ ∈ C_c^∞` and `χ = Δψ`
(`sa16sw_heatWeak`), the function `f σ = ν ℓ_χ(u σ) + ℓ_ψ(K σ (u σ))` is continuous on `[0,T]`, bounded by
`(ν‖ℓ_χ^{(m)}‖ + cN vol^{1/q} + ‖ℓ_ψ^{(m)}‖ CG) Bm` and `ℓ_ψ(u τ) = ℓ_ψ(φ) + ∫_0^τ f` (all `τ ∈ [0,T]`).
These are exactly the hypotheses `hfc, hfb, hid` of `sa16y3_limit_identity`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Li1
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

set_option maxHeartbeats 1600000 in
theorem sa16y4_weak_integrand {m : ℕ} {ν T B' Bk CG cN R0 Bm : ℝ} (hν : 0 < ν) (hT : 0 < T) (hcN : 0 ≤ cN)
    (bc : ℝ → Fin d → Euc d → ℝ) (hbo : ∀ r ∈ Icc (0 : ℝ) T, SA16BddCoef (m + 1) B' (bc r))
    (T1 : ℝ → WmpSpace d (m + 1) p →L[ℝ] WmpSpace d (m + 1) p)
    (T0 : ℝ → WmpSpace d m p →L[ℝ] WmpSpace d m p)
    (hcomp : ∀ r ∈ Icc (0 : ℝ) T, (sa16r_iota d m p).comp (T1 r) = (T0 r).comp (sa16r_iota d m p))
    (hT0 : ∀ r ∈ Icc (0 : ℝ) T, ‖T0 r‖ ≤ CG)
    (K : ℝ → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p)
    (hK : ∀ r, K r = sa16so_B d (m + 1) p (bc r) - (T1 r).comp (sa16r_iota d (m + 1) p))
    (hKb : ∀ r ∈ Icc (0 : ℝ) T, ‖K r‖ ≤ Bk)
    (hKc : ∀ x, ContinuousOn (fun r => K r x) (Icc 0 T)) (φ : WmpSpace d (m + 1 + 1) p)
    {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ)
    (hNb : ∀ r ∈ Icc (0 : ℝ) T, ∀ x, |sa16so_divFun (bc r) ψ x| ≤
      cN * (closedBall (0 : Euc d) R0).indicator (fun _ => (1 : ℝ)) x)
    {u : ℝ → WmpSpace d (m + 1 + 1) p} (hu : ContinuousOn u (Icc 0 T))
    (hsol : ∀ τ ∈ Icc (0 : ℝ) T, u τ = sa16r_f0 d (m + 1) p ν φ τ +
      voltOp (gainKer (sa16r_GamT d (m + 1) p ν) K) u τ)
    (hbd : ∀ r ∈ Icc (0 : ℝ) T, ‖sa16sz_iota2 d m p (u r)‖ ≤ Bm) :
    let f : ℝ → ℝ := fun σ => ν * sa16r_ell d (m + 1 + 1) p (sa16sw_cc_lap hψ) (u σ) +
      sa16r_ell d (m + 1) p hψ (K σ (u σ))
    (∀ τ ∈ Icc (0 : ℝ) T, sa16r_ell d (m + 1 + 1) p hψ (u τ) =
        sa16r_ell d (m + 1 + 1) p hψ φ + ∫ σ in (0 : ℝ)..τ, f σ) ∧
      ContinuousOn f (Icc 0 T) ∧
      ∀ σ ∈ Icc (0 : ℝ) T, |f σ| ≤ (ν * ‖sa16r_ell d m p (sa16sw_cc_lap hψ)‖ +
        cN * (volume (closedBall (0 : Euc d) R0)).toReal ^ (1 / Real.conjExponent p) +
          ‖sa16r_ell d m p hψ‖ * CG) * Bm := by
  intro f
  have hBK0 : 0 ≤ Bk := (ContinuousLinearMap.opNorm_nonneg _).trans (hKb 0 ⟨le_rfl, hT.le⟩)
  have hid := sa16r_fixedn_weak (B := Bk) hν hT hBK0 (m + 1) K hKb hKc φ hψ (sa16sw_cc_lap hψ)
    (sa16sw_heatWeak hν T (m + 1) hψ) hu hsol
  have hcont : ContinuousOn f (Icc 0 T) := by
    refine ContinuousOn.add ?_ ?_
    · exact continuousOn_const.mul ((sa16r_ell d (m + 1 + 1) p (sa16sw_cc_lap hψ)).continuous.comp_continuousOn hu)
    · exact (sa16r_ell d (m + 1) p hψ).continuous.comp_continuousOn (sa16y3_K_continuousOn K hKb hKc hu)
  have hCG0 : 0 ≤ CG := (ContinuousLinearMap.opNorm_nonneg _).trans (hT0 0 ⟨le_rfl, hT.le⟩)
  refine ⟨fun τ hτ => hid τ hτ, hcont, fun σ hσ => ?_⟩
  have h1 : |sa16r_ell d (m + 1 + 1) p (sa16sw_cc_lap hψ) (u σ)| ≤ ‖sa16r_ell d m p (sa16sw_cc_lap hψ)‖ * Bm := by
    rw [← sa16y3_ell_iota2 (sa16sw_cc_lap hψ), ← Real.norm_eq_abs]
    exact ((sa16r_ell d m p _).le_opNorm _).trans
      (mul_le_mul_of_nonneg_left (hbd σ hσ) (ContinuousLinearMap.opNorm_nonneg _))
  have h2 := sa16y3_K_pair_bound (hbo σ hσ) hψ (hNb σ hσ) hcN (T1 σ) (T0 σ) (hcomp σ hσ) (hT0 σ hσ) (K σ)
    (hK σ) (u σ)
  have h3 : |sa16r_ell d (m + 1) p hψ (K σ (u σ))| ≤
      (cN * (volume (closedBall (0 : Euc d) R0)).toReal ^ (1 / Real.conjExponent p) +
        ‖sa16r_ell d m p hψ‖ * CG) * Bm :=
    h2.trans (mul_le_mul_of_nonneg_left (hbd σ hσ)
      (add_nonneg (mul_nonneg hcN (Real.rpow_nonneg ENNReal.toReal_nonneg _))
        (mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) hCG0)))
  calc |f σ| ≤ |ν * sa16r_ell d (m + 1 + 1) p (sa16sw_cc_lap hψ) (u σ)| +
        |sa16r_ell d (m + 1) p hψ (K σ (u σ))| := abs_add_le _ _
    _ ≤ ν * (‖sa16r_ell d m p (sa16sw_cc_lap hψ)‖ * Bm) + (cN * (volume (closedBall (0 : Euc d) R0)).toReal ^
        (1 / Real.conjExponent p) + ‖sa16r_ell d m p hψ‖ * CG) * Bm := by
        refine add_le_add ?_ h3
        rw [abs_mul, abs_of_pos hν]
        exact mul_le_mul_of_nonneg_left h1 hν.le
    _ = _ := by ring

end Li1

end HRS.Whole.AppendixA.Phase2SA16R
