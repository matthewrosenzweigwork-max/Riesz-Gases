import HRS.MS.SA16Y3L1
import HRS.MS.SA16Y3L3

/-!
# S.A.16 (SA16Y3) L5: equi-Lipschitz pairings of the truncated mild solutions (test-function-dependent constant)

`sa16y3_lip_trunc`: for the mild solution `u` of the truncated problem (`K_r = B_{b_r} - T1_r ι`) with
`‖ι² u r‖ ≤ Bm` on `[0,T]`, a test function `ψ` with `|div(b_r ψ)| ≤ cN` on `closedBall 0 R0` (zero outside) and `χ = Δψ`:
`|ℓ_ψ(u τ) − ℓ_ψ(u τ')| ≤ (ν ‖ℓ_χ‖ + cN vol(B_{R0})^{1/q} + ‖ℓ_ψ‖ CG) Bm |τ − τ'|`.
The constant involves no operator norm of `K_r`, `B'` or `sup |b_r|` away from `supp ψ`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section L5
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

set_option maxHeartbeats 1000000 in
theorem sa16y3_lip_trunc {m : ℕ} {ν T B' Bk CG cN R0 Bm : ℝ} (hν : 0 < ν) (hT : 0 < T) (hcN : 0 ≤ cN)
    (bc : ℝ → Fin d → Euc d → ℝ) (hbo : ∀ r ∈ Icc (0 : ℝ) T, SA16BddCoef (m + 1) B' (bc r))
    (T1 : ℝ → WmpSpace d (m + 1) p →L[ℝ] WmpSpace d (m + 1) p)
    (T0 : ℝ → WmpSpace d m p →L[ℝ] WmpSpace d m p)
    (hcomp : ∀ r ∈ Icc (0 : ℝ) T, (sa16r_iota d m p).comp (T1 r) = (T0 r).comp (sa16r_iota d m p))
    (hT0 : ∀ r ∈ Icc (0 : ℝ) T, ‖T0 r‖ ≤ CG)
    (K : ℝ → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p)
    (hK : ∀ r, K r = sa16so_B d (m + 1) p (bc r) - (T1 r).comp (sa16r_iota d (m + 1) p))
    (hKb : ∀ r ∈ Icc (0 : ℝ) T, ‖K r‖ ≤ Bk)
    (hKc : ∀ x, ContinuousOn (fun r => K r x) (Icc 0 T)) (φ : WmpSpace d (m + 1 + 1) p)
    {ψ χ : Euc d → ℝ} (hψ : IsCcInfty ψ) (hχ : IsCcInfty χ) (hHW : SA16RHeatWeak d (m + 1) p ν T hψ hχ)
    (hNb : ∀ r ∈ Icc (0 : ℝ) T, ∀ x, |sa16so_divFun (bc r) ψ x| ≤
      cN * (closedBall (0 : Euc d) R0).indicator (fun _ => (1 : ℝ)) x)
    {u : ℝ → WmpSpace d (m + 1 + 1) p} (hu : ContinuousOn u (Icc 0 T))
    (hsol : ∀ τ ∈ Icc (0 : ℝ) T, u τ = sa16r_f0 d (m + 1) p ν φ τ +
      voltOp (gainKer (sa16r_GamT d (m + 1) p ν) K) u τ)
    (hbd : ∀ r ∈ Icc (0 : ℝ) T, ‖sa16sz_iota2 d m p (u r)‖ ≤ Bm) :
    ∀ τ ∈ Icc (0 : ℝ) T, ∀ τ' ∈ Icc (0 : ℝ) T,
      |sa16r_ell d (m + 1 + 1) p hψ (u τ) - sa16r_ell d (m + 1 + 1) p hψ (u τ')| ≤
        (ν * ‖sa16r_ell d m p hχ‖ + cN * (volume (closedBall (0 : Euc d) R0)).toReal ^ (1 / Real.conjExponent p) +
          ‖sa16r_ell d m p hψ‖ * CG) * Bm * |τ - τ'| := by
  have hBm : ∀ r ∈ Icc (0 : ℝ) T, 0 ≤ Bm := fun r hr => (norm_nonneg _).trans (hbd r hr)
  have hBm0 : 0 ≤ Bm := hBm 0 ⟨le_rfl, hT.le⟩
  have h := sa16y3_lip_pairD (k := m + 1) (ν := ν) (T := T) (B := Bk) (BK := Bk)
    (Lψ := (cN * (volume (closedBall (0 : Euc d) R0)).toReal ^ (1 / Real.conjExponent p) +
      ‖sa16r_ell d m p hψ‖ * CG) * Bm) (Lχ := ‖sa16r_ell d m p hχ‖ * Bm) hν hT
    ((ContinuousLinearMap.opNorm_nonneg _).trans (hKb 0 ⟨le_rfl, hT.le⟩)) K hKb hKc φ hψ hχ hHW hu hsol
    (fun r hr => by
      rw [← sa16y3_ell_iota2 hχ, ← Real.norm_eq_abs]
      exact ((sa16r_ell d m p hχ).le_opNorm _).trans (mul_le_mul_of_nonneg_left (hbd r hr) (ContinuousLinearMap.opNorm_nonneg _)))
    (fun r hr => by
      have := sa16y3_K_pair_bound (hbo r hr) hψ (hNb r hr) hcN (T1 r) (T0 r) (hcomp r hr) (hT0 r hr) (K r)
        (hK r) (u r)
      exact this.trans (mul_le_mul_of_nonneg_left (hbd r hr)
        (add_nonneg (mul_nonneg hcN (Real.rpow_nonneg ENNReal.toReal_nonneg _))
          (mul_nonneg (ContinuousLinearMap.opNorm_nonneg _) ((ContinuousLinearMap.opNorm_nonneg (T0 0)).trans (hT0 0 ⟨le_rfl, hT.le⟩))))))
  intro τ hτ τ' hτ'
  refine (h τ hτ τ' hτ').trans (le_of_eq ?_)
  ring

end L5

end HRS.Whole.AppendixA.Phase2SA16R
