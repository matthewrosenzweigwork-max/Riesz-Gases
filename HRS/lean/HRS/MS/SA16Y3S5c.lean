import HRS.MS.SA16Y3S5b
import HRS.MS.SA16Y3L3

/-!
# S.A.16 (SA16Y3) S5c: pointwise-in-time convergence of the integrand of the weak identity

`sa16y3_K_pair_eq`: `ℓ_ψ(K y) = -∫ wrep(ι² y) div(bψ) - ℓ_ψ(T0 ι² y)` for `K = B_b - T1 ι`, `T0 ι = ι T1`.
`sa16y3_f_tendsto`: along a sequence of data (truncated drifts `b_j` with `div(b_j ψ) → Dn` uniformly with common support ball,
solutions `u_j` with `ι² u_j` bounded and weakly convergent to `G`, a common nonlocal operator pair `T1, T0`) the integrands
`ν ℓ_χ(u_j) + ℓ_ψ(K_j u_j)` of the weak identity converge to `ν ℓ_χ(G) - ∫ wrep G · Dn - ℓ_ψ(T0 G)`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section S5c
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

set_option maxHeartbeats 1000000 in
theorem sa16y3_K_pair_eq {m : ℕ} {B' : ℝ} {bc : Fin d → Euc d → ℝ}
    (hbo : SA16BddCoef (m + 1) B' bc) {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ)
    (T1 : WmpSpace d (m + 1) p →L[ℝ] WmpSpace d (m + 1) p)
    (T0 : WmpSpace d m p →L[ℝ] WmpSpace d m p)
    (hcomp : (sa16r_iota d m p).comp T1 = T0.comp (sa16r_iota d m p))
    (K : WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p)
    (hK : K = sa16so_B d (m + 1) p bc - T1.comp (sa16r_iota d (m + 1) p)) (y : WmpSpace d (m + 1 + 1) p) :
    sa16r_ell d (m + 1) p hψ (K y) =
      -(∫ x, wrep d m p (sa16sz_iota2 d m p y) x * sa16so_divFun bc ψ x) -
        sa16r_ell d m p hψ (T0 (sa16sz_iota2 d m p y)) := by
  have h1 : sa16r_ell d (m + 1) p hψ (K y) =
      -sa16r_ell d (m + 1 + 1) p (sa16so_cc_div hbo hψ) y -
        sa16r_ell d m p hψ (T0 (sa16sz_iota2 d m p y)) := by
    rw [hK, sub_apply, map_sub, sa16so_ell_B hbo hψ y]
    congr 1
    rw [ContinuousLinearMap.comp_apply, ← sa16r_ell_iota hψ m]
    have h1 := congrArg (fun L => L (sa16r_iota d (m + 1) p y)) hcomp
    simp only [ContinuousLinearMap.comp_apply] at h1
    rw [h1]; rfl
  rw [h1, ← sa16y3_ell_iota2 (sa16so_cc_div hbo hψ), sa16r_ell_apply]

theorem sa16y3_f_tendsto {m : ℕ} {ν Bm R0 : ℝ} {Bj : ℕ → ℝ} (bc : ℕ → Fin d → Euc d → ℝ)
    (hbo : ∀ j, SA16BddCoef (m + 1) (Bj j) (bc j)) {ψ χ : Euc d → ℝ} (hψ : IsCcInfty ψ) (hχ : IsCcInfty χ)
    (T1 : WmpSpace d (m + 1) p →L[ℝ] WmpSpace d (m + 1) p)
    (T0 : WmpSpace d m p →L[ℝ] WmpSpace d m p)
    (hcomp : (sa16r_iota d m p).comp T1 = T0.comp (sa16r_iota d m p))
    (K : ℕ → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p)
    (hK : ∀ j, K j = sa16so_B d (m + 1) p (bc j) - T1.comp (sa16r_iota d (m + 1) p))
    (u : ℕ → WmpSpace d (m + 1 + 1) p) (G : WmpSpace d m p)
    (hbd : ∀ j, ‖sa16sz_iota2 d m p (u j)‖ ≤ Bm)
    (hw : ∀ ℓ : StrongDual ℝ (WmpSpace d m p), Tendsto (fun j => ℓ (sa16sz_iota2 d m p (u j))) atTop (𝓝 (ℓ G)))
    (Dn : Euc d → ℝ) (hDc : Continuous Dn) (hD0 : ∀ x, R0 < ‖x‖ → Dn x = 0)
    (hD0j : ∀ j x, R0 < ‖x‖ → sa16so_divFun (bc j) ψ x = 0)
    (huni : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ x, |sa16so_divFun (bc j) ψ x - Dn x| ≤ ε) :
    Tendsto (fun j => ν * sa16r_ell d (m + 1 + 1) p hχ (u j) + sa16r_ell d (m + 1) p hψ (K j (u j))) atTop
      (𝓝 (ν * sa16r_ell d m p hχ G - (∫ x, wrep d m p G x * Dn x) - sa16r_ell d m p hψ (T0 G))) := by
  have hDj : ∀ j, Continuous (sa16so_divFun (bc j) ψ) := fun j => (sa16so_cc_div (hbo j) hψ).1.continuous
  have hA : Tendsto (fun j => ν * sa16r_ell d (m + 1 + 1) p hχ (u j)) atTop
      (𝓝 (ν * sa16r_ell d m p hχ G)) := by
    simp_rw [← sa16y3_ell_iota2 hχ]
    exact (hw (sa16r_ell d m p hχ)).const_mul ν
  have hB := sa16y3_pair_tendsto (p := p) (fun j => sa16sz_iota2 d m p (u j)) G hbd hw
    (fun j => sa16so_divFun (bc j) ψ) Dn hDj hDc hD0j hD0 huni
  have hC := hw ((sa16r_ell d m p hψ).comp T0)
  have hsum := hA.add ((hB.neg).sub hC)
  rw [show ν * sa16r_ell d m p hχ G - (∫ x, wrep d m p G x * Dn x) - sa16r_ell d m p hψ (T0 G) =
      ν * sa16r_ell d m p hχ G + ((-∫ x, wrep d m p G x * Dn x) - (sa16r_ell d m p hψ).comp T0 G) by
    simp only [ContinuousLinearMap.comp_apply]; ring]
  refine hsum.congr (fun j => ?_)
  rw [sa16y3_K_pair_eq (hbo j) hψ T1 T0 hcomp (K j) (hK j) (u j)]
  simp [sub_eq_add_neg]

end S5c

end HRS.Whole.AppendixA.Phase2SA16R
