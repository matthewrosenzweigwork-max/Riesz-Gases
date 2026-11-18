import HRS.MS.SA16Y4Nc6
import HRS.MS.SA16Y4Tl2
import HRS.MS.SA16Y3S5c

/-!
# S.A.16 (SA16Y4) Lm3: convergence of the weak-identity integrands with only `C^0` convergence of the coefficients

`sa16y4_f_tendsto2`: `f_j(σ) = ν_j ℓ_χ(u_j) + ℓ_ψ(K_j u_j) → ν ℓ_χ(G) - ∫ wrep G · div(c ψ) - ℓ_ψ(Tμ G)` when `ν_j → ν`, the transport
coefficients `c_j → c` uniformly on the support ball of `ψ`, the nonlocal coefficients `a_j → μ` pointwise with a common decay bound,
`ι² u_j ⇀ G` boundedly and `K_j = B_{c_j} - T1_j ι` with `ι T1_j = T0_j ι`, `T0_j`, `Tμ` the nonlocal operators of `a_j`, `μ`.
This replaces `sa16y4_f_tendsto` (which needed `L^{p'}` convergence of the nonlocal test functions, i.e. derivatives of the coefficients).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Lm3
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

set_option maxHeartbeats 3200000 in
theorem sa16y4_f_tendsto2 {m : ℕ} (hm : 1 ≤ m) (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (M : Matrix (Fin d) (Fin d) ℝ) {W Bm R0 νlim : ℝ} (hW : 0 ≤ W) {Bj : ℕ → ℝ} (ν : ℕ → ℝ)
    (hν : Tendsto ν atTop (𝓝 νlim)) (bc : ℕ → Fin d → EuclideanSpace ℝ (Fin d) → ℝ)
    (hbo : ∀ j, SA16BddCoef (m + 1) (Bj j) (bc j)) (cl : Fin d → EuclideanSpace ℝ (Fin d) → ℝ)
    (hcl : ∀ k, ContDiff ℝ 1 (cl k)) {ψ χ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ) (hχ : IsCcInfty χ)
    (hψ0 : ∀ x, R0 < ‖x‖ → ψ x = 0)
    (huni : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ k x, ‖x‖ ≤ R0 → |bc j k x - cl k x| ≤ ε)
    (a : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (μ : EuclideanSpace ℝ (Fin d) → ℝ)
    (ha1 : ∀ j, ContDiff ℝ 1 (a j)) (hμ1 : ContDiff ℝ 1 μ)
    (haW : ∀ j x, |a j x| ≤ W * (1 + ‖x‖) ^ (-((d : ℝ) + 3))) (hμW : ∀ x, |μ x| ≤ W * (1 + ‖x‖) ^ (-((d : ℝ) + 3)))
    (hpt : ∀ x, Tendsto (fun j => a j x) atTop (𝓝 (μ x)))
    (T1 : ℕ → WmpSpace d (m + 1) p →L[ℝ] WmpSpace d (m + 1) p)
    (T0 : ℕ → WmpSpace d m p →L[ℝ] WmpSpace d m p) (hT0 : ∀ j, SA16SubOp d m p s M (a j) (T0 j))
    (hcomp : ∀ j, (sa16r_iota d m p).comp (T1 j) = (T0 j).comp (sa16r_iota d m p))
    (Tμ : WmpSpace d m p →L[ℝ] WmpSpace d m p) (hTμ : SA16SubOp d m p s M μ Tμ)
    (K : ℕ → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p)
    (hK : ∀ j, K j = sa16so_B d (m + 1) p (bc j) - (T1 j).comp (sa16r_iota d (m + 1) p))
    (u : ℕ → WmpSpace d (m + 1 + 1) p) (G : WmpSpace d m p)
    (hbd : ∀ j, ‖sa16sz_iota2 d m p (u j)‖ ≤ Bm)
    (hw : ∀ ℓ : StrongDual ℝ (WmpSpace d m p), Tendsto (fun j => ℓ (sa16sz_iota2 d m p (u j))) atTop (𝓝 (ℓ G))) :
    Tendsto (fun j => ν j * sa16r_ell d (m + 1 + 1) p hχ (u j) + sa16r_ell d (m + 1) p hψ (K j (u j))) atTop
      (𝓝 (νlim * sa16r_ell d m p hχ G - (∫ x, wrep d m p G x * sa16so_divFun cl ψ x) -
        sa16r_ell d m p hψ (Tμ G))) := by
  have hA : Tendsto (fun j => ν j * sa16r_ell d (m + 1 + 1) p hχ (u j)) atTop
      (𝓝 (νlim * sa16r_ell d m p hχ G)) := by
    simp_rw [← sa16y3_ell_iota2 hχ]
    exact hν.mul (hw (sa16r_ell d m p hχ))
  have hB := sa16y4_transport_limit (p := p) hm (R0 := R0) bc (fun j k => (hbo j).smooth k |>.of_le (by simp)) cl hcl hψ hψ0
    huni (fun j => sa16sz_iota2 d m p (u j)) G hbd hw
  have hC := sa16y4_nl_tendsto (p := p) hm hd hs0 hsd M hW a μ ha1 hμ1 haW hμW hpt hψ T0 hT0 Tμ hTμ
    (fun j => sa16sz_iota2 d m p (u j)) G hbd hw
  have hsum := hA.add ((hB.neg).sub hC)
  rw [show νlim * sa16r_ell d m p hχ G - (∫ x, wrep d m p G x * sa16so_divFun cl ψ x) - sa16r_ell d m p hψ (Tμ G) =
      νlim * sa16r_ell d m p hχ G + ((-∫ x, wrep d m p G x * sa16so_divFun cl ψ x) - sa16r_ell d m p hψ (Tμ G)) by ring]
  refine hsum.congr (fun j => ?_)
  rw [sa16y3_K_pair_eq (hbo j) hψ (T1 j) (T0 j) (hcomp j) (K j) (hK j) (u j)]

end Lm3

end HRS.Whole.AppendixA.Phase2SA16R
