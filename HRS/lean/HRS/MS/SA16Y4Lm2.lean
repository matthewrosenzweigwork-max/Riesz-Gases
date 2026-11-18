import HRS.MS.SA16Y4Lm1
import HRS.MS.SA16Y3S5c
import HRS.MS.SA16Y4S5d

/-!
# S.A.16 (SA16Y4) Lm2: pointwise-in-time convergence of the integrands (varying viscosity and varying nonlocal term)

`sa16y4_f_tendsto`: `f_j(σ) = ν_j ℓ_χ(u_j) + ℓ_ψ(K_j u_j)` converges to `ν ℓ_χ(G) - ∫ wrep G · Dn - ∫ wrep G · NL` provided
`ν_j → ν`, `ι² u_j` bounded and weakly convergent to `G`, `div(b_j ψ) → Dn` uniformly with a common support ball
(`sa16y4_divFun_tendsto`), and the nonlocal test functions `NL_j` of `T0_j` (`ℓ_ψ(T0_j y) = ∫ wrep y · NL_j`) converge to `NL` in
`L^{p'}` (the convergence `nonlocalTestRd(ρ_n ⋆ μ) ψ → nonlocalTestRd(μ) ψ`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Lm2
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

set_option maxHeartbeats 1600000 in
theorem sa16y4_f_tendsto {m : ℕ} {Bm R0 νlim : ℝ} {Bj : ℕ → ℝ} (ν : ℕ → ℝ) (hν : Tendsto ν atTop (𝓝 νlim))
    (bc : ℕ → Fin d → EuclideanSpace ℝ (Fin d) → ℝ) (hbo : ∀ j, SA16BddCoef (m + 1) (Bj j) (bc j))
    {ψ χ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ) (hχ : IsCcInfty χ)
    (T1 : ℕ → WmpSpace d (m + 1) p →L[ℝ] WmpSpace d (m + 1) p)
    (T0 : ℕ → WmpSpace d m p →L[ℝ] WmpSpace d m p)
    (hcomp : ∀ j, (sa16r_iota d m p).comp (T1 j) = (T0 j).comp (sa16r_iota d m p))
    (K : ℕ → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p)
    (hK : ∀ j, K j = sa16so_B d (m + 1) p (bc j) - (T1 j).comp (sa16r_iota d (m + 1) p))
    (u : ℕ → WmpSpace d (m + 1 + 1) p) (G : WmpSpace d m p)
    (hbd : ∀ j, ‖sa16sz_iota2 d m p (u j)‖ ≤ Bm)
    (hw : ∀ ℓ : StrongDual ℝ (WmpSpace d m p), Tendsto (fun j => ℓ (sa16sz_iota2 d m p (u j))) atTop (𝓝 (ℓ G)))
    (Dn : EuclideanSpace ℝ (Fin d) → ℝ) (hDc : Continuous Dn) (hD0 : ∀ x, R0 < ‖x‖ → Dn x = 0)
    (hD0j : ∀ j x, R0 < ‖x‖ → sa16so_divFun (bc j) ψ x = 0)
    (huni : ∀ ε : ℝ, 0 < ε → ∀ᶠ j in atTop, ∀ x, |sa16so_divFun (bc j) ψ x - Dn x| ≤ ε)
    (NL : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (NLlim : EuclideanSpace ℝ (Fin d) → ℝ)
    (hNLid : ∀ j (y : WmpSpace d m p), sa16r_ell d m p hψ (T0 j y) = ∫ x, wrep d m p y x * NL j x)
    (hNLm : ∀ j, AEStronglyMeasurable (NL j) volume) (hNLm' : AEStronglyMeasurable NLlim volume)
    (hNLj : ∀ j, MemLp (NL j) (ENNReal.conjExponent (ENNReal.ofReal p)) volume)
    (hNL : MemLp NLlim (ENNReal.conjExponent (ENNReal.ofReal p)) volume)
    (hNLc : Tendsto (fun j => (eLpNorm (fun x => NL j x - NLlim x) (ENNReal.conjExponent (ENNReal.ofReal p))
      volume).toReal) atTop (𝓝 0)) :
    Tendsto (fun j => ν j * sa16r_ell d (m + 1 + 1) p hχ (u j) + sa16r_ell d (m + 1) p hψ (K j (u j))) atTop
      (𝓝 (νlim * sa16r_ell d m p hχ G - (∫ x, wrep d m p G x * Dn x) - ∫ x, wrep d m p G x * NLlim x)) := by
  have hDj : ∀ j, Continuous (sa16so_divFun (bc j) ψ) := fun j => (sa16so_cc_div (hbo j) hψ).1.continuous
  have hA : Tendsto (fun j => ν j * sa16r_ell d (m + 1 + 1) p hχ (u j)) atTop
      (𝓝 (νlim * sa16r_ell d m p hχ G)) := by
    simp_rw [← sa16y3_ell_iota2 hχ]
    exact hν.mul (hw (sa16r_ell d m p hχ))
  have hB := sa16y3_pair_tendsto (p := p) (fun j => sa16sz_iota2 d m p (u j)) G hbd hw
    (fun j => sa16so_divFun (bc j) ψ) Dn hDj hDc hD0j hD0 huni
  have hC := sa16y4_pair_tendsto_Lq (p := p) (fun j => sa16sz_iota2 d m p (u j)) G hbd hw NL NLlim hNLm hNLm' hNLj
    hNL hNLc
  have hsum := hA.add ((hB.neg).sub hC)
  rw [show νlim * sa16r_ell d m p hχ G - (∫ x, wrep d m p G x * Dn x) - ∫ x, wrep d m p G x * NLlim x =
      νlim * sa16r_ell d m p hχ G + ((-∫ x, wrep d m p G x * Dn x) - ∫ x, wrep d m p G x * NLlim x) by ring]
  refine hsum.congr (fun j => ?_)
  rw [sa16y3_K_pair_eq (hbo j) hψ (T1 j) (T0 j) (hcomp j) (K j) (hK j) (u j), hNLid j]

end Lm2

end HRS.Whole.AppendixA.Phase2SA16R
