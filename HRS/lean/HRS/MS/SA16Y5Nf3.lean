import HRS.MS.SA16Y5Nf2

/-!
# S.A.16 (SA16Y5) Nf3: limit of the nonlocal functional `Φ_{a_j}(g_j)` (pointwise convergent coefficients, common decay)

`sa16y5_Phi_tendsto`: `a_j → μ` pointwise, `|a_j|, |μ| ≤ W (1+|x|)^{-(d+3)}`, `g_j ⇀ G` boundedly in `W^{m,p}` (`m ≥ 1`) give
`Φ_{a_j}(g_j) → Φ_μ(G)`.  No derivative of the coefficients and no operator enters (copy of the tail of `sa16y4_nl_tendsto`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Nf3
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

set_option maxHeartbeats 1600000 in
theorem sa16y5_Phi_tendsto {m : ℕ} (hm : 1 ≤ m) (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (M : Matrix (Fin d) (Fin d) ℝ) {W Bm : ℝ} (hW : 0 ≤ W)
    (a : ℕ → EuclideanSpace ℝ (Fin d) → ℝ) (μ : EuclideanSpace ℝ (Fin d) → ℝ)
    (ha1 : ∀ j, ContDiff ℝ 1 (a j)) (hμ1 : ContDiff ℝ 1 μ)
    (haW : ∀ j x, |a j x| ≤ W * (1 + ‖x‖) ^ (-((d : ℝ) + 3))) (hμW : ∀ x, |μ x| ≤ W * (1 + ‖x‖) ^ (-((d : ℝ) + 3)))
    (hpt : ∀ x, Tendsto (fun j => a j x) atTop (𝓝 (μ x)))
    {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ)
    (gs : ℕ → WmpSpace d m p) (G : WmpSpace d m p) (hbd : ∀ j, ‖gs j‖ ≤ Bm)
    (hw : ∀ ℓ : StrongDual ℝ (WmpSpace d m p), Tendsto (fun j => ℓ (gs j)) atTop (𝓝 (ℓ G))) :
    Tendsto (fun j => sa16y5_Phi d m hm p s M (a j) ψ (gs j)) atTop (𝓝 (sa16y5_Phi d m hm p s M μ ψ G)) := by
  have hq := (sa16y3_conj_bridge (Fact.out : 2 ≤ p))
  obtain ⟨cψ, Cb, hcψ0, hCb0, hκc, hprod, hmem⟩ := sa16y5_nl_data (p := p) hd hs0 hsd hW hψ
  have hd2 : (d : ℝ) < (d : ℝ) + 2 := by linarith
  unfold sa16y5_Phi
  refine (tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun k _ => ?_).neg
  refine (sa16y4_comp_tendsto_Lq (p := p) (sa16y4_tau1 d m hm k) gs G hbd hw (fun j x => a j x * kernelConvDeriv d s i ψ x)
    (fun x => μ x * kernelConvDeriv d s i ψ x) (fun j => ((ha1 j).continuous.mul (hκc i)).aestronglyMeasurable)
    (hμ1.continuous.mul (hκc i)).aestronglyMeasurable (fun j => (hmem (a j) (ha1 j).continuous (haW j) i).1)
    (hmem μ hμ1.continuous hμW i).1 ?_).const_mul (M k i)
  refine sa16y4_Lq_dominated hq.1 hq.2.1.le hd2 (fun j x => a j x * kernelConvDeriv d s i ψ x)
    (fun x => μ x * kernelConvDeriv d s i ψ x) (fun j => (ha1 j).continuous.mul (hκc i))
    (hμ1.continuous.mul (hκc i)) (fun j x => hprod (a j) (haW j) i x) (hprod μ hμW i)
    (fun x => (hpt x).mul_const _)

end Nf3

end HRS.Whole.AppendixA.Phase2SA16R
