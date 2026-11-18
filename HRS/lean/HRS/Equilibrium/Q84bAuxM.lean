/-
# HRS.Equilibrium.Q84bAuxM — packet Q84b: measurability of the second-slot gradient, `μ`-integrals
-/
import HRS.Equilibrium.Q84bAuxL

open MeasureTheory Filter Topology

noncomputable section

namespace HRS.Q84b

variable {d : ℕ} {s : ℝ}

theorem q84b_gradFst_snd_aesm (hd0 : 0 < d) {K : ℝ} {ψ : Torus d → Torus d → ℝ}
    (hPs : PsiSize s K ψ) (x : Torus d) : AEStronglyMeasurable (fun z => gradFst ψ x z) volume := by
  set H : Torus d → Euc d := fun z => (InnerProductSpace.toDual ℝ (Euc d)).symm
    ((fderiv ℝ (lift2 ψ) (Torus.rep x, Torus.rep z)).comp (ContinuousLinearMap.inl ℝ (Euc d) (Euc d)))
    with hH
  have hHm : Measurable H := by
    have h1 : Measurable (fun z : Torus d => fderiv ℝ (lift2 ψ) (Torus.rep x, Torus.rep z)) :=
      (measurable_fderiv ℝ (lift2 ψ)).comp (measurable_const.prodMk (q84b_measurable_rep d))
    have h2 : Continuous (fun L : (Euc d × Euc d) →L[ℝ] ℝ =>
        (InnerProductSpace.toDual ℝ (Euc d)).symm (L.comp (ContinuousLinearMap.inl ℝ (Euc d) (Euc d)))) :=
      (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp
        (ContinuousLinearMap.precomp ℝ (ContinuousLinearMap.inl ℝ (Euc d) (Euc d))).continuous
    exact h2.measurable.comp h1
  refine hHm.aestronglyMeasurable.congr ?_
  filter_upwards [q84b_ae_ne hd0 x] with z hz
  have hxz : x ≠ z := fun h => hz h.symm
  have hp : ((Torus.rep x, Torus.rep z) : Euc d × Euc d) ∈ offDiag d := by
    show Torus.mk (Torus.rep x) ≠ Torus.mk (Torus.rep z)
    rw [Torus.mk_rep, Torus.mk_rep]; exact hxz
  have e := Q84a.q84a_gradFst_eq hPs.smooth hp
  rw [Torus.mk_rep, Torus.mk_rep] at e
  exact e.symm

theorem q84b_gradFst_snd_integrable (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {K : ℝ}
    {ψ : Torus d → Torus d → ℝ} (hPs : PsiSize s K ψ) (x : Torus d) :
    Integrable (fun z => gradFst ψ x z) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs1 : 1 ≤ s := by rw [hcrit]; linarith
  have hd0 : 0 < d := by omega
  refine Integrable.mono' ((q84b_w_integrable hd hcrit x).const_mul K)
    (q84b_gradFst_snd_aesm hd0 hPs x) ?_
  filter_upwards [q84b_ae_ne hd0 x] with z hz
  exact Q84a.q84a_grad_le_w hs1 hPs (fun h => hz h.symm)

/-- Integrability against `μ = ρ dx` in terms of `ρ g`. -/
theorem q84b_integrable_mu_iff {ρ : Torus d → ℝ} (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    {g : Torus d → ℝ} :
    Integrable g (withDensityReal ρ) ↔ Integrable (fun z => ρ z * g z) := by
  unfold withDensityReal
  rw [integrable_withDensity_iff (f := fun x => ENNReal.ofReal (ρ x))
    (ENNReal.measurable_ofReal.comp hρm)
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integrable_congr (Eventually.of_forall fun z => ?_)
  simp [ENNReal.toReal_ofReal (hρ0 z), mul_comm]

end HRS.Q84b
