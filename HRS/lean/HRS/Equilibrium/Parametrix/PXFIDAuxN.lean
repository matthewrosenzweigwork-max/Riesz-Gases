import HRS.Equilibrium.Parametrix.PXFIDAuxM

/-!
# Packet PX-FID, file N: a.e. measurability on `𝕋^d × 𝕋^d` of the slice quantities
-/

open MeasureTheory Filter Topology
open scoped ContDiff ENNReal

noncomputable section

namespace HRS.Parx.PXFID

variable {d : ℕ} {s : ℝ} {V : Torus d → ℝ} {β : ℝ} {ρ : Torus d → ℝ}

theorem differentiableAt_offDiag {K : ℝ} {ψ : Torus d → Torus d → ℝ} (hψ : PsiSize s K ψ)
    (x y : Torus d) (hxy : x ≠ y) :
    DifferentiableAt ℝ (lift2 ψ) (Torus.rep x, Torus.rep y) := by
  have hmem : (Torus.rep x, Torus.rep y) ∈ offDiag d := by
    simp [offDiag, Torus.mk_rep, hxy]
  exact ((hψ.smooth.contDiffAt ((isOpen_offDiag'' d).mem_nhds hmem)).differentiableAt (by simp))

theorem differentiableAt_of_smooth {φ : Torus d → Torus d → ℝ} (hφ : ContDiff ℝ ∞ (lift2 φ))
    (p : Euc d × Euc d) : DifferentiableAt ℝ (lift2 φ) p :=
  hφ.differentiable (by simp) p

theorem aem_gradFst {K : ℝ} {ψ : Torus d → Torus d → ℝ} (hψ : PsiSize s K ψ) (hd : 1 ≤ d)
    (hρ : IsProbDensity ρ) :
    AEMeasurable (fun p : Torus d × Torus d => gradFst ψ p.1 p.2)
      ((withDensityReal ρ).prod (withDensityReal ρ)) := by
  refine (measurable_g1 ψ).aemeasurable.congr ?_
  filter_upwards [ae_ne_prod hd hρ] with p hp
  exact (gradFst_eq_g1 ψ p.1 p.2 (differentiableAt_offDiag hψ p.1 p.2 hp)).symm

theorem aem_gradSnd {K : ℝ} {ψ : Torus d → Torus d → ℝ} (hψ : PsiSize s K ψ) (hd : 1 ≤ d)
    (hρ : IsProbDensity ρ) :
    AEMeasurable (fun p : Torus d × Torus d => gradSnd ψ p.1 p.2)
      ((withDensityReal ρ).prod (withDensityReal ρ)) := by
  refine (measurable_g2 ψ).aemeasurable.congr ?_
  filter_upwards [ae_ne_prod hd hρ] with p hp
  exact (gradSnd_eq_g2 ψ p.1 p.2 (differentiableAt_offDiag hψ p.1 p.2 hp)).symm

theorem measurable_gradFst_smooth {φ : Torus d → Torus d → ℝ} (hφ : ContDiff ℝ ∞ (lift2 φ)) :
    Measurable (fun p : Torus d × Torus d => gradFst φ p.1 p.2) := by
  have : (fun p : Torus d × Torus d => gradFst φ p.1 p.2) = g1 φ := by
    funext p
    exact gradFst_eq_g1 φ p.1 p.2 (differentiableAt_of_smooth hφ _)
  rw [this]; exact measurable_g1 φ

theorem measurable_gradSnd_smooth {φ : Torus d → Torus d → ℝ} (hφ : ContDiff ℝ ∞ (lift2 φ)) :
    Measurable (fun p : Torus d × Torus d => gradSnd φ p.1 p.2) := by
  have : (fun p : Torus d × Torus d => gradSnd φ p.1 p.2) = g2 φ := by
    funext p
    exact gradSnd_eq_g2 φ p.1 p.2 (differentiableAt_of_smooth hφ _)
  rw [this]; exact measurable_g2 φ

theorem aem_B1 {K : ℝ} {ψ : Torus d → Torus d → ℝ} (hψ : PsiSize s K ψ) (hd : 1 ≤ d)
    (hρ : IsProbDensity ρ) :
    AEMeasurable (fun p : Torus d × Torus d => Bop d s V β ρ (fun z => ψ z p.2) p.1)
      ((withDensityReal ρ).prod (withDensityReal ρ)) := by
  have hm : Measurable (fun p : Torus d × Torus d => β⁻¹ * l1 ψ p -
      inner ℝ (Torus.grad V p.1 + forceField d s ρ p.1) (g1 ψ p)) :=
    (measurable_const.mul (measurable_l1 ψ)).sub
      ((((measurable_grad V).comp measurable_fst).add
        ((measurable_grad _).comp measurable_fst)).inner (measurable_g1 ψ))
  refine hm.aemeasurable.congr ?_
  filter_upwards [ae_ne_prod hd hρ] with p hp
  unfold Bop
  rw [laplacian_fst_eq_l1 hψ p.1 p.2 hp]
  have := gradFst_eq_g1 ψ p.1 p.2 (differentiableAt_offDiag hψ p.1 p.2 hp)
  unfold gradFst at this
  rw [this]

theorem aem_B2 {K : ℝ} {ψ : Torus d → Torus d → ℝ} (hψ : PsiSize s K ψ) (hd : 1 ≤ d)
    (hρ : IsProbDensity ρ) :
    AEMeasurable (fun p : Torus d × Torus d => Bop d s V β ρ (fun z => ψ p.1 z) p.2)
      ((withDensityReal ρ).prod (withDensityReal ρ)) := by
  have hm : Measurable (fun p : Torus d × Torus d => β⁻¹ * l2 ψ p -
      inner ℝ (Torus.grad V p.2 + forceField d s ρ p.2) (g2 ψ p)) :=
    (measurable_const.mul (measurable_l2 ψ)).sub
      ((((measurable_grad V).comp measurable_snd).add
        ((measurable_grad _).comp measurable_snd)).inner (measurable_g2 ψ))
  refine hm.aemeasurable.congr ?_
  filter_upwards [ae_ne_prod hd hρ] with p hp
  unfold Bop
  rw [laplacian_snd_eq_l2 hψ p.1 p.2 hp]
  have := gradSnd_eq_g2 ψ p.1 p.2 (differentiableAt_offDiag hψ p.1 p.2 hp)
  unfold gradSnd at this
  rw [this]

end HRS.Parx.PXFID

end
