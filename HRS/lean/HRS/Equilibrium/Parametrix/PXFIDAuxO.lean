import HRS.Equilibrium.Parametrix.PXFIDAuxN

/-!
# Packet PX-FID, file O: measurability of the source `H_f`
-/

open MeasureTheory Filter Topology
open scoped ContDiff ENNReal

noncomputable section

namespace HRS.Parx.PXFID

variable {d : ℕ} {s : ℝ}

theorem measurable_hTransport (hsd : s < d) (f : Torus d → ℝ) :
    Measurable (fun p : Torus d × Torus d => hTransport d s f p.1 p.2) := by
  unfold hTransport
  exact (((measurable_grad f).comp measurable_fst).sub
    ((measurable_grad f).comp measurable_snd)).inner
    ((KernelGrad.measurable_periodicRieszGrad hsd).comp (measurable_fst.sub measurable_snd))

theorem measurable_canonicalCenter {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    {h : Torus d → Torus d → ℝ} (hm : Measurable (fun p : Torus d × Torus d => h p.1 p.2)) :
    Measurable (fun p : Torus d × Torus d => canonicalCenter μ h p.1 p.2) := by
  unfold canonicalCenter
  have t2 : Measurable (fun p : Torus d × Torus d => ∫ y', h p.1 y' ∂μ) := by
    have : StronglyMeasurable (fun x : Torus d => ∫ y', h x y' ∂μ) :=
      (hm.stronglyMeasurable : StronglyMeasurable (Function.uncurry h)).integral_prod_right
    exact this.measurable.comp measurable_fst
  have t3 : Measurable (fun p : Torus d × Torus d => ∫ x', h x' p.2 ∂μ) := by
    have h' : StronglyMeasurable (Function.uncurry fun y x' => h x' y) :=
      (hm.comp measurable_swap).stronglyMeasurable
    have : StronglyMeasurable (fun y : Torus d => ∫ x', h x' y ∂μ) := h'.integral_prod_right
    exact this.measurable.comp measurable_snd
  exact ((hm.sub t2).sub t3).add measurable_const

theorem measurable_Hsource (hsd : s < d) (ρ : Torus d → ℝ) (hρ : IsProbDensity ρ) (f : Torus d → ℝ) :
    Measurable (fun p : Torus d × Torus d => Hsource d s ρ f p.1 p.2) := by
  have : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ
  unfold Hsource
  exact measurable_const.mul (measurable_canonicalCenter (measurable_hTransport hsd f))

end HRS.Parx.PXFID

end
