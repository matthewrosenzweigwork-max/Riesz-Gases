import HRS.MS.MfeConfAux119

/-!
# S.B.1, packet F9 (part 23): the entropy inequality for an initial law dominated by the canonical Gibbs measure

`sb1_bdd_entropy`: assembly of the whole `M → ∞` argument (D01-D09 of the Pro note SB1-Dissipation) for the bounded-density case
`law(X_0) ≤ c · e^{-β H} dX`.  Inputs that are NOT proved here (they are explicit hypotheses):
* `SM`: the vanishing of the force-defect remainder `B^M` (an `η_M`-small envelope, `η_M → 0`; packet R06/D05b);
* `hBmeas`, `hTM`: measurability of `B^M` and measurability in time of the level-`M` source mean (export from `sb1_lv_ineq`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory InformationTheory
open HRS HRS.Whole HRS.MD.EQLawPath HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d N : ℕ}

/-- setwise convergence of the laws of the regularised solutions at a fixed time -/
theorem sb1_setwise {Ω : Type*} [mΩ : MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {Z : ℕ → Ω → Whole.EucConfig d N} {Zlim : Ω → Whole.EucConfig d N}
    (hZ : ∀ M, Measurable (Z M)) (hZlim : Measurable Zlim) (hae : ∀ᵐ ξ ∂Pm, ∀ᶠ M in atTop, Z M ξ = Zlim ξ)
    (A : Set (Whole.EucConfig d N)) (hA : MeasurableSet A) :
    Tendsto (fun M => Pm.map (Z M) A) atTop (𝓝 (Pm.map Zlim A)) := by
  simp only [Measure.map_apply (hZ _) hA, Measure.map_apply hZlim hA]
  refine tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop (hZlim hA) (fun M => hZ M hA) ?_
  filter_upwards [hae] with ξ h
  filter_upwards [h] with M hM
  simp only [Set.mem_preimage, hM]

end HRS.MS.MfeConf
