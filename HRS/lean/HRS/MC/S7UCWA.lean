import HRS.MC.S7UCDefs
import HRS.MC.S7UCHA
import HRS.MC.S7FCH4G

/-!
# Packet ucW (UC-H4), helper A: the laws of the finite-rank pair at window `a` as pushforwards of the window laws

Sorry-free; imports no sorried module.  `S7UCW_particle_law` / `S7UCW_gauss_law` are the window-`a` versions of the
identifications `hL`, `hR` in the proof of `S7FCH4_core` (`S7FCH4H.lean`), from the identities UC-H4a/b.
Namespace `HRS.MC.Sec7.S7UCW`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.SEdge HRS.MC.QRSpec HRS.MC.Sec7.FCPlan HRS.MC.Sec7.S7FCH4
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7UCW

variable {d : ℕ}

/-- Particle side: the law of `(ζ_N^a, toL2 fcPart)` is the pushforward of `Law ζ_N^a` by `u ↦ (u, ι(Y u - ∫ Y))`. -/
theorem S7UCW_particle_law (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) (T : ℝ) (hT : 0 < T)
    {N : ℕ} (hN : 2 ≤ N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hreal : PreparedRealization R.D P
      (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) X₀ W X)
    (a : ℝ) (ha : 0 ≤ a)
    (S : Finset (NonzeroLattice d)) (K : NonzeroLattice d → FRKernel d) (m : PathSpace d r T)
    (hm : ∀ᵐ ω ∂P, zetaWin r T a P X ω = HRS.Main.windowFluc r T a (Real.sqrt N) X R.ρ ω - m)
    (hzm : AEMeasurable (zetaWin r T a P X) P)
    (hint : Integrable (fun ω => S7FCH4_Y S K (Real.sqrt N)⁻¹ m (zetaWin r T a P X ω)) P) :
    law P (fun ω => (zetaWin r T a P X ω,
      toL2 r T (fun t => fcPartAt r S K (fun t => withDensityReal (R.ρ t)) P X (a + t) ω))) =
      (law P (zetaWin r T a P X)).map (fun u => (u, S7FCH4_iota hT.le
        (S7FCH4_Y S K (Real.sqrt N)⁻¹ m u - ∫ x, S7FCH4_Y S K (Real.sqrt N)⁻¹ m x ∂(law P (zetaWin r T a P X))))) := by
  classical
  have hΨ : Measurable (fun u : PathSpace d r T => (u, S7FCH4_iota hT.le
      (S7FCH4_Y S K (Real.sqrt N)⁻¹ m u - ∫ x, S7FCH4_Y S K (Real.sqrt N)⁻¹ m x ∂(law P (zetaWin r T a P X))))) :=
    measurable_id.prodMk ((S7FCH4_iota_continuous hT.le).measurable.comp
      ((S7FCH4_Y_continuous S K _ _).measurable.sub_const _))
  have hcen : ∫ x, S7FCH4_Y S K (Real.sqrt N)⁻¹ m x ∂(law P (zetaWin r T a P X)) =
      ∫ ω, S7FCH4_Y S K (Real.sqrt N)⁻¹ m (zetaWin r T a P X ω) ∂P :=
    integral_map hzm (S7FCH4_Y_continuous S K _ _).aestronglyMeasurable
  have hid := HRS.MC.Sec7.S7UCH.s7_UC_H4_particle_id_proof R r hr T hT hN P X₀ W X hreal a ha S K m hm hint
  rw [AEMeasurable.map_map_of_aemeasurable hΨ.aemeasurable hzm]
  refine Measure.map_congr (hid.mono fun ω h => ?_)
  simp only [Function.comp]
  rw [h, hcen]

/-- Gaussian side: the law of `(procWin^a, toL2 fcGauss)` is the pushforward of `Law procWin^a` by `v ↦ (v, ι(Y₀ v - ∫ Y₀))`. -/
theorem S7UCW_gauss_law {r : ℝ} {T : ℝ} (hT : 0 < T) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    [IsProbabilityMeasure P'] (η : ℝ → Ω' → NegSobolev d r) (S : Finset (NonzeroLattice d))
    (K : NonzeroLattice d → FRKernel d) (a : ℝ) (ha : 0 ≤ a) (hmeas : ∀ t, Measurable (η t))
    (hc : ∀ᵐ ω ∂P', ContinuousOn (fun t => η t ω) (Set.Icc a (a + T)))
    (hpm : AEMeasurable (procWin r T a η) P')
    (hmom : Integrable (fun ω => ‖procWin r T a η ω‖ ^ 2) P')
    (hint : Integrable (fun ω => S7FCH4_Y S K 0 (0 : PathSpace d r T) (procWin r T a η ω)) P') :
    law P' (fun ω => (procWin r T a η ω, toL2 r T (fun t => fcGaussAt r S K P' η (a + t) ω))) =
      (law P' (procWin r T a η)).map (fun u => (u, S7FCH4_iota hT.le
        (S7FCH4_Y S K 0 (0 : PathSpace d r T) u - ∫ x, S7FCH4_Y S K 0 (0 : PathSpace d r T) x ∂(law P' (procWin r T a η))))) := by
  classical
  have hΨ0 : Measurable (fun u : PathSpace d r T => (u, S7FCH4_iota hT.le
      (S7FCH4_Y S K 0 (0 : PathSpace d r T) u - ∫ x, S7FCH4_Y S K 0 (0 : PathSpace d r T) x ∂(law P' (procWin r T a η))))) :=
    measurable_id.prodMk ((S7FCH4_iota_continuous hT.le).measurable.comp
      ((S7FCH4_Y_continuous S K _ _).measurable.sub_const _))
  have hcen0 : ∫ x, S7FCH4_Y S K 0 (0 : PathSpace d r T) x ∂(law P' (procWin r T a η)) =
      ∫ ω, S7FCH4_Y S K 0 (0 : PathSpace d r T) (procWin r T a η ω) ∂P' :=
    integral_map hpm (S7FCH4_Y_continuous S K _ _).aestronglyMeasurable
  have hgid := HRS.MC.Sec7.S7UCH.s7_UC_H4_gauss_id_proof hT P' η S K a ha hmeas hc hmom hint
  refine Eq.trans ?_ (AEMeasurable.map_map_of_aemeasurable hΨ0.aemeasurable hpm).symm
  refine Measure.map_congr (hgid.mono fun ω h => ?_)
  simp only [Function.comp]
  rw [h, hcen0]

end HRS.MC.Sec7.S7UCW

end
