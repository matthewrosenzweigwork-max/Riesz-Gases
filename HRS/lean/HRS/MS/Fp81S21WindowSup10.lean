import HRS.MS.Fp81S21WindowSup9

/-!
# HRS S2.1(iii), SOL40 packet 9d: joint measurability of the centered slice

The compiled definition is
`s102_zf P X ω b f = √N * (pair (empirical (X b.toNNReal ω)) f -
pair (meanEmpirical (P.map (X b.toNNReal))) f)`.
This adapter proves measurability for a jointly measurable real test family,
using the finite-coordinate formula for the empirical pairing and measurable
parameter integration for the deterministic mean pairing.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal
open HRS.Whole HRS.MS.R2Interp

namespace HRS.Fp81.S21

/-- Joint measurability in time and realization of `s102_zf` applied to a
jointly measurable family of tests, with particle time held fixed. -/
theorem fp81s21_s102_zf_family_measurable
    {d N : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → EucConfig d N) (b : ℝ)
    (hX : Measurable (X b.toNNReal)) (hN : 0 < N)
    (f : ℝ → Euc d → ℝ)
    (hf : Measurable (Function.uncurry f)) :
    Measurable (fun z : ℝ × Ω => s102_zf P X z.2 b (f z.1)) := by
  let Xb : Ω → EucConfig d N := X b.toNNReal
  let ν : Measure (Euc d) := HRS.Whole.meanEmpirical (P.map Xb)
  haveI : IsProbabilityMeasure (P.map Xb) :=
    (Measure.isProbabilityMeasure_map_iff hX.aemeasurable).2 inferInstance
  haveI : IsProbabilityMeasure ν :=
    HRS.Whole.meanEmpirical_isProbabilityMeasure (P.map Xb)
      (by omega)
  have hMean : Measurable (fun s : ℝ => HRS.Whole.pair ν (f s)) := by
    change Measurable (fun s : ℝ => ∫ x, f s x ∂ν)
    exact (hf.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
  have hEmp : Measurable (fun z : ℝ × Ω =>
      (N : ℝ)⁻¹ * ∑ i : Fin N, f z.1 (Xb z.2 i)) := by
    apply measurable_const.mul
    refine Finset.measurable_sum _ fun i hi => ?_
    exact hf.comp (measurable_fst.prodMk
      ((measurable_pi_apply i).comp (hX.comp measurable_snd)))
  have hPairEmp :
      (fun z : ℝ × Ω => HRS.Whole.pair (HRS.Whole.empirical (Xb z.2)) (f z.1)) =
        (fun z => (N : ℝ)⁻¹ * ∑ i : Fin N, f z.1 (Xb z.2 i)) := by
    funext z
    exact HRS.Whole.pair_empirical hN (Xb z.2) (f z.1)
  have hEmpPair : Measurable (fun z : ℝ × Ω =>
      HRS.Whole.pair (HRS.Whole.empirical (Xb z.2)) (f z.1)) := by
    rw [hPairEmp]
    exact hEmp
  unfold s102_zf
  change Measurable (fun z : ℝ × Ω => Real.sqrt N *
    (HRS.Whole.pair (HRS.Whole.empirical (Xb z.2)) (f z.1) -
      HRS.Whole.pair ν (f z.1)))
  exact measurable_const.mul (hEmpPair.sub (hMean.comp measurable_fst))

#print axioms fp81s21_s102_zf_family_measurable

end HRS.Fp81.S21

end
