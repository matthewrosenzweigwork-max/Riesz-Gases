import HRS.MS.TransOpAux10

/-!
# S611 packet P2d: `Λ_c` on embedded measures

`s611_Lam_ofMeasureDiff`: for `m > d` and finite measures `μ, ν`:
`Λ_c (μ - ν) = (T_c μ - T_c ν)` with `T_c μ = μ.map (· + c)` (the exact field transformation `W:r2mov:exact-field`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.TransOp

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

/-- `(μ - ν)(φ) = ∫ φ dμ - ∫ φ dν` for continuous `φ ∈ Σ^m`, `m > d` (the proof of `OscDual.eval_ofMeasureDiff`). -/
theorem s611_eval_ofMeasureDiff {m : ℝ} (hm : (d : ℝ) < m) (μ ν : Measure (Euc d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] {φ : Euc d → ℝ} (hφc : Continuous φ) (hM : MemOsc m φ) :
    OscDual.eval (OscDual.ofMeasureDiff m μ ν) φ = ∫ x, φ x ∂μ - ∫ x, φ x ∂ν := by
  have hsum := OscDual.summable_abs_hermiteCoeff hm hM
  have hexp : ∀ x, φ x = ∑' α : MultiIndex d, Whole.hermiteCoeff φ α * hermiteFunD α x :=
    fun x => OscDual.hermite_expansion_of_summable hφc hM.1 hsum x
  have hsμ := OscDual.summable_measureHermiteCoeff_mul μ hsum
  have hsν := OscDual.summable_measureHermiteCoeff_mul ν hsum
  calc OscDual.eval (OscDual.ofMeasureDiff m μ ν) φ
      = ∑' α : MultiIndex d, (measureHermiteCoeff μ α * Whole.hermiteCoeff φ α
          - measureHermiteCoeff ν α * Whole.hermiteCoeff φ α) := by
        unfold OscDual.eval
        exact tsum_congr fun α => by
          rw [OscDual.hermiteCoeff_ofMeasureDiff hm μ ν α]; ring
    _ = ∑' α : MultiIndex d, measureHermiteCoeff μ α * Whole.hermiteCoeff φ α
          - ∑' α : MultiIndex d, measureHermiteCoeff ν α * Whole.hermiteCoeff φ α :=
        hsμ.tsum_sub hsν
    _ = ∫ x, φ x ∂μ - ∫ x, φ x ∂ν := by
        rw [OscDual.integral_eq_tsum_hermite μ hsum hexp, OscDual.integral_eq_tsum_hermite ν hsum hexp]

/-- `T_c μ = μ.map (· + c)`. -/
theorem s611_measureHermiteCoeff_map (c : Euc d) (μ : Measure (Euc d)) (α : MultiIndex d) :
    measureHermiteCoeff (μ.map (fun x => x + c)) α = ∫ x, hermiteFunD α (x + c) ∂μ := by
  unfold measureHermiteCoeff
  rw [integral_map (measurable_add_const c).aemeasurable
    (contDiff_hermiteFunD α).continuous.aestronglyMeasurable]

theorem s611_Lam_ofMeasureDiff (m : ℕ) (hm : 1 ≤ m) (hdm : (d : ℝ) < m) (c : Euc d)
    (μ ν : Measure (Euc d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    s611_Lam m hm c (OscDual.ofMeasureDiff (m : ℝ) μ ν) =
      OscDual.ofMeasureDiff (m : ℝ) (μ.map (fun x => x + c)) (ν.map (fun x => x + c)) := by
  haveI : IsFiniteMeasure (μ.map (fun x => x + c)) := inferInstance
  haveI : IsFiniteMeasure (ν.map (fun x => x + c)) := inferInstance
  refine OscDual.ext_hermiteCoeff fun α => ?_
  rw [s611_hermiteCoeff_Lam, OscDual.hermiteCoeff_ofMeasureDiff hdm, s611_measureHermiteCoeff_map,
    s611_measureHermiteCoeff_map]
  have hc : Continuous (fun x : Euc d => hermiteFunD α (x + c)) :=
    (contDiff_hermiteFunD α).continuous.comp (continuous_id.add continuous_const)
  exact s611_eval_ofMeasureDiff hdm μ ν hc (s611_memOsc_translate m hm c (s611_memOsc_herm m α)).1

end HRS.MS.TransOp

end
