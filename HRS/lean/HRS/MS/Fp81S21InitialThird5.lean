import HRS.MS.Fp81S21InitialThird4

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open S45 S99
open HRS.Whole
open HRS (Euc)
open HRS.MS.R26T3

/-- Third-series identity at the actual initial law. The coefficient is the actual response
cube, and the reversed basis order agrees with `S99.s99_third_apply`. -/
theorem fp81s21_initial_third_series
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (E : InitialSteinEnv R) (hγ : 0 < p.γ)
    {φ : ℕ → Euc p.d → ℝ}
    (hφ : IsSummableFeatureFamily (fp81s21_J1 p.d) φ)
    (F : InitialFamData R φ)
    {G : Measure SeqL2} [IsProbabilityMeasure G]
    {Φ' : SeqL2 → ℝ} (hΦ : ContDiff ℝ 3 Φ')
    (hD : ∀ z, ‖iteratedFDeriv ℝ 3 Φ' z‖ ≤ 1) :
    ∫ z, (∫ x, iteratedFDeriv ℝ 3 Φ' z
        ![fp81s21_initial_ellv R φ x, fp81s21_initial_ellv R φ x,
          fp81s21_initial_ellv R φ x] ∂(r26t3_mu R 0)) ∂G =
      ∑' j, ∑' k, ∑' m, fp81s21_initial_kap3 R φ j k m *
        ∫ z, iteratedFDeriv ℝ 3 Φ' z
          ![s45_e1 m (1 : ℝ), s45_e1 k (1 : ℝ), s45_e1 j (1 : ℝ)] ∂G := by
  have hinner : ∀ z, ∫ x, iteratedFDeriv ℝ 3 Φ' z
      ![fp81s21_initial_ellv R φ x, fp81s21_initial_ellv R φ x,
        fp81s21_initial_ellv R φ x] ∂(r26t3_mu R 0) =
      ∑' j, ∑' k, ∑' m, fp81s21_initial_kap3 R φ j k m *
        iteratedFDeriv ℝ 3 Φ' z
          ![s45_e1 m (1 : ℝ), s45_e1 k (1 : ℝ), s45_e1 j (1 : ℝ)] := by
    intro z
    exact fp81s21_initial_third_inner R E hφ F hΦ hD z
  calc
    ∫ z, (∫ x, iteratedFDeriv ℝ 3 Φ' z
        ![fp81s21_initial_ellv R φ x, fp81s21_initial_ellv R φ x,
          fp81s21_initial_ellv R φ x] ∂(r26t3_mu R 0)) ∂G =
      ∫ z, ∑' j, ∑' k, ∑' m, fp81s21_initial_kap3 R φ j k m *
        iteratedFDeriv ℝ 3 Φ' z
          ![s45_e1 m (1 : ℝ), s45_e1 k (1 : ℝ), s45_e1 j (1 : ℝ)] ∂G := by
        apply integral_congr_ae
        filter_upwards with z
        exact hinner z
    _ = ∑' j, ∑' k, ∑' m, fp81s21_initial_kap3 R φ j k m *
        ∫ z, iteratedFDeriv ℝ 3 Φ' z
          ![s45_e1 m (1 : ℝ), s45_e1 k (1 : ℝ), s45_e1 j (1 : ℝ)] ∂G :=
      fp81s21_initial_third_outer R E hφ F hΦ hD

#print axioms fp81s21_initial_third_series

end HRS.Fp81.S21

end
