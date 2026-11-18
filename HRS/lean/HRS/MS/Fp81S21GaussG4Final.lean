import HRS.MS.Fp81S21GaussG4U824
import HRS.MS.Fp81S21GaussG4U842
import HRS.MS.Fp81S21GaussG4U9

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.S111X2 HRS.MS.ProClosureS111

theorem fp81s21_g4_physical_unconditional (p : Parameters) :
    fp81s21_g4Phys p (fun _ R =>
      letI : IsProbabilityMeasure (r26t3_mu R 0) := fp81s21_initialMeasure_isProbability p R
      ∃ Mg : ℝ, ∃ K : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ] Lp ℝ 2 (r26t3_mu R 0),
      ∃ hK : KRep (rieszKernel p.d p.s) (r26t3_mu R 0) K Mg,
      ∀ E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2),
      ∀ H : ℝ, 0 < H → ∃ l : ℕ → ℝ,
        (∀ j, 0 ≤ l j) ∧ Summable l ∧
        ∀ a : ℝ, 0 ≤ a → ∀ s ∈ Icc (0 : ℝ) H, ∀ t ∈ Icc (0 : ℝ) H, ∀ j,
          ‖fp81s21_combinedFeature p R hK (a+t) (E.test j) -
            fp81s21_combinedFeature p R hK (a+s) (E.test j)‖^2 ≤ l j * |t-s|) := by
  apply fp81s21_g4_physical p
    (fp81s21_g4_compact_pieces p (fp81s21_g4_compact_reference_pieces p))
  intro δ R hδ hδhalf
  letI : IsProbabilityMeasure (r26t3_mu R 0) := fp81s21_initialMeasure_isProbability p R
  intro Mg K hK f hf v w hv hvw
  exact fp81s21_g4_initial_increment_le_centered p R hδ hδhalf hK hf hv hvw

theorem fp81s21_g4_weighted_trace_chart (p : Parameters) :
    fp81s21_g4Phys p (fun _ R =>
      letI : IsProbabilityMeasure (r26t3_mu R 0) := fp81s21_initialMeasure_isProbability p R
      ∃ Mg : ℝ, ∃ K : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ] Lp ℝ 2 (r26t3_mu R 0),
      ∃ hK : KRep (rieszKernel p.d p.s) (r26t3_mu R 0) K Mg,
      ∀ E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2),
      ∀ H : ℝ, 0 < H → ∃ l : ℕ → ℝ,
        (∀ j, 0 ≤ l j) ∧ Summable l ∧
        ∀ a : ℝ, 0 ≤ a → ∀ s ∈ Icc (0 : ℝ) H, ∀ t ∈ Icc (0 : ℝ) H, ∀ j,
          ‖fp81s21_combinedFeature p R hK (a+t) (E.test j) -
            fp81s21_combinedFeature p R hK (a+s) (E.test j)‖^2 ≤ l j * |t-s|) :=
  fp81s21_g4_physical_unconditional p

#print axioms fp81s21_g4_physical_unconditional
#print axioms fp81s21_g4_weighted_trace_chart
end HRS.Fp81.S21
end
