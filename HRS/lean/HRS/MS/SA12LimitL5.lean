import HRS.MS.SA12LimitDefs
import HRS.MS.FeatDecAux8
import HRS.MS.ToriCoefAAux1

/-!
# S.A.12 L5: a countable dense family of weighted compact tests in the fixed Hilbert space
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Limit

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd

variable {d : ℕ}

theorem sa12x_weight_pos (x : Euc d) : 0 < compactWeight d x :=
  Real.rpow_pos_of_pos (HRS.MS.ToriCoefA.tca_jbracket_pos x) _

theorem sa12x_weight_le_one (x : Euc d) : compactWeight d x ≤ 1 := by
  unfold compactWeight
  exact Real.rpow_le_one_of_one_le_of_nonpos (HRS.MS.ToriCoefA.tca_one_le_jbracket x)
    (by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith)

theorem sa12x_weight_contDiff : ContDiff ℝ ∞ (compactWeight d) :=
  HRS.MS.S85.s85_jbpow_contDiff (d := d) _

instance sa12x_compactMeasure_fmoc : IsFiniteMeasureOnCompacts (compactMeasure d) := by
  refine ⟨fun K hK => ?_⟩
  unfold compactMeasure
  rw [withDensity_apply _ hK.measurableSet]
  calc ∫⁻ x in K, ENNReal.ofReal (compactWeight d x) ≤ ∫⁻ x in K, 1 :=
        lintegral_mono fun x => by simpa using sa12x_weight_le_one x
    _ = volume K := by simp
    _ < ⊤ := hK.measure_lt_top

-- BEGIN SA12.L5
theorem weighted_compact_tests_dense (hd : 1 ≤ d) :
    ∃ e : ℕ → CompactL2 d, DenseRange e ∧
      ∀ j, ∃ ψ : Euc d → ℝ, IsCcInfty ψ ∧
        (e j : Euc d → ℝ) =ᵐ[compactMeasure d] fun x => ψ x / compactWeight d x := by
  let T : Set (CompactL2 d) := {f | ∃ ψ : Euc d → ℝ, IsCcInfty ψ ∧
    (f : Euc d → ℝ) =ᵐ[compactMeasure d] fun x => ψ x / compactWeight d x}
  have hTdense : Dense T := by
    refine Dense.mono ?_ (MeasureTheory.Lp.dense_hasCompactSupport_contDiff (F := ℝ)
      (E := Euc d) (μ := compactMeasure d) (p := 2) (by simp))
    rintro f ⟨g, hfg, hg1, hg2⟩
    refine ⟨fun x => compactWeight d x * g x,
      ⟨sa12x_weight_contDiff.mul hg2, hg1.mul_left⟩, ?_⟩
    refine hfg.trans (Filter.Eventually.of_forall fun x => ?_)
    simp [(sa12x_weight_pos x).ne']
  have hsep : TopologicalSpace.SeparableSpace T :=
    (TopologicalSpace.IsSeparable.of_separableSpace T).separableSpace
  have hne : Nonempty T := ⟨⟨0, 0, ⟨contDiff_const, HasCompactSupport.zero⟩, by
    filter_upwards [Lp.coeFn_zero ℝ 2 (compactMeasure d)] with x hx
    rw [hx]; simp⟩⟩
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq T
  refine ⟨fun n => (u n : CompactL2 d), ?_, fun n => (u n).2⟩
  exact hTdense.denseRange_val.comp hu continuous_subtype_val
-- END SA12.L5

end HRS.MH.AdjointRd.Phase2SA12Limit
