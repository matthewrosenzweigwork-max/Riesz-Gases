import HRS.MS.SA12LimitDefs
import HRS.MS.UniqN0f

/-!
# S.A.12 L3: finite `H⁰_uloc` norm gives a bounded norm in the compactness `L²` space
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Limit

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd HRS.MS.UniqM1 HRS.MS.UniqN0

variable {d : ℕ}

theorem sa12l3_compactWeight_le (x : Euc d) :
    ENNReal.ofReal (compactWeight d x) ≤
      ENNReal.ofReal (Real.sqrt 2 ^ ((d : ℝ) + 3)) *
        ENNReal.ofReal ((1 + ‖x - 0‖) ^ (-((d : ℝ) + 3))) := by
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  simpa [compactWeight] using n0_jbracket_rpow_le (d := d) (κ := (d : ℝ) + 3) (by positivity) x

theorem sa12l3_measurable_weight : Measurable fun x : Euc d => ENNReal.ofReal (compactWeight d x) := by
  refine ENNReal.measurable_ofReal.comp ?_
  unfold compactWeight jbracket
  fun_prop

theorem sa12l3_sq_le_sq {a b : ℝ≥0∞} (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  have e : ∀ x : ℝ≥0∞, (x ^ 2) ^ (1 / 2 : ℝ) = x := fun x => by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
  calc a = (a ^ 2) ^ (1 / 2 : ℝ) := (e a).symm
    _ ≤ (b ^ 2) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow h (by norm_num)
    _ = b := e b

-- BEGIN SA12.L3
theorem weighted_l2_from_uloc (hd : 1 ≤ d) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : Euc d → ℝ) (B : ℝ), 0 ≤ B →
      ulocNormE 0 χ u ≤ ENNReal.ofReal B →
      MemLp u 2 (compactMeasure d) ∧
        eLpNorm u 2 (compactMeasure d) ≤ ENNReal.ofReal (C * B) := by
  set κ : ℝ := (d : ℝ) + 3 with hκ
  have hκd : (d : ℝ) < κ := by rw [hκ]; linarith
  set V : ℝ≥0∞ := volume (Metric.ball (0 : Euc d) 1) with hV
  have hV0 : V ≠ 0 := (Metric.measure_ball_pos volume (0 : Euc d) one_pos).ne'
  have hVt : V ≠ ⊤ := measure_ball_lt_top.ne
  set W : Euc d → ℝ≥0∞ := fun w => ENNReal.ofReal ((1 + ‖w - 0‖) ^ (-κ)) with hW
  have hWint : ∫⁻ w, W w < ⊤ := by
    have := (n0_decay_integrable (d := d) hκd 0).lintegral_lt_top
    simpa [hW] using this
  set c : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt 2 ^ κ) *
    (V⁻¹ * (ENNReal.ofReal (2 ^ κ) * ∫⁻ w, W w)) with hc
  have hcfin : c ≠ ⊤ := by
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.mul_ne_top (ENNReal.inv_ne_top.2 hV0)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hWint.ne))
  refine ⟨Real.sqrt c.toReal, Real.sqrt_nonneg _, fun u B hB hu => ?_⟩
  have hfm := locMass_of_ulocNormE hχ hB hu
  set u' : Euc d → ℝ := hfm.1.mk u with hu'
  have hu'm : Measurable u' := hfm.1.stronglyMeasurable_mk.measurable
  have huu' : u =ᵐ[volume] u' := hfm.1.ae_eq_mk
  have huu'c : u =ᵐ[compactMeasure d] u' := (withDensity_absolutelyContinuous _ _) huu'
  -- the local `L¹` mass of `u'^2`
  set f : Euc d → ℝ := fun y => u' y ^ 2 with hf
  have hfm' : Measurable f := hu'm.pow_const 2
  have hL : ∀ c0 : Euc d, ∫⁻ y in Metric.ball c0 1, ‖f y‖ₑ ≤ ENNReal.ofReal (B ^ 2) := by
    intro c0
    refine le_trans (le_of_eq ?_) (hfm.2 c0)
    refine lintegral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae huu'] with y hy
    simp only [hf, enorm_pow, hy]
  have hcore := n0_decay_core hκd 0 f hfm' (ENNReal.ofReal (B ^ 2)) hL
  rw [← hV] at hcore
  have hcore' : ∫⁻ y, ‖f y‖ₑ * W y ≤
      V⁻¹ * (ENNReal.ofReal (2 ^ κ) * (ENNReal.ofReal (B ^ 2) * ∫⁻ w, W w)) :=
    (ENNReal.mul_le_iff_le_inv hV0 hVt).1 hcore
  -- the weighted square of `u'`
  have hsq : eLpNorm u' 2 (compactMeasure d) ^ 2 = ∫⁻ x, ENNReal.ofReal (compactWeight d x) *
      ‖u' x‖ₑ ^ 2 := by
    rw [sq_eLpNorm_two hu'm.aestronglyMeasurable, compactMeasure,
      lintegral_withDensity_eq_lintegral_mul _ sa12l3_measurable_weight
        (hu'm.enorm.pow_const 2)]
    rfl
  have hbound : ∫⁻ x, ENNReal.ofReal (compactWeight d x) * ‖u' x‖ₑ ^ 2 ≤
      c * ENNReal.ofReal (B ^ 2) := by
    calc ∫⁻ x, ENNReal.ofReal (compactWeight d x) * ‖u' x‖ₑ ^ 2
        ≤ ∫⁻ x, ENNReal.ofReal (Real.sqrt 2 ^ κ) * (‖f x‖ₑ * W x) := by
          refine lintegral_mono fun x => ?_
          have h1 := sa12l3_compactWeight_le (d := d) x
          have h2 : ‖u' x‖ₑ ^ 2 = ‖f x‖ₑ := by simp [hf, enorm_pow]
          rw [h2]
          calc ENNReal.ofReal (compactWeight d x) * ‖f x‖ₑ
              ≤ (ENNReal.ofReal (Real.sqrt 2 ^ κ) * W x) * ‖f x‖ₑ :=
                mul_le_mul' h1 le_rfl
            _ = _ := by ring
      _ = ENNReal.ofReal (Real.sqrt 2 ^ κ) * ∫⁻ x, ‖f x‖ₑ * W x := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (Real.sqrt 2 ^ κ) *
            (V⁻¹ * (ENNReal.ofReal (2 ^ κ) * (ENNReal.ofReal (B ^ 2) * ∫⁻ w, W w))) :=
          mul_le_mul' le_rfl hcore'
      _ = c * ENNReal.ofReal (B ^ 2) := by
          rw [hc]; ring
  have hsq2 : eLpNorm u' 2 (compactMeasure d) ^ 2 ≤ ENNReal.ofReal (c.toReal * B ^ 2) := by
    rw [hsq]
    refine hbound.trans ?_
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hcfin]
  have hnorm : eLpNorm u' 2 (compactMeasure d) ≤ ENNReal.ofReal (Real.sqrt c.toReal * B) := by
    have e : ENNReal.ofReal (c.toReal * B ^ 2) = ENNReal.ofReal (Real.sqrt c.toReal * B) ^ 2 := by
      rw [← ENNReal.ofReal_pow (by positivity)]
      congr 1
      rw [mul_pow, Real.sq_sqrt ENNReal.toReal_nonneg]
    rw [e] at hsq2
    exact sa12l3_sq_le_sq hsq2
  have hnorm' : eLpNorm u 2 (compactMeasure d) = eLpNorm u' 2 (compactMeasure d) :=
    eLpNorm_congr_ae huu'c
  have hmem : MemLp u 2 (compactMeasure d) := by
    rw [memLp_iff, hnorm']; exact hnorm.trans_lt ENNReal.ofReal_lt_top
  exact ⟨hmem, hnorm'.le.trans hnorm⟩
-- END SA12.L3

end HRS.MH.AdjointRd.Phase2SA12Limit
