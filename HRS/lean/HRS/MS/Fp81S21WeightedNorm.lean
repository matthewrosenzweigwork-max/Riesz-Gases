import HRS.Whole.Round2
import HRS.Whole.Orbits
import HRS.MS.R26T6CD01
import HRS.MS.ProClosureS111WeightedChart

/-! Exact dual norm of the Hilbert chart action. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.ProClosureS111

variable {d r : ℕ} {Pw : ℝ}

/-- Pair a chart coordinate vector with the encoded weighted test. -/
def fp81s21_chartAction (E : r26t6_WeightedChart d r Pw)
    (z : r26t6_Coeff) (f : Euc d → ℝ) : ℝ :=
  inner ℝ z (E.encode f)

/-- The compact-test dual norm of the action induced by a weighted chart
is exactly the Hilbert norm of its coordinate vector. -/
theorem fp81s21_chartAction_dualNorm
    (hP : (d : ℝ) < 2 * Pw) (E : r26t6_WeightedChart d r Pw)
    (z : r26t6_Coeff) :
    dualNormE r Pw (fp81s21_chartAction E z) = ENNReal.ofReal ‖z‖ := by
  let η : (Euc d → ℝ) → ℝ := fp81s21_chartAction E z
  have hupper : dualNormE r Pw η ≤ ENNReal.ofReal ‖z‖ := by
    unfold dualNormE
    refine iSup_le fun f => iSup_le fun hf => ?_
    have hw : IsR2WeightedTest r Pw f :=
      ⟨hf.1.of_le (by exact_mod_cast (le_top : (r : ℕ∞) ≤ ⊤)), hf.2.2.2⟩
    have hnorm := E.norm f hw
    have hpoint : |η f| ≤ ‖z‖ * (weightedSobolevE r Pw f).toReal := by
      dsimp [η, fp81s21_chartAction]
      rw [← hnorm]
      exact abs_real_inner_le_norm _ _
    refine ENNReal.div_le_of_le_mul ?_
    calc ENNReal.ofReal |η f|
        ≤ ENNReal.ofReal (‖z‖ * (weightedSobolevE r Pw f).toReal) :=
          ENNReal.ofReal_le_ofReal hpoint
      _ = ENNReal.ofReal ‖z‖ * weightedSobolevE r Pw f := by
          rw [ENNReal.ofReal_mul (norm_nonneg _), ENNReal.ofReal_toReal hf.2.2.2.ne]

  have hDtop : dualNormE r Pw η < ⊤ :=
    lt_of_le_of_lt hupper ENNReal.ofReal_lt_top
  have hrange : ∀ y ∈ Set.range
      (fun f : {f : Euc d → ℝ // IsR2Test f} => E.encode f),
      |inner ℝ z y| ≤ (dualNormE r Pw η).toReal * ‖y‖ := by
    intro y hy
    obtain ⟨f, rfl⟩ := hy
    let f₀ : Euc d → ℝ := f
    let w := weightedSobolevE r Pw f₀
    have hwt : IsR2WeightedTest r Pw f₀ :=
      weightedTestSubmodule_iff.1
        (weighted_test_of_compact_smooth (r := r) (Pw := Pw) hP f.property)
    have hnorm := E.norm f₀ hwt
    by_cases hy0 : E.encode f₀ = 0
    · change |inner ℝ z (E.encode f₀)| ≤
        (dualNormE r Pw η).toReal * ‖E.encode f₀‖
      simp [hy0]
    · have hwpos : 0 < w := by
        by_contra hn
        have hwzero : w = 0 := le_antisymm (not_lt.mp hn) bot_le
        have hnorm' : ‖E.encode f₀‖ = w.toReal := by
          simpa [w] using hnorm
        have : ‖E.encode f₀‖ = 0 := by rw [hnorm', hwzero]; simp
        exact hy0 (norm_eq_zero.mp this)
      have hterm : ENNReal.ofReal |η f₀| / w ≤ dualNormE r Pw η := by
        unfold dualNormE
        exact le_iSup_of_le f₀
          (le_iSup_of_le ⟨f.property.1, f.property.2, hwpos, hwt.2⟩ le_rfl)
      have hprod := (ENNReal.div_le_iff hwpos.ne' hwt.2.ne).1 hterm
      have hprodtop : dualNormE r Pw η * w ≠ ⊤ :=
        ENNReal.mul_ne_top hDtop.ne hwt.2.ne
      have hreal := ENNReal.toReal_mono hprodtop hprod
      rw [ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_mul] at hreal
      have hnorm' : ‖E.encode f₀‖ = w.toReal := by
        simpa [w] using hnorm
      rw [← hnorm'] at hreal
      simpa [η, fp81s21_chartAction] using hreal

  have hclosed : IsClosed {y : r26t6_Coeff |
      |inner ℝ z y| ≤ (dualNormE r Pw η).toReal * ‖y‖} := by
    apply isClosed_le
    · fun_prop
    · exact continuous_const.mul continuous_norm
  have hclosure := closure_minimal hrange hclosed
  have hall : ∀ y : r26t6_Coeff,
      |inner ℝ z y| ≤ (dualNormE r Pw η).toReal * ‖y‖ := by
    intro y
    have hy : y ∈ closure (Set.range
        (fun f : {f : Euc d → ℝ // IsR2Test f} => E.encode f)) :=
      (E.dense.closure_eq).symm ▸ Set.mem_univ y
    exact hclosure hy
  have hn : ‖z‖ ≤ (dualNormE r Pw η).toReal := by
    by_cases hz : z = 0
    · simp [hz]
    · have hself := hall z
      rw [real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg ‖z‖)] at hself
      have hzn : 0 < ‖z‖ := norm_pos_iff.mpr hz
      nlinarith
  have hlower : ENNReal.ofReal ‖z‖ ≤ dualNormE r Pw η := by
    calc
      _ ≤ ENNReal.ofReal (dualNormE r Pw η).toReal := ENNReal.ofReal_le_ofReal hn
      _ = dualNormE r Pw η := ENNReal.ofReal_toReal hDtop.ne
  exact le_antisymm hupper hlower

#print axioms HRS.Fp81.S21.fp81s21_chartAction_dualNorm

end HRS.Fp81.S21
