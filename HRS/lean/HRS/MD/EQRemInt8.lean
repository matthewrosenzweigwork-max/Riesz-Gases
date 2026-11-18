import HRS.MD.EQRemInt7

/-!
# EQ-REM (b), part 8: Minkowski's integral inequality for the weighted `ℓ²` energy
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MD.EQRem

open HRS HRS.MD.EQ29 HRS.Quad

variable {d : ℕ}

theorem eqrem_ennreal_le_of_sq_le {a b : ℝ≥0∞} (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  by_contra hc
  push Not at hc
  exact absurd h (not_le.2 (ENNReal.pow_lt_pow_left (by norm_num) hc))

/-- `‖∫ f‖_{E_M} ≤ ∫ ‖f‖_{E_M}`: Minkowski for the weighted `ℓ²` energy. -/
theorem eqrem_minkowski {M : ℝ} (S : Set ℝ) (hS : MeasurableSet S) (f : NonzeroLattice d → ℝ → ℝ)
    (hf : ∀ k, IntegrableOn (f k) S) (G : ℝ → ℝ≥0∞)
    (hG : ∀ r ∈ S, coordEnergy M (fun k => f k r) ≤ G r ^ 2) :
    coordEnergy M (fun k => ∫ r in S, f k r) ≤ (∫⁻ r in S, G r) ^ 2 := by
  classical
  unfold coordEnergy
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun F => ?_
  set c : NonzeroLattice d → ℝ := fun k => ∫ r in S, f k r with hc
  set w : NonzeroLattice d → ℝ := fun k => Lattice.jp k.1 ^ (-2 * M) with hw
  have hw0 : ∀ k, 0 ≤ w k := fun k => Real.rpow_nonneg (Torus.jp_pos _).le _
  set A : ℝ := ∑ k ∈ F, w k * c k ^ 2 with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun k _ => mul_nonneg (hw0 k) (sq_nonneg _)
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => mul_nonneg (hw0 k) (sq_nonneg _))]
  show ENNReal.ofReal A ≤ _
  set I : ℝ≥0∞ := ∫⁻ r in S, G r with hI
  rcases hA0.eq_or_lt with hA00 | hApos
  · rw [← hA00]; simp
  -- the integrand
  set h : ℝ → ℝ := fun r => ∑ k ∈ F, w k * c k * f k r with hh
  have hhint : Integrable h (volume.restrict S) := integrable_finsetSum _ fun k _ => (hf k).const_mul _
  have hAeq : A = ∫ r in S, h r := by
    rw [hh, integral_finsetSum _ fun k _ => (hf k).const_mul _]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul]; simp only [hc]; ring
  have hpt : ∀ r ∈ S, |h r| ≤ Real.sqrt A * Real.sqrt (∑ k ∈ F, w k * f k r ^ 2) := by
    intro r hr
    have := Real.sum_mul_le_sqrt_mul_sqrt F (fun k => |Real.sqrt (w k) * c k|) (fun k => |Real.sqrt (w k) * f k r|)
    have e1 : ∑ k ∈ F, |Real.sqrt (w k) * c k| ^ 2 = A := by
      rw [hA]; refine Finset.sum_congr rfl fun k _ => ?_
      rw [sq_abs, mul_pow, Real.sq_sqrt (hw0 k)]
    have e2 : ∑ k ∈ F, |Real.sqrt (w k) * f k r| ^ 2 = ∑ k ∈ F, w k * f k r ^ 2 := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [sq_abs, mul_pow, Real.sq_sqrt (hw0 k)]
    rw [e1, e2] at this
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_trans (le_of_eq ?_) this)
    refine Finset.sum_congr rfl fun k _ => ?_
    have : w k * c k * f k r = (Real.sqrt (w k) * c k) * (Real.sqrt (w k) * f k r) := by
      have e := Real.mul_self_sqrt (hw0 k)
      calc w k * c k * f k r = (Real.sqrt (w k) * Real.sqrt (w k)) * c k * f k r := by rw [e]
        _ = _ := by ring
    rw [this, abs_mul]
  -- pointwise bound by G
  have hpt2 : ∀ r ∈ S, ENNReal.ofReal (|h r|) ≤ ENNReal.ofReal (Real.sqrt A) * G r := by
    intro r hr
    refine (ENNReal.ofReal_le_ofReal (hpt r hr)).trans ?_
    rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    refine mul_le_mul' le_rfl ?_
    refine eqrem_ennreal_le_of_sq_le ?_
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (Finset.sum_nonneg fun k _ =>
      mul_nonneg (hw0 k) (sq_nonneg _))]
    refine le_trans ?_ (hG r hr)
    unfold coordEnergy
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => mul_nonneg (hw0 k) (sq_nonneg _))]
    exact ENNReal.sum_le_tsum F
  -- integrate
  have hstep : ENNReal.ofReal A ≤ ENNReal.ofReal (Real.sqrt A) * I := by
    calc ENNReal.ofReal A = ENNReal.ofReal (∫ r in S, h r) := by rw [hAeq]
      _ ≤ ENNReal.ofReal (∫ r in S, |h r|) :=
          ENNReal.ofReal_le_ofReal ((le_abs_self _).trans abs_integral_le_integral_abs)
      _ = ∫⁻ r in S, ENNReal.ofReal (|h r|) :=
          ofReal_integral_eq_lintegral_ofReal hhint.abs (ae_of_all _ fun r => abs_nonneg _)
      _ ≤ ∫⁻ r in S, ENNReal.ofReal (Real.sqrt A) * G r := by
          exact setLIntegral_mono' hS hpt2
      _ = ENNReal.ofReal (Real.sqrt A) * I := by
          rw [hI]; exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  have hsp : 0 < Real.sqrt A := Real.sqrt_pos.2 hApos
  have hs0 : ENNReal.ofReal (Real.sqrt A) ≠ 0 := (ENNReal.ofReal_pos.2 hsp).ne'
  have hAs : ENNReal.ofReal A = ENNReal.ofReal (Real.sqrt A) * ENNReal.ofReal (Real.sqrt A) := by
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _), Real.mul_self_sqrt hA0]
  have hsI : ENNReal.ofReal (Real.sqrt A) ≤ I := by
    rw [hAs] at hstep
    exact (ENNReal.mul_le_mul_iff_right hs0 ENNReal.ofReal_ne_top).1 hstep
  rw [hAs, ← sq]
  exact pow_le_pow_left' hsI 2

end HRS.MD.EQRem

end
