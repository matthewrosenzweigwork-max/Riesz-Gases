import HRS.Main.T25PAux25

/-!
# T25P, part 26: clause 1 of Theorem 2.5 (smooth and `W₁` bounds)

`t25p_exists_coupling` (`ε`-optimal couplings), `t25p_lim` (`ε → 0`), and `t25p_clause1`.
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory Complex
open scoped ENNReal NNReal BigOperators Matrix RealInnerProductSpace

namespace HRS.T25P

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.Main HRS.T25

variable {d : ℕ}

theorem t25p_exists_coupling {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    (p : ℝ) (μ ν : Measure B) (hW : wassersteinE p μ ν ≠ ⊤) {δ : ℝ≥0∞} (hδ : δ ≠ 0) :
    ∃ π₀, IsCoupling π₀ μ ν ∧
      (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ p) ∂π₀) ^ (1 / p) ≤ wassersteinE p μ ν + δ := by
  have hlt : wassersteinE p μ ν < wassersteinE p μ ν + δ := ENNReal.lt_add_right hW hδ
  unfold wassersteinE at hlt ⊢
  obtain ⟨π, hπ⟩ := iInf_lt_iff.1 hlt
  exact ⟨π.1, π.2, hπ.le⟩

theorem t25p_ofReal_norm_rpow {E : Type*} [NormedAddCommGroup E] (x : E) {p : ℝ} (hp : 0 ≤ p) :
    ENNReal.ofReal (‖x‖ ^ p) = ‖x‖ₑ ^ p := by
  rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp]

theorem t25p_lim {y R W : ℝ≥0∞} {c0 : ℝ} (hc0 : 0 ≤ c0)
    (h : ∀ δ : ℝ, 0 < δ → y ≤ ENNReal.ofReal c0 * (W + ENNReal.ofReal δ) + R) :
    y ≤ ENNReal.ofReal c0 * W + R := by
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hε' : (0 : ℝ) < ε := by exact_mod_cast hε
  have := h (ε / (c0 + 1)) (by positivity)
  refine this.trans ?_
  rw [mul_add, add_assoc, add_comm (ENNReal.ofReal c0 * ENNReal.ofReal _) R, ← add_assoc]
  gcongr
  rw [← ENNReal.ofReal_mul hc0]
  calc ENNReal.ofReal (c0 * (ε / (c0 + 1))) ≤ ENNReal.ofReal ε := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith
    _ = ε := ENNReal.ofReal_coe_nnreal

end HRS.T25P
