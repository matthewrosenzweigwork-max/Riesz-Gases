import HRS.MC.S7S7bAux2

/-!
# Packet `s7_S7b_weighted_moments`, helper 3: moments of `B_{N,v}` from the exponential pair estimate
For `v` with Lipschitz constants `L_k` and any `Lam > 0` with `K sum L <= Lam`:
`E_Q |B_{N,v}|^{2q} <= M Lam^{2q}` (and integrability), with `K, M` independent of `v, N`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7b

open HRS HRS.Sec7 HRS.MC.SEdge

variable {d : ℕ} {s : ℝ}

/-- From an exponential moment to polynomial moments. -/
theorem s7b_moment_of_exp {α : Type*} [MeasurableSpace α] (P : Measure α) {Z : α → ℝ}
    (hZ : Measurable Z) {θ M : ℝ} (hθ : 0 < θ) (hM : 0 ≤ M)
    (hE : ∫⁻ x, ENNReal.ofReal (Real.exp (θ * |Z x|)) ∂P ≤ ENNReal.ofReal M) (p : ℕ) :
    Integrable (fun x => |Z x| ^ p) P ∧
      ∫ x, |Z x| ^ p ∂P ≤ (p.factorial : ℝ) * θ⁻¹ ^ p * M := by
  have hexp_meas : Measurable (fun x => Real.exp (θ * |Z x|)) :=
    Real.measurable_exp.comp (measurable_const.mul hZ.abs)
  have hI : Integrable (fun x => Real.exp (θ * |Z x|)) P := by
    refine ⟨hexp_meas.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    simp_rw [Real.enorm_eq_ofReal (Real.exp_pos _).le]
    exact lt_of_le_of_lt hE ENNReal.ofReal_lt_top
  have hIM : ∫ x, Real.exp (θ * |Z x|) ∂P ≤ M := by
    have := ofReal_integral_eq_lintegral_ofReal hI
      (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)
    rw [← this] at hE
    exact (ENNReal.ofReal_le_ofReal_iff hM).1 hE
  have hdom : ∀ x, |Z x| ^ p ≤ (p.factorial : ℝ) * θ⁻¹ ^ p * Real.exp (θ * |Z x|) := by
    intro x
    have h1 := Real.pow_div_factorial_le_exp (θ * |Z x|) (mul_nonneg hθ.le (abs_nonneg _)) p
    have hf : (0 : ℝ) < p.factorial := by exact_mod_cast Nat.factorial_pos p
    rw [div_le_iff₀ hf] at h1
    have hθp : 0 < θ⁻¹ ^ p := by positivity
    calc |Z x| ^ p = θ⁻¹ ^ p * (θ * |Z x|) ^ p := by
          rw [mul_pow, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hθ.ne', one_pow, one_mul]
      _ ≤ θ⁻¹ ^ p * (Real.exp (θ * |Z x|) * p.factorial) :=
          mul_le_mul_of_nonneg_left h1 hθp.le
      _ = _ := by ring
  have hInt : Integrable (fun x => |Z x| ^ p) P := by
    refine Integrable.mono' (hI.const_mul ((p.factorial : ℝ) * θ⁻¹ ^ p))
      (hZ.abs.pow_const p).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
    exact hdom x
  refine ⟨hInt, ?_⟩
  calc ∫ x, |Z x| ^ p ∂P ≤ ∫ x, (p.factorial : ℝ) * θ⁻¹ ^ p * Real.exp (θ * |Z x|) ∂P :=
        integral_mono hInt (hI.const_mul _) hdom
    _ = (p.factorial : ℝ) * θ⁻¹ ^ p * ∫ x, Real.exp (θ * |Z x|) ∂P := integral_const_mul _ _
    _ ≤ (p.factorial : ℝ) * θ⁻¹ ^ p * M :=
        mul_le_mul_of_nonneg_left hIM (by positivity)

end HRS.MC.Sec7.S7b

end
