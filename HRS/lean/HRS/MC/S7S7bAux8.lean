import HRS.MC.S7S7bAux7
import HRS.Dynamics.InitialData

/-!
# Packet `s7_S7b_weighted_moments`, helper 8: `||h_v||_{L^2(mu x mu)} <= C ||v||_{H^1}`
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ComplexConjugate

noncomputable section

namespace HRS.MC.Sec7.S7b

open HRS HRS.Sec7 HRS.MC.SEdge HRS.PDE

variable {d : ℕ} {s : ℝ}

/-- Change of variables `y = x - z` in an iterated lintegral on the torus (Lebesgue measure). -/
theorem s7b_lintegral_shift (G : Torus d → Torus d → ℝ≥0∞) (hG : Measurable (Function.uncurry G)) :
    ∫⁻ x, ∫⁻ y, G x y = ∫⁻ z, ∫⁻ y, G (y + z) y := by
  have h1 : ∫⁻ x, ∫⁻ y, G x y = ∫⁻ y, ∫⁻ x, G x y :=
    lintegral_lintegral_swap hG.aemeasurable
  have h2 : ∀ y : Torus d, ∫⁻ x, G x y = ∫⁻ z, G (y + z) y := fun y =>
    (lintegral_add_left_eq_self (μ := (volume : Measure (Torus d))) (fun x => G x y) y).symm
  simp_rw [h2] at h1
  rw [h1]
  refine lintegral_lintegral_swap ?_
  have : Measurable (fun p : Torus d × Torus d => G (p.1 + p.2) p.1) :=
    hG.comp ((measurable_fst.add measurable_snd).prodMk measurable_fst)
  exact this.aemeasurable

/-- Comparison of the integral against `withDensityReal ρ` with Lebesgue. -/
theorem s7b_lintegral_density_le {ρ : Torus d → ℝ} {Λ : ℝ} (hΛ : ∀ x, ρ x ≤ Λ)
    (f : Torus d → ℝ≥0∞) :
    ∫⁻ x, f x ∂(withDensityReal ρ) ≤ ENNReal.ofReal Λ * ∫⁻ x, f x := by
  calc ∫⁻ x, f x ∂(withDensityReal ρ) ≤ ∫⁻ x, f x ∂(ENNReal.ofReal Λ • (volume : Measure (Torus d))) :=
        lintegral_mono' (withDensityReal_le_smul hΛ) le_rfl
    _ = _ := by rw [lintegral_smul_measure, smul_eq_mul]

theorem s7b_hv_sq_le {v : Fin d → Torus d → ℝ} (x y : Torus d) :
    Q66.q66_hv d s v x y ^ 2 ≤
      ‖periodicRieszGrad d s (x - y)‖ ^ 2 * ∑ j, (v j x - v j y) ^ 2 := by
  unfold Q66.q66_hv
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin d))
    (fun j => v j x - v j y) (fun j => (periodicRieszGrad d s (x - y)) j)
  have hn : ‖periodicRieszGrad d s (x - y)‖ ^ 2 = ∑ j, (periodicRieszGrad d s (x - y)) j ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [Real.norm_eq_abs, sq_abs]
  rw [hn, mul_comm]
  exact h

end HRS.MC.Sec7.S7b

end
