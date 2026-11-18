import HRS.MS.Fp81S21GaussianQuadraticHilbert4
import HRS.MC.E213U13k

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology
open scoped ENNReal BigOperators
open HRS HRS.MC.E213U13 HRS.MS.R26T6
namespace HRS.Fp81.S21

/-- A dominated time integral of bounded functionals of a coefficient
second-chaos field stays in the same scalar second chaos. -/
theorem fp81s21_InQ2_coeff_time_integral
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} (hξ : IsStdGaussianSeq P ξ)
    (ν : Measure ℝ) [SFinite ν] (q : ℝ → Ω → r26t6_Coeff)
    (hqmeas : Measurable (fun p : Ω × ℝ => q p.2 p.1))
    (hqcoord : ∀ᵐ t ∂ν, MemLp (q t) 2 P ∧ ∀ j, InQ2 hξ (fun ω => q t ω j))
    (hqint : ∀ᵐ ω ∂P, Integrable (fun t => ‖q t ω‖) ν)
    (hqL2 : MemLp (fun ω => ∫ t, ‖q t ω‖ ∂ν) 2 P)
    (ℓ : ℝ → r26t6_Coeff →L[ℝ] ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hℓ : ∀ t, ‖ℓ t‖ ≤ C)
    (hℓmeas : Measurable (fun p : ℝ × r26t6_Coeff => ℓ p.1 p.2))
    {Z : Ω → ℝ} (hZ : MemLp Z 2 P)
    (hZeq : Z =ᵐ[P] fun ω => ∫ t, ℓ t (q t ω) ∂ν) : InQ2 hξ Z := by
  let g : Ω → ℝ → ℝ := fun ω t => ℓ t (q t ω)
  let B : Ω → ℝ → ℝ := fun ω t => C * ‖q t ω‖
  have hgm : Measurable (Function.uncurry g) :=
    hℓmeas.comp (measurable_snd.prodMk hqmeas)
  refine InQ2.of_prod_limit (ν := ν) (f := fun _ => g) (g := g) (B := B)
    hZ (fun _ => hgm) hgm (measurable_const.mul hqmeas.norm) ?_ ?_ ?_ ?_ ?_ ?_ hZeq
  · intro ω t
    exact mul_nonneg hC (norm_nonneg _)
  · intro n
    filter_upwards [hqcoord] with t ht
    exact fp81s21_InQ2_coeff_functional hξ (q t) ht.1 ht.2 (ℓ t)
  · intro ω t
    exact tendsto_const_nhds
  · intro n ω t
    change |ℓ t (q t ω)| ≤ C * ‖q t ω‖
    rw [← Real.norm_eq_abs]
    exact ((ℓ t).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hℓ t) (norm_nonneg _))
  · filter_upwards [hqint] with ω hω
    exact hω.const_mul C
  · have he : (fun ω => ∫ t, B ω t ∂ν) = fun ω => C * ∫ t, ‖q t ω‖ ∂ν := by
      funext ω
      exact integral_const_mul _ _
    rw [he]
    exact hqL2.const_mul C

#print axioms fp81s21_InQ2_coeff_time_integral
end HRS.Fp81.S21
end
