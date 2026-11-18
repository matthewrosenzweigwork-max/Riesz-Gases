import HRS.MS.Fp81S21GaussG4U44
import HRS.MS.Fp81S21Absorption

/-! Spatial integrability of the gradient of the propagated generator. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2WinErr HRS.MS.R2WinOrbNL HRS.MS.S111X2

theorem fp81s21_g4_generator_gradient_slice
    (p : Parameters) {δ q : ℝ} (R : Trajectory p δ)
    (hterm : S104bTermRegGen p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁)
    {f : Euc p.d → ℝ} (hf : IsR2DualCombo (wholeSpaceIndex p.d : ℝ) f)
    (hq : 0 ≤ q) (r : ℝ) (hr : r ∈ Icc (0 : ℝ) q) :
    Integrable (fun x => ‖gradient (r26t3_U R r q
      (generatorW (r26t3_coeff R) q f)) x‖ ^ 2)
      (HRS.Whole.withDensityReal R.ρβ) := by
  let μ := HRS.Whole.withDensityReal R.ρβ
  letI : IsProbabilityMeasure μ := HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  obtain ⟨S, c, hfS⟩ := hf
  have hex : ∃ u, IsClassicalAdjointW (r26t3_coeff R) q
      (generatorW (r26t3_coeff R) q f) u := by
    rw [hfS]
    exact (fp81s21_g4_generator_combo p R hterm hq le_rfl S c).2.1
  have hu : IsClassicalAdjointW (r26t3_coeff R) q
      (generatorW (r26t3_coeff R) q f)
      (fun r => r26t3_U R r q (generatorW (r26t3_coeff R) q f)) :=
    HRS.MS.Fcau.propagatorW_isClassical hex
  obtain ⟨B0, B1, B2, hB0, hB1, hB2, huB⟩ := HRS.MS.S111X1.classical_bounds hu
  have hcont : Continuous (gradient (r26t3_U R r q
      (generatorW (r26t3_coeff R) q f))) :=
    s111x2_gradient_continuous ((hu.c2 r hr).of_le (by norm_num))
  have hm : MemLp (gradient (r26t3_U R r q
      (generatorW (r26t3_coeff R) q f))) 2 μ := by
    apply MemLp.of_bound hcont.aestronglyMeasurable B1
    exact Filter.Eventually.of_forall fun x => by
      rw [s111x2_norm_gradient]
      exact (huB r hr x).2.1
  exact (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).1 hm

#print axioms fp81s21_g4_generator_gradient_slice
end HRS.Fp81.S21
end
