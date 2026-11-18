import HRS.MS.Fp81S21Absorption
import HRS.MS.S21F_C00

/-! The integrated gradient energy budget for classical adjoints. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.S111X2

theorem fp81s21_g4_adjoint_energy (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∃ B : ℝ, 0 < B ∧ ∀ H : ℝ, 0 < H →
        ∀ (g : Euc p.d → ℝ) (u : ℝ → Euc p.d → ℝ),
        IsClassicalAdjointW (r26t3_coeff R) H g u →
        MemLp g 2 (HRS.Whole.withDensityReal R.ρβ) →
        IntegrableOn (fun r => ∫ x, ‖gradient (u r) x‖ ^ 2
          ∂HRS.Whole.withDensityReal R.ρβ) (Icc (0 : ℝ) H) ∧
        (∫ r in Icc (0 : ℝ) H, ∫ x, ‖gradient (u r) x‖ ^ 2
          ∂HRS.Whole.withDensityReal R.ρβ) ≤
          B * ∫ x, (g x)^2 ∂HRS.Whole.withDensityReal R.ρβ := by
  obtain ⟨δ0, Q, C, c, hδ0, hhalf, hQ, hQδ, hC, hc, henergy⟩ :=
    sol13_uniform_adjoint_energy p
  refine ⟨δ0, hδ0, hhalf, ?_⟩
  intro δ hδ hδle R
  let μ := HRS.Whole.withDensityReal R.ρβ
  letI : IsProbabilityMeasure μ := HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  obtain ⟨a, B, ha, hB, hb⟩ := r26t3_energy_bounds R
  refine ⟨B, hB, ?_⟩
  intro H hH g u hu hg
  obtain ⟨B0, B1, B2, hB0, hB1, hB2, huB⟩ :=
    HRS.MS.S111X1.classical_bounds hu
  have hu0 : MemLp (u 0) 2 μ :=
    (MemLp.of_bound (hu.c2 0 ⟨le_rfl, hH.le⟩).continuous.aestronglyMeasurable B0
      (Filter.Eventually.of_forall fun x => (huB 0 ⟨le_rfl, hH.le⟩ x).1)).mono_exponent le_top
  have hnonneg : 0 ≤ r26t3_energy R (u 0) := by
    have h := (hb (u 0) hu0).1
    have hs : 0 ≤ ∫ x, (HRS.Whole.projMean μ (u 0) x)^2 ∂μ :=
      integral_nonneg fun x => sq_nonneg _
    exact (mul_nonneg ha.le hs).trans h
  have hbound := henergy δ hδ hδle R H hH g u hu
  refine ⟨hbound.2.2.1, ?_⟩
  have he := (hbound.2.2.2 0 ⟨le_rfl, hH.le⟩).1
  have hgenergy := (hb g hg).2
  have hcent := s111x2_cs_le_sq hg
  change (∫ x, (HRS.Whole.projMean μ g x)^2 ∂μ) ≤ _ at hcent
  have hmul := mul_le_mul_of_nonneg_left hcent hB.le
  linarith

#print axioms fp81s21_g4_adjoint_energy
end HRS.Fp81.S21
end
