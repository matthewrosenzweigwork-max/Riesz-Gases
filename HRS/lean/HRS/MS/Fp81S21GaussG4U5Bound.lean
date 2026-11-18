import HRS.MS.Fp81S21GaussG4U5Cost
import HRS.MS.Fp81S21GaussG4U5Energy
import HRS.MS.Fp81S21GaussG4U2
import HRS.MS.Fp81S21GaussG4U44
import HRS.MS.ProClosureS111ChartedOrbits

/-! The energy budget applied to generators of finite oscillator combinations. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2WinErr HRS.MS.R2WinOrbNL

theorem fp81s21_g4_generator_energy (p : Parameters) :
    fp81s21_g4Phys p (fun _ R =>
      ∃ A : ℝ, 0 ≤ A ∧ ∀ f, IsR2DualCombo (wholeSpaceIndex p.d : ℝ) f →
        ∀ q : ℝ, 0 < q →
        IntegrableOn (fun r => ∫ x, ‖gradient (r26t3_U R r q
          (generatorW (r26t3_coeff R) q f)) x‖^2
            ∂HRS.Whole.withDensityReal R.ρβ) (Icc (0 : ℝ) q) ∧
        (∫ r in Icc (0 : ℝ) q, ∫ x, ‖gradient (r26t3_U R r q
          (generatorW (r26t3_coeff R) q f)) x‖^2
            ∂HRS.Whole.withDensityReal R.ρβ) ≤ A * fp81s21_g4_J p.d f) := by
  obtain ⟨δe, hδe, hehalf, he⟩ := fp81s21_g4_adjoint_energy p
  obtain ⟨δg, hδg, hghalf, hg⟩ := fp81s21_g4_generator p
  obtain ⟨δc, C, c, hδc, hchalf, hc, hcommon⟩ := fp81s21_common_radius p
  refine ⟨min δe (min δg δc), lt_min hδe (lt_min hδg hδc),
    (min_le_left _ _).trans hehalf, ?_⟩
  intro δ hδ hδle R
  have hδe' := hδle.trans (min_le_left δe (min δg δc))
  have hδg' := hδle.trans ((min_le_right δe (min δg δc)).trans (min_le_left δg δc))
  have hδc' := hδle.trans ((min_le_right δe (min δg δc)).trans (min_le_right δg δc))
  obtain ⟨B, hB, hbudget⟩ := he δ hδ hδe' R
  obtain ⟨D, hD, hgen⟩ := hg δ hδ hδg' R
  obtain ⟨_, _, hterm, _⟩ := hcommon δ hδ hδc' R.ρβ R.thermal
  refine ⟨B * D, mul_nonneg hB.le hD, ?_⟩
  intro f hf q hq
  have hfosc := HRS.MS.ProClosureS111.dualCombo_isOscTest hf
  obtain ⟨hm, hgrad, hbound⟩ := hgen q hq.le f hfosc
  have hgrad0 : 0 ≤ ∫ x, ‖gradient f x‖^2 ∂HRS.Whole.withDensityReal R.ρβ :=
    integral_nonneg fun x => sq_nonneg _
  have hcost : (∫ x, (generatorW (r26t3_coeff R) q f x)^2
      ∂HRS.Whole.withDensityReal R.ρβ) ≤ D * fp81s21_g4_J p.d f := by
    rw [← fp81s21_g4_cost_eq]
    linarith
  obtain ⟨S, coeff, hfS⟩ := hf
  have hex : ∃ u, IsClassicalAdjointW (r26t3_coeff R) q
      (generatorW (r26t3_coeff R) q f) u := by
    rw [hfS]
    exact (fp81s21_g4_generator_combo p R hterm hq.le le_rfl S coeff).2.1
  have hu : IsClassicalAdjointW (r26t3_coeff R) q
      (generatorW (r26t3_coeff R) q f)
      (fun r => r26t3_U R r q (generatorW (r26t3_coeff R) q f)) :=
    HRS.MS.Fcau.propagatorW_isClassical hex
  obtain ⟨hi, hb⟩ := hbudget q hq _ _ hu hm
  refine ⟨hi, hb.trans ?_⟩
  nlinarith [mul_le_mul_of_nonneg_left hcost hB.le]

#print axioms fp81s21_g4_generator_energy
end HRS.Fp81.S21
end
