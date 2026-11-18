import HRS.MS.Fp81S21WeightedMomentsS3
import HRS.MS.Fp81S21WeightedMomentsS4

/-! Shared strong-chart particle moment and first-moment export. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6

/-- The empirical and centered quadratic particle fields admit chart representatives
under one second-moment constant, with both first-moment consequences. -/
theorem fp81s21_particle_momentReps_strong (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ M : ℝ, 0 ≤ M ∧ ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N,
          ∀ E : r26t6_WeightedChart p.d (2 * p.d + 6)
              ((p.d : ℝ) + 4),
            ∃ qη qB : ℝ → A.Ω → r26t6_Coeff,
              fp81s21_MomentRep E A.P
                (fp81s21_particleEmpField R N A) qη M ∧
              fp81s21_MomentRep E A.P
                (fp81s21_particleQuadField R N A) qB M ∧
              ∀ u : ℝ, 0 ≤ u →
                AEMeasurable (fun ω => dualNormE (2 * p.d + 6)
                  ((p.d : ℝ) + 4)
                  (fp81s21_particleEmpField R N A u ω)) A.P ∧
                (∫⁻ ω, dualNormE (2 * p.d + 6) ((p.d : ℝ) + 4)
                  (fp81s21_particleEmpField R N A u ω) ∂A.P) ≤
                  ENNReal.ofReal (Real.sqrt M) ∧
                AEMeasurable (fun ω => dualNormE (2 * p.d + 6)
                  ((p.d : ℝ) + 4)
                  (fp81s21_particleQuadField R N A u ω)) A.P ∧
                (∫⁻ ω, dualNormE (2 * p.d + 6) ((p.d : ℝ) + 4)
                  (fp81s21_particleQuadField R N A u ω) ∂A.P) ≤
                  ENNReal.ofReal (Real.sqrt M) := by
  obtain ⟨δη, hδη, hδηhalf, hη⟩ := fp81s21_particle_eta_momentRep_strong p
  obtain ⟨δB, hδB, hδBhalf, hB⟩ := fp81s21_particle_quad_momentRep_strong p
  let δ0 : ℝ := min δη δB
  have hδ0 : 0 < δ0 := lt_min hδη hδB
  have hδ0half : δ0 ≤ 1 / 2 := (min_le_right _ _).trans hδBhalf
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R
  have hδleη : δ ≤ δη := hδle.trans (min_le_left _ _)
  have hδleB : δ ≤ δB := hδle.trans (min_le_right _ _)
  obtain ⟨Mη, hMη, hηR⟩ := hη δ hδ hδleη R
  obtain ⟨MB, hMB, hBR⟩ := hB δ hδ hδleB R
  let M : ℝ := Mη + MB
  have hM : 0 ≤ M := by dsimp [M]; positivity
  refine ⟨M, hM, ?_⟩
  intro N hN A E
  obtain ⟨qη, hηrep⟩ := hηR N hN A E
  obtain ⟨qB, hBrep⟩ := hBR N hN A E
  have hηrepM : fp81s21_MomentRep E A.P
      (fp81s21_particleEmpField R N A) qη M := by
    refine ⟨hηrep.1, ?_⟩
    intro u hu
    obtain ⟨hmem, hbound, hfields⟩ := hηrep.2 u hu
    refine ⟨hmem, hbound.trans ?_, hfields⟩
    exact le_add_of_nonneg_right hMB
  have hBrepM : fp81s21_MomentRep E A.P
      (fp81s21_particleQuadField R N A) qB M := by
    refine ⟨hBrep.1, ?_⟩
    intro u hu
    obtain ⟨hmem, hbound, hfields⟩ := hBrep.2 u hu
    refine ⟨hmem, hbound.trans ?_, hfields⟩
    exact le_add_of_nonneg_left hMη
  refine ⟨qη, qB, hηrepM, hBrepM, ?_⟩
  intro u hu
  have hηfirst := fp81s21_MomentRep_firstMoment E A.P
    (fp81s21_particleEmpField R N A) qη M hηrepM u hu
  have hBfirst := fp81s21_MomentRep_firstMoment E A.P
    (fp81s21_particleQuadField R N A) qB M hBrepM u hu
  exact ⟨hηfirst.1, hηfirst.2, hBfirst.1, hBfirst.2⟩


#print axioms HRS.Fp81.S21.fp81s21_particle_momentReps_strong

end HRS.Fp81.S21

end
