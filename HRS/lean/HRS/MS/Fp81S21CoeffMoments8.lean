import HRS.MS.Fp81S21CoeffMoments7
import HRS.MS.Fp81S21TimeRep15
import HRS.MS.Fp81S21WeightedMoments2

/-! The physical embedded form of the combined particle coefficient moments. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

/-- The combined particle coefficient moment certificate in both the strong
and physical charts.  Each selected field uses one and the same strong
representative for its second and sixth moment; its image under the chart
embedding has the same bounds.  The final clause gives the corresponding
first-moment estimate in the physical chart. -/
theorem fp81s21_particleCoeffMoments_embedded (p : Parameters)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4)) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ M2 M6 : ℝ, 0 ≤ M2 ∧ 0 ≤ M6 ∧
          ∀ E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2),
          ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N,
            ∀ Q ∈ ({fp81s21_particleEmpField R N A,
              fp81s21_particleQuadRawField R N A,
              fp81s21_particleQuadField R N A} :
              Set (ℝ → A.Ω → (Euc p.d → ℝ) → ℝ)),
              ∃ qs : ℝ → A.Ω → r26t6_Coeff,
                fp81s21_MomentRep Es A.P Q qs M2 ∧
                fp81s21_Six A.P qs M6 ∧
                fp81s21_MomentRep E A.P Q
                  (fun u ω => fp81s21_embedField
                    (by nlinarith [p.hd]) (by nlinarith [p.hd])
                    (by
                      have hExp : ((p.d : ℝ) + 2) + 2 = (p.d : ℝ) + 4 := by ring
                      exact hExp.symm ▸ Es)
                    E (qs u ω)) M2 ∧
                fp81s21_Six A.P
                  (fun u ω => fp81s21_embedField
                    (by nlinarith [p.hd]) (by nlinarith [p.hd])
                    (by
                      have hExp : ((p.d : ℝ) + 2) + 2 = (p.d : ℝ) + 4 := by ring
                      exact hExp.symm ▸ Es)
                    E (qs u ω)) M6 ∧
                (∀ u, 0 ≤ u →
                  AEMeasurable (fun ω => HRS.Whole.dualNormE
                    (2 * p.d + 8) ((p.d : ℝ) + 2) (Q u ω)) A.P ∧
                  (∫⁻ ω, HRS.Whole.dualNormE
                    (2 * p.d + 8) ((p.d : ℝ) + 2) (Q u ω) ∂A.P) ≤
                    ENNReal.ofReal (Real.sqrt M2)) := by
  obtain ⟨δ0, hδ0, hδhalf, hStrong⟩ :=
    fp81s21_particleCoeffMoments_strong p Es
  refine ⟨δ0, hδ0, hδhalf, ?_⟩
  intro δ hδ hδle R
  obtain ⟨M2, M6, hM2, hM6, hCommon⟩ := hStrong δ hδ hδle R
  refine ⟨M2, M6, hM2, hM6, ?_⟩
  intro E N hN A Q hQ
  obtain ⟨qs, hRep, hSix⟩ := hCommon N hN A Q hQ
  have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by nlinarith [p.hd]
  have hPs : (p.d : ℝ) < 2 * (((p.d : ℝ) + 2) + 2) := by
    nlinarith [p.hd]
  have hExp : ((p.d : ℝ) + 2) + 2 = (p.d : ℝ) + 4 := by ring
  let Es' : r26t6_WeightedChart p.d (2 * p.d + 6)
      (((p.d : ℝ) + 2) + 2) := hExp.symm ▸ Es
  let qE : ℝ → A.Ω → r26t6_Coeff := fun u ω =>
    fp81s21_embedField hP hPs Es' E (qs u ω)
  have hWeak : fp81s21_MomentRep E A.P Q qE M2 := by
    simpa [qE, Es'] using fp81s21_MomentRep_embedField_weight
      hP hPs Es hExp.symm E A.P Q qs M2 hRep
  have hWeakSix : fp81s21_Six A.P qE M6 := by
    simpa [qE] using fp81s21_Six_embedField hP hPs Es' E A.P qs M6 hSix
  have hFirst : ∀ u, 0 ≤ u →
      AEMeasurable (fun ω => HRS.Whole.dualNormE
        (2 * p.d + 8) ((p.d : ℝ) + 2) (Q u ω)) A.P ∧
      (∫⁻ ω, HRS.Whole.dualNormE
        (2 * p.d + 8) ((p.d : ℝ) + 2) (Q u ω) ∂A.P) ≤
        ENNReal.ofReal (Real.sqrt M2) := by
    intro u hu
    simpa using fp81s21_MomentRep_firstMoment E A.P Q qE M2 hWeak u hu
  exact ⟨qs, hRep, hSix, hWeak, hWeakSix, hFirst⟩

#print axioms HRS.Fp81.S21.fp81s21_particleCoeffMoments_embedded

end HRS.Fp81.S21

end
