import HRS.MS.Fp81S21CoeffMoments10
import HRS.MS.Fp81S21CoeffMoments8

/-! First-moment consequences for the selected Gaussian and particle
coefficient representatives. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

/-- The Gaussian coefficient representatives from the uniform sixth-moment
certificate also satisfy the strong and embedded physical first-moment
bounds. The coefficient representative and both moment constants are those
provided by `fp81s21_gaussian_six_momentRep`. -/
theorem fp81s21_gaussian_firstMomentRep (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∀ Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4),
      ∀ E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2),
        ∃ M2 M6 : ℝ, 0 ≤ M2 ∧ 0 ≤ M6 ∧
          ∀ G : GaussianRealization R,
            ∃ q : ℝ → G.Ω → r26t6_Coeff,
              fp81s21_MomentRep Es G.P
                (fun u ω f => OscDual.eval (G.Z u ω) f) q M2 ∧
              fp81s21_Six G.P q M6 ∧
              fp81s21_MomentRep E G.P
                (fun u ω f => OscDual.eval (G.Z u ω) f)
                (fun u ω => fp81s21_gaussian_chartEmbed p Es E (q u ω)) M2 ∧
              fp81s21_Six G.P
                (fun u ω => fp81s21_gaussian_chartEmbed p Es E (q u ω)) M6 ∧
              (∀ u, 0 ≤ u →
                AEMeasurable (fun ω => dualNormE (2 * p.d + 6)
                  ((p.d : ℝ) + 4)
                  (fun f => OscDual.eval (G.Z u ω) f)) G.P ∧
                (∫⁻ ω, dualNormE (2 * p.d + 6) ((p.d : ℝ) + 4)
                  (fun f => OscDual.eval (G.Z u ω) f) ∂G.P) ≤
                  ENNReal.ofReal (Real.sqrt M2)) ∧
              (∀ u, 0 ≤ u →
                AEMeasurable (fun ω => dualNormE (2 * p.d + 8)
                  ((p.d : ℝ) + 2)
                  (fun f => OscDual.eval (G.Z u ω) f)) G.P ∧
                (∫⁻ ω, dualNormE (2 * p.d + 8) ((p.d : ℝ) + 2)
                  (fun f => OscDual.eval (G.Z u ω) f) ∂G.P) ≤
                  ENNReal.ofReal (Real.sqrt M2)) := by
  obtain ⟨δ0, hδ0, hδhalf, hUniform⟩ := fp81s21_gaussian_six_momentRep p
  refine ⟨δ0, hδ0, hδhalf, ?_⟩
  intro δ hδ hδle R Es E
  obtain ⟨M2, M6, hM2, hM6, hForG⟩ := hUniform δ hδ hδle R Es E
  refine ⟨M2, M6, hM2, hM6, ?_⟩
  intro G
  obtain ⟨q, hStrong, hSixStrong, hWeak, hSixWeak⟩ := hForG G
  refine ⟨q, hStrong, hSixStrong, hWeak, hSixWeak, ?_, ?_⟩
  · intro u hu
    exact fp81s21_MomentRep_firstMoment Es G.P
      (fun u ω f => OscDual.eval (G.Z u ω) f) q M2 hStrong u hu
  · intro u hu
    exact fp81s21_MomentRep_firstMoment E G.P
      (fun u ω f => OscDual.eval (G.Z u ω) f)
      (fun u ω => fp81s21_gaussian_chartEmbed p Es E (q u ω)) M2
      hWeak u hu

/-- Strong and physical first-moment bounds for all three coefficient fields
in the embedded particle certificate, including the centered quadratic field.
The raw quadratic field remains present only as a moment field; this theorem
makes no centering assertion about it. -/
theorem fp81s21_particleCoeffMoments_firstMoment (p : Parameters)
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
                (∀ u, 0 ≤ u →
                  AEMeasurable (fun ω => dualNormE (2 * p.d + 6)
                    ((p.d : ℝ) + 4) (Q u ω)) A.P ∧
                  (∫⁻ ω, dualNormE (2 * p.d + 6) ((p.d : ℝ) + 4)
                    (Q u ω) ∂A.P) ≤ ENNReal.ofReal (Real.sqrt M2)) ∧
                fp81s21_Six A.P qs M6 ∧
                fp81s21_MomentRep E A.P Q
                  (fun u ω => fp81s21_embedField
                    (by nlinarith [p.hd]) (by nlinarith [p.hd])
                    (by
                      have hExp : ((p.d : ℝ) + 2) + 2 = (p.d : ℝ) + 4 := by ring
                      exact hExp.symm ▸ Es)
                    E (qs u ω)) M2 ∧
                (∀ u, 0 ≤ u →
                  AEMeasurable (fun ω => dualNormE (2 * p.d + 8)
                    ((p.d : ℝ) + 2) (Q u ω)) A.P ∧
                  (∫⁻ ω, dualNormE (2 * p.d + 8) ((p.d : ℝ) + 2)
                    (Q u ω) ∂A.P) ≤ ENNReal.ofReal (Real.sqrt M2)) ∧
                fp81s21_Six A.P
                  (fun u ω => fp81s21_embedField
                    (by nlinarith [p.hd]) (by nlinarith [p.hd])
                    (by
                      have hExp : ((p.d : ℝ) + 2) + 2 = (p.d : ℝ) + 4 := by ring
                      exact hExp.symm ▸ Es)
                    E (qs u ω)) M6 := by
  obtain ⟨δ0, hδ0, hδhalf, hUniform⟩ :=
    fp81s21_particleCoeffMoments_embedded p Es
  refine ⟨δ0, hδ0, hδhalf, ?_⟩
  intro δ hδ hδle R
  obtain ⟨M2, M6, hM2, hM6, hFor⟩ := hUniform δ hδ hδle R
  refine ⟨M2, M6, hM2, hM6, ?_⟩
  intro E N hN A Q hQ
  obtain ⟨qs, hStrong, hSixStrong, hWeak, hSixWeak, hFirstWeak⟩ :=
    hFor E N hN A Q hQ
  refine ⟨qs, hStrong, ?_, hSixStrong, hWeak, hFirstWeak, hSixWeak⟩
  intro u hu
  exact fp81s21_MomentRep_firstMoment Es A.P Q qs M2 hStrong u hu

#print axioms HRS.Fp81.S21.fp81s21_gaussian_firstMomentRep
#print axioms HRS.Fp81.S21.fp81s21_particleCoeffMoments_firstMoment

end HRS.Fp81.S21

end
