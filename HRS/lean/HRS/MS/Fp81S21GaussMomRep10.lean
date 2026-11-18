import HRS.MS.Fp81S21GaussMomRep9
import HRS.MS.Fp81S21EmbedMom3

/-! Embedded weak-chart representation of the moving Gaussian field. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory
open scoped ENNReal

namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

def fp81s21_embedField_normalized {d r r' : ℕ} {Pw Ps : ℝ}
    (hr : r + 2 = r') (hp : Pw + 2 = Ps)
    (hP : (d : ℝ) < 2 * Pw) (hPs : (d : ℝ) < 2 * Ps)
    (Es : r26t6_WeightedChart d r Ps) (E : r26t6_WeightedChart d r' Pw) :
    r26t6_Coeff →L[ℝ] r26t6_Coeff := by
  subst r'
  subst Ps
  exact fp81s21_embedField hP hPs Es E

theorem fp81s21_MomentRep_embedField_normalized {d r r' : ℕ} {Pw Ps : ℝ}
    {Ω : Type*} [MeasurableSpace Ω]
    (hr : r + 2 = r') (hp : Pw + 2 = Ps)
    (hP : (d : ℝ) < 2 * Pw) (hPs : (d : ℝ) < 2 * Ps)
    (Es : r26t6_WeightedChart d r Ps) (E : r26t6_WeightedChart d r' Pw)
    (P : Measure Ω) (Q : ℝ → Ω → (Euc d → ℝ) → ℝ)
    (qs : ℝ → Ω → r26t6_Coeff) (M : ℝ)
    (hrep : fp81s21_MomentRep Es P Q qs M) :
    fp81s21_MomentRep E P Q
      (fun u ω => fp81s21_embedField_normalized hr hp hP hPs Es E (qs u ω)) M := by
  subst r'
  subst Ps
  exact fp81s21_MomentRep_embedField hP hPs Es E P Q qs M hrep

/-- The physical chart embedding, with the conventional normalized indices. -/
def fp81s21_gaussian_chartEmbed (p : Parameters)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2)) :
    r26t6_Coeff →L[ℝ] r26t6_Coeff :=
  fp81s21_embedField_normalized (by omega) (by ring)
    (by nlinarith) (by nlinarith) Es E

/-- One moment bound works for both the strong field and its embedded field. -/
theorem fp81s21_gaussian_momentRep_embedded (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∀ Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4),
      ∀ E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2),
        ∃ M : ℝ, 0 ≤ M ∧ ∀ G : GaussianRealization R,
          ∃ q : ℝ → G.Ω → r26t6_Coeff,
            fp81s21_MomentRep Es G.P (fun u ω f => OscDual.eval (G.Z u ω) f) q M ∧
            fp81s21_MomentRep E G.P (fun u ω f => OscDual.eval (G.Z u ω) f)
              (fun u ω => fp81s21_gaussian_chartEmbed p Es E (q u ω)) M := by
  obtain ⟨δ0, hδ0, hhalf, hstrong⟩ := fp81s21_gaussian_strong_momentRep p
  refine ⟨δ0, hδ0, hhalf, ?_⟩
  intro δ hδ hδle R Es E
  obtain ⟨M, hM, hG⟩ := hstrong δ hδ hδle R Es E
  refine ⟨M, hM, ?_⟩
  intro G
  obtain ⟨q, hq⟩ := hG G
  refine ⟨q, hq, ?_⟩
  exact fp81s21_MomentRep_embedField_normalized (by omega) (by ring)
    (by nlinarith) (by nlinarith) Es E G.P
      (fun u ω f => OscDual.eval (G.Z u ω) f) q M hq

#print axioms fp81s21_embedField_normalized
#print axioms fp81s21_MomentRep_embedField_normalized
#print axioms fp81s21_gaussian_chartEmbed
#print axioms fp81s21_gaussian_momentRep_embedded
end HRS.Fp81.S21
end
