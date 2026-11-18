import HRS.MS.Fp81S21ResponseAll
import HRS.MS.Fp81S21GaussianPhysicalPackage

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.S21E

/-- A radius property whose quantifiers range over every trajectory. -/
def fp81s21_Rad (p : Parameters)
    (F : ∀ δ : ℝ, Trajectory p δ → Prop) : Prop :=
  ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ R : Trajectory p δ, F δ R

/-- The five response conclusions, uniformly over all nonnegative starts,
together with symmetry of the initial cubic tensor. -/
def fp81s21_Response9 {p : Parameters} {δ : ℝ}
    (R : Trajectory p δ) (K : ℝ) : Prop :=
  letI : IsProbabilityMeasure (r26t3_mu R 0) :=
    fp81s21_initialMeasure_isProbability p R
  (∀ b : ℝ, 0 ≤ b →
    AEStronglyMeasurable (responseWindow R b) (r26t3_mu R 0) ∧
    Integrable (fun x => ‖responseWindow R b x‖ ^ 3) (r26t3_mu R 0) ∧
    (∀ x, ‖responseWindow R b x‖ ≤ K) ∧
    initialKappa R b ∈ projTensor (Window p) 3 ∧
    ‖initialKappa R b‖ ≤ K ^ 3) ∧
  (∀ b : ℝ, 0 ≤ b →
    ∀ σ : Equiv.Perm (Fin 3), ∀ M : (Window p) [×3]→L[ℝ] ℝ,
      initialKappa R b (M.domDomCongr σ) = initialKappa R b M)

/-- The literal drift mixed moment of a retained physical package. -/
def fp81s21_ID {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (Q : fp81s21_Physical35 p R) (a : ℝ) : ℝ :=
  ∫ ω, ‖fp81s21_physical35_D Q.tofp81s21_Gaussian35Selection Q.OD a ω‖ *
    ‖r26t3_Zpath Q.src.G0 a ω‖ * ‖r26t3_Zpath Q.src.G0 a ω‖ ∂Q.src.G0.P

/-- The literal covariance mixed moment of a retained physical package. -/
def fp81s21_IJ {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (Q : fp81s21_Physical35 p R) (a : ℝ) : ℝ :=
  ∫ ω, ‖fp81s21_physical35_J Q.tofp81s21_Gaussian35Selection Q.OJ a ω‖ *
    ‖r26t3_Zpath Q.src.G0 a ω‖ ∂Q.src.G0.P

/-- The response tensor and the two physical mixed moments obey the O1 bound. -/
theorem fp81s21_gaussian35_O1_moment_bound (p : Parameters) :
    fp81s21_Rad p (fun δ R =>
      letI : IsProbabilityMeasure (r26t3_mu R 0) :=
        fp81s21_initialMeasure_isProbability p R
      ∃ Kresponse : ℝ, 0 ≤ Kresponse ∧
        fp81s21_Response9 R Kresponse ∧
        ∀ Q : fp81s21_Physical35 p R, ∀ a : ℝ, 0 ≤ a →
          ‖initialKappa R a‖ + 3 * fp81s21_ID Q a + 3 * fp81s21_IJ Q a ≤
            Kresponse ^ 3 +
              3 * (Q.MD ^ (1 / 3 : ℝ) * Q.MZ ^ (1 / 2 : ℝ) +
                Q.MJ ^ (1 / 2 : ℝ) * Q.MZ ^ (1 / 4 : ℝ))) := by
  obtain ⟨δ₀, hδ₀, hδhalf, hresponse⟩ :=
    fp81s21_responseWindow_all_strengths p
  refine ⟨δ₀, hδ₀, hδhalf, ?_⟩
  intro δ hδ hδle R
  letI : IsProbabilityMeasure (r26t3_mu R 0) :=
    fp81s21_initialMeasure_isProbability p R
  obtain ⟨Kresponse, hKresponse, hresponseAll⟩ :=
    hresponse δ hδ hδle R
  have hResponse9 : fp81s21_Response9 R Kresponse := by
    refine ⟨hresponseAll, ?_⟩
    intro b hb σ M
    have hprod : Integrable
        (fun x : Euc p.d =>
          ‖responseWindow R b x‖ * ‖responseWindow R b x‖ *
            ‖responseWindow R b x‖) (r26t3_mu R 0) := by
      apply (hresponseAll b hb).2.1.congr
      filter_upwards with x
      ring
    simpa [initialKappa] using
      HRS.MS.S21E.s21e_kappa0_symm (r26t3_mu R 0)
        (hresponseAll b hb).1 hprod σ M
  refine ⟨Kresponse, hKresponse, hResponse9, ?_⟩
  intro Q a ha
  have hκ := (hresponseAll a ha).2.2.2.2
  have hmix :
      fp81s21_ID Q a + fp81s21_IJ Q a ≤
        Q.MD ^ (1 / 3 : ℝ) * Q.MZ ^ (1 / 2 : ℝ) +
          Q.MJ ^ (1 / 2 : ℝ) * Q.MZ ^ (1 / 4 : ℝ) := by
    simpa [fp81s21_ID, fp81s21_IJ] using Q.mixed_bound a ha
  calc
    ‖initialKappa R a‖ + 3 * fp81s21_ID Q a + 3 * fp81s21_IJ Q a
        ≤ Kresponse ^ 3 + 3 * (fp81s21_ID Q a + fp81s21_IJ Q a) := by
          nlinarith
    _ ≤ Kresponse ^ 3 +
        3 * (Q.MD ^ (1 / 3 : ℝ) * Q.MZ ^ (1 / 2 : ℝ) +
          Q.MJ ^ (1 / 2 : ℝ) * Q.MZ ^ (1 / 4 : ℝ)) := by
          nlinarith [hmix]

#print axioms HRS.Fp81.S21.fp81s21_gaussian35_O1_moment_bound

end HRS.Fp81.S21

end
