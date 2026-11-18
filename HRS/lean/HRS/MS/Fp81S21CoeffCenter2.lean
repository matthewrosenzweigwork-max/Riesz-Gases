import HRS.MS.Fp81S21CoeffCenter

/-! Bochner centering of the selected Gaussian coefficient representative and
its physical chart embedding. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

/-- The coordinate representative for the Gaussian linear field has zero
Bochner mean, as does its physical chart embedding. Both representatives also
retain the strong and weak first-moment bounds. -/
theorem fp81s21_gaussian_coord_firstMoment_center (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∀ Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4),
      ∀ E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2),
        ∃ M : ℝ, 0 ≤ M ∧ ∀ G : GaussianRealization R,
          ∃ q : ℝ → G.Ω → r26t6_Coeff,
            fp81s21_MomentRep Es G.P
              (fun u ω f => OscDual.eval (G.Z u ω) f) q M ∧
            (∀ u, 0 ≤ u → ∀ j, ∀ᵐ ω ∂G.P,
              q u ω j = OscDual.eval (G.Z u ω) (Es.test j)) ∧
            fp81s21_MomentRep E G.P
              (fun u ω f => OscDual.eval (G.Z u ω) f)
              (fun u ω => fp81s21_gaussian_chartEmbed p Es E (q u ω)) M ∧
            (∀ u, 0 ≤ u →
              (AEMeasurable (fun ω => dualNormE (2 * p.d + 6)
                ((p.d : ℝ) + 4)
                (fun f => OscDual.eval (G.Z u ω) f)) G.P ∧
                (∫⁻ ω, dualNormE (2 * p.d + 6) ((p.d : ℝ) + 4)
                  (fun f => OscDual.eval (G.Z u ω) f) ∂G.P) ≤
                  ENNReal.ofReal (Real.sqrt M)) ∧
              (AEMeasurable (fun ω => dualNormE (2 * p.d + 8)
                ((p.d : ℝ) + 2)
                (fun f => OscDual.eval (G.Z u ω) f)) G.P ∧
                (∫⁻ ω, dualNormE (2 * p.d + 8) ((p.d : ℝ) + 2)
                  (fun f => OscDual.eval (G.Z u ω) f) ∂G.P) ≤
                  ENNReal.ofReal (Real.sqrt M)) ∧
              (∫ ω, q u ω ∂G.P) = 0 ∧
              (∫ ω, fp81s21_gaussian_chartEmbed p Es E (q u ω) ∂G.P) = 0) := by
  obtain ⟨δc, hδc, hδchalf, hCoordinates⟩ :=
    fp81s21_gaussian_strong_coord p
  obtain ⟨δg, hδg, hδghalf, hGaussianLaw⟩ :=
    fp81s21_gaussLin_test_gaussian_law p
  refine ⟨min δc δg, lt_min hδc hδg,
    (min_le_left _ _).trans hδchalf, ?_⟩
  intro δ hδ hδle R Es E
  obtain ⟨M, hM, hCoordRep⟩ := hCoordinates δ hδ
    (hδle.trans (min_le_left _ _)) R Es E
  have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by nlinarith [p.hd]
  have hPs : (p.d : ℝ) < 2 * ((p.d : ℝ) + 4) := by nlinarith [p.hd]
  have hWeakRep : ∀ G : GaussianRealization R,
      ∀ q : ℝ → G.Ω → r26t6_Coeff,
        fp81s21_MomentRep Es G.P
            (fun u ω f => OscDual.eval (G.Z u ω) f) q M →
        fp81s21_MomentRep E G.P
            (fun u ω f => OscDual.eval (G.Z u ω) f)
            (fun u ω => fp81s21_gaussian_chartEmbed p Es E (q u ω)) M := by
    intro G q hRep
    simpa [fp81s21_gaussian_chartEmbed] using
      (fp81s21_MomentRep_embedField_normalized
        (d := p.d) (r := 2 * p.d + 6) (r' := 2 * p.d + 8)
        (Pw := (p.d : ℝ) + 2) (Ps := (p.d : ℝ) + 4)
        (by omega) (by ring) hP hPs Es E G.P
        (fun u ω f => OscDual.eval (G.Z u ω) f) q M hRep)
  refine ⟨M, hM, ?_⟩
  intro G
  obtain ⟨q, hRep, hCoord⟩ := hCoordRep G
  have hWeak := hWeakRep G q hRep
  refine ⟨q, hRep, hCoord, hWeak, ?_⟩
  intro u hu
  have hFirstStrong := fp81s21_MomentRep_firstMoment Es G.P
    (fun u ω f => OscDual.eval (G.Z u ω) f) q M hRep u hu
  have hFirstWeak := fp81s21_MomentRep_firstMoment E G.P
    (fun u ω f => OscDual.eval (G.Z u ω) f)
    (fun u ω => fp81s21_gaussian_chartEmbed p Es E (q u ω)) M hWeak u hu
  have hCoordinateMean : ∀ j : ℕ, ∫ ω, q u ω j ∂G.P = 0 := by
    intro j
    let φ : Euc p.d → ℝ := Es.test j
    have hφ : IsOscTest (wholeSpaceIndex p.d : ℝ) φ :=
      r2Test_isOscTest _ (Es.test_smooth j)
    obtain ⟨v, hMap⟩ := hGaussianLaw δ hδ
      (hδle.trans (min_le_right _ _)) R G u hu φ hφ
    have hEvalMeas : Measurable
        (fun ω => OscDual.eval (G.Z u ω) φ) := by
      let phi : HRS.MS.S111X1.oscSub p.d (wholeSpaceIndex p.d : ℝ) := ⟨φ, hφ⟩
      have heq : (fun ω => OscDual.eval (G.Z u ω) φ) =
          HRS.MS.ProClosureS111.gaussianOscEval phi ∘ G.Z u := by
        funext ω
        exact (HRS.MS.ProClosureS111.gaussianOscEval_apply phi (G.Z u ω)).symm
      rw [heq]
      exact (HRS.MS.ProClosureS111.gaussianOscEval phi).continuous.measurable.comp
        ((G.evolution (u + 1)).meas u)
    have hEvalMean :
        (∫ ω, OscDual.eval (G.Z u ω) φ ∂G.P) = 0 := by
      calc
        _ = ∫ x, x ∂G.P.map (fun ω => OscDual.eval (G.Z u ω) φ) := by
          symm
          exact integral_map hEvalMeas.aemeasurable
            measurable_id'.aestronglyMeasurable
        _ = ∫ x, x ∂gaussianReal 0 v := by rw [hMap]
        _ = 0 := by simp
    have hcoordj : (fun ω => q u ω j) =ᵐ[G.P]
        (fun ω => OscDual.eval (G.Z u ω) (Es.test j)) := hCoord u hu j
    calc
      _ = ∫ ω, OscDual.eval (G.Z u ω) φ ∂G.P := by
        exact integral_congr_ae hcoordj
      _ = 0 := hEvalMean
  have hqInt : Integrable (q u) G.P :=
    (hRep.2 u hu).1.integrable one_le_two
  have hStrongMean : (∫ ω, q u ω ∂G.P) = 0 := by
    apply lp.ext (funext fun j => ?_)
    have hComm :=
      (lp.evalCLM ℝ (fun _ : ℕ => ℝ) (2 : ℝ≥0∞) j).integral_comp_comm hqInt
    change (∫ ω, q u ω j ∂G.P) = (∫ ω, q u ω ∂G.P) j at hComm
    rw [hCoordinateMean j] at hComm
    exact hComm.symm
  let K : r26t6_Coeff →L[ℝ] r26t6_Coeff :=
    fp81s21_gaussian_chartEmbed p Es E
  have hWeakMean : (∫ ω, K (q u ω) ∂G.P) = 0 := by
    rw [K.integral_comp_comm hqInt, hStrongMean]
    simp
  exact ⟨hFirstStrong, hFirstWeak, hStrongMean, by simpa [K] using hWeakMean⟩

#print axioms HRS.Fp81.S21.fp81s21_gaussian_coord_firstMoment_center

end HRS.Fp81.S21

end
