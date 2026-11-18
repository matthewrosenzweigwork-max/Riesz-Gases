import HRS.MS.Fp81S21CoeffCenter

/-! Centering of the strong and physical coefficient representatives of the
particle quadratic field centered against its actual law. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

private theorem fp81s21_chartAction_test_coordinate
    {d r : ℕ} {Pw : ℝ} (E : r26t6_WeightedChart d r Pw)
    (z : r26t6_Coeff) (j : ℕ) :
    fp81s21_chartAction E z (E.test j) = z j := by
  have hcoord : E.encode (E.test j) =
      (lp.single 2 j (1 : ℝ) : r26t6_Coeff) := by
    ext i
    change E.encode (E.test j) i = _
    rw [E.test_coord]
    simp [lp.single_apply, Pi.single_apply, eq_comm]
  rw [fp81s21_chartAction, hcoord]
  simpa [lp.inner_single_right]

private theorem fp81s21_r2QuadField_MomentRep_mean_zero
    {d r N : ℕ} {Pw s : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (E : r26t6_WeightedChart d r Pw) (μ : Measure (Euc d))
    (X : ℝ≥0 → Ω → EucConfig d N) (u : ℝ) (hN : 0 < N)
    (q : Ω → r26t6_Coeff)
    (hmem : MemLp q 2 P)
    (hrep : ∀ᵐ ω ∂P, ∀ f, IsR2Test f →
      fp81s21_chartAction E (q ω) f =
        HRS.Whole.r2QuadField s μ P X u ω f) :
    (∫ ω, q ω ∂P) = 0 := by
  have hqInt : Integrable q P := hmem.integrable one_le_two
  have hCoordinateMean : ∀ j : ℕ, ∫ ω, q ω j ∂P = 0 := by
    intro j
    let f : Euc d → ℝ := E.test j
    let g : Ω → ℝ := fun ω =>
      HRS.Whole.pairEnergy
        (HRS.Whole.commutatorKernel d s (fun x => gradient f x))
        (X u.toNNReal ω) μ
    let c : ℝ := ∫ ω, g ω ∂P
    have hFieldDef (ω : Ω) : HRS.Whole.r2QuadField s μ P X u ω f =
        (N : ℝ) * (g ω - c) := by
      rfl
    have hcoordAE : (fun ω => q ω j) =ᵐ[P]
        (fun ω => HRS.Whole.r2QuadField s μ P X u ω f) := by
      filter_upwards [hrep] with ω hω
      calc
        q ω j = fp81s21_chartAction E (q ω) (E.test j) :=
          (fp81s21_chartAction_test_coordinate E (q ω) j).symm
        _ = HRS.Whole.r2QuadField s μ P X u ω f :=
          hω (E.test j) (E.test_smooth j)
    let ev : r26t6_Coeff →L[ℝ] ℝ :=
      lp.evalCLM ℝ (fun _ : ℕ => ℝ) (2 : ℝ≥0∞) j
    have hcoordInt : Integrable (fun ω => q ω j) P := by
      have h := ev.integrable_comp hqInt
      change Integrable (fun ω => q ω j) P at h
      exact h
    have hfieldInt : Integrable
        (fun ω => HRS.Whole.r2QuadField s μ P X u ω f) P :=
      hcoordInt.congr hcoordAE
    have hNreal : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have hgEq : g = fun ω =>
        HRS.Whole.r2QuadField s μ P X u ω f / (N : ℝ) + c := by
      funext ω
      rw [hFieldDef ω]
      dsimp [c]
      field_simp [hNreal]
      ring
    have hgInt : Integrable g P := by
      rw [hgEq]
      exact (hfieldInt.div_const (N : ℝ)).add (integrable_const c)
    have hFieldMean :
        (∫ ω, HRS.Whole.r2QuadField s μ P X u ω f ∂P) = 0 := by
      have hfun : (fun ω => HRS.Whole.r2QuadField s μ P X u ω f) =
          fun ω => (N : ℝ) * (g ω - c) := funext hFieldDef
      rw [hfun, integral_const_mul,
        integral_sub hgInt (integrable_const c)]
      simp [c, IsProbabilityMeasure.measure_univ]
    calc
      _ = ∫ ω, HRS.Whole.r2QuadField s μ P X u ω f ∂P :=
        integral_congr_ae hcoordAE
      _ = 0 := hFieldMean
  apply lp.ext (funext fun j => ?_)
  have hComm :=
    (lp.evalCLM ℝ (fun _ : ℕ => ℝ) (2 : ℝ≥0∞) j).integral_comp_comm hqInt
  change (∫ ω, q ω j ∂P) = (∫ ω, q ω ∂P) j at hComm
  rw [hCoordinateMean j] at hComm
  exact hComm.symm

/-- The strong coefficient representative of the centered particle quadratic
field has zero Bochner mean. Its physical chart embedding has zero Bochner
mean as well. The same representatives retain first-moment control. -/
theorem fp81s21_particleQuadCoeff_firstMoment_centered (p : Parameters)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4)) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ M2 M6 : ℝ, 0 ≤ M2 ∧ 0 ≤ M6 ∧
          ∀ E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2),
          ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N,
            ∃ qB : ℝ → A.Ω → r26t6_Coeff,
              fp81s21_MomentRep Es A.P
                (fp81s21_particleQuadField R N A) qB M2 ∧
              (∀ u, 0 ≤ u →
                (AEMeasurable (fun ω => dualNormE (2 * p.d + 6)
                  ((p.d : ℝ) + 4)
                  (fp81s21_particleQuadField R N A u ω)) A.P ∧
                  (∫⁻ ω, dualNormE (2 * p.d + 6) ((p.d : ℝ) + 4)
                    (fp81s21_particleQuadField R N A u ω) ∂A.P) ≤
                    ENNReal.ofReal (Real.sqrt M2)) ∧
                (∫ ω, qB u ω ∂A.P) = 0) ∧
              fp81s21_MomentRep E A.P
                (fp81s21_particleQuadField R N A)
                (fun u ω => fp81s21_embedField
                  (by nlinarith [p.hd]) (by nlinarith [p.hd])
                  (by
                    have hExp : ((p.d : ℝ) + 2) + 2 = (p.d : ℝ) + 4 := by ring
                    exact hExp.symm ▸ Es)
                  E (qB u ω)) M2 ∧
              (∀ u, 0 ≤ u →
                (AEMeasurable (fun ω => dualNormE (2 * p.d + 8)
                  ((p.d : ℝ) + 2)
                  (fp81s21_particleQuadField R N A u ω)) A.P ∧
                  (∫⁻ ω, dualNormE (2 * p.d + 8) ((p.d : ℝ) + 2)
                    (fp81s21_particleQuadField R N A u ω) ∂A.P) ≤
                    ENNReal.ofReal (Real.sqrt M2)) ∧
                (∫ ω, fp81s21_embedField
                  (by nlinarith [p.hd]) (by nlinarith [p.hd])
                  (by
                    have hExp : ((p.d : ℝ) + 2) + 2 = (p.d : ℝ) + 4 := by ring
                    exact hExp.symm ▸ Es)
                  E (qB u ω) ∂A.P) = 0) := by
  obtain ⟨δ0, hδ0, hδhalf, hUniform⟩ :=
    fp81s21_particleCoeffMoments_embedded p Es
  refine ⟨δ0, hδ0, hδhalf, ?_⟩
  intro δ hδ hδle R
  obtain ⟨M2, M6, hM2, hM6, hFor⟩ := hUniform δ hδ hδle R
  refine ⟨M2, M6, hM2, hM6, ?_⟩
  intro E N hN A
  have hNpos : 0 < N := lt_of_lt_of_le (by decide) hN
  have hQmem : fp81s21_particleQuadField R N A ∈
      ({fp81s21_particleEmpField R N A,
        fp81s21_particleQuadRawField R N A,
        fp81s21_particleQuadField R N A} :
        Set (ℝ → A.Ω → (Euc p.d → ℝ) → ℝ)) := by simp
  obtain ⟨qB, hStrong, hSix, hWeak, hSixWeak, hFirstWeak⟩ :=
    hFor E N hN A (fp81s21_particleQuadField R N A) hQmem
  refine ⟨qB, hStrong, ?_, hWeak, ?_⟩
  · intro u hu
    have hFirstStrong := fp81s21_MomentRep_firstMoment Es A.P
      (fp81s21_particleQuadField R N A) qB M2 hStrong u hu
    have hmean := fp81s21_r2QuadField_MomentRep_mean_zero
      (E := Es) (μ := r26t3_mu R u) (X := A.X) (u := u) hNpos
      (qB u) ((hStrong.2 u hu).1)
      ((hStrong.2 u hu).2.2.mono fun ω hω => hω.1)
    exact ⟨hFirstStrong, hmean⟩
  · intro u hu
    have hfirst := hFirstWeak u hu
    have hMeanStrong := fp81s21_r2QuadField_MomentRep_mean_zero
      (E := Es) (μ := r26t3_mu R u) (X := A.X) (u := u) hNpos
      (qB u) ((hStrong.2 u hu).1)
      ((hStrong.2 u hu).2.2.mono fun ω hω => hω.1)
    let K : r26t6_Coeff →L[ℝ] r26t6_Coeff :=
      fp81s21_embedField
        (by nlinarith [p.hd]) (by nlinarith [p.hd])
        (by
          have hExp : ((p.d : ℝ) + 2) + 2 = (p.d : ℝ) + 4 := by ring
          exact hExp.symm ▸ Es) E
    have hqInt : Integrable (qB u) A.P :=
      (hStrong.2 u hu).1.integrable one_le_two
    have hMeanWeak : (∫ ω, K (qB u ω) ∂A.P) = 0 := by
      rw [K.integral_comp_comm hqInt, hMeanStrong]
      simp
    exact ⟨hfirst, by simpa [K] using hMeanWeak⟩

#print axioms HRS.Fp81.S21.fp81s21_particleQuadCoeff_firstMoment_centered

end HRS.Fp81.S21

end
