import HRS.MS.Fp81S21CovRS5
import HRS.MS.Fp81S21MovingAllInputs
import HRS.MS.Fp81S21MovingHeat4

/-! One common radius and future for the physical covariance RS families. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
open scoped BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp

/-- The physical prediction and raw-eta covariance cumulative admit specified
projected covariance RS windows under one common radius and one selected heat
future. The selected values have the exact integrable supremum-times-variation
majorant, uniformly over projection levels. -/
def fp81s21_moving_covariance_rsbv_statement (p : Parameters) : Prop :=
  ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∃ future : (H : ℝ) → ℝ →
          Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H),
        fp81s21_moving_heat_full_clause p R future ∧
        ∀ (a : ℝ) (ha : 0 ≤ a) (hH : 0 < a + p.T)
          (N : ℕ) (hN : 2 ≤ N) (A : Particle R N) (F : FilteredParticle A),
          let H : ℝ := a + p.T
          let B_H := OscPath p.d (wholeSpaceIndex p.d : ℝ) H
          letI : CompleteSpace (projTensor B_H 2) :=
            HRS.Fp81.V01.fp81v01_projTensorComplete B_H 2
          ∃ (Yh : A.Ω → ℝ → B_H)
            (Fj : A.Ω → ℝ → projTensor B_H 2)
            (V : A.Ω → ℝ),
            (∀ t : ℝ, Measurable (fun ω => Yh ω t)) ∧
            (∀ t : ℝ, Measurable (fun ω => Fj ω t)) ∧
            Integrable V A.P ∧
            (∀ ω, Fj ω 0 = 0) ∧
            (∀ᵐ ω ∂A.P,
              (∀ t ∈ Icc (0 : ℝ) H,
                Yh ω t = s102_Y (r26t3_coeff R)
                  (wholeSpaceIndex p.d : ℝ) H A.P A.X ω t) ∧
              ContinuousOn (Yh ω) (Icc 0 H) ∧
              (∀ q r, 0 ≤ q → q ≤ r → r ≤ H →
                IsR2JValue (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
                  (fp81s21_movingRawEtaField p R A ω) (Ioc q r)
                  (((Fj ω r - Fj ω q : projTensor B_H 2) : TensorDual B_H 2))) ∧
              ContinuousOn (Fj ω) (Icc 0 H) ∧
              BoundedVariationOn (Fj ω) (Icc 0 H) ∧
              (eVariationOn (Fj ω) (Icc 0 H)).toReal ≤ V ω) ∧
            ∀ (Φ : Window p → ℝ), MemCb 5 Φ →
              let W : B_H →L[ℝ] Window p :=
                HRS.MS.ProClosureS111.physicalWindowRestriction
                  (d := p.d) (m := (wholeSpaceIndex p.d : ℝ))
                  (T := p.T) (H := H) ha le_rfl
              let Ψ : B_H → ℝ := fun w => Φ (W w)
              let Aj : ℕ → A.Ω → ℝ → (projTensor B_H 2 →L[ℝ] ℝ) :=
                fun L ω τ => fp81s21_covariance_pairingCLM
                  (iteratedFDeriv ℝ 2
                    (r2HeatFn (future H)
                      (fun w => Ψ (s102_Pj H hH L w)) τ)
                    (Yh ω τ))
              ∃ M : A.Ω → ℝ, Integrable M A.P ∧
                ∀ L : ℕ,
                  ∃ WS : fp81s21_RSBVWindow A.P H (Aj L) Fj,
                    ∀ q r, 0 ≤ q → q ≤ r → r ≤ H →
                      Integrable
                        (fp81s21_rs_bv_variation_majorant (Aj L) Fj q r) A.P ∧
                      ∀ᵐ ω ∂A.P,
                        fp81s21_rs_bv_variation_majorant (Aj L) Fj q r ω ≤ M ω

theorem fp81s21_moving_covariance_rsbv_families (p : Parameters) :
    fp81s21_moving_covariance_rsbv_statement p := by
  obtain ⟨δi, hδi, hihalf, hinputs⟩ := fp81s21_moving_inputs_all p
  obtain ⟨δh, hδh, hhhalf, hheat⟩ :=
    fp81s21_moving_heat_family_window_derivs p
  refine ⟨min δi δh, lt_min hδi hδh,
    (min_le_left _ _).trans hihalf, ?_⟩
  intro δ hδ hδle R
  have hδi' : δ ≤ δi := hδle.trans (min_le_left _ _)
  have hδh' : δ ≤ δh := hδle.trans (min_le_right _ _)
  obtain ⟨future, hfuture, -⟩ := hheat δ hδ hδh' R
  refine ⟨future, hfuture, ?_⟩
  intro a ha hH N hN A F
  obtain ⟨c, hstd, hphys⟩ := hinputs δ hδ hδi' R a ha
  have hlin : S102Lin (r26t3_coeff R)
      (wholeSpaceIndex p.d : ℝ) (a + p.T) :=
    fp81s21_S102Lin p R (a + p.T)
  have hphysicalH : Fp81MovingPhysicalInputs R hN A (a + p.T) := by
    simpa using hphys N hN A
  have hfixed := fp81s21_moving_covariance_rsbv_window_fixed p R hδ
    (hδh'.trans hhhalf) a ha hH hN A F hstd hlin hphysicalH future hfuture
  rcases hfixed with ⟨Yh, Fj, V, hYm, hFm, hVi, hF0, hgood, hfamily⟩
  refine ⟨Yh, Fj, V, hYm, hFm, hVi, hF0, hgood, ?_⟩
  intro Φ hΦ
  rcases hfamily Φ hΦ with ⟨M, hMi, hbyL⟩
  refine ⟨M, hMi, ?_⟩
  intro L
  rcases hbyL L with ⟨hwindow, hbound⟩
  refine ⟨Classical.choice hwindow, ?_⟩
  intro q r hq hqr hr
  exact hbound q r hq hqr hr

#print axioms HRS.Fp81.S21.fp81s21_moving_covariance_rsbv_statement
#print axioms HRS.Fp81.S21.fp81s21_moving_covariance_rsbv_families

end HRS.Fp81.S21

end
