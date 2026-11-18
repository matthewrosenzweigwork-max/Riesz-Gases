import HRS.MS.Fp81S21DriftRS15
import HRS.MS.Fp81S21CovCumulative10
import HRS.MS.Fp81S21MovingHeatItoPartition
import HRS.MS.Fp81V01Insert

/-!
# HRS S2.1(iii), packet 19c-ii: specified cylindrical covariance RS header

This file records the exact physical RS contract against the compiled moving
Itô rate and raw-eta covariance definitions.  The physical construction of the
RS families and their level-uniform integrable variation majorant remains a
separate proof stage.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp HRS.MS.CovMeas
open HRS.MC.Sec7.PI HRS.MC.Sec7.S7PIF6

/-- Evaluation of a bilinear form on the projective tensor, as a continuous
linear functional on the projective tensor subtype. -/
def fp81s21_covariance_pairingCLM
    {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (Q : B [×2]→L[ℝ] ℝ) : projTensor B 2 →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ Q).comp (projTensor B 2).subtypeL

/-- The unscaled covariance time integrand in the public moving heat Itô rate.
The factor `2 * C.ν` occurs once, inside the covariance integrand. -/
noncomputable def fp81s21_moving_covariance_cyl_sum
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {N : ℕ} (A : Particle R N) (F : FilteredParticle A)
    (a : ℝ) (ha : 0 ≤ a) (hH : 0 < a + p.T)
    (L : ℕ) (Φ : Window p → ℝ) (ζ : A.Ω) (u : ℝ) : ℝ := by
  let H : ℝ := a + p.T
  let C : WholeCoeff p.d := r26t3_coeff R
  let m : ℝ := (wholeSpaceIndex p.d : ℝ)
  let τ : Fin (s102_q p.d L) → Icc (0 : ℝ) H := s102_tauk hH L
  let α : Fin (s102_q p.d L) → MultiIndex p.d := s102_alk L
  let W : OscPath p.d (wholeSpaceIndex p.d : ℝ) H →L[ℝ] Window p :=
    HRS.MS.ProClosureS111.physicalWindowRestriction
      (d := p.d) (m := (wholeSpaceIndex p.d : ℝ)) (T := p.T)
      (H := H) ha le_rfl
  let G : EuclideanSpace ℝ (Fin (s102_q p.d L)) → ℝ :=
    fun x => Φ (W (s102_Lam H L x))
  exact
    ∑ i, ∑ j, iteratedFDeriv ℝ 2
      (gaussHeat (s102_obsCov C m τ α) G u)
      (s102_obs τ α (s102_Y C m H A.P A.X ζ u))
      ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] *
      (2 * C.ν * s102_hh2 C m τ α
        (fun v => s102_etaf (r26t3_mu R v) F.X ζ v) i j u)

/-- The coefficient in the moving rate is exactly `2 / β`; the public rate
places this single factor inside `s102_hh2`. -/
theorem fp81s21_moving_covariance_factor_eq
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) :
    2 * (r26t3_coeff R).ν = 2 * p.β⁻¹ := by
  rfl

/-- Exact target contract for the specified cylindrical covariance RS
families.  It uses one selected future, the same measurable prediction as the
moving drift theorem, and the measurable projective raw-eta cumulative.  For
each level it requires one `fp81s21_RSBVWindow` selection on every physical
subinterval; its value is the covariance time integral from the public rate. -/
def fp81s21_moving_covariance_rs_statement (p : Parameters) : Prop :=
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
              let W : OscPath p.d (wholeSpaceIndex p.d : ℝ) H →L[ℝ] Window p :=
                HRS.MS.ProClosureS111.physicalWindowRestriction
                  (d := p.d) (m := (wholeSpaceIndex p.d : ℝ))
                  (T := p.T) (H := H) ha le_rfl
              let Ψ : B_H → ℝ := fun w => Φ (W w)
              let Aj : ℕ → A.Ω → ℝ →
                  (projTensor B_H 2 →L[ℝ] ℝ) :=
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
                      (∀ᵐ ω ∂A.P,
                        IntegrableOn
                          (fp81s21_moving_covariance_cyl_sum
                            p R A F a ha hH L Φ ω) (Ioc q r) ∧
                        WS.value q r ω =
                          ∫ u in Ioc q r,
                            fp81s21_moving_covariance_cyl_sum
                              p R A F a ha hH L Φ ω u) ∧
                      (∀ᵐ ω ∂A.P,
                        fp81s21_rs_bv_variation_majorant
                          (Aj L) Fj q r ω ≤ M ω)

#print axioms HRS.Fp81.S21.fp81s21_covariance_pairingCLM
#print axioms HRS.Fp81.S21.fp81s21_moving_covariance_cyl_sum
#print axioms HRS.Fp81.S21.fp81s21_moving_covariance_factor_eq
#print axioms HRS.Fp81.S21.fp81s21_moving_covariance_rs_statement

end HRS.Fp81.S21

end
