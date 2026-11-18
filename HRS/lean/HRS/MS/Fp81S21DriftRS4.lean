import HRS.MS.Fp81S21MovingHeat3
import HRS.MS.S21F_P00
import HRS.MS.R2InterpAux47
import HRS.MS.Fp81S21DriftRS3

/-! The proposed physical drift RS contract. This is a proposition, not a proof
of the contract. The selected RS family is shared by all intervals at level L. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set
open scoped BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp
open HRS.MC.Sec7.PI HRS.MC.Sec7.S7PIF6

/-- The cylindrical drift sum appearing before the factor `-(sqrt N)⁻¹` in
the moving Itô rate. -/
def fp81s21_moving_drift_cyl_sum
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {N : ℕ} (A : Particle R N) (F : FilteredParticle A)
    (a : ℝ) (ha : 0 ≤ a) (hH : 0 < a + p.T)
    (L : ℕ) (Φ : Window p → ℝ) (ω : A.Ω) (u : ℝ) : ℝ :=
  let H := a + p.T
  let τ := s102_tauk hH L
  let α := s102_alk L
  let W := HRS.MS.ProClosureS111.physicalWindowRestriction
    (d := p.d) (m := (wholeSpaceIndex p.d : ℝ)) (T := p.T) (H := H) ha le_rfl
  let G := fun x => Φ (W (s102_Lam H L x))
  ∑ i, fderiv ℝ (gaussHeat
      (s102_obsCov (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) τ α) G u)
      (s102_obs τ α (s102_Y (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
        H A.P A.X ω u)) (EuclideanSpace.single i 1) *
    s102_hh (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) τ α
      (fun v => r2QuadField p.s (r26t3_mu R v) A.P F.X v ω) i u

/-- The full intended public contract. The proposition records the common
radius and future, the physical measurable versions, one RS family per level,
and an integrable majorant independent of the level. It is not yet proved. -/
def fp81s21_moving_drift_rs_statement (p : Parameters) : Prop :=
  ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
    ∃ future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H),
      fp81s21_moving_heat_full_clause p R future ∧
      ∀ (a : ℝ) (ha : 0 ≤ a) (hH : 0 < a + p.T)
        (N : ℕ) (hN : 2 ≤ N) (A : Particle R N) (F : FilteredParticle A),
      ∃ (Yh Fd : A.Ω → ℝ → OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T))
        (V : A.Ω → ℝ),
        (∀ t, Measurable (fun ω => Yh ω t)) ∧
        (∀ t, Measurable (fun ω => Fd ω t)) ∧ Integrable V A.P ∧
        (∀ᵐ ω ∂A.P, (∀ t ∈ Icc (0 : ℝ) (a + p.T),
          Yh ω t = s102_Y (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
            (a + p.T) A.P A.X ω t) ∧
          ContinuousOn (Yh ω) (Icc 0 (a + p.T)) ∧
          Fd ω 0 = 0 ∧ ContinuousOn (Fd ω) (Icc 0 (a + p.T)) ∧
          BoundedVariationOn (Fd ω) (Icc 0 (a + p.T)) ∧
          (eVariationOn (Fd ω) (Icc 0 (a + p.T))).toReal ≤ V ω ∧
          ∀ q r, 0 ≤ q → q ≤ r → r ≤ a + p.T →
            Fd ω r - Fd ω q = r2DriftInc (r26t3_coeff R)
              (wholeSpaceIndex p.d : ℝ) (a + p.T)
              (fun u f => r2QuadField p.s (r26t3_mu R u) A.P A.X u ω f) q r) ∧
        ∀ (Φ : Window p → ℝ), MemCb 5 Φ →
          let W := HRS.MS.ProClosureS111.physicalWindowRestriction
            (d := p.d) (m := (wholeSpaceIndex p.d : ℝ)) (T := p.T)
            (H := a + p.T) ha le_rfl
          let Ad := fun L ω t => fderiv ℝ
            (r2HeatFn (future (a + p.T)) (fun w => Φ (W (s102_Pj (a + p.T) hH L w))) t)
            (Yh ω t)
          ∃ M : A.Ω → ℝ, Integrable M A.P ∧
            ∀ L : ℕ, ∃ WS : fp81s21_RSBVWindow A.P (a + p.T) (Ad L) Fd,
              ∀ q r, 0 ≤ q → q ≤ r → r ≤ a + p.T →
                Integrable (fp81s21_rs_bv_variation_majorant (Ad L) Fd q r) A.P ∧
                (∀ᵐ ω ∂A.P,
                  IntegrableOn (fp81s21_moving_drift_cyl_sum p R A F a ha hH L Φ ω) (Ioc q r) ∧
                  WS.value q r ω =
                    ∫ u in Ioc q r, fp81s21_moving_drift_cyl_sum p R A F a ha hH L Φ ω u) ∧
                (∀ᵐ ω ∂A.P,
                  fp81s21_rs_bv_variation_majorant (Ad L) Fd q r ω ≤ M ω)

end HRS.Fp81.S21
#print axioms HRS.Fp81.S21.fp81s21_moving_drift_cyl_sum
#print axioms HRS.Fp81.S21.fp81s21_moving_drift_rs_statement
