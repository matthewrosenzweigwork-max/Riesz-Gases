import HRS.MS.Fp81S21WinRSBV3
import HRS.MS.Fp81S21CovCumulative9

/-! Shared measurable drift and covariance witnesses with one variation bound. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp

def fp81s21_moving_shared_rs_core
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {N : ℕ} (A : Particle R N) (a : ℝ)
    (Yh : A.Ω → ℝ → OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T))
    (Fd : A.Ω → ℝ → OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T))
    (Fj : A.Ω → ℝ → projTensor
      (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)) 2)
    (V : A.Ω → ℝ) : Prop :=
  (∀ t, Measurable (fun ω => Yh ω t)) ∧
  (∀ t, Measurable (fun ω => Fd ω t)) ∧
  (∀ t, Measurable (fun ω => Fj ω t)) ∧
  Integrable V A.P ∧
  (∀ ω, Fj ω 0 = 0) ∧
  ∀ᵐ ω ∂A.P,
    (∀ t ∈ Icc (0 : ℝ) (a + p.T),
      Yh ω t = s102_Y (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
        (a + p.T) A.P A.X ω t) ∧
    ContinuousOn (Yh ω) (Icc 0 (a + p.T)) ∧
    Fd ω 0 = 0 ∧
    ContinuousOn (Fd ω) (Icc 0 (a + p.T)) ∧
    BoundedVariationOn (Fd ω) (Icc 0 (a + p.T)) ∧
    (eVariationOn (Fd ω) (Icc 0 (a + p.T))).toReal ≤ V ω ∧
    (∀ q r, 0 ≤ q → q ≤ r → r ≤ a + p.T →
      Fd ω r - Fd ω q = r2DriftInc (r26t3_coeff R)
        (wholeSpaceIndex p.d : ℝ) (a + p.T)
        (fun u f => r2QuadField p.s (r26t3_mu R u) A.P A.X u ω f) q r) ∧
    (∀ q r, 0 ≤ q → q ≤ r → r ≤ a + p.T →
      IsR2JValue (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) (a + p.T)
        (fp81s21_movingRawEtaField p R A ω) (Ioc q r)
        (((Fj ω r - Fj ω q : projTensor
          (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)) 2) : TensorDual
          (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)) 2))) ∧
    ContinuousOn (Fj ω) (Icc 0 (a + p.T)) ∧
    BoundedVariationOn (Fj ω) (Icc 0 (a + p.T)) ∧
    (eVariationOn (Fj ω) (Icc 0 (a + p.T))).toReal ≤ V ω

theorem fp81s21_moving_shared_rs_core_of_producers
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {N : ℕ} (A : Particle R N) (a : ℝ) (ha : 0 ≤ a)
    (Yh : A.Ω → ℝ → OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T))
    (Fd : A.Ω → ℝ → OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T))
    (Vd : A.Ω → ℝ) (Fj : A.Ω → ℝ → projTensor
      (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)) 2)
    (Vj : A.Ω → ℝ)
    (hYm : ∀ t, Measurable (fun ω => Yh ω t))
    (hDm : ∀ t, Measurable (fun ω => Fd ω t))
    (hDVi : Integrable Vd A.P)
    (hDgood : ∀ᵐ ω ∂A.P,
      (∀ t ∈ Icc (0 : ℝ) (a + p.T),
        Yh ω t = s102_Y (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
          (a + p.T) A.P A.X ω t) ∧
      ContinuousOn (Yh ω) (Icc 0 (a + p.T)) ∧
      Fd ω 0 = 0 ∧
      ContinuousOn (Fd ω) (Icc 0 (a + p.T)) ∧
      BoundedVariationOn (Fd ω) (Icc 0 (a + p.T)) ∧
      (eVariationOn (Fd ω) (Icc 0 (a + p.T))).toReal ≤ Vd ω ∧
      ∀ q r, 0 ≤ q → q ≤ r → r ≤ a + p.T →
        Fd ω r - Fd ω q = r2DriftInc (r26t3_coeff R)
          (wholeSpaceIndex p.d : ℝ) (a + p.T)
          (fun u f => r2QuadField p.s (r26t3_mu R u) A.P A.X u ω f) q r)
    (hJm : ∀ t, Measurable (fun ω => Fj ω t))
    (hJVi : Integrable Vj A.P)
    (hJzero : ∀ ω, Fj ω 0 = 0)
    (hJgood : ∀ᵐ ω ∂A.P,
      (∀ q r, 0 ≤ q → q ≤ r → r ≤ a + p.T →
        IsR2JValue (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) (a + p.T)
          (fp81s21_movingRawEtaField p R A ω) (Ioc q r)
          (((Fj ω r - Fj ω q : projTensor
            (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)) 2) : TensorDual
            (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)) 2))) ∧
      ContinuousOn (Fj ω) (Icc 0 (a + p.T)) ∧
      BoundedVariationOn (Fj ω) (Icc 0 (a + p.T)) ∧
      (eVariationOn (Fj ω) (Icc 0 (a + p.T))).toReal ≤ Vj ω) :
    ∃ V : A.Ω → ℝ,
      (∀ ω, V ω = |Vd ω| + |Vj ω|) ∧
      fp81s21_moving_shared_rs_core p R A a Yh Fd Fj V := by
  classical
  let V : A.Ω → ℝ := fun ω => |Vd ω| + |Vj ω|
  have hVi : Integrable V A.P := hDVi.abs.add hJVi.abs
  refine ⟨V, (fun ω => rfl), ?_⟩
  dsimp [fp81s21_moving_shared_rs_core]
  refine ⟨hYm, hDm, hJm, hVi, hJzero, ?_⟩
  filter_upwards [hDgood, hJgood] with ω hd hj
  rcases hd with ⟨hYeq, hYc, hDzero, hDc, hDBV, hDvar, hDinc⟩
  rcases hj with ⟨hJinc, hJc, hJBV, hJvar⟩
  refine ⟨hYeq, hYc, hDzero, hDc, hDBV, ?_, hDinc,
    hJinc, hJc, hJBV, ?_⟩
  · calc
      (eVariationOn (Fd ω) (Icc 0 (a + p.T))).toReal ≤ Vd ω := hDvar
      _ ≤ |Vd ω| := le_abs_self _
      _ ≤ |Vd ω| + |Vj ω| := le_add_of_nonneg_right (abs_nonneg _)
  · calc
      (eVariationOn (Fj ω) (Icc 0 (a + p.T))).toReal ≤ Vj ω := hJvar
      _ ≤ |Vj ω| := le_abs_self _
      _ ≤ |Vd ω| + |Vj ω| := le_add_of_nonneg_left (abs_nonneg _)

#print axioms HRS.Fp81.S21.fp81s21_moving_shared_rs_core_of_producers
end HRS.Fp81.S21
end
