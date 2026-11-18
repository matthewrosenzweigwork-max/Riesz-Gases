import HRS.MS.R26T6CD02
import HRS.MS.S111TermAux7

/-! Original proposed boundary vocabulary R26-T6C.D03 (definition-only, no proof). -/
set_option autoImplicit false
noncomputable section
open Classical MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff
namespace HRS.MS.R26T6
open HRS
open HRS.Whole

abbrev r26t6_TimeCoeff (H : ℝ) := Lp r26t6_Coeff 1 (volume.restrict (Set.Icc (0 : ℝ) H))

def r26t6_coefficientField {d r : ℕ} {Pw : ℝ} (E : r26t6_WeightedChart d r Pw)
    (q : ℝ → r26t6_Coeff) (v : ℝ) (f : Euc d → ℝ) : ℝ :=
  inner ℝ (q v) (E.encode f)

structure r26t6_IntervalOperators {d r : ℕ} {Pw : ℝ} (E : r26t6_WeightedChart d r Pw)
    (C : WholeCoeff d) (T u c0 B : ℝ) where
  drift : ℝ → ℝ → r26t6_TimeCoeff (u + T) →L[ℝ] R2X d T
  covariance : ℝ → ℝ → r26t6_TimeCoeff (u + T) →L[ℝ] projTensor (R2X d T) 2
  drift_zero : ∀ v, drift v v = 0
  covariance_zero : ∀ v, covariance v v = 0
  drift_add : ∀ v w z, 0 ≤ v → v ≤ w → w ≤ z → z ≤ u + T →
    drift v z = drift v w + drift w z
  covariance_add : ∀ v w z, 0 ≤ v → v ≤ w → w ≤ z → z ≤ u + T →
    covariance v z = covariance v w + covariance w z
  drift_cont : ∀ q, ContinuousOn (fun v => drift 0 v q) (Set.Icc 0 (u + T))
  covariance_cont : ∀ q, ContinuousOn (fun v => covariance 0 v q) (Set.Icc 0 (u + T))
  drift_norm : ∀ v w, 0 ≤ v → v ≤ w → w ≤ u + T → ∀ q : r26t6_TimeCoeff (u + T),
    ‖drift v w q‖ ≤ B * ∫ z in Set.Ioc v w, HRS.MS.S111K2.s111k2_age c0 u z * ‖q z‖
  covariance_norm : ∀ v w, 0 ≤ v → v ≤ w → w ≤ u + T → ∀ q : r26t6_TimeCoeff (u + T),
    ‖covariance v w q‖ ≤ B * |2 * C.ν| * ∫ z in Set.Ioc v w, HRS.MS.S111K2.s111k2_age c0 u z ^ 2 * ‖q z‖
  drift_coordinate : ∀ q : r26t6_TimeCoeff (u + T),
    (∀ᵐ v ∂volume.restrict (Set.Icc 0 (u + T)),
      inner ℝ (q v) (E.encode (fun _ => 1)) = 0) →
    ∀ v w, 0 ≤ v → v ≤ w → w ≤ u + T →
    ∀ tau : Set.Icc (0 : ℝ) T, ∀ phi : Euc d → ℝ,
    IsR2DualCombo (wholeSpaceIndex d) phi →
      OscDual.eval (OscPath.at' (drift v w q) tau) phi =
        ∫ z in Set.Ioc v w ∩ Set.Icc 0 (u + tau),
          r26t6_coefficientField E q z (propagatorW C z (u + tau) phi)
  covariance_coordinate : ∀ q : r26t6_TimeCoeff (u + T),
    ∀ v w, 0 ≤ v → v ≤ w → w ≤ u + T →
      r26t6_ShiftedJValue C (wholeSpaceIndex d) T u (r26t6_coefficientField E q) v w (covariance v w q)

def r26t6_timeCoeffOf {Omega : Type*} (H : ℝ) (q : ℝ × Omega → r26t6_Coeff)
    (w : Omega) : r26t6_TimeCoeff H :=
  if h : MemLp (fun v => q (v, w)) 1 (volume.restrict (Set.Icc 0 H)) then
    h.toLp (fun v => q (v, w))
  else 0

def r26t6_randomDrift {d r : ℕ} {Pw : ℝ} {E : r26t6_WeightedChart d r Pw}
    {C : WholeCoeff d} {T u c0 B : ℝ} (O : r26t6_IntervalOperators E C T u c0 B)
    {Omega : Type*} (q : ℝ × Omega → r26t6_Coeff) (v : ℝ) (w : Omega) : R2X d T :=
  O.drift 0 v (r26t6_timeCoeffOf (u + T) q w)

def r26t6_randomCovariance {d r : ℕ} {Pw : ℝ} {E : r26t6_WeightedChart d r Pw}
    {C : WholeCoeff d} {T u c0 B : ℝ} (O : r26t6_IntervalOperators E C T u c0 B)
    {Omega : Type*} (q : ℝ × Omega → r26t6_Coeff) (v : ℝ) (w : Omega) :
    projTensor (R2X d T) 2 :=
  O.covariance 0 v (r26t6_timeCoeffOf (u + T) q w)

def r26t6_pairedProcess (d : ℕ) (m H : ℝ) (hH : 0 ≤ H)
    (i : Fin 2) (t : ℝ) (w : HRS.MS.S111T.PathPair d m H) : OscDual d m :=
  OscPath.at' (if i = 0 then w.1 else w.2) (HRS.MS.S111T.clippedTime H hH t)

def r26t6_preparation (beta gamma : ℝ) (i : Fin 2) : ℝ := if i = 0 then gamma else beta

structure r26t6_SharedThermalLaw {d : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) (s a beta gamma H : ℝ) (rho : Euc d → ℝ)
    (Z : Fin 2 → ℝ → Omega → OscDual d (wholeSpaceIndex d)) : Prop where
  evolution : ∀ i, IsLinearGaussianEvolutionW P (r26t6_thermalCoeff d s a beta rho)
    (wholeSpaceIndex d) beta⁻¹ H
    (HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s)
      (HRS.Whole.withDensityReal rho) (r26t6_preparation beta gamma i)) (Z i)
  joint : ∀ n : ℕ, ∀ side : Fin n → Fin 2, ∀ ts : Fin n → ℝ,
    ∀ phi : Fin n → Euc d → ℝ,
    (∀ j, ts j ∈ Set.Icc 0 H) → (∀ j, IsOscTest (wholeSpaceIndex d) (phi j)) →
      P.map (fun w => (WithLp.toLp 2 fun j => OscDual.eval (Z (side j) (ts j) w) (phi j) :
        EuclideanSpace ℝ (Fin n))) =
      multivariateGaussian 0 (Matrix.of fun j k =>
        (if side j = side k then
          HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s)
            (HRS.Whole.withDensityReal rho) (r26t6_preparation beta gamma (side j))
            (propagatorW (r26t6_thermalCoeff d s a beta rho) 0 (ts j) (phi j))
            (propagatorW (r26t6_thermalCoeff d s a beta rho) 0 (ts k) (phi k))
        else 0) +
        noiseCovW (r26t6_thermalCoeff d s a beta rho) beta⁻¹ (ts j) (ts k) (phi j) (phi k))

def r26t6_coreOrder (d : ℕ) : ℕ := 2 * d + 8

def r26t6_coreWeight (d : ℕ) : ℝ := (d : ℝ) + 2

def r26t6_InitialCoordinates (d : ℕ) (s a beta gamma : ℝ) (rho : Euc d → ℝ)
    (T u : ℝ) (I : projTensor (R2X d T) 3) : Prop :=
  ∀ tau : Fin 3 → Set.Icc (0 : ℝ) T, ∀ phi : Fin 3 → Euc d → ℝ,
    (∀ i, IsOscTest (wholeSpaceIndex d) (phi i)) →
    ∀ M : (R2X d T) [×3]→L[ℝ] ℝ,
    (∀ w, M w = ∏ i, r26t6_obs (w i) (tau i) (phi i)) →
    let C := r26t6_thermalCoeff d s a beta rho
    let mu := HRS.Whole.withDensityReal rho
    let h := fun i => HRS.Whole.responseInverse (HRS.Whole.rieszKernel d s) mu gamma
      (propagatorW C 0 (u + tau i) (phi i))
    (I : TensorDual (R2X d T) 3) M = ∫ x, h 0 x * h 1 x * h 2 x ∂mu

end HRS.MS.R26T6
