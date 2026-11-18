import HRS.MS.S111K2B02

/-!
# S11.1 / J01 definitions (S11K4): the skeleton interval interface, copied verbatim

Source: Pro branch `skeleton/cores/S11.1-Native.lean`, `S11.1-NativeAdapters.lean`, `S11.1-BV.lean` and
`S11.1-Intervals.lean` (`origin/pro/fine-breakdown`). Definitions only; no theorem is stated here.
Names live in `HRS.MS.S111K4J01`.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K4J01

open HRS HRS.Whole

/-- Coefficient space `ℓ²` (skeleton `Coeff`). -/
abbrev Coeff := lp (fun _ : ℕ => ℝ) 2

/-- Borel structure on the coefficient space (as in the Pro `r26t6_coeffMeasurable`; needed for `Measurable q`). -/
instance coeffMeasurable : MeasurableSpace Coeff := borel _

instance coeffBorel : BorelSpace Coeff := ⟨rfl⟩

/-- Time coefficients in `L¹([0,H]; ℓ²)` (skeleton `TimeCoeff`). -/
abbrev TimeCoeff (H : ℝ) := Lp Coeff 1 (volume.restrict (Set.Icc (0 : ℝ) H))

/-- Exponential age weight (skeleton `age`). -/
def age (c u v : ℝ) : ℝ := Real.exp (-c * max (u - v) 0)

/-- An actual coordinate chart of the weighted test completion (skeleton `WeightedChart`). -/
structure WeightedChart (d r : ℕ) (Pw : ℝ) where
  encode : (Euc d → ℝ) → Coeff
  test : ℕ → Euc d → ℝ
  add : ∀ f g, IsR2WeightedTest r Pw f → IsR2WeightedTest r Pw g →
    encode (f + g) = encode f + encode g
  smul : ∀ (a : ℝ) f, IsR2WeightedTest r Pw f →
    encode (a • f) = a • encode f
  norm : ∀ f, IsR2WeightedTest r Pw f →
    ‖encode f‖ = (weightedSobolevE r Pw f).toReal
  test_smooth : ∀ i, IsR2Test (test i)
  test_coord : ∀ i j, encode (test i) j = if i = j then 1 else 0
  dense : Dense (Set.range fun f : {f : Euc d → ℝ // IsR2Test f} => encode f)

/-- Charted orbit predicate (skeleton `ChartedOrbits`). -/
def ChartedOrbits {d r : ℕ} {Pw : ℝ} (E : WeightedChart d r Pw)
    (C : WholeCoeff d) (m H : ℝ) : Prop :=
  (∀ ta tb : ℝ, ∀ phi psi : Euc d → ℝ,
    IsR2DualCombo m phi → IsR2DualCombo m psi →
    ta ∈ Set.Icc 0 H → tb ∈ Set.Icc 0 H →
    AEStronglyMeasurable (fun v => E.encode (fun x =>
      inner ℝ (gradient (propagatorW C v ta phi) x)
        (gradient (propagatorW C v tb psi) x)))
      (volume.restrict (Set.Icc 0 (min ta tb)))) ∧
  ∀ t ∈ Set.Icc 0 H, ∀ phi, IsR2DualCombo m phi →
    AEStronglyMeasurable (fun v => E.encode (propagatorW C v t phi))
      (volume.restrict (Set.Icc 0 t))

/-- The native continuity premise used by S10.1, at one forcing time (skeleton `ShiftedJValue`). -/
def ShiftedJValue {d : ℕ} (C : WholeCoeff d) (m T u : ℝ)
    (z : ℝ → (Euc d → ℝ) → ℝ) (a b : ℝ)
    (J : projTensor (OscPath d m T) 2) : Prop :=
  ∀ ta tb : Set.Icc (0 : ℝ) T, ∀ phi psi : Euc d → ℝ,
    ∀ l1 l2 : StrongDual ℝ (OscPath d m T),
      IsR2DualCombo m phi → IsR2DualCombo m psi →
      (∀ w, l1 w = OscDual.eval (OscPath.at' w ta) phi) →
      (∀ w, l2 w = OscDual.eval (OscPath.at' w tb) psi) →
      (J : TensorDual (OscPath d m T) 2)
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap ![l1, l2]) =
        2 * C.ν * ∫ v in Set.Ioc a b ∩ Set.Icc 0 (min (u + ta) (u + tb)),
          z v (fun x => inner ℝ (gradient (propagatorW C v (u + ta) phi) x)
            (gradient (propagatorW C v (u + tb) psi) x))

/-- All drift coordinates (skeleton `AllDriftCoordinates`). -/
def AllDriftCoordinates {d : ℕ} (C : WholeCoeff d) (m T u : ℝ)
    (z : ℝ → (Euc d → ℝ) → ℝ) (v : ℝ) (D : OscPath d m T) : Prop :=
  ∀ tau : Set.Icc (0 : ℝ) T, ∀ phi : Euc d → ℝ, IsOscTest m phi →
    IntegrableOn (fun r => z r (propagatorW C r (u + tau) phi))
      (Set.Icc 0 (min v (u + tau))) ∧
    OscDual.eval (OscPath.at' D tau) phi =
      ∫ r in Set.Icc 0 (min v (u + tau)),
        z r (propagatorW C r (u + tau) phi)

/-- All shifted covariance coordinates (skeleton `AllShiftedJValue`). -/
def AllShiftedJValue {d : ℕ} (C : WholeCoeff d) (m T u : ℝ)
    (z : ℝ → (Euc d → ℝ) → ℝ) (v : ℝ)
    (J : projTensor (OscPath d m T) 2) : Prop :=
  ∀ ta tb : Set.Icc (0 : ℝ) T, ∀ phi psi : Euc d → ℝ,
    IsOscTest m phi → IsOscTest m psi →
    IntegrableOn (fun r => z r (fun x =>
      inner ℝ (gradient (propagatorW C r (u + ta) phi) x)
        (gradient (propagatorW C r (u + tb) psi) x)))
      (Set.Icc 0 (min v (min (u + ta) (u + tb)))) ∧
    ∀ l1 l2 : StrongDual ℝ (OscPath d m T),
      (∀ w, l1 w = OscDual.eval (OscPath.at' w ta) phi) →
      (∀ w, l2 w = OscDual.eval (OscPath.at' w tb) psi) →
      (J : TensorDual (OscPath d m T) 2)
        ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap ![l1, l2]) =
        2 * C.ν * ∫ r in Set.Icc 0 (min v (min (u + ta) (u + tb))),
          z r (fun x => inner ℝ (gradient (propagatorW C r (u + ta) phi) x)
            (gradient (propagatorW C r (u + tb) psi) x))

/-- Coefficient field of a time-coefficient path at a fixed time (skeleton `coefficientField`). -/
def coefficientField {d r : ℕ} {Pw : ℝ} (E : WeightedChart d r Pw)
    (q : ℝ → Coeff) (v : ℝ) (f : Euc d → ℝ) : ℝ :=
  inner ℝ (q v) (E.encode f)

/-- A bounded operator on L1 is chosen once and used for every random field (skeleton `IntervalOperators`). -/
structure IntervalOperators {d r : ℕ} {Pw : ℝ} (E : WeightedChart d r Pw)
    (C : WholeCoeff d) (T u c0 B : ℝ) where
  drift : ℝ → ℝ → TimeCoeff (u + T) →L[ℝ] R2X d T
  covariance : ℝ → ℝ → TimeCoeff (u + T) →L[ℝ] projTensor (R2X d T) 2
  drift_zero : ∀ v, drift v v = 0
  covariance_zero : ∀ v, covariance v v = 0
  drift_add : ∀ v w z, 0 ≤ v → v ≤ w → w ≤ z → z ≤ u + T →
    drift v z = drift v w + drift w z
  covariance_add : ∀ v w z, 0 ≤ v → v ≤ w → w ≤ z → z ≤ u + T →
    covariance v z = covariance v w + covariance w z
  drift_cont : ∀ q, ContinuousOn (fun v => drift 0 v q) (Set.Icc 0 (u + T))
  covariance_cont : ∀ q, ContinuousOn (fun v => covariance 0 v q) (Set.Icc 0 (u + T))
  drift_norm : ∀ v w, 0 ≤ v → v ≤ w → w ≤ u + T → ∀ q : TimeCoeff (u + T),
    ‖drift v w q‖ ≤ B * ∫ z in Set.Ioc v w, age c0 u z * ‖q z‖
  covariance_norm : ∀ v w, 0 ≤ v → v ≤ w → w ≤ u + T → ∀ q : TimeCoeff (u + T),
    ‖covariance v w q‖ ≤ B * |2 * C.ν| * ∫ z in Set.Ioc v w, age c0 u z ^ 2 * ‖q z‖
  drift_coordinate : ∀ q : TimeCoeff (u + T),
    (∀ᵐ v ∂volume.restrict (Set.Icc 0 (u + T)),
      inner ℝ (q v) (E.encode (fun _ => 1)) = 0) →
    ∀ v w, 0 ≤ v → v ≤ w → w ≤ u + T →
    ∀ tau : Set.Icc (0 : ℝ) T, ∀ phi : Euc d → ℝ,
    IsR2DualCombo (wholeSpaceIndex d) phi →
      OscDual.eval (OscPath.at' (drift v w q) tau) phi =
        ∫ z in Set.Ioc v w ∩ Set.Icc 0 (u + tau),
          coefficientField E q z (propagatorW C z (u + tau) phi)
  covariance_coordinate : ∀ q : TimeCoeff (u + T),
    ∀ v w, 0 ≤ v → v ≤ w → w ≤ u + T →
      ShiftedJValue C (wholeSpaceIndex d) T u (coefficientField E q) v w (covariance v w q)

open Classical in
/-- Time coefficient path of a random field, `ω`-slice (skeleton `timeCoeffOf`). -/
def timeCoeffOf {Omega : Type*} (H : ℝ) (q : ℝ × Omega → Coeff)
    (w : Omega) : TimeCoeff H :=
  if h : MemLp (fun v => q (v, w)) 1 (volume.restrict (Set.Icc 0 H)) then
    h.toLp (fun v => q (v, w))
  else 0

/-- Random drift (skeleton `randomDrift`). -/
def randomDrift {d r : ℕ} {Pw : ℝ} {E : WeightedChart d r Pw}
    {C : WholeCoeff d} {T u c0 B : ℝ} (O : IntervalOperators E C T u c0 B)
    {Omega : Type*} (q : ℝ × Omega → Coeff) (v : ℝ) (w : Omega) : R2X d T :=
  O.drift 0 v (timeCoeffOf (u + T) q w)

/-- Random covariance (skeleton `randomCovariance`). -/
def randomCovariance {d r : ℕ} {Pw : ℝ} {E : WeightedChart d r Pw}
    {C : WholeCoeff d} {T u c0 B : ℝ} (O : IntervalOperators E C T u c0 B)
    {Omega : Type*} (q : ℝ × Omega → Coeff) (v : ℝ) (w : Omega) :
    projTensor (R2X d T) 2 :=
  O.covariance 0 v (timeCoeffOf (u + T) q w)

end HRS.MS.S111K4J01
