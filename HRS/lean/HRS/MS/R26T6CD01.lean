import HRS.MS.R26T6D00

/-! Original proposed boundary vocabulary R26-T6C.D01 (definition-only, no proof). -/
set_option autoImplicit false
noncomputable section
open Classical MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff
namespace HRS.MS.R26T6
open HRS
open HRS.Whole

def r26t6_centeredSquare {d : ℕ} (mu : Measure (Euc d)) (f : Euc d → ℝ) : ℝ :=
  ∫ x, (HRS.Whole.projMean mu f x) ^ 2 ∂mu

def r26t6_dirichlet {d : ℕ} (mu : Measure (Euc d)) (f g : Euc d → ℝ) : ℝ :=
  ∫ x, inner ℝ (gradient f x) (gradient g x) ∂mu

def r26t6_weightedL {d : ℕ} (rho : Euc d → ℝ) (f : Euc d → ℝ) (x : Euc d) : ℝ :=
  -Laplacian.laplacian f x -
    (rho x)⁻¹ * inner ℝ (gradient rho x) (gradient f x)

def r26t6_testSpace (d : ℕ) : Submodule ℝ (Euc d → ℝ) :=
  Submodule.span ℝ {f | IsOscTest (wholeSpaceIndex d : ℝ) f}

structure r26t6_ResponseForm {d : ℕ} (g : Euc d → ℝ) (mu : Measure (Euc d))
    (theta eta : ℝ) : Prop where
  solution : ∀ f : Euc d → ℝ, MemLp f 2 mu →
    HRS.Whole.IsResponse g mu theta f (HRS.Whole.responseInverse g mu theta f)
  linear : ∀ f h : Euc d → ℝ, MemLp f 2 mu → MemLp h 2 mu → ∀ c : ℝ,
    HRS.Whole.responseInverse g mu theta (f + c • h) =ᵐ[mu]
      HRS.Whole.responseInverse g mu theta f + c • HRS.Whole.responseInverse g mu theta h
  symmetry : ∀ f h : Euc d → ℝ, MemLp f 2 mu → MemLp h 2 mu →
    HRS.Whole.susceptibilityCov g mu theta f h = HRS.Whole.susceptibilityCov g mu theta h f
  coercive : ∀ f : Euc d → ℝ, MemLp f 2 mu →
    eta * r26t6_centeredSquare mu f ≤ HRS.Whole.susceptibilityCov g mu theta f f ∧
      HRS.Whole.susceptibilityCov g mu theta f f ≤ r26t6_centeredSquare mu f
  schwarz : ∀ f h : Euc d → ℝ, MemLp f 2 mu → MemLp h 2 mu →
    |HRS.Whole.susceptibilityCov g mu theta f h| ≤
      Real.sqrt (r26t6_centeredSquare mu f) * Real.sqrt (r26t6_centeredSquare mu h)

def r26t6_ShiftedJValue {d : ℕ} (C : WholeCoeff d) (m T u : ℝ)
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

abbrev r26t6_Coeff := lp (fun _ : ℕ => ℝ) 2

instance r26t6_coeffMeasurable : MeasurableSpace r26t6_Coeff := borel _
instance r26t6_coeffBorel : BorelSpace r26t6_Coeff := ⟨rfl⟩

structure r26t6_WeightedChart (d r : ℕ) (Pw : ℝ) where
  encode : (Euc d → ℝ) → r26t6_Coeff
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

def r26t6_ChartedOrbits {d r : ℕ} {Pw : ℝ} (E : r26t6_WeightedChart d r Pw)
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

end HRS.MS.R26T6
