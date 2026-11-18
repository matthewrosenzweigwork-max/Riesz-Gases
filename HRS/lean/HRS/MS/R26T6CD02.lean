import HRS.MS.R26T6CD01

/-! Original proposed boundary vocabulary R26-T6C.D02 (definition-only, no proof). -/
set_option autoImplicit false
noncomputable section
open Classical MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff
namespace HRS.MS.R26T6
open HRS
open HRS.Whole

def r26t6_obs {d : ℕ} {T : ℝ} (Z : R2X d T)
    (tau : Set.Icc (0 : ℝ) T) (phi : Euc d → ℝ) : ℝ :=
  OscDual.eval (OscPath.at' Z tau) phi

def r26t6_driftInsertion {B : Type*} (D Z : B) (i j : Fin 3) : B :=
  if j = i then D else Z

structure r26t6_SourceContractions {d : ℕ} {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) (s a beta gamma : ℝ) (rho : Euc d → ℝ)
    (T u : ℝ) (Z : Omega → R2X d T)
    (b z : ℝ → Omega → (Euc d → ℝ) → ℝ) : Prop where
  drift : ∀ tau : Fin 3 → Set.Icc (0 : ℝ) T, ∀ phi : Fin 3 → Euc d → ℝ,
    (∀ i, IsOscTest (wholeSpaceIndex d) (phi i)) →
    ∀ chi, IsR2CrossDensities d s a beta gamma rho T u tau phi chi →
    ∀ i : Fin 3,
      let C := (quadraticGradientDyn d s a beta).coeff (fun _ => rho)
      let F := fun p : ℝ × Omega =>
        b p.1 p.2 (propagatorW C p.1 (u + tau i) (phi i)) *
          r26t6_obs (Z p.2) (tau (i + 1)) (phi (i + 1)) *
          r26t6_obs (Z p.2) (tau (i + 2)) (phi (i + 2))
      Integrable F ((volume.restrict (Set.Icc 0 (u + tau i))).prod P) ∧
      ∀ᵐ r ∂volume.restrict (Set.Icc 0 (u + tau i)),
        (∫ w, F (r, w) ∂P) =
          -∫ x, ∫ y, commutatorKernel d s
            (gradient (propagatorW C r (u + tau i) (phi i))) x y *
              chi (i + 1) r x * chi (i + 2) r y
  covariance : ∀ tau : Fin 3 → Set.Icc (0 : ℝ) T, ∀ phi : Fin 3 → Euc d → ℝ,
    (∀ i, IsOscTest (wholeSpaceIndex d) (phi i)) →
    ∀ chi, IsR2CrossDensities d s a beta gamma rho T u tau phi chi →
    ∀ i : Fin 3,
      let C := (quadraticGradientDyn d s a beta).coeff (fun _ => rho)
      let F := fun p : ℝ × Omega =>
        z p.1 p.2 (fun x =>
          inner ℝ (gradient (propagatorW C p.1 (u + tau i) (phi i)) x)
            (gradient (propagatorW C p.1 (u + tau (i + 1)) (phi (i + 1))) x)) *
          r26t6_obs (Z p.2) (tau (i + 2)) (phi (i + 2))
      Integrable F ((volume.restrict (Set.Icc 0 (min (u + tau i) (u + tau (i + 1))))).prod P) ∧
      ∀ᵐ r ∂volume.restrict (Set.Icc 0 (min (u + tau i) (u + tau (i + 1)))),
        (∫ w, F (r, w) ∂P) =
          ∫ x, inner ℝ (gradient (propagatorW C r (u + tau i) (phi i)) x)
            (gradient (propagatorW C r (u + tau (i + 1)) (phi (i + 1))) x) *
              chi (i + 2) r x

def r26t6_hermiteSection {d : ℕ} (m : ℝ) (n : ℕ) (phi : Euc d → ℝ) : Euc d → ℝ :=
  fun x => ∑ alpha ∈ (multiIndex_sublevel_finite d n).toFinset,
    (oscEigenvalue d alpha ^ (m / 2) * HRS.Whole.hermiteCoeff phi alpha) *
      oscTestFun m alpha x

structure r26t6_OscOrbitApprox {d : ℕ} (C : WholeCoeff d) (m H : ℝ) (r : ℕ) : Prop where
  classical : ∀ phi, IsOscTest m phi → ∀ t ∈ Set.Icc 0 H,
    ∃ f, IsClassicalAdjointW C t phi f
  smooth : ∀ phi, IsOscTest m phi → ∀ v ∈ Set.Icc 0 H, ∀ t ∈ Set.Icc v H,
    ContDiff ℝ (r + 1) (propagatorW C v t phi)
  bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ phi, IsOscTest m phi →
    ∀ v ∈ Set.Icc 0 H, ∀ t ∈ Set.Icc v H,
      weightedSupE (r + 1) 0 (propagatorW C v t phi) ≤
        ENNReal.ofReal (K * oscNorm m phi)
  limit : ∀ phi, IsOscTest m phi →
    Tendsto (fun n => ⨆ v ∈ Set.Icc (0 : ℝ) H, ⨆ t ∈ Set.Icc v H,
      weightedSupE (r + 1) 0
        (propagatorW C v t (r26t6_hermiteSection m n phi) - propagatorW C v t phi))
      atTop (𝓝 0)

def r26t6_AllDriftCoordinates {d : ℕ} (C : WholeCoeff d) (m T u : ℝ)
    (z : ℝ → (Euc d → ℝ) → ℝ) (v : ℝ) (D : OscPath d m T) : Prop :=
  ∀ tau : Set.Icc (0 : ℝ) T, ∀ phi : Euc d → ℝ, IsOscTest m phi →
    IntegrableOn (fun r => z r (propagatorW C r (u + tau) phi))
      (Set.Icc 0 (min v (u + tau))) ∧
    OscDual.eval (OscPath.at' D tau) phi =
      ∫ r in Set.Icc 0 (min v (u + tau)),
        z r (propagatorW C r (u + tau) phi)

def r26t6_AllShiftedJValue {d : ℕ} (C : WholeCoeff d) (m T u : ℝ)
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

structure r26t6_PhysicalChartFields {d r : ℕ} {Pw : ℝ}
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (rho : Euc d → ℝ) (s H : ℝ) (E : r26t6_WeightedChart d r Pw)
    (a : ℕ → Euc d → ℝ) (Z : ℝ → Omega → OscDual d (wholeSpaceIndex d))
    (qLin qQuad : ℝ × Omega → r26t6_Coeff) : Prop where
  linear_measurable : Measurable qLin
  quadratic_measurable : Measurable qQuad
  linear_moment : MemLp qLin 2 ((volume.restrict (Set.Icc 0 H)).prod P)
  quadratic_moment : MemLp qQuad 2 ((volume.restrict (Set.Icc 0 H)).prod P)
  mass_zero : ∀ p,
    inner ℝ (qLin p) (E.encode (fun _ => 1)) = 0 ∧
    inner ℝ (qQuad p) (E.encode (fun _ => 1)) = 0
  linear_coordinates : ∀ᵐ v ∂volume.restrict (Set.Icc 0 H), ∀ j : ℕ,
    (fun w => qLin (v, w) j) =ᵐ[P]
      (fun w => OscDual.eval (Z v w) (E.test j))
  wick_coordinates : ∀ᵐ v ∂volume.restrict (Set.Icc 0 H), ∀ j : ℕ,
    IsR2WickChaos P (HRS.Whole.withDensityReal rho) a
      (fun i w => OscDual.eval (Z v w) (a i))
      (HRS.Whole.commutatorKernel d s (gradient (E.test j)))
      (fun w => -2 * qQuad (v, w) j)

end HRS.MS.R26T6
