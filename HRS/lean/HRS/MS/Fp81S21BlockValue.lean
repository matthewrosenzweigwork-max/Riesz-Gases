import HRS.MS.Fp81S21WindowLocal
import HRS.MS.Fp81S21BlockRecon2
import HRS.MS.Fp81S21UnitCov2

/-!
# S2.1(iii), packet 15d-4: block covariance value

The value is the unit-clock covariance tensor pushed through the block
reconstruction. Its density is the indicator-localized representative from
packet 16a-2.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.Uniform HRS.Uniform.Q45 HRS.MS.CovMeas HRS.MS.GenPath

/-- The unit-clock covariance constant, chosen before the feature Hilbert space. -/
noncomputable def fp81s21_blockC0 : ℝ :=
  Classical.choose fp81s21_unitCovProps_exists

theorem fp81s21_blockC0_nonneg : 0 ≤ fp81s21_blockC0 :=
  (Classical.choose_spec fp81s21_unitCovProps_exists).1

/-- The unit-clock covariance vector measure for a feature Hilbert space,
using the common constant `fp81s21_blockC0`. -/
noncomputable def fp81s21_blockCovariance
    (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    [CompleteSpace K] [MeasurableSpace K] [BorelSpace K]
    [SecondCountableTopology K] :
    (ℝ → K →L[ℝ] K →L[ℝ] ℝ) →
      VectorMeasure ℝ (ProjTensor2 (PathSp 1 K)) := by
  let h := (Classical.choose_spec fp81s21_unitCovProps_exists).2 K
  exact Classical.choose h

theorem fp81s21_blockCovariance_props
    (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℝ K]
    [CompleteSpace K] [MeasurableSpace K] [BorelSpace K]
    [SecondCountableTopology K] :
    fp81s21_UnitCovProps K fp81s21_blockC0
      (fp81s21_blockCovariance K) := by
  dsimp [fp81s21_blockCovariance, fp81s21_blockC0]
  exact Classical.choose_spec
    ((Classical.choose_spec fp81s21_unitCovProps_exists).2 K)

/-- The actual block value, represented in the projective tensor subspace of
`TensorDual (OscPath d m H) 2`. The constant was chosen before `KSpace d m H`;
`I` is localized by `fp81s21_windowLocalD`. -/
noncomputable def fp81s21_blockValue
    {d : ℕ} {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} {Cmix cdec : ℝ}
    (D : fp81s21_WindowLocalInput C m H a r P z Cmix cdec)
    (I : Set ℝ) (k : ℕ) : projTensor (OscPath d m H) 2 :=
  ⟨fp81s21_blockPsi
      (fp81s21_blockRecon (le_of_lt D.fp81s21_hH) a k)
      (fp81s21_blockCovariance (KSpace d m H)
        (fun s => fp81s21_windowLocalD I k C m H a z D.fp81s21_ha
          (le_of_lt D.fp81s21_hH) s) (Icc (0 : ℝ) 1)),
    fp81s21_blockPsi_mem
      (fp81s21_blockRecon (le_of_lt D.fp81s21_hH) a k)
      (fp81s21_blockCovariance (KSpace d m H)
        (fun s => fp81s21_windowLocalD I k C m H a z D.fp81s21_ha
          (le_of_lt D.fp81s21_hH) s) (Icc (0 : ℝ) 1))⟩

theorem fp81s21_blockValue_mem
    {d : ℕ} {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} {Cmix cdec : ℝ}
    (D : fp81s21_WindowLocalInput C m H a r P z Cmix cdec)
    (I : Set ℝ) (k : ℕ) :
    ((fp81s21_blockValue D I k : projTensor (OscPath d m H) 2) :
      TensorDual (OscPath d m H) 2) ∈ projTensor (OscPath d m H) 2 :=
  (fp81s21_blockValue D I k).property

#print axioms fp81s21_blockC0_nonneg
#print axioms fp81s21_blockCovariance_props
#print axioms fp81s21_blockValue_mem

end HRS.Fp81.S21

end
