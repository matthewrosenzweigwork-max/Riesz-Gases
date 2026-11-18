import HRS.MS.R26T6CI11Aesq
import Mathlib.MeasureTheory.Integral.Prod

/-!
# I11: countably many time-space coordinates admit an L²-valued
# representative whenever their time-sectional second moments are
# controlled by a square-summable sequence.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T6C
open HRS HRS.Whole

theorem r26t6c_spacetime_coordinate_square_ae
    {Time Omega iota : Type*} [MeasurableSpace Time]
    [MeasurableSpace Omega] [Countable iota]
    (dt : Measure Time) [IsFiniteMeasure dt]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (f : iota → Time × Omega → ℝ)
    (b : iota → ℝ)
    (hb : Summable (fun i => b i ^ 2))
    (h2 : ∀ i, MemLp (f i) 2 (dt.prod P))
    (hsec : ∀ i, ∀ᵐ t ∂dt,
      (∫ w, (f i (t,w)) ^ 2 ∂P) ≤ b i ^ 2) :
    (∀ᵐ z ∂dt.prod P, Summable (fun i => (f i z) ^ 2)) := by
  have hS : Summable (fun i => (dt Set.univ).toReal * b i ^ 2) :=
    hb.mul_left _
  have hBound : ∀ i, (∫ z, (f i z) ^ 2 ∂(dt.prod P)) ≤
      (dt Set.univ).toReal * b i ^ 2 := by
    intro i
    have hI : Integrable (fun z => (f i z) ^ 2) (dt.prod P) :=
      (h2 i).integrable_sq
    have hInt : Integrable (fun t => ∫ w, (f i (t,w)) ^ 2 ∂P) dt :=
      hI.integral_prod_left
    calc
      _ = ∫ t, ∫ w, (f i (t,w)) ^ 2 ∂P ∂dt := integral_prod _ hI
      _ ≤ ∫ t, b i ^ 2 ∂dt :=
        integral_mono_ae hInt (integrable_const _) (hsec i)
      _ = (dt Set.univ).toReal * b i ^ 2 := by
        rw [integral_const]
        simp [Measure.real, mul_comm]
  have hIntSum : Summable
      (fun i => ∫ z, (f i z) ^ 2 ∂(dt.prod P)) :=
    Summable.of_nonneg_of_le
      (fun i => integral_nonneg (fun _ => sq_nonneg _))
      hBound hS
  exact r26t6c_square_ae_of_integrated_sum (dt.prod P) f h2 hIntSum

end HRS.MS.R26T6C
