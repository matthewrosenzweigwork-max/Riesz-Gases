import HRS.MS.Fp81S21CovCumulative6

/-!
# HRS S2.1(iii), packet 19c-i: reconstruct tensor measurability from evaluations

A projective covariance tensor is measurable once its countable evaluation
coordinates are measurable.  The proof uses the finite path projections and
their convergence on the projective tensor subspace.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R2Interp HRS.Sec7 HRS.MC.Sec7.S7PIG5

set_option maxSynthPendingDepth 3 in
/-- A projective tensor-valued map is a.e. measurable when all its path
evaluation-pairing coordinates are a.e. measurable. -/
theorem fp81s21_projTensor_aemeasurable_of_pairing_coordinates
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {d : ℕ} {m T : ℝ} (hT : 0 < T)
    (F : Ω → projTensor (OscPath d m T) 2)
    (hcoord : ∀ (ta tb : Set.Icc (0 : ℝ) T) (α β : MultiIndex d),
      AEMeasurable
        (fun ω => (F ω : TensorDual (OscPath d m T) 2)
          ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap
            ![s102_ell ta α, s102_ell tb β])) P) :
    AEMeasurable F P := by
  classical
  let B := OscPath d m T
  haveI : SecondCountableTopology B := by infer_instance
  haveI : SecondCountableTopology (projTensor B 2) :=
    HRS.MS.R26T3.s21g2_k06_sc (B := B) 2
  letI : MeasurableAdd₂ (projTensor B 2) := ⟨continuous_add.measurable⟩
  let Q : ℕ → projTensor B 2 →L[ℝ] projTensor B 2 := fun L =>
    ((tensorPow 2 (s102_Pj T hT L)).comp (projTensor B 2).subtypeL).codRestrict
      (projTensor B 2) (fun e => S7PIG5_tensorPow_mem 2 (s102_Pj T hT L) e.2)
  have hQ : ∀ L ω,
      Q L (F ω) =
        ∑ r ∈ Fintype.piFinset (fun _ : Fin 2 => s102_idx d L),
          ((F ω : TensorDual B 2)
            ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap
              ![s102_ellp hT L (r 0), s102_ellp hT L (r 1)])) •
            (⟨elemTensor (fun i : Fin 2 => s102_bpath T L (r i)),
              HRS.MC.E213T.elemTensor_mem_projTensor _⟩ : projTensor B 2) := by
    intro L ω
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro M
    change (F ω : TensorDual B 2)
        (M.compContinuousLinearMap fun _ => s102_Pj T hT L) = _
    rw [s102_pair_expand]
    simp [elemTensor_apply, smul_eq_mul, mul_comm]
  have happrox : ∀ L, AEMeasurable (fun ω => Q L (F ω)) P := by
    intro L
    rw [show (fun ω => Q L (F ω)) = fun ω =>
      ∑ r ∈ Fintype.piFinset (fun _ : Fin 2 => s102_idx d L),
        ((F ω : TensorDual B 2)
          ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap
            ![s102_ellp hT L (r 0), s102_ellp hT L (r 1)])) •
          (⟨elemTensor (fun i : Fin 2 => s102_bpath T L (r i)),
            HRS.MC.E213T.elemTensor_mem_projTensor _⟩ : projTensor B 2) from by
        funext ω
        exact hQ L ω]
    refine Finset.aemeasurable_fun_sum _ fun r _ => ?_
    have ht0 : (s102_node hT L (r 0).1 : ℝ) ∈ Icc (0 : ℝ) T :=
      (s102_node hT L (r 0).1).2
    have ht1 : (s102_node hT L (r 1).1 : ℝ) ∈ Icc (0 : ℝ) T :=
      (s102_node hT L (r 1).1).2
    have hc := hcoord (s102_node hT L (r 0).1) (s102_node hT L (r 1).1)
      (r 0).2 (r 1).2
    have hc' : AEMeasurable
        (fun ω => (F ω : TensorDual B 2)
          ((ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin 2) ℝ).compContinuousLinearMap
            ![s102_ellp hT L (r 0), s102_ellp hT L (r 1)])) P := by
      convert hc using 1 <;> simp [s102_ellp, s102_ell]
    exact hc'.smul_const _
  have hconv : ∀ ω, Tendsto (fun L => Q L (F ω)) atTop (𝓝 (F ω)) := by
    intro ω
    have hstrong := (s102_projection_strong (d := d) m T hT).2.2
    exact tendsto_subtype_rng.2 (hstrong 2 (F ω : TensorDual B 2) (F ω).2)
  apply aemeasurable_of_tendsto_metrizable_ae' happrox
  filter_upwards [] with ω
  exact hconv ω

#print axioms HRS.Fp81.S21.fp81s21_projTensor_aemeasurable_of_pairing_coordinates

end HRS.Fp81.S21

end
