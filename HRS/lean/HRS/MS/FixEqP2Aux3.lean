import HRS.MS.FixEqP2Aux2

/-!
# S5.7 `fixed_equation` (worker S57P), part 6: parametric integrals of `C^{n+1}`-bounded families

`s57p_param_jets`: for a family `F u`, `u ∈ (a,b]`, of functions that are `C^{n+1}` with all derivatives of order `≤ n+1`
bounded by `B` and whose jets of order `≤ n` are continuous in `u` at every point, the integral `∫_a^b F u` is `C^n` and its
jets are the integrals of the jets.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.FixEq

open HRS HRS.Whole

variable {d : ℕ}

theorem s57p_integral_lie {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (L : E ≃ₗᵢ[ℝ] F) (φ : X → E) : ∫ x, L (φ x) ∂μ = L (∫ x, φ x ∂μ) :=
  L.toLinearIsometry.integral_comp_comm φ

theorem s57p_param_jets (n : ℕ) {a b B : ℝ} (hab : a ≤ b) {F : ℝ → Euc d → ℝ}
    (hF : ∀ u ∈ Set.Ioc a b, ContDiff ℝ (n + 1 : ℕ) (F u) ∧ ∀ j ≤ n + 1, ∀ y, ‖iteratedFDeriv ℝ j (F u) y‖ ≤ B)
    (hc : ∀ j ≤ n, ∀ y, ContinuousOn (fun u => iteratedFDeriv ℝ j (F u) y) (Set.Ioc a b)) :
    ContDiff ℝ n (fun y => ∫ u in a..b, F u y) ∧
      ∀ j ≤ n, ∀ y, iteratedFDeriv ℝ j (fun y => ∫ u in a..b, F u y) y =
        ∫ u in a..b, iteratedFDeriv ℝ j (F u) y := by
  simp only [intervalIntegral.integral_of_le hab]
  set μ : Measure ℝ := volume.restrict (Set.Ioc a b) with hμ
  haveI : IsFiniteMeasure μ := ⟨by simp [hμ]⟩
  set Zf : Euc d → ℝ := fun y => ∫ u in Set.Ioc a b, F u y with hZf
  have hmeasu : ∀ j ≤ n, ∀ y, AEStronglyMeasurable (fun u => iteratedFDeriv ℝ j (F u) y) μ :=
    fun j hj y => (hc j hj y).aestronglyMeasurable measurableSet_Ioc
  have hBj : ∀ u ∈ Set.Ioc a b, ∀ j ≤ n + 1, ∀ y, ‖iteratedFDeriv ℝ j (F u) y‖ ≤ B := fun u hu => (hF u hu).2
  have hdiffj : ∀ u ∈ Set.Ioc a b, ∀ j ≤ n, Differentiable ℝ (iteratedFDeriv ℝ j (F u)) := fun u hu j hj =>
    (hF u hu).1.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_of_le hj)
  -- the derivative of the `j`-th jet
  have hstep : ∀ j < n, ∀ y, HasFDerivAt (fun y => ∫ u in Set.Ioc a b, iteratedFDeriv ℝ j (F u) y)
      (∫ u in Set.Ioc a b, fderiv ℝ (iteratedFDeriv ℝ j (F u)) y) y := by
    intro j hj y
    have hae : ∀ᵐ u ∂μ, u ∈ Set.Ioc a b := by
      rw [hμ]; exact ae_restrict_mem measurableSet_Ioc
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun z u => iteratedFDeriv ℝ j (F u) z)
      (F' := fun z u => fderiv ℝ (iteratedFDeriv ℝ j (F u)) z) (bound := fun _ => B) (s := Set.univ)
      Filter.univ_mem ?_ ?_ ?_ ?_ (integrable_const _) ?_
    · exact Eventually.of_forall fun z => hmeasu j hj.le z
    · exact (integrable_const B).mono' (hmeasu j hj.le y) (by
        filter_upwards [hae] with u hu
        exact hBj u hu j (by omega) y)
    · have h1 : ∀ z, AEStronglyMeasurable (fun u => fderiv ℝ (iteratedFDeriv ℝ j (F u)) z) μ := by
        intro z
        have e : (fun u => fderiv ℝ (iteratedFDeriv ℝ j (F u)) z) = fun u =>
            (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => Euc d) ℝ)
              (iteratedFDeriv ℝ (j + 1) (F u) z) := by
          funext u
          rw [iteratedFDeriv_succ_eq_comp_left]
          simp
        rw [e]
        exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => Euc d) ℝ).continuous.comp_aestronglyMeasurable
          (hmeasu (j + 1) hj z)
      exact h1 y
    · filter_upwards [hae] with u hu z _
      rw [norm_fderiv_iteratedFDeriv]
      exact hBj u hu (j + 1) (by omega) z
    · filter_upwards [hae] with u hu z _
      exact ((hdiffj u hu j hj.le) z).hasFDerivAt
  have hA : ∀ j ≤ n, ∀ y, iteratedFDeriv ℝ j Zf y = ∫ u in Set.Ioc a b, iteratedFDeriv ℝ j (F u) y := by
    intro j
    induction j with
    | zero =>
      intro _ y
      rw [iteratedFDeriv_zero_eq_comp]
      simp only [Function.comp_apply, hZf]
      have := s57p_integral_lie (μ := μ) (continuousMultilinearCurryFin0 ℝ (Euc d) ℝ).symm (fun u => F u y)
      rw [← this]
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      simp [iteratedFDeriv_zero_eq_comp]
    | succ j ih =>
      intro hj y
      have hjn : j < n := by omega
      have e1 : iteratedFDeriv ℝ j Zf = fun y => ∫ u in Set.Ioc a b, iteratedFDeriv ℝ j (F u) y :=
        funext (ih (by omega))
      rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, e1, (hstep j hjn y).fderiv]
      have := s57p_integral_lie (E := Euc d →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin j => Euc d) ℝ) (μ := μ) (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => Euc d) ℝ).symm
        (fun u => fderiv ℝ (iteratedFDeriv ℝ j (F u)) y)
      rw [← this]
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      simp only [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply]
  refine ⟨?_, fun j hj y => hA j hj y⟩
  suffices h : ContDiff ℝ ((n : ℕ∞)) Zf by exact_mod_cast h
  rw [contDiff_iff_continuous_differentiable]
  refine ⟨fun m hm => ?_, fun m hm => ?_⟩
  · have e : (fun y => iteratedFDeriv ℝ m Zf y) = fun y => ∫ u in Set.Ioc a b, iteratedFDeriv ℝ m (F u) y :=
      funext (hA m (by exact_mod_cast hm))
    rw [e]
    have hmn : m ≤ n := by exact_mod_cast hm
    refine continuous_of_dominated (bound := fun _ => B) (fun y => hmeasu m hmn y) (fun y => ?_) (integrable_const _) ?_
    · have hae : ∀ᵐ u ∂μ, u ∈ Set.Ioc a b := by rw [hμ]; exact ae_restrict_mem measurableSet_Ioc
      filter_upwards [hae] with u hu
      exact hBj u hu m (by omega) y
    · have hae : ∀ᵐ u ∂μ, u ∈ Set.Ioc a b := by rw [hμ]; exact ae_restrict_mem measurableSet_Ioc
      filter_upwards [hae] with u hu
      exact ((hF u hu).1.continuous_iteratedFDeriv (by exact_mod_cast Nat.le_succ_of_le hmn))
  · have hmn : m < n := by exact_mod_cast hm
    have e : (fun y => iteratedFDeriv ℝ m Zf y) = fun y => ∫ u in Set.Ioc a b, iteratedFDeriv ℝ m (F u) y :=
      funext (hA m hmn.le)
    rw [e]
    exact fun y => (hstep m hmn y).differentiableAt

end HRS.MS.FixEq
