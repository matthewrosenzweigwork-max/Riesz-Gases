import HRS.Equilibrium.Parametrix.PX3aAuxA
import HRS.Equilibrium.Parametrix.PX2AuxB

/-!
# Packet PX3a auxiliaries B: differentiation under the integral on an open set
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Parx

universe u

section ParamOn

variable {α : Type*} [MeasurableSpace α] {ν : Measure α}
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Hypotheses for differentiation under the integral up to order `m`, on an open set `U`. -/
structure ParamHypOn {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (U : Set E) (m : ℕ) (K : E → α → F) (ν : Measure α) : Prop where
  smooth : ∀ᵐ w ∂ν, ContDiffOn ℝ m (fun x => K x w) U
  meas : ∀ k : ℕ, k ≤ m → ∀ x ∈ U,
    AEStronglyMeasurable (fun w => iteratedFDeriv ℝ k (fun x' => K x' w) x) ν
  bound : ∀ k : ℕ, k ≤ m → ∃ bd : α → ℝ, Integrable bd ν ∧
    ∀ᵐ w ∂ν, ∀ x ∈ U, ‖iteratedFDeriv ℝ k (fun x' => K x' w) x‖ ≤ bd w

theorem ParamHypOn.meas_zero {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} {m : ℕ} {K : E → α → F} (h : ParamHypOn U m K ν) {x : E} (hx : x ∈ U) :
    AEStronglyMeasurable (fun w => K x w) ν := by
  have h0 := h.meas 0 (Nat.zero_le _) x hx
  have : (fun w => K x w) = fun w => (continuousMultilinearCurryFin0 ℝ E F)
      (iteratedFDeriv ℝ 0 (fun x' => K x' w) x) := by
    funext w
    simp [iteratedFDeriv_zero_eq_comp]
  rw [this]
  exact (continuousMultilinearCurryFin0 ℝ E F).continuous.comp_aestronglyMeasurable h0

theorem ParamHypOn.succ {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {U : Set E} (hU : IsOpen U) {m : ℕ} {K : E → α → F} (h : ParamHypOn U (m + 1) K ν) :
    ParamHypOn U m (fun x w => fderiv ℝ (fun y => K y w) x) ν where
  smooth := by
    filter_upwards [h.smooth] with w hw
    exact hw.fderiv_of_isOpen hU (by norm_cast)
  meas := by
    intro k hk x hx
    have h1 := h.meas (k + 1) (by omega) x hx
    have : (fun w => iteratedFDeriv ℝ k (fun x' => fderiv ℝ (fun y => K y w) x') x) =
        fun w => (continuousMultilinearCurryRightEquiv' ℝ k E F)
          (iteratedFDeriv ℝ (k + 1) (fun x' => K x' w) x) := by
      funext w
      rw [iteratedFDeriv_succ_eq_comp_right]
      simp
    rw [this]
    exact (continuousMultilinearCurryRightEquiv' ℝ k E F).continuous.comp_aestronglyMeasurable h1
  bound := by
    intro k hk
    obtain ⟨bd, hbd, hb⟩ := h.bound (k + 1) (by omega)
    refine ⟨bd, hbd, ?_⟩
    filter_upwards [hb] with w hw x hx
    rw [norm_iteratedFDeriv_fderiv]
    exact hw x hx

theorem integrable_zeroth_on {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} {m : ℕ} {K : E → α → F} (h : ParamHypOn U m K ν) {x : E} (hx : x ∈ U) :
    Integrable (fun w => K x w) ν := by
  obtain ⟨bd, hbd, hb⟩ := h.bound 0 (Nat.zero_le _)
  refine hbd.mono' (h.meas_zero hx) ?_
  filter_upwards [hb] with w hw
  have := hw x hx
  rwa [norm_iteratedFDeriv_zero] at this

theorem contDiffOn_integral_param_aux {U : Set E} (hU : IsOpen U) : ∀ (m : ℕ) {F : Type u}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (K : E → α → F),
    ParamHypOn U m K ν →
    ContDiffOn ℝ m (fun x => ∫ w, K x w ∂ν) U ∧ ∀ k : ℕ, k ≤ m → ∀ x ∈ U,
      iteratedFDeriv ℝ k (fun x' => ∫ w, K x' w ∂ν) x =
        ∫ w, iteratedFDeriv ℝ k (fun x' => K x' w) x ∂ν
  | 0, F, _, _, _, K, h => by
    have hk0 : ∀ x, iteratedFDeriv ℝ 0 (fun x' => ∫ w, K x' w ∂ν) x =
        ∫ w, iteratedFDeriv ℝ 0 (fun x' => K x' w) x ∂ν := by
      intro x
      simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
      exact ((continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.integral_comp_comm
        (fun w => K x w)).symm
    refine ⟨?_, fun k hk x _ => ?_⟩
    · rw [Nat.cast_zero, contDiffOn_zero]
      obtain ⟨bd, hbd, hb⟩ := h.bound 0 (Nat.zero_le _)
      refine continuousOn_of_dominated (bound := bd) (fun x hx => h.meas_zero hx) (fun x hx => ?_) hbd ?_
      · filter_upwards [hb] with w hw
        have := hw x hx
        rwa [norm_iteratedFDeriv_zero] at this
      · filter_upwards [h.smooth] with w hw
        exact (contDiffOn_zero (𝕜 := ℝ)).mp (by simpa using hw)
    · have : k = 0 := by omega
      subst this
      exact hk0 x
  | m + 1, F, _, _, _, K, h => by
    have hK' := h.succ hU
    obtain ⟨ih1, ih2⟩ := contDiffOn_integral_param_aux hU m (fun x w => fderiv ℝ (fun y => K y w) x) hK'
    have hderiv : ∀ x ∈ U, HasFDerivAt (fun x' => ∫ w, K x' w ∂ν)
        (∫ w, fderiv ℝ (fun y => K y w) x ∂ν) x := by
      intro x hx
      obtain ⟨bd, hbd, hb⟩ := h.bound 1 (by omega)
      refine hasFDerivAt_integral_of_dominated_of_fderiv_le (s := U) (bound := bd)
        (F' := fun x w => fderiv ℝ (fun y => K y w) x)
        (hU.mem_nhds hx) (Filter.eventually_of_mem (hU.mem_nhds hx) fun x' hx' => h.meas_zero hx')
        (integrable_zeroth_on h hx) (hK'.meas_zero hx) ?_ hbd ?_
      · filter_upwards [hb] with w hw x' hx'
        have := hw x' hx'
        have e : ‖iteratedFDeriv ℝ 1 (fun x'' => K x'' w) x'‖ =
            ‖fderiv ℝ (fun y => K y w) x'‖ := by
          have := (norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := fun x'' => K x'' w) (x := x') (n := 0)).symm
          rw [this, norm_iteratedFDeriv_zero]
        rwa [e] at this
      · filter_upwards [h.smooth] with w hw x' hx'
        exact ((hw.differentiableOn (by simp)) x' hx').differentiableAt (hU.mem_nhds hx') |>.hasFDerivAt
    have hfd : ∀ x ∈ U, fderiv ℝ (fun x' => ∫ w, K x' w ∂ν) x =
        ∫ w, fderiv ℝ (fun y => K y w) x ∂ν := fun x hx => (hderiv x hx).fderiv
    refine ⟨?_, fun k hk x hx => ?_⟩
    · rw [Nat.cast_succ]
      refine (contDiffOn_succ_iff_fderiv_of_isOpen hU).mpr ⟨?_, ?_, ?_⟩
      · exact fun x hx => (hderiv x hx).differentiableAt.differentiableWithinAt
      · intro h; exact absurd h (by simp)
      · exact ih1.congr hfd
    · rcases k with _ | j
      · simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
        exact ((continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv.integral_comp_comm
          (fun w => K x w)).symm
      · rw [iteratedFDeriv_succ_eq_comp_right]
        simp only [Function.comp_apply]
        have hev : fderiv ℝ (fun x' => ∫ w, K x' w ∂ν) =ᶠ[𝓝 x]
            fun y => ∫ w, fderiv ℝ (fun y' => K y' w) y ∂ν :=
          Filter.eventually_of_mem (hU.mem_nhds hx) hfd
        rw [(hev.iteratedFDeriv ℝ j).eq_of_nhds, ih2 j (by omega) x hx]
        have e := (continuousMultilinearCurryRightEquiv' ℝ j E F).symm.toContinuousLinearEquiv.integral_comp_comm
          (μ := ν) (fun w => iteratedFDeriv ℝ j (fun x' => fderiv ℝ (fun y => K y w) x') x)
        simp only [LinearIsometryEquiv.coe_toContinuousLinearEquiv] at e
        rw [← e]
        refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
        simp only [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply]


theorem contDiffOn_integral_param {U : Set E} (hU : IsOpen U) {m : ℕ} {F : Type u}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {K : E → α → F}
    (h : ParamHypOn U m K ν) :
    ContDiffOn ℝ m (fun x => ∫ w, K x w ∂ν) U ∧ ∀ k : ℕ, k ≤ m → ∀ x ∈ U,
      iteratedFDeriv ℝ k (fun x' => ∫ w, K x' w ∂ν) x =
        ∫ w, iteratedFDeriv ℝ k (fun x' => K x' w) x ∂ν :=
  contDiffOn_integral_param_aux hU m K h

end ParamOn

end HRS.Parx

end
