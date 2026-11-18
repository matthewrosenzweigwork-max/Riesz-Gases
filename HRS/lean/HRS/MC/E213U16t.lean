import HRS.MC.E213U16s
import HRS.MC.E213U11e
import HRS.MC.S7PIG2

/-!
# Packet e213u16, file t: the interval structure of the window covariance tensor `winJ`

* `u16_Jstruct`: for a bounded measurable coefficient, `winJ` over `(u,u']` is bounded by `C M (u'-u)` and additive in
  the interval;
* `u16_exists_LambdaI`: `w ↦ winJ(embed ∘ cp w)((u,u'])` is a continuous linear map.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace HRS.MC.E213U16

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Q HRS.MC.E213U13 HRS.MC.E213Plan
open HRS.MC.E213U10 HRS.MC.E213U11

variable {d : ℕ}

section Jstruct

variable {S : PreparedData d} {β₀ m : ℝ}

theorem u16_Jstruct (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (zr : ℝ → NegSobolev d (rLvl d)), Measurable zr → ∀ M : ℝ,
      (∀ v ∈ Set.Icc (0 : ℝ) (a + T), ‖zr v‖ ≤ M) →
      (∀ u u' : ℝ, 0 ≤ u → u ≤ u' → u' ≤ a + T →
        ‖winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (zr v)) (Set.Ioc u u')‖ ≤ C * M * (u' - u)) ∧
      (∀ u u' u'' : ℝ, 0 ≤ u → u ≤ u' → u' ≤ u'' → u'' ≤ a + T →
        winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (zr v)) (Set.Ioc u u'') =
          winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (zr v)) (Set.Ioc u u') +
          winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (zr v)) (Set.Ioc u' u'')) := by
  classical
  have hH : 0 < a + T := by linarith
  obtain ⟨C, hC⟩ := HRS.MC.Sec7.S7PIG1.s7_PIG_J_measure_proof (regime S β₀ hE) m hE.m_gt (a + T) hH
  refine ⟨max C 0, le_max_right _ _, fun zr hzr M hM => ?_⟩
  obtain ⟨Jc, -, hJc⟩ := hC zr hzr M hM
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, hH.le⟩)
  have key : ∀ u u' : ℝ, 0 ≤ u → u ≤ u' → u' ≤ a + T →
      winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (zr v)) (Set.Ioc u u') =
        tensorPow' 2 (winRestr a ha) (Jc u' - Jc u) := by
    intro u u' hu huu hu'
    obtain ⟨hIs, -, -⟩ := hJc u u' hu huu hu'
    unfold winJ
    rw [HRS.MC.E213U2.e213u2_jTensor_eq (regime S β₀ hE) m (a + T) (fun v => NegSobolev.embed m (zr v))
      (Set.Ioc u u') _ hIs]
  refine ⟨fun u u' hu huu hu' => ?_, fun u u' u'' hu huu huu' hu'' => ?_⟩
  · rw [key u u' hu huu hu']
    obtain ⟨-, hn, -⟩ := hJc u u' hu huu hu'
    refine (winRestr_tensorPow'_norm_le a ha 2 _).trans (hn.trans ?_)
    have : 0 ≤ M * (u' - u) := mul_nonneg hM0 (by linarith)
    nlinarith [le_max_left C 0]
  · rw [key u u'' hu (huu.trans huu') hu'', key u u' hu huu (huu'.trans hu''),
      key u' u'' (hu.trans huu) huu' hu'', ← map_add]
    congr 1
    abel

end Jstruct


section Lambda

variable {S : PreparedData d} {β₀ m : ℝ}

theorem u16_exists_LambdaI (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) {L : ℝ}
    (hL0 : 0 ≤ L) {u u' : ℝ} (hu : 0 ≤ u) (huu : u ≤ u') (hu' : u' ≤ a + T) :
    ∃ Λ : PathSpace d (rLvl d) L →L[ℝ] TensorDual (PathSpace d m T) 2,
      (∀ w, Λ w = winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (u11_cp hL0 w v)) (Set.Ioc u u')) ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ w, ‖Λ w‖ ≤ K * ‖w‖ := by
  classical
  obtain ⟨C, hC0, hC⟩ := u16_Jstruct hE T hT a ha
  have hH : 0 < a + T := by linarith
  have hadd : ∀ w w' : PathSpace d (rLvl d) L,
      winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (u11_cp hL0 (w + w') v)) (Set.Ioc u u') =
        winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (u11_cp hL0 w v)) (Set.Ioc u u') +
        winJ (regime S β₀ hE) m T a ha (fun v => NegSobolev.embed m (u11_cp hL0 w' v)) (Set.Ioc u u') := by
    intro w w'
    exact HRS.MC.E213U2.winJ_add_proof hE T hT a ha (u11_cp hL0 w) (u11_cp hL0 w')
      (u11_measurable_nearCoef_of_continuous (u11_cp_continuous hL0 w))
      (u11_measurable_nearCoef_of_continuous (u11_cp_continuous hL0 w')) ‖w‖ ‖w'‖
      (u11_cp_bounds hL0 w _ _) (u11_cp_bounds hL0 w' _ _) u u' hu huu hu'
  let f : PathSpace d (rLvl d) L →+ TensorDual (PathSpace d m T) 2 :=
    AddMonoidHom.mk' (fun w => winJ (regime S β₀ hE) m T a ha
      (fun v => NegSobolev.embed m (u11_cp hL0 w v)) (Set.Ioc u u')) hadd
  have hbound : ∀ w, ‖f w‖ ≤ (C * (u' - u)) * ‖w‖ := by
    intro w
    have h := (hC (u11_cp hL0 w) (u11_cp_continuous hL0 w).measurable ‖w‖ (u11_cp_bounds hL0 w _ _)).1 u u' hu huu hu'
    calc ‖f w‖ ≤ C * ‖w‖ * (u' - u) := h
      _ = (C * (u' - u)) * ‖w‖ := by ring
  have hcont : Continuous f := AddMonoidHomClass.continuous_of_bound f _ hbound
  let Lm : PathSpace d (rLvl d) L →L[ℝ] TensorDual (PathSpace d m T) 2 :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun c x => map_real_smul f hcont c x
      cont := hcont }
  exact ⟨Lm, fun w => rfl, C * (u' - u), mul_nonneg hC0 (by linarith), hbound⟩

end Lambda

end HRS.MC.E213U16

end
