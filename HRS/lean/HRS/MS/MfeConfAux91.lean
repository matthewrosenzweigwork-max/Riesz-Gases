import HRS.MS.MfeConfAux90

/-!
# S.B.1, packet F8 (part 23): `K̇_s` is continuous and bounded; `κ` and `κ'` (continuity, bounds, derivative)
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace HRS.MS.MfeConf

variable {d N : ℕ}

section Traj

variable {D : Whole.WholeDyn d} {T C B C3 : ℝ} {ρ : ℝ → Euc d → ℝ} (H : Sb1Tr3 D T C B C3 ρ) (hT : 0 ≤ T)
  {r₀ : ℝ} {k : Euc d → ℝ}

include H hT

theorem sb1_lv_En_cont (hk4 : IsP4Kernel d D.s r₀ k) (X : Whole.EucConfig d N) :
    Continuous fun s => sb1En k (ρ (sb1_lv_cl' hT s)) X := by
  obtain ⟨A, hA⟩ := sb1_lv_gr_k hk4 H.tr.hs0
  have hG := sb1_lv_G_cont H hT hA hk4.smooth.continuous
  have hc := sb1_lv_cb_cont H hT (sb1KerU_of_p4 H.tr.hs0 hk4)
  unfold sb1En
  have h2 : ∀ a : Fin N, Continuous fun s => sb1G k (ρ (sb1_lv_cl' hT s)) (X a) := fun a =>
    sb1_lv_curry_s (F := fun s x => sb1G k (sb1_lv_rb hT ρ s) x) hG (X a)
  exact (continuous_const.sub (continuous_const.mul (continuous_finset_sum _ fun a _ => h2 a))).add
    (continuous_const.mul hc)

theorem sb1_lv_Wdot_cont (hk4 : IsP4Kernel d D.s r₀ k) (β : ℝ) (X : Whole.EucConfig d N) :
    Continuous fun s => sb1Wdot D ρ k β N (sb1_lv_cl' hT s) X := by
  obtain ⟨A, hA⟩ := sb1_lv_gr_k hk4 H.tr.hs0
  have hGd := sb1_lv_Gd_cont H hT hA hk4.smooth.continuous
  have hr := sb1_lv_rb_cont H hT
  have hAt := sb1At_cont H.tr hT
  have hcd := sb1_lv_cdot_cont H hT hk4
  have hEn := sb1_lv_En_cont H hT hk4 X
  have hρ : ∀ y : Euc d, Continuous fun s => ρ (sb1_lv_cl' hT s) y := fun y =>
    sb1_lv_curry_s (F := fun s x => sb1_lv_rb hT ρ s x) hr y
  have hA' : ∀ y : Euc d, Continuous fun s => sb1A D (ρ (sb1_lv_cl' hT s)) y := fun y =>
    sb1_lv_curry_s (F := fun s x => sb1At D hT ρ s x) hAt y
  have hGd' : ∀ y : Euc d, Continuous fun s => sb1Gd D ρ k (sb1_lv_cl' hT s) y := fun y =>
    sb1_lv_curry_s (F := fun s x => sb1_lv_cv k (sb1At D hT ρ s) x) hGd y
  unfold sb1Wdot sb1EnDot
  refine ((continuous_finset_sum _ fun i _ => (hA' (X i)).mul (continuous_finset_prod _ fun l _ => hρ (X l))).mul
    (Real.continuous_exp.comp (continuous_const.mul hEn))).add ?_
  refine (continuous_finset_prod _ fun i _ => hρ (X i)).mul ((Real.continuous_exp.comp (continuous_const.mul hEn)).mul
    (continuous_const.mul ((continuous_const.mul (continuous_finset_sum _ fun a _ => hGd' (X a))).add
      (continuous_const.mul hcd))))

theorem sb1_lv_Kdot_cont (hk4 : IsP4Kernel d D.s r₀ k) {β : ℝ} (hβ : 0 ≤ β) (hN : 1 ≤ N) :
    Continuous (sb1_lv_Kdot D k β N hT ρ) := by
  have hk := sb1KerU_of_p4 H.tr.hs0 hk4
  obtain ⟨Lg, hRg⟩ := sb1_lv_kerR hk4 H.tr.hs0
  have hBd : Integrable (fun X : Whole.EucConfig d N => ∏ l, sb1w ((d : ℝ) + 2) (X l)) volume :=
    Integrable.fintype_prod (fun _ => sb1w_int H.tr.hd (p := (d : ℝ) + 2) (by linarith))
  unfold sb1_lv_Kdot
  refine continuous_of_dominated (bound := fun X => sb1Kb d D B C C3 β N * ∏ l, sb1w ((d : ℝ) + 2) (X l))
    (fun s => ?_) (fun s => Eventually.of_forall fun X => ?_) (hBd.const_mul _)
    (Eventually.of_forall fun X => sb1_lv_Wdot_cont H hT hk4 β X)
  · exact (sb1_Wdot_meas H hk hRg (sb1_lv_cl'_mem hT s)).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    exact sb1_Wdot_bound H hk hβ hN (sb1_lv_cl'_mem hT s) X

end Traj

end HRS.MS.MfeConf
