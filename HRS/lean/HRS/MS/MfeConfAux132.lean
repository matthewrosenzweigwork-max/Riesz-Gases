import HRS.MS.MfeConfAux131

/-!
# S.B.1, R2 (part 3): measurability of the level-`k` remainder `B^k_r`

`sb1_lv_B_meas`: `Z ↦ ∑_i (B^k_one(Z_i) + B^k_pair(Z,i))` is measurable (all pieces are continuous or are derivatives of
smooth functions, hence Borel measurable by `measurable_fderiv`).
-/

open MeasureTheory Filter Topology InformationTheory
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace HRS.MS.MfeConf

variable {d N : ℕ}

theorem sb1_gradient_meas (f : Euc d → ℝ) : Measurable (gradient f) :=
  (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.measurable.comp (measurable_fderiv ℝ f)

theorem sb1_meas_clm_apply {φ : Euc d → (Euc d →L[ℝ] ℝ)} {v : Euc d → Euc d} (hφ : Measurable φ)
    (hv : Measurable v) : Measurable fun x => φ x (v x) :=
  (continuous_fst.clm_apply continuous_snd).measurable.comp (hφ.prodMk hv)

section Main

variable {D : Whole.WholeDyn d} {T C B C3 : ℝ} {ρ : ℝ → Euc d → ℝ} (H : Sb1Tr3 D T C B C3 ρ) (hT : 0 ≤ T)
  {r₀ : ℝ} {k : Euc d → ℝ}

include H hT

theorem sb1_lv_Bone_meas (hk4 : IsP4Kernel d D.s r₀ k) (s : ℝ) : Measurable (sb1_lv_Bone D k hT ρ s) := by
  obtain ⟨A, hA⟩ := sb1_lv_gr_k hk4 H.tr.hs0
  have hS := sb1_lv_rb_slice H hT s
  have hU : Continuous (sb1_lv_U D k hT ρ s) := by
    have h := (sb1_lv_U_cont H hT hk4).comp (Continuous.prodMk_right (X := ℝ) (Y := Euc d) s)
    exact h
  have hdiv : Continuous (sb1divE (sb1_lv_U D k hT ρ s)) := by
    have h := (sb1_lv_divU_cont H hT hk4).comp (Continuous.prodMk_right (X := ℝ) (Y := Euc d) s)
    exact h
  have hAt : Continuous (sb1At D hT ρ s) := by
    have h := (sb1At_cont H.tr hT).comp (Continuous.prodMk_right (X := ℝ) (Y := Euc d) s)
    exact h
  have hr : Continuous (sb1_lv_rb hT ρ s) := by
    have h := (sb1_lv_rb_cont H hT).comp (Continuous.prodMk_right (X := ℝ) (Y := Euc d) s)
    exact h
  have hgd : Continuous (sb1_lv_cv k (sb1At D hT ρ s)) := by
    have h := (sb1_lv_Gd_cont H hT hA hk4.smooth.continuous).comp (Continuous.prodMk_right (X := ℝ) (Y := Euc d) s)
    exact h
  have hv : Continuous (Whole.mfeTransportW D (sb1_lv_rb hT ρ s)) :=
    (sb1_lv_v_contDiff H.tr.V H.tr.hd H.tr.hs0 H.tr.hsd hS (sb1_lv_rb_pos H hT s)).continuous
  have hVm : Measurable fun x => inner ℝ (sb1_lv_U D k hT ρ s x) (gradient D.V x) := by
    have e : (fun x => inner ℝ (sb1_lv_U D k hT ρ s x) (gradient D.V x)) =
        fun x => fderiv ℝ D.V x (sb1_lv_U D k hT ρ s x) := funext fun x => by
      rw [real_inner_comm, p4k_inner_grad]
    rw [e]
    exact sb1_meas_clm_apply (measurable_fderiv ℝ D.V) hU.measurable
  have hGm : Measurable fun x => fderiv ℝ (sb1G k (sb1_lv_rb hT ρ s)) x
      (Whole.mfeTransportW D (sb1_lv_rb hT ρ s) x) :=
    sb1_meas_clm_apply (measurable_fderiv ℝ _) hv.measurable
  have hAm : Measurable fun x => sb1A D (sb1_lv_rb hT ρ s) x / sb1_lv_rb hT ρ s x :=
    hAt.measurable.div hr.measurable
  unfold sb1_lv_Bone sb1_lv_Th sb1_lv_Theta
  exact ((((hdiv.measurable.const_mul _).sub hVm).add (hU.norm.pow 2).measurable).add
    (((hAm.const_mul _).add hgd.measurable).neg)).sub (hGm.sub hgd.measurable) |>.div_const _

theorem sb1_lv_B_meas (hk4 : IsP4Kernel d D.s r₀ k) (s : ℝ) : Measurable (sb1_lv_B (N := N) D k hT ρ s) := by
  obtain ⟨A, hA⟩ := sb1_lv_gr_k hk4 H.tr.hs0
  have hU : Continuous (sb1_lv_U D k hT ρ s) := by
    have h := (sb1_lv_U_cont H hT hk4).comp (Continuous.prodMk_right (X := ℝ) (Y := Euc d) s)
    exact h
  have hS := sb1_lv_rb_slice H hT s
  have hv : Continuous (Whole.mfeTransportW D (sb1_lv_rb hT ρ s)) :=
    (sb1_lv_v_contDiff H.tr.V H.tr.hd H.tr.hs0 H.tr.hsd hS (sb1_lv_rb_pos H hT s)).continuous
  have he : Measurable (sb1_lv_e D k hT ρ s) := (hU.sub hv).measurable
  unfold sb1_lv_B
  refine Finset.measurable_sum _ fun i _ => ?_
  refine ((sb1_lv_Bone_meas H hT hk4 s).comp (measurable_pi_apply i)).add ?_
  unfold sb1_lv_Bpair sb1_lv_pairV
  refine Measurable.div_const (Measurable.neg ?_) _
  refine Measurable.inner (he.comp (measurable_pi_apply i)) ?_
  have hsum : Measurable fun Z : EucConfig d N => ∑ j ∈ Finset.univ.erase i, gradient k (Z i - Z j) :=
    Finset.measurable_sum _ fun j _ =>
      (sb1_gradient_meas k).comp ((measurable_pi_apply i).sub (measurable_pi_apply j))
  exact hsum.const_smul (1 / (N : ℝ))

end Main

end HRS.MS.MfeConf
