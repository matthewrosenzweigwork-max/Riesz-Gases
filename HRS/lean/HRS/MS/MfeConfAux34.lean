import HRS.MS.MfeConfAux33

/-!
# S.B.1, packet F3 (part 15): continuity in time of `ρ_r`, `G_r`, `c_r` and of the normaliser `K_r` on `[0,T]`
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d N : ℕ}

section TimeCont

variable {D : Whole.WholeDyn d} {T C B C3 : ℝ} {ρ : ℝ → Euc d → ℝ} {k : Euc d → ℝ}

theorem sb1_rho_contOn (H : Sb1Tr3 D T C B C3 ρ) (y : Euc d) : ContinuousOn (fun r => ρ r y) (Set.Icc 0 T) := by
  rw [continuousOn_iff_continuous_restrict]
  exact (sb1_rho_cont H.tr).comp (continuous_id.prodMk continuous_const)

theorem sb1CG_tr3_nonneg (H : Sb1Tr3 D T C B C3 ρ) :
    0 ≤ sb1CG d D.s C3 (C3 * ∫ y : Euc d, sb1w ((d : ℝ) + 2) y) := by
  have h1 : 0 ≤ ∫ y : Euc d, sb1w ((d : ℝ) + 2) y := integral_nonneg fun y => (sb1w_pos _ _).le
  have h2 := sb1Isig_nonneg (d := d) (sb1sig D.s)
  have := H.C3nn
  unfold sb1CG
  positivity

theorem sb1_G_contOn (H : Sb1Tr3 D T C B C3 ρ) (hk : Sb1KerU d D.s k) (x : Euc d) :
    ContinuousOn (fun r => sb1G k (ρ r) x) (Set.Icc 0 T) := by
  have hd := H.tr.hd
  obtain ⟨hψi, hψ1⟩ := sb1_psiA (d := d) hd (a := C3)
  obtain ⟨hI, -⟩ := sb1_Om_conv hd H.tr.hs0 H.tr.hsd (ψ := fun y => C3 * sb1w ((d : ℝ) + 2) y)
    (fun y => mul_nonneg H.C3nn (sb1w_pos _ _).le) (measurable_const.mul (sb1w_meas _)) hψi
    (Cψ := C3) (fun y => mul_le_of_le_one_right H.C3nn (sb1w_le_one (by positivity) y)) hψ1 x
  refine continuousOn_of_dominated (bound := fun y => C3 * sb1w ((d : ℝ) + 2) y * sb1Om D.s (x - y))
    (fun r hr => ?_) (fun r hr => ?_) hI (Eventually.of_forall fun y => ?_)
  · exact ((H.tr.cont hr).measurable.mul (hk.meas.comp (measurable_const.sub measurable_id))).aestronglyMeasurable
  · filter_upwards [sb1_ae_ne hd x] with y hy
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (sb1_rho_absw H hr y) (sb1_k_abs_le H.tr.hs0 hk (sub_ne_zero.2 (Ne.symm hy)))
      (abs_nonneg _) (mul_nonneg H.C3nn (sb1w_pos _ _).le)
  · exact (sb1_rho_contOn H y).mul continuousOn_const

theorem sb1_c_contOn (H : Sb1Tr3 D T C B C3 ρ) (hk : Sb1KerU d D.s k) :
    ContinuousOn (fun r => sb1c k (ρ r)) (Set.Icc 0 T) := by
  have hd := H.tr.hd
  have hw2 := sb1w_int hd (p := (d : ℝ) + 2) (by linarith)
  have hC3 := H.C3nn
  have hCG0 := sb1CG_tr3_nonneg H
  refine continuousOn_of_dominated
    (bound := fun x => C3 * (1 + sb1CG d D.s C3 (C3 * ∫ y : Euc d, sb1w ((d : ℝ) + 2) y)) * sb1w ((d : ℝ) + 2) x)
    (fun r hr => ?_) (fun r hr => ?_) (hw2.const_mul _) (Eventually.of_forall fun x => ?_)
  · exact ((H.tr.cont hr).measurable.mul (sb1_G_meas hk (H.rho hd hr))).aestronglyMeasurable
  · refine Eventually.of_forall fun x => ?_
    have Rr := H.rho hd hr
    have hG := sb1_G_abs_le hd H.tr.hs0 H.tr.hsd hk Rr x
    have hρ := H.rho_le hr x
    have hρ0 := H.pos r hr x
    have e2 := sb1w_32 x
    have hn := norm_nonneg x
    have hl := sb1_log_le_norm x
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hρ0]
    calc ρ r x * |sb1G k (ρ r) x|
        ≤ (C3 * sb1w ((d : ℝ) + 3) x) * ((1 + sb1CG d D.s C3 (C3 * ∫ y : Euc d, sb1w ((d : ℝ) + 2) y)) * (1 + ‖x‖)) :=
          mul_le_mul hρ (hG.trans (by nlinarith [sb1_log_nonneg x, mul_nonneg hCG0 hn])) (abs_nonneg _)
            (mul_nonneg hC3 (sb1w_pos _ _).le)
      _ = _ := by rw [← e2]; ring
  · exact (sb1_rho_contOn H x).mul (sb1_G_contOn H hk x)

theorem sb1_En_contOn (H : Sb1Tr3 D T C B C3 ρ) (hk : Sb1KerU d D.s k) (X : Whole.EucConfig d N) :
    ContinuousOn (fun r => sb1En k (ρ r) X) (Set.Icc 0 T) := by
  unfold sb1En
  exact ((continuousOn_const.sub (continuousOn_const.mul (continuousOn_finset_sum _ fun a _ =>
    sb1_G_contOn H hk (X a)))).add (continuousOn_const.mul (sb1_c_contOn H hk)))

theorem sb1_Kk_contOn (H : Sb1Tr3 D T C B C3 ρ) (hk : Sb1KerU d D.s k) {β : ℝ} (hβ : 0 ≤ β) (hN : 1 ≤ N) :
    ContinuousOn (fun r => ∫ X : Whole.EucConfig d N, sb1Wf k β N ρ r X) (Set.Icc 0 T) := by
  have hd := H.tr.hd
  have hBd : Integrable (fun X : Whole.EucConfig d N => ∏ l, sb1w ((d : ℝ) + 2) (X l)) volume :=
    Integrable.fintype_prod (fun _ => sb1w_int hd (p := (d : ℝ) + 2) (by linarith))
  refine continuousOn_of_dominated
    (bound := fun X : Whole.EucConfig d N => sb1Cw d D.s C3 β N * C3 ^ N * ∏ l, sb1w ((d : ℝ) + 2) (X l))
    (fun r hr => ?_) (fun r hr => ?_) (hBd.const_mul _) (Eventually.of_forall fun X => ?_)
  · unfold sb1Wf
    exact ((Finset.measurable_prod _ fun i _ => (H.tr.cont hr).measurable.comp (measurable_pi_apply i)).mul
      (Real.measurable_exp.comp ((sb1_En_meas hk (H.rho hd hr)).const_mul _))).aestronglyMeasurable
  · exact Eventually.of_forall fun X => by rw [Real.norm_eq_abs]; exact sb1_Wf_bound H hk hβ hN hr X
  · unfold sb1Wf
    exact (continuousOn_finset_prod _ fun i _ => sb1_rho_contOn H (X i)).mul
      (Real.continuous_exp.comp_continuousOn (continuousOn_const.mul (sb1_En_contOn H hk X)))

end TimeCont

end HRS.MS.MfeConf
