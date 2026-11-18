import HRS.MS.MfeConfAux117

/-!
# S.B.1, packet F9 (part 21): integrability in time of the level-`M` Gibbs mean `E_{Q^M_r} C^M_r`
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d N : ℕ}

section Main

variable {D : Whole.WholeDyn d} {T C B C3 : ℝ} {ρ : ℝ → Euc d → ℝ} (H : Sb1Tr3 D T C B C3 ρ)

include H

theorem sb1_EQ_integrableOn (hT : 0 ≤ T) (hβ : 0 < D.invβ) (hN : 1 ≤ N) (Kf : ℝ → ℝ)
    (hKi : IntegrableOn Kf (Set.Icc 0 T))
    (hLip : ∀ t ∈ Set.Icc (0 : ℝ) T, Whole.HasLipBoundW (Whole.mfeTransportW D (ρ t)) (Kf t)) (M : ℕ) :
    IntegrableOn (fun r => sb1_lv_EQ D (sb1kM d D.s M) N ρ r) (Set.Icc 0 T) := by
  have hs0 := H.tr.hs0
  have hd := H.tr.hd
  have hsd := H.tr.hsd
  have hβ0 : 0 < D.invβ⁻¹ := inv_pos.2 hβ
  set β := D.invβ⁻¹ with hβdef
  have hL : ∀ r ∈ Set.Icc (0 : ℝ) T, 0 ≤ Kf r ∧
      ∀ x y, ‖Whole.mfeTransportW D (ρ r) x - Whole.mfeTransportW D (ρ r) y‖ ≤ Kf r * ‖x - y‖ :=
    fun r hr => sb1_lip_of_hasLip (hLip r hr)
  obtain ⟨A2, hA20, hA2⟩ := sb1kM_hk_bound (d := d) D.s hs0
  set CwR := sb1CwR d D.s C3 (C3 * ∫ y : Euc d, sb1w ((d : ℝ) + 2) y) β N with hCwR
  let Φb : ℝ → ℝ := fun r => CwR * (2 * (A2 * Kf r * sb1Cs d D.s C3))
  have hΦb : IntegrableOn Φb (Set.Icc 0 T) := (hKi.const_mul (A2 * sb1Cs d D.s C3 * 2 * CwR)).congr
    (Eventually.of_forall fun r => by simp only [Φb]; ring)
  have hk4 := sb1kM_isKernel (d := d) D.s hs0 M
  obtain ⟨Lg, hRg⟩ := sb1_lv_kerR hk4 hs0
  have hk := sb1kM_ker (d := d) D.s hs0 M
  have hbd : ∀ r ∈ Set.Icc (0 : ℝ) T, |sb1Phipi (sb1kM d D.s M) (fun r => Whole.mfeTransportW D (ρ r)) β N ρ r| ≤ Φb r := by
    intro r hr
    refine (sb1_Phi_abs_le hd hs0 hsd hN hβ0.le hk (H.rho hd hr) (mul_nonneg hA20 (hL r hr).1)
      (fun x y => hA2 M (hL r hr).1 (hL r hr).2 x y)).trans (le_of_eq ?_)
    simp only [Φb, hCwR]
  have hKpos : ∀ r ∈ Set.Icc (0 : ℝ) T, 0 < sb1Kpi (sb1kM d D.s M) β N ρ r := fun r hr => by
    unfold sb1Kpi
    exact sb1_Kpi_pos' hd hs0 hsd hN hβ0.le hk (H.rho hd hr)
  have hcont : ContinuousOn (sb1Kpi (sb1kM d D.s M) β N ρ) (Set.Icc 0 T) :=
    (sb1_Kk_contOn H hk hβ0.le hN).congr (fun r hr => sb1_Kpi_eq H hr _ β)
  obtain ⟨r0, hr0, hmin⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 hT) hcont
  have hm : 0 < sb1Kpi (sb1kM d D.s M) β N ρ r0 := hKpos r0 hr0
  have hEQ : ∀ r ∈ Set.Icc (0 : ℝ) T, sb1_lv_EQ D (sb1kM d D.s M) N ρ r =
      (sb1Kpi (sb1kM d D.s M) β N ρ r)⁻¹ * sb1Phipi (sb1kM d D.s M) (fun r => Whole.mfeTransportW D (ρ r)) β N ρ r :=
    fun r hr => sb1_lv_EQ_eq H hk.meas hr
  have hmeas : AEStronglyMeasurable (fun r => sb1_lv_EQ D (sb1kM d D.s M) N ρ r) (volume.restrict (Set.Icc 0 T)) := by
    have h1 : AEStronglyMeasurable (fun r => (sb1Kpi (sb1kM d D.s M) β N ρ r)⁻¹) (volume.restrict (Set.Icc 0 T)) :=
      ((hcont.aestronglyMeasurable measurableSet_Icc).aemeasurable.inv).aestronglyMeasurable
    have h2 := h1.mul (sb1_Phipi_aesm H hT hβ0 hN hk hRg)
    exact h2.congr ((ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun r hr => (hEQ r hr).symm))
  refine Integrable.mono' (hΦb.const_mul (sb1Kpi (sb1kM d D.s M) β N ρ r0)⁻¹) hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
  rw [hEQ r hr, Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.2 (hKpos r hr))]
  have h1 : sb1Kpi (sb1kM d D.s M) β N ρ r0 ≤ sb1Kpi (sb1kM d D.s M) β N ρ r := (isMinOn_iff.1 hmin) r hr
  calc (sb1Kpi (sb1kM d D.s M) β N ρ r)⁻¹ * |sb1Phipi (sb1kM d D.s M) (fun r => Whole.mfeTransportW D (ρ r)) β N ρ r|
      ≤ (sb1Kpi (sb1kM d D.s M) β N ρ r0)⁻¹ * Φb r :=
        mul_le_mul (inv_anti₀ hm h1) (hbd r hr) (abs_nonneg _) (inv_pos.2 hm).le
    _ = _ := rfl

end Main

end HRS.MS.MfeConf
