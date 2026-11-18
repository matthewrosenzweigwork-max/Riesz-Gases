import HRS.MC.CepP3Aux8

/-!
# Packet P3, Aux9: Proposition B.3 for the periodic lift
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MC.CepP3

open HRS

variable {d N : ℕ}

theorem continuous_Lop (D : DynData d) (hV : Torus.IsSmooth D.V) {T : ℝ}
    {F : ℝ × (Fin N → Euc d) → ℝ} (hFs : ContDiff ℝ ∞ F)
    (hFO : tsupport F ⊆ Ioo 0 T ×ˢ liftedFree d N) : Continuous (Lop D.invβ (bC D) F) := by
  have h1 : Continuous fun p => fderiv ℝ F p (1, 0) :=
    (hFs.continuous_fderiv (by simp)).clm_apply continuous_const
  have h2 : Continuous fun p => D.invβ * ∑ k : Fin N × Fin d,
      fderiv ℝ (fderiv ℝ F) p (0, configBasis d N k) (0, configBasis d N k) := by
    refine continuous_const.mul (continuous_finsetSum _ fun k _ => ?_)
    have hF2 : Continuous (fderiv ℝ (fderiv ℝ F)) :=
      (hFs.fderiv_right (m := ∞) (by simp)).continuous_fderiv (by simp)
    exact (hF2.clm_apply continuous_const).clm_apply continuous_const
  have h3 : Continuous fun p => fderiv ℝ F p (0, bC D p) := by
    rw [continuous_iff_continuousAt]
    intro p
    by_cases hp : p ∈ tsupport F
    · have hO : Ioo 0 T ×ˢ liftedFree d N ∈ 𝓝 p :=
        (isOpen_Ioo.prod (isOpen_liftedFree d N)).mem_nhds (hFO hp)
      have hb : ContinuousAt (bC (N := N) D) p :=
        ((contDiffOn_bC D hV (T := T)).continuousOn).continuousAt hO
      have hfd : ContinuousAt (fderiv ℝ F) p := (hFs.continuous_fderiv (by simp)).continuousAt
      exact hfd.clm_apply (continuousAt_const.prodMk hb)
    · have hz : fderiv ℝ F =ᶠ[𝓝 p] fun _ => (0 : (ℝ × (Fin N → Euc d)) →L[ℝ] ℝ) := by
        have : (tsupport F)ᶜ ∈ 𝓝 p := (isClosed_tsupport F).isOpen_compl.mem_nhds hp
        filter_upwards [this] with q hq
        have : F =ᶠ[𝓝 q] fun _ => (0 : ℝ) := by
          filter_upwards [(isClosed_tsupport F).isOpen_compl.mem_nhds hq] with x hx
          exact F_eq_zero_of_notMem hx
        rw [this.fderiv_eq]; simp
      have : (fun q => fderiv ℝ F q (0, bC D q)) =ᶠ[𝓝 p] fun _ => (0 : ℝ) := by
        filter_upwards [hz] with q hq
        simp [hq]
      exact continuousAt_const.congr this.symm
  exact (h1.add h2).add h3

theorem measurable_per_psi {H : ℝ × (Fin N → Euc d) → ℝ} {R : ℝ} (hc : Continuous H) (hS : Supp R H) :
    Measurable fun q : ℝ × Config d N => per H (psi 0 q) := by
  obtain ⟨S, hSS⟩ := exists_finset_uniform (d := d) (N := N) R
  have : (fun q : ℝ × Config d N => per H (psi 0 q)) = fun q => ∑ w ∈ S, H (tau w (psi 0 q)) :=
    funext fun q => per_eq_sum hS (fun w hw => hSS q w hw)
  rw [this]
  refine Finset.measurable_sum _ fun w _ => hc.measurable.comp ?_
  have : (fun q : ℝ × Config d N => tau w (psi 0 q)) = psi w := funext fun q => (psi_eq w q).symm
  rw [this]
  exact measurable_psi w

theorem bounded_per_psi {H : ℝ × (Fin N → Euc d) → ℝ} {R : ℝ} (hc : Continuous H) (hS : Supp R H) :
    ∃ C, ∀ q : ℝ × Config d N, ‖per H (psi 0 q)‖ ≤ C := by
  obtain ⟨S, hSS⟩ := exists_finset_uniform (d := d) (N := N) R
  have hcs : HasCompactSupport H := by
    refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℝ × (Fin N → Euc d)) R) ?_
    intro p hp
    by_contra h
    exact hp (hS p (by simpa using h))
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hcs
  refine ⟨S.card * C, fun q => ?_⟩
  rw [per_eq_sum hS (fun w hw => hSS q w hw)]
  calc ‖∑ w ∈ S, H (tau w (psi 0 q))‖ ≤ ∑ w ∈ S, ‖H (tau w (psi 0 q))‖ := norm_sum_le _ _
    _ ≤ ∑ _w ∈ S, C := Finset.sum_le_sum fun w _ => hC _
    _ = S.card * C := by simp

end HRS.MC.CepP3
