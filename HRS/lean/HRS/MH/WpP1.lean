import HRS.MH.WpSpec

/-!
# P1: `HRS.MH.Wp.maximal_estimate_meas_p`

The proof of `HRS.Uniform.Q45.maximal_estimate_meas` (Q45Max.lean) at order `p ≥ 2`: `hilbert_bdg p hp` for the
two-level branch, `sup_Z_bound` with `p` for the dissipative branch, constant `max (c ^ p * Cb) (CD p K T)`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.MH.WpP

open HRS HRS.Uniform HRS.Uniform.Kot

theorem maximal_estimate_meas_p_proof :
    type_of% @HRS.MH.Wp.maximal_estimate_meas_p := by
  intro T K p hT hp
  have hp0 : 0 < p := by linarith
  have hp0' : 0 ≤ p := hp0.le
  obtain ⟨Cb, hCb0, hCb⟩ := HilbertBDG.hilbert_bdg p hp
  set c : ℝ := |K| + |K| * (|K| * T) with hc
  have hc0 : 0 ≤ c := by positivity
  refine ⟨max (c ^ p * Cb) (CD p K T), le_max_of_le_left (mul_nonneg (Real.rpow_nonneg hc0 p) hCb0), ?_⟩
  intro Ω mΩ P _ ℱ H E _ _ _ _ _ _ _ _ _ _ _ _ S hS M Sg hM
  obtain ⟨hev, h | h⟩ := hS
  · -- two levels
    have hK := h.K_nonneg
    have hcont := hM.cont
    have hzero := hM.zero
    have hMeas : ∀ s ∈ Set.Icc (0 : ℝ) T, AEMeasurable (M s) P := fun s hs =>
      (hM.sq_int s hs).aestronglyMeasurable.aemeasurable
    have hfin := supNorm_sq_ne_top hM
    refine ⟨Zc h.1 T M, fun t ht => h.isStochConv hT hev hcont hzero hMeas hfin ht, ?_,
      fun t ht => h.aemeasurable_Zc hT hev hcont hzero hMeas ht, ?_⟩
    · filter_upwards [hcont] with ω hc'
      exact h.continuousOn_zdet hev (continuous_pathOf hT hc')
    · have hpt : ∀ᵐ ω ∂P, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖Zc h.1 T M t ω‖ₑ) ≤
          ENNReal.ofReal (K + K * (K * T)) * supNorm T M ω := by
        filter_upwards [hcont] with ω hc'
        refine iSup₂_le fun t ht => ?_
        have hY : ∀ s ∈ Set.Icc (0 : ℝ) T, ‖pathOf T M ω s‖ ≤ (supNorm T M ω).toReal := by
          intro s hs
          rw [pathOf_of_mem hs]
          exact norm_le_supNorm_toReal hT hc' hs
        have hn := h.norm_zdet_le ht hY (continuous_pathOf hT hc') hev
        rw [← ofReal_norm]
        have hfin' : supNorm T M ω = ENNReal.ofReal (supNorm T M ω).toReal :=
          (ENNReal.ofReal_toReal (supNorm_lt_top hT hc').ne).symm
        rw [hfin', ← ENNReal.ofReal_mul (by positivity)]
        exact ENNReal.ofReal_le_ofReal hn
      have hcK : c = K + K * (K * T) := by
        rw [hc, abs_of_nonneg hK]
      set R := ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) T, ENNReal.ofReal (traceNormForm (Sg r ω))) ^ (p / 2) ∂P with hR
      have hbdg : ∫⁻ ω, (supNorm T M ω) ^ p ∂P ≤ ENNReal.ofReal Cb * R := hCb Ω P ℱ H T M Sg hM
      rw [← hcK] at hpt
      calc ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖Zc h.1 T M t ω‖ₑ) ^ p ∂P
          ≤ ∫⁻ ω, (ENNReal.ofReal c * supNorm T M ω) ^ p ∂P :=
            lintegral_mono_ae (hpt.mono fun ω hω => ENNReal.rpow_le_rpow hω hp0')
        _ = ENNReal.ofReal c ^ p * ∫⁻ ω, (supNorm T M ω) ^ p ∂P := by
            simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp0']
            exact lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp0' ENNReal.ofReal_ne_top)
        _ ≤ ENNReal.ofReal c ^ p * (ENNReal.ofReal Cb * R) := mul_le_mul' le_rfl hbdg
        _ = ENNReal.ofReal (c ^ p * Cb) * R := by
            rw [← mul_assoc, ENNReal.ofReal_rpow_of_nonneg hc0 hp0', ← ENNReal.ofReal_mul (Real.rpow_nonneg hc0 p)]
        _ ≤ ENNReal.ofReal (max (c ^ p * Cb) (CD p K T)) * R :=
            mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_left _ _)) le_rfl
  · -- one dissipative level
    have hD0 := h
    obtain ⟨hj, hsurj, -, -, -⟩ := hD0
    have hjE : ∀ x, ‖S.j x‖ₑ = ‖x‖ₑ := fun x => by
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, hj x]
    have hcomp : IsCompleteFiltration P (augFiltration P ℱ) := augFiltration_isComplete ℱ
    have hM' := isHMC_aug hM
    have hV : EvolBound S.VH K T :=
      { norm_le := fun r t hr hrt htT => by
          refine ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le fun x => ?_
          exact EvolData.Dissipative.norm_VH_le S h ⟨hr, hrt.trans htT⟩ ⟨hrt, htT⟩ x
        comp := fun r t u hr hrt htu huT => by
          have := hev.comp_H r t u hr hrt htu huT
          exact this
        self := fun t ht0 htT => hev.self_H t ⟨ht0, htT⟩ }
    obtain ⟨m, Z', hm, hZc, hlim⟩ := exists_dyadic_limit hcomp hM' hV (EvolData.Dissipative.cont_VH hev h) hT
    refine ⟨fun t ω => S.j (Z' t ω), ?_, ?_, ?_, ?_⟩
    · intro t ht ε hε
      obtain ⟨δ, hδ, hconv⟩ := hconv_Z hcomp hM' hV (EvolData.Dissipative.cont_VH hev h) hT hm hlim ht ε hε
      refine ⟨δ, hδ, fun n r hr0 hrn hmono hmesh => ?_⟩
      have hrs : ∀ ω, riemannSum S.VE S.j M t r ω =
          S.j (∑ i : Fin n, S.VH t (r i.castSucc) (M (r i.succ) ω - M (r i.castSucc) ω)) := by
        intro ω
        unfold riemannSum
        rw [map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        have h0 : 0 ≤ r i.castSucc := hr0 ▸ hmono (Fin.zero_le _)
        have h1 : r i.castSucc ≤ t := hrn ▸ hmono (Fin.le_last _)
        have := congrArg (fun F : H →L[ℝ] E => F (M (r i.succ) ω - M (r i.castSucc) ω))
          (hev.intertwine (r i.castSucc) t h0 h1 ht.2)
        simpa using this
      have := hconv n r hr0 hrn hmono hmesh
      refine lt_of_le_of_lt (le_of_eq ?_) this
      refine lintegral_congr fun ω => ?_
      rw [hrs ω, ← map_sub, hjE]
    · exact hZc.mono fun ω h => S.j.continuous.comp_continuousOn h
    · intro t ht
      have hYmeas : ∀ k, AEStronglyMeasurable (rsProc S.VH M (Kot.dy T (m k)) (2 ^ m k) t) P := fun k =>
        aestronglyMeasurable_rsTag hM' (Kot.dy_mono hT _) (by rw [Kot.dy_zero]) (by rw [Kot.dy_top]) _ t
      have hZm : AEMeasurable (Z' t) P :=
        aemeasurable_of_tendsto_metrizable_ae atTop (fun k => (hYmeas k).aemeasurable)
          (hlim.mono fun ω hω => hω t ht)
      exact S.j.continuous.measurable.comp_aemeasurable hZm
    · have hb := sup_Z_bound hcomp hM' hV hT hZc hlim (p := p) (by linarith)
      have e : ∀ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖S.j (Z' t ω)‖ₑ) = ⨆ t ∈ Set.Icc (0 : ℝ) T, ‖Z' t ω‖ₑ := by
        intro ω
        refine iSup_congr fun t => iSup_congr fun _ => ?_
        exact hjE _
      simp_rw [e]
      exact hb.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_right _ _)) le_rfl)

end HRS.MH.WpP
