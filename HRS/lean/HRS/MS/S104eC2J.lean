import HRS.MS.S104eC2I

/-!
# S104E route C, packet C2, part J: parametric continuity of `ultK`

Prefix `s104c2_`, namespace `HRS.MS.S104e.C`.  `s104c2_ultK_jc`: if the family `G_v` (`v ∈ S`) is uniformly Hölder near (`HolNear η H`), uniformly weighted
(`‖G_v y‖ ≤ A0 (1+‖y‖)^{-L}`, `L > d`) and `(v,y) ↦ G_v y` is continuous on `S × ℝ^d`, then `(v,x) ↦ ultK κ (G_v) x` is continuous on `S × ℝ^d`
(dominated convergence in the near and far integrals).
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000

namespace HRS.MS.S104e.C

open HRS HRS.Whole HRS.MS.Ul HRS.MS.R2WinOrbNL

variable {d : ℕ}

lemma s104c2_wt_shift {L : ℝ} (hL : 0 ≤ L) (x x0 z : Euc d) (hx : ‖x - x0‖ ≤ 1) :
    u2Wt L (x - z) ≤ 2 ^ L * u2Wt L (x0 - z) := by
  unfold u2Wt
  have ha : 0 < 1 + ‖x - z‖ := by positivity
  have hb : 0 < 1 + ‖x0 - z‖ := by positivity
  have hle : 1 + ‖x0 - z‖ ≤ 2 * (1 + ‖x - z‖) := by
    have h1 : ‖x0 - z‖ ≤ ‖x0 - x‖ + ‖x - z‖ := by
      have := norm_add_le (x0 - x) (x - z)
      simpa using this
    have h2 : ‖x0 - x‖ = ‖x - x0‖ := norm_sub_rev _ _
    have := norm_nonneg (x - z)
    linarith
  have key : (1 + ‖x0 - z‖) ^ L ≤ 2 ^ L * (1 + ‖x - z‖) ^ L := by
    rw [← Real.mul_rpow (by norm_num) ha.le]
    exact Real.rpow_le_rpow hb.le hle hL
  rw [Real.rpow_neg ha.le, Real.rpow_neg hb.le, inv_eq_one_div, inv_eq_one_div, mul_one_div,
    div_le_div_iff₀ (Real.rpow_pos_of_pos ha _) (Real.rpow_pos_of_pos hb _)]
  linarith

theorem s104c2_ultK_jc (hd : 1 ≤ d) {κ : Euc d → ℝ} {s η H L A0 : ℝ} (hK : UlKer κ s) (hη1 : η < 1)
    (hηd : s + 1 - η < (d : ℝ)) (hH0 : 0 ≤ H) (hL : (d : ℝ) < L) (hA0 : 0 ≤ A0)
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {S : Set ℝ} {Gf : ℝ → Euc d → F}
    (hH : ∀ v ∈ S, HolNear η H (Gf v)) (hb : ∀ v ∈ S, ∀ y, ‖Gf v y‖ ≤ A0 * u2Wt L y)
    (hc : ContinuousOn (fun p : ℝ × Euc d => Gf p.1 p.2) (S ×ˢ univ)) :
    ContinuousOn (fun p : ℝ × Euc d => ultK κ (Gf p.1) p.2) (S ×ˢ univ) := by
  intro p0 hp0
  have hL0 : 0 ≤ L := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hGv : ∀ v ∈ S, Continuous (Gf v) := fun v hv => by
    have h1 : Continuous (fun y : Euc d => (v, y)) := Continuous.prodMk continuous_const continuous_id
    exact hc.comp_continuous h1 (fun y => ⟨hv, mem_univ y⟩)
  obtain ⟨C0, hC0, hb0⟩ := ult_ker_bound hK
  set l : Filter (ℝ × Euc d) := 𝓝[S ×ˢ univ] p0 with hl
  have F0 : ∀ᶠ p in l, p ∈ S ×ˢ univ := self_mem_nhdsWithin
  have hshift : ∀ z : Euc d, ContinuousWithinAt (fun p : ℝ × Euc d => Gf p.1 (p.2 - z)) (S ×ˢ univ) p0 := by
    intro z
    have hmap : Continuous (fun p : ℝ × Euc d => (p.1, p.2 - z)) :=
      continuous_fst.prodMk (continuous_snd.sub continuous_const)
    have h1 := hc (p0.1, p0.2 - z) ⟨hp0.1, mem_univ _⟩
    exact h1.comp (f := fun p : ℝ × Euc d => (p.1, p.2 - z)) hmap.continuousWithinAt
      (fun p hp => ⟨hp.1, mem_univ _⟩)
  have hnear : ContinuousWithinAt (fun p : ℝ × Euc d => ultNear κ (Gf p.1) p.2) (S ×ˢ univ) p0 := by
    show Tendsto (fun p : ℝ × Euc d => ∫ z, ultKN κ z • (Gf p.1 (p.2 - z) - Gf p.1 p.2)) l _
    refine tendsto_integral_filter_of_dominated_convergence (μ := volume)
      (bound := fun z => C0 * H * s104c2_Psi d s η z) ?_ ?_
      ((s104c2_Psi_int hd hK.hs0 hη1 hηd).const_mul (C0 * H)) ?_
    · filter_upwards [F0] with p hp
      exact ult_near_meas hK.meas (hGv p.1 hp.1) p.2
    · filter_upwards [F0] with p hp
      filter_upwards [u2_ae_ne_zero hd] with z hz
      refine s104c2_near_dom hC0 hb0 hH0 hz (fun h1 => ?_)
      have := hH p.1 hp.1 (p.2 - z) p.2 (by simpa using h1)
      simpa using this
    · refine Filter.Eventually.of_forall fun z => ?_
      exact ((hshift z).sub (hc p0 hp0)).const_smul (ultKN κ z)
  have hfar : ContinuousWithinAt (fun p : ℝ × Euc d => u2Conv (ultKF κ) (Gf p.1) p.2) (S ×ˢ univ) p0 := by
    show Tendsto (fun p : ℝ × Euc d => ∫ z, ultKF κ z • Gf p.1 (p.2 - z)) l _
    have hbi : Integrable (fun z => ‖ultKF κ z‖ * u2Wt L (p0.2 - z)) volume :=
      u2_wt_translate_int (ult_far_U2Ker hd hK) hL p0.2
    refine tendsto_integral_filter_of_dominated_convergence (μ := volume)
      (bound := fun z => (A0 * 2 ^ L) * (‖ultKF κ z‖ * u2Wt L (p0.2 - z))) ?_ ?_ (hbi.const_mul _) ?_
    · filter_upwards [F0] with p hp
      exact ((ultKF_meas hK.meas).aestronglyMeasurable).smul
        ((hGv p.1 hp.1).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    · have hnb : ∀ᶠ p in l, ‖p.2 - p0.2‖ ≤ 1 := by
        have h1 : Tendsto (fun p : ℝ × Euc d => p.2) l (𝓝 p0.2) :=
          (continuous_snd.continuousAt (x := p0)).tendsto.mono_left nhdsWithin_le_nhds
        have := Metric.tendsto_nhds.1 h1 1 one_pos
        filter_upwards [this] with p hp
        rw [dist_eq_norm] at hp
        exact hp.le
      filter_upwards [F0, hnb] with p hp hp1
      refine Filter.Eventually.of_forall fun z => ?_
      rw [norm_smul]
      have h1 := hb p.1 hp.1 (p.2 - z)
      have h2 := s104c2_wt_shift hL0 p.2 p0.2 z hp1
      calc ‖ultKF κ z‖ * ‖Gf p.1 (p.2 - z)‖ ≤ ‖ultKF κ z‖ * (A0 * u2Wt L (p.2 - z)) :=
            mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ ≤ ‖ultKF κ z‖ * (A0 * (2 ^ L * u2Wt L (p0.2 - z))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hA0) (norm_nonneg _)
        _ = (A0 * 2 ^ L) * (‖ultKF κ z‖ * u2Wt L (p0.2 - z)) := by ring
    · refine Filter.Eventually.of_forall fun z => ?_
      exact (hshift z).const_smul (ultKF κ z)
  exact hnear.add hfar

end HRS.MS.S104e.C

end
