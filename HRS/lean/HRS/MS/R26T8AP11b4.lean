import HRS.MS.R26T8AP11gm
import HRS.MS.R26T8AP11pa
import HRS.MS.R26T8AP11int
import HRS.MS.R26T8AContInt

/-!
# S8.2 nonlocal layer: smoothness of the local Riesz potential off the diagonal (P11e, part 3b, piece B4)
`r26t8a_localRiesz_contDiffOn`: for `F` conormal of order `sigma < d`, `(x,y) ↦ chi(x-y) ∫ ‖x-y-v‖^(alpha-d) chi(v) F(y+v,y) dv` is
`C^k` on `{x ≠ y}`.  Near `(x0,y0)` the integral splits as `I_A + I_B` (`r26t8a_loc_partA`, smooth everywhere, and the part near `v = 0`, smooth on a ball
by differentiation under the integral sign, `r26t8a_contDiffOn_integral`, with the jet bound `r26t8a_G_jet`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

theorem r26t8a_locInt_contDiffOn (d : ℕ) (hd : 2 ≤ d) (k b : ℕ) (alpha M sigma : ℝ)
    (halpha : 0 < alpha) (had : alpha < d) (hM : 0 ≤ M) (hsd : sigma < d)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) (A : ℝ) (hA : 0 ≤ A) (F : Euc d → Euc d → ℝ)
    (hF : Conormal k b M sigma A F) :
    ContDiffOn ℝ k (fun p : Euc d × Euc d => ∫ v : Euc d, ‖p.1 - p.2 - v‖ ^ (alpha - (d : ℝ)) * chi v * F (p.2 + v) p.2)
      {p : Euc d × Euc d | p.1 ≠ p.2} := by
  obtain ⟨s, hs0, hsd', hGj⟩ := r26t8a_G_jet d hd alpha halpha had chi hchi k b M sigma hM hsd
  have hFc : ContDiffOn ℝ k (Function.uncurry F) {p | p.1 ≠ p.2} := hF.1
  intro p0 hp0
  haveI : Nontrivial (Euc d) := ⟨⟨0, EuclideanSpace.single ⟨0, by omega⟩ (1 : ℝ), by
    intro h; have := congrArg (fun v : Euc d => v ⟨0, by omega⟩) h; simp at this⟩⟩
  have hz0 : 0 < ‖p0.1 - p0.2‖ := norm_pos_iff.2 (sub_ne_zero.2 hp0)
  set δ : ℝ := min (‖p0.1 - p0.2‖ / 4) 1 with hδd
  have hδ : 0 < δ := lt_min (by positivity) one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδ4 : 4 * δ ≤ ‖p0.1 - p0.2‖ := by
    have := min_le_left (‖p0.1 - p0.2‖ / 4) 1; linarith
  obtain ⟨c, hc0, hc⟩ := hGj A hA F hF δ hδ hδ1 p0 hδ4
  set U : Set (Euc d × Euc d) := ball p0 (δ / 2) with hU
  have hUo : IsOpen U := isOpen_ball
  have hp0U : p0 ∈ U := mem_ball_self (by positivity)
  have hUle : ∀ p ∈ U, ‖p - p0‖ ≤ δ / 2 := fun p hp => by
    rw [hU, mem_ball, dist_eq_norm] at hp; exact hp.le
  have hae : ∀ᵐ v : Euc d, v ≠ 0 := compl_mem_ae_iff.2 (measure_singleton (0 : Euc d))
  have hchic : ContDiff ℝ (k : WithTop ℕ∞) chi := hchi.1.of_le (by exact_mod_cast le_top)
  -- integrable majorant
  set Φ : Euc d → ℝ := (closedBall (0 : Euc d) (2 * δ)).indicator (fun v => c * ‖v‖ ^ (-s)) with hΦd
  have hΦ : Integrable Φ := by
    have h := (r26t8a_p11a_mass d hd (d - s) (by linarith) (by linarith) 3 (by norm_num)).1
    have h' : IntegrableOn (fun v : Euc d => ‖v‖ ^ (-s)) (ball (0 : Euc d) 3) := by
      refine h.congr_fun (fun v _ => ?_) measurableSet_ball
      simp only; congr 1; ring
    have h'' : IntegrableOn (fun v : Euc d => c * ‖v‖ ^ (-s)) (ball (0 : Euc d) 3) := h'.const_mul c
    exact (h''.mono_set (closedBall_subset_ball (by linarith))).integrable_indicator
      measurableSet_closedBall
  have hIB : ContDiffOn ℝ k (fun p : Euc d × Euc d => ∫ v : Euc d, r26t8a_G alpha chi δ F v p) U :=
    r26t8a_contDiffOn_integral (E := Euc d × Euc d) (μ := volume) hUo (r26t8a_G alpha chi δ F) k
      (by
        filter_upwards [hae] with v hv x _
        exact (r26t8a_G_contDiff d alpha halpha had hd chi hchi F hFc hδ hv).contDiffAt)
      hΦ
      (fun i hi => by
        filter_upwards [hae] with v hv x hx
        exact hc i hi x (hUle x hx) v hv)
      (fun i hi x _ => r26t8a_G_meas d alpha halpha had hd chi hchi F hFc hδ hi x)
  have hIA := r26t8a_loc_partA d hd alpha halpha had chi hchi F hFc hδ
  -- measurability of the fibre
  have hFm : ∀ y : Euc d, AEStronglyMeasurable (fun v : Euc d => F (y + v) y) volume := by
    intro y
    have hcont : ContinuousOn (fun v : Euc d => F (y + v) y) {v : Euc d | v ≠ 0} := by
      have h1 := hFc.continuousOn
      refine h1.comp (f := fun v : Euc d => (y + v, y)) ((continuous_const.add continuous_id).prodMk
        continuous_const).continuousOn (fun v hv => ?_)
      simp only [Set.mem_setOf_eq] at hv ⊢
      intro h; apply hv; simpa using h
    have h := hcont.aestronglyMeasurable (μ := (volume : Measure (Euc d)))
      (isOpen_ne.measurableSet : MeasurableSet {v : Euc d | v ≠ 0})
    have e1 : (volume : Measure (Euc d)).restrict {v : Euc d | v ≠ 0} = volume := by
      have := restrict_compl_singleton (μ := (volume : Measure (Euc d))) (0 : Euc d)
      simpa [Set.compl_singleton_eq] using this
    rwa [e1] at h
  -- geometry
  have hz3 : ∀ p : Euc d × Euc d, ‖p - p0‖ ≤ δ / 2 → 3 * δ ≤ ‖p.1 - p.2‖ := by
    intro p hp
    have hp1 : ‖p.1 - p0.1‖ ≤ δ / 2 := (norm_fst_le (p - p0)).trans hp
    have hp2 : ‖p.2 - p0.2‖ ≤ δ / 2 := (norm_snd_le (p - p0)).trans hp
    have h2 : ‖(p.1 - p0.1) - (p.2 - p0.2)‖ ≤ δ := by
      have := norm_sub_le (p.1 - p0.1) (p.2 - p0.2); linarith
    have h1 : ‖p0.1 - p0.2‖ ≤ ‖p.1 - p.2‖ + ‖(p.1 - p0.1) - (p.2 - p0.2)‖ := by
      have : p0.1 - p0.2 = (p.1 - p.2) - ((p.1 - p0.1) - (p.2 - p0.2)) := by abel
      rw [this]; exact norm_sub_le _ _
    linarith
  have hfar : ∀ p : Euc d × Euc d, ‖p - p0‖ ≤ δ / 2 → ∀ v : Euc d, ‖v‖ ≤ 2 * δ → δ ≤ ‖p.1 - p.2 - v‖ := by
    intro p hp v hv
    have h3 : ‖p.1 - p.2‖ ≤ ‖p.1 - p.2 - v‖ + ‖v‖ := by
      have := norm_add_le (p.1 - p.2 - v) v
      simpa using this
    linarith [hz3 p hp]
  -- the splitting of the integral
  have hEq : ∀ p ∈ U, (∫ v : Euc d, ‖p.1 - p.2 - v‖ ^ (alpha - (d : ℝ)) * chi v * F (p.2 + v) p.2) =
      (∫ v : Euc d, ‖p.1 - p.2 - v‖ ^ (alpha - (d : ℝ)) * (chi v * (1 - chi (δ⁻¹ • v)) * F (p.2 + v) p.2)) +
        ∫ v : Euc d, r26t8a_G alpha chi δ F v p := by
    intro p hp
    have hpd := hUle p hp
    have hzp : p.1 - p.2 ≠ 0 := by
      intro h; have := hz3 p hpd; rw [h, norm_zero] at this; linarith
    have hpt : ∀ v : Euc d, ‖p.1 - p.2 - v‖ ^ (alpha - (d : ℝ)) * chi v * F (p.2 + v) p.2 =
        ‖p.1 - p.2 - v‖ ^ (alpha - (d : ℝ)) * (chi v * (1 - chi (δ⁻¹ • v)) * F (p.2 + v) p.2) +
          r26t8a_G alpha chi δ F v p := by
      intro v
      by_cases hv2 : ‖v‖ ≤ 2 * δ
      · have := r26t8a_Kc_eq d alpha chi hchi hδ (u := p.1 - p.2 - v) (by linarith [hfar p hpd v hv2])
        simp only [r26t8a_G, this]; ring
      · have h : ‖δ⁻¹ • v‖ ≥ 2 := by
          rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hδ.le), inv_mul_eq_div, ge_iff_le, le_div_iff₀ hδ]
          linarith [not_le.1 hv2]
        simp only [r26t8a_G, hchi.2.2.2.2 _ h]; ring
    have hT : Integrable (fun v : Euc d => ‖p.1 - p.2 - v‖ ^ (alpha - (d : ℝ)) * chi v * F (p.2 + v) p.2) := by
      refine (r26t8a_loc_integrable d hd k b alpha M sigma halpha had hM hsd A hA F hF p.2 (p.1 - p.2)
        hzp).mono' ?_ ?_
      · exact ((((measurable_norm.comp (measurable_const.sub measurable_id)).pow_const _).aestronglyMeasurable).mul
          hchi.1.continuous.aestronglyMeasurable).mul (hFm p.2)
      · refine Filter.Eventually.of_forall fun v => ?_
        have hK0 : 0 ≤ ‖p.1 - p.2 - v‖ ^ (alpha - (d : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
        have hch := hchi.2.2.1 v
        by_cases hv2 : ‖v‖ ≤ 2
        · rw [Set.indicator_of_mem (by simpa using hv2), norm_mul, norm_mul, Real.norm_of_nonneg hK0,
            Real.norm_of_nonneg hch.1]
          have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hch.2 hK0)
            (norm_nonneg (F (p.2 + v) p.2))
          calc ‖p.1 - p.2 - v‖ ^ (alpha - (d : ℝ)) * chi v * ‖F (p.2 + v) p.2‖
              ≤ ‖p.1 - p.2 - v‖ ^ (alpha - (d : ℝ)) * 1 * ‖F (p.2 + v) p.2‖ := this
            _ = ‖p.1 - p.2 - v‖ ^ (alpha - (d : ℝ)) * ‖F (p.2 + v) p.2‖ := by rw [mul_one]
        · rw [Set.indicator_of_notMem (by simpa using hv2), hchi.2.2.2.2 v (by linarith [not_le.1 hv2])]
          simp
    have hTB : Integrable (fun v : Euc d => r26t8a_G alpha chi δ F v p) := by
      refine hΦ.mono' ?_ ?_
      · have hKm : AEStronglyMeasurable (fun v : Euc d => r26t8a_Kc alpha chi δ (p.1 - p.2 - v)) volume :=
          ((r26t8a_Kc_contDiff d hd alpha halpha had chi hchi hδ).continuous.comp
            (continuous_const.sub continuous_id)).aestronglyMeasurable
        have hc2 : AEStronglyMeasurable (fun v : Euc d => chi (δ⁻¹ • v)) volume :=
          (hchi.1.continuous.comp (continuous_const_smul δ⁻¹)).aestronglyMeasurable
        exact hKm.mul (((hchi.1.continuous.aestronglyMeasurable).mul hc2).mul (hFm p.2))
      · filter_upwards [hae] with v hv
        have := hc 0 (Nat.zero_le _) p hpd v hv
        rwa [norm_iteratedFDeriv_zero] at this
    have hTA : Integrable (fun v : Euc d => ‖p.1 - p.2 - v‖ ^ (alpha - (d : ℝ)) *
        (chi v * (1 - chi (δ⁻¹ • v)) * F (p.2 + v) p.2)) := by
      refine (hT.sub hTB).congr (Filter.Eventually.of_forall fun v => ?_)
      simp only [Pi.sub_apply]
      linarith [hpt v]
    rw [← integral_add hTA hTB]
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  have hLeq : ∀ p ∈ U, (∫ v : Euc d, ‖p.1 - p.2 - v‖ ^ (alpha - (d : ℝ)) * chi v * F (p.2 + v) p.2) =
      (∫ v : Euc d, ‖p.1 - p.2 - v‖ ^ (alpha - (d : ℝ)) *
        (chi v * (1 - chi (δ⁻¹ • v)) * F (p.2 + v) p.2)) + ∫ v : Euc d, r26t8a_G alpha chi δ F v p :=
    fun p hp => hEq p hp
  have hcd : ContDiffAt ℝ (k : WithTop ℕ∞) (fun p : Euc d × Euc d =>
      (∫ v : Euc d, ‖p.1 - p.2 - v‖ ^ (alpha - (d : ℝ)) * (chi v * (1 - chi (δ⁻¹ • v)) * F (p.2 + v) p.2)) +
        ∫ v : Euc d, r26t8a_G alpha chi δ F v p) p0 :=
    (hIA.contDiffAt).add (hIB.contDiffAt (hUo.mem_nhds hp0U))
  exact (hcd.congr_of_eventuallyEq (by
    filter_upwards [hUo.mem_nhds hp0U] with p hp using hLeq p hp)).contDiffWithinAt

theorem r26t8a_localRiesz_contDiffOn (d : ℕ) (hd : 2 ≤ d) (k b : ℕ) (alpha M sigma : ℝ)
    (halpha : 0 < alpha) (had : alpha < d) (hM : 0 ≤ M) (hsd : sigma < d)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) (A : ℝ) (hA : 0 ≤ A) (F : Euc d → Euc d → ℝ)
    (hF : Conormal k b M sigma A F) :
    ContDiffOn ℝ k (Function.uncurry (r26t8a_localRiesz alpha chi F)) {p : Euc d × Euc d | p.1 ≠ p.2} := by
  have hchic : ContDiff ℝ (k : WithTop ℕ∞) chi := hchi.1.of_le (by exact_mod_cast le_top)
  exact ((hchic.comp (contDiff_fst.sub contDiff_snd)).contDiffOn).mul
    (r26t8a_locInt_contDiffOn d hd k b alpha M sigma halpha had hM hsd chi hchi A hA F hF)

end HRS.MS.R26T8A
