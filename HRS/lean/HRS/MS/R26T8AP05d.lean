import HRS.MS.R26T8AP05c

/-!
# S8.2 local Newton layer, packet T8A.P05 (part d): the convolution formula for the nested jet
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_conv_formula (hd : 2 ≤ d) {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (nu : ℝ) {R : ℝ} (hR : 0 < R)
    {F : Euc d → Euc d → ℝ} {k : ℕ} (hF : ContDiffOn ℝ k (Function.uncurry F) {p | p.1 ≠ p.2})
    {z : Euc d} (hz : ‖z‖ ≤ 4 * R) {p q : ℕ} (hpq : p + q ≤ k) (kappa : ℝ) (hkappa : q = 0 → kappa = 0) (X : Euc d) :
    iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q (r26t8a_annularNewton nu chi R F Y) z) X =
      ∫ u, r26t8a_Kk chi nu kappa (6 * R + 1) u • iteratedFDeriv ℝ p
        (fun Y => iteratedFDeriv ℝ q (fun w => r26t8a_annulus chi R w * midPair F Y w) (z - u)) X := by
  set r1 : ℝ := 6 * R + 1 with hr1def
  have hr1 : 0 < r1 := by rw [hr1def]; positivity
  set Kk := r26t8a_Kk chi nu kappa r1 with hKkdef
  have hKk : Integrable Kk := r26t8a_Kk_integrable hd hchi nu kappa hr1
  set S : Euc d × Euc d → ℝ := fun Yw => r26t8a_annulus chi R Yw.2 * midPair F Yw.1 Yw.2 with hSdef
  have hS : ContDiff ℝ k S := r26t8a_S_contDiff hchi hR hF
  have hsupp : ∀ Y, Function.support (fun w => S (Y, w)) ⊆ Metric.closedBall (0 : Euc d) (2 * R) := by
    intro Y w hw
    by_contra hn
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hn
    exact hw (by simp [hSdef, r26t8a_annulus_zero_large hchi hR hn.le])
  have hsd : ∀ Y, ContDiff ℝ (q : WithTop ℕ∞) (fun w => S (Y, w)) := fun Y =>
    (hS.comp (contDiff_const.prodMk contDiff_id)).of_le (by exact_mod_cast (by omega : q ≤ k))
  have hsk : ∀ Y, HasCompactSupport (fun w => S (Y, w)) := fun Y =>
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall _ _) (hsupp Y)
  -- Claim 1: derivative in z for fixed Y
  have hclaim : ∀ Y, iteratedFDeriv ℝ q (r26t8a_annularNewton nu chi R F Y) z =
      ∫ u, Kk u • iteratedFDeriv ℝ q (fun w => S (Y, w)) (z - u) := by
    intro Y
    set s : Euc d → ℝ := fun w => S (Y, w) with hsdef
    have hscont : Continuous s := hS.continuous.comp (continuous_const.prodMk continuous_id)
    have hsint : Integrable s := hscont.integrable_of_hasCompactSupport (hsk Y)
    obtain ⟨hAd, hAf⟩ := r26t8a_stageA hKk (hsd Y) (hsk Y) z
    obtain ⟨B, hB0, hB⟩ := r26t8a_jets_bdd2 (hsd Y) (hsk Y)
    have hloc : ∀ x ∈ Metric.ball z 1, r26t8a_annularNewton nu chi R F Y x =
        (∫ u, Kk u * s (x - u)) + kappa * ∫ w, s w := by
      intro x hx
      have hxz : ‖x - z‖ < 1 := by simpa [dist_eq_norm] using hx
      have hx4 : ‖x‖ ≤ 4 * R + 1 := by
        have := norm_le_norm_add_norm_sub' x z
        linarith
      have h1 : r26t8a_annularNewton nu chi R F Y x = ∫ u, newtonKernel d nu u * s (x - u) := by
        unfold r26t8a_annularNewton
        rw [← integral_sub_left_eq_self (fun u => newtonKernel d nu u * s (x - u)) volume x]
        refine integral_congr_ae (Eventually.of_forall fun w => ?_)
        simp only [hsdef, hSdef, sub_sub_cancel]
        ring
      have h2 : ∀ u, newtonKernel d nu u * s (x - u) = Kk u * s (x - u) + kappa * s (x - u) := by
        intro u
        by_cases h0 : s (x - u) = 0
        · rw [h0]; ring
        · have ha : r26t8a_annulus chi R (x - u) ≠ 0 := fun h => h0 (by simp [hsdef, hSdef, h])
          obtain ⟨-, hw2⟩ := r26t8a_annulus_ne_zero hchi hR ha
          have hu : ‖u‖ ≤ 2 * r1 := by
            have h3 : ‖u‖ ≤ ‖x‖ + ‖x - u‖ := by
              calc ‖u‖ = ‖x - (x - u)‖ := by congr 1; abel
                _ ≤ ‖x‖ + ‖x - u‖ := norm_sub_le _ _
            rw [hr1def]; linarith
          rw [hKkdef, r26t8a_Kk_eq hchi hr1 hu]; ring
      obtain ⟨B0, hB0'⟩ := hscont.bounded_above_of_compact_support (hsk Y)
      have hint1 : Integrable (fun u => Kk u * s (x - u)) :=
        hKk.mul_bdd (hscont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
          (c := B0) (Eventually.of_forall fun u => hB0' _)
      have hint2 : Integrable (fun u => s (x - u)) := hsint.comp_sub_left x
      rw [h1, show (fun u => newtonKernel d nu u * s (x - u)) = fun u => Kk u * s (x - u) + kappa * s (x - u) from
        funext h2, integral_add hint1 (hint2.const_mul kappa), integral_const_mul,
        integral_sub_left_eq_self s volume x]
    have hev : r26t8a_annularNewton nu chi R F Y =ᶠ[𝓝 z]
        fun x => (∫ u, Kk u * s (x - u)) + kappa * ∫ w, s w :=
      Filter.eventuallyEq_of_mem (Metric.ball_mem_nhds z one_pos) hloc
    rw [(hev.iteratedFDeriv ℝ q).eq_of_nhds]
    by_cases hq0 : q = 0
    · have hk0 := hkappa hq0
      simp only [hk0, zero_mul, add_zero]
      exact hAf
    · have hc : ContDiffAt ℝ (q : WithTop ℕ∞) (fun _ : Euc d => kappa * ∫ w, s w) z := contDiffAt_const
      rw [show (fun x => (∫ u, Kk u * s (x - u)) + kappa * ∫ w, s w) =
        (fun x => ∫ u, Kk u * s (x - u)) + fun _ => kappa * ∫ w, s w from rfl,
        iteratedFDeriv_add_apply hAd.contDiffAt hc, iteratedFDeriv_const_of_ne hq0, Pi.zero_apply, add_zero]
      exact hAf
  -- Claim 2: derivative in Y
  set Θ : Euc d × Euc d → ℝ := fun Yw => chi (Yw.1 - X) * S Yw with hΘdef
  have hΘ : ContDiff ℝ k Θ :=
    ((hchi.1.comp (contDiff_fst.sub contDiff_const)).of_le (by exact_mod_cast le_top)).mul hS
  have hΘc : HasCompactSupport Θ := by
    refine HasCompactSupport.of_support_subset_isCompact
      ((isCompact_closedBall X 2).prod (isCompact_closedBall (0 : Euc d) (2 * R))) (fun Yw hYw => ?_)
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_eq_norm]
      by_contra hn
      push Not at hn
      exact hYw (by simp only [hΘdef]; rw [hchi.2.2.2.2 _ hn.le, zero_mul])
    · exact hsupp Yw.1 (fun h => hYw (by simp only [hΘdef]; rw [show S Yw = 0 from h, mul_zero]))
  have hΘq : ContDiff ℝ (q : WithTop ℕ∞) Θ := hΘ.of_le (by exact_mod_cast (by omega : q ≤ k))
  set Ψ : Euc d × Euc d → ContinuousMultilinearMap ℝ (fun _ : Fin q => Euc d) ℝ :=
    fun Yw => iteratedFDeriv ℝ q (fun w => Θ (Yw.1, w)) Yw.2 with hΨdef
  have hΨeq : Ψ = fun Yw => (iteratedFDeriv ℝ q Θ Yw).compContinuousLinearMap
      (fun _ => ContinuousLinearMap.inr ℝ (Euc d) (Euc d)) :=
    funext fun Yw => r26t8a_slice_jet_inr hΘq Yw.1 Yw.2
  have hΨd : ContDiff ℝ (p : WithTop ℕ∞) Ψ := by
    rw [hΨeq]
    exact (ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin q => ContinuousLinearMap.inr ℝ (Euc d) (Euc d))).contDiff.comp
      (hΘ.iteratedFDeriv_right (m := (p : WithTop ℕ∞)) (by exact_mod_cast hpq))
  have hΨc : HasCompactSupport Ψ := by
    rw [hΨeq]
    exact (hΘc.iteratedFDeriv q).comp_left (g := fun T : ContinuousMultilinearMap ℝ (fun _ : Fin q => Euc d × Euc d) ℝ =>
      T.compContinuousLinearMap (fun _ => ContinuousLinearMap.inr ℝ (Euc d) (Euc d)))
      (ContinuousMultilinearMap.ext fun _ => rfl)
  have hopen : IsOpen {Y : Euc d | ‖Y - X‖ < 1} :=
    isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const
  have hΘS : ∀ Y : Euc d, ‖Y - X‖ < 1 → (fun w => Θ (Y, w)) = fun w => S (Y, w) := fun Y hY =>
    funext fun w => by simp [hΘdef, hchi.2.2.2.1 _ hY.le]
  have hev1 : (fun Y => iteratedFDeriv ℝ q (r26t8a_annularNewton nu chi R F Y) z) =ᶠ[𝓝 X]
      fun Y => ∫ u, Kk u • Ψ (Y, z - u) := by
    filter_upwards [hopen.mem_nhds (by simp)] with Y hY
    rw [hclaim Y]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [hΨdef, hΘS Y hY]
  rw [(hev1.iteratedFDeriv ℝ p).eq_of_nhds, r26t8a_stageB hKk hΨd hΨc X z]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  beta_reduce
  congr 1
  have hev2 : (fun Y => Ψ (Y, z - u)) =ᶠ[𝓝 X]
      fun Y => iteratedFDeriv ℝ q (fun w => r26t8a_annulus chi R w * midPair F Y w) (z - u) := by
    filter_upwards [hopen.mem_nhds (by simp)] with Y hY
    simp only [hΨdef, hΘS Y hY]
    rfl
  exact (hev2.iteratedFDeriv ℝ p).eq_of_nhds

end HRS.MS.R26T8A
