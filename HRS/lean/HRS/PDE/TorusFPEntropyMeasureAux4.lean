import HRS.PDE.TorusFPEntropyMeasureAux3

/-!
# D3-b, Aux4: the measure-valued free-energy inequality (proof of `d3_tilted_inequality`)

Route: entropy-recovering smooth positive data `g k → μ 0` (Aux2), classical solutions `w k` and the exact
identity (packet D3A), narrow stability by duality (Aux1), lower semicontinuity of the entropy and of the
Fisher information, Fatou in time, dominated convergence for the source term, and the real combination
lemma of Aux3.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS

variable {n : ℕ}

theorem d3b_source_cont {κ : ℝ} {U : Torus n → ℝ} (hU : Torus.IsSmooth U) {T : ℝ}
    {ψ ψt : ℝ → Torus n → ℝ} (hψ : IsC12Test T ψ ψt) :
    Continuous fun p : Set.Icc (0 : ℝ) T × Torus n => d3_source κ U ψ ψt p.1 p.2 :=
  ((hψ.continuous_gen (d1_gradDrift_continuous hU)).add
    (continuous_const.mul ((d3a_continuous_grad hψ).norm.pow 2))).sub hψ.cont_time_deriv

theorem d3b_classical_prob0 {κ : ℝ} {U : Torus n → ℝ} (hU : Torus.IsSmooth U) {w : Torus n → ℝ}
    (hc : Continuous w) (hpos : ∀ x, 0 < w x) (hmass : ∫ x, w x ∂(d1_gibbsMeasure κ U) = 1) :
    IsProbabilityMeasure ((d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (w x)) := by
  haveI := d3a_gibbs_isProb (κ := κ) hU
  exact ⟨by rw [d3a_mass_eq hc (fun x => (hpos x).le), hmass]; simp⟩

/-- **Measure-valued free-energy inequality** (statement of `d3_tilted_inequality`). -/
theorem d3b_tilted_main (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)
    {T : ℝ} (hT : 0 < T) {μ : ℝ → Measure (Torus n)}
    (hμ : D1WeakSolution κ (d1_gradDrift U) T μ) [IsProbabilityMeasure (μ 0)]
    (hfin : relEntropy (μ 0) (d1_gibbsMeasure κ U) ≠ ⊤)
    {ψ ψt : ℝ → Torus n → ℝ} (hψ : IsC12Test T ψ ψt) :
    ∀ t ∈ Set.Icc 0 T,
      relEntropy (μ t) (d1_gibbsMeasure κ U) ≠ ⊤ ∧
      ∫⁻ r in Set.Icc 0 t, d1_fisherInfo κ (d3_tiltPot κ U (ψ r)) (μ r) < ⊤ ∧
      ((relEntropy (μ t) (d1_gibbsMeasure κ U)).toReal - ∫ x, ψ t x ∂(μ t))
        + κ * (∫⁻ r in Set.Icc 0 t, d1_fisherInfo κ (d3_tiltPot κ U (ψ r)) (μ r)).toReal
      ≤ ((relEntropy (μ 0) (d1_gibbsMeasure κ U)).toReal - ∫ x, ψ 0 x ∂(μ 0))
        + ∫ r in Set.Icc 0 t, ∫ x, d3_source κ U ψ ψt r x ∂(μ r) := by
  haveI hP := d3a_gibbs_isProb (κ := κ) hU
  obtain ⟨g, hgs, hgpos, hgmass, hgconv, hgent⟩ := d3b_approx_measure (d1_gibbsMeasure κ U) (μ 0) hfin
  have hex : ∀ k, ∃ w : ℝ → Torus n → ℝ, D3Classical κ U T w ∧ w 0 = g k := fun k =>
    d3_classical_exists_proof hn hκ hU hT (hgs k) (hgpos k)
  choose w hw hw0 using hex
  set P : Measure (Torus n) := d1_gibbsMeasure κ U with hPdef
  set μk : ℕ → ℝ → Measure (Torus n) := fun k s => P.withDensity fun x => ENNReal.ofReal (w k s x)
    with hμk
  have hmassk : ∀ k, ∫ x, w k 0 x ∂P = 1 := fun k => by rw [hw0 k]; exact hgmass k
  have hweak : ∀ k, D1WeakSolution κ (d1_gradDrift U) T (μk k) := fun k =>
    d3_classical_isWeak_proof hn hκ hU (hw k)
  have hwc : ∀ k, Continuous fun p : Set.Icc (0 : ℝ) T × Torus n => w k p.1 p.2 := fun k =>
    (hw k).c12.continuous_f
  have hc0 : ∀ k, Continuous (w k 0) := fun k => by
    rw [hw0 k]; exact d1c_continuous_of_isSmooth (hgs k)
  haveI hpk0 : ∀ k, IsProbabilityMeasure (μk k 0) := fun k =>
    d3b_classical_prob0 hU (hc0 k) (fun x => by rw [hw0 k]; exact hgpos k x) (hmassk k)
  have hμk0 : ∀ k, μk k 0 = P.withDensity fun x => ENNReal.ofReal (g k x) := fun k => by
    simp only [hμk, hw0 k]
  have h0conv : ∀ φ : Torus n → ℝ, Continuous φ →
      Tendsto (fun k => ∫ x, φ x ∂(μk k 0)) atTop (𝓝 (∫ x, φ x ∂(μ 0))) := fun φ hφ => by
    simp_rw [hμk0]; exact hgconv φ hφ
  have hstab := d3b_stability hn hκ hU hμ hweak h0conv
  intro t ht
  have hTI : ∀ r ∈ Set.Icc (0 : ℝ) t, r ∈ Set.Icc (0 : ℝ) T := fun r hr => ⟨hr.1, hr.2.trans ht.2⟩
  have hprob : ∀ r ∈ Set.Icc (0 : ℝ) T, IsProbabilityMeasure (μ r) := fun r hr =>
    d1_isProbabilityMeasure hμ hr
  have hprk : ∀ k, ∀ r ∈ Set.Icc (0 : ℝ) T, IsProbabilityMeasure (μk k r) := fun k r hr =>
    d1_isProbabilityMeasure (hweak k) hr
  have hψc : ∀ r ∈ Set.Icc (0 : ℝ) T, Continuous (ψ r) := fun r hr =>
    d3a_continuous_of_ck1 (d3a_ck2_ck1 (hψ.c2 r hr))
  have h0T : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
  -- source term
  have hsc := d3b_source_cont (κ := κ) hU hψ
  obtain ⟨Cs, hCs⟩ := d3a_bound hsc
  have hS : Tendsto (fun k => ∫ r in Set.Icc (0 : ℝ) t, ∫ x, d3_source κ U ψ ψt r x ∂(μk k r)) atTop
      (𝓝 (∫ r in Set.Icc (0 : ℝ) t, ∫ x, d3_source κ U ψ ψt r x ∂(μ r))) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => Cs) (fun k => ?_)
      (integrable_const _) (fun k => ?_) ?_
    · have := d3b_contOn_param (μ := μk k) (hprk k) (hweak k).narrow hsc
      exact (this.mono (Set.Icc_subset_Icc_right ht.2)).aestronglyMeasurable measurableSet_Icc
    · refine (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ fun r hr => ?_)
      haveI := hprk k r (hTI r hr)
      calc ‖∫ x, d3_source κ U ψ ψt r x ∂(μk k r)‖ ≤ Cs * (μk k r).real Set.univ :=
            norm_integral_le_of_norm_le_const (ae_of_all _ fun x => hCs r (hTI r hr) x)
        _ = Cs := by simp
    · refine (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ fun r hr => ?_)
      exact hstab r (hTI r hr) _ (d3a_contOn_space hsc (hTI r hr))
  have hΨt := hstab t ht (ψ t) (hψc t ht)
  have hΨ0 := h0conv (ψ 0) (hψc 0 h0T)
  -- the Fisher integrals
  have hgψ := d3a_continuous_grad hψ
  have hgl : ∀ k, Continuous fun p : Set.Icc (0 : ℝ) T × Torus n =>
      Torus.grad (fun y => Real.log (w k p.1 y)) p.2 := fun k => by
    have e : (fun p : Set.Icc (0 : ℝ) T × Torus n => Torus.grad (fun y => Real.log (w k p.1 y)) p.2) =
        fun p => (w k p.1 p.2)⁻¹ • Torus.grad (w k p.1) p.2 := funext fun p =>
      d3a_grad_log (d3a_ck2_ck1 ((hw k).c12.c2 p.1 p.1.2)) ((hw k).pos p.1 p.1.2) p.2
    rw [e]
    exact ((hwc k).inv₀ fun p => ((hw k).pos p.1 p.1.2 p.2).ne').smul (d3a_continuous_grad (hw k).c12)
  set J : ℕ → ℝ → ℝ := fun k r =>
    ∫ x, ‖Torus.grad (fun y => Real.log (w k r y)) x - Torus.grad (ψ r) x‖ ^ 2 ∂(μk k r) with hJdef
  have hJc : ∀ k, ContinuousOn (J k) (Set.Icc 0 T) := fun k =>
    d3b_contOn_param (μ := μk k) (hprk k) (hweak k).narrow
      (G := fun r x => ‖Torus.grad (fun y => Real.log (w k r y)) x - Torus.grad (ψ r) x‖ ^ 2)
      (((hgl k).sub hgψ).norm.pow 2)
  have hJ0 : ∀ k r, 0 ≤ J k r := fun k r => integral_nonneg fun x => sq_nonneg _
  have hFk : ∀ k, ∀ r ∈ Set.Icc (0 : ℝ) T,
      d1_fisherInfo κ (d3_tiltPot κ U (ψ r)) (μk k r) = ENNReal.ofReal (J k r) := fun k r hr =>
    d3_fisher_classical_proof hκ hU ((hw k).c12.c2 r hr) ((hw k).pos r hr) (hψ.c2 r hr)
  set j : ℕ → ℝ := fun k => ∫ r in Set.Icc (0 : ℝ) t, J k r with hjdef
  have hj0 : ∀ k, 0 ≤ j k := fun k => integral_nonneg fun r => hJ0 k r
  have hlint : ∀ k, ∫⁻ r in Set.Icc (0 : ℝ) t, ENNReal.ofReal (J k r) = ENNReal.ofReal (j k) := fun k => by
    rw [hjdef]
    exact (ofReal_integral_eq_lintegral_ofReal
      (((hJc k).mono (Set.Icc_subset_Icc_right ht.2)).integrableOn_Icc)
      (ae_of_all _ fun r => hJ0 k r)).symm
  have hFatou : ∫⁻ r in Set.Icc (0 : ℝ) t, d1_fisherInfo κ (d3_tiltPot κ U (ψ r)) (μ r) ≤
      liminf (fun k => ENNReal.ofReal (j k)) atTop := by
    calc ∫⁻ r in Set.Icc (0 : ℝ) t, d1_fisherInfo κ (d3_tiltPot κ U (ψ r)) (μ r)
        ≤ ∫⁻ r in Set.Icc (0 : ℝ) t, liminf (fun k => ENNReal.ofReal (J k r)) atTop := by
          refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ fun r hr => ?_))
          haveI := hprob r (hTI r hr)
          haveI : ∀ k, IsProbabilityMeasure (μk k r) := fun k => hprk k r (hTI r hr)
          have hl := d3b_fisher_lsc (κ := κ) (V := d3_tiltPot κ U (ψ r))
            (d3b_tilt_ck1 (d3a_smooth_ck1 hU) (d3a_ck2_ck1 (hψ.c2 r (hTI r hr))))
            (P := μ r) (Pn := fun k => μk k r) (hstab r (hTI r hr))
          refine hl.trans (le_of_eq ?_)
          congr 1
          funext k
          exact hFk k r (hTI r hr)
      _ ≤ liminf (fun k => ∫⁻ r in Set.Icc (0 : ℝ) t, ENNReal.ofReal (J k r)) atTop :=
          lintegral_liminf_le' fun k =>
            (ENNReal.measurable_ofReal.comp_aemeasurable
              (((hJc k).mono (Set.Icc_subset_Icc_right ht.2)).aemeasurable measurableSet_Icc))
      _ = _ := by congr 1; funext k; exact hlint k
  -- entropies
  set a : ℕ → ℝ := fun k => (relEntropy (μk k t) P).toReal with hadef
  have ha0 : ∀ k, 0 ≤ a k := fun k => ENNReal.toReal_nonneg
  have hrel : ∀ k, relEntropy (μk k t) P = ENNReal.ofReal (a k) := fun k => by
    have hne := d3b_klDiv_classical_ne_top (P := P) (d3a_contOn_space (hwc k) ht)
      (fun x => (hw k).pos t ht x)
    exact (ENNReal.ofReal_toReal hne).symm
  haveI hpt : IsProbabilityMeasure (μ t) := hprob t ht
  haveI hpkt : ∀ k, IsProbabilityMeasure (μk k t) := fun k => hprk k t ht
  have hA : relEntropy (μ t) P ≤ liminf (fun k => ENNReal.ofReal (a k)) atTop := by
    have h := b15b_klDiv_liminf_le (P := μ t) (Q := P) (Pn := fun k => μk k t) (Qn := fun _ => P)
      (hstab t ht) (fun φ _ => tendsto_const_nhds)
    have h' : relEntropy (μ t) P ≤ liminf (fun k => relEntropy (μk k t) P) atTop := h
    rwa [show (fun k => relEntropy (μk k t) P) = fun k => ENNReal.ofReal (a k) from funext hrel] at h'
  have hid : ∀ k, a k - ∫ x, ψ t x ∂(μk k t) + κ * j k =
      (relEntropy (μk k 0) P).toReal - ∫ x, ψ 0 x ∂(μk k 0) +
        ∫ r in Set.Icc (0 : ℝ) t, ∫ x, d3_source κ U ψ ψt r x ∂(μk k r) := fun k =>
    d3_tilted_identity_classical_proof hn hκ hU hT (hw k) (hmassk k) hψ t ht
  have hH0 : ∀ k : ℕ, (relEntropy (μk k 0) P).toReal ≤ (relEntropy (μ 0) P).toReal + 1 / ((k : ℝ) + 1) :=
    fun k => by rw [hμk0 k]; exact hgent k
  have hR : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, a k + κ * j k ≤
      (((relEntropy (μ 0) P).toReal - ∫ x, ψ 0 x ∂(μ 0)) +
        (∫ r in Set.Icc (0 : ℝ) t, ∫ x, d3_source κ U ψ ψt r x ∂(μ r)) + ∫ x, ψ t x ∂(μ t)) + ε := by
    intro ε hε
    have e1 : ∀ᶠ k : ℕ in atTop, 1 / ((k : ℝ) + 1) < ε / 4 :=
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds (by positivity))
    have e2 := (Metric.tendsto_nhds.1 hΨ0) (ε / 4) (by positivity)
    have e3 := (Metric.tendsto_nhds.1 hΨt) (ε / 4) (by positivity)
    have e4 := (Metric.tendsto_nhds.1 hS) (ε / 4) (by positivity)
    filter_upwards [e1, e2, e3, e4] with k h1 h2 h3 h4
    rw [Real.dist_eq, abs_lt] at h2 h3 h4
    have := hid k
    have := hH0 k
    linarith [h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]
  obtain ⟨hAt, hβt, hineq⟩ := d3b_combine hκ ha0 hj0 hA hFatou hR
  refine ⟨hAt, lt_top_iff_ne_top.2 hβt, ?_⟩
  linarith

end HRS
