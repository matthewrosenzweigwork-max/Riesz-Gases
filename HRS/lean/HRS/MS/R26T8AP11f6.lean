import HRS.MS.R26T8AP11f5
import HRS.MS.R26T8AP10a1

/-!
# S8.2 T8A P11f (part 6): singular-kernel potential of a smooth Gaussian-decaying source
`r26t8a_f6_pot_smooth`: if `H` is `C^k` on `E x E` with `‖D^i H (u,y)‖ ≤ B e^{-c|u|²} jb(y)^M`, then
`V(x,y) = ∫ |w|^(-s) H(x-w, y) dw` (`0 < s < d`) is `C^k` with `‖D^i V (x,y)‖ ≤ C B jb(y)^M`, `C` independent of `x`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem r26t8a_f6_pot_smooth (d : ℕ) (hd : 2 ≤ d) (k : ℕ) {s : ℝ} (hs0 : 0 < s) (hsd : s < d) {M c : ℝ}
    (hM : 0 ≤ M) (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (B : ℝ) (H : Euc d → Euc d → ℝ), 0 ≤ B →
      ContDiff ℝ (k : WithTop ℕ∞) (Function.uncurry H) →
      (∀ i ≤ k, ∀ u y : Euc d, ‖iteratedFDeriv ℝ i (Function.uncurry H) (u, y)‖ ≤
        B * Real.exp (-c * ‖u‖ ^ 2) * jbracket y ^ M) →
      ContDiff ℝ (k : WithTop ℕ∞) (fun p : Euc d × Euc d => ∫ w, ‖w‖ ^ (-s) * H (p.1 - w) p.2) ∧
      ∀ i ≤ k, ∀ p : Euc d × Euc d,
        ‖iteratedFDeriv ℝ i (fun p : Euc d × Euc d => ∫ w, ‖w‖ ^ (-s) * H (p.1 - w) p.2) p‖ ≤
          C * B * jbracket p.2 ^ M := by
  haveI : Nontrivial (Euc d) := ⟨⟨0, EuclideanSpace.single ⟨0, by omega⟩ (1 : ℝ), by
    intro h; have := congrArg (fun v : Euc d => v ⟨0, by omega⟩) h; simp at this⟩⟩
  obtain ⟨hmI, hmV⟩ := r26t8a_p11a_mass d hd ((d : ℝ) - s) (by linarith) (by linarith) 1 one_pos
  have hexp : (d : ℝ) - s - d = -s := by ring
  rw [hexp] at hmI hmV
  set Ω : ℝ := sphereArea d * ((1 : ℝ) ^ ((d : ℝ) - s) / ((d : ℝ) - s)) with hΩ
  have hgi : Integrable (fun v : Euc d => Real.exp (-(c / 2) * ‖v‖ ^ 2)) :=
    r26t8a_p10a_gauss_int (by linarith)
  set Gi : ℝ := ∫ v : Euc d, Real.exp (-(c / 2) * ‖v‖ ^ 2) with hGi
  have hGi0 : 0 ≤ Gi := integral_nonneg fun v => (Real.exp_pos _).le
  have hΩ0 : 0 ≤ Ω := by
    have : 0 ≤ ∫ z in ball (0 : Euc d) 1, ‖z‖ ^ (-s) :=
      setIntegral_nonneg measurableSet_ball fun z _ => Real.rpow_nonneg (norm_nonneg _) _
    rwa [hmV] at this
  refine ⟨Real.exp c * 3 ^ M * (Ω + Gi), by positivity, ?_⟩
  intro B H hB hHc hHj
  have hae : ∀ᵐ w : Euc d, w ≠ 0 := compl_mem_ae_iff.2 (measure_singleton (0 : Euc d))
  set G : Euc d → Euc d × Euc d → ℝ := fun w p => ‖w‖ ^ (-s) * H (p.1 - w) p.2 with hG
  have hHc' : ∀ w : Euc d, ContDiff ℝ (k : WithTop ℕ∞) (fun p : Euc d × Euc d => H (p.1 - w) p.2) := by
    intro w
    have : ContDiff ℝ (k : WithTop ℕ∞) (fun p : Euc d × Euc d => Function.uncurry H (p.1 - w, p.2)) :=
      hHc.comp ((contDiff_fst.sub contDiff_const).prodMk contDiff_snd)
    exact this
  have hGc : ∀ w : Euc d, ContDiff ℝ (k : WithTop ℕ∞) (G w) := fun w => contDiff_const.mul (hHc' w)
  -- jets of the fibre
  have hjet : ∀ (w : Euc d) (i : ℕ) (p : Euc d × Euc d),
      iteratedFDeriv ℝ i (fun p : Euc d × Euc d => H (p.1 - w) p.2) p =
        iteratedFDeriv ℝ i (Function.uncurry H) (p.1 - w, p.2) := by
    intro w i p
    have e : (fun p : Euc d × Euc d => H (p.1 - w) p.2) =
        fun z => Function.uncurry H (z - ((w, 0) : Euc d × Euc d)) := by
      funext z; simp [Function.uncurry]
    rw [e, iteratedFDeriv_comp_sub]
    congr 1
    ext <;> simp
  have hmeas : ∀ i ≤ k, ∀ p : Euc d × Euc d,
      AEStronglyMeasurable (fun w : Euc d => iteratedFDeriv ℝ i (G w) p) volume := by
    intro i hi p
    have hcont : ContinuousOn (fun w : Euc d => iteratedFDeriv ℝ i (G w) p) {w : Euc d | w ≠ 0} := by
      have e : ∀ w : Euc d, iteratedFDeriv ℝ i (G w) p =
          ‖w‖ ^ (-s) • iteratedFDeriv ℝ i (Function.uncurry H) (p.1 - w, p.2) := by
        intro w
        have h1 : G w = fun p => ‖w‖ ^ (-s) • (fun p : Euc d × Euc d => H (p.1 - w) p.2) p := rfl
        rw [h1, iteratedFDeriv_const_smul_apply' ((hHc' w).of_le (by exact_mod_cast hi)).contDiffAt, hjet]
      simp only [e]
      have hA : ContinuousOn (fun w : Euc d => ‖w‖ ^ (-s)) {w : Euc d | w ≠ 0} :=
        continuous_norm.continuousOn.rpow_const fun w hw => Or.inl (norm_ne_zero_iff.2 hw)
      have h1 := hHc.continuous_iteratedFDeriv (m := i) (by exact_mod_cast hi)
      have hB' : ContinuousOn (fun w : Euc d => iteratedFDeriv ℝ i (Function.uncurry H) (p.1 - w, p.2))
          {w : Euc d | w ≠ 0} :=
        (h1.comp ((continuous_const.sub continuous_id).prodMk continuous_const)).continuousOn
      exact hA.smul hB'
    have hs : MeasurableSet {w : Euc d | w ≠ 0} := isOpen_ne.measurableSet
    have h := hcont.aestronglyMeasurable (μ := (volume : Measure (Euc d))) hs
    have e1 : (volume : Measure (Euc d)).restrict {w : Euc d | w ≠ 0} = volume := by
      have := restrict_compl_singleton (μ := (volume : Measure (Euc d))) (0 : Euc d)
      simpa [Set.compl_singleton_eq] using this
    rwa [e1] at h
  have hmain : ∀ p0 : Euc d × Euc d, ContDiffAt ℝ (k : WithTop ℕ∞) (fun p : Euc d × Euc d => ∫ w, G w p) p0 ∧
      ∀ i ≤ k, ‖iteratedFDeriv ℝ i (fun p : Euc d × Euc d => ∫ w, G w p) p0‖ ≤
        Real.exp c * 3 ^ M * (Ω + Gi) * B * jbracket p0.2 ^ M := by
    intro p0
    set U : Set (Euc d × Euc d) := ball p0 1 with hU
    have hUo : IsOpen U := isOpen_ball
    have hp0U : p0 ∈ U := mem_ball_self one_pos
    have hj0 := s83_jb_pos p0.2
    set e0 : ℝ := B * Real.exp c * (3 * jbracket p0.2) ^ M with he0
    have he00 : 0 ≤ e0 := by
      have : 0 ≤ (3 * jbracket p0.2) ^ M := Real.rpow_nonneg (by positivity) _
      positivity
    set Φ : Euc d → ℝ := fun w => e0 * ((ball (0 : Euc d) 1).indicator (fun v => ‖v‖ ^ (-s)) w +
      Real.exp (-(c / 2) * ‖p0.1 - w‖ ^ 2)) with hΦd
    have hΦ : Integrable Φ := by
      refine Integrable.const_mul (Integrable.add ?_ ?_) e0
      · exact (integrable_indicator_iff measurableSet_ball).2 hmI
      · exact hgi.comp_sub_left p0.1
    have hbd : ∀ i ≤ k, ∀ᵐ w : Euc d, ∀ p ∈ U, ‖iteratedFDeriv ℝ i (G w) p‖ ≤ Φ w := by
      intro i hi
      filter_upwards [hae] with w hw p hp
      have hp1 : ‖p - p0‖ < 1 := by rw [hU, mem_ball, dist_eq_norm] at hp; exact hp
      have h1 : ‖p.1 - p0.1‖ ≤ ‖p - p0‖ := norm_fst_le (p - p0)
      have h2 : ‖p.2 - p0.2‖ ≤ ‖p - p0‖ := norm_snd_le (p - p0)
      have hjb : jbracket p.2 ≤ 3 * jbracket p0.2 := by
        have := r26t8a_jb_shift' p0.2 (p.2 - p0.2)
        rw [add_sub_cancel] at this
        have h2' : ‖p.2 - p0.2‖ ≤ 1 := by linarith
        nlinarith [mul_le_mul_of_nonneg_right (show 2 + ‖p.2 - p0.2‖ ≤ 3 by linarith) hj0.le]
      have h3 : jbracket p.2 ^ M ≤ (3 * jbracket p0.2) ^ M :=
        Real.rpow_le_rpow (s83_jb_pos _).le hjb hM
      have hg : -c * ‖p.1 - w‖ ^ 2 ≤ -(c / 2) * ‖p0.1 - w‖ ^ 2 + c := by
        have h4 : ‖p0.1 - w‖ ≤ ‖p.1 - w‖ + ‖p.1 - p0.1‖ := by
          have : p0.1 - w = (p.1 - w) - (p.1 - p0.1) := by abel
          rw [this]; exact norm_sub_le _ _
        have h5 : ‖p0.1 - w‖ ^ 2 ≤ 2 * ‖p.1 - w‖ ^ 2 + 2 * 1 := by
          have h6 : ‖p.1 - p0.1‖ ≤ 1 := by linarith
          have h7 := pow_le_pow_left₀ (norm_nonneg _) h4 2
          nlinarith [sq_nonneg (‖p.1 - w‖ - ‖p.1 - p0.1‖), norm_nonneg (p.1 - p0.1), norm_nonneg (p.1 - w)]
        linarith [mul_le_mul_of_nonneg_left h5 hc.le]
      have h7 : Real.exp (-c * ‖p.1 - w‖ ^ 2) ≤ Real.exp c * Real.exp (-(c / 2) * ‖p0.1 - w‖ ^ 2) := by
        rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
      have hGj : ‖iteratedFDeriv ℝ i (G w) p‖ = ‖w‖ ^ (-s) *
          ‖iteratedFDeriv ℝ i (Function.uncurry H) (p.1 - w, p.2)‖ := by
        have h1' : G w = fun p => ‖w‖ ^ (-s) • (fun p : Euc d × Euc d => H (p.1 - w) p.2) p := rfl
        rw [h1', iteratedFDeriv_const_smul_apply' ((hHc' w).of_le (by exact_mod_cast hi)).contDiffAt, hjet,
          norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      rw [hGj]
      have h8 := hHj i hi (p.1 - w) p.2
      have hk0 : 0 ≤ ‖w‖ ^ (-s) := Real.rpow_nonneg (norm_nonneg _) _
      have hE : ‖iteratedFDeriv ℝ i (Function.uncurry H) (p.1 - w, p.2)‖ ≤
          B * (Real.exp c * Real.exp (-(c / 2) * ‖p0.1 - w‖ ^ 2)) * (3 * jbracket p0.2) ^ M := by
        refine h8.trans ?_
        have hjp : 0 ≤ jbracket p.2 ^ M := Real.rpow_nonneg (s83_jb_pos _).le _
        exact mul_le_mul (mul_le_mul_of_nonneg_left h7 hB) h3 hjp (by positivity)
      have hker : ‖w‖ ^ (-s) * Real.exp (-(c / 2) * ‖p0.1 - w‖ ^ 2) ≤
          (ball (0 : Euc d) 1).indicator (fun v => ‖v‖ ^ (-s)) w + Real.exp (-(c / 2) * ‖p0.1 - w‖ ^ 2) := by
        by_cases hw1 : w ∈ ball (0 : Euc d) 1
        · rw [Set.indicator_of_mem hw1]
          have : Real.exp (-(c / 2) * ‖p0.1 - w‖ ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖p0.1 - w‖])
          nlinarith [Real.exp_pos (-(c / 2) * ‖p0.1 - w‖ ^ 2), mul_le_mul_of_nonneg_left this hk0]
        · rw [Set.indicator_of_notMem hw1]
          have hw2 : 1 ≤ ‖w‖ := by simpa [mem_ball_zero_iff] using hw1
          have : ‖w‖ ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hw2 (by linarith)
          nlinarith [Real.exp_pos (-(c / 2) * ‖p0.1 - w‖ ^ 2), mul_le_mul_of_nonneg_right this
            (Real.exp_pos (-(c / 2) * ‖p0.1 - w‖ ^ 2)).le]
      calc ‖w‖ ^ (-s) * ‖iteratedFDeriv ℝ i (Function.uncurry H) (p.1 - w, p.2)‖
          ≤ ‖w‖ ^ (-s) * (B * (Real.exp c * Real.exp (-(c / 2) * ‖p0.1 - w‖ ^ 2)) * (3 * jbracket p0.2) ^ M) :=
            mul_le_mul_of_nonneg_left hE hk0
        _ = e0 * (‖w‖ ^ (-s) * Real.exp (-(c / 2) * ‖p0.1 - w‖ ^ 2)) := by rw [he0]; ring
        _ ≤ e0 * ((ball (0 : Euc d) 1).indicator (fun v => ‖v‖ ^ (-s)) w +
              Real.exp (-(c / 2) * ‖p0.1 - w‖ ^ 2)) := mul_le_mul_of_nonneg_left hker he00
    have hG' : ∀ᵐ w : Euc d, ∀ p ∈ U, ContDiffAt ℝ (k : WithTop ℕ∞) (G w) p := by
      filter_upwards with w p _
      exact (hGc w).contDiffAt
    have hmeas' : ∀ i ≤ k, ∀ p ∈ U, AEStronglyMeasurable (fun w : Euc d => iteratedFDeriv ℝ i (G w) p) volume :=
      fun i hi p _ => hmeas i hi p
    have hform := r26t8a_iter_integral (μ := volume) hUo G k hG' hΦ hbd hmeas'
    have hcd := r26t8a_contDiffOn_integral (μ := volume) hUo G k hG' hΦ hbd hmeas'
    refine ⟨(hcd.contDiffAt (hUo.mem_nhds hp0U)), fun i hi => ?_⟩
    rw [hform i hi p0 hp0U]
    refine (norm_integral_le_of_norm_le hΦ (by filter_upwards [hbd i hi] with w hw using hw p0 hp0U)).trans ?_
    rw [hΦd, integral_const_mul]
    have hi1 : ∫ w : Euc d, (ball (0 : Euc d) 1).indicator (fun v => ‖v‖ ^ (-s)) w = Ω := by
      rw [integral_indicator measurableSet_ball, hmV]
    have hi2 : ∫ w : Euc d, Real.exp (-(c / 2) * ‖p0.1 - w‖ ^ 2) = Gi := by
      rw [hGi]
      exact integral_sub_left_eq_self (fun v : Euc d => Real.exp (-(c / 2) * ‖v‖ ^ 2)) volume p0.1
    have hsplit : ∫ w : Euc d, ((ball (0 : Euc d) 1).indicator (fun v => ‖v‖ ^ (-s)) w +
        Real.exp (-(c / 2) * ‖p0.1 - w‖ ^ 2)) = Ω + Gi := by
      rw [integral_add ((integrable_indicator_iff measurableSet_ball).2 hmI) (hgi.comp_sub_left p0.1), hi1, hi2]
    rw [hsplit, he0]
    have h3 : (3 * jbracket p0.2) ^ M = 3 ^ M * jbracket p0.2 ^ M :=
      Real.mul_rpow (by norm_num) (s83_jb_pos _).le
    rw [h3]
    refine le_of_eq ?_
    ring
  exact ⟨contDiff_iff_contDiffAt.2 fun p0 => (hmain p0).1, fun i hi p => (hmain p).2 i hi⟩

end HRS.MS.R26T8A
