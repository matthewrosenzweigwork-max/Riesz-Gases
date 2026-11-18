import HRS.MS.ToriCoefBAux2

/-!
# MS-TORI-COEFB, helper file 3: the kernel hypotheses `tcb_Kern` for the coordinates of `∇γ_L`

For every `γ` with `IsPeriodicRieszKernel d s L γ` (`L ≥ 1`) we have, with `C₀` independent of `L`,
`|∇γ(z)| ≤ C₀|z|^{-(s+1)}` for `0 < |z| ≤ 1/2` (from `ker1_gam_bound_a` and `ker1_eq_gam`), and
`|∇γ(z)| ≤ C₀` on the part `|z| > 1/4` of the closed cube `[-L/2, L/2]^d` (also the corners, by scaling
`γ_L = L^{-s} g₁(·/L)` and compactness of `{|w|_∞ ≤ 1/2, |w| ≥ 1/2}`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ToriCoefB

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.Ker1

variable {d : ℕ}

theorem tcb_corner_mk_ne {w : Euc d} (hw : ∀ i, |w i| ≤ 1 / 2) (hn : 1 / 2 ≤ ‖w‖) :
    Torus.mk w ≠ 0 := by
  intro h
  obtain ⟨n, hn'⟩ := ker1_mk_eq_zero h
  have h0 : w = 0 := by
    ext i
    have hi : w i = (n i : ℝ) := by rw [hn']; rfl
    have h1 := hw i
    rw [hi] at h1
    have h2 : |n i| < 1 := by
      have : ((|n i| : ℤ) : ℝ) < 1 := by
        rw [Int.cast_abs]; linarith
      exact_mod_cast this
    have h3 : n i = 0 := Int.abs_lt_one_iff.1 h2
    simp [hi, h3]
  rw [h0] at hn
  simp at hn
  linarith

theorem tcb_corner_bound (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ w : Euc d, (∀ i, |w i| ≤ 1 / 2) → 1 / 2 ≤ ‖w‖ →
      ‖iteratedFDeriv ℝ 1 (ker1_g1 d s) w‖ ≤ M := by
  set K : Set (Euc d) :=
    {w | ∀ i, w i ∈ Icc (-(1 / 2 : ℝ)) (1 / 2)} ∩ {w | 1 / 2 ≤ ‖w‖} with hKdef
  have hK : IsCompact K :=
    (tcb_compact_Icc _ _).inter_right (isClosed_le continuous_const continuous_norm)
  have hsm := ker1_g1_contDiffOn hd hs0 hsd
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    ((ker1_continuousOn_iteratedFDeriv hsm 1).mono (fun w hw =>
      tcb_corner_mk_ne (fun i => abs_le.2 ⟨(hw.1 i).1, (hw.1 i).2⟩) hw.2))
  refine ⟨max M 0, le_max_right _ _, fun w hw hn => ?_⟩
  refine (hM w ⟨fun i => ?_, hn⟩).trans (le_max_left _ _)
  have := abs_le.1 (hw i)
  exact ⟨this.1, this.2⟩

theorem tcb_norm_gradient (f : Euc d → ℝ) (z : Euc d) :
    ‖gradient f z‖ = ‖iteratedFDeriv ℝ 1 f z‖ := by
  rw [norm_iteratedFDeriv_one]
  unfold gradient
  exact LinearIsometryEquiv.norm_map _ _

theorem tcb_gradient_eq {γ g : Euc d → ℝ} {z : Euc d} (h : γ =ᶠ[𝓝 z] g) :
    gradient γ z = gradient g z := by
  unfold gradient
  rw [h.fderiv_eq]

theorem tcb_grad_bounds (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ L : ℝ, 1 ≤ L → ∀ γ : Euc d → ℝ, IsPeriodicRieszKernel d s L γ →
      (∀ z : Euc d, z ≠ 0 → ‖z‖ ≤ 1 / 2 → ‖gradient γ z‖ ≤ C₀ * ‖z‖ ^ (-(s + 1))) ∧
      (∀ z : Euc d, (∀ i, |z i| ≤ L / 2) → 1 / 4 < ‖z‖ → ‖gradient γ z‖ ≤ C₀) := by
  obtain ⟨C, hC0, hC⟩ := ker1_gam_bound_a hd hs0 hsd 1 (by positivity)
  obtain ⟨M, hM0, hM⟩ := tcb_corner_bound hd hs0 hsd
  have hq : 0 ≤ C * (1 / 4 : ℝ) ^ (-(s + 1)) := mul_nonneg hC0 (Real.rpow_nonneg (by norm_num) _)
  refine ⟨C + C * (1 / 4 : ℝ) ^ (-(s + 1)) + M, by positivity, fun L hL γ hγ => ⟨?_, ?_⟩⟩
  · intro z hz0 hz
    have hLp : 0 < L := by linarith
    have hoff := ker1_offLattice_of_half hLp hz0 (by linarith : ‖z‖ ≤ L / 2)
    rw [tcb_gradient_eq (ker1_eventually_eq_gam hd hs0 hsd hLp hγ hoff), tcb_norm_gradient]
    have h1 := hC L hLp z hz0 (by linarith)
    have e : -s - ((1 : ℕ) : ℝ) = -(s + 1) := by push_cast; ring
    rw [e] at h1
    refine h1.trans ?_
    have : 0 ≤ ‖z‖ ^ (-(s + 1)) := Real.rpow_nonneg (norm_nonneg _) _
    nlinarith
  · intro z hzc hz4
    have hLp : 0 < L := by linarith
    have hz0 : z ≠ 0 := by
      intro h; rw [h, norm_zero] at hz4; linarith
    by_cases hzL : ‖z‖ ≤ L / 2
    · have hoff := ker1_offLattice_of_half hLp hz0 hzL
      rw [tcb_gradient_eq (ker1_eventually_eq_gam hd hs0 hsd hLp hγ hoff), tcb_norm_gradient]
      have h1 := hC L hLp z hz0 hzL
      have e : -s - ((1 : ℕ) : ℝ) = -(s + 1) := by push_cast; ring
      rw [e] at h1
      refine h1.trans ?_
      have h2 : ‖z‖ ^ (-(s + 1)) ≤ (1 / 4 : ℝ) ^ (-(s + 1)) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hz4.le (by linarith)
      have h3 := mul_le_mul_of_nonneg_left h2 hC0
      linarith
    · push_neg at hzL
      have hw : ∀ i, |(L⁻¹ • z) i| ≤ 1 / 2 := by
        intro i
        have : (L⁻¹ • z) i = L⁻¹ * z i := by simp
        rw [this, abs_mul, abs_of_pos (inv_pos.2 hLp), ← div_eq_inv_mul, div_le_iff₀ hLp]
        linarith [hzc i]
      have hwn : 1 / 2 ≤ ‖L⁻¹ • z‖ := by
        rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hLp, inv_mul_eq_div, le_div_iff₀ hLp]
        linarith
      have hmk := tcb_corner_mk_ne hw hwn
      have hoff := (ker1_offLattice_iff hLp z).2 hmk
      rw [tcb_gradient_eq (ker1_eventually_eq_gam hd hs0 hsd hLp hγ hoff), tcb_norm_gradient,
        ker1_gam_iter hd hs0 hsd hLp hmk 1, norm_smul, Real.norm_eq_abs]
      have h1 := hM _ hw hwn
      have hL1 : L ^ (-s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL (by linarith)
      have hL2 : L⁻¹ ^ 1 ≤ 1 := by
        rw [pow_one]; exact inv_le_one_of_one_le₀ hL
      have hL3 : 0 ≤ L ^ (-s) * L⁻¹ ^ 1 :=
        mul_nonneg (Real.rpow_nonneg hLp.le _) (pow_nonneg (inv_nonneg.2 hLp.le) _)
      rw [abs_of_nonneg hL3]
      have h4 : L ^ (-s) * L⁻¹ ^ 1 ≤ 1 := by
        calc L ^ (-s) * L⁻¹ ^ 1 ≤ 1 * 1 :=
              mul_le_mul hL1 hL2 (pow_nonneg (inv_nonneg.2 hLp.le) _) zero_le_one
          _ = 1 := one_mul 1
      have h5 : L ^ (-s) * L⁻¹ ^ 1 * ‖iteratedFDeriv ℝ 1 (ker1_g1 d s) (L⁻¹ • z)‖ ≤ M := by
        calc L ^ (-s) * L⁻¹ ^ 1 * ‖iteratedFDeriv ℝ 1 (ker1_g1 d s) (L⁻¹ • z)‖
            ≤ 1 * M := mul_le_mul h4 h1 (norm_nonneg _) zero_le_one
          _ = M := one_mul M
      linarith

theorem tcb_kern_coord (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C₀ A₀ : ℝ, 0 ≤ C₀ ∧ 0 ≤ A₀ ∧ ∀ L : ℝ, 1 ≤ L → ∀ γ : Euc d → ℝ, IsPeriodicRieszKernel d s L γ →
      ∀ i : Fin d, tcb_Kern L (fun z => gradient γ z i) C₀ ∧
        tcb_a (fun z => gradient γ z i) ≤ A₀ := by
  obtain ⟨C₀, hC₀, hC⟩ := tcb_grad_bounds hd hs0 hsd
  have hfin : 1 ≤ Module.finrank ℝ (Euc d) := by
    rw [finrank_euclideanSpace_fin]; exact hd
  have hrhs : IntegrableOn (fun z : Euc d => C₀ * ‖z‖ ^ (-s)) (Metric.ball 0 (1 / 2)) volume := by
    refine integrableOn_ball_of_norm_le_rpow hfin (C := C₀) (α := s)
      (by rw [finrank_euclideanSpace_fin]; exact hsd) ?_
      ((measurable_norm.pow_const _).const_mul C₀).aestronglyMeasurable
    refine Filter.Eventually.of_forall fun z => ?_
    rw [Real.norm_of_nonneg (mul_nonneg hC₀ (Real.rpow_nonneg (norm_nonneg _) _))]
  have hNsub : tcb_N d ⊆ Metric.ball (0 : Euc d) (1 / 2) := fun z hz => by
    have : ‖z‖ ≤ 1 / 4 := by simpa [tcb_N] using hz
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  refine ⟨C₀, ∫ z in tcb_N d, C₀ * ‖z‖ ^ (-s),  hC₀,
    setIntegral_nonneg tcb_measurableSet_N fun z _ =>
      mul_nonneg hC₀ (Real.rpow_nonneg (norm_nonneg _) _), fun L hL γ hγ i => ?_⟩
  obtain ⟨hnear, hfar⟩ := hC L hL γ hγ
  have hcoord : ∀ z : Euc d, |gradient γ z i| ≤ ‖gradient γ z‖ := fun z => by
    have := PiLp.norm_apply_le (gradient γ z) i
    rwa [Real.norm_eq_abs] at this
  have hm : Measurable (gradient γ) := by
    have : gradient γ = (InnerProductSpace.toDual ℝ (Euc d)).symm ∘ fderiv ℝ γ := rfl
    rw [this]
    exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.measurable.comp (measurable_fderiv ℝ γ)
  have hmi : Measurable fun z : Euc d => gradient γ z i :=
    (by fun_prop : Continuous fun v : Euc d => v i).measurable.comp hm
  have hmeas : AEStronglyMeasurable (fun z : Euc d => |gradient γ z i| * ‖z‖) volume :=
    (hmi.abs.mul measurable_norm).aestronglyMeasurable
  have hdom : ∀ z ∈ Metric.ball (0 : Euc d) (1 / 2),
      |gradient γ z i| * ‖z‖ ≤ C₀ * ‖z‖ ^ (-s) := by
    intro z hz
    have hz2 : ‖z‖ ≤ 1 / 2 := by
      have := mem_ball_zero_iff.1 hz
      linarith
    by_cases hz0 : z = 0
    · subst hz0
      simp only [norm_zero, mul_zero]
      exact mul_nonneg hC₀ (Real.rpow_nonneg le_rfl _)
    · have h1 := (hcoord z).trans (hnear z hz0 hz2)
      have h2 : ‖z‖ ^ (-s) = ‖z‖ ^ (-(s + 1)) * ‖z‖ := by
        rw [← Real.rpow_add_one (norm_ne_zero_iff.2 hz0)]
        congr 1; ring
      rw [h2]
      have := mul_le_mul_of_nonneg_right h1 (norm_nonneg z)
      linarith
  have hball : IntegrableOn (fun z : Euc d => |gradient γ z i| * ‖z‖) (Metric.ball 0 (1 / 2))
      volume := by
    refine Integrable.mono' hrhs hmeas.restrict ?_
    refine ae_restrict_of_forall_mem Metric.isOpen_ball.measurableSet fun z hz => ?_
    rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (norm_nonneg _))]
    exact hdom z hz
  have hintN : IntegrableOn (fun z : Euc d => |gradient γ z i| * ‖z‖) (tcb_N d) volume :=
    hball.mono_set hNsub
  refine ⟨⟨hL, hC₀, hmi, hintN, ?_⟩, ?_⟩
  · intro z hz hz4
    have h4 : 1 / 4 < ‖z‖ := not_le.1 hz4
    exact (hcoord z).trans (hfar z (fun j => abs_le.2 ⟨(hz j).1, (hz j).2.le⟩) h4)
  · unfold tcb_a
    exact setIntegral_mono_on hintN (hrhs.mono_set hNsub) tcb_measurableSet_N
      fun z hz => hdom z (hNsub hz)

end HRS.MS.ToriCoefB
