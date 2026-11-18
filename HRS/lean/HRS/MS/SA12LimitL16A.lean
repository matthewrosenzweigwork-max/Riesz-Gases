import HRS.MH.AdjointRdDefs
import HRS.Whole.AppendixAAdjoint
import HRS.PDE.ToolboxRd.Fourier

/-!
# S.A.12 L16 (core): weak lower semicontinuity of the `H^m` Fourier norm
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff ComplexConjugate

namespace HRS.MH.AdjointRd.Phase2SA12Limit

open HRS HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

theorem sa12x_inner_cplx {w : Euc d → ℝ} (hw : MemLp w 2 volume) (k : Lp (α := Euc d) ℂ 2) :
    inner ℂ (ofRealLp hw) k = ((∫ x, w x * (k x).re : ℝ) : ℂ) + ((∫ x, w x * (k x).im : ℝ) : ℂ) * Complex.I := by
  rw [MeasureTheory.L2.inner_def]
  have hi : Integrable (fun x => inner ℂ ((ofRealLp hw : Lp ℂ 2) x) (k x)) volume :=
    MeasureTheory.L2.integrable_inner _ _
  have h1 : (fun x => inner ℂ ((ofRealLp hw : Lp ℂ 2) x) (k x)) =ᵐ[volume]
      fun x => (k x) * ((w x : ℝ) : ℂ) := by
    filter_upwards [ofRealLp_coe hw] with x hx
    rw [hx]; simp
  rw [integral_congr_ae h1]
  have hi' : Integrable (fun x => (k x) * ((w x : ℝ) : ℂ)) volume := hi.congr h1
  have := integral_re_add_im hi'
  simp only [RCLike.re_to_complex, RCLike.im_to_complex, RCLike.I_to_complex] at this
  have e1 : ∀ x, ((k x) * ((w x : ℝ) : ℂ)).re = w x * (k x).re := fun x => by
    simp [Complex.mul_re, mul_comm]
  have e2 : ∀ x, ((k x) * ((w x : ℝ) : ℂ)).im = w x * (k x).im := fun x => by
    simp [Complex.mul_im, mul_comm]
  simp_rw [e1, e2] at this
  exact this.symm

theorem sa12x_weak_cplx {wn : ℕ → Euc d → ℝ} {w : Euc d → ℝ}
    (hwn : ∀ n, MemLp (wn n) 2 volume) (hw : MemLp w 2 volume)
    (hconv : ∀ ψ : Euc d → ℝ, MemLp ψ 2 volume →
      Tendsto (fun n => ∫ x, wn n x * ψ x) atTop (𝓝 (∫ x, w x * ψ x)))
    (k : Lp (α := Euc d) ℂ 2) :
    Tendsto (fun n => inner ℂ (ofRealLp (hwn n)) k) atTop (𝓝 (inner ℂ (ofRealLp hw) k)) := by
  simp_rw [sa12x_inner_cplx]
  have hre : MemLp (fun x => (k x).re) 2 volume := (Lp.memLp k).re
  have him : MemLp (fun x => (k x).im) 2 volume := (Lp.memLp k).im
  have h1 := Complex.continuous_ofReal.tendsto _ |>.comp (hconv _ hre)
  have h2 := (Complex.continuous_ofReal.tendsto _ |>.comp (hconv _ him)).mul_const Complex.I
  exact h1.add h2

/-- The truncated weighted Fourier mass of a weak limit is at most `b²`. -/
theorem sa12x_weak_trunc (m : ℝ) {wn : ℕ → Euc d → ℝ} {w : Euc d → ℝ}
    (hwn : ∀ n, MemLp (wn n) 2 volume) (hw : MemLp w 2 volume)
    (hconv : ∀ ψ : Euc d → ℝ, MemLp ψ 2 volume →
      Tendsto (fun n => ∫ x, wn n x * ψ x) atTop (𝓝 (∫ x, w x * ψ x)))
    {b : ℝ} (hfreq : ∃ᶠ n in atTop, HRS.PDE.ToolboxRd.MemSobolev m (wn n) ∧ HRS.PDE.ToolboxRd.sobolevNormSq m (wn n) ≤ b ^ 2)
    (R : ℝ) :
    Integrable (fun ξ => (Metric.closedBall (0 : Euc d) R).indicator
      (fun ξ => wt ξ ^ m * ‖fourierL2 w ξ‖ ^ 2) ξ) volume ∧
    ∫ ξ, (Metric.closedBall (0 : Euc d) R).indicator (fun ξ => wt ξ ^ m * ‖fourierL2 w ξ‖ ^ 2) ξ
      ≤ b ^ 2 := by
  set g : Euc d → ℂ := fourierL2 w with hgdef
  have hg2 : MemLp g 2 volume := memLp_fourierL2 hw
  set c : Euc d → ℝ := (Metric.closedBall (0 : Euc d) R).indicator (fun ξ => wt ξ ^ m) with hc
  have hcm : Measurable c := (continuous_wt_rpow m).measurable.indicator measurableSet_closedBall
  have hc0 : ∀ ξ, 0 ≤ c ξ := fun ξ => by
    by_cases h : ξ ∈ Metric.closedBall (0 : Euc d) R
    · rw [hc, Set.indicator_of_mem h]; exact (Real.rpow_pos_of_pos (wt_pos ξ) _).le
    · rw [hc, Set.indicator_of_notMem h]
  have hcle : ∀ ξ, c ξ ≤ wt ξ ^ m := fun ξ => by
    by_cases h : ξ ∈ Metric.closedBall (0 : Euc d) R
    · rw [hc, Set.indicator_of_mem h]
    · rw [hc, Set.indicator_of_notMem h]; exact (Real.rpow_pos_of_pos (wt_pos ξ) _).le
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Euc d) R).exists_bound_of_continuousOn
    (continuous_wt_rpow m).continuousOn
  have hcC : ∀ ξ, ‖c ξ‖ ≤ max C 0 := fun ξ => by
    by_cases h : ξ ∈ Metric.closedBall (0 : Euc d) R
    · rw [hc, Set.indicator_of_mem h]; exact (hC ξ h).trans (le_max_left _ _)
    · rw [hc, Set.indicator_of_notMem h]; simp
  have hR : MemLp (fun ξ => ((c ξ : ℝ) : ℂ) * g ξ) 2 volume := by
    refine hg2.of_le_mul (c := max C 0)
      ((Complex.measurable_ofReal.comp hcm).aestronglyMeasurable.mul hg2.aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun ξ => ?_
    rw [norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_right (hcC ξ) (norm_nonneg _)
  set H : Lp (α := Euc d) ℂ 2 := hR.toLp _ with hH
  set k : Lp (α := Euc d) ℂ 2 := (FT d).symm H with hk
  have hFTk : FT d k = H := (FT d).apply_symm_apply H
  have hΦn : ∀ n, inner ℂ (FT d (ofRealLp (hwn n))) H = inner ℂ (ofRealLp (hwn n)) k := by
    intro n; rw [← hFTk, inner_FT]
  have hΦ : inner ℂ (FT d (ofRealLp hw)) H = inner ℂ (ofRealLp hw) k := by
    rw [← hFTk, inner_FT]
  have hlim : Tendsto (fun n => inner ℂ (FT d (ofRealLp (hwn n))) H) atTop
      (𝓝 (inner ℂ (FT d (ofRealLp hw)) H)) := by
    simp_rw [hΦn, hΦ]
    exact sa12x_weak_cplx hwn hw hconv k
  -- the value of the limit
  set P : ℝ := ∫ ξ, c ξ * ‖g ξ‖ ^ 2 with hP
  have hPeq : ∫ ξ, (Metric.closedBall (0 : Euc d) R).indicator
      (fun ξ => wt ξ ^ m * ‖fourierL2 w ξ‖ ^ 2) ξ = P := by
    rw [hP]; refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    by_cases h : ξ ∈ Metric.closedBall (0 : Euc d) R
    · simp [hc, Set.indicator_of_mem h, hgdef]
    · simp [hc, Set.indicator_of_notMem h]
  have hcg_int : Integrable (fun ξ => c ξ * ‖g ξ‖ ^ 2) volume := by
    refine Integrable.bdd_mul (c := max C 0) hg2.norm.integrable_sq ?_ ?_
    · exact hcm.aestronglyMeasurable
    · exact Filter.Eventually.of_forall hcC
  have hind : (fun ξ => (Metric.closedBall (0 : Euc d) R).indicator
      (fun ξ => wt ξ ^ m * ‖fourierL2 w ξ‖ ^ 2) ξ) = fun ξ => c ξ * ‖g ξ‖ ^ 2 := by
    funext ξ
    by_cases h : ξ ∈ Metric.closedBall (0 : Euc d) R
    · simp [hc, Set.indicator_of_mem h, hgdef]
    · simp [hc, Set.indicator_of_notMem h]
  refine And.intro (by rw [hind]; exact hcg_int) ?_
  rw [hPeq]
  have hlimval : inner ℂ (FT d (ofRealLp hw)) H = ((P : ℝ) : ℂ) := by
    rw [MeasureTheory.L2.inner_def, hP, ← integral_complex_ofReal (μ := volume)]
    refine integral_congr_ae ?_
    filter_upwards [hR.coeFn_toLp] with ξ hξ
    rw [fourierL2_eq hw] at hgdef
    have h1 : ((FT d (ofRealLp hw) : Lp (α := Euc d) ℂ 2) ξ) = g ξ := by rw [hgdef]
    simp only [RCLike.inner_apply]
    rw [hH, hξ, h1]
    rw [show ((c ξ : ℝ) : ℂ) * g ξ * conj (g ξ) = ((c ξ : ℝ) : ℂ) * (g ξ * conj (g ξ)) by ring,
      Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast; ring
  have hmem : ∃ᶠ n in atTop, ‖inner ℂ (FT d (ofRealLp (hwn n))) H‖ ≤ (b ^ 2 + P) / 2 := by
    refine hfreq.mono fun n hn => ?_
    set gn : Euc d → ℂ := fourierL2 (wn n) with hgn
    have hgn' : (FT d (ofRealLp (hwn n)) : Euc d → ℂ) = gn := (fourierL2_eq (hwn n)).symm
    have hQ : ∫ ξ, wt ξ ^ m * ‖gn ξ‖ ^ 2 = HRS.PDE.ToolboxRd.sobolevNormSq m (wn n) := rfl
    have hI2 : Integrable (fun ξ => wt ξ ^ m * ‖gn ξ‖ ^ 2) volume := hn.1.2
    have hBint : Integrable (fun ξ => (c ξ * ‖g ξ‖ ^ 2 + wt ξ ^ m * ‖gn ξ‖ ^ 2) / 2) volume :=
      (hcg_int.add hI2).div_const 2
    rw [MeasureTheory.L2.inner_def]
    refine (norm_integral_le_of_norm_le hBint ?_).trans ?_
    · filter_upwards [hR.coeFn_toLp] with ξ hξ
      rw [hgn']
      simp only [RCLike.inner_apply]
      rw [hH, hξ, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg (hc0 ξ)]
      have h1 := hc0 ξ
      have h2 := hcle ξ
      have h3 : 0 ≤ wt ξ ^ m := (Real.rpow_pos_of_pos (wt_pos ξ) _).le
      nlinarith [mul_nonneg h1 (sq_nonneg (‖g ξ‖ - ‖gn ξ‖)), mul_nonneg (sub_nonneg.2 h2) (sq_nonneg ‖gn ξ‖)]
    · rw [integral_div, integral_add hcg_int hI2, hQ]
      have := hn.2
      rw [← hP]
      linarith
  have hclosed : IsClosed {z : ℂ | ‖z‖ ≤ (b ^ 2 + P) / 2} := isClosed_le continuous_norm continuous_const
  have := hclosed.mem_of_frequently_of_tendsto hmem hlim
  simp only [Set.mem_ofPred_eq, hlimval, Complex.norm_real] at this
  have hP0 : 0 ≤ P := integral_nonneg fun ξ => mul_nonneg (hc0 ξ) (sq_nonneg _)
  rw [Real.norm_of_nonneg hP0] at this
  linarith

theorem sa12x_weak_lsc (m : ℝ) {wn : ℕ → Euc d → ℝ} {w : Euc d → ℝ}
    (hwn : ∀ n, MemLp (wn n) 2 volume) (hw : MemLp w 2 volume)
    (hconv : ∀ ψ : Euc d → ℝ, MemLp ψ 2 volume →
      Tendsto (fun n => ∫ x, wn n x * ψ x) atTop (𝓝 (∫ x, w x * ψ x)))
    {b : ℝ} (hfreq : ∃ᶠ n in atTop, HRS.PDE.ToolboxRd.MemSobolev m (wn n) ∧
      HRS.PDE.ToolboxRd.sobolevNormSq m (wn n) ≤ b ^ 2) :
    HRS.PDE.ToolboxRd.MemSobolev m w ∧ HRS.PDE.ToolboxRd.sobolevNormSq m w ≤ b ^ 2 := by
  set F : Euc d → ℝ := fun ξ => wt ξ ^ m * ‖fourierL2 w ξ‖ ^ 2 with hF
  have hF0 : ∀ ξ, 0 ≤ F ξ := fun ξ => by
    have := wt_pos (d := d) ξ; positivity
  have hFm : AEStronglyMeasurable F volume := aesm_wt_mul (aestronglyMeasurable_fourierL2 hw) m
  have hk : ∀ k : ℕ, Integrable ((Metric.closedBall (0 : Euc d) (k : ℝ)).indicator F) volume ∧
      ∫ ξ, (Metric.closedBall (0 : Euc d) (k : ℝ)).indicator F ξ ≤ b ^ 2 :=
    fun k => sa12x_weak_trunc m hwn hw hconv hfreq (k : ℝ)
  have hlint : ∫⁻ ξ, ENNReal.ofReal (F ξ) ≤ ENNReal.ofReal (b ^ 2) := by
    have hmono : Monotone fun (k : ℕ) ξ => ENNReal.ofReal
        ((Metric.closedBall (0 : Euc d) (k : ℝ)).indicator F ξ) := by
      intro j k hjk ξ
      refine ENNReal.ofReal_le_ofReal ?_
      refine Set.indicator_le_indicator_of_subset (Metric.closedBall_subset_closedBall
        (by exact_mod_cast hjk)) (fun ξ => hF0 ξ) ξ
    have hsup : (fun ξ => ENNReal.ofReal (F ξ)) = fun ξ => ⨆ k : ℕ, ENNReal.ofReal
        ((Metric.closedBall (0 : Euc d) (k : ℝ)).indicator F ξ) := by
      funext ξ
      apply le_antisymm
      · obtain ⟨k, hk'⟩ := exists_nat_ge ‖ξ‖
        refine le_trans ?_ (le_iSup _ k)
        rw [Set.indicator_of_mem (by simpa using hk')]
      · refine iSup_le fun k => ENNReal.ofReal_le_ofReal ?_
        exact Set.indicator_le_self' (fun ξ _ => hF0 ξ) ξ
    rw [hsup, lintegral_iSup' (fun k => ((hFm.aemeasurable.indicator
      measurableSet_closedBall).ennreal_ofReal))
      (Filter.Eventually.of_forall fun ξ => fun j k hjk => hmono hjk ξ)]
    refine iSup_le fun k => ?_
    rw [← ofReal_integral_eq_lintegral_ofReal (hk k).1
      (Filter.Eventually.of_forall fun ξ => Set.indicator_nonneg (fun ξ _ => hF0 ξ) ξ)]
    exact ENNReal.ofReal_le_ofReal (hk k).2
  have hint : Integrable F volume := by
    refine ⟨hFm, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hF0)]
    exact hlint.trans_lt ENNReal.ofReal_lt_top
  refine ⟨⟨hw, hint⟩, ?_⟩
  show ∫ ξ, F ξ ≤ b ^ 2
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hF0) hFm]
  exact ENNReal.toReal_le_of_le_ofReal (sq_nonneg b) hlint

end HRS.MH.AdjointRd.Phase2SA12Limit
