import HRS.MS.SA12NearN6B
import HRS.MS.Ker1Aux4
import HRS.MP.RdGenAux
import HRS.MS.SA12CompB4A

/-!
# S.A.12 N6, part C: Cauchy-Schwarz on the support ball and the bound for one derivative of the convolution
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

theorem sa12n_cs {F : Euc d → ℝ} (hF : Continuous F) (c : Euc d) (ρ : ℝ) :
    ENNReal.ofReal (∫ y in Metric.closedBall c ρ, |F y|) ≤
      eLpNorm ((Metric.closedBall c ρ).indicator F) 2 volume *
        ENNReal.ofReal ((volume (Metric.closedBall (0 : Euc d) ρ)).toReal ^ (1 / 2 : ℝ)) := by
  set μ' : Measure (Euc d) := volume.restrict (Metric.closedBall c ρ) with hμ'
  haveI : IsFiniteMeasure μ' := ⟨by rw [hμ', Measure.restrict_apply_univ]; exact measure_closedBall_lt_top⟩
  have hint : Integrable F μ' := hF.locallyIntegrable.integrableOn_isCompact (isCompact_closedBall c ρ)
  have h1 : ENNReal.ofReal (∫ y in Metric.closedBall c ρ, |F y|) = eLpNorm F 1 μ' := by
    rw [eLpNorm_one_eq_lintegral_enorm hint.aestronglyMeasurable, ← ofReal_integral_norm_eq_lintegral_enorm hint]
    simp [Real.norm_eq_abs, hμ']
  have h2 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ') (p := 1) (q := 2)
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) hint.aestronglyMeasurable
  rw [← h1] at h2
  refine h2.trans ?_
  rw [hμ', ← eLpNorm_indicator_eq_eLpNorm_restrict Metric.isClosed_closedBall.measurableSet]
  refine mul_le_mul' le_rfl (le_of_eq ?_)
  rw [Measure.restrict_apply_univ, Measure.addHaar_closedBall_center]
  have hV : volume (Metric.closedBall (0 : Euc d) ρ) ≠ ⊤ := measure_closedBall_lt_top.ne
  rw [← ENNReal.ofReal_toReal hV, ENNReal.toReal_ofReal ENNReal.toReal_nonneg,
    ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num)]
  norm_num

/-- `|∂^idx f(z)| ≤ ‖D^k f(z)‖`. -/
theorem sa12n_pd_le {f : Euc d → ℝ} {k : ℕ} (idx : Fin k → Fin d) (z : Euc d) :
    |partialDeriv idx f z| ≤ ‖iteratedFDeriv ℝ k f z‖ := by
  unfold partialDeriv
  have := (iteratedFDeriv ℝ k f z).le_opNorm (fun l => EuclideanSpace.single (idx l) (1 : ℝ))
  simpa [Real.norm_eq_abs] using this

theorem sa12n_pd_contDiff {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) {k : ℕ} (idx : Fin k → Fin d) :
    ContDiff ℝ ∞ (partialDeriv idx f) :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Euc d) ℝ
    (fun l => EuclideanSpace.single (idx l) (1 : ℝ))).contDiff.comp (hf.iteratedFDeriv_right (by simp))

theorem sa12n_pd_eventually {f g : Euc d → ℝ} {z : Euc d} (hfg : f =ᶠ[𝓝 z] g) {k : ℕ}
    (idx : Fin k → Fin d) : partialDeriv idx f z = partialDeriv idx g z := by
  unfold partialDeriv
  rw [(hfg.iteratedFDeriv ℝ k).eq_of_nhds]

/-- One partial derivative of order `j+1` of the convolution of the Riesz kernel with a coefficient supported
away from the evaluation point, bounded through one integration by parts. -/
theorem sa12n_term_bound (hd : 1 ≤ d) (s : ℝ) {m : ℕ} {h BB ρ : ℝ} (hh : 0 < h) (hρ0 : 0 ≤ ρ)
    (hBB : 0 ≤ BB)
    (hker : ∀ n : ℕ, 1 ≤ n → n ≤ m + 2 → ∀ z : Euc d, h ≤ ‖z‖ →
      ‖iteratedFDeriv ℝ n (rieszKernel d s) z‖ ≤ BB)
    {a F : Euc d → ℝ} (ha : MemCb 1 a) (hF : ContDiff ℝ ∞ F) {c : Euc d}
    (hts : tsupport a ⊆ Metric.closedBall c ρ) {x : Euc d}
    (hsep : ∀ y ∈ tsupport a, h ≤ ‖x - y‖) (i j' : Fin d) (j : ℕ) (hj : j ≤ m) :
    ContDiffAt ℝ ∞ (fun x' => fderiv ℝ (fun x'' => ∫ y, rieszKernel d s (x'' - y) *
        (a y * fderiv ℝ F y (EuclideanSpace.single j' (1 : ℝ)))) x'
        (EuclideanSpace.single i (1 : ℝ))) x ∧
    ‖iteratedFDeriv ℝ j (fun x' => fderiv ℝ (fun x'' => ∫ y, rieszKernel d s (x'' - y) *
        (a y * fderiv ℝ F y (EuclideanSpace.single j' (1 : ℝ)))) x'
        (EuclideanSpace.single i (1 : ℝ))) x‖ ≤
      (d : ℝ) ^ j * (cbNorm 1 a * (BB + BB) * ∫ y in Metric.closedBall c ρ, |F y|) := by
  set R : ℝ := ‖x - c‖ + ρ + h with hR
  have hRpos : 0 < R := by positivity
  obtain ⟨Gh, hGh, hGhc, hGheq⟩ := sa12n_cutoff_kernel (d := d) s hh hRpos
  set e' : Euc d := EuclideanSpace.single j' (1 : ℝ) with he'
  set v : Euc d → ℝ := fun y => a y * fderiv ℝ F y e' with hv
  have hvc : Continuous v :=
    ha.1.continuous.mul ((hF.of_le (by exact_mod_cast le_top) : ContDiff ℝ 1 F).continuous_fderiv
      one_ne_zero |>.clm_apply continuous_const)
  obtain ⟨hΨ, hpart⟩ := sa12n_conv_partial hvc.locallyIntegrable hGh hGhc
  set Ψ : Euc d → ℝ := sa12n_conv v Gh with hΨdef
  set Φ : Euc d → ℝ := fun x'' => ∫ y, rieszKernel d s (x'' - y) * v y with hΦ
  -- geometry on the support of `a`
  have hgeo : ∀ y ∈ tsupport a, ∀ x' : Euc d, ‖x' - x‖ < h / 2 →
      h / 2 < ‖x' - y‖ ∧ ‖x' - y‖ < R := by
    intro y hy x' hx'
    have h1 := hsep y hy
    have h2 : ‖x - y‖ ≤ ‖x' - y‖ + ‖x' - x‖ := by
      calc ‖x - y‖ = ‖(x' - y) - (x' - x)‖ := by congr 1; abel
        _ ≤ _ := norm_sub_le _ _
    have h3 : ‖x' - y‖ ≤ ‖x' - x‖ + ‖x - c‖ + ‖c - y‖ := by
      calc ‖x' - y‖ = ‖(x' - x) + (x - c) + (c - y)‖ := by congr 1; abel
        _ ≤ ‖(x' - x) + (x - c)‖ + ‖c - y‖ := norm_add_le _ _
        _ ≤ _ := by gcongr; exact norm_add_le _ _
    have h4 : ‖c - y‖ ≤ ρ := by
      have := Metric.mem_closedBall.1 (hts hy)
      rw [dist_eq_norm, norm_sub_rev] at this
      exact this
    constructor <;> linarith
  have hΦΨ : ∀ x' : Euc d, ‖x' - x‖ < h / 2 → Φ x' = Ψ x' := by
    intro x' hx'
    simp only [hΦ, hΨdef, sa12n_conv]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    by_cases hy : a y = 0
    · simp [hv, hy]
    · have hyt : y ∈ tsupport a := subset_tsupport _ (Function.mem_support.2 hy)
      obtain ⟨hg1, hg2⟩ := hgeo y hyt x' hx'
      have := (hGheq (x' - y) hg1 hg2).eq_of_nhds
      beta_reduce
      rw [this]; ring
  have hΦΨ' : ∀ x' : Euc d, ‖x' - x‖ < h / 2 → fderiv ℝ Φ x' = fderiv ℝ Ψ x' := by
    intro x' hx'
    refine Filter.EventuallyEq.fderiv_eq ?_
    filter_upwards [(Metric.isOpen_ball (x := x) (ε := h / 2)).mem_nhds
      (show x' ∈ Metric.ball x (h / 2) by rw [Metric.mem_ball, dist_eq_norm]; exact hx')] with w hw
    exact hΦΨ w (by have := Metric.mem_ball.1 hw; rwa [dist_eq_norm] at this)
  have hT : (fun x' => fderiv ℝ Φ x' (EuclideanSpace.single i (1 : ℝ))) =ᶠ[𝓝 x]
      fun x' => fderiv ℝ Ψ x' (EuclideanSpace.single i (1 : ℝ)) := by
    filter_upwards [Metric.ball_mem_nhds x (show 0 < h / 2 by positivity)] with w hw
    have := Metric.mem_ball.1 hw
    rw [dist_eq_norm] at this
    rw [hΦΨ' w this]
  have hsm : ContDiffAt ℝ ∞ (fun x' => fderiv ℝ Ψ x' (EuclideanSpace.single i (1 : ℝ))) x :=
    ((hΨ.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const).contDiffAt
  refine ⟨hsm.congr_of_eventuallyEq hT, ?_⟩
  show ‖iteratedFDeriv ℝ j (fun x' => fderiv ℝ Φ x' (EuclideanSpace.single i (1 : ℝ))) x‖ ≤ _
  rw [(hT.iteratedFDeriv ℝ j).eq_of_nhds]
  -- bound by the partial derivatives
  have hcb := HRS.MH.AdjointRd.Phase2SA12Companions.sa12z_cb_nonneg ha
  set I : ℝ := ∫ y in Metric.closedBall c ρ, |F y| with hI
  have hI0 : 0 ≤ I := setIntegral_nonneg Metric.isClosed_closedBall.measurableSet (fun _ _ => abs_nonneg _)
  have hK0 : 0 ≤ cbNorm 1 a * (BB + BB) * I := by positivity
  have hzgeo : ∀ y ∈ tsupport a, h / 2 < ‖x - y‖ ∧ ‖x - y‖ < R := by
    intro y hy
    have := hgeo y hy x (by simp; positivity)
    exact this
  have hbound : ∀ idx : Fin j → Fin d,
      |iteratedFDeriv ℝ j (fun x' => fderiv ℝ Ψ x' (EuclideanSpace.single i (1 : ℝ))) x
        (fun l => EuclideanSpace.single (idx l) (1 : ℝ))| ≤ cbNorm 1 a * (BB + BB) * I := by
    intro idx
    have e1 : iteratedFDeriv ℝ j (fun x' => fderiv ℝ Ψ x' (EuclideanSpace.single i (1 : ℝ))) x
        (fun l => EuclideanSpace.single (idx l) (1 : ℝ)) =
        partialDeriv idx (fun x' => fderiv ℝ Ψ x' (EuclideanSpace.single i (1 : ℝ))) x := rfl
    rw [e1, ← sa12n_pd_snoc hΨ i idx x, hpart]
    refine sa12n_conv_ibp_bound ha hF (sa12n_pd_contDiff hGh _) hts j' x hBB hBB ?_ ?_
    · intro y hy
      obtain ⟨g1, g2⟩ := hzgeo y hy
      rw [sa12n_pd_eventually (hGheq (x - y) g1 g2)]
      exact (sa12n_pd_le _ _).trans (hker (j + 1) (by omega) (by omega) _ (hsep y hy))
    · intro y hy
      obtain ⟨g1, g2⟩ := hzgeo y hy
      have hc := sa12n_pd_cons hGh (Fin.snoc idx i : Fin (j + 1) → Fin d) j' (x - y)
      rw [← hc, sa12n_pd_eventually (hGheq (x - y) g1 g2)]
      exact (sa12n_pd_le _ _).trans (hker (j + 1 + 1) (by omega) (by omega) _ (hsep y hy))
  exact HRS.MP.RdGen.rg_norm_le_of_partial hd _ hbound

end HRS.MH.AdjointRd.Phase2SA12Near
