import HRS.MS.SA12K7

/-!
# S.A.12 C1, time regularity of the mollified periodic density

`PeriodicTimeSmooth T (τ ↦ η * μ0^τ)` for `μ0^τ = perL L (Z_τ⁻¹ ζ_L ρ(τ))`, from the joint continuity of `ρ`
(weak continuity plus bounds, `sa12k_joint_jets`) and the kernel form of the mollification.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
open HRS.MS.ToriCoefA HRS.MS.ToriCoefB

variable {d : ℕ}

/-- The value of a jointly continuous jet at order zero. -/
theorem sa12k_joint_val {s : ℝ} {m : ℕ} {Λ T : ℝ} {ρ : ℝ → Euc d → ℝ} (hρ : CoeffHypRd s m Λ T ρ) :
    ContinuousOn (fun p : ℝ × Euc d => ρ p.1 p.2) (Icc (0 : ℝ) T ×ˢ univ) := by
  have h := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => Euc d) ℝ
    (fun i => i.elim0)).continuous.comp_continuousOn (sa12k_joint_jets hρ 0 (by omega))
  refine h.congr fun p _ => ?_
  simp [iteratedFDeriv_zero_apply]

/-- Joint continuity of the parameter integral against a compactly supported continuous kernel. -/
theorem sa12k_kconv_joint2 {T : ℝ} {f : ℝ → Euc d → ℝ}
    (hfc : ContinuousOn (fun p : ℝ × Euc d => f p.1 p.2) (Icc (0 : ℝ) T ×ˢ univ)) {B : ℝ}
    (hB : ∀ τ ∈ Icc (0 : ℝ) T, ∀ y, |f τ y| ≤ B)
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V] {κ : Euc d → V}
    (hκ : Continuous κ) (hc : HasCompactSupport κ) :
    ContinuousOn (fun p : ℝ × Euc d => sa12k_kconv (f p.1) κ p.2) (Icc (0 : ℝ) T ×ˢ univ) := by
  intro q₀ hq₀
  obtain ⟨R₀, hR₀⟩ := hc.isCompact.isBounded.subset_closedBall (0 : Euc d)
  obtain ⟨Bκ, hBκ⟩ := hc.exists_bound_of_continuous hκ
  have hKc : IsCompact (Metric.closedBall q₀.2 (1 + R₀)) := isCompact_closedBall _ _
  have hint : Integrable (fun y => (Metric.closedBall q₀.2 (1 + R₀)).indicator
      (fun _ => B * Bκ) y) := by
    rw [integrable_indicator_iff hKc.measurableSet]
    exact continuousOn_const.integrableOn_compact hKc
  refine continuousWithinAt_of_dominated (μ := (volume : Measure (Euc d)))
    (F := fun (p : ℝ × Euc d) (y : Euc d) => f p.1 y • κ (p.2 - y))
    (bound := fun y => (Metric.closedBall q₀.2 (1 + R₀)).indicator (fun _ => B * Bκ) y) ?_ ?_ hint ?_
  · -- measurability
    have hmem : Icc (0 : ℝ) T ×ˢ (univ : Set (Euc d)) ∈ 𝓝[Icc (0 : ℝ) T ×ˢ univ] q₀ := self_mem_nhdsWithin
    filter_upwards [hmem] with p hp
    -- `f p.1` is continuous because it is continuous in the second variable
    have hfy : Continuous (f p.1) := by
      have h1 : ContinuousOn (fun y : Euc d => f p.1 y) univ := by
        exact hfc.comp (f := fun y : Euc d => (p.1, y))
          (continuous_const.prodMk continuous_id).continuousOn (fun y _ => ⟨hp.1, mem_univ y⟩)
      exact continuousOn_univ.1 h1
    exact (hfy.smul (hκ.comp (continuous_const.sub continuous_id))).aestronglyMeasurable
  · -- the bound
    have h1 : ∀ᶠ p : ℝ × Euc d in 𝓝[Icc (0 : ℝ) T ×ˢ univ] q₀, p ∈ Icc (0 : ℝ) T ×ˢ (univ : Set (Euc d)) :=
      self_mem_nhdsWithin
    have h2 : ∀ᶠ p : ℝ × Euc d in 𝓝[Icc (0 : ℝ) T ×ˢ univ] q₀, ‖p.2 - q₀.2‖ < 1 := by
      have : Tendsto (fun p : ℝ × Euc d => p.2) (𝓝[Icc (0 : ℝ) T ×ˢ univ] q₀) (𝓝 q₀.2) :=
        (continuous_snd.tendsto q₀).mono_left nhdsWithin_le_nhds
      have := this.eventually (Metric.ball_mem_nhds q₀.2 one_pos)
      filter_upwards [this] with p hp
      simpa [Metric.mem_ball, dist_eq_norm] using hp
    have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB q₀.1 hq₀.1 0)
    have hBκ0 : 0 ≤ Bκ := (norm_nonneg _).trans (hBκ 0)
    filter_upwards [h1, h2] with p hp hp2
    refine Filter.Eventually.of_forall fun y => ?_
    show ‖f p.1 y • κ (p.2 - y)‖ ≤ _
    by_cases hy : y ∈ Metric.closedBall q₀.2 (1 + R₀)
    · rw [Set.indicator_of_mem hy, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (hB p.1 hp.1 y) (hBκ _) (norm_nonneg _) hB0
    · rw [Set.indicator_of_notMem hy]
      have : κ (p.2 - y) = 0 := by
        by_contra hne
        apply hy
        have hmem : p.2 - y ∈ tsupport κ := subset_tsupport _ hne
        have h3 := hR₀ hmem
        rw [Metric.mem_closedBall, dist_zero_right] at h3
        rw [Metric.mem_closedBall, dist_eq_norm]
        calc ‖y - q₀.2‖ = ‖(p.2 - q₀.2) - (p.2 - y)‖ := by congr 1; abel
          _ ≤ ‖p.2 - q₀.2‖ + ‖p.2 - y‖ := norm_sub_le _ _
          _ ≤ 1 + R₀ := by linarith
      rw [this]; simp
  · refine Filter.Eventually.of_forall fun y => ?_
    have h1 : ContinuousOn (fun p : ℝ × Euc d => f p.1 y) (Icc (0 : ℝ) T ×ˢ univ) :=
      hfc.comp (f := fun p : ℝ × Euc d => (p.1, y))
        (continuous_fst.prodMk continuous_const).continuousOn (fun p hp => ⟨hp.1, mem_univ y⟩)
    exact (h1.continuousWithinAt hq₀).smul
      ((hκ.comp (continuous_snd.sub continuous_const)).continuousWithinAt)

/-- Joint continuity of `Z_τ⁻¹ ζ_L ρ(τ)`. -/
theorem sa12k_f0_joint {s : ℝ} {m : ℕ} {Λ T : ℝ} {ρ : ℝ → Euc d → ℝ} (hρ : CoeffHypRd s m Λ T ρ)
    {ζ : Euc d → ℝ} (hζ : IsCutoffRad (1 / 4) (1 / 3) ζ) (L : ℝ)
    (hZ : ∀ τ ∈ Icc (0 : ℝ) T, 1 / 2 ≤ ∫ y, ζ (L⁻¹ • y) * ρ τ y) :
    ContinuousOn (fun p : ℝ × Euc d => sa12k_f0 ζ (ρ p.1) L p.2) (Icc (0 : ℝ) T ×ˢ univ) := by
  have hZc : ContinuousOn (fun τ => ∫ y, ζ (L⁻¹ • y) * ρ τ y) (Icc (0 : ℝ) T) := by
    have hcont : Continuous (fun y : Euc d => ζ (L⁻¹ • y)) :=
      hζ.1.continuous.comp (continuous_const_smul _)
    refine hρ.cont (fun y => ζ (L⁻¹ • y)) hcont ⟨1, fun x => ?_⟩
    have hz := hζ.2.2.2.1 (L⁻¹ • x)
    rw [abs_of_nonneg hz.1]; exact hz.2
  have hZc' : ContinuousOn (fun p : ℝ × Euc d => (∫ y, ζ (L⁻¹ • y) * ρ p.1 y)⁻¹)
      (Icc (0 : ℝ) T ×ˢ univ) := by
    have h1 : ContinuousOn (fun p : ℝ × Euc d => ∫ y, ζ (L⁻¹ • y) * ρ p.1 y)
        (Icc (0 : ℝ) T ×ˢ univ) := hZc.comp continuous_fst.continuousOn (fun p hp => hp.1)
    exact h1.inv₀ fun p hp => by have := hZ p.1 hp.1; linarith
  have hρv := sa12k_joint_val hρ
  have hζc : Continuous (fun p : ℝ × Euc d => ζ (L⁻¹ • p.2)) :=
    hζ.1.continuous.comp (continuous_const_smul _ |>.comp continuous_snd)
  exact hZc'.mul (hζc.continuousOn.mul hρv)

/-- Joint continuity of `μ0^τ = perL L f0^τ`. -/
theorem sa12k_mu0_joint {s : ℝ} {m : ℕ} {Λ T : ℝ} {ρ : ℝ → Euc d → ℝ} (hρ : CoeffHypRd s m Λ T ρ)
    {ζ : Euc d → ℝ} (hζ : IsCutoffRad (1 / 4) (1 / 3) ζ) {L : ℝ} (hL : 0 < L)
    (hZ : ∀ τ ∈ Icc (0 : ℝ) T, 1 / 2 ≤ ∫ y, ζ (L⁻¹ • y) * ρ τ y)
    (hv : ∀ τ ∈ Icc (0 : ℝ) T, ∀ y : Euc d, L / 3 ≤ ‖y‖ → sa12k_f0 ζ (ρ τ) L y = 0) :
    ContinuousOn (fun p : ℝ × Euc d => sa12k_mu0 ζ (ρ p.1) L p.2) (Icc (0 : ℝ) T ×ˢ univ) := by
  have hf := sa12k_f0_joint hρ hζ L hZ
  intro q₀ hq₀
  obtain ⟨k, hk⟩ := tca_exists_U L hL q₀.2
  have hU : (Icc (0 : ℝ) T ×ˢ tca_U L k) ∈ 𝓝[Icc (0 : ℝ) T ×ˢ (univ : Set (Euc d))] q₀ := by
    refine mem_nhdsWithin.2 ⟨Set.univ ×ˢ tca_U L k, isOpen_univ.prod (tca_U_isOpen L k),
      ⟨mem_univ _, hk⟩, ?_⟩
    rintro p ⟨⟨-, hp2⟩, hp3⟩
    exact ⟨hp3.1, hp2⟩
  have hcont : ContinuousOn (fun p : ℝ × Euc d => sa12k_f0 ζ (ρ p.1) L (p.2 - L • latticePt k))
      (Icc (0 : ℝ) T ×ˢ tca_U L k) := by
    refine hf.comp (f := fun p : ℝ × Euc d => (p.1, p.2 - L • latticePt k))
      (continuous_fst.prodMk (continuous_snd.sub continuous_const)).continuousOn ?_
    exact fun p hp => ⟨hp.1, mem_univ _⟩
  have hcw := hcont.continuousWithinAt (x := q₀) ⟨hq₀.1, hk⟩
  refine ContinuousWithinAt.mono_of_mem_nhdsWithin ?_ hU
  refine hcw.congr (fun p hp => ?_) ?_
  · exact tca_perL_eq_on L hL _ (hv p.1 hp.1) k p.2 hp.2
  · exact tca_perL_eq_on L hL _ (hv q₀.1 hq₀.1) k q₀.2 hk

/-- `PeriodicTimeSmooth` of the mollified density. -/
theorem sa12k_timeSmooth {s : ℝ} {m : ℕ} {Λ T : ℝ} {ρ : ℝ → Euc d → ℝ} (hρ : CoeffHypRd s m Λ T ρ)
    {ζ : Euc d → ℝ} (hζ : IsCutoffRad (1 / 4) (1 / 3) ζ) {L : ℝ} (hL : 0 < L)
    (hZ : ∀ τ ∈ Icc (0 : ℝ) T, 1 / 2 ≤ ∫ y, ζ (L⁻¹ • y) * ρ τ y)
    (hv : ∀ τ ∈ Icc (0 : ℝ) T, ∀ y : Euc d, L / 3 ≤ ‖y‖ → sa12k_f0 ζ (ρ τ) L y = 0)
    (hcont : ∀ τ ∈ Icc (0 : ℝ) T, Continuous (sa12k_mu0 ζ (ρ τ) L))
    {B : ℝ} (hB : ∀ τ ∈ Icc (0 : ℝ) T, ∀ y, |sa12k_mu0 ζ (ρ τ) L y| ≤ B)
    {δ : ℝ} {η : Euc d → ℝ} (hη : SA12KMoll δ η) :
    PeriodicTimeSmooth T (fun τ => sa12k_moll η (sa12k_mu0 ζ (ρ τ) L)) := by
  intro j
  have hmu := sa12k_mu0_joint hρ hζ hL hZ hv
  have hk := sa12k_kconv_joint2 hmu hB
    (hη.smooth.continuous_iteratedFDeriv (by exact_mod_cast le_top) :
      Continuous (iteratedFDeriv ℝ j η)) (hη.compact.iteratedFDeriv j)
  refine hk.congr fun q hq => ?_
  have h1 := sa12k_kconv_iter (hcont q.1 hq.1) hη.smooth hη.compact j
  show iteratedFDeriv ℝ j (sa12k_moll η (sa12k_mu0 ζ (ρ q.1) L)) q.2 = _
  rw [sa12k_moll_eq_kconv]
  exact congrFun h1 q.2

end HRS.MH.AdjointRd.Phase2SA12Construction
