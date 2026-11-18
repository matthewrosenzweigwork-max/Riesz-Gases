import HRS.MH.AdjointRdDefs
import HRS.MS.SA12BuildC20
import HRS.MS.UniqT3

/-!
# S.A.12 C21: near/far decomposition of the periodic nonlocal operator at a point
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd

variable {d : ℕ}

theorem sa12c21_cell_eq (L : ℝ) (c : Euc d) :
    {y : Euc d | y - c ∈ centeredBox d L} =
      {z : Euc d | ∀ i, (c - (L / 2) • (WithLp.toLp 2 fun _ : Fin d => (1 : ℝ)) : Euc d) i ≤ z i ∧
        z i < (c - (L / 2) • (WithLp.toLp 2 fun _ : Fin d => (1 : ℝ)) : Euc d) i + L} := by
  ext y
  simp only [Set.mem_setOf_eq, centeredBox, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  refine forall_congr' fun i => ?_
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem sa12c21_perConv_cell (L : ℝ) (hL : 0 < L) (γ g : Euc d → ℝ)
    (hγp : ∀ (x : Euc d) (k : Fin d → ℤ), γ (x + L • latticePt k) = γ x)
    (hgp : ∀ (x : Euc d) (k : Fin d → ℤ), g (x + L • latticePt k) = g x) (c x' : Euc d) :
    perConv L γ g x' = ∫ y in {y : Euc d | y - c ∈ centeredBox d L}, γ (x' - y) * g y := by
  set f : Euc d → ℝ := fun y => γ (x' - y) * g y with hf
  have hper : ∀ (y : Euc d) (k : Fin d → ℤ), f (y + L • latticePt k) = f y := by
    intro y k
    simp only [hf]
    have e1 : x' - (y + L • latticePt (d := d) k) = (x' - y) + L • latticePt (d := d) (-k) := by
      ext i; simp [latticePt]; ring
    rw [e1, hγp, hgp]
  rw [sa12c21_cell_eq]
  exact (sa12c20_cell_shift L hL hper _).symm

theorem sa12c21_norm_le {a : ℝ} (ha : 0 ≤ a) {w : Euc d} (hw : ∀ i, |w i| ≤ a) :
    ‖w‖ ≤ Real.sqrt (d * a ^ 2) := by
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt ?_
  calc ∑ i, ‖w i‖ ^ 2 ≤ ∑ _i : Fin d, a ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [Real.norm_eq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hw i) 2
    _ = d * a ^ 2 := by simp

theorem sa12c21_cell_bdd (L : ℝ) (hL : 0 < L) (c : Euc d) {y : Euc d}
    (hy : y - c ∈ centeredBox d L) : ‖y - c‖ ≤ Real.sqrt (d * L ^ 2) := by
  refine sa12c21_norm_le hL.le fun i => ?_
  have := hy i
  rw [abs_le]
  constructor <;> linarith [this.1, this.2]

theorem sa12c21_measurable_cell (L : ℝ) (c : Euc d) :
    MeasurableSet {y : Euc d | y - c ∈ centeredBox d L} := by
  have : {y : Euc d | y - c ∈ centeredBox d L} = (fun y => y - c) ⁻¹' (centeredBox d L) := rfl
  rw [this]
  refine (measurable_sub_const c) ?_
  have hproj : ∀ i : Fin d, Measurable fun z : Euc d => z i := fun i =>
    (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.measurable
  have : centeredBox d L = ⋂ i, ({z : Euc d | -(L / 2) ≤ z i} ∩ {z : Euc d | z i < L / 2}) := by
    ext z; simp [centeredBox]
  rw [this]
  exact MeasurableSet.iInter fun i =>
    (measurableSet_le measurable_const (hproj i)).inter (measurableSet_lt (hproj i) measurable_const)

theorem sa12c21_integrableOn_sub {γ : Euc d → ℝ} (hγ : LocallyIntegrable γ volume) (x' : Euc d)
    {S : Set (Euc d)} (hS : Bornology.IsBounded S) :
    IntegrableOn (fun y => γ (x' - y)) S volume := by
  obtain ⟨B, hB⟩ := hS.subset_closedBall (0 : Euc d)
  have hpre : (fun y : Euc d => x' - y) ⁻¹' S ⊆ Metric.closedBall (0 : Euc d) (‖x'‖ + B) := by
    intro w hw
    have := hB hw
    rw [Metric.mem_closedBall, dist_zero_right] at this ⊢
    calc ‖w‖ = ‖x' - (x' - w)‖ := by congr 1; abel
      _ ≤ ‖x'‖ + ‖x' - w‖ := norm_sub_le _ _
      _ ≤ ‖x'‖ + B := by linarith
  have h1 : IntegrableOn γ ((fun y : Euc d => x' - y) ⁻¹' S) volume :=
    (hγ.integrableOn_isCompact (isCompact_closedBall (0 : Euc d) (‖x'‖ + B))).mono_set hpre
  have h2 := ((volume : Measure (Euc d)).measurePreserving_sub_left x').integrableOn_comp_preimage
    (MeasurableEquiv.subLeft x').measurableEmbedding (f := γ)
    (s := (fun y : Euc d => x' - y) ⁻¹' S)
  have hpre2 : (fun y : Euc d => x' - y) ⁻¹' ((fun y : Euc d => x' - y) ⁻¹' S) = S := by
    ext z; simp
  rw [hpre2] at h2
  exact h2.2 h1

theorem sa12c21_no_lattice {L R : ℝ} (hbox : 4 * R < L) (hR : 0 < R) {c x' y : Euc d}
    (hx' : ‖x' - c‖ < R) (hy : y - c ∈ centeredBox d L) {z : Fin d → ℤ}
    (h : x' - y = L • latticePt z) : z = 0 := by
  have hL : 0 < L := by linarith
  funext i
  have h1 : |(x' - c) i| ≤ ‖x' - c‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (x' - c) i
  have h2 := hy i
  have h3 : (x' - y) i = L * (z i : ℝ) := by
    have := congrArg (fun w : Euc d => w i) h
    simpa [latticePt] using this
  have h4 : (x' - y) i = (x' - c) i - (y - c) i := by simp
  have h5 : |L * (z i : ℝ)| < L := by
    rw [← h3, h4]
    refine lt_of_le_of_lt (abs_sub _ _) ?_
    have : |(y - c) i| ≤ L / 2 := by
      rw [abs_le]; constructor <;> linarith [h2.1, h2.2]
    linarith
  have h6 : |(z i : ℝ)| < 1 := by
    rw [abs_mul, abs_of_pos hL] at h5
    by_contra hcon
    push Not at hcon
    nlinarith
  have h7 : |z i| < 1 := by exact_mod_cast h6
  exact Int.abs_lt_one_iff.1 h7

/-- Differentiation of the far part under the integral sign (the kernel is differentiated). -/
theorem sa12c21_far_deriv {s L R h : ℝ} (hR : 0 < R) (hh : 0 < h) (hbox : 4 * R < L)
    {γ : Euc d → ℝ} (hγ : IsPeriodicRieszKernel d s L γ) {c x : Euc d}
    (hx : x ∈ Metric.ball c R) {η g : Euc d → ℝ} (hη1 : ∀ y ∈ Metric.ball x h, η y = 1)
    (hηc : Continuous η) (hgc : Continuous g) :
    HasFDerivAt (fun x' => ∫ y in {y : Euc d | y - c ∈ centeredBox d L},
        γ (x' - y) * ((1 - η y) * g y))
      (∫ y in {y : Euc d | y - c ∈ centeredBox d L},
        ((1 - η y) * g y) • fderiv ℝ γ (x - y)) x ∧
    Integrable (fun y => ((1 - η y) * g y) • fderiv ℝ γ (x - y))
      (volume.restrict {y : Euc d | y - c ∈ centeredBox d L}) := by
  have hL : 0 < L := by linarith
  set Cell : Set (Euc d) := {y : Euc d | y - c ∈ centeredBox d L} with hCell
  set μ : Measure (Euc d) := volume.restrict Cell with hμ
  set k : Euc d → ℝ := fun y => (1 - η y) * g y with hk
  have hkc : Continuous k := (continuous_const.sub hηc).mul hgc
  set Bc : ℝ := Real.sqrt (d * L ^ 2) with hBc
  have hCellb : Cell ⊆ Metric.closedBall c Bc := by
    intro y hy
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact sa12c21_cell_bdd L hL c hy
  have hCellbdd : Bornology.IsBounded Cell := Metric.isBounded_closedBall.subset hCellb
  haveI : IsFiniteMeasure μ := ⟨by rw [hμ, Measure.restrict_apply_univ]; exact hCellbdd.measure_lt_top⟩
  have hCellm : MeasurableSet Cell := sa12c21_measurable_cell L c
  obtain ⟨Kk, hKk⟩ := (isCompact_closedBall c Bc).exists_bound_of_continuousOn hkc.continuousOn
  have hkb : ∀ y ∈ Cell, |k y| ≤ max Kk 0 := fun y hy => by
    have := hKk y (hCellb hy)
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  -- geometry
  set r : ℝ := min (h / 2) (R - ‖x - c‖) with hr
  have hrpos : 0 < r := by
    refine lt_min (by linarith) ?_
    have := hx; rw [Metric.mem_ball, dist_eq_norm] at this; linarith
  have hxc : ‖x - c‖ < R := by have := hx; rwa [Metric.mem_ball, dist_eq_norm] at this
  -- the compact set of differences
  set K : Set (Euc d) := {u | h / 2 ≤ ‖u‖} ∩ Metric.closedBall 0 (R + Bc) ∩
    {u | ∀ i, |u i| ≤ L / 2 + R} with hK
  have hKc : IsCompact K := by
    refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Euc d) (R + Bc)) ?_ ?_
    · refine ((isClosed_le continuous_const continuous_norm).inter Metric.isClosed_closedBall).inter ?_
      have : {u : Euc d | ∀ i, |u i| ≤ L / 2 + R} = ⋂ i, {u : Euc d | |u i| ≤ L / 2 + R} := by
        ext u; simp
      rw [this]
      exact isClosed_iInter fun i => isClosed_le
        ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.abs) continuous_const
    · intro u hu; exact hu.1.2
  set W : Set (Euc d) := {u | ∀ i, |u i| < L} \ {0} with hW
  have hWo : IsOpen W := by
    have : {u : Euc d | ∀ i, |u i| < L} = ⋂ i, {u : Euc d | |u i| < L} := by ext u; simp
    refine IsOpen.sdiff ?_ isClosed_singleton
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_lt
      ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.abs) continuous_const
  have hWU : W ⊆ {x : Euc d | ∀ z : Fin d → ℤ, x ≠ L • latticePt z} := by
    intro u hu z hz
    obtain ⟨hu1, hu2⟩ := hu
    have : z = 0 := by
      funext i
      have h3 : u i = L * (z i : ℝ) := by
        have := congrArg (fun w : Euc d => w i) hz
        simpa [latticePt] using this
      have h5 : |L * (z i : ℝ)| < L := by rw [← h3]; exact hu1 i
      have h6 : |(z i : ℝ)| < 1 := by
        rw [abs_mul, abs_of_pos hL] at h5
        by_contra hcon
        push Not at hcon
        nlinarith
      have h7 : |z i| < 1 := by exact_mod_cast h6
      exact Int.abs_lt_one_iff.1 h7
    subst this
    apply hu2
    rw [hz]; ext i; simp [latticePt]
  have hWsm : ContDiffOn ℝ ∞ γ W := hγ.smooth.mono hWU
  have hKW : K ⊆ W := by
    intro u hu
    refine ⟨fun i => lt_of_le_of_lt (hu.2 i) (by linarith), ?_⟩
    intro h0
    have : h / 2 ≤ ‖u‖ := hu.1.1
    rw [Set.mem_singleton_iff] at h0
    simp [h0] at this
    linarith
  obtain ⟨Mγ, hMγ⟩ := hKc.exists_bound_of_continuousOn
    ((hWsm.continuousOn_fderiv_of_isOpen hWo (by norm_num)).mono hKW)
  have hMγ0 : 0 ≤ max Mγ 0 := le_max_right _ _
  -- difference lemma: for x' near x and y in the cell with k y ≠ 0, x' - y ∈ K
  have hdiff : ∀ x' ∈ Metric.ball x r, ∀ y ∈ Cell, k y ≠ 0 → x' - y ∈ K ∧ x' - y ∈ W := by
    intro x' hx' y hy hky
    have hx'x : ‖x' - x‖ < r := by rwa [Metric.mem_ball, dist_eq_norm] at hx'
    have hx'c : ‖x' - c‖ < R := by
      have : ‖x' - c‖ ≤ ‖x' - x‖ + ‖x - c‖ := by
        calc ‖x' - c‖ = ‖(x' - x) + (x - c)‖ := by congr 1; abel
          _ ≤ _ := norm_add_le _ _
      have h2 : r ≤ R - ‖x - c‖ := min_le_right _ _
      linarith
    have hyx : h ≤ ‖y - x‖ := by
      by_contra hcon
      push Not at hcon
      have : y ∈ Metric.ball x h := by rw [Metric.mem_ball, dist_eq_norm]; exact hcon
      have h1 := hη1 y this
      apply hky
      simp [hk, h1]
    have h1 : h / 2 ≤ ‖x' - y‖ := by
      have : ‖y - x‖ ≤ ‖y - x'‖ + ‖x' - x‖ := by
        calc ‖y - x‖ = ‖(y - x') + (x' - x)‖ := by congr 1; abel
          _ ≤ _ := norm_add_le _ _
      rw [norm_sub_rev y x'] at this
      have h2 : r ≤ h / 2 := min_le_left _ _
      linarith
    have h2 : ‖x' - y‖ ≤ R + Bc := by
      have : ‖x' - y‖ ≤ ‖x' - c‖ + ‖y - c‖ := by
        calc ‖x' - y‖ = ‖(x' - c) - (y - c)‖ := by congr 1; abel
          _ ≤ _ := norm_sub_le _ _
      have := sa12c21_cell_bdd L hL c hy
      linarith
    have h3 : ∀ i, |(x' - y) i| ≤ L / 2 + R := by
      intro i
      have e1 : |(x' - c) i| ≤ ‖x' - c‖ := by
        simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (x' - c) i
      have e2 := hy i
      have e3 : (x' - y) i = (x' - c) i - (y - c) i := by simp
      rw [e3]
      refine (abs_sub _ _).trans ?_
      have : |(y - c) i| ≤ L / 2 := by
        rw [abs_le]; constructor <;> linarith [e2.1, e2.2]
      linarith
    have hKm : x' - y ∈ K := ⟨⟨h1, by rw [Metric.mem_closedBall, dist_zero_right]; exact h2⟩, h3⟩
    exact ⟨hKm, hKW hKm⟩
  -- the main application
  have hint : ∀ x' : Euc d, Integrable (fun y => γ (x' - y)) μ := fun x' =>
    sa12c21_integrableOn_sub hγ.locInt x' hCellbdd
  have hm1 : Measurable (fun y : Euc d => fderiv ℝ γ (x - y)) :=
    (measurable_fderiv ℝ γ).comp (measurable_const.sub measurable_id)
  have hF'meas : AEStronglyMeasurable (fun y => k y • fderiv ℝ γ (x - y)) μ :=
    hkc.aestronglyMeasurable.smul hm1.aestronglyMeasurable
  have hF'bound : ∀ᵐ y ∂μ, ∀ x' ∈ Metric.ball x r, ‖k y • fderiv ℝ γ (x' - y)‖ ≤ max Kk 0 * max Mγ 0 := by
    filter_upwards [ae_restrict_mem hCellm] with y hy x' hx'
    by_cases hky : k y = 0
    · simp [hky]; positivity
    · obtain ⟨hKm, -⟩ := hdiff x' hx' y hy hky
      rw [norm_smul]
      refine mul_le_mul ?_ ?_ (norm_nonneg _) (le_max_right Kk 0)
      · simpa [Real.norm_eq_abs] using hkb y hy
      · exact (hMγ _ hKm).trans (le_max_left _ _)
  refine ⟨hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun x' y => γ (x' - y) * k y) (F' := fun x' y => k y • fderiv ℝ γ (x' - y))
    (bound := fun _ => max Kk 0 * max Mγ 0) (Metric.ball_mem_nhds x hrpos) ?_ ?_ hF'meas hF'bound
    (integrable_const _) ?_, ?_⟩
  · exact Filter.Eventually.of_forall fun x' => (hint x').1.mul hkc.aestronglyMeasurable
  · have := (hint x).bdd_mul hkc.aestronglyMeasurable (c := max Kk 0) (by
      filter_upwards [ae_restrict_mem hCellm] with y hy
      simpa [Real.norm_eq_abs] using hkb y hy)
    simpa [mul_comm] using this
  · filter_upwards [ae_restrict_mem hCellm] with y hy x' hx'
    by_cases hky : k y = 0
    · have : (fun x'' : Euc d => γ (x'' - y) * k y) = fun _ => 0 := by funext x''; simp [hky]
      rw [this, hky, zero_smul]
      exact hasFDerivAt_const 0 x'
    · obtain ⟨-, hWm⟩ := hdiff x' hx' y hy hky
      have hd : DifferentiableAt ℝ γ (x' - y) :=
        ((hWsm.contDiffAt (hWo.mem_nhds hWm)).differentiableAt (by norm_num))
      have h1 : HasFDerivAt (fun x'' : Euc d => γ (x'' - y)) (fderiv ℝ γ (x' - y)) x' := by
        have := hd.hasFDerivAt.comp x' ((hasFDerivAt_id x').sub_const y)
        exact this.congr_fderiv (ContinuousLinearMap.comp_id _)
      exact h1.mul_const (k y)
  · refine Integrable.mono' (integrable_const (max Kk 0 * max Mγ 0)) hF'meas ?_
    filter_upwards [hF'bound] with y hy
    exact hy x (Metric.mem_ball_self hrpos)

/-- Differentiation of the convolution of a compactly supported continuous function with a `C¹`
kernel. -/
theorem sa12c21_smooth_conv_deriv {G k : Euc d → ℝ} (hG : ContDiff ℝ 1 G) (hk : Continuous k)
    (hkc : HasCompactSupport k) (x : Euc d) :
    HasFDerivAt (fun x' => ∫ y, G (x' - y) * k y) (∫ y, k y • fderiv ℝ G (x - y)) x := by
  obtain ⟨B0, hB0⟩ := hkc.isCompact.isBounded.subset_closedBall (0 : Euc d)
  set B1 : ℝ := ‖x‖ + 1 + B0 with hB1
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Euc d) B1).exists_bound_of_continuousOn
    (hG.continuous_fderiv one_ne_zero).continuousOn
  obtain ⟨C0, hC0⟩ := (isCompact_closedBall (0 : Euc d) B1).exists_bound_of_continuousOn
    hG.continuous.continuousOn
  have hmem : ∀ x' ∈ Metric.ball x 1, ∀ y, k y ≠ 0 → x' - y ∈ Metric.closedBall (0 : Euc d) B1 := by
    intro x' hx' y hy
    have hy' : y ∈ Metric.closedBall (0 : Euc d) B0 :=
      hB0 (subset_tsupport k (Function.mem_support.2 hy))
    rw [Metric.mem_closedBall, dist_zero_right] at hy' ⊢
    have h1 : ‖x'‖ ≤ ‖x‖ + 1 := by
      have := norm_le_norm_add_norm_sub' x' x
      rw [Metric.mem_ball, dist_eq_norm] at hx'
      linarith
    calc ‖x' - y‖ ≤ ‖x'‖ + ‖y‖ := norm_sub_le _ _
      _ ≤ B1 := by rw [hB1]; linarith
  have hcont : ∀ x' : Euc d, Continuous fun y => G (x' - y) * k y := fun x' =>
    (hG.continuous.comp (continuous_const.sub continuous_id)).mul hk
  have hcs : ∀ x' : Euc d, HasCompactSupport fun y => G (x' - y) * k y := fun x' => hkc.mul_left
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun x' y => G (x' - y) * k y) (F' := fun x' y => k y • fderiv ℝ G (x' - y))
    (bound := fun y => ‖k y‖ * max C 0) (Metric.ball_mem_nhds x one_pos) ?_ ?_ ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun x' => (hcont x').aestronglyMeasurable
  · exact (hcont x).integrable_of_hasCompactSupport (hcs x)
  · exact hk.aestronglyMeasurable.smul
      ((hG.continuous_fderiv one_ne_zero).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun y x' hx' => ?_
    by_cases hky : k y = 0
    · simp [hky]
    · rw [norm_smul]
      exact mul_le_mul_of_nonneg_left ((hC _ (hmem x' hx' y hky)).trans (le_max_left _ _))
        (norm_nonneg _)
  · exact (hk.norm.integrable_of_hasCompactSupport hkc.norm).mul_const _
  · refine Filter.Eventually.of_forall fun y x' _ => ?_
    have h0 : HasFDerivAt G (fderiv ℝ G (x' - y)) (x' - y) :=
      ((hG.differentiable one_ne_zero) (x' - y)).hasFDerivAt
    have h1 : HasFDerivAt (fun x'' : Euc d => G (x'' - y)) (fderiv ℝ G (x' - y)) x' := by
      have := h0.comp x' ((hasFDerivAt_id x').sub_const y)
      exact this.congr_fderiv (ContinuousLinearMap.comp_id _)
    exact h1.mul_const (k y)

/-- The near part: the periodic kernel is the Euclidean kernel plus a constant plus a smooth term. -/
theorem sa12c21_near_deriv (hd : 1 ≤ d) {s L R δ c₀ : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (hR : 0 < R) (hbox : 4 * R < L) (hloc : 2 * R < δ * L)
    {q γ : Euc d → ℝ} (hq : ContDiff ℝ ∞ q)
    (hdec : ∀ u : Euc d, u ≠ 0 → ‖u‖ < δ * L →
      γ u = rieszKernel d s u + c₀ + L ^ (-s) * q (L⁻¹ • u))
    {c x : Euc d} (hx : x ∈ Metric.ball c R) {k1 : Euc d → ℝ} (hk1 : ContDiff ℝ 1 k1)
    (hk1c : HasCompactSupport k1) (hk1s : tsupport k1 ⊆ Metric.ball c R) :
    HasFDerivAt (fun x' => ∫ y in {y : Euc d | y - c ∈ centeredBox d L}, γ (x' - y) * k1 y)
      (fderiv ℝ (fun x' => ∫ y, rieszKernel d s (x' - y) * k1 y) x +
        L ^ (-s) • ∫ y, k1 y • fderiv ℝ (fun u => q (L⁻¹ • u)) (x - y)) x := by
  have hL : 0 < L := by linarith
  haveI : Nontrivial (Euc d) := by
    haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    infer_instance
  have hriesz := rieszKernel_locallyIntegrable (d := d) hs0 hsd
  have hsm : ContDiff ℝ 1 (fun u : Euc d => L⁻¹ • u) := contDiff_id.const_smul L⁻¹
  have hq1 : ContDiff ℝ 1 (fun u : Euc d => q (L⁻¹ • u)) :=
    (hq.of_le (m := 1) (by exact_mod_cast le_top)).comp hsm
  have hk1cont : Continuous k1 := hk1.continuous
  set Cell : Set (Euc d) := {y : Euc d | y - c ∈ centeredBox d L} with hCell
  have hball : Metric.ball c R ⊆ Cell := by
    intro y hy
    rw [Metric.mem_ball, dist_eq_norm] at hy
    intro i
    have : |(y - c) i| ≤ ‖y - c‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (y - c) i
    rw [abs_le] at this
    constructor <;> linarith [this.1, this.2]
  have hzero : ∀ y, y ∉ Metric.ball c R → k1 y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport (fun h => hy (hk1s h))
  -- the three integrable pieces
  have hT1 : ∀ x' : Euc d, Integrable (fun y => rieszKernel d s (x' - y) * k1 y) volume := by
    intro x'
    have h1 := sa12c21_integrableOn_sub hriesz x' (Metric.isBounded_ball (x := c) (r := R))
    have h2 : IntegrableOn (fun y => rieszKernel d s (x' - y) * k1 y) (Metric.ball c R) volume := by
      obtain ⟨C, hC⟩ := hk1c.exists_bound_of_continuous hk1cont
      have h3 := Integrable.bdd_mul (μ := volume.restrict (Metric.ball c R)) (c := C) h1
        hk1cont.aestronglyMeasurable (Filter.Eventually.of_forall hC)
      exact h3.congr (Filter.Eventually.of_forall fun y => mul_comm _ _)
    refine (integrableOn_iff_integrable_of_support_subset ?_).1 h2
    intro y hy
    by_contra hcon
    exact hy (by simp [hzero y hcon])
  have hT2 : Integrable k1 volume := hk1cont.integrable_of_hasCompactSupport hk1c
  have hq' : Continuous fun u : Euc d => q (L⁻¹ • u) := hq1.continuous
  have hT3 : ∀ x' : Euc d, Integrable (fun y => q (L⁻¹ • (x' - y)) * k1 y) volume := fun x' =>
    ((hq'.comp (continuous_const.sub continuous_id)).mul hk1cont).integrable_of_hasCompactSupport
      hk1c.mul_left
  have hae : ∀ᵐ y : Euc d, y ≠ x := by
    have := (Set.countable_singleton x).ae_notMem (volume : Measure (Euc d))
    filter_upwards [this] with y hy; simpa using hy
  -- local description of the near integral
  have hEq : ∀ x' ∈ Metric.ball c R, ∫ y in Cell, γ (x' - y) * k1 y =
      (∫ y, rieszKernel d s (x' - y) * k1 y) + c₀ * (∫ y, k1 y) +
        L ^ (-s) * (∫ y, q (L⁻¹ • (x' - y)) * k1 y) := by
    intro x' hx'
    have hx'c : ‖x' - c‖ < R := by rwa [Metric.mem_ball, dist_eq_norm] at hx'
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
      rw [hzero y (fun h => hy (hball h)), mul_zero])]
    have hae' : ∀ᵐ y : Euc d, y ≠ x' := by
      have := (Set.countable_singleton x').ae_notMem (volume : Measure (Euc d))
      filter_upwards [this] with y hy; simpa using hy
    have hpt : ∫ y, γ (x' - y) * k1 y = ∫ y, (rieszKernel d s (x' - y) * k1 y + c₀ * k1 y +
        L ^ (-s) * (q (L⁻¹ • (x' - y)) * k1 y)) := by
      refine integral_congr_ae ?_
      filter_upwards [hae'] with y hy
      by_cases hk : k1 y = 0
      · simp [hk]
      · have hyb : y ∈ Metric.ball c R := by
          by_contra hcon; exact hk (hzero y hcon)
        have hyc : ‖y - c‖ < R := by rwa [Metric.mem_ball, dist_eq_norm] at hyb
        have hu : x' - y ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
        have hun : ‖x' - y‖ < δ * L := by
          have : ‖x' - y‖ ≤ ‖x' - c‖ + ‖y - c‖ := by
            calc ‖x' - y‖ = ‖(x' - c) - (y - c)‖ := by congr 1; abel
              _ ≤ _ := norm_sub_le _ _
          linarith
        rw [hdec _ hu hun]
        ring
    have i2 : Integrable (fun y => c₀ * k1 y) volume := hT2.const_mul c₀
    have i3 : Integrable (fun y => L ^ (-s) * (q (L⁻¹ • (x' - y)) * k1 y)) volume :=
      (hT3 x').const_mul _
    have i12 : Integrable (fun y => rieszKernel d s (x' - y) * k1 y + c₀ * k1 y) volume :=
      (hT1 x').add i2
    rw [hpt, integral_add i12 i3, integral_add (hT1 x') i2, integral_const_mul, integral_const_mul]
  -- derivatives of the three pieces
  have hE : HasFDerivAt (fun x' => ∫ y, rieszKernel d s (x' - y) * k1 y)
      (fderiv ℝ (fun x' => ∫ y, rieszKernel d s (x' - y) * k1 y) x) x :=
    ((HRS.MS.UniqT3.convFun_diff hriesz hk1 hk1c) x).hasFDerivAt
  have hQ := sa12c21_smooth_conv_deriv hq1 hk1cont hk1c x
  have hcomb := (hE.add_const (c₀ * ∫ y, k1 y)).add (hQ.const_mul (L ^ (-s)))
  refine hcomb.congr_of_eventuallyEq ?_
  filter_upwards [Metric.ball_mem_nhds x (show 0 < R - ‖x - c‖ by
    have := hx; rw [Metric.mem_ball, dist_eq_norm] at this; linarith)] with x' hx'
  have hx'c : x' ∈ Metric.ball c R := by
    rw [Metric.mem_ball, dist_eq_norm] at hx' ⊢
    have hx0 := hx; rw [Metric.mem_ball, dist_eq_norm] at hx0
    calc ‖x' - c‖ = ‖(x' - x) + (x - c)‖ := by congr 1; abel
      _ ≤ ‖x' - x‖ + ‖x - c‖ := norm_add_le _ _
      _ < R := by linarith
  exact hEq x' hx'c

theorem sa12c21_int_cell {γ k : Euc d → ℝ} (hγ : LocallyIntegrable γ volume) (hk : Continuous k)
    (L : ℝ) (hL : 0 < L) (c x' : Euc d) :
    Integrable (fun y => γ (x' - y) * k y) (volume.restrict {y : Euc d | y - c ∈ centeredBox d L}) := by
  set Cell : Set (Euc d) := {y : Euc d | y - c ∈ centeredBox d L} with hCell
  have hCellb : Cell ⊆ Metric.closedBall c (Real.sqrt (d * L ^ 2)) := by
    intro y hy
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact sa12c21_cell_bdd L hL c hy
  have hCellbdd : Bornology.IsBounded Cell := Metric.isBounded_closedBall.subset hCellb
  obtain ⟨C, hC⟩ := (isCompact_closedBall c (Real.sqrt (d * L ^ 2))).exists_bound_of_continuousOn
    hk.continuousOn
  have h1 := sa12c21_integrableOn_sub hγ x' hCellbdd
  have h3 := Integrable.bdd_mul (μ := volume.restrict Cell) (c := C) h1 hk.aestronglyMeasurable
    (by filter_upwards [ae_restrict_mem (sa12c21_measurable_cell L c)] with y hy
        exact hC y (hCellb hy))
  exact h3.congr (Filter.Eventually.of_forall fun y => mul_comm _ _)

-- BEGIN SA12.C21
theorem periodic_near_identity (hd : 1 ≤ d) (s : ℝ)
    (hs0 : 0 ≤ s) (hsd : s<d) (δ L R h : ℝ) (hL : 1 ≤ L)
    (hR : 0<R) (hh : 0<h) (hbox : 4*R<L) (hloc : 2*R<δ*L)
    (q γ : Euc d → ℝ) (hq : ContDiff ℝ ∞ q)
    (hγ : HRS.Whole.AppendixALemmas.IsPeriodicRieszKernel d s L γ)
    (c₀ : ℝ) (hdec : ∀ u : Euc d, u≠0 → ‖u‖<δ*L →
      γ u=rieszKernel d s u+c₀+L^(-s)*q (L⁻¹ • u))
    (M : Matrix (Fin d) (Fin d) ℝ) (μ F : Euc d → ℝ)
    (hμ : ContDiff ℝ ∞ μ) (hF : ContDiff ℝ ∞ F)
    (hμp : ∀ (x : Euc d) (k : Fin d → ℤ), μ (x+L • latticePt k)=μ x)
    (hFp : ∀ (x : Euc d) (k : Fin d → ℤ), F (x+L • latticePt k)=F x)
    (c x : Euc d) (hx : x ∈ Metric.ball c R) (η : Euc d → ℝ)
    (hη : MemCb 1 η) (hηs : tsupport η ⊆ Metric.ball c R)
    (hη1 : ∀ y ∈ Metric.ball x h, η y=1) :
    perNonlocal L γ M μ F x =
      eucNonlocal s M (fun y => η y*μ y) F x+
      (∑ i : Fin d, ∑ j : Fin d, M j i*(L^(-s-1)*
        ∫ y, fderiv ℝ q (L⁻¹ • (x-y)) (EuclideanSpace.single i (1 : ℝ))*
          (η y*μ y*fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ)))))+
      (∑ i : Fin d, ∑ j : Fin d, M j i*
        ∫ y in {y | y-c ∈ centeredBox d L},
          fderiv ℝ γ (x-y) (EuclideanSpace.single i (1 : ℝ))*
            ((1-η y)*(μ y*fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ))))) := by
  have hL0 : 0 < L := by linarith
  have hμ1 : ContDiff ℝ 1 μ := hμ.of_le (by exact_mod_cast le_top)
  have hη1' : ContDiff ℝ 1 η := hη.1
  have hdF : ContDiff ℝ ∞ (fderiv ℝ F) := hF.fderiv_right (m := ∞) le_rfl
  have hηcs : HasCompactSupport η :=
    IsCompact.of_isClosed_subset (isCompact_closedBall c R) (isClosed_tsupport η)
      (hηs.trans Metric.ball_subset_closedBall)
  have hper_fd : ∀ (y : Euc d) (k : Fin d → ℤ), fderiv ℝ F (y + L • latticePt k) = fderiv ℝ F y := by
    intro y k
    have h1 : (fun z => F (z + L • latticePt (d := d) k)) = F := funext fun z => hFp z k
    have h2 := fderiv_comp_add_right (𝕜 := ℝ) (f := F) (x := y) (L • latticePt (d := d) k)
    rw [h1] at h2
    exact h2.symm
  have key : ∀ i j : Fin d,
      fderiv ℝ (perConv L γ (fun y => μ y * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ)))) x
        (EuclideanSpace.single i (1 : ℝ)) =
      fderiv ℝ (fun x' => ∫ y, rieszKernel d s (x' - y) *
          ((fun y => η y * μ y) y * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ)))) x
        (EuclideanSpace.single i (1 : ℝ)) +
      L ^ (-s - 1) * (∫ y, fderiv ℝ q (L⁻¹ • (x - y)) (EuclideanSpace.single i (1 : ℝ)) *
        (η y * μ y * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ)))) +
      (∫ y in {y | y - c ∈ centeredBox d L},
        fderiv ℝ γ (x - y) (EuclideanSpace.single i (1 : ℝ)) *
          ((1 - η y) * (μ y * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ))))) := by
    intro i j
    set ej : Euc d := EuclideanSpace.single j (1 : ℝ) with hej
    set ei : Euc d := EuclideanSpace.single i (1 : ℝ) with hei
    set g : Euc d → ℝ := fun y => μ y * fderiv ℝ F y ej with hg
    have hgc : Continuous g :=
      hμ.continuous.mul ((hdF.continuous).clm_apply continuous_const)
    have hgp : ∀ (y : Euc d) (k : Fin d → ℤ), g (y + L • latticePt k) = g y := by
      intro y k; simp only [hg]; rw [hμp, hper_fd]
    set k1 : Euc d → ℝ := fun y => η y * μ y * fderiv ℝ F y ej with hk1
    have hk1sm : ContDiff ℝ 1 k1 :=
      (hη1'.mul hμ1).mul (((hdF.of_le (by exact_mod_cast le_top)) : ContDiff ℝ 1 (fderiv ℝ F)).clm_apply
        contDiff_const)
    have hk1c : HasCompactSupport k1 := (hηcs.mul_right).mul_right
    have hk1s : tsupport k1 ⊆ Metric.ball c R := by
      refine (tsupport_mul_subset_left.trans ?_).trans hηs
      exact tsupport_mul_subset_left
    set k2 : Euc d → ℝ := fun y => (1 - η y) * g y with hk2
    have hsplit : ∀ y, g y = k1 y + k2 y := by
      intro y; simp only [hg, hk1, hk2]; ring
    have hk2c : Continuous k2 := (continuous_const.sub hη1'.continuous).mul hgc
    have hperC : ∀ x' : Euc d, perConv L γ g x' =
        (∫ y in {y : Euc d | y - c ∈ centeredBox d L}, γ (x' - y) * k1 y) +
        ∫ y in {y : Euc d | y - c ∈ centeredBox d L}, γ (x' - y) * k2 y := by
      intro x'
      rw [sa12c21_perConv_cell L hL0 γ g hγ.periodic hgp c x', ← integral_add
        (sa12c21_int_cell hγ.locInt hk1sm.continuous L hL0 c x')
        (sa12c21_int_cell hγ.locInt hk2c L hL0 c x')]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [hsplit y]; ring
    have hA := sa12c21_near_deriv hd hs0 hsd hR hbox hloc hq hdec hx hk1sm hk1c hk1s
    obtain ⟨hB, hBint⟩ := sa12c21_far_deriv hR hh hbox hγ hx hη1 hη1'.continuous hgc
    have hP : HasFDerivAt (perConv L γ g)
        ((fderiv ℝ (fun x' => ∫ y, rieszKernel d s (x' - y) * k1 y) x +
            L ^ (-s) • ∫ y, k1 y • fderiv ℝ (fun u => q (L⁻¹ • u)) (x - y)) +
          ∫ y in {y : Euc d | y - c ∈ centeredBox d L}, (k2 y) • fderiv ℝ γ (x - y)) x := by
      refine (hA.add hB).congr_of_eventuallyEq ?_
      exact Filter.Eventually.of_forall fun x' => hperC x'
    have hsm : ContDiff ℝ 1 (fun u : Euc d => L⁻¹ • u) := contDiff_id.const_smul L⁻¹
    have hq1 : ContDiff ℝ 1 (fun u : Euc d => q (L⁻¹ • u)) :=
      (hq.of_le (m := 1) (by exact_mod_cast le_top)).comp hsm
    have hqt : ∀ u : Euc d, fderiv ℝ (fun u => q (L⁻¹ • u)) u ei =
        L⁻¹ * fderiv ℝ q (L⁻¹ • u) ei := by
      intro u
      have h0 : HasFDerivAt q (fderiv ℝ q (L⁻¹ • u)) (L⁻¹ • u) :=
        ((hq.differentiable (by norm_num)) (L⁻¹ • u)).hasFDerivAt
      have h1 := h0.comp u ((hasFDerivAt_id u).const_smul L⁻¹)
      rw [show (fun u : Euc d => q (L⁻¹ • u)) = q ∘ (fun u => L⁻¹ • u) from rfl, h1.fderiv]
      simp
    have hint1 : Integrable (fun y => k1 y • fderiv ℝ (fun u => q (L⁻¹ • u)) (x - y)) volume :=
      (hk1sm.continuous.smul ((hq1.continuous_fderiv one_ne_zero).comp
        (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport hk1c.smul_right
    rw [hP.fderiv, ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.integral_apply hint1,
      ContinuousLinearMap.integral_apply hBint]
    have e1 : ∫ y, (k1 y • fderiv ℝ (fun u => q (L⁻¹ • u)) (x - y)) ei =
        L⁻¹ * ∫ y, fderiv ℝ q (L⁻¹ • (x - y)) ei * k1 y := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, hqt]; ring
    have e2 : ∫ y in {y : Euc d | y - c ∈ centeredBox d L}, (k2 y • fderiv ℝ γ (x - y)) ei =
        ∫ y in {y : Euc d | y - c ∈ centeredBox d L}, fderiv ℝ γ (x - y) ei * k2 y := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]; ring
    have e3 : L ^ (-s - 1) = L ^ (-s) * L⁻¹ := by
      rw [Real.rpow_sub_one hL0.ne', div_eq_mul_inv]
    rw [e1, e2, e3, smul_eq_mul]
    simp only [hk1, hk2, hg]
    ring
  unfold perNonlocal eucNonlocal
  have h1 : ∀ i j : Fin d, M j i * fderiv ℝ (perConv L γ
        (fun y => μ y * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ)))) x
        (EuclideanSpace.single i (1 : ℝ)) =
      M j i * fderiv ℝ (fun x' => ∫ y, rieszKernel d s (x' - y) *
          ((fun y => η y * μ y) y * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ)))) x
        (EuclideanSpace.single i (1 : ℝ)) +
      M j i * (L ^ (-s - 1) * ∫ y, fderiv ℝ q (L⁻¹ • (x - y)) (EuclideanSpace.single i (1 : ℝ)) *
        (η y * μ y * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ)))) +
      M j i * ∫ y in {y | y - c ∈ centeredBox d L},
        fderiv ℝ γ (x - y) (EuclideanSpace.single i (1 : ℝ)) *
          ((1 - η y) * (μ y * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ)))) := by
    intro i j
    rw [key i j]; ring
  simp only [h1, Finset.sum_add_distrib]

-- END SA12.C21

end HRS.MH.AdjointRd.Phase2SA12Construction
