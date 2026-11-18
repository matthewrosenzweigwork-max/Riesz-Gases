import HRS.MS.R26T8AP10a1

/-!
# S8.2 T8A P10a (part 3): the cutoff `1 - chi((u-y)/δ)` and its limit `δ → 0`
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

def r26t8a_cut (chi : Euc d → ℝ) (y : Euc d) (δ : ℝ) (u : Euc d) : ℝ := 1 - chi (δ⁻¹ • (u - y))

section cut
variable {chi : Euc d → ℝ}

theorem r26t8a_cut_norm {δ : ℝ} (hδ : 0 < δ) (y u : Euc d) : ‖δ⁻¹ • (u - y)‖ = ‖u - y‖ / δ := by
  rw [norm_smul, norm_inv, Real.norm_of_nonneg hδ.le]; ring

theorem r26t8a_cut_contDiff (hchi : NewtonCutoff chi) (y : Euc d) (δ : ℝ) :
    ContDiff ℝ ∞ (r26t8a_cut chi y δ) := by
  unfold r26t8a_cut
  exact contDiff_const.sub (hchi.1.comp ((contDiff_id.sub contDiff_const).const_smul _))

theorem r26t8a_cut_eq_zero (hchi : NewtonCutoff chi) (y : Euc d) {δ : ℝ} (hδ : 0 < δ) {u : Euc d}
    (hu : ‖u - y‖ ≤ δ) : r26t8a_cut chi y δ u = 0 := by
  have h : ‖δ⁻¹ • (u - y)‖ ≤ 1 := by
    rw [r26t8a_cut_norm hδ, div_le_one hδ]; exact hu
  unfold r26t8a_cut
  rw [hchi.2.2.2.1 _ h]
  norm_num

theorem r26t8a_cut_eq_one (hchi : NewtonCutoff chi) (y : Euc d) {δ : ℝ} (hδ : 0 < δ) {u : Euc d}
    (hu : 2 * δ ≤ ‖u - y‖) : r26t8a_cut chi y δ u = 1 := by
  have h : 2 ≤ ‖δ⁻¹ • (u - y)‖ := by
    rw [r26t8a_cut_norm hδ, le_div_iff₀ hδ]; exact hu
  unfold r26t8a_cut
  rw [hchi.2.2.2.2 _ h]
  norm_num

theorem r26t8a_cut_mem (hchi : NewtonCutoff chi) (y : Euc d) (δ : ℝ) (u : Euc d) :
    0 ≤ r26t8a_cut chi y δ u ∧ r26t8a_cut chi y δ u ≤ 1 := by
  have := hchi.2.2.1 (δ⁻¹ • (u - y))
  unfold r26t8a_cut
  constructor <;> linarith [this.1, this.2]

theorem r26t8a_cut_fderiv_zero_lt (hchi : NewtonCutoff chi) (y : Euc d) {δ : ℝ} (hδ : 0 < δ)
    {u : Euc d} (hu : ‖u - y‖ < δ) : fderiv ℝ (r26t8a_cut chi y δ) u = 0 := by
  have : r26t8a_cut chi y δ =ᶠ[𝓝 u] fun _ => 0 := by
    have hm : ball y δ ∈ 𝓝 u :=
      isOpen_ball.mem_nhds (by simpa [mem_ball_iff_norm, dist_eq_norm] using hu)
    filter_upwards [hm] with v hv
    exact r26t8a_cut_eq_zero hchi y hδ (by simpa [mem_ball_iff_norm, dist_eq_norm] using hv.le)
  rw [this.fderiv_eq]; simp

theorem r26t8a_cut_fderiv_zero_gt (hchi : NewtonCutoff chi) (y : Euc d) {δ : ℝ} (hδ : 0 < δ)
    {u : Euc d} (hu : 2 * δ < ‖u - y‖) : fderiv ℝ (r26t8a_cut chi y δ) u = 0 := by
  have : r26t8a_cut chi y δ =ᶠ[𝓝 u] fun _ => 1 := by
    have hm : (closedBall y (2 * δ))ᶜ ∈ 𝓝 u :=
      (isClosed_closedBall).isOpen_compl.mem_nhds
        (by simpa [mem_closedBall_iff_norm, dist_eq_norm] using hu)
    filter_upwards [hm] with v hv
    have h2 : 2 * δ < ‖v - y‖ := by simpa [mem_closedBall_iff_norm, dist_eq_norm, not_le] using hv
    exact r26t8a_cut_eq_one hchi y hδ h2.le
  rw [this.fderiv_eq]; simp

theorem r26t8a_cut_fderiv_bound (hchi : NewtonCutoff chi) :
    ∃ Cχ : ℝ, 0 ≤ Cχ ∧ ∀ (y : Euc d) {δ : ℝ}, 0 < δ → ∀ u : Euc d,
      ‖fderiv ℝ (r26t8a_cut chi y δ) u‖ ≤ Cχ / δ := by
  have hcont : Continuous (fderiv ℝ chi) := hchi.1.continuous_fderiv (by simp)
  obtain ⟨B, hB⟩ :=
    (isCompact_closedBall (0 : Euc d) 2).exists_bound_of_continuousOn hcont.continuousOn
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (by simp))
  have hbd : ∀ z : Euc d, ‖fderiv ℝ chi z‖ ≤ B := by
    intro z
    by_cases hz : ‖z‖ ≤ 2
    · exact hB z (by simpa [mem_closedBall_zero_iff] using hz)
    · have : fderiv ℝ chi z = 0 := by
        have : chi =ᶠ[𝓝 z] fun _ => 0 := by
          have hm : (closedBall (0 : Euc d) 2)ᶜ ∈ 𝓝 z :=
            (isClosed_closedBall).isOpen_compl.mem_nhds (by simpa [mem_closedBall_zero_iff] using hz)
          filter_upwards [hm] with v hv
          have h2 : 2 < ‖v‖ := by simpa [mem_closedBall_zero_iff, not_le] using hv
          exact hchi.2.2.2.2 v h2.le
        rw [this.fderiv_eq]; simp
      rw [this]; simpa using hB0
  refine ⟨B, hB0, fun y δ hδ u => ?_⟩
  unfold r26t8a_cut
  have hd : HasFDerivAt (fun u : Euc d => δ⁻¹ • (u - y)) (δ⁻¹ • ContinuousLinearMap.id ℝ (Euc d)) u :=
    ((hasFDerivAt_id u).sub_const y).const_smul δ⁻¹
  have hc : HasFDerivAt (fun u : Euc d => chi (δ⁻¹ • (u - y)))
      ((fderiv ℝ chi (δ⁻¹ • (u - y))).comp (δ⁻¹ • ContinuousLinearMap.id ℝ (Euc d))) u :=
    (hchi.1.contDiffAt.differentiableAt (by simp)).hasFDerivAt.comp u hd
  rw [fderiv_const_sub, hc.fderiv, norm_neg]
  calc ‖(fderiv ℝ chi (δ⁻¹ • (u - y))).comp (δ⁻¹ • ContinuousLinearMap.id ℝ (Euc d))‖
      ≤ ‖fderiv ℝ chi (δ⁻¹ • (u - y))‖ * ‖δ⁻¹ • ContinuousLinearMap.id ℝ (Euc d)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ B * δ⁻¹ := by
        refine mul_le_mul (hbd _) ?_ (norm_nonneg _) hB0
        refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
        rw [norm_inv, Real.norm_of_nonneg hδ.le]
        have := ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := Euc d)
        nlinarith [inv_pos.2 hδ]
    _ = B / δ := by ring

/-- `∫ cut_δ F → ∫ F` as `δ → 0+` for integrable `F`. -/
theorem r26t8a_cut_tendsto (hd : 2 ≤ d) (hchi : NewtonCutoff chi) (y : Euc d) {F : Euc d → ℝ}
    (hF : Integrable F) :
    Tendsto (fun δ : ℝ => ∫ u, r26t8a_cut chi y δ u * F u) (𝓝[>] 0) (𝓝 (∫ u, F u)) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun u => ‖F u‖) ?_ ?_ hF.norm ?_
  · refine Filter.Eventually.of_forall fun δ => ?_
    exact ((r26t8a_cut_contDiff hchi y δ).continuous.aestronglyMeasurable).mul hF.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun δ => Filter.Eventually.of_forall fun u => ?_
    have := r26t8a_cut_mem hchi y δ u
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg this.1]
    exact mul_le_of_le_one_left (norm_nonneg _) this.2
  · haveI : Nontrivial (Euc d) := by
      apply Module.nontrivial_of_finrank_pos (R := ℝ)
      simp; omega
    have hae : ∀ᵐ u : Euc d ∂volume, u ≠ y := compl_mem_ae_iff.mpr (measure_singleton y)
    refine hae.mono fun u hu => ?_
    · have hn : 0 < ‖u - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hu)
      have : (fun δ : ℝ => r26t8a_cut chi y δ u * F u) =ᶠ[𝓝[>] 0] fun _ => F u := by
        have hm : Set.Ioo 0 (‖u - y‖ / 2) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by positivity)
        filter_upwards [hm] with δ hδ
        rw [r26t8a_cut_eq_one hchi y hδ.1 (by linarith [hδ.2]), one_mul]
      exact tendsto_const_nhds.congr' (this.symm)

theorem r26t8a_p10a_pole_int (hd : 2 ≤ d) {τ : ℝ} (hτ0 : 0 < τ) (hτ : τ < d) (y : Euc d) {R : ℝ}
    (hR : 0 < R) :
    ∫ u in ball y R, ‖u - y‖ ^ (-τ) = sphereArea d * (R ^ ((d : ℝ) - τ) / ((d : ℝ) - τ)) := by
  have hm := (r26t8a_p11a_mass d hd ((d : ℝ) - τ) (by linarith) (by linarith) R hR).2
  have e : (d : ℝ) - τ - d = -τ := by ring
  rw [e] at hm
  rw [← hm, ← integral_indicator measurableSet_ball, ← integral_indicator measurableSet_ball,
    ← integral_sub_right_eq_self
      (fun z : Euc d => (ball (0 : Euc d) R).indicator (fun z => ‖z‖ ^ (-τ)) z) y]
  congr 1
  funext u
  by_cases hu : u ∈ ball y R
  · have : u - y ∈ ball (0 : Euc d) R := by simpa [mem_ball_iff_norm, dist_eq_norm] using hu
    simp [Set.indicator_of_mem hu, Set.indicator_of_mem this]
  · have : u - y ∉ ball (0 : Euc d) R := by simpa [mem_ball_iff_norm, dist_eq_norm] using hu
    simp [Set.indicator_of_notMem hu, Set.indicator_of_notMem this]

/-- The cutoff term tends to `0`. -/
theorem r26t8a_p10a_cut_term (hd : 2 ≤ d) {τ : ℝ} (hτ0 : 0 < τ) (hτ : τ + 1 < d) (y : Euc d)
    (W : ℝ → Euc d → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hW : ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → ∀ u : Euc d,
      ‖W δ u‖ ≤ if ‖u - y‖ ≤ 2 * δ then K * δ⁻¹ * ‖u - y‖ ^ (-τ) else 0) :
    Tendsto (fun δ : ℝ => ∫ u, W δ u) (𝓝[>] 0) (𝓝 0) := by
  have hτd : τ < d := by linarith
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = (d : ℝ) - τ := ⟨_, rfl⟩
  have hα1 : 0 < α - 1 := by rw [hα]; linarith
  have hbound : ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 →
      ‖∫ u, W δ u‖ ≤ K * (sphereArea d * (3 ^ α / α)) * δ ^ (α - 1) := by
    intro δ hδ hδ2
    have hint : Integrable
        (Set.indicator (ball y (3 * δ)) (fun u : Euc d => K * δ⁻¹ * ‖u - y‖ ^ (-τ))) := by
      rw [integrable_indicator_iff measurableSet_ball]
      exact (r26t8a_p10a_pole_on hd hτ0 hτd y (by positivity)).const_mul _
    refine (norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall fun u => ?_)).trans ?_
    · refine (hW δ hδ hδ2 u).trans ?_
      by_cases h2 : ‖u - y‖ ≤ 2 * δ
      · rw [if_pos h2, Set.indicator_of_mem]
        simpa [mem_ball_iff_norm, dist_eq_norm] using (by linarith : ‖u - y‖ < 3 * δ)
      · rw [if_neg h2]
        exact Set.indicator_nonneg (fun v _ => by positivity) u
    · rw [integral_indicator measurableSet_ball, integral_const_mul,
        r26t8a_p10a_pole_int hd hτ0 hτd y (by positivity), ← hα]
      have h3 : (3 * δ) ^ α = 3 ^ α * δ ^ α := Real.mul_rpow (by norm_num) hδ.le
      have h4 : δ⁻¹ * δ ^ α = δ ^ (α - 1) := by
        rw [← Real.rpow_neg_one, ← Real.rpow_add hδ]; congr 1; ring
      rw [h3]
      refine le_of_eq ?_
      calc K * δ⁻¹ * (sphereArea d * (3 ^ α * δ ^ α / α))
          = K * (sphereArea d * (3 ^ α / α)) * (δ⁻¹ * δ ^ α) := by ring
        _ = _ := by rw [h4]
  refine squeeze_zero_norm' (a := fun δ => K * (sphereArea d * (3 ^ α / α)) * δ ^ (α - 1)) ?_ ?_
  · have : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ ∈ Set.Ioo 0 (1 / 2) := Ioo_mem_nhdsGT (by norm_num)
    filter_upwards [this] with δ hδ
    exact hbound δ hδ.1 hδ.2.le
  · have hc : ContinuousAt (fun δ : ℝ => δ ^ (α - 1)) 0 :=
      Real.continuousAt_rpow_const 0 _ (Or.inr hα1.le)
    have h := (hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))).const_mul
      (K * (sphereArea d * (3 ^ α / α)))
    rwa [Real.zero_rpow hα1.ne', mul_zero] at h

end cut
end HRS.MS.R26T8A
