import HRS.MS.S82WK3

/-!
# S8.2 A04 (S82W), part 5: `L²` convergence by domination, generator bounds in terms of jets
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.S82W
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82U

lemma w_eLp_two {α V : Type*} [MeasurableSpace α] [NormedAddCommGroup V] {P : Measure α} {f : α → V}
    (hf : AEStronglyMeasurable f P) : eLpNorm f 2 P = (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂P) ^ (1 / (2 : ℝ)) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by simp) hf]
  simp

lemma w_l2_dom {α V : Type*} [MeasurableSpace α] [NormedAddCommGroup V] {P : Measure α}
    {g : ℕ → α → V} {H : α → ℝ} (hH : MemLp H 2 P) (hg : ∀ n, AEStronglyMeasurable (g n) P)
    (hb : ∀ n, ∀ᵐ x ∂P, ‖g n x‖ ≤ ‖H x‖) (hl : ∀ᵐ x ∂P, Tendsto (fun n => g n x) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (g n) 2 P) atTop (𝓝 0) := by
  have hfin : ∫⁻ x, ‖H x‖ₑ ^ (2 : ℝ) ∂P ≠ (⊤ : ℝ≥0∞) := by
    have := hH.eLpNorm_lt_top
    rw [w_eLp_two hH.aestronglyMeasurable] at this
    intro h
    rw [h] at this
    simp at this
  have hlim : Tendsto (fun n => ∫⁻ x, ‖g n x‖ₑ ^ (2 : ℝ) ∂P) atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence' (μ := P) (F := fun n x => ‖g n x‖ₑ ^ (2 : ℝ))
      (f := fun _ => 0) (fun x => ‖H x‖ₑ ^ (2 : ℝ))
      (fun n => ((hg n).enorm.pow_const (2 : ℝ))) ?_ hfin ?_
    · simpa using this
    · intro n
      filter_upwards [hb n] with x hx
      exact ENNReal.rpow_le_rpow (enorm_le_iff_norm_le.2 hx) (by norm_num)
    · filter_upwards [hl] with x hx
      have h1 : Tendsto (fun n => ‖g n x‖ₑ) atTop (𝓝 0) := by
        simpa [Function.comp_def] using (continuous_enorm.tendsto (0 : V)).comp hx
      have := (ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto 0 |>.comp h1
      simpa [Function.comp_def] using this
  have := (ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto 0 |>.comp hlim
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at this
  refine this.congr fun n => ?_
  simp only [Function.comp]
  rw [w_eLp_two (hg n)]

section gen
variable {d N : ℕ}

/-- size of the drift terms -/
def wGb (d N : ℕ) (a : ℝ) (X : EucConfig d N) : ℝ :=
  ∑ i, (∑ j ∈ Finset.univ.erase i,
    HRS.Whole.movtr_sigma (criticalS d) * ‖X i - X j‖ ^ (-(criticalS d + 1)) + a * ‖X‖)

lemma wGb_tame (hd : 2 ≤ d) (a : ℝ) : u4Tame (wGb d N a) := by
  refine u4Tame_sum _ _ fun i _ => u4Tame_add (u4Tame_sum _ _ fun j hj => ?_)
    (u4Tame_const_mul a u4Tame_norm)
  exact u4Tame_const_mul _ (u4Tame_pole (Finset.ne_of_mem_erase hj).symm (by linarith [u4_crit_pos hd]))

lemma wGb_nonneg (hd : 2 ≤ d) {a : ℝ} (ha : 0 ≤ a) (X : EucConfig d N) : 0 ≤ wGb d N a X := by
  have hσ := HRS.MS.S82T.s82t_sigma_nonneg (criticalS d) (u4_crit_pos hd).le
  exact Finset.sum_nonneg fun i _ => add_nonneg
    (Finset.sum_nonneg fun j _ => mul_nonneg hσ (Real.rpow_nonneg (norm_nonneg _) _))
    (mul_nonneg ha (norm_nonneg _))

lemma w_gen_bound (hd : 2 ≤ d) (hN : 0 < N) {a : ℝ} (ha : 0 ≤ a) (beta : ℝ) (hbeta : 0 < beta)
    {φ : EucConfig d N → ℝ} (hφ : ContDiffOn ℝ 2 φ (eucCollisionSet d N)ᶜ) {X : EucConfig d N}
    (hX : X ∉ eucCollisionSet d N) :
    |particleGenerator (quadraticGradientDyn d (criticalS d) a beta) φ X| ≤
      beta⁻¹ * N * d * ‖iteratedFDeriv ℝ 2 φ X‖ + wGb d N a X * ‖fderiv ℝ φ X‖ := by
  set ν := beta⁻¹ with hν
  have hν0 : 0 ≤ ν := by positivity
  have hgen : particleGenerator (quadraticGradientDyn d (criticalS d) a beta) φ X =
      ν * ∑ i, Laplacian.laplacian (fun y => φ (Function.update X i y)) (X i) +
        ∑ i, inner ℝ (particleDriftW (quadraticGradientDyn d (criticalS d) a beta) X i)
          (Phase2S82.configGrad φ X i) := rfl
  have hσ := HRS.MS.S82T.s82t_sigma_nonneg (criticalS d) (u4_crit_pos hd).le
  have hlap : ∀ i, |Laplacian.laplacian (fun y => φ (Function.update X i y)) (X i)| ≤
      d * ‖iteratedFDeriv ℝ 2 φ X‖ := fun i => u4_laplacian_bound hφ hX i
  have hin : ∀ i, |inner ℝ (particleDriftW (quadraticGradientDyn d (criticalS d) a beta) X i)
      (Phase2S82.configGrad φ X i)| ≤
      (∑ j ∈ Finset.univ.erase i, HRS.Whole.movtr_sigma (criticalS d) *
        ‖X i - X j‖ ^ (-(criticalS d + 1)) + a * ‖X‖) * ‖fderiv ℝ φ X‖ := by
    intro i
    refine (abs_real_inner_le_norm _ _).trans ?_
    exact mul_le_mul (u4_drift_norm_le hd hN ha beta hX i) (u4_configGrad_norm_le hφ hX i) (norm_nonneg _)
      (add_nonneg (Finset.sum_nonneg fun j _ => mul_nonneg hσ (Real.rpow_nonneg (norm_nonneg _) _))
        (mul_nonneg ha (norm_nonneg _)))
  rw [hgen]
  calc _ ≤ |ν * ∑ i, Laplacian.laplacian (fun y => φ (Function.update X i y)) (X i)| +
        |∑ i, inner ℝ (particleDriftW (quadraticGradientDyn d (criticalS d) a beta) X i)
          (Phase2S82.configGrad φ X i)| := abs_add_le _ _
    _ ≤ ν * ∑ i : Fin N, d * ‖iteratedFDeriv ℝ 2 φ X‖ + ∑ i : Fin N, (∑ j ∈ Finset.univ.erase i,
          HRS.Whole.movtr_sigma (criticalS d) * ‖X i - X j‖ ^ (-(criticalS d + 1)) + a * ‖X‖) *
          ‖fderiv ℝ φ X‖ := by
        refine add_le_add ?_ ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hin i))
        rw [abs_mul, abs_of_nonneg hν0]
        exact mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun i _ => hlap i)) hν0
    _ = _ := by
        simp only [wGb, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.sum_mul]
        ring

end gen

end HRS.MS.S82W
