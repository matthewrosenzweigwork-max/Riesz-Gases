import HRS.PDE.MovCAux9

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem movc_ae_ne {ρ : Torus d → ℝ} (hd : 1 ≤ d) (x : Torus d) :
    ∀ᵐ y ∂(withDensityReal ρ), y ≠ x := by
  rw [ae_iff]
  simpa using withDensityReal_singleton hd ρ x

theorem movc_integrable_W_shift {ρ : Torus d → ℝ} {Λ₀ : ℝ} (hρΛ : ∀ x, ρ x ≤ Λ₀)
    {W : Torus d → ℝ} (hW : Integrable W) (x : Torus d) :
    Integrable (fun y => W (x - y)) (withDensityReal ρ) :=
  ((hW.comp_sub_left x).smul_measure ENNReal.ofReal_ne_top).mono_measure
    (withDensityReal_le_smul hρΛ)

theorem movc_row_tendsto (hd : 1 ≤ d) {ρ : Torus d → ℝ} {Λ₀ : ℝ} (hρΛ : ∀ x, ρ x ≤ Λ₀)
    {W : Torus d → ℝ} (hW : Integrable W) {kn : ℕ → Torus d → Torus d → ℝ}
    {k : Torus d → Torus d → ℝ}
    (hm : ∀ n, Measurable (Function.uncurry (kn n)))
    (hdom : ∀ n x y, |kn n x y| ≤ W (x - y))
    (hconv : ∀ x y, x ≠ y → Tendsto (fun n => kn n x y) atTop (𝓝 (k x y))) (x : Torus d) :
    Tendsto (fun n => ∫ y, kn n x y ∂(withDensityReal ρ)) atTop
      (𝓝 (∫ y, k x y ∂(withDensityReal ρ))) := by
  refine tendsto_integral_of_dominated_convergence (fun y => W (x - y))
    (fun n => ((hm n).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
    (movc_integrable_W_shift hρΛ hW x) (fun n => Eventually.of_forall fun y => ?_) ?_
  · rw [Real.norm_eq_abs]; exact hdom n x y
  · filter_upwards [movc_ae_ne (ρ := ρ) hd x] with y hy
    exact hconv x y hy.symm

theorem movc_dbl_tendsto (hd : 1 ≤ d) {ρ : Torus d → ℝ} {Λ₀ : ℝ} (hΛ0 : 0 ≤ Λ₀)
    (hρΛ : ∀ x, ρ x ≤ Λ₀) (hρ : IsProbDensity ρ)
    {W : Torus d → ℝ} (hW : Integrable W) {kn : ℕ → Torus d → Torus d → ℝ}
    {k : Torus d → Torus d → ℝ}
    (hm : ∀ n, Measurable (Function.uncurry (kn n)))
    (hdom : ∀ n x y, |kn n x y| ≤ W (x - y))
    (hconv : ∀ x y, x ≠ y → Tendsto (fun n => kn n x y) atTop (𝓝 (k x y))) :
    Tendsto (fun n => ∫ x, ∫ y, kn n x y ∂(withDensityReal ρ) ∂(withDensityReal ρ)) atTop
      (𝓝 (∫ x, ∫ y, k x y ∂(withDensityReal ρ) ∂(withDensityReal ρ))) := by
  haveI := isProb_withDensityReal hρ
  refine tendsto_integral_of_dominated_convergence (fun _ => Λ₀ * ∫ z, W z)
    (fun n => ((hm n).stronglyMeasurable.integral_prod_right'
      (ν := withDensityReal ρ)).aestronglyMeasurable)
    (integrable_const _) (fun n => Eventually.of_forall fun x => ?_)
    (Eventually.of_forall fun x => movc_row_tendsto hd hρΛ hW hm hdom hconv x)
  rw [Real.norm_eq_abs]
  refine abs_integral_le_integral_abs.trans ?_
  simpa using (rowOK_of_dom hΛ0 hρΛ hW (hm n) (hdom n)).2 x

theorem movc_modEnergy_tendsto (hd : 1 ≤ d) {ρ : Torus d → ℝ} {Λ₀ : ℝ} (hΛ0 : 0 ≤ Λ₀)
    (hρΛ : ∀ x, ρ x ≤ Λ₀) (hρ : IsProbDensity ρ)
    {W : Torus d → ℝ} (hW : Integrable W) {kn : ℕ → Torus d → Torus d → ℝ}
    {k : Torus d → Torus d → ℝ}
    (hm : ∀ n, Measurable (Function.uncurry (kn n)))
    (hdom : ∀ n x y, |kn n x y| ≤ W (x - y))
    (hconv : ∀ x y, x ≠ y → Tendsto (fun n => kn n x y) atTop (𝓝 (k x y)))
    {X : Config d N} (hX : X ∉ collisionSet d N) :
    Tendsto (fun n => modulatedEnergy (kn n) X (withDensityReal ρ)) atTop
      (𝓝 (modulatedEnergy k X (withDensityReal ρ))) := by
  unfold modulatedEnergy
  refine Tendsto.add (Tendsto.sub ?_ ?_) ?_
  · refine Tendsto.const_mul _ (tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j hj => ?_)
    have hij : i ≠ j := (Finset.mem_erase.mp hj).1.symm
    exact hconv _ _ (fun h => hX ⟨i, j, hij, h⟩)
  · exact Tendsto.const_mul _ (tendsto_finsetSum _ fun i _ =>
      movc_row_tendsto hd hρΛ hW hm hdom hconv (X i))
  · exact Tendsto.const_mul _ (movc_dbl_tendsto hd hΛ0 hρΛ hρ hW hm hdom hconv)

/-- The dominating energy `E_W(X) = F^W(X) + (2/N) ∑_i ∫ W(X_i - y) dμ`. -/
def movc_Emax (W : Torus d → ℝ) (X : Config d N) (μ : Measure (Torus d)) : ℝ :=
  modulatedEnergy (fun x y => W (x - y)) X μ + (2 / (N : ℝ)) * ∑ i, ∫ y, W (X i - y) ∂μ

theorem movc_modEnergy_abs_le {ρ : Torus d → ℝ} {Λ₀ : ℝ} (hΛ0 : 0 ≤ Λ₀) (hρΛ : ∀ x, ρ x ≤ Λ₀)
    (hρ : IsProbDensity ρ)
    {W : Torus d → ℝ} (hW : Integrable W) (hW0 : ∀ z, 0 ≤ W z) (hWm : Measurable W)
    {k : Torus d → Torus d → ℝ} (hm : Measurable (Function.uncurry k))
    (hdom : ∀ x y, |k x y| ≤ W (x - y)) (X : Config d N) :
    |modulatedEnergy k X (withDensityReal ρ)| ≤ movc_Emax W X (withDensityReal ρ) := by
  have := isProb_withDensityReal hρ
  have hrow : ∀ x, |∫ y, k x y ∂(withDensityReal ρ)| ≤ ∫ y, W (x - y) ∂(withDensityReal ρ) := fun x => by
    have := norm_integral_le_of_norm_le (movc_integrable_W_shift hρΛ hW x)
      (f := fun y => k x y) (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]; exact hdom x y)
    simpa [Real.norm_eq_abs] using this
  have hkW : RowOK (withDensityReal ρ) (fun x y => W (x - y)) :=
    (rowOK_of_dom (k := fun x y => W (x - y)) hΛ0 hρΛ hW
      (hWm.comp (measurable_fst.sub measurable_snd))
      (fun x y => by rw [abs_of_nonneg (hW0 _)])).1
  have hdbl : |∫ x, ∫ y, k x y ∂(withDensityReal ρ) ∂(withDensityReal ρ)| ≤
      ∫ x, ∫ y, W (x - y) ∂(withDensityReal ρ) ∂(withDensityReal ρ) := by
    have := norm_integral_le_of_norm_le hkW.integrable_rowInt
      (f := fun x => ∫ y, k x y ∂(withDensityReal ρ)) (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact hrow x)
    simpa [Real.norm_eq_abs] using this
  have hpair : ∀ i j : Fin N, |k (X i) (X j)| ≤ W (X i - X j) := fun i j => hdom _ _
  have hP : |∑ i, ∑ j ∈ Finset.univ.erase i, k (X i) (X j)| ≤
      ∑ i, ∑ j ∈ Finset.univ.erase i, W (X i - X j) :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ =>
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => hpair i j))
  have hS : |∑ i, ∫ y, k (X i) y ∂(withDensityReal ρ)| ≤
      ∑ i, ∫ y, W (X i - y) ∂(withDensityReal ρ) :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hrow (X i))
  unfold movc_Emax modulatedEnergy
  have hc1 : (0 : ℝ) ≤ 1 / (2 * (N : ℝ) ^ 2) := by positivity
  have hc2 : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
  have a1 : |(1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, k (X i) (X j)| ≤
      (1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, W (X i - X j) := by
    rw [abs_mul, abs_of_nonneg hc1]; exact mul_le_mul_of_nonneg_left hP hc1
  have a2 : |(1 / (N : ℝ)) * ∑ i, ∫ y, k (X i) y ∂(withDensityReal ρ)| ≤
      (1 / (N : ℝ)) * ∑ i, ∫ y, W (X i - y) ∂(withDensityReal ρ) := by
    rw [abs_mul, abs_of_nonneg hc2]; exact mul_le_mul_of_nonneg_left hS hc2
  have a3 : |(1 / 2 : ℝ) * ∫ x, ∫ y, k x y ∂(withDensityReal ρ) ∂(withDensityReal ρ)| ≤
      (1 / 2 : ℝ) * ∫ x, ∫ y, W (x - y) ∂(withDensityReal ρ) ∂(withDensityReal ρ) := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    exact mul_le_mul_of_nonneg_left hdbl (by norm_num)
  have e : (2 / (N : ℝ)) * ∑ i, ∫ y, W (X i - y) ∂(withDensityReal ρ) =
      2 * ((1 / (N : ℝ)) * ∑ i, ∫ y, W (X i - y) ∂(withDensityReal ρ)) := by ring
  have hSW : 0 ≤ (1 / (N : ℝ)) * ∑ i, ∫ y, W (X i - y) ∂(withDensityReal ρ) :=
    mul_nonneg hc2 (Finset.sum_nonneg fun i _ => integral_nonneg fun y => hW0 _)
  calc _ ≤ |(1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, k (X i) (X j)| +
        |(1 / (N : ℝ)) * ∑ i, ∫ y, k (X i) y ∂(withDensityReal ρ)| +
        |(1 / 2 : ℝ) * ∫ x, ∫ y, k x y ∂(withDensityReal ρ) ∂(withDensityReal ρ)| := by
        refine (abs_add_le _ _).trans (add_le_add_left (abs_sub _ _) _)
    _ ≤ _ := by rw [e]; linarith

end HRS
