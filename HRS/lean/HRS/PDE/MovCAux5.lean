import HRS.PDE.MovCAux4

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem movc_energy_lower (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hN : 1 ≤ N)
    {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) (hc : Continuous ρ) :
    ∃ c : ℝ, ∀ M : ℝ, 0 ≤ M → ∀ X : Config d N,
      -c ≤ modulatedEnergyKernel (b15c_gReg d s M) X (withDensityReal ρ) := by
  obtain ⟨C, -, hC⟩ := exists_abs_bound hc
  obtain ⟨B, Cb, hB0, hB, hCb0, hCb⟩ := movc_conv_bound hd hs0 hsd hC
  haveI := isProb_withDensityReal hρ
  refine ⟨B / 2 + Cb + Cb / 2, fun M hM X => ?_⟩
  rw [movc_energy_eq _ hρ.measurable hρ.nonneg]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hge := b15c_gReg_ge (d := d) s hB0 hM hB
  have h1 : ∀ i : Fin N, -((N : ℝ) * B) ≤
      ∑ j ∈ Finset.univ.erase i, b15c_gReg d s M (X i - X j) := by
    intro i
    calc -((N : ℝ) * B) ≤ ∑ j ∈ Finset.univ.erase i, (-B) := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem (Finset.mem_univ i)]
          simp only [Finset.card_univ, Fintype.card_fin]
          have : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
          nlinarith
      _ ≤ _ := Finset.sum_le_sum fun j _ => hge _
  have h2 : -((N : ℝ) * ((N : ℝ) * B)) ≤
      ∑ i, ∑ j ∈ Finset.univ.erase i, b15c_gReg d s M (X i - X j) := by
    calc -((N : ℝ) * ((N : ℝ) * B)) = ∑ i : Fin N, (-((N : ℝ) * B)) := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => h1 i
  have h3 : ∑ i, convFun (b15c_gReg d s M) ρ (X i) ≤ (N : ℝ) * Cb := by
    calc _ ≤ ∑ i : Fin N, Cb := Finset.sum_le_sum fun i _ => (le_abs_self _).trans ((hCb _).2 M hM)
      _ = _ := by simp
  have h4 : -Cb ≤ ∫ x, convFun (b15c_gReg d s M) ρ x ∂(withDensityReal ρ) := by
    have := norm_integral_le_of_norm_le_const (μ := withDensityReal ρ) (C := Cb)
      (f := fun x => convFun (b15c_gReg d s M) ρ x)
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact (hCb x).2 M hM)
    rw [Real.norm_eq_abs] at this
    simp at this
    linarith [neg_abs_le (∫ x, convFun (b15c_gReg d s M) ρ x ∂(withDensityReal ρ))]
  have hP : -(B / 2) ≤ (1 / (2 * (N : ℝ) ^ 2)) *
      ∑ i, ∑ j ∈ Finset.univ.erase i, b15c_gReg d s M (X i - X j) := by
    have : -(B / 2) = (1 / (2 * (N : ℝ) ^ 2)) * (-((N : ℝ) * ((N : ℝ) * B))) := by
      field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have hS : (1 / (N : ℝ)) * ∑ i, convFun (b15c_gReg d s M) ρ (X i) ≤ Cb := by
    calc _ ≤ (1 / (N : ℝ)) * ((N : ℝ) * Cb) := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = Cb := by field_simp
  linarith


theorem movc_energy_tendsto (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) (hc : Continuous ρ) {M : ℕ → ℝ}
    (hM : Tendsto M atTop atTop) (hM0 : ∀ n, 0 ≤ M n) {X : Config d N} (hX : X ∉ collisionSet d N) :
    Tendsto (fun n => modulatedEnergyKernel (b15c_gReg d s (M n)) X (withDensityReal ρ)) atTop
      (𝓝 (modulatedEnergyKernel (periodicRiesz d s) X (withDensityReal ρ))) := by
  obtain ⟨C, -, hC⟩ := exists_abs_bound hc
  obtain ⟨B, Cb, hB0, hB, hCb0, hCb⟩ := movc_conv_bound hd hs0 hsd hC
  haveI := isProb_withDensityReal hρ
  have hU' := movc_convFun_tendstoUniformly hd hs0 hsd hM hM0 hc
  simp_rw [movc_energy_eq _ hρ.measurable hρ.nonneg]
  refine Tendsto.add (Tendsto.sub ?_ ?_) ?_
  · refine Tendsto.const_mul _ (tendsto_finset_sum _ fun i _ => tendsto_finset_sum _ fun j hj => ?_)
    have hij : i ≠ j := (Finset.mem_erase.mp hj).1.symm
    exact movc_gReg_tendsto_pt hM (sub_ne_zero.mpr fun h => hX ⟨i, j, hij, h⟩)
  · exact Tendsto.const_mul _ (tendsto_finset_sum _ fun i _ => hU'.tendsto_at (X i))
  · refine Tendsto.const_mul _ ?_
    have hgm := CoercAux.measurable_periodicRiesz_one hd hs0 hsd
    refine tendsto_integral_of_dominated_convergence (fun _ => Cb)
      (fun n => (movc_convFun_measurable (movc_gReg_measurable hd hs0 hsd (M n)).measurable
        hρ.measurable).aestronglyMeasurable) (integrable_const Cb) (fun n => ?_) ?_
    · exact Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact (hCb x).2 (M n) (hM0 n)
    · exact Eventually.of_forall fun x => hU'.tendsto_at x

end HRS
