import HRS.MC.D47Aux2

/-!
# Packet D47, auxiliary facts 3: energy of spectral kernels.

* `modE (specKernel a) ≥ -specKernel a 0 / (2N)` for `a ≥ 0` summable (from `energy_identity`);
* `modE (-g) = - modE g`;
* `modE (g - c) = modE g + c/(2N)` for continuous `g` and a probability measure.
-/

noncomputable section

open MeasureTheory Filter Topology Set

namespace HRS.MC.D47

open HRS HRS.StaticLimitAux

variable {d : ℕ}

lemma d47_modE_spec_lower {a : Lattice d → ℝ} (ha0 : ∀ k, 0 ≤ a k) (has : Summable a)
    (μ : Measure (Torus d)) [IsProbabilityMeasure μ] {N : ℕ} (hN : 1 ≤ N) (X : Fin N → Torus d) :
    -(specKernel a 0) / (2 * N) ≤ modE (specKernel a) N X μ := by
  have h := HRS.StaticLimitAux.energy_identity (0 : ℝ) ha0 has μ N hN X
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have key : -(1 / 2) * specKernel a 0 ≤ (N : ℝ) * modE (specKernel a) N X μ := by
    rw [h]
    have := mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (sq_nonneg ‖(Ssum (Yj (0 : ℝ) ha0 has μ) N X).snd‖)
    linarith
  rw [div_le_iff₀ (by positivity)]
  nlinarith

lemma d47_modE_neg (g : Torus d → ℝ) (N : ℕ) (X : Fin N → Torus d) (μ : Measure (Torus d)) :
    modE (fun x => -g x) N X μ = -modE g N X μ := by
  unfold modE
  simp only [Finset.sum_neg_distrib, integral_neg]
  ring

lemma d47_modE_sub_const {g : Torus d → ℝ} (hg : Continuous g) (c : ℝ) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] {N : ℕ} (hN : 1 ≤ N) (X : Fin N → Torus d) :
    modE (fun x => g x - c) N X μ = modE g N X μ + c / (2 * N) := by
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have hint : ∀ x : Torus d, Integrable (fun y => g (x - y)) μ := fun x =>
    (hg.comp (continuous_const.sub continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hμ : μ.real Set.univ = 1 := by simp [Measure.real]
  have e1 : ∀ x : Torus d, ∫ y, (g (x - y) - c) ∂μ = ∫ y, g (x - y) ∂μ - c := by
    intro x
    rw [integral_sub (hint x) (integrable_const c), integral_const, hμ]
    simp
  have hcont := HRS.continuous_conv0 hg μ
  have hint2 : Integrable (fun x => ∫ y, g (x - y) ∂μ) μ :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  unfold modE
  simp only [e1]
  rw [integral_sub hint2 (integrable_const c), integral_const, hμ]
  have h1 : ∀ i : Fin N, ∑ j ∈ Finset.univ.erase i, (g (X i - X j) - c) =
      ∑ j ∈ Finset.univ.erase i, g (X i - X j) - ((N : ℝ) - 1) * c := by
    intro i
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Nat.cast_sub hN]; simp
  simp only [h1, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  simp
  field_simp
  ring

end HRS.MC.D47
