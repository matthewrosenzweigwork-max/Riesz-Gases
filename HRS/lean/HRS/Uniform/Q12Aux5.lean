import HRS.Uniform.Q12Aux4

/-!
# Q12, part 5: Fourier-side control of the heat filter `heatS`
-/

noncomputable section

open MeasureTheory Filter Topology Set
open HRS HRS.CoercAux

namespace HRS.Uniform.Q12

variable {d : ℕ}

lemma q12_sum_choose_le (L : ℕ) : ∑ j ∈ Finset.range L, (L.choose (j + 1) : ℝ) ≤ 2 ^ L := by
  have h := Nat.sum_range_choose L
  have h2 : ∑ i ∈ Finset.range (L + 1), (L.choose i : ℝ) = 2 ^ L := by exact_mod_cast h
  rw [Finset.sum_range_succ'] at h2
  have : (0 : ℝ) ≤ (L.choose 0 : ℝ) := by positivity
  linarith

theorem q12_fourier_heatS (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ Cl : ℝ, 0 ≤ Cl ∧ ∀ {ε : ℝ}, 0 < ε → ∀ {N : ℕ}, 0 < N → ∀ (X : Config d N)
      (μ : Measure (Torus d)) [IsProbabilityMeasure μ] {φ : Torus d → ℝ}, Continuous φ →
      HasFiniteHomSobolev (((d : ℝ) - s) / 2) φ → ∀ L : ℕ,
      |∫ x, heatS L ε φ x ∂(empirical X) - ∫ x, heatS L ε φ x ∂μ| ≤
        2 ^ L * (Real.sqrt (homSobolevSq (((d : ℝ) - s) / 2) φ) *
          Real.sqrt (Cl * Esq d s ε X μ)) := by
  obtain ⟨Cl, hCl0, hCl⟩ := fourier_side_bound hd hs0 hsd
  refine ⟨Cl, hCl0, fun {ε} hε {N} hN X μ _ {φ} hc hhom L => ?_⟩
  haveI := empirical_isProbabilityMeasure hN X
  have hcont : ∀ j : ℕ, Continuous fun x => (-1 : ℝ) ^ j * (L.choose (j + 1) : ℝ) *
      heatP d (((j + 1 : ℕ) : ℝ) * ε) φ x := fun j =>
    continuous_const.mul (heatP_continuous hc (by positivity))
  have hint : ∀ (Q : Measure (Torus d)) [IsFiniteMeasure Q] (j : ℕ), Integrable (fun x =>
      (-1 : ℝ) ^ j * (L.choose (j + 1) : ℝ) * heatP d (((j + 1 : ℕ) : ℝ) * ε) φ x) Q :=
    fun Q _ j => (hcont j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hsplit : ∀ (Q : Measure (Torus d)) [IsFiniteMeasure Q], ∫ x, heatS L ε φ x ∂Q =
      ∑ j ∈ Finset.range L, (-1 : ℝ) ^ j * (L.choose (j + 1) : ℝ) *
        ∫ x, heatP d (((j + 1 : ℕ) : ℝ) * ε) φ x ∂Q := by
    intro Q _
    unfold heatS
    rw [integral_finsetSum _ fun j _ => hint Q j]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
  rw [hsplit (empirical X), hsplit μ, ← Finset.sum_sub_distrib]
  set a := Real.sqrt (homSobolevSq (((d : ℝ) - s) / 2) φ) with ha
  set b := Real.sqrt (Cl * Esq d s ε X μ) with hb
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hterm : ∀ j ∈ Finset.range L,
      |(-1 : ℝ) ^ j * (L.choose (j + 1) : ℝ) *
          ∫ x, heatP d (((j + 1 : ℕ) : ℝ) * ε) φ x ∂(empirical X) -
        (-1 : ℝ) ^ j * (L.choose (j + 1) : ℝ) *
          ∫ x, heatP d (((j + 1 : ℕ) : ℝ) * ε) φ x ∂μ| ≤ (L.choose (j + 1) : ℝ) * (a * b) := by
    intro j _
    have hpos : 0 < ((j + 1 : ℕ) : ℝ) * ε := by positivity
    have h1 := hCl hpos hN X μ hc hhom
    have hle : ε ≤ ((j + 1 : ℕ) : ℝ) * ε := by
      have : (1 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos j
      nlinarith
    have h2 := q12_Esq_anti hd hs0 hsd hε hle hN X μ
    have h3 : Real.sqrt (Cl * Esq d s (((j + 1 : ℕ) : ℝ) * ε) X μ) ≤ b :=
      Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left h2 hCl0)
    rw [← mul_sub, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (L.choose (j + 1) : ℝ))]
    refine mul_le_mul_of_nonneg_left (h1.trans ?_) (by positivity)
    exact mul_le_mul_of_nonneg_left h3 ha0
  calc |∑ j ∈ Finset.range L, _| ≤ ∑ j ∈ Finset.range L, |_| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.range L, (L.choose (j + 1) : ℝ) * (a * b) := Finset.sum_le_sum hterm
    _ = (∑ j ∈ Finset.range L, (L.choose (j + 1) : ℝ)) * (a * b) := by rw [Finset.sum_mul]
    _ ≤ 2 ^ L * (a * b) := mul_le_mul_of_nonneg_right (q12_sum_choose_le L) (mul_nonneg ha0 hb0)

end HRS.Uniform.Q12
