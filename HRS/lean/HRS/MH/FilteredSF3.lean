import HRS.Torus.Basic

/-!
# Packet SF3 `sf3_block_iter_norm` (Pythagoras for iterated derivatives of an orthogonal block)

Statement copied verbatim from `HRS/MH/FilteredSpec.lean` (namespace `HRS.MH.Filtered` there, `HRS.MH.FilteredP` here).
Imports only the repo module `HRS.Torus.Basic` (vocabulary: `Torus`, `Euc`, `Lattice`, `NonzeroLattice`, `summable_jp_rpow`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MH.FilteredP

open HRS

variable {d : ℕ}

/-- **SF3** (size M, about 100 lines).  Pythagoras for the derivatives of a finite orthogonal
block: if `e` is orthonormal and each scalar `g k` has `‖D^i (g k) y‖ ≤ B k`, then
`‖D^i (∑_{k ∈ I} g k • e k) y‖ ≤ (∑_{k ∈ I} B k ^ 2)^{1/2}`.
Route: `iteratedFDeriv_sum` (`ContDiff` of each `g k •  e k` from `hg`), `ContinuousLinearMap.iteratedFDeriv_comp_left` with
`ContinuousLinearMap.toSpanSingleton ℝ (e k)` (pattern of `gfb3_norm_iter_term`, `HRS/Main/GFB3Aux1.lean:89`), then for a fixed
argument tuple `m`: `‖∑ φ_k m • e k‖^2 = ∑ (φ_k m)^2 ≤ (∑ B k ^2) ∏‖m_i‖^2` by `Orthonormal.inner_sum` /
`norm_sq_eq_sum` for orthonormal families and `ContinuousMultilinearMap.opNorm_le_bound`. -/
theorem sf3_block_iter_norm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {ι : Type*}
    (e : ι → E) (he : Orthonormal ℝ e) (I : Finset ι) (g : ι → Euc d → ℝ) (n : ℕ)
    (hg : ∀ k, ContDiff ℝ n (g k)) (B : ι → ℝ) (i : ℕ) (hi : i ≤ n)
    (hB : ∀ k y, ‖iteratedFDeriv ℝ i (g k) y‖ ≤ B k) (y : Euc d) :
    ‖iteratedFDeriv ℝ i (fun z => ∑ k ∈ I, g k z • e k) y‖ ≤ Real.sqrt (∑ k ∈ I, B k ^ 2) := by
  classical
  have hS0 : 0 ≤ ∑ k ∈ I, B k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hc : ∀ k, ContDiff ℝ i (fun z => g k z • e k) := fun k =>
    ((hg k).of_le (by exact_mod_cast hi)).smul contDiff_const
  have hsum_eq : iteratedFDeriv ℝ i (fun z => ∑ k ∈ I, g k z • e k) y =
      ∑ k ∈ I, (ContinuousLinearMap.toSpanSingleton ℝ (e k)).compContinuousMultilinearMap
        (iteratedFDeriv ℝ i (g k) y) := by
    rw [iteratedFDeriv_fun_sum_apply (x := y) (fun k _ => (hc k).contDiffAt)]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h := ContinuousLinearMap.iteratedFDeriv_comp_left (ContinuousLinearMap.toSpanSingleton ℝ (e k))
      ((hg k).contDiffAt : ContDiffAt ℝ n (g k) y) (by exact_mod_cast hi)
    exact h
  have hmain : ‖∑ k ∈ I, (ContinuousLinearMap.toSpanSingleton ℝ (e k)).compContinuousMultilinearMap
      (iteratedFDeriv ℝ i (g k) y)‖ ≤ Real.sqrt (∑ k ∈ I, B k ^ 2) := by
    apply ContinuousMultilinearMap.opNorm_le_bound (Real.sqrt_nonneg _)
    intro m
    rw [_root_.sum_apply]
    have hP0 : 0 ≤ ∏ j, ‖m j‖ := Finset.prod_nonneg fun j _ => norm_nonneg _
    have hterm : ∑ k ∈ I, ((ContinuousLinearMap.toSpanSingleton ℝ (e k)).compContinuousMultilinearMap
        (iteratedFDeriv ℝ i (g k) y)) m
        = ∑ k ∈ I, (iteratedFDeriv ℝ i (g k) y m) • e k :=
      Finset.sum_congr rfl fun k _ => rfl
    rw [hterm]
    have hbound : ∀ k ∈ I, |iteratedFDeriv ℝ i (g k) y m| ≤ B k * ∏ j, ‖m j‖ := by
      intro k _
      have h1 := (iteratedFDeriv ℝ i (g k) y).le_opNorm m
      have h2 := hB k y
      rw [← Real.norm_eq_abs]
      exact h1.trans (mul_le_mul_of_nonneg_right h2 hP0)
    have hsq : ‖∑ k ∈ I, (iteratedFDeriv ℝ i (g k) y m) • e k‖ ^ 2
        = ∑ k ∈ I, (iteratedFDeriv ℝ i (g k) y m) ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, he.inner_sum _ _ I]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [sq]
    have hsq2 : ∑ k ∈ I, (iteratedFDeriv ℝ i (g k) y m) ^ 2
        ≤ (∏ j, ‖m j‖) ^ 2 * ∑ k ∈ I, B k ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun k hk => ?_
      calc (iteratedFDeriv ℝ i (g k) y m) ^ 2
          = |iteratedFDeriv ℝ i (g k) y m| ^ 2 := (sq_abs _).symm
        _ ≤ (B k * ∏ j, ‖m j‖) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hbound k hk) 2
        _ = (∏ j, ‖m j‖) ^ 2 * B k ^ 2 := by ring
    calc ‖∑ k ∈ I, (iteratedFDeriv ℝ i (g k) y m) • e k‖
        = Real.sqrt (‖∑ k ∈ I, (iteratedFDeriv ℝ i (g k) y m) • e k‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt ((∏ j, ‖m j‖) ^ 2 * ∑ k ∈ I, B k ^ 2) :=
          Real.sqrt_le_sqrt (by rw [hsq]; exact hsq2)
      _ = (∏ j, ‖m j‖) * Real.sqrt (∑ k ∈ I, B k ^ 2) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hP0]
      _ = Real.sqrt (∑ k ∈ I, B k ^ 2) * ∏ j, ‖m j‖ := mul_comm _ _
  rw [hsum_eq]
  exact hmain

end HRS.MH.FilteredP
