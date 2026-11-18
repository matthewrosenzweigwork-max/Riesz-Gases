import HRS.Whole.Round2

/-!
# S8.2 NormalForm packet A03: the deleted-diagonal canonical identity

Pure finite-sum algebra (Pro packet S82.A03, `S8.2-NormalForm.lean`):
`(√N/2) · centeredPairFunctional h X μ − pairStatistic ((1/2)·r2CenterKernel μ h) X
  = −N^{-3/2} ∑_i ∫ h(X_i,y) dμ + (∬ h dμ dμ)/(2√N)`
for a symmetric `h`.  The definitions `pairSum`, `pairStatistic` are renamed with the prefix `s82n_`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S82N

open HRS HRS.Whole

/-- Ordered pair sum with the deleted diagonal. -/
def s82n_pairSum {d N : ℕ} (F : Euc d → Euc d → ℝ) (X : EucConfig d N) : ℝ :=
  ∑ i, ∑ j ∈ Finset.univ.erase i, F (X i) (X j)

/-- `N^{-3/2}` times the ordered pair sum. -/
def s82n_pairStatistic {d N : ℕ} (F : Euc d → Euc d → ℝ) (X : EucConfig d N) : ℝ :=
  (N : ℝ) ^ (-(3 / 2 : ℝ)) * s82n_pairSum F X

lemma s82n_sum_erase_const {α : Type*} [Fintype α] [DecidableEq α] (c : ℝ) (i : α) :
    ∑ _j ∈ Finset.univ.erase i, c = ((Fintype.card α : ℝ) - 1) * c := by
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
    nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos (Fintype.card α) with h | h
  · exact absurd (Fintype.card_pos_iff.2 ⟨i⟩) (by omega)
  · rw [Nat.cast_sub h]; simp

lemma s82n_double_sum_erase {α : Type*} [Fintype α] [DecidableEq α] (g : α → ℝ) :
    ∑ i : α, ∑ j ∈ Finset.univ.erase i, g j = ((Fintype.card α : ℝ) - 1) * ∑ j, g j := by
  have : ∀ i : α, ∑ j ∈ Finset.univ.erase i, g j = ∑ j, g j - g i := fun i => by
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
  simp only [this, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

lemma s82n_rpow_three_half (N : ℕ) (hN : 1 ≤ N) :
    (N : ℝ) ^ (-(3 / 2 : ℝ)) = 1 / ((N : ℝ) * Real.sqrt N) := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.rpow_neg hpos.le, Real.sqrt_eq_rpow]
  have : (N : ℝ) ^ (3 / 2 : ℝ) = (N : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) := by
    conv_lhs => rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num]
    rw [Real.rpow_add hpos, Real.rpow_one]
  rw [this]; simp [one_div]

theorem s82n_deleted_canonical_identity
    (d N : ℕ) (hN : 1 ≤ N) (mu : Measure (Euc d)) [IsProbabilityMeasure mu]
    (h : Euc d → Euc d → ℝ) (hsym : ∀ x y, h x y = h y x)
    (hrow : ∀ x, Integrable (h x) mu)
    (hint : Integrable (Function.uncurry h) (mu.prod mu))
    (X : EucConfig d N) :
    (Real.sqrt N / 2) * centeredPairFunctional h X mu -
      s82n_pairStatistic (fun x y => (1 / 2) * r2CenterKernel mu h x y) X =
        -(N : ℝ) ^ (-(3 / 2 : ℝ)) * (∑ i, ∫ y, h (X i) y ∂mu) +
          (∫ x, ∫ y, h x y ∂mu ∂mu) / (2 * Real.sqrt N) := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hpos
  have hss : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hpos.le
  set I : ℝ := ∫ x, ∫ y, h x y ∂mu ∂mu with hI
  set hm : Euc d → ℝ := fun x => ∫ y, h x y ∂mu with hhm
  have hcol : ∀ y, ∫ x', h x' y ∂mu = hm y := fun y => by
    simp only [hhm]; exact integral_congr_ae (Filter.Eventually.of_forall fun x => hsym x y)
  have hPS : s82n_pairSum (fun x y => (1 / 2) * r2CenterKernel mu h x y) X =
      (1 / 2) * (∑ i, ∑ j ∈ Finset.univ.erase i, h (X i) (X j)) -
        (((N : ℝ) - 1)) * ∑ i, hm (X i) + ((N : ℝ) * ((N : ℝ) - 1) / 2) * I := by
    unfold s82n_pairSum r2CenterKernel
    have e : ∀ i j, (1 / 2 : ℝ) * (h (X i) (X j) - ∫ y', h (X i) y' ∂mu -
        ∫ x', h x' (X j) ∂mu + I) =
        (1 / 2) * h (X i) (X j) - (1 / 2) * hm (X i) - (1 / 2) * hm (X j) + (1 / 2) * I := by
      intro i j; rw [hcol]; simp only [hhm]; ring
    have S2 : ∑ i, ∑ _j ∈ Finset.univ.erase i, hm (X i) = ((N : ℝ) - 1) * ∑ i, hm (X i) := by
      simp only [s82n_sum_erase_const, Fintype.card_fin]
      rw [← Finset.mul_sum]
    have S3 : ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, hm (X j) =
        ((N : ℝ) - 1) * ∑ i, hm (X i) := by
      have := s82n_double_sum_erase (fun j : Fin N => hm (X j))
      simpa only [Fintype.card_fin] using this
    have S4 : ∑ i : Fin N, ∑ _j ∈ Finset.univ.erase i, I = (N : ℝ) * ((N : ℝ) - 1) * I := by
      simp only [s82n_sum_erase_const, Fintype.card_fin]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => e i j))]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [S2, S3, S4]
    ring
  unfold s82n_pairStatistic centeredPairFunctional
  rw [hPS, s82n_rpow_three_half N hN]
  have e1 : (1 / (N : ℝ)) * ∑ i, ∫ y, h (X i) y ∂mu = (1 / (N : ℝ)) * ∑ i, hm (X i) := rfl
  rw [e1]
  set s := Real.sqrt N with hsdef
  rw [← hss]
  field_simp
  ring

end HRS.MS.S82N
