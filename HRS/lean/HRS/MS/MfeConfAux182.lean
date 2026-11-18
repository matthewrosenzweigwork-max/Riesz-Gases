import HRS.MS.MfeConfAux181

/-!
# S.B.1 (SB5), R1b (part 3): the pair part of the remainder

`sb1_pair_bound`: if `e` is `ε`-Lipschitz and `|z||∇k(z)| ≤ A_k (k + log(1+|z|) + 1)` then
`|∑_i ⟨e(Z_i), N⁻¹ ∑_{j≠i} ∇k(Z_i - Z_j)⟩| ≤ N ε A_k (P_M(Z) + ℓ(Z))` and `P_M + ℓ ≥ 0`.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d N : ℕ}

theorem sb1_pair_bound {s r₀ : ℝ} {k : Euc d → ℝ} (hk4 : IsP4Kernel d s r₀ k) (hs0 : 0 ≤ s) (hN : 1 ≤ N) {Ak : ℝ}
    (hAk : 0 < Ak) (henv : ∀ z, ‖z‖ * ‖gradient k z‖ ≤ Ak * (k z + Real.log (1 + ‖z‖) + 1))
    (e : Euc d → Euc d) {ε : ℝ} (hε : 0 ≤ ε) (he : ∀ x y, ‖e x - e y‖ ≤ ε * ‖x - y‖) (Z : EucConfig d N) :
    0 ≤ sb1PM k N Z + sb1ell d N Z ∧
      |∑ i, sb1_lv_pairV (gradient k) e Z i| ≤ N * ε * Ak * (sb1PM k N Z + sb1ell d N Z) := by
  obtain ⟨Lg, hRg⟩ := sb1_lv_kerR hk4 hs0
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hterm0 : ∀ z, 0 ≤ k z + Real.log (1 + ‖z‖) + 1 := fun z => by
    have := henv z
    have h2 : 0 ≤ ‖z‖ * ‖gradient k z‖ := by positivity
    by_contra hneg
    push Not at hneg
    nlinarith
  have hsumE : sb1PM k N Z + sb1ell d N Z =
      (1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, (k (Z i - Z j) + Real.log (1 + ‖Z i - Z j‖) + 1) := by
    unfold sb1PM sb1ell
    rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  refine ⟨?_, ?_⟩
  · rw [hsumE]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hterm0 _)
  · rw [sb1_lv_pairV_sum, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ))]
    have hsym := sb1_lv_pair_sym hRg e Z
    have hS : ∑ i, ∑ j ∈ Finset.univ.erase i, fderiv ℝ k (Z i - Z j) (e (Z i)) =
        (1 / 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, fderiv ℝ k (Z i - Z j) (e (Z i) - e (Z j)) := by
      rw [hsym]; ring
    rw [hS, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have hpt : ∀ i, ∀ j ∈ Finset.univ.erase i, |fderiv ℝ k (Z i - Z j) (e (Z i) - e (Z j))| ≤
        ε * Ak * (k (Z i - Z j) + Real.log (1 + ‖Z i - Z j‖) + 1) := by
      intro i j _
      rw [← p4k_inner_grad, ← Real.norm_eq_abs]
      calc ‖inner ℝ (gradient k (Z i - Z j)) (e (Z i) - e (Z j))‖
          ≤ ‖gradient k (Z i - Z j)‖ * ‖e (Z i) - e (Z j)‖ := norm_inner_le_norm _ _
        _ ≤ ‖gradient k (Z i - Z j)‖ * (ε * ‖Z i - Z j‖) :=
            mul_le_mul_of_nonneg_left (he _ _) (norm_nonneg _)
        _ = ε * (‖Z i - Z j‖ * ‖gradient k (Z i - Z j)‖) := by ring
        _ ≤ ε * (Ak * (k (Z i - Z j) + Real.log (1 + ‖Z i - Z j‖) + 1)) :=
            mul_le_mul_of_nonneg_left (henv _) hε
        _ = _ := by ring
    have hb : |∑ i, ∑ j ∈ Finset.univ.erase i, fderiv ℝ k (Z i - Z j) (e (Z i) - e (Z j))| ≤
        ε * Ak * ∑ i, ∑ j ∈ Finset.univ.erase i, (k (Z i - Z j) + Real.log (1 + ‖Z i - Z j‖) + 1) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun j hj => hpt i j hj
    have hE : ∑ i, ∑ j ∈ Finset.univ.erase i, (k (Z i - Z j) + Real.log (1 + ‖Z i - Z j‖) + 1) =
        (2 * (N : ℝ) ^ 2) * (sb1PM k N Z + sb1ell d N Z) := by
      rw [hsumE]; field_simp
    rw [hE] at hb
    calc 1 / (N : ℝ) * (1 / 2 * |∑ i, ∑ j ∈ Finset.univ.erase i, fderiv ℝ k (Z i - Z j) (e (Z i) - e (Z j))|)
        ≤ 1 / (N : ℝ) * (1 / 2 * (ε * Ak * ((2 * (N : ℝ) ^ 2) * (sb1PM k N Z + sb1ell d N Z)))) := by
          gcongr
      _ = _ := by field_simp
