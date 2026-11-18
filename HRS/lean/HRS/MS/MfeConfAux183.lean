import HRS.MS.MfeConfAux182

/-!
# S.B.1 (SB5), R1b (part 4): the remainder bound from the smallness of the force defect

`sb1_B_bound`: if the force defect `e = u^k - v` satisfies `E0` (`|e| ≤ ε w_{d+3}`), `E1` (`|div`-type sum`| ≤ ε`) and `E2`
(`e` is `ε`-Lipschitz) then `|B^k_r(Z)| ≤ ε (1+K(r)) (A₃ (P_k + ℓ) + A₄)` with `A₃, A₄` independent of `k, ε, r, Z`.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d N : ℕ}

section Main

variable {D : Whole.WholeDyn d} {T C B C3 : ℝ} {ρ : ℝ → Euc d → ℝ} (H : Sb1Tr3 D T C B C3 ρ)

include H

theorem sb1_B_bound (hT : 0 < T) (hN : 1 ≤ N) (hβ : 0 < D.invβ) (Kf : ℝ → ℝ)
    (hLip : ∀ t ∈ Set.Icc (0 : ℝ) T, Whole.HasLipBoundW (Whole.mfeTransportW D (ρ t)) (Kf t))
    {Ak ε1 : ℝ} (hAk : 0 < Ak) (hε1 : 0 ≤ ε1) :
    ∃ A3 A4 : ℝ, 0 < A3 ∧ 0 ≤ A4 ∧ ∀ (r₀ : ℝ) (k : Euc d → ℝ) (ε : ℝ), IsP4Kernel d D.s r₀ k →
      (∀ z, ‖z‖ * ‖gradient k z‖ ≤ Ak * (k z + Real.log (1 + ‖z‖) + 1)) → 0 ≤ ε → ε ≤ ε1 →
      (∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x, ‖sb1_lv_e D k hT.le ρ r x‖ ≤ ε * sb1w ((d : ℝ) + 3) x) →
      (∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x, |∑ j, sb1_lv_cv (sb1_lv_hjj k j) (ρ r) x -
        ∑ j, fderiv ℝ (sb1F d D.s (ρ r) j) x (sb1e j)| ≤ ε) →
      (∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x y, ‖sb1_lv_e D k hT.le ρ r x - sb1_lv_e D k hT.le ρ r y‖ ≤ ε * ‖x - y‖) →
      ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ Z : EucConfig d N,
        |sb1_lv_B (N := N) D k hT.le ρ r Z| ≤ ε * (1 + Kf r) * (A3 * (sb1PM k N Z + sb1ell d N Z) + A4) := by
  obtain ⟨V0, hV00, hV0⟩ := sb1_V0 H hT.le
  have hVB := H.tr.V
  have hB0 : 0 ≤ B := hVB.B_nonneg
  have hθi : 0 < D.invβ⁻¹ := inv_pos.2 hβ
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hG0 := norm_nonneg (fderiv ℝ D.V 0)
  set A1 : ℝ := 1 + D.invβ⁻¹ * d * (V0 + ‖fderiv ℝ D.V 0‖ + ε1 + B + 1) with hA1
  have hA10 : 0 ≤ A1 := by rw [hA1]; positivity
  refine ⟨D.invβ⁻¹ * N * Ak + 1, N * A1, by positivity, by positivity, ?_⟩
  intro r₀ k ε hk4 henv hε0 hε1' E0 E1 E2 r hr Z
  obtain ⟨hK0, hL⟩ := sb1_lip_of_hasLip (hLip r hr)
  have hrb : sb1_lv_rb hT.le ρ r = ρ r := sb1_lv_rb_mem hT.le ρ hr
  obtain ⟨hPl, hPb⟩ := sb1_pair_bound hk4 H.tr.hs0 hN hAk henv (sb1_lv_e D k hT.le ρ r) hε0 (E2 r hr) Z
  have hone : ∀ i, |sb1_lv_Bone D k hT.le ρ r (Z i)| ≤ ε * (1 + Kf r) * A1 := fun i =>
    sb1_Bone_bound H hT.le hk4 hβ hr (hV0 r hr) hK0 hL hε0 hε1' (E0 r hr) (E1 r hr) (Z i)
  have hBeq : sb1_lv_B (N := N) D k hT.le ρ r Z = ∑ i, sb1_lv_Bone D k hT.le ρ r (Z i) -
      (∑ i, sb1_lv_pairV (gradient k) (sb1_lv_e D k hT.le ρ r) Z i) / D.invβ := by
    unfold sb1_lv_B sb1_lv_Bpair
    rw [Finset.sum_add_distrib, Finset.sum_div, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    simp only [neg_div]
  rw [hBeq]
  have h1 : |∑ i, sb1_lv_Bone D k hT.le ρ r (Z i)| ≤ N * (ε * (1 + Kf r) * A1) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => hone i).trans (le_of_eq ?_)
    simp
  have h2 : |(∑ i, sb1_lv_pairV (gradient k) (sb1_lv_e D k hT.le ρ r) Z i) / D.invβ| ≤
      D.invβ⁻¹ * (N * ε * Ak * (sb1PM k N Z + sb1ell d N Z)) := by
    rw [div_eq_inv_mul, abs_mul, abs_of_nonneg hθi.le]
    exact mul_le_mul_of_nonneg_left hPb hθi.le
  have hK1 : 1 ≤ 1 + Kf r := by linarith
  calc |∑ i, sb1_lv_Bone D k hT.le ρ r (Z i) -
        (∑ i, sb1_lv_pairV (gradient k) (sb1_lv_e D k hT.le ρ r) Z i) / D.invβ|
      ≤ N * (ε * (1 + Kf r) * A1) + D.invβ⁻¹ * (N * ε * Ak * (sb1PM k N Z + sb1ell d N Z)) :=
        (abs_sub _ _).trans (add_le_add h1 h2)
    _ ≤ ε * (1 + Kf r) * ((D.invβ⁻¹ * N * Ak + 1) * (sb1PM k N Z + sb1ell d N Z) + N * A1) := by
        have hP := hPl
        have e1 : D.invβ⁻¹ * (N * ε * Ak * (sb1PM k N Z + sb1ell d N Z)) =
            ε * (D.invβ⁻¹ * N * Ak) * (sb1PM k N Z + sb1ell d N Z) := by ring
        rw [e1]
        have e2 : ε * (D.invβ⁻¹ * N * Ak) * (sb1PM k N Z + sb1ell d N Z) ≤
            ε * (1 + Kf r) * ((D.invβ⁻¹ * N * Ak + 1) * (sb1PM k N Z + sb1ell d N Z)) := by
          have h0 : 0 ≤ ε * (sb1PM k N Z + sb1ell d N Z) := mul_nonneg hε0 hP
          have h3 : 0 ≤ D.invβ⁻¹ * N * Ak := by positivity
          nlinarith [mul_nonneg h0 h3, mul_nonneg (mul_nonneg h0 h3) hK0, mul_nonneg h0 hK0]
        nlinarith [e2]

end Main

end HRS.MS.MfeConf
