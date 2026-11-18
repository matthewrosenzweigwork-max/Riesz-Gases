import HRS.MS.SA16Y4Mb1
import HRS.MS.SA16JetSchwartz

/-!
# S.A.16 (SA16Y4) Mb2: uniform derivative and growth bounds of the mollified field

For a mollifier `ρ ≥ 0`, `∫ρ = 1`, `supp ρ ⊂ closedBall 0 1` (any `ρ_n`) and `b ∈ C^k` with `‖D^j b‖ ≤ L` (`1 ≤ j ≤ k`):
`sa16y4_mol_iter_bound`: `‖D^j (ρ ⋆ b)(x)‖ ≤ d^j L` for `1 ≤ j ≤ k`, independent of `ρ`;
`sa16y4_mol_growth`: `|b y| ≤ A + L‖y‖ → |(ρ ⋆ b) x| ≤ A + L (‖x‖ + 1)`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal ContDiff Convolution

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16

section Mb2
variable {d : ℕ}

lemma sa16y4_shift_integral {ρ : EuclideanSpace ℝ (Fin d) → ℝ} (hρ1 : ∫ z, ρ z = 1) (x : EuclideanSpace ℝ (Fin d)) :
    ∫ y, ρ (x - y) = 1 := by
  rw [integral_sub_left_eq_self (fun z => ρ z) volume x]; exact hρ1

lemma sa16y4_mol_pd_bound {ρ : EuclideanSpace ℝ (Fin d) → ℝ} (hρ : IsCcInfty ρ) (hρ0 : ∀ z, 0 ≤ ρ z)
    (hρ1 : ∫ z, ρ z = 1) {b : EuclideanSpace ℝ (Fin d) → ℝ} {j : ℕ} (hb : ContDiff ℝ (j : WithTop ℕ∞) b)
    (κ : Fin j → Fin d) {L : ℝ} (hL : ∀ x, |partialDeriv κ b x| ≤ L) (x : EuclideanSpace ℝ (Fin d)) :
    |partialDeriv κ (fun x => ∫ y, b y * ρ (x - y)) x| ≤ L := by
  rw [sa16y4_mol_pd hρ j b hb κ]
  have hρi : Integrable (fun y => ρ (x - y)) := (sa16y4_cc_shift hρ x |> fun h =>
    (hρ.1.continuous.comp (continuous_const.sub continuous_id)).integrable_of_hasCompactSupport h)
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL x)
  have := norm_integral_le_of_norm_le (hρi.const_mul L) (μ := volume)
    (f := fun y => partialDeriv κ b y * ρ (x - y)) (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 _)]
      exact mul_le_mul_of_nonneg_right (hL y) (hρ0 _))
  rw [integral_const_mul, sa16y4_shift_integral hρ1 x, mul_one] at this
  simpa [Real.norm_eq_abs] using this

lemma sa16y4_mol_iter_bound {ρ : EuclideanSpace ℝ (Fin d) → ℝ} (hρ : IsCcInfty ρ) (hρ0 : ∀ z, 0 ≤ ρ z)
    (hρ1 : ∫ z, ρ z = 1) {k : ℕ} {b : EuclideanSpace ℝ (Fin d) → ℝ} (hb : ContDiff ℝ (k : WithTop ℕ∞) b) {L : ℝ}
    (hL : ∀ j, 1 ≤ j → j ≤ k → ∀ x, ‖iteratedFDeriv ℝ j b x‖ ≤ L) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (x : EuclideanSpace ℝ (Fin d)) :
    ‖iteratedFDeriv ℝ j (fun x => ∫ y, b y * ρ (x - y)) x‖ ≤ (d : ℝ) ^ j * L := by
  refine (sa16j_norm_iter_le _ x j).trans ?_
  have hbj : ContDiff ℝ (j : WithTop ℕ∞) b := hb.of_le (by exact_mod_cast hjk)
  calc ∑ r : Fin j → Fin d, |partialDeriv r (fun x => ∫ y, b y * ρ (x - y)) x|
      ≤ ∑ r : Fin j → Fin d, L :=
        Finset.sum_le_sum fun r _ => sa16y4_mol_pd_bound hρ hρ0 hρ1 hbj r
          (fun y => (sa16y_pd_le_iter b y r).trans (hL j hj1 hjk y)) x
    _ = (d : ℝ) ^ j * L := by simp [Finset.sum_const]

lemma sa16y4_mol_growth {ρ : EuclideanSpace ℝ (Fin d) → ℝ} (hρ : IsCcInfty ρ) (hρ0 : ∀ z, 0 ≤ ρ z)
    (hρ1 : ∫ z, ρ z = 1) (hρs : ∀ z, 1 < ‖z‖ → ρ z = 0) {b : EuclideanSpace ℝ (Fin d) → ℝ} {A L : ℝ}
    (hA : ∀ y, |b y| ≤ A + L * ‖y‖) (hL0 : 0 ≤ L) (x : EuclideanSpace ℝ (Fin d)) :
    |∫ y, b y * ρ (x - y)| ≤ A + L * (‖x‖ + 1) := by
  have hρi : Integrable (fun y => ρ (x - y)) :=
    (hρ.1.continuous.comp (continuous_const.sub continuous_id)).integrable_of_hasCompactSupport (sa16y4_cc_shift hρ x)
  have := norm_integral_le_of_norm_le (hρi.const_mul (A + L * (‖x‖ + 1))) (μ := volume)
    (f := fun y => b y * ρ (x - y)) (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 _)]
      by_cases hz : 1 < ‖x - y‖
      · rw [hρs _ hz]; simp
      · refine mul_le_mul_of_nonneg_right ((hA y).trans ?_) (hρ0 _)
        have h1 : ‖y‖ ≤ ‖x‖ + ‖x - y‖ := by
          calc ‖y‖ = ‖x - (x - y)‖ := by congr 1; abel
            _ ≤ ‖x‖ + ‖x - y‖ := norm_sub_le _ _
        have h2 : ‖x - y‖ ≤ 1 := not_lt.1 hz
        nlinarith)
  rw [integral_const_mul, sa16y4_shift_integral hρ1 x, mul_one] at this
  simpa [Real.norm_eq_abs] using this

end Mb2

end HRS.Whole.AppendixA.Phase2SA16R
