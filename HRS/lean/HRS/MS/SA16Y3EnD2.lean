import HRS.MS.SA16SEn1
import HRS.MS.SA16Y3Dc1

/-!
# S.A.16 (SA16Y3) EnD2: the commutator bound with derivative-only hypotheses (copy of `sa16sy_comm_term`)

The only change from `sa16sy_comm_term` (SA16SEn2) is that the sign `0 ≤ B` is an explicit hypothesis
instead of being derived from the zeroth-order bound `hbb 0`. The bound `hbb` is required only for `1 ≤ i ≤ k`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section EnD2
variable {d : ℕ}

lemma sa16y3_sy_comm_termD {k : ℕ} {B : ℝ} {b : Euc d → ℝ} (hbs : ContDiff ℝ ∞ b)
    (hbb : ∀ i, 1 ≤ i → i ≤ k → ∀ y, ‖iteratedFDeriv ℝ i b y‖ ≤ B) (hB0 : 0 ≤ B) {φ : Euc d → ℝ} (hφ : ContDiff ℝ ∞ φ) (l : Fin d)
    {j : ℕ} (hj : j ≤ k) (idx : Fin j → Fin d) (x : Euc d) :
    |partialDeriv idx (fun y => (b y - b x) * fderiv ℝ φ y (EuclideanSpace.single l 1)) x| ≤
      2 ^ j * (B * ((d : ℝ) + 1) ^ j) * ‖wJet j φ x‖ := by
  have hJ0 := norm_nonneg (wJet j φ x)
  have hcs : ContDiff ℝ ∞ (fun y => b y - b x) := hbs.sub contDiff_const
  have hgs := sa16so_dir_smooth hφ (EuclideanSpace.single l 1)
  refine (sa16y_pd_le_iter _ x idx).trans ?_
  have hL := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (hcs.of_le (by exact_mod_cast le_top))
    (hgs.of_le (by exact_mod_cast le_top)) x (n := j) (N := (j : ℕ∞ω)) le_rfl
  refine hL.trans ?_
  have hterm : ∀ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y => b y - b x) x‖ *
      ‖iteratedFDeriv ℝ (j - i) (fun y => fderiv ℝ φ y (EuclideanSpace.single l 1)) x‖ ≤
      (j.choose i : ℝ) * (B * (((d : ℝ) + 1) ^ j * ‖wJet j φ x‖)) := by
    intro i hi
    have hi' : i ≤ j := by have := Finset.mem_range.1 hi; omega
    have hc : (0 : ℝ) ≤ j.choose i := Nat.cast_nonneg _
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      simp only [norm_iteratedFDeriv_zero, sub_self, norm_zero, mul_zero, zero_mul]
      positivity
    · have h1 : ‖iteratedFDeriv ℝ i (fun y => b y - b x) x‖ ≤ B := by
        have := iteratedFDeriv_sub_apply (𝕜 := ℝ) (i := i) (x := x) (f := b) (g := fun _ => b x)
          (hbs.contDiffAt.of_le (by exact_mod_cast le_top)) (contDiff_const.contDiffAt.of_le (by exact_mod_cast le_top))
        rw [show (fun y => b y - b x) = b - fun _ => b x from rfl, this,
          iteratedFDeriv_const_of_ne (by omega : i ≠ 0)]
        simpa using hbb i hpos (hi'.trans hj) x
      have h2 := sa16so_norm_iter_dir hφ (EuclideanSpace.single l 1) (j - i) x
      rw [PiLp.norm_single, norm_one, one_mul] at h2
      have h3 := sa16y_iter_le_jet φ x (n := j) (l := j - i + 1) (by omega)
      have h4 : ((d : ℝ)) ^ (j - i + 1) ≤ ((d : ℝ) + 1) ^ j := by
        calc ((d : ℝ)) ^ (j - i + 1) ≤ ((d : ℝ) + 1) ^ (j - i + 1) :=
              pow_le_pow_left₀ (Nat.cast_nonneg d) (by linarith) _
          _ ≤ ((d : ℝ) + 1) ^ j :=
              pow_le_pow_right₀ (by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith) (by omega)
      have h5 : ‖iteratedFDeriv ℝ (j - i) (fun y => fderiv ℝ φ y (EuclideanSpace.single l 1)) x‖ ≤
          ((d : ℝ) + 1) ^ j * ‖wJet j φ x‖ :=
        h2.trans (h3.trans (mul_le_mul_of_nonneg_right h4 hJ0))
      calc (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y => b y - b x) x‖ *
            ‖iteratedFDeriv ℝ (j - i) (fun y => fderiv ℝ φ y (EuclideanSpace.single l 1)) x‖
          ≤ (j.choose i : ℝ) * B * (((d : ℝ) + 1) ^ j * ‖wJet j φ x‖) :=
            mul_le_mul (mul_le_mul_of_nonneg_left h1 hc) h5 (norm_nonneg _) (mul_nonneg hc hB0)
        _ = _ := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul]
  have hsum : ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) = 2 ^ j := by
    exact_mod_cast Nat.sum_range_choose j
  rw [hsum]
  exact le_of_eq (by ring)


end EnD2

end HRS.Whole.AppendixA.Phase2SA16R
