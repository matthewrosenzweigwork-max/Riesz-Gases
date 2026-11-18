import HRS.MS.Fp81S21WeightedGenCoef
import HRS.MS.Fp81S21GaussG4U1
import HRS.MS.UlTail

/-! The compact nonlocal contract and differentiation of its source. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.Ul

abbrev fp81s21_b3_P (p : Parameters) : ℝ := (p.d : ℝ) + 2

def fp81s21_b3_source {p : Parameters} {δ : ℝ} (R : Trajectory p δ)
    (u : ℝ) (f : Euc p.d → ℝ) (j : Fin p.d) (y : Euc p.d) : ℝ :=
  R.ρ u y * (HRS.Torus.matVec (r26t3_coeff R).M.transpose (gradient f y)) j

/-- Exact proposed compact-test bound; this is a proposition, not a proof of it. -/
def fp81s21_b3_nonlocal_compact_contract (p : Parameters) (B c : ℝ) : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∀ {δ : ℝ} (R : Trajectory p δ),
    fp81s21_b3_Data R B c → ∀ u, 0 ≤ u → ∀ f,
      ContDiff ℝ (fp81s21_b3_q p + 2) f → HasCompactSupport f →
      IsR2WeightedTest (fp81s21_b3_q p) (fp81s21_b3_P p) (fp81s21_g4N p R u f) ∧
      weightedSobolevE (fp81s21_b3_q p) (fp81s21_b3_P p) (fp81s21_g4N p R u f) ≤
        ENNReal.ofReal A * weightedSobolevE (fp81s21_b3_q p + 2) (fp81s21_b3_P p) f

/-- Differentiate the sources rather than the singular kernel. The decay
assumption is an intermediate obligation, not part of the compact-test contract. -/
theorem fp81s21_b3_nonlocal_iter_source (p : Parameters) {δ : ℝ}
    (R : Trajectory p δ) (u : ℝ) (f : Euc p.d → ℝ)
    {k : ℕ} {L A : ℝ} (hL : (p.d : ℝ) < L) (hA : 0 ≤ A)
    (hdec : ∀ j, U2Dec (k + 1) L A (fp81s21_b3_source R u f j)) :
    ContDiff ℝ k (fp81s21_g4N p R u f) ∧
    ∀ m ≤ k, ∀ (v : Fin m → Euc p.d) x,
      iteratedFDeriv ℝ m (fp81s21_g4N p R u f) x v =
        ∑ j : Fin p.d, ultK (u2_kap p.d p.s j)
          (fun y => iteratedFDeriv ℝ m (fp81s21_b3_source R u f j) y v) x := by
  have hd : 1 ≤ p.d := by have := p.hd; omega
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  have heq : ∀ j : Fin p.d,
      (fun x => convGradConvW (rieszKernelGrad p.d p.s) (fp81s21_b3_source R u f j) x j) =
        ultK (u2_kap p.d p.s j) (fp81s21_b3_source R u f j) := by
    intro j
    funext x
    exact (ult_conv_comp hd p.hs0 hsd hL hA
      (ult_U2Dec_mono (hdec j) (by omega : 1 ≤ k + 1)) x).2 j
  have hN : fp81s21_g4N p R u f = fun x => ∑ j : Fin p.d,
      ultK (u2_kap p.d p.s j) (fp81s21_b3_source R u f j) x := by
    funext x
    unfold fp81s21_g4N
    exact Finset.sum_congr rfl fun j _ => congrFun (heq j) x
  have hcd : ∀ j : Fin p.d, ContDiff ℝ k
      (ultK (u2_kap p.d p.s j) (fp81s21_b3_source R u f j)) := fun j =>
    (ult_K_iter hd (ult_ker_kap p.hs0 hsd j) hL hA (hdec j)).2
  refine ⟨?_, ?_⟩
  · rw [hN]; exact ContDiff.sum fun j _ => hcd j
  · intro m hm v x
    rw [hN, iteratedFDeriv_fun_sum_apply (fun j _ =>
      ((hcd j).of_le (by exact_mod_cast hm)).contDiffAt)]
    simp only [ContinuousMultilinearMap.sum_apply]
    exact Finset.sum_congr rfl fun j _ =>
      ult_K_iter_apply hd (ult_ker_kap p.hs0 hsd j) hL hA (hdec j) hm v x

#print axioms HRS.Fp81.S21.fp81s21_b3_nonlocal_compact_contract
#print axioms HRS.Fp81.S21.fp81s21_b3_nonlocal_iter_source
end HRS.Fp81.S21
