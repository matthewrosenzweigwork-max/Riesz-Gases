import HRS.Main.A8PAux26

/-!
# Packet A8P, part 27: the Hilbert-Schmidt covariance form of the vector integrand
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A8P

open HRS.GF HRS.Uniform

variable {d : ℕ}

theorem a8p_killed_prod {Ω : Type*} {κ : Type*} [Fintype κ] (Φa Φb : ℝ → Ω → κ → ℝ) (ta tb r : ℝ)
    (ω : Ω) :
    ∑ k, killAfter Φa ta r ω k * killAfter Φb tb r ω k =
      if r < min ta tb then ∑ k, Φa r ω k * Φb r ω k else 0 := by
  by_cases h1 : r < ta <;> by_cases h2 : r < tb <;> simp [killAfter, h1, h2, lt_min_iff]

theorem a8p_hsCov_eq (S : MainData d) (R : ∀ N, Realization d N) (N : ℕ) {q : ℕ}
    (ts : Fin q → ℝ) (φ : Fin q → Torus d → ℝ) (r : ℝ) (ω : (R N).Ω) :
    hsCovForm (a8pPhiH S R N ts φ r ω) = a8pForm (a8pSg S R N ts φ r ω) := by
  ext x y
  unfold hsCovForm
  rw [tsum_fintype, a8pForm_apply]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul]
  have hk : ∀ k, inner ℝ (a8pPhiH S R N ts φ r ω k) x = ∑ a, killAfter
      (a8pPhi (S.dyn N) (S.sigma N) (ts a) (a8pF S N ts φ a) (R N).X) (ts a) r ω k * x a := by
    intro k
    simp [a8pPhiH, PiLp.inner_apply, mul_comm]
  have hk' : ∀ k, inner ℝ (a8pPhiH S R N ts φ r ω k) y = ∑ b, killAfter
      (a8pPhi (S.dyn N) (S.sigma N) (ts b) (a8pF S N ts φ b) (R N).X) (ts b) r ω k * y b := by
    intro k
    simp [a8pPhiH, PiLp.inner_apply, mul_comm]
  simp only [hk, hk', Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  have := a8p_killed_prod (a8pPhi (S.dyn N) (S.sigma N) (ts a) (a8pF S N ts φ a) (R N).X)
    (a8pPhi (S.dyn N) (S.sigma N) (ts b) (a8pF S N ts φ b) (R N).X) (ts a) (ts b) r ω
  have e : a8pSg S R N ts φ r ω a b = ∑ k, killAfter
      (a8pPhi (S.dyn N) (S.sigma N) (ts a) (a8pF S N ts φ a) (R N).X) (ts a) r ω k *
      killAfter (a8pPhi (S.dyn N) (S.sigma N) (ts b) (a8pF S N ts φ b) (R N).X) (ts b) r ω k := by
    rw [this]; simp [a8pSg, killedCovMatrix]
  rw [e, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

end HRS.Main.A8P
