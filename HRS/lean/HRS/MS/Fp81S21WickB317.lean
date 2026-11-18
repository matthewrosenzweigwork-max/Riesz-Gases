import HRS.MS.Fp81S21WickB316

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory
open HRS (Euc)
open HRS.Whole

namespace HRS.Fp81.S21

/-- A continuous symmetrization-invariant map with the prescribed finite-rank
polynomial values is uniquely determined on the full product L² space. -/
theorem fp81s21_wickB317_unique_finite_rank
    {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 P) (Kstar : ℝ)
    (hL : ‖L‖ ≤ Kstar)
    (hJoint : ∀ r (v : Fin r → Lp ℝ 2 μ),
      HRS.IsCenteredGaussian (P.map fun ω => fun i => (L (v i)) ω))
    (F : Lp ℝ 2 (μ.prod μ) →L[ℝ] Lp ℝ 2 P)
    (hFsym : ∀ k, F k = F (fp81s21_wickB23_symmetrize μ k))
    (hFfinite : ∀ (m : ℕ) (u : Fin m → Euc d → ℝ)
      (hu : ∀ i, MemLp (u i) 2 μ) (c : Fin m → Fin m → ℝ)
      (hk : MemLp (fp81s21_wickG_finite_rank_kernel u c) 2 (μ.prod μ))
      (hW : MemLp (fp81s21_wickG_finite_rank_polynomial L u hu c) 2 P),
      F (hk.toLp (fp81s21_wickG_finite_rank_kernel u c)) =
        hW.toLp (fp81s21_wickG_finite_rank_polynomial L u hu c)) :
    F = fp81s21_wickG_operator L Kstar hL hJoint := by
  apply fp81s21_wickB312_unique L Kstar hL hJoint F hFsym
  intro x
  let r := fp81s21_wickB38_choose μ x
  change F x = fp81s21_wickB22_polynomialLp L Kstar hL hJoint r.u r.hu r.c
  calc
    F x = F (r.hk.toLp (fp81s21_wickG_finite_rank_kernel r.u r.c)) := congrArg F r.eq_class
    _ = _ := hFfinite r.m r.u r.hu r.c r.hk
      (fp81s21_wickG_finite_rank_bound L Kstar hL hJoint r.u r.hu r.c).2.1

#print axioms fp81s21_wickB317_unique_finite_rank

end HRS.Fp81.S21
end
