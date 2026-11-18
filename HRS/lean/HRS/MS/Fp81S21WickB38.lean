import HRS.MS.Fp81S21WickB37

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory
open HRS (Euc)
open HRS.Whole

namespace HRS.Fp81.S21

/-- Chosen data for a finite-rank class. -/
structure fp81s21_wickB38_Representation {d : ℕ} (μ : Measure (Euc d))
    (k : Lp ℝ 2 (μ.prod μ)) where
  m : ℕ
  u : Fin m → Euc d → ℝ
  hu : ∀ i, MemLp (u i) 2 μ
  c : Fin m → Fin m → ℝ
  hk : MemLp (fp81s21_wickG_finite_rank_kernel u c) 2 (μ.prod μ)
  eq_class : k = hk.toLp (fp81s21_wickG_finite_rank_kernel u c)

def fp81s21_wickB38_choose {d : ℕ} (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    (k : fp81s21_wickB32_finiteRankSubmodule μ) :
    fp81s21_wickB38_Representation μ k := by
  classical
  apply Classical.choice
  obtain ⟨m, u, hu, c, hk, h⟩ := fp81s21_wickB37_span_representable μ k
  exact ⟨⟨m, u, hu, c, hk, h⟩⟩

/-- The finite-rank assignment formed from a chosen representation. -/
def fp81s21_wickB38_operator {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 P) (Kstar : ℝ)
    (hL : ‖L‖ ≤ Kstar)
    (hJoint : ∀ r (v : Fin r → Lp ℝ 2 μ),
      HRS.IsCenteredGaussian (P.map fun ω => fun i => (L (v i)) ω))
    (k : fp81s21_wickB32_finiteRankSubmodule μ) : Lp ℝ 2 P :=
  let r := fp81s21_wickB38_choose μ k
  fp81s21_wickB22_polynomialLp L Kstar hL hJoint r.u r.hu r.c

/-- The chosen-representation assignment agrees with every representation. -/
theorem fp81s21_wickB38_operator_eq
    {d m : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 P) (Kstar : ℝ)
    (hL : ‖L‖ ≤ Kstar)
    (hJoint : ∀ r (v : Fin r → Lp ℝ 2 μ),
      HRS.IsCenteredGaussian (P.map fun ω => fun i => (L (v i)) ω))
    (k : fp81s21_wickB32_finiteRankSubmodule μ)
    (u : Fin m → Euc d → ℝ) (hu : ∀ i, MemLp (u i) 2 μ)
    (c : Fin m → Fin m → ℝ)
    (hk : MemLp (fp81s21_wickG_finite_rank_kernel u c) 2 (μ.prod μ))
    (heq : (k : Lp ℝ 2 (μ.prod μ)) = hk.toLp (fp81s21_wickG_finite_rank_kernel u c)) :
    fp81s21_wickB38_operator L Kstar hL hJoint k =
      fp81s21_wickB22_polynomialLp L Kstar hL hJoint u hu c := by
  let r := fp81s21_wickB38_choose μ k
  exact fp81s21_wickB34_class_independent L Kstar hL hJoint r.u r.hu r.c u hu c
    r.hk hk (r.eq_class.symm.trans heq)

#print axioms fp81s21_wickB38_operator
#print axioms fp81s21_wickB38_operator_eq

end HRS.Fp81.S21
end
