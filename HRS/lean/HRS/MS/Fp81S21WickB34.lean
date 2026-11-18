import HRS.MS.Fp81S21WickB33

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory
open HRS (Euc)
open HRS.Whole

namespace HRS.Fp81.S21

/-- The finite polynomial assignment has the sharp bound on product L². -/
theorem fp81s21_wickB34_polynomialLp_bound
    {d m : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 P) (Kstar : ℝ)
    (hL : ‖L‖ ≤ Kstar)
    (hJoint : ∀ r (v : Fin r → Lp ℝ 2 μ),
      HRS.IsCenteredGaussian (P.map fun ω => fun i => (L (v i)) ω))
    (u : Fin m → Euc d → ℝ) (hu : ∀ i, MemLp (u i) 2 μ)
    (c : Fin m → Fin m → ℝ)
    (hk : MemLp (fp81s21_wickG_finite_rank_kernel u c) 2 (μ.prod μ)) :
    ‖fp81s21_wickB22_polynomialLp L Kstar hL hJoint u hu c‖ ≤
      Kstar ^ 2 / Real.sqrt 2 *
        ‖hk.toLp (fp81s21_wickG_finite_rank_kernel u c)‖ := by
  obtain ⟨hW, hk', hbound⟩ :=
    (fp81s21_wickG_finite_rank_bound L Kstar hL hJoint u hu c).2.2.2.2
  simpa only [fp81s21_wickB22_polynomialLp] using hbound

/-- Equal product L² kernel classes yield equal finite Wick polynomial classes. -/
theorem fp81s21_wickB34_class_independent
    {d m n : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 P) (Kstar : ℝ)
    (hL : ‖L‖ ≤ Kstar)
    (hJoint : ∀ r (v : Fin r → Lp ℝ 2 μ),
      HRS.IsCenteredGaussian (P.map fun ω => fun i => (L (v i)) ω))
    (u : Fin m → Euc d → ℝ) (hu : ∀ i, MemLp (u i) 2 μ)
    (c : Fin m → Fin m → ℝ)
    (v : Fin n → Euc d → ℝ) (hv : ∀ i, MemLp (v i) 2 μ)
    (c' : Fin n → Fin n → ℝ)
    (hk : MemLp (fp81s21_wickG_finite_rank_kernel u c) 2 (μ.prod μ))
    (hk' : MemLp (fp81s21_wickG_finite_rank_kernel v c') 2 (μ.prod μ))
    (heq : hk.toLp (fp81s21_wickG_finite_rank_kernel u c) =
      hk'.toLp (fp81s21_wickG_finite_rank_kernel v c')) :
    fp81s21_wickB22_polynomialLp L Kstar hL hJoint u hu c =
      fp81s21_wickB22_polynomialLp L Kstar hL hJoint v hv c' := by
  apply (fp81s21_wickB22_representation_independent L Kstar hL hJoint
    u hu c v hv c' ?_).1
  filter_upwards [hk.coeFn_toLp, hk'.coeFn_toLp] with z hz hz'
  have hpoint := congrFun (congrArg (fun w : Lp ℝ 2 (μ.prod μ) =>
    (w : Euc d × Euc d → ℝ)) heq) z
  exact hz.symm.trans (hpoint.trans hz')

#print axioms fp81s21_wickB34_polynomialLp_bound
#print axioms fp81s21_wickB34_class_independent

end HRS.Fp81.S21
end
