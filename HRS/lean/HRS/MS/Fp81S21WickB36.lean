import HRS.MS.Fp81S21WickB35

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory
open HRS (Euc)
open HRS.Whole

namespace HRS.Fp81.S21

/-- A common block family is square integrable when its two blocks are. -/
theorem fp81s21_wickB36_concat_memLp {d m n : ℕ} {μ : Measure (Euc d)}
    (u : Fin m → Euc d → ℝ) (hu : ∀ i, MemLp (u i) 2 μ)
    (v : Fin n → Euc d → ℝ) (hv : ∀ i, MemLp (v i) 2 μ) :
    ∀ i, MemLp (fp81s21_wickB22_concatFunction u v i) 2 μ := fun i => by
  cases hi : fp81s21_wickB22_splitIndex i with
  | inl a => simpa [fp81s21_wickB22_concatFunction, hi] using hu a
  | inr b => simpa [fp81s21_wickB22_concatFunction, hi] using hv b

/-- The block polynomial represents the difference of the two output classes. -/
theorem fp81s21_wickB36_polynomialLp_concat
    {d m n : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 P) (Kstar : ℝ)
    (hL : ‖L‖ ≤ Kstar)
    (hJoint : ∀ r (v : Fin r → Lp ℝ 2 μ),
      HRS.IsCenteredGaussian (P.map fun ω => fun i => (L (v i)) ω))
    (u : Fin m → Euc d → ℝ) (hu : ∀ i, MemLp (u i) 2 μ)
    (v : Fin n → Euc d → ℝ) (hv : ∀ i, MemLp (v i) 2 μ)
    (c : Fin m → Fin m → ℝ) (c' : Fin n → Fin n → ℝ) :
    fp81s21_wickB22_polynomialLp L Kstar hL hJoint
      (fp81s21_wickB22_concatFunction u v) (fp81s21_wickB36_concat_memLp u hu v hv)
      (fp81s21_wickB22_concatCoeff c c') =
    fp81s21_wickB22_polynomialLp L Kstar hL hJoint u hu c -
      fp81s21_wickB22_polynomialLp L Kstar hL hJoint v hv c' := by
  let h1 := (fp81s21_wickG_finite_rank_bound L Kstar hL hJoint u hu c).2.1
  let h2 := (fp81s21_wickG_finite_rank_bound L Kstar hL hJoint v hv c').2.1
  apply Lp.ext
  have hconcat := fp81s21_wickB22_polynomial_concat L u hu v hv c c'
  have hc := (fp81s21_wickG_finite_rank_bound L Kstar hL hJoint
      (fp81s21_wickB22_concatFunction u v) (fp81s21_wickB36_concat_memLp u hu v hv)
      (fp81s21_wickB22_concatCoeff c c')).2.1.coeFn_toLp
  have hs := Lp.coeFn_sub (fp81s21_wickB22_polynomialLp L Kstar hL hJoint u hu c)
    (fp81s21_wickB22_polynomialLp L Kstar hL hJoint v hv c')
  filter_upwards [hc, h1.coeFn_toLp, h2.coeFn_toLp, hs] with ω hc' h1' h2' hs'
  change _ = _ at hs'
  change _ = _ at hc'
  rw [hs']
  simp only [Pi.sub_apply, fp81s21_wickB22_polynomialLp]
  rw [hc', h1', h2']
  exact congrFun hconcat ω

/-- Scaling the coefficients scales the output class. -/
theorem fp81s21_wickB36_polynomialLp_smul
    {d m : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 P) (Kstar : ℝ)
    (hL : ‖L‖ ≤ Kstar)
    (hJoint : ∀ r (v : Fin r → Lp ℝ 2 μ),
      HRS.IsCenteredGaussian (P.map fun ω => fun i => (L (v i)) ω))
    (u : Fin m → Euc d → ℝ) (hu : ∀ i, MemLp (u i) 2 μ)
    (c : Fin m → Fin m → ℝ) (a : ℝ) :
    fp81s21_wickB22_polynomialLp L Kstar hL hJoint u hu (fun i j => a * c i j) =
      a • fp81s21_wickB22_polynomialLp L Kstar hL hJoint u hu c := by
  apply Lp.ext
  have h1 := (fp81s21_wickG_finite_rank_bound L Kstar hL hJoint u hu c).2.1.coeFn_toLp
  have h2 := (fp81s21_wickG_finite_rank_bound L Kstar hL hJoint u hu
    (fun i j => a * c i j)).2.1.coeFn_toLp
  have hs := Lp.coeFn_smul a (fp81s21_wickB22_polynomialLp L Kstar hL hJoint u hu c)
  filter_upwards [h1, h2, hs] with ω h1' h2' hs'
  rw [hs']
  simp only [Pi.smul_apply, smul_eq_mul, fp81s21_wickB22_polynomialLp]
  rw [h2', h1']
  exact congrFun (fp81s21_wickB2_polynomial_smul_coeff L u hu a c) ω

#print axioms fp81s21_wickB36_concat_memLp
#print axioms fp81s21_wickB36_polynomialLp_concat
#print axioms fp81s21_wickB36_polynomialLp_smul

end HRS.Fp81.S21
end
