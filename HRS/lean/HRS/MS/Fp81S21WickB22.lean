import HRS.MS.Fp81S21WickB2

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
open HRS (Euc)
open HRS.Whole

namespace HRS.Fp81.S21

def fp81s21_wickB22_splitIndex {m n : ℕ} :
    Fin (m + n) → Fin m ⊕ Fin n :=
  Fin.addCases (fun i => Sum.inl i) (fun j => Sum.inr j)

def fp81s21_wickB22_concatFunction {d m n : ℕ}
    (u : Fin m → Euc d → ℝ) (v : Fin n → Euc d → ℝ)
    (i : Fin (m + n)) : Euc d → ℝ :=
  Sum.elim u v (fp81s21_wickB22_splitIndex i)

def fp81s21_wickB22_concatCoeff {m n : ℕ}
    (c : Fin m → Fin m → ℝ) (c' : Fin n → Fin n → ℝ)
    (i j : Fin (m + n)) : ℝ :=
  match fp81s21_wickB22_splitIndex i, fp81s21_wickB22_splitIndex j with
  | Sum.inl a, Sum.inl b => c a b
  | Sum.inl _, Sum.inr _ => 0
  | Sum.inr _, Sum.inl _ => 0
  | Sum.inr a, Sum.inr b => -c' a b

private theorem fp81s21_wickB22_concat_kernel
    {d m n : ℕ} (u : Fin m → Euc d → ℝ) (v : Fin n → Euc d → ℝ)
    (c : Fin m → Fin m → ℝ) (c' : Fin n → Fin n → ℝ)
    (x y : Euc d) :
    r2FiniteRankKernel (fp81s21_wickB22_concatCoeff c c')
        (fp81s21_wickB22_concatFunction u v) x y =
      r2FiniteRankKernel c u x y - r2FiniteRankKernel c' v x y := by
  classical
  simp [r2FiniteRankKernel, fp81s21_wickB22_concatCoeff,
    fp81s21_wickB22_concatFunction, fp81s21_wickB22_splitIndex,
    Fin.sum_univ_add]
  ring

private theorem fp81s21_wickB22_concat_polynomial
    {d m n : ℕ} {μ : Measure (Euc d)} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} (L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 P)
    (u : Fin m → Euc d → ℝ) (hu : ∀ i, MemLp (u i) 2 μ)
    (v : Fin n → Euc d → ℝ) (hv : ∀ i, MemLp (v i) 2 μ)
    (c : Fin m → Fin m → ℝ) (c' : Fin n → Fin n → ℝ) :
    fp81s21_wickG_finite_rank_polynomial L
        (fp81s21_wickB22_concatFunction u v)
        (fun i => by
          cases hi : fp81s21_wickB22_splitIndex i with
          | inl a => simpa [fp81s21_wickB22_concatFunction, hi] using hu a
          | inr b => simpa [fp81s21_wickB22_concatFunction, hi] using hv b)
        (fp81s21_wickB22_concatCoeff c c') =
      fun ω => fp81s21_wickG_finite_rank_polynomial L u hu c ω -
        fp81s21_wickG_finite_rank_polynomial L v hv c' ω := by
  classical
  funext ω
  simp [fp81s21_wickG_finite_rank_polynomial,
    fp81s21_wickB22_concatCoeff, fp81s21_wickB22_concatFunction,
    fp81s21_wickB22_splitIndex, Fin.sum_univ_add]
  ring

/-- A canonical `Lp` class for the finite half-Wick polynomial. The preceding
finite-rank estimate supplies its integrability. -/
noncomputable def fp81s21_wickB22_polynomialLp
    {d m : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 P) (Kstar : ℝ)
    (hL : ‖L‖ ≤ Kstar)
    (hJoint : ∀ r (v : Fin r → Lp ℝ 2 μ),
      HRS.IsCenteredGaussian (P.map fun ω => fun i => (L (v i)) ω))
    (u : Fin m → Euc d → ℝ) (hu : ∀ i, MemLp (u i) 2 μ)
    (c : Fin m → Fin m → ℝ) : Lp ℝ 2 P :=
  (fp81s21_wickG_finite_rank_bound L Kstar hL hJoint u hu c).2.1.toLp
    (fp81s21_wickG_finite_rank_polynomial L u hu c)

/-- Two finite representations of the same product-kernel `Lp` class yield
the same centered half-Wick polynomial, both almost everywhere and as an `Lp`
class. The proof forms one block family and applies the zero-kernel case of the
finite-rank norm bound. -/
theorem fp81s21_wickB22_representation_independent
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
    (hKernel : (fun z : Euc d × Euc d => r2FiniteRankKernel c u z.1 z.2) =ᵐ[μ.prod μ]
      fun z => r2FiniteRankKernel c' v z.1 z.2) :
    fp81s21_wickB22_polynomialLp L Kstar hL hJoint u hu c =
        fp81s21_wickB22_polynomialLp L Kstar hL hJoint v hv c' ∧
      fp81s21_wickG_finite_rank_polynomial L u hu c =ᵐ[P]
        fp81s21_wickG_finite_rank_polynomial L v hv c' := by
  classical
  let w : Fin (m + n) → Euc d → ℝ :=
    fp81s21_wickB22_concatFunction u v
  let a : Fin (m + n) → Fin (m + n) → ℝ :=
    fp81s21_wickB22_concatCoeff c c'
  let hw : ∀ i, MemLp (w i) 2 μ := fun i => by
    cases hi : fp81s21_wickB22_splitIndex i with
    | inl j => simpa [w, fp81s21_wickB22_concatFunction, hi] using hu j
    | inr j => simpa [w, fp81s21_wickB22_concatFunction, hi] using hv j
  let hBound := fp81s21_wickG_finite_rank_bound L Kstar hL hJoint w hw a
  have hKernelZero :
      (fp81s21_wickG_finite_rank_kernel w a) =ᵐ[μ.prod μ] 0 := by
    filter_upwards [hKernel] with z hz
    change r2FiniteRankKernel a w z.1 z.2 = 0
    rw [fp81s21_wickB22_concat_kernel]
    rw [hz]
    simp
  rcases hBound.2.2.2.2 with ⟨hW, hk, hNorm⟩
  have hkZero : hk.toLp (fp81s21_wickG_finite_rank_kernel w a) = 0 := by
    apply Lp.ext
    filter_upwards [hk.coeFn_toLp, hKernelZero] with z hz1 hz2
    rw [hz1, hz2]
    simp
  have hNormZero :
      ‖hW.toLp (fp81s21_wickG_finite_rank_polynomial L w hw a)‖ = 0 := by
    rw [hkZero, norm_zero, mul_zero] at hNorm
    exact le_antisymm hNorm (norm_nonneg _)
  have hWZero : hW.toLp
      (fp81s21_wickG_finite_rank_polynomial L w hw a) = 0 :=
    norm_eq_zero.mp hNormZero
  have hWAE :
      fp81s21_wickG_finite_rank_polynomial L w hw a =ᵐ[P] 0 := by
    have hclass :
        (hW.toLp (fp81s21_wickG_finite_rank_polynomial L w hw a) : Ω → ℝ) =ᵐ[P] 0 := by
      rw [hWZero]
      exact (Lp.coeFn_zero (E := ℝ) (p := 2) (μ := P))
    exact hW.coeFn_toLp.symm.trans hclass
  have hDifference :
      (fun ω => fp81s21_wickG_finite_rank_polynomial L u hu c ω -
        fp81s21_wickG_finite_rank_polynomial L v hv c' ω) =ᵐ[P] 0 := by
    have hConcat := fp81s21_wickB22_concat_polynomial L u hu v hv c c'
    rw [← hConcat]
    exact hWAE
  have hPolyAE :
      fp81s21_wickG_finite_rank_polynomial L u hu c =ᵐ[P]
        fp81s21_wickG_finite_rank_polynomial L v hv c' := by
    filter_upwards [hDifference] with ω hω
    exact sub_eq_zero.mp hω
  have hPolyLp :
      fp81s21_wickB22_polynomialLp L Kstar hL hJoint u hu c =
        fp81s21_wickB22_polynomialLp L Kstar hL hJoint v hv c' := by
    apply Lp.ext
    change ((fp81s21_wickG_finite_rank_bound L Kstar hL hJoint u hu c).2.1.toLp
      (fp81s21_wickG_finite_rank_polynomial L u hu c) : Ω → ℝ) =ᵐ[P]
      ((fp81s21_wickG_finite_rank_bound L Kstar hL hJoint v hv c').2.1.toLp
        (fp81s21_wickG_finite_rank_polynomial L v hv c') : Ω → ℝ)
    filter_upwards [
      (fp81s21_wickG_finite_rank_bound L Kstar hL hJoint u hu c).2.1.coeFn_toLp,
      (fp81s21_wickG_finite_rank_bound L Kstar hL hJoint v hv c').2.1.coeFn_toLp,
      hPolyAE] with ω hU hV hP
    rw [hU, hV]
    exact hP
  exact ⟨hPolyLp, hPolyAE⟩

#print axioms fp81s21_wickB22_representation_independent

end HRS.Fp81.S21

end

namespace HRS.Fp81.S21

open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
open HRS (Euc)
open HRS.Whole
/-- Additivity of the finite half-Wick polynomial over block concatenation of
input families, with the second coefficient block negated to form a
representation difference. -/
theorem fp81s21_wickB22_polynomial_concat
    {d m n : ℕ} {μ : Measure (Euc d)} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} (L : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 P)
    (u : Fin m → Euc d → ℝ) (hu : ∀ i, MemLp (u i) 2 μ)
    (v : Fin n → Euc d → ℝ) (hv : ∀ i, MemLp (v i) 2 μ)
    (c : Fin m → Fin m → ℝ) (c' : Fin n → Fin n → ℝ) :
    fp81s21_wickG_finite_rank_polynomial L
        (fp81s21_wickB22_concatFunction u v)
        (fun i => by
          cases hi : fp81s21_wickB22_splitIndex i with
          | inl a => simpa [fp81s21_wickB22_concatFunction, hi] using hu a
          | inr b => simpa [fp81s21_wickB22_concatFunction, hi] using hv b)
        (fp81s21_wickB22_concatCoeff c c') =
      fun ω => fp81s21_wickG_finite_rank_polynomial L u hu c ω -
        fp81s21_wickG_finite_rank_polynomial L v hv c' ω :=
  fp81s21_wickB22_concat_polynomial L u hu v hv c c'

#print axioms fp81s21_wickB22_polynomial_concat

end HRS.Fp81.S21

