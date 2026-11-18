import HRS.MS.S111X2Aux3

/-!
# S15d: diagonalization of the exact positive-operator response resolvent

For every positive bounded symmetric operator from the frozen S11.1 X2
framework, the *actual* resolvent defined by the unique solution of
(I + θK)h = f acts on each eigenvector with multiplier (1 + θλ)⁻¹.
The second theorem identifies its matrix elements on an orthonormal
eigenfamily, including zero eigenvalues and θ=0.

This is source supporting the original S15d susceptibility identification;
it does not by itself prove the physical Riesz covariance formula.
-/
set_option autoImplicit false
noncomputable section
open HRS
open HRS.MS.S111X2
open scoped RealInnerProductSpace
namespace HRS.MS.R26T3

theorem s15d_positive_resolvent_eigenvector
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {K : H →L[ℝ] H} {Mg : ℝ} (hK : PosOp K Mg)
    {θ lam : ℝ} (hθ : 0 ≤ θ) (hlam : 0 ≤ lam)
    (v : H) (heig : K v = lam • v) :
    s111x2_Res hK hθ v = (1 + θ * lam)⁻¹ • v := by
  have hden : 1 + θ * lam ≠ 0 := by positivity
  have hscalar : (1 + θ * lam)⁻¹ + θ * ((1 + θ * lam)⁻¹ * lam) = 1 := by
    field_simp
  symm
  apply s111x2_Res_unique hK hθ
  calc
    (1 + θ * lam)⁻¹ • v + θ • K ((1 + θ * lam)⁻¹ • v) =
        ((1 + θ * lam)⁻¹ + θ * ((1 + θ * lam)⁻¹ * lam)) • v := by
          rw [map_smul, heig, smul_smul, smul_smul, ← add_smul]
          congr 1
          ring
    _ = v := by rw [hscalar, one_smul]

theorem s15d_positive_resolvent_eigenfamily_covariance
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {K : H →L[ℝ] H} {Mg : ℝ} (hK : PosOp K Mg)
    {θ : ℝ} (hθ : 0 ≤ θ)
    (lam : ℕ → ℝ) (hlam : ∀ j, 0 ≤ lam j)
    (e : ℕ → H)
    (heig : ∀ j, K (e j) = lam j • e j)
    (horth : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0)
    (i j : ℕ) :
    inner ℝ (e i) (s111x2_Res hK hθ (e j)) =
      if i = j then (1 + θ * lam j)⁻¹ else 0 := by
  rw [s15d_positive_resolvent_eigenvector hK hθ (hlam j) (e j) (heig j)]
  rw [real_inner_smul_right, horth]
  split_ifs <;> simp

#print axioms s15d_positive_resolvent_eigenvector
#print axioms s15d_positive_resolvent_eigenfamily_covariance

end HRS.MS.R26T3
