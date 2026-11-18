import HRS.MS.PROS15dEigenResolventR60
import HRS.MS.S21H2_S14aB

/-!
# S15d: exact all-test spectral series of the original Hilbert-space resolvent

For a complete Hilbert eigenbasis, this is an unconditional Parseval
representation of the actual frozen response operator. No finite-rank
truncation is inserted into the operator definition and zero eigenvalues
are allowed. The theorem is not yet the physical tilted covariance identity.
-/
set_option autoImplicit false
noncomputable section
open HRS
open HRS.MS.S111X2
open scoped RealInnerProductSpace
namespace HRS.MS.R26T3

theorem s15d_positive_resolvent_alltest_spectral_series
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    {K : H →L[ℝ] H} {Mg : ℝ} (hK : PosOp K Mg)
    {θ : ℝ} (hθ : 0 ≤ θ)
    (b : HilbertBasis ℕ ℝ H)
    (lam : ℕ → ℝ) (hlam : ∀ j, 0 ≤ lam j)
    (heig : ∀ j, K (b j) = lam j • b j)
    (v w : H) :
    HasSum (fun j => (1 + θ * lam j)⁻¹ *
      (inner ℝ v (b j) * inner ℝ (b j) w))
      (inner ℝ v (s111x2_Res hK hθ w)) := by
  have hsum := b.hasSum_inner_mul_inner v (s111x2_Res hK hθ w)
  have hterm : ∀ j,
      inner ℝ (b j) (s111x2_Res hK hθ w) =
        (1 + θ * lam j)⁻¹ * inner ℝ (b j) w := by
    intro j
    have hs := s111x2_Res_symm hK hθ (b j) w
    rw [← hs, s15d_positive_resolvent_eigenvector hK hθ
      (hlam j) (b j) (heig j), real_inner_smul_left]
  convert hsum using 1
  funext j
  rw [hterm j]
  ring

#print axioms s15d_positive_resolvent_alltest_spectral_series
end HRS.MS.R26T3
