import HRS.MS.Fp81S21WickG6

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace HRS.Fp81.S21

private def fp81s21_wickG7_coord {Ω : Type*} {n : ℕ}
    (Z : Ω → EuclideanSpace ℝ (Fin n)) (i : Fin n) (ω : Ω) : ℝ :=
  (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (Z ω)

/-- Finite-dimensional Isserlis identity and the sharp covariance-form bound
for an arbitrary (not necessarily symmetric) coefficient matrix.  The
covariance domination hypothesis is `C ≤ Λ² I`; the resulting variance
constant is `Λ⁴ / 2`. -/
theorem fp81s21_wickG_finite_half_wick_identity_and_bound
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (Z : Ω → EuclideanSpace ℝ (Fin n)) (hZm : AEMeasurable Z P)
    (hG : HRS.IsCenteredGaussian (P.map Z))
    (Λ : ℝ)
    (hΛ : ∀ α : Fin n → ℝ,
      HRS.MS.R2Chaos.s94q P (fun i ω => fp81s21_wickG7_coord Z i ω) α ≤
        Λ ^ 2 * ∑ i, α i ^ 2)
    (d : Fin n → Fin n → ℝ) :
    (∫ ω, ((1 / 2 : ℝ) * ∑ i, ∑ j, d i j *
      (fp81s21_wickG7_coord Z i ω * fp81s21_wickG7_coord Z j ω -
        ∫ ω', fp81s21_wickG7_coord Z i ω' * fp81s21_wickG7_coord Z j ω' ∂P)) ^ 2 ∂P =
      (1 / 4 : ℝ) * ∑ i, ∑ k, ∑ j, ∑ l,
        (d i j * d k l) *
          ((∫ ω, fp81s21_wickG7_coord Z i ω * fp81s21_wickG7_coord Z k ω ∂P) *
            (∫ ω, fp81s21_wickG7_coord Z j ω * fp81s21_wickG7_coord Z l ω ∂P) +
           (∫ ω, fp81s21_wickG7_coord Z i ω * fp81s21_wickG7_coord Z l ω ∂P) *
            (∫ ω, fp81s21_wickG7_coord Z j ω * fp81s21_wickG7_coord Z k ω ∂P))) ∧
    (∫ ω, ((1 / 2 : ℝ) * ∑ i, ∑ j, d i j *
      (fp81s21_wickG7_coord Z i ω * fp81s21_wickG7_coord Z j ω -
        ∫ ω', fp81s21_wickG7_coord Z i ω' * fp81s21_wickG7_coord Z j ω' ∂P)) ^ 2 ∂P ≤
      (1 / 2 : ℝ) * Λ ^ 4 * ∑ i, ∑ j, d i j ^ 2) := by
  classical
  let g : Fin n → Ω → ℝ := fun i ω => fp81s21_wickG7_coord Z i ω
  let C : Fin n → Fin n → ℝ := fun i j => ∫ ω, g i ω * g j ω ∂P
  let q : Fin n → Fin n → Ω → ℝ := fun i j ω => g i ω * g j ω - C i j
  have hFamily : HRS.MS.R2Chaos.S94GFam P g := by
    exact fp81s21_wickG_joint_to_s94_family Z hZm hG
  have hCov : ∀ α : Fin n → ℝ,
      HRS.MS.R2Chaos.s94q P g α ≤ Λ ^ 2 * ∑ i, α i ^ 2 := by
    exact hΛ
  have hGspace : HRS.MC.QRSpec.Wick.QrpwG4 P
      (HRS.MC.E213U18.u18_gspace P Z) :=
    HRS.MC.E213U18.u18_gspace_G4 hZm hG
  have hLin : ∀ i, g i ∈ HRS.MC.E213U18.u18_gspace P Z := by
    intro i
    exact HRS.MC.E213U18.u18_mem_gspace Z (EuclideanSpace.proj i)
  have hLin4 : ∀ i, MemLp (g i) 4 P := by
    intro i
    exact (hGspace (g i) (hLin i)).1
  have hq : ∀ i j, MemLp (q i j) 2 P := by
    intro i j
    have hProd : MemLp (fun ω => g i ω * g j ω) 2 P :=
      HRS.MC.QRSpec.Wick.qrpw_memLp2_mul (hLin4 i) (hLin4 j)
    exact hProd.sub (memLp_const (C i j))
  have hC : ∀ i j, C i j = ∫ ω, g i ω * g j ω ∂P := by
    intro i j
    rfl
  have hPair : ∀ i j k l, ∫ ω, q i j ω * q k l ω ∂P =
      C i k * C j l + C i l * C j k := by
    intro i j k l
    exact fp81s21_wickG_centered_product_covariance Z hZm hG C hC i j k l
  have hMoment := fp81s21_wickG_finite_weighted_second_moment q hq C hPair d
  have hBound := fp81s21_wickG_finite_half_wick_bound hFamily Λ hCov d
  constructor
  · simpa [g, C, q, fp81s21_wickG7_coord] using hMoment
  · simpa [g, C, q, fp81s21_wickG7_coord] using hBound

#print axioms fp81s21_wickG_finite_half_wick_identity_and_bound

end HRS.Fp81.S21

end
