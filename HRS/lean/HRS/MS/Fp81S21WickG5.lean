import HRS.MS.Fp81S21WickG4

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace HRS.Fp81.S21

private def fp81s21_wickG_coord {Ω : Type*} {n : ℕ}
    (Z : Ω → EuclideanSpace ℝ (Fin n)) (i : Fin n) (ω : Ω) : ℝ :=
  (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (Z ω)

/-- The covariance of two centered Gaussian products is the sum of the two
cross pairings.  This is the four-variable Isserlis identity, centered by the
actual second moments. -/
theorem fp81s21_wickG_centered_product_covariance
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n : ℕ} (Z : Ω → EuclideanSpace ℝ (Fin n)) (hZm : AEMeasurable Z P)
    (hG : HRS.IsCenteredGaussian (P.map Z))
    (C : Fin n → Fin n → ℝ)
    (hC : ∀ i j, C i j = ∫ ω, fp81s21_wickG_coord Z i ω *
      fp81s21_wickG_coord Z j ω ∂P)
    (i j k l : Fin n) :
    ∫ ω, (fp81s21_wickG_coord Z i ω * fp81s21_wickG_coord Z j ω - C i j) *
      (fp81s21_wickG_coord Z k ω * fp81s21_wickG_coord Z l ω - C k l) ∂P =
      C i k * C j l + C i l * C j k := by
  classical
  let g : Fin n → Ω → ℝ := fun a ω => fp81s21_wickG_coord Z a ω
  let 𝒢 := HRS.MC.E213U18.u18_gspace P Z
  have hG4 : HRS.MC.QRSpec.Wick.QrpwG4 P 𝒢 :=
    HRS.MC.E213U18.u18_gspace_G4 hZm hG
  have hcoord : ∀ a, g a ∈ 𝒢 := by
    intro a
    exact HRS.MC.E213U18.u18_mem_gspace Z (EuclideanSpace.proj a)
  have hcoord4 : ∀ a, MemLp (g a) 4 P := by
    intro a
    exact (hG4 (g a) (hcoord a)).1
  have hquad : ∀ a b, MemLp (fun ω => g a ω * g b ω) 2 P := by
    intro a b
    exact HRS.MC.QRSpec.Wick.qrpw_memLp2_mul (hcoord4 a) (hcoord4 b)
  have hprodAB : Integrable (fun ω => g i ω * g j ω) P := (hquad i j).integrable (by norm_num)
  have hprodCD : Integrable (fun ω => g k ω * g l ω) P := (hquad k l).integrable (by norm_num)
  have hprod4 : Integrable (fun ω => g i ω * g j ω * (g k ω * g l ω)) P :=
    HRS.MC.QRSpec.Wick.qrpw_int_mul4 (hcoord4 i) (hcoord4 j) (hcoord4 k) (hcoord4 l)
  have hcentAB : MemLp (fun ω => g i ω * g j ω - C i j) 2 P :=
    (hquad i j).sub (memLp_const (C i j))
  have hcentCD : MemLp (fun ω => g k ω * g l ω - C k l) 2 P :=
    (hquad k l).sub (memLp_const (C k l))
  have hcentProd : Integrable
      (fun ω => (g i ω * g j ω - C i j) * (g k ω * g l ω - C k l)) P :=
    hcentAB.integrable_mul hcentCD
  have hmeanAB : ∫ ω, g i ω * g j ω ∂P = C i j := (hC i j).symm
  have hmeanCD : ∫ ω, g k ω * g l ω ∂P = C k l := (hC k l).symm
  have hmeanIK : ∫ ω, g i ω * g k ω ∂P = C i k := (hC i k).symm
  have hmeanJL : ∫ ω, g j ω * g l ω ∂P = C j l := (hC j l).symm
  have hmeanIL : ∫ ω, g i ω * g l ω ∂P = C i l := (hC i l).symm
  have hmeanJK : ∫ ω, g j ω * g k ω ∂P = C j k := (hC j k).symm
  have hWick := HRS.MC.QRSpec.Wick.qrpw_wick4 hG4
    (hcoord i) (hcoord j) (hcoord k) (hcoord l)
  have hform : ∀ ω,
      (g i ω * g j ω - C i j) * (g k ω * g l ω - C k l) =
        g i ω * g j ω * (g k ω * g l ω) -
          C i j * (g k ω * g l ω) - C k l * (g i ω * g j ω) + C i j * C k l := by
    intro ω
    ring
  rw [integral_congr_ae (ae_of_all _ hform)]
  have hsub1 : Integrable (fun ω => g i ω * g j ω * (g k ω * g l ω) -
      C i j * (g k ω * g l ω)) P := hprod4.sub (hprodCD.const_mul (C i j))
  have hsub2 : Integrable (fun ω => g i ω * g j ω * (g k ω * g l ω) -
      C i j * (g k ω * g l ω) - C k l * (g i ω * g j ω)) P :=
    hsub1.sub (hprodAB.const_mul (C k l))
  rw [integral_add hsub2 (integrable_const _), integral_sub hsub1 (hprodAB.const_mul _),
    integral_sub hprod4 (hprodCD.const_mul _), integral_const_mul, integral_const_mul,
    integral_const_mul, hWick, hmeanAB, hmeanCD, hmeanIK, hmeanJL, hmeanIL, hmeanJK]
  simp
  ring

#print axioms fp81s21_wickG_centered_product_covariance

end HRS.Fp81.S21

end
