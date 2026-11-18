import HRS.MC.E213U18c

/-!
# S21G2 K11a -- exact finite half-Wick pairing (R26-T3.K11a)

`E[(1/2) ∑ a_ij (z_i z_j - E z_i z_j) X Y] = ∑ a_ij E[z_i X] E[z_j Y]` for symmetric `a` in a Gaussian
linear space `𝒢` (`QrpwG4`): fourth-moment Wick pairing `qrpw_wick4` for `(z_i, z_j, X, Y)`, subtraction of the
internal covariance term, symmetry of `a`.  The contract is taken verbatim.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace HRS.MS.R26T3

theorem r26t3_finite_wick_pair {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (𝒢 : Submodule ℝ (Ω → ℝ))
    (h𝒢 : HRS.MC.QRSpec.Wick.QrpwG4 P 𝒢) (n : ℕ)
    (z : Fin n → Ω → ℝ) (hz : ∀ i, z i∈𝒢)
    (X Y : Ω → ℝ) (hX : X∈𝒢) (hY : Y∈𝒢)
    (a : Fin n → Fin n → ℝ) (ha : ∀ i j, a i j=a j i) :
    (∫ ω, ((1/2)*∑ i, ∑ j, a i j*(z i ω*z j ω-∫ ω', z i ω'*z j ω' ∂P))*X ω*Y ω ∂P)=
      ∑ i, ∑ j, a i j*(∫ ω, z i ω*X ω ∂P)*(∫ ω, z j ω*Y ω ∂P) := by
  have m4 : ∀ W ∈ 𝒢, MemLp W 4 P := fun W hW => (h𝒢 W hW).1
  have iXY : Integrable (fun ω => X ω * Y ω) P := HRS.MC.QRSpec.Wick.qrpw_int_mul (m4 X hX) (m4 Y hY)
  have iZ : ∀ i j, Integrable (fun ω => z i ω * z j ω * (X ω * Y ω)) P := fun i j =>
    HRS.MC.QRSpec.Wick.qrpw_int_mul4 (m4 _ (hz i)) (m4 _ (hz j)) (m4 X hX) (m4 Y hY)
  have pw : ∀ ω, ((1/2)*∑ i, ∑ j, a i j*(z i ω*z j ω-∫ ω', z i ω'*z j ω' ∂P))*X ω*Y ω =
      ∑ i, ∑ j, (a i j / 2) * (z i ω * z j ω * (X ω * Y ω) -
        (∫ ω', z i ω'*z j ω' ∂P) * (X ω * Y ω)) := fun ω => by
    rw [mul_assoc, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have iterm : ∀ i j, Integrable (fun ω => (a i j / 2) * (z i ω * z j ω * (X ω * Y ω) -
        (∫ ω', z i ω'*z j ω' ∂P) * (X ω * Y ω))) P := fun i j =>
    ((iZ i j).sub (iXY.const_mul _)).const_mul _
  simp_rw [pw]
  rw [integral_finsetSum _ (fun i _ => integrable_finset_sum _ fun j _ => iterm i j)]
  have hw : ∀ i j, ∫ ω, (a i j / 2) * (z i ω * z j ω * (X ω * Y ω) -
        (∫ ω', z i ω'*z j ω' ∂P) * (X ω * Y ω)) ∂P =
      (a i j / 2) * ((∫ ω, z i ω * X ω ∂P) * (∫ ω, z j ω * Y ω ∂P) +
        (∫ ω, z i ω * Y ω ∂P) * (∫ ω, z j ω * X ω ∂P)) := fun i j => by
    rw [integral_const_mul, integral_sub (iZ i j) (iXY.const_mul _), integral_const_mul,
      HRS.MC.QRSpec.Wick.qrpw_wick4 h𝒢 (hz i) (hz j) hX hY]
    ring
  have hs : ∀ i, ∫ ω, ∑ j, (a i j / 2) * (z i ω * z j ω * (X ω * Y ω) -
        (∫ ω', z i ω'*z j ω' ∂P) * (X ω * Y ω)) ∂P =
      ∑ j, (a i j / 2) * ((∫ ω, z i ω * X ω ∂P) * (∫ ω, z j ω * Y ω ∂P) +
        (∫ ω, z i ω * Y ω ∂P) * (∫ ω, z j ω * X ω ∂P)) := fun i => by
    rw [integral_finsetSum _ (fun j _ => iterm i j)]
    exact Finset.sum_congr rfl fun j _ => hw i j
  simp only [hs]
  have hsw : ∑ i, ∑ j, a i j * (∫ ω, z i ω * Y ω ∂P) * (∫ ω, z j ω * X ω ∂P) =
      ∑ i, ∑ j, a i j * (∫ ω, z i ω * X ω ∂P) * (∫ ω, z j ω * Y ω ∂P) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [ha i j]; ring
  have : ∀ i j, (a i j / 2) * ((∫ ω, z i ω * X ω ∂P) * (∫ ω, z j ω * Y ω ∂P) +
        (∫ ω, z i ω * Y ω ∂P) * (∫ ω, z j ω * X ω ∂P)) =
      (1/2) * (a i j * (∫ ω, z i ω * X ω ∂P) * (∫ ω, z j ω * Y ω ∂P)) +
        (1/2) * (a i j * (∫ ω, z i ω * Y ω ∂P) * (∫ ω, z j ω * X ω ∂P)) := fun i j => by ring
  simp only [this, Finset.sum_add_distrib, ← Finset.mul_sum, hsw]
  ring

end HRS.MS.R26T3
