import HRS.MC.QRPGaussErAux1

/-!
# QRPGaussEr: `qrs_gauss_er_proof` (`E_r`-norm moments of a centred Gaussian field)

Relocated proof of `HRS.MC.QRSpec.qrs_gauss_er`.  Route: `‖X‖² = ∑_k w_k X̂_k²`, Minkowski in `L^{q/2}` over finite
sections of the sum plus Fatou (`QRPGaussErAux1.qrpg_minkowski`), scalar Gaussian moments `‖Z‖_q = c_q ‖Z‖_2`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace HRS.MC.QRSpec.GaussEr

theorem qrs_gauss_er_proof : ∀ q : ℝ, 1 ≤ q → ∃ C : ℝ, 0 < C ∧
    ∀ (d : ℕ) (r : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X : Ω → NegSobolev d r), Measurable X → HasFiniteGaussianCoeffs P X →
      (Summable fun k : NonzeroLattice d =>
        Lattice.jp k.1 ^ (-2 * r) * ∫ ω, NegSobolev.fourierCoeff (X ω) k ^ 2 ∂P) →
      eLpNorm (fun ω => ‖X ω‖) (ENNReal.ofReal q) P ≤
        ENNReal.ofReal (C * Real.sqrt (∑' k : NonzeroLattice d,
          Lattice.jp k.1 ^ (-2 * r) * ∫ ω, NegSobolev.fourierCoeff (X ω) k ^ 2 ∂P)) := by
  intro q hq
  set q' : ℝ := max q 2 with hq'
  have hq2 : 2 ≤ q' := le_max_right _ _
  have hqq : q ≤ q' := le_max_left _ _
  set c : ℝ := (eLpNorm (fun x : ℝ => x) (ENNReal.ofReal q') (gaussianReal 0 1)).toReal with hc
  have hc0 : 0 ≤ c := ENNReal.toReal_nonneg
  refine ⟨c + 1, by linarith, ?_⟩
  intro d r Ω _ P _ X hXm hG hsum
  set w : NonzeroLattice d → ℝ := fun k => Lattice.jp k.1 ^ (-2 * r) with hw
  set Z : NonzeroLattice d → Ω → ℝ := fun k ω => NegSobolev.fourierCoeff (X ω) k with hZdef
  have hZ : ∀ k, HasGaussianLaw (Z k) P := fun k =>
    HasGaussianLaw.eval (X := fun (j : ({k} : Finset (NonzeroLattice d))) ω =>
      NegSobolev.fourierCoeff (X ω) j.1) (hG {k}).1 ⟨k, by simp⟩
  have h0 : ∀ k, ∫ ω, Z k ω ∂P = 0 := fun k => (hG {k}).2 k
  have hw0 : ∀ k, 0 ≤ w k := fun k => Real.rpow_nonneg (Torus.jp_pos k.1).le _
  have hwZ : ∀ (F : NegSobolev d r) k, w k * NegSobolev.fourierCoeff F k ^ 2 =
      NegSobolev.coord F k ^ 2 := by
    intro F k
    have hj := Torus.jp_pos k.1
    simp only [hw, NegSobolev.fourierCoeff]
    rw [mul_pow, Torus.jp_rpow_sq, ← mul_assoc, ← Real.rpow_add hj]
    simp
  have hT : ∀ ω, HasSum (fun k => w k * Z k ω ^ 2) (‖X ω‖ ^ 2) := by
    intro ω
    obtain ⟨h1, h2⟩ := NegSobolev.coord_sq (X ω)
    rw [h2]
    simp only [hZdef, hwZ]
    exact h1.hasSum
  have hTm : AEStronglyMeasurable (fun ω => ‖X ω‖ ^ 2) P :=
    (hXm.norm.pow_const 2).aestronglyMeasurable
  have hNm : AEStronglyMeasurable (fun ω => ‖X ω‖) P := hXm.norm.aestronglyMeasurable
  have hmk := qrpg_minkowski Z hZ h0 w hw0 (fun ω => ‖X ω‖ ^ 2) hT hTm hsum q' hq2
  set W : ℝ := ∑' k : NonzeroLattice d,
    Lattice.jp k.1 ^ (-2 * r) * ∫ ω, NegSobolev.fourierCoeff (X ω) k ^ 2 ∂P with hW
  have hW0 : 0 ≤ W := tsum_nonneg fun k =>
    mul_nonneg (hw0 k) (integral_nonneg fun ω => sq_nonneg _)
  have hsq := qrpg_sq_eLpNorm hNm (s := q' / 2) (by linarith)
  rw [show 2 * (q' / 2) = q' by ring] at hsq
  have hsq' : eLpNorm (fun ω => ‖X ω‖) (ENNReal.ofReal q') P ^ 2 ≤
      ENNReal.ofReal (c * Real.sqrt W) ^ 2 := by
    have : eLpNorm (fun ω => ‖X ω‖ ^ 2) (ENNReal.ofReal (q' / 2)) P ≤
        ENNReal.ofReal (c ^ 2 * W) := hmk
    have e : eLpNorm (fun ω => ‖X ω‖ ^ 2) (ENNReal.ofReal (q' / 2)) P =
        eLpNorm (fun ω => ‖X ω‖) (ENNReal.ofReal q') P ^ 2 := by
      rw [← hsq]
    rw [e] at this
    refine this.trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_pow (mul_nonneg hc0 (Real.sqrt_nonneg _)), mul_pow, Real.sq_sqrt hW0]
  have h1 : eLpNorm (fun ω => ‖X ω‖) (ENNReal.ofReal q') P ≤ ENNReal.ofReal (c * Real.sqrt W) := by
    by_contra hcon
    rw [not_le] at hcon
    have := ENNReal.pow_lt_pow_left (two_ne_zero) hcon
    exact absurd hsq' (not_le.mpr this)
  refine (eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hqq)).trans (h1.trans ?_)
  refine ENNReal.ofReal_le_ofReal ?_
  nlinarith [Real.sqrt_nonneg W]

end HRS.MC.QRSpec.GaussEr

end
