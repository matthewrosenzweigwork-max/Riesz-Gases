import HRS.MC.QRVocab
import HRS.MC.QRAsmAux2
import HRS.MC.QRAsmAux4
import HRS.MC.QRPMargAux2
import HRS.MC.L2C6Aux1

/-!
# QRAsm, auxiliary file 6: exponent bookkeeping, matrix entries, summations over modes, regime facts
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace HRS.MC.QRSpec.Asm

open HRS.Sec7

variable {Ω : Type} [MeasurableSpace Ω]

lemma asm_modeCov_mono {P : Measure Ω} {d : ℕ} {r : ℝ} {X : Ω → NegSobolev d r} {K K' : ℝ}
    (h : K ≤ K') (hK : ModeCovBound P X K) : ModeCovBound P X K' := fun S a =>
  (hK S a).trans (mul_le_mul_of_nonneg_right h (Finset.sum_nonneg fun _ _ => sq_nonneg _))

/-- Entries of a Hilbert-Schmidt matrix are bounded by the square root of the total mass. -/
lemma asm_entry_le {ι : Type*} {A : ι → ι → ℝ} (hs : Summable fun p : ι × ι => A p.1 p.2 ^ 2) {C : ℝ}
    (hC : tailHS A ∅ ≤ C) (a b : ι) : |A a b| ≤ Real.sqrt C := by
  apply Real.abs_le_sqrt
  have h1 : A a b ^ 2 ≤ ∑' p : ι × ι, A p.1 p.2 ^ 2 :=
    hs.le_tsum (a, b) (fun _ _ => sq_nonneg _)
  have h2 : tailHS A ∅ = ∑' p : ι × ι, A p.1 p.2 ^ 2 := by
    unfold tailHS
    simp
  rw [h2] at hC
  exact h1.trans hC

lemma asm_sqrt_tail {Chd j Lr : ℝ} (hC : 0 ≤ Chd) (hj : 0 < j) (hL : 0 < Lr) (d : ℕ) (θ : ℝ) :
    Real.sqrt (Chd * j ^ ((d : ℝ) + 3) * Lr ^ (-θ)) =
      Real.sqrt Chd * j ^ (((d : ℝ) + 3) / 2) * Lr ^ (-(θ / 2)) := by
  rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
  congr 2
  · rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hj.le]
    congr 1; ring
  · rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hL.le]
    congr 1; ring

lemma asm_sqrt_H {Chd jj : ℝ} (hC : 0 ≤ Chd) (hj : 0 < jj) (d : ℕ) :
    Real.sqrt (Chd * jj ^ ((d : ℝ) + 3)) = Real.sqrt Chd * jj ^ (((d : ℝ) + 3) / 2) := by
  rw [Real.sqrt_mul hC, Real.sqrt_eq_rpow (jj ^ ((d : ℝ) + 3)), ← Real.rpow_mul hj.le]
  congr 2; ring

lemma asm_sqrt_eps (Cε Sr c0 t : ℝ) (hC : 0 ≤ Cε) (hS : 0 ≤ Sr) :
    Real.sqrt (Cε * Real.exp (-c0 * t) * Sr) = Real.sqrt (Cε * Sr) * Real.exp (-c0 * t / 2) := by
  rw [Real.exp_half, show Cε * Real.exp (-c0 * t) * Sr = Cε * Sr * Real.exp (-c0 * t) by ring,
    Real.sqrt_mul (mul_nonneg hC hS)]

section Sums

variable {d : ℕ}

lemma asm_summable_w {r : ℝ} (hr : r = 2 * (d : ℝ) + 6) :
    Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (-2 * r) := by
  have h := summable_jp_rpow (d := d) r (by rw [hr]; have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith)
  refine h.congr fun k => ?_
  rw [neg_mul]

lemma asm_summable_wm {r : ℝ} (hr : r = 2 * (d : ℝ) + 6) :
    Summable fun k : NonzeroLattice d =>
      Lattice.jp k.1 ^ (-2 * r) * (Lattice.jp k.1 ^ (((d : ℝ) + 3) / 2)) ^ 2 := by
  have h := summable_jp_rpow (d := d) ((2 * r - ((d : ℝ) + 3)) / 2) (by
    rw [hr]; have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith)
  refine h.congr fun k => ?_
  rw [Torus.jp_rpow_sq, ← Real.rpow_add (Torus.jp_pos k.1)]
  congr 1
  ring

end Sums

end HRS.MC.QRSpec.Asm

end
