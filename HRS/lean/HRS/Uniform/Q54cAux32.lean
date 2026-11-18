import HRS.Uniform.Q54cAux31
import HRS.Uniform.Q14Aux6

/-!
# Q54c, part 32: `⟨b_{a,j}, lpFun n ψ⟩ = ∂_jψ(a)`

For `ψ ∈ H^n`, `n > d/2 + 2`, continuous and `C¹`: the real Fourier series of `ψ` may be differentiated termwise.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.Uniform.Q54c

open HRS HRS.PDE HRS.Torus

variable {d : ℕ}

theorem summable_jp_mul_realCoeff {n : ℝ} (hn : (d : ℝ) / 2 + 1 < n) {ψ : Torus d → ℝ}
    (hψ : MemSobolev n ψ) :
    Summable fun k : NonzeroLattice d => Lattice.jp k.1 * |Torus.funRealCoeff ψ k| := by
  have h1 := hψ.2
  have h2 := summable_jp_rpow (d := d) (n - 1) (by linarith)
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (Torus.jp_pos k.1).le (abs_nonneg _))
    (fun k => ?_) ((h1.add h2).mul_left (1 / 2))
  have hj := Torus.jp_pos k.1
  set a := Lattice.jp k.1 ^ n with ha
  set b := Lattice.jp k.1 ^ (1 - n) with hb
  have hab : a * b = Lattice.jp k.1 := by
    rw [ha, hb, ← Real.rpow_add hj]; simp
  have ha2 : a ^ 2 = Lattice.jp k.1 ^ (2 * n) := Torus.jp_rpow_sq n k.1
  have hb2 : b ^ 2 = Lattice.jp k.1 ^ (-(2 * (n - 1))) := by
    rw [hb, Torus.jp_rpow_sq]; congr 1; ring
  have : Lattice.jp k.1 * |Torus.funRealCoeff ψ k| = (a * |Torus.funRealCoeff ψ k|) * b := by
    rw [← hab]; ring
  rw [this]
  have hc := abs_nonneg (Torus.funRealCoeff ψ k)
  have hsq : (a * |Torus.funRealCoeff ψ k|) ^ 2 = Lattice.jp k.1 ^ (2 * n) * Torus.funRealCoeff ψ k ^ 2 := by
    rw [mul_pow, ha2, sq_abs]
  nlinarith [sq_nonneg (a * |Torus.funRealCoeff ψ k| - b), hsq, hb2]

end HRS.Uniform.Q54c
