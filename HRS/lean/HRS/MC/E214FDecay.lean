import HRS.PDE.Toolbox

/-!
# E214F-Decay: coordinate form of a test-function second-moment bound

`coord_sq_of_eval_sq`: if `E (eval (X t) φ)² ≤ A e^{-ct} ‖φ‖²_{L²}` for all smooth `φ`
(this is exactly the conclusion of `HRS.MC.L2C6c.l2c6c_proof` for `X = η - ηs`, and of `l2c6a/b`
with `c = 0`), then `E coord_k(X t)² ≤ A e^{-ct} ⟨k⟩^{-2r}`: take `φ = realMode k`.
-/

open MeasureTheory ProbabilityTheory

noncomputable section

namespace HRS.MC.E214F

variable {d : ℕ} {r : ℝ}

theorem eval_realMode (F : NegSobolev d r) (k : NonzeroLattice d) :
    NegSobolev.eval F (Torus.realMode k) = NegSobolev.fourierCoeff F k := by
  unfold NegSobolev.eval
  rw [tsum_eq_single k]
  · have : Torus.funRealCoeff (Torus.realMode k) k = 1 := by
      unfold Torus.funRealCoeff
      simpa using Torus.realMode_orthonormal k k
    rw [this, mul_one]
  · intro k' hk'
    have : Torus.funRealCoeff (Torus.realMode k) k' = 0 := by
      unfold Torus.funRealCoeff
      have := Torus.realMode_orthonormal k' k
      simpa [hk'] using this
    rw [this, mul_zero]

theorem coord_sq_eq (F : NegSobolev d r) (k : NonzeroLattice d) :
    NegSobolev.coord F k ^ 2 = Lattice.jp k.1 ^ (-(2 * r)) * NegSobolev.eval F (Torus.realMode k) ^ 2 := by
  rw [eval_realMode]
  unfold NegSobolev.fourierCoeff
  have hj : 0 < Lattice.jp k.1 := Torus.jp_pos k.1
  have h1 : (Lattice.jp k.1 ^ r) ^ 2 = Lattice.jp k.1 ^ (2 * r) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hj.le]; push_cast; ring_nf
  have h2 : Lattice.jp k.1 ^ (-(2 * r)) * Lattice.jp k.1 ^ (2 * r) = 1 := by
    rw [← Real.rpow_add hj]; simp
  rw [mul_pow, h1, ← mul_assoc, h2, one_mul]

theorem l2NormSq_realMode (k : NonzeroLattice d) : PDE.l2NormSq (Torus.realMode k) = 1 := by
  unfold PDE.l2NormSq
  simpa [sq] using Torus.realMode_orthonormal k k

/-- Coordinate form of a second-moment bound for the test functions `realMode k`. -/
theorem coord_sq_of_eval_sq {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → NegSobolev d r)
    {B : ℝ} (k : NonzeroLattice d)
    (hB : ∫ ω, NegSobolev.eval (X ω) (Torus.realMode k) ^ 2 ∂μ ≤ B) :
    ∫ ω, NegSobolev.coord (X ω) k ^ 2 ∂μ ≤ B * Lattice.jp k.1 ^ (-(2 * r)) := by
  simp_rw [coord_sq_eq]
  rw [integral_const_mul]
  have hj : 0 ≤ Lattice.jp k.1 ^ (-(2 * r)) := Real.rpow_nonneg (Torus.jp_pos k.1).le _
  nlinarith

theorem eval_realMode_sub (F G : NegSobolev d r) (k : NonzeroLattice d) :
    NegSobolev.eval (F - G) (Torus.realMode k) =
      NegSobolev.eval F (Torus.realMode k) - NegSobolev.eval G (Torus.realMode k) := by
  rw [eval_realMode, eval_realMode, eval_realMode]
  unfold NegSobolev.fourierCoeff
  rw [← mul_sub]
  rfl

end HRS.MC.E214F

end
