import HRS.Energy.Modulated
import HRS.Torus.Sobolev
import HRS.Prob.Gaussian
import HRS.MP.MartModulus

/-!
# Proofs of the bracket lemmas of the small rows (packet SM2)

Statements copied verbatim from `HRS/MC/SmallRowsSpec.lean` (`jp_rpow_le_two_pi_bracket`,
`sobolevNorm_realMode_le_bracket`, `cbNorm_realMode_le_bracket`).  The spec file is not imported
(it is an unproved stub file).  Helper lemmas carry the prefix `p_sm2_`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

set_option maxSynthPendingDepth 3

namespace HRS.MC.SmallRows

open HRS

/-- `jp k ≤ 2π √(1 + |k|²)` (uses `4π² ≥ 1`). -/
lemma p_sm2_jp_le_two_pi_sqrt {d : ℕ} (k : Lattice d) :
    Lattice.jp k ≤ 2 * Real.pi * Real.sqrt (1 + Lattice.enorm k ^ 2) := by
  unfold Lattice.jp
  rw [Real.sqrt_le_iff]
  have hsq : Real.sqrt (1 + Lattice.enorm k ^ 2) ^ 2 = 1 + Lattice.enorm k ^ 2 :=
    Real.sq_sqrt (by positivity)
  have key : (2 * Real.pi * Real.sqrt (1 + Lattice.enorm k ^ 2)) ^ 2 =
      4 * Real.pi ^ 2 * (1 + Lattice.enorm k ^ 2) := by
    rw [mul_pow, mul_pow, hsq]; ring
  refine ⟨by positivity, ?_⟩
  rw [key]
  nlinarith [Real.pi_gt_three, sq_nonneg (Lattice.enorm k), sq_nonneg Real.pi]

/-- `√(1 + e²) ≤ 1 + e` for `e ≥ 0`. -/
lemma p_sm2_sqrt_one_add_sq_le {e : ℝ} (he : 0 ≤ e) :
    Real.sqrt (1 + e ^ 2) ≤ 1 + e := by
  rw [Real.sqrt_le_iff]
  exact ⟨by linarith, by nlinarith⟩

/-- `0 ≤ jp k`. -/
lemma p_sm2_jp_nonneg {d : ℕ} (k : Lattice d) : 0 ≤ Lattice.jp k := by
  unfold Lattice.jp
  positivity

/-- `jp k ≤ 2π (1 + |k|)`. -/
lemma p_sm2_jp_le_linear {d : ℕ} (k : Lattice d) :
    Lattice.jp k ≤ 2 * Real.pi * (1 + Lattice.enorm k) := by
  have he : 0 ≤ Lattice.enorm k := norm_nonneg _
  refine (p_sm2_jp_le_two_pi_sqrt k).trans ?_
  exact mul_le_mul_of_nonneg_left (p_sm2_sqrt_one_add_sq_le he) (by positivity)

/-- NEW STATEMENT (clause P6/U2, TeX M L10061-10062, "`(1+4π²|k|²)^{m/2} ≤ (2π⟨k⟩)^m` for `m ≥ 0`",
with `⟨k⟩ = (1+|k|²)^{1/2}`): numerical inequality for `jp k = (1+4π²|k|²)^{1/2}`.  Proof route:
`1 + 4π²|k|² ≤ 4π²(1+|k|²)` (as `π ≥ 1/2`), `Real.sqrt_le_sqrt`, `Real.rpow_le_rpow`. -/
theorem jp_rpow_le_two_pi_bracket {d : ℕ} (k : Lattice d) {m : ℝ} (hm : 0 ≤ m) :
    Lattice.jp k ^ m ≤ (2 * Real.pi * Real.sqrt (1 + Lattice.enorm k ^ 2)) ^ m :=
  Real.rpow_le_rpow (p_sm2_jp_nonneg k) (p_sm2_jp_le_two_pi_sqrt k) hm

/-- NEW STATEMENT (clause P6/U2, TeX M L10061-10062): the Sobolev norm of the real mode
`√2 cos(2πk·x)` / `√2 sin(2πk·x)` (`Torus.realMode k`) is at most `(2π⟨k⟩)^m`, `m ≥ 0`.  Proof
route: `HRS.MP.MartMod.mmm_sobolevNorm_realMode` (`sobolevNorm m (realMode k) = jp k ^ m`) and
`jp_rpow_le_two_pi_bracket`. -/
theorem sobolevNorm_realMode_le_bracket {d : ℕ} (k : NonzeroLattice d) {m : ℝ} (hm : 0 ≤ m) :
    sobolevNorm m (Torus.realMode k : Torus d → ℝ) ≤
      (2 * Real.pi * Real.sqrt (1 + Lattice.enorm k.1 ^ 2)) ^ m := by
  rw [HRS.MP.MartMod.mmm_sobolevNorm_realMode m k]
  exact jp_rpow_le_two_pi_bracket k.1 hm

/-- NEW STATEMENT (clause P8/U3(a), TeX M L10068: `‖e_k‖_{𝒞^r} ≤ C_r (1+|k|)^r`, integer `r = j`;
the fractional Hölder-Zygmund case is a cited identification and is not formalised): the `C^j_b`
norm (`Torus.cbNorm`, a sum over orders, which is within a factor `j+1` of the printed max norm) of
the real plane waves grows at most like `(1+|k|)^j`.  Proof route: `Torus.cbNorm_realMode_le` and
`jp k ≤ 1 + 2π|k| ≤ 2π(1+|k|)`, `C := (j+1)√2 (2π)^j`. -/
theorem cbNorm_realMode_le_bracket {d : ℕ} (j : ℕ) :
    ∃ C : ℝ, ∀ k : NonzeroLattice d,
      Torus.cbNorm j (Torus.realMode k : Torus d → ℝ) ≤ C * (1 + Lattice.enorm k.1) ^ j := by
  refine ⟨((j : ℝ) + 1) * Real.sqrt 2 * (2 * Real.pi) ^ j, fun k => ?_⟩
  have h1 := Torus.cbNorm_realMode_le_aux j k
  have h2 : Lattice.jp k.1 ^ j ≤ (2 * Real.pi * (1 + Lattice.enorm k.1)) ^ j :=
    pow_le_pow_left₀ (p_sm2_jp_nonneg k.1) (p_sm2_jp_le_linear k.1) j
  calc Torus.cbNorm j (Torus.realMode k : Torus d → ℝ)
      ≤ ((j + 1) * Real.sqrt 2) * Lattice.jp k.1 ^ j := h1
    _ ≤ ((j + 1) * Real.sqrt 2) * (2 * Real.pi * (1 + Lattice.enorm k.1)) ^ j :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = ((j : ℝ) + 1) * Real.sqrt 2 * (2 * Real.pi) ^ j * (1 + Lattice.enorm k.1) ^ j := by
        rw [mul_pow]; ring

end HRS.MC.SmallRows
