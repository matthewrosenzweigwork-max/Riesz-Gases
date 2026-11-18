import HRS.MS.SuppU3Aux2
import HRS.MS.SuppU3Aux4
import HRS.Whole.AppendixA

/-!
# U3, part 5: the abstract `𝒩`-bound for `h = ∑_j (B Ψ_j, Ψ_j)`

`u3_abstract`: for a Hilbert space `H` with a norming family of functionals `ℓ_i` and maps `Φ_j : ℝ^d → H` whose
weak compositions `ℓ_i ∘ Φ_j` are `C^m` with `‖D^k (ℓ_i ∘ Φ_j)‖ ≤ K nrm_i` (`k ≤ m`, `m ≥ 2`), the function
`h = ∑_j (B Φ_j, Φ_j)` (`‖B‖ ≤ 1`) satisfies `‖h‖_{C_b^{0,1}} + ‖h‖_{H^m_uloc} ≤ C(d, m, K, χ)`.
Route: `Φ_j` is bounded and Lipschitz (mean value theorem on the scalar functions), `h` is bounded and Lipschitz;
mollifying `Φ_j` gives smooth `Ψ_n^j` with the same derivative bounds (`u3_moll_bound`), `h_n = ∑ (B Ψ_n, Ψ_n)` has
uniformly bounded `C_b^m` norm and converges pointwise to `h`, and the Sobolev norm of `χ(·-z) h` follows from
`u3_sobE_prod_limit`.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.SuppU3

variable {d : ℕ}

/-- The bumps with outer radius `1/(n+1)`. -/
def u3_bump (n : ℕ) : ContDiffBump (0 : Euc d) :=
  ⟨1 / (2 * ((n : ℝ) + 1)), 1 / ((n : ℝ) + 1), by positivity, by
    have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [div_lt_div_iff₀ (by positivity) this]; nlinarith⟩

theorem u3_bump_rOut (n : ℕ) : (u3_bump (d := d) n).rOut = 1 / ((n : ℝ) + 1) := rfl

theorem u3_bump_rOut_le (n : ℕ) : (u3_bump (d := d) n).rOut ≤ 1 := by
  rw [u3_bump_rOut]
  have : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
  exact (div_le_one (by positivity)).2 this

theorem u3_bump_tendsto : Tendsto (fun n : ℕ => (u3_bump (d := d) n).rOut) atTop (𝓝 0) := by
  simp only [u3_bump_rOut]
  exact tendsto_one_div_add_atTop_nhds_zero_nat

section Abstract
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem u3_quad_lip (B : H →L[ℝ] H) (hB : ‖B‖ ≤ 1) {K : ℝ} (hK : 0 ≤ K) {a b : H} (ha : ‖a‖ ≤ K)
    (hb : ‖b‖ ≤ K) : |inner ℝ (B a) a - inner ℝ (B b) b| ≤ 2 * K * ‖a - b‖ := by
  have e : inner ℝ (B a) a - inner ℝ (B b) b = inner ℝ (B (a - b)) a + inner ℝ (B b) (a - b) := by
    rw [map_sub, inner_sub_left, inner_sub_right]; ring
  rw [e]
  have h1 : |inner ℝ (B (a - b)) a| ≤ ‖a - b‖ * K := by
    calc |inner ℝ (B (a - b)) a| ≤ ‖B (a - b)‖ * ‖a‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖B‖ * ‖a - b‖) * ‖a‖ := by gcongr; exact B.le_opNorm _
      _ ≤ (1 * ‖a - b‖) * K := by gcongr
      _ = ‖a - b‖ * K := by ring
  have h2 : |inner ℝ (B b) (a - b)| ≤ K * ‖a - b‖ := by
    calc |inner ℝ (B b) (a - b)| ≤ ‖B b‖ * ‖a - b‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖B‖ * ‖b‖) * ‖a - b‖ := by gcongr; exact B.le_opNorm _
      _ ≤ (1 * K) * ‖a - b‖ := by gcongr
      _ = K * ‖a - b‖ := by ring
  calc _ ≤ |inner ℝ (B (a - b)) a| + |inner ℝ (B b) (a - b)| := abs_add_le _ _
    _ ≤ ‖a - b‖ * K + K * ‖a - b‖ := add_le_add h1 h2
    _ = 2 * K * ‖a - b‖ := by ring

theorem u3_quad_bd (B : H →L[ℝ] H) (hB : ‖B‖ ≤ 1) {K : ℝ} (hK : 0 ≤ K) {a : H} (ha : ‖a‖ ≤ K) :
    |inner ℝ (B a) a| ≤ K ^ 2 := by
  calc |inner ℝ (B a) a| ≤ ‖B a‖ * ‖a‖ := abs_real_inner_le_norm _ _
    _ ≤ (‖B‖ * ‖a‖) * ‖a‖ := by gcongr; exact B.le_opNorm _
    _ ≤ (1 * K) * K := by gcongr
    _ = K ^ 2 := by ring

end Abstract

end HRS.MS.SuppU3
