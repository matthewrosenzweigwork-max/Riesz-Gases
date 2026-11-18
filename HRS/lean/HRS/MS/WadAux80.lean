import HRS.MS.WadAux79

/-!
# S8.3, packet S8E-3, part 1: the flow-shifted difference of a mild solution

For a mild solution `w` (`S84Sol`) and `ζ ∈ ℝ^d` put `z_s = e^{-as} ζ`, `u_s(y) = w_s(y + z_s) - w_s(y)` and
`qu_s(y) = q_s(y + z_s) - q_s(y)`, `q_s = 𝓑 w_s`.  Since `P_τ g (x + z) = P_τ (g(· + e^{-aτ} z)) x`
(`s8e_P_shift`) and `e^{-a(s-r)} z_r = z_s`, `u` satisfies the mild equation with source `qu`
(`s8e_shift_mild`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

def s8e_zs (a : ℝ) (ζ : Euc d) (s : ℝ) : Euc d := Real.exp (-a * s) • ζ

def s8e_u (a : ℝ) (ζ : Euc d) (w : ℝ → Euc d → ℝ) (s : ℝ) (y : Euc d) : ℝ :=
  w s (y + s8e_zs a ζ s) - w s y

theorem s8e_zs_norm {a s : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) (ζ : Euc d) : ‖s8e_zs a ζ s‖ ≤ ‖ζ‖ := by
  unfold s8e_zs
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have : Real.exp (-a * s) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  nlinarith [norm_nonneg ζ]

theorem s8e_zs_flow (a : ℝ) (ζ : Euc d) (r s : ℝ) :
    Real.exp (-a * (s - r)) • s8e_zs a ζ r = s8e_zs a ζ s := by
  unfold s8e_zs
  rw [smul_smul, ← Real.exp_add]
  congr 2
  ring

theorem s8e_jb_shift {M : ℝ} (hM : 0 ≤ M) {z : Euc d} (hz : ‖z‖ < 1 / 4) (y : Euc d) :
    jbracket (y + z) ^ M ≤ 3 ^ M * jbracket y ^ M :=
  s84_jb_ball hM (by rw [mem_ball_iff_norm]; simpa using hz)

theorem s8e_wt_shift {M C : ℝ} (hM : 0 ≤ M) {f : Euc d → ℝ} (hf : Wt M C f) {z : Euc d} (hz : ‖z‖ < 1 / 4) :
    Wt M (C * 3 ^ M) (fun y => f (y + z)) := fun y => by
  have := hf (y + z)
  calc ‖f (y + z)‖ ≤ C * jbracket (y + z) ^ M := this
    _ ≤ C * (3 ^ M * jbracket y ^ M) := mul_le_mul_of_nonneg_left (s8e_jb_shift hM hz y) hf.nonneg
    _ = _ := by ring

theorem s8e_wt_poly {f : Euc d → ℝ} {K : ℝ} {p : ℕ} (hK : 0 ≤ K) (hf : ∀ y, |f y| ≤ K * (1 + ‖y‖) ^ p) :
    Wt (p : ℝ) (K * 2 ^ p) f := fun y => by
  rw [Real.norm_eq_abs, Real.rpow_natCast]
  refine (hf y).trans ?_
  have h1 : 1 + ‖y‖ ≤ 2 * jbracket y := by linarith [s83_norm_le_jb y, s83_one_le_jb y]
  calc K * (1 + ‖y‖) ^ p ≤ K * (2 * jbracket y) ^ p :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h1 p) hK
    _ = _ := by rw [mul_pow]; ring

end HRS.MS.Wad
