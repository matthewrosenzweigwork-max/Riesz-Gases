import HRS.MC.S7PIDDefs

/-!
# Packet PI-D, sub-packet K (part 2): the evaluation `F ↦ F(φ)` on `E_m` for a test function with `H^m`-summable coefficients

Linearity (subtraction, scalar multiples) and continuity of `NegSobolev.eval · φ`, and the convergence
`x_n → x ⟹ x_n(φ) → x(φ)`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIDK

open HRS HRS.Sec7 HRS.MC.Sec7.PID

variable {d : ℕ} {m : ℝ} {φ : Torus d → ℝ}

/-- the `E_m`-weighted coefficient sequence of the test function -/
def S7PIDK_y (m : ℝ) (φ : Torus d → ℝ) (k : NonzeroLattice d) : ℝ :=
  Lattice.jp k.1 ^ m * Torus.funRealCoeff φ k

theorem S7PIDK_y_sq (hφ : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff φ k ^ 2) :
    Summable fun k => S7PIDK_y m φ k ^ 2 := by
  refine hφ.congr fun k => ?_
  simp only [S7PIDK_y]; rw [mul_pow, Torus.jp_rpow_sq]

theorem S7PIDK_eval_eq (F : NegSobolev d m) (φ : Torus d → ℝ) :
    NegSobolev.eval F φ = ∑' k, NegSobolev.coord F k * S7PIDK_y m φ k := by
  unfold NegSobolev.eval NegSobolev.fourierCoeff
  refine tsum_congr fun k => ?_
  simp only [S7PIDK_y]; ring

theorem S7PIDK_prod_summable (hφ : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff φ k ^ 2)
    (F : NegSobolev d m) :
    Summable fun k => NegSobolev.coord F k * S7PIDK_y m φ k := by
  obtain ⟨hF2, -⟩ := NegSobolev.coord_sq F
  have hcs := Torus.cs_tsum (fun k => |NegSobolev.coord F k|) (fun k => |S7PIDK_y m φ k|)
    (fun _ => abs_nonneg _) (fun _ => abs_nonneg _) (by simpa [sq_abs] using hF2)
    (by simpa [sq_abs] using S7PIDK_y_sq hφ)
  refine Summable.of_norm ?_
  simpa [abs_mul] using hcs.1

theorem S7PIDK_eval_sub (hφ : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff φ k ^ 2)
    (F G : NegSobolev d m) :
    NegSobolev.eval (F - G) φ = NegSobolev.eval F φ - NegSobolev.eval G φ := by
  rw [S7PIDK_eval_eq, S7PIDK_eval_eq, S7PIDK_eval_eq, ← Summable.tsum_sub (S7PIDK_prod_summable hφ F)
    (S7PIDK_prod_summable hφ G)]
  refine tsum_congr fun k => ?_
  have : NegSobolev.coord (F - G) k = NegSobolev.coord F k - NegSobolev.coord G k := rfl
  rw [this]; ring

theorem S7PIDK_eval_smul (r : ℝ) (F : NegSobolev d m) (φ : Torus d → ℝ) :
    NegSobolev.eval (r • F) φ = r * NegSobolev.eval F φ := by
  rw [S7PIDK_eval_eq, S7PIDK_eval_eq, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  have : NegSobolev.coord (r • F) k = r * NegSobolev.coord F k := rfl
  rw [this]; ring

theorem S7PIDK_eval_zero (φ : Torus d → ℝ) : NegSobolev.eval (0 : NegSobolev d m) φ = 0 := by
  have := S7PIDK_eval_smul (0 : ℝ) (0 : NegSobolev d m) φ
  simpa using this

theorem S7PIDK_eval_tendsto (hφ : Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff φ k ^ 2)
    {ι : Type*} {l : Filter ι} {x : ι → NegSobolev d m} {x₀ : NegSobolev d m} (hx : Tendsto x l (𝓝 x₀)) :
    Tendsto (fun i => NegSobolev.eval (x i) φ) l (𝓝 (NegSobolev.eval x₀ φ)) := by
  set C : ℝ := Real.sqrt (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff φ k ^ 2)
  have hb : ∀ i, |NegSobolev.eval (x i) φ - NegSobolev.eval x₀ φ| ≤ ‖x i - x₀‖ * C := by
    intro i
    rw [← S7PIDK_eval_sub hφ]
    exact NegSobolev.abs_eval_le _ φ hφ
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h0 : Tendsto (fun i => ‖x i - x₀‖ * C) l (𝓝 0) := by
    have := (tendsto_iff_norm_sub_tendsto_zero.1 hx).mul_const C
    simpa using this
  exact squeeze_zero (fun i => norm_nonneg _) (fun i => by rw [Real.norm_eq_abs]; exact hb i) h0

end HRS.MC.Sec7.S7PIDK

end
