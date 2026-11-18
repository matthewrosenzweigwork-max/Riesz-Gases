import Mathlib
import HRS.Main.A33Aux10

/-!
# Packet A33, helper 11: pairings `F(ψ)` of `E_m` with weighted-summable test functions
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate RealInnerProductSpace

namespace HRS.A33

open HRS HRS.PDE HRS.PDE.ET

variable {d : ℕ}

/-- weighted summability of the real Fourier coefficients (`ψ ∈ H^m`, zero mode aside) -/
def A33WS (m : ℝ) (ψ : Torus d → ℝ) : Prop :=
  Summable fun k : NonzeroLattice d => Lattice.jp k.1 ^ (2 * m) * Torus.funRealCoeff ψ k ^ 2

lemma a33_ws_smooth (m : ℝ) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) : A33WS m φ :=
  StaticLimitAux.summable_weighted_smooth m hφ

lemma a33_ws_of_memSobolev {m : ℝ} {ψ : Torus d → ℝ} (h : MemSobolev m ψ) : A33WS m ψ := h.2

lemma a33_summable_eval' {m : ℝ} (F : NegSobolev d m) {ψ : Torus d → ℝ} (hψ : A33WS m ψ) :
    Summable fun k : NonzeroLattice d => NegSobolev.fourierCoeff F k * Torus.funRealCoeff ψ k := by
  have h1 := (NegSobolev.coord_sq F).1
  have h2 : Summable fun k : NonzeroLattice d => (Lattice.jp k.1 ^ m * Torus.funRealCoeff ψ k) ^ 2 := by
    refine hψ.congr fun k => ?_
    rw [mul_pow, Torus.jp_rpow_sq]
  refine Summable.of_norm_bounded (g := fun k => (NegSobolev.coord F k ^ 2 +
    (Lattice.jp k.1 ^ m * Torus.funRealCoeff ψ k) ^ 2)) (h1.add h2) fun k => ?_
  have : NegSobolev.fourierCoeff F k * Torus.funRealCoeff ψ k =
      NegSobolev.coord F k * (Lattice.jp k.1 ^ m * Torus.funRealCoeff ψ k) := by
    unfold NegSobolev.fourierCoeff; ring
  rw [this, Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|NegSobolev.coord F k| - |Lattice.jp k.1 ^ m * Torus.funRealCoeff ψ k|),
    sq_abs (NegSobolev.coord F k), sq_abs (Lattice.jp k.1 ^ m * Torus.funRealCoeff ψ k),
    abs_nonneg (NegSobolev.coord F k), abs_nonneg (Lattice.jp k.1 ^ m * Torus.funRealCoeff ψ k)]

lemma a33_funRealCoeff_lin {ψ₁ ψ₂ : Torus d → ℝ} (h1 : Continuous ψ₁) (h2 : Continuous ψ₂)
    (α β : ℝ) (k : NonzeroLattice d) :
    Torus.funRealCoeff (fun x => α * ψ₁ x + β * ψ₂ x) k =
      α * Torus.funRealCoeff ψ₁ k + β * Torus.funRealCoeff ψ₂ k := by
  have hc := HRS.FieldSingAux.continuous_realMode (d := d) k
  unfold Torus.funRealCoeff
  have e : ∀ x, Torus.realMode k x * (α * ψ₁ x + β * ψ₂ x) =
      α * (Torus.realMode k x * ψ₁ x) + β * (Torus.realMode k x * ψ₂ x) := fun x => by ring
  simp_rw [e]
  have i1 : Integrable (fun x => Torus.realMode k x * ψ₁ x) :=
    a33_integrable (by exact hc.mul h1)
  have i2 : Integrable (fun x => Torus.realMode k x * ψ₂ x) :=
    a33_integrable (by exact hc.mul h2)
  rw [integral_add (i1.const_mul α) (i2.const_mul β), integral_const_mul, integral_const_mul]

lemma a33_eval_lin {m : ℝ} (F : NegSobolev d m) {ψ₁ ψ₂ : Torus d → ℝ} (h1 : Continuous ψ₁)
    (h2 : Continuous ψ₂) (w1 : A33WS m ψ₁) (w2 : A33WS m ψ₂) (α β : ℝ) :
    NegSobolev.eval F (fun x => α * ψ₁ x + β * ψ₂ x) =
      α * NegSobolev.eval F ψ₁ + β * NegSobolev.eval F ψ₂ := by
  unfold NegSobolev.eval
  simp_rw [a33_funRealCoeff_lin h1 h2 α β]
  have s1 := (a33_summable_eval' F w1).mul_left α
  have s2 := (a33_summable_eval' F w2).mul_left β
  rw [← tsum_mul_left, ← tsum_mul_left, ← Summable.tsum_add s1 s2]
  refine tsum_congr fun k => ?_
  ring

lemma a33_funRealCoeff_const (c : ℝ) (k : NonzeroLattice d) :
    Torus.funRealCoeff (fun _ : Torus d => c) k = 0 := by
  unfold Torus.funRealCoeff
  simp_rw [mul_comm (Torus.realMode k _) c]
  rw [integral_const_mul, Torus.integral_realMode, mul_zero]

lemma a33_eval_const {m : ℝ} (F : NegSobolev d m) (c : ℝ) :
    NegSobolev.eval F (fun _ : Torus d => c) = 0 := by
  unfold NegSobolev.eval
  simp [a33_funRealCoeff_const]

lemma a33_abs_eval_le {m : ℝ} (F : NegSobolev d m) {ψ : Torus d → ℝ} (hψ : A33WS m ψ) :
    |NegSobolev.eval F ψ| ≤ ‖F‖ * sobolevNorm m ψ := by
  refine (NegSobolev.abs_eval_le F ψ hψ).trans ?_
  refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (norm_nonneg _)
  have : 0 ≤ (Torus.mean ψ) ^ 2 := sq_nonneg _
  linarith

lemma a33_eval_tendsto' {m : ℝ} (e : ℕ ≃ NonzeroLattice d) (F : NegSobolev d m)
    {ψ : Torus d → ℝ} (hψ : A33WS m ψ) :
    Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n,
      NegSobolev.fourierCoeff F (e i) * Torus.funRealCoeff ψ (e i)) atTop
      (𝓝 (NegSobolev.eval F ψ)) := by
  have h := (a33_summable_eval' F hψ).hasSum
  have h' := (e.hasSum_iff (f := fun k : NonzeroLattice d =>
    NegSobolev.fourierCoeff F k * Torus.funRealCoeff ψ k)).2 h
  exact h'.tendsto_sum_nat

lemma a33_eval_measurable {m : ℝ} (e : ℕ ≃ NonzeroLattice d) {ψ : Torus d → ℝ} (hψ : A33WS m ψ) :
    Measurable fun F : NegSobolev d m => NegSobolev.eval F ψ := by
  refine measurable_of_tendsto_metrizable (f := fun n F => ∑ i ∈ Finset.range n,
      NegSobolev.fourierCoeff F (e i) * Torus.funRealCoeff ψ (e i)) (fun n => ?_) ?_
  · refine Finset.measurable_sum _ fun i _ => ?_
    exact ((HRS.FieldSingAux.coordCLM m (e i)).continuous.measurable).mul_const _
  · exact tendsto_pi_nhds.2 fun F => a33_eval_tendsto' e F hψ

end HRS.A33
