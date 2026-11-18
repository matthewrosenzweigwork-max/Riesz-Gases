import Mathlib
import HRS.Main.A33Aux8

/-!
# Packet A33, helper 9: random `E_m`-valued fields from random coefficient sequences
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate RealInnerProductSpace

namespace HRS.A33

open HRS

variable {d : ℕ}

lemma a33_summable_of_tsum_ofReal_ne_top {ι : Type*} (f : ι → ℝ) (hf : ∀ k, 0 ≤ f k)
    (h : ∑' k, ENNReal.ofReal (f k) ≠ ⊤) : Summable f := by
  have e : ∀ k, ENNReal.ofReal (f k) = (((f k).toNNReal : ℝ≥0) : ℝ≥0∞) := fun k => rfl
  simp_rw [e] at h
  rw [ENNReal.tsum_coe_ne_top_iff_summable, ← NNReal.summable_coe] at h
  simpa only [Real.coe_toNNReal _ (hf _)] using h

/-- A weighted sum of squares of random variables with summable weighted second moments is a.s.
finite. -/
lemma a33_ae_summable_sq {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] {P : Measure Ω}
    [IsProbabilityMeasure P] (X : ι → Ω → ℝ) (hX : ∀ k, Measurable (X k))
    (hX2 : ∀ k, MemLp (X k) 2 P) (w : ι → ℝ) (hw : ∀ k, 0 ≤ w k)
    (hsum : Summable fun k => w k * ∫ ω, X k ω ^ 2 ∂P) :
    ∀ᵐ ω ∂P, Summable fun k => w k * X k ω ^ 2 := by
  set S : Ω → ℝ≥0∞ := fun ω => ∑' k, ENNReal.ofReal (w k * X k ω ^ 2) with hS
  have hSm : Measurable S :=
    Measurable.ennreal_tsum fun k => ENNReal.measurable_ofReal.comp (((hX k).pow_const 2).const_mul _)
  have hint : ∀ k, ∫⁻ ω, ENNReal.ofReal (w k * X k ω ^ 2) ∂P =
      ENNReal.ofReal (w k * ∫ ω, X k ω ^ 2 ∂P) := by
    intro k
    have h1 : Integrable (fun ω => X k ω ^ 2) P := (hX2 k).integrable_sq
    rw [← integral_const_mul, ofReal_integral_eq_lintegral_ofReal (h1.const_mul _)
      (Eventually.of_forall fun ω => mul_nonneg (hw k) (sq_nonneg _))]
  have hfin : ∫⁻ ω, S ω ∂P ≠ ⊤ := by
    have := lintegral_tsum (μ := P) (f := fun k ω => ENNReal.ofReal (w k * X k ω ^ 2))
      (fun k => ((ENNReal.measurable_ofReal.comp
        (((hX k).pow_const 2).const_mul _))).aemeasurable)
    simp only [hS]
    rw [this]
    simp_rw [hint]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => mul_nonneg (hw k) (integral_nonneg fun ω => sq_nonneg _)) hsum]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_lt_top hSm hfin] with ω hω
  exact a33_summable_of_tsum_ofReal_ne_top _ (fun k => mul_nonneg (hw k) (sq_nonneg _)) hω.ne

lemma a33_summable_eval {m : ℝ} (F : NegSobolev d m) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    Summable fun k : NonzeroLattice d => NegSobolev.fourierCoeff F k * Torus.funRealCoeff φ k := by
  have h1 := (NegSobolev.coord_sq F).1
  have h2 : Summable fun k : NonzeroLattice d => (Lattice.jp k.1 ^ m * Torus.funRealCoeff φ k) ^ 2 := by
    refine (HRS.StaticLimitAux.summable_weighted_smooth m hφ).congr fun k => ?_
    rw [mul_pow, Torus.jp_rpow_sq]
  refine Summable.of_norm_bounded (g := fun k => (NegSobolev.coord F k ^ 2 +
    (Lattice.jp k.1 ^ m * Torus.funRealCoeff φ k) ^ 2)) (h1.add h2) fun k => ?_
  have : NegSobolev.fourierCoeff F k * Torus.funRealCoeff φ k =
      NegSobolev.coord F k * (Lattice.jp k.1 ^ m * Torus.funRealCoeff φ k) := by
    unfold NegSobolev.fourierCoeff; ring
  rw [this, Real.norm_eq_abs, abs_mul]
  nlinarith [sq_nonneg (|NegSobolev.coord F k| - |Lattice.jp k.1 ^ m * Torus.funRealCoeff φ k|),
    sq_abs (NegSobolev.coord F k), sq_abs (Lattice.jp k.1 ^ m * Torus.funRealCoeff φ k),
    abs_nonneg (NegSobolev.coord F k), abs_nonneg (Lattice.jp k.1 ^ m * Torus.funRealCoeff φ k)]

lemma a33_eval_tendsto {m : ℝ} (e : ℕ ≃ NonzeroLattice d) (F : NegSobolev d m)
    {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n,
      NegSobolev.fourierCoeff F (e i) * Torus.funRealCoeff φ (e i)) atTop
      (𝓝 (NegSobolev.eval F φ)) := by
  have h := (a33_summable_eval F hφ).hasSum
  have h' := (e.hasSum_iff (f := fun k : NonzeroLattice d =>
    NegSobolev.fourierCoeff F k * Torus.funRealCoeff φ k)).2 h
  exact h'.tendsto_sum_nat

end HRS.A33
