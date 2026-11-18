import Mathlib

/-!
A Hilbert-valued L2 field has zero pairing with a vector if the squared
pairings with norm-convergent finite approximants tend to zero. This is
the analytic passage from physical compact chart sections to the exact
constant-test mass functional.
-/
set_option autoImplicit false
noncomputable section
open Classical MeasureTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

namespace HRS.MS.ProClosureS111

theorem inner_ae_zero_of_approximants {X V : Type*} [MeasurableSpace X]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (mu : Measure X) (q : X → V) (hq : MemLp q 2 mu)
    (c : V) (cn : ℕ → V) (hc : Tendsto cn atTop (𝓝 c))
    (hlim : Tendsto (fun n => ∫ x, inner ℝ (q x) (cn n) ^ 2 ∂mu)
      atTop (𝓝 0)) :
    ∀ᵐ x ∂mu, inner ℝ (q x) c = 0 := by
  have hqi : Integrable (fun x => ‖q x‖ ^ 2) mu :=
    (memLp_two_iff_integrable_sq_norm hq.aestronglyMeasurable).1 hq
  have hci : Integrable (fun x => inner ℝ (q x) c ^ 2) mu :=
    (hq.inner_const c).integrable_sq
  have hni : ∀ n, Integrable (fun x => inner ℝ (q x) (cn n) ^ 2) mu :=
    fun n => (hq.inner_const (cn n)).integrable_sq
  have hb : ∀ n, (∫ x, inner ℝ (q x) c ^ 2 ∂mu) ≤
      2 * (∫ x, inner ℝ (q x) (cn n) ^ 2 ∂mu) +
        2 * ‖c - cn n‖ ^ 2 * (∫ x, ‖q x‖ ^ 2 ∂mu) := by
    intro n
    have hpoint : ∀ x, inner ℝ (q x) c ^ 2 ≤
        2 * inner ℝ (q x) (cn n) ^ 2 + 2 * ‖c - cn n‖ ^ 2 * ‖q x‖ ^ 2 := by
      intro x
      have he : inner ℝ (q x) c =
          inner ℝ (q x) (cn n) + inner ℝ (q x) (c - cn n) := by
        rw [inner_sub_right]
        ring
      have hnorm := norm_inner_le_norm (𝕜 := ℝ) (q x) (c - cn n)
      have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      rw [Real.norm_eq_abs, sq_abs, mul_pow] at hsq
      rw [he]
      nlinarith [sq_nonneg (inner ℝ (q x) (cn n) - inner ℝ (q x) (c - cn n))]
    calc
      _ ≤ ∫ x, 2 * inner ℝ (q x) (cn n) ^ 2 +
          2 * ‖c - cn n‖ ^ 2 * ‖q x‖ ^ 2 ∂mu :=
        integral_mono hci ((hni n).const_mul 2 |>.add (hqi.const_mul _)) hpoint
      _ = _ := by rw [integral_add ((hni n).const_mul _) (hqi.const_mul _),
        integral_const_mul, integral_const_mul]
  have hd : Tendsto (fun n => ‖c - cn n‖ ^ 2) atTop (𝓝 0) := by
    have hconst : Tendsto (fun _ : ℕ => c) atTop (𝓝 c) := tendsto_const_nhds
    simpa using (hconst.sub hc).norm.pow 2
  have hupper : Tendsto (fun n =>
      2 * (∫ x, inner ℝ (q x) (cn n) ^ 2 ∂mu) +
        2 * ‖c - cn n‖ ^ 2 * (∫ x, ‖q x‖ ^ 2 ∂mu)) atTop (𝓝 0) := by
    simpa using (hlim.const_mul 2).add ((hd.const_mul 2).mul_const
      (∫ x, ‖q x‖ ^ 2 ∂mu))
  have hzero : (∫ x, inner ℝ (q x) c ^ 2 ∂mu) = 0 :=
    le_antisymm (ge_of_tendsto' hupper hb)
      (integral_nonneg fun _ => sq_nonneg _)
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (inner ℝ (q x) c)) hci).1 hzero
  exact hae.mono fun x hx => (sq_eq_zero_iff).1 hx

end HRS.MS.ProClosureS111

#print axioms HRS.MS.ProClosureS111.inner_ae_zero_of_approximants
