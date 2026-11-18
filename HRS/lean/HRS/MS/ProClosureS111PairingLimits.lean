import HRS.MS.ProClosureS111MassLimit
import HRS.MS.S111X1Aux4

/-! Actual L2 continuity of Hilbert pairings and scalar covariance integrals. -/
set_option autoImplicit false
noncomputable section
open Classical MeasureTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

namespace HRS.MS.ProClosureS111

theorem inner_pairing_square_error {X V : Type*} [MeasurableSpace X]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (mu : Measure X) (q : X → V) (hq : MemLp q 2 mu) (c d : V) :
    (∫ x, (inner ℝ (q x) c - inner ℝ (q x) d) ^ 2 ∂mu) ≤
      ‖c - d‖ ^ 2 * (∫ x, ‖q x‖ ^ 2 ∂mu) := by
  have hi : Integrable (fun x => ‖q x‖ ^ 2) mu :=
    (memLp_two_iff_integrable_sq_norm hq.aestronglyMeasurable).1 hq
  have hj : Integrable (fun x => (inner ℝ (q x) c - inner ℝ (q x) d) ^ 2) mu :=
    ((hq.inner_const c).sub (hq.inner_const d)).integrable_sq
  calc
    _ ≤ ∫ x, ‖c - d‖ ^ 2 * ‖q x‖ ^ 2 ∂mu := by
      refine integral_mono hj (hi.const_mul _) fun x => ?_
      rw [← inner_sub_right]
      have h := pow_le_pow_left₀ (norm_nonneg _)
        (norm_inner_le_norm (𝕜 := ℝ) (q x) (c - d)) 2
      simpa only [Real.norm_eq_abs, sq_abs, mul_pow, mul_comm] using h
    _ = _ := integral_const_mul _ _

theorem inner_pairing_square_tendsto {X V : Type*} [MeasurableSpace X]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (mu : Measure X) (q : X → V) (hq : MemLp q 2 mu)
    (c : V) (cn : ℕ → V) (hc : Tendsto cn atTop (𝓝 c)) :
    Tendsto (fun n => ∫ x, (inner ℝ (q x) (cn n) - inner ℝ (q x) c) ^ 2 ∂mu)
      atTop (𝓝 0) := by
  have hn := (tendsto_iff_norm_sub_tendsto_zero.1 hc).pow 2
  have hu : Tendsto (fun n => ‖cn n - c‖ ^ 2 * (∫ x, ‖q x‖ ^ 2 ∂mu))
      atTop (𝓝 0) := by simpa using hn.mul_const (∫ x, ‖q x‖ ^ 2 ∂mu)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
    (fun n => integral_nonneg fun _ => sq_nonneg _)
    (fun n => inner_pairing_square_error mu q hq (cn n) c)

theorem integral_mul_tendsto_of_square_error {X : Type*} [MeasurableSpace X]
    (mu : Measure X) (fn : ℕ → X → ℝ) (f g : X → ℝ)
    (hfn : ∀ n, MemLp (fn n) 2 mu) (hf : MemLp f 2 mu) (hg : MemLp g 2 mu)
    (hlim : Tendsto (fun n => ∫ x, (fn n x - f x) ^ 2 ∂mu) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, fn n x * g x ∂mu) atTop (𝓝 (∫ x, f x * g x ∂mu)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have he : ∀ n, (∫ x, fn n x * g x ∂mu) - (∫ x, f x * g x ∂mu) =
      ∫ x, (fn n x - f x) * g x ∂mu := by
    intro n
    calc
      (∫ x, fn n x * g x ∂mu) - (∫ x, f x * g x ∂mu) =
          ∫ x, (fn n x * g x - f x * g x) ∂mu :=
        (integral_sub ((hfn n).integrable_mul hg) (hf.integrable_mul hg)).symm
      _ = ∫ x, (fn n x - f x) * g x ∂mu := by
        congr 1
        funext x
        ring
  have hu : Tendsto (fun n => Real.sqrt
      ((∫ x, (fn n x - f x) ^ 2 ∂mu) * (∫ x, g x ^ 2 ∂mu))) atTop (𝓝 0) := by
    simpa using (hlim.mul_const (∫ x, g x ^ 2 ∂mu)).sqrt
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
    (fun _ => norm_nonneg _) fun n => ?_
  rw [he, Real.norm_eq_abs]
  apply Real.le_sqrt_of_sq_le
  rw [sq_abs]
  exact HRS.MS.S111X1.x1_cs_L2 ((hfn n).sub hf) hg

end HRS.MS.ProClosureS111

#print axioms HRS.MS.ProClosureS111.inner_pairing_square_tendsto
#print axioms HRS.MS.ProClosureS111.integral_mul_tendsto_of_square_error
