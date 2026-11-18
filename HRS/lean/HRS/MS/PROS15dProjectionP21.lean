import HRS.MS.PROS15dPhysicalTiltConvergence
import HRS.MS.S21H2_S14a

/-!
# S15d: actual spectral projection tails under a fixed square-integrable tilt

A complete Hilbert basis of centered spatial L² classes is projected
on the original ProductGaussian probability space. The resulting physical
first-chaos tails converge in L² under any fixed normalized exponential
tilt with a square-integrable density, including nontrivial Riesz tilts.
No smoothness of the spatial basis is assumed.
-/
set_option autoImplicit false
noncomputable section
open HRS MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators RealInnerProductSpace
namespace HRS.MS.R26T3

theorem s15d_hilbert_basis_physical_tilt_tail
    {d : ℕ} {μ : Measure (HRS.Euc d)}
    [IsProbabilityMeasure μ]
    (I : ProductGaussian μ)
    (b : HilbertBasis ℕ ℝ (s21h2_V μ))
    (v : s21h2_V μ)
    (W : I.Ω → ℝ) (hW : AEMeasurable W I.P)
    (hExp1 : Integrable (fun ω => Real.exp (-W ω)) I.P)
    (hExp2 : Integrable (fun ω => Real.exp (-(2 * W ω))) I.P) :
    Tendsto (fun n => ∫ ω,
      (I.η (fun x => (((v - ∑ j ∈ Finset.range n,
        inner ℝ (b j) v • b j : s21h2_V μ) : Lp ℝ 2 μ) x)) ω)^2
        ∂(r26t3_tilt I.P W)) atTop (𝓝 0) := by
  classical
  let r : ℕ → s21h2_V μ :=
    fun n => v - ∑ j ∈ Finset.range n, inner ℝ (b j) v • b j
  have hHas : HasSum (fun j => inner ℝ (b j) v • b j) v := by
    simpa only [b.repr_apply_apply] using b.hasSum_repr v
  have hT : Tendsto (fun n => ∑ j ∈ Finset.range n,
      inner ℝ (b j) v • b j) atTop (𝓝 v) := hHas.tendsto_sum_nat
  have hNorm : Tendsto (fun n => ‖r n‖) atTop (𝓝 0) := by
    have hSub := (tendsto_const_nhds (x := v)).sub hT
    have h := hSub.norm
    simpa only [r, sub_self, norm_zero] using h
  let f : ℕ → HRS.Euc d → ℝ :=
    fun n x => ((r n : Lp ℝ 2 μ) : HRS.Euc d → ℝ) x
  have hf : ∀ n, MemLp (f n) 2 μ := fun n => Lp.memLp _
  have hSquare : ∀ n, (∫ x, (f n x)^2 ∂μ) = ‖r n‖^2 := by
    intro n
    have hi := s21h2_L2_inner (hf n) (hf n)
    have hcoe : ((hf n).toLp (f n)) = (r n : Lp ℝ 2 μ) := by
      exact Lp.toLp_coeFn (r n : Lp ℝ 2 μ) (hf n)
    rw [hcoe, real_inner_self_eq_norm_sq] at hi
    convert hi.symm using 1
    · congr 1; funext x; ring
    · rfl
  have hSp : Tendsto (fun n => ∫ x, (f n x)^2 ∂μ) atTop (𝓝 0) := by
    have ht := hNorm.pow 2
    simpa only [hSquare, zero_pow (by norm_num : (2:ℕ) ≠ 0)] using ht
  simpa only [f, r] using
    s15d_physical_tilted_second_tendsto_of_spatial_second
      I W hW hExp1 hExp2 f hf hSp

#print axioms s15d_hilbert_basis_physical_tilt_tail
end HRS.MS.R26T3
