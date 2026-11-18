import HRS.MS.Fp81S21WindowSup18
import HRS.MS.R2S11Aux10

/-!
# S2.1(iii), packet 9d: parameterized quadratic-field measurability

The compiled source definitions are

* `pairEnergy k X μ = (1/(2N²)) Σᵢ Σⱼ≠ᵢ k (Xᵢ) (Xⱼ) -
  (1/N) Σᵢ ∫ k (Xᵢ) y dμ + (1/2) ∫∫ k x y dμ(y)dμ(x)`;
* `r2QuadField s μ P X v ω f = N * (pairEnergy (commutatorKernel d s
  (fun x => gradient f x)) (X v ω) μ - ∫ pairEnergy ... (X v ω') μ ∂P)`.

For a terminal-time family, the centered field depends jointly on source and
terminal parameters. The existing moving pair-energy adapter has a single real
parameter, so this file gives its product-parameter extension directly from
the compiled moving spatial-integral adapter.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole

private theorem fp81s21_param_pair_row_joint_meas
    {S : Type} [MeasurableSpace S] {d : ℕ}
    {ρ : S → Euc d → ℝ} {k : S → Euc d → Euc d → ℝ}
    (hρ : Measurable (fun q : S × Euc d => ρ q.1 q.2))
    (hρ0 : ∀ a x, 0 ≤ ρ a x)
    (hk : Measurable fun q : S × Euc d × Euc d => k q.1 q.2.1 q.2.2) :
    Measurable (fun q : S × Euc d =>
      ∫ y, k q.1 q.2 y ∂(HRS.Whole.withDensityReal (ρ q.1))) := by
  let ρ' : (S × Euc d) → Euc d → ℝ := fun q y => ρ q.1 y
  let f : (S × Euc d) → Euc d → ℝ := fun q y => k q.1 q.2 y
  have hρ' : Measurable (fun q : (S × Euc d) × Euc d => ρ' q.1 q.2) := by
    exact hρ.comp (measurable_fst.fst.prodMk measurable_snd)
  have hρ'0 : ∀ q y, 0 ≤ ρ' q y := fun q y => hρ0 q.1 y
  have hf : Measurable (fun q : (S × Euc d) × Euc d => f q.1 q.2) := by
    exact hk.comp (measurable_fst.fst.prodMk
      (measurable_fst.snd.prodMk measurable_snd))
  have hr := fp81s21_moving_spatial_integral_meas
    (ρ := ρ') hρ' hρ'0 (f := f) hf
  change Measurable (fun q : S × Euc d =>
    ∫ y, k q.1 q.2 y ∂(HRS.Whole.withDensityReal (fun y => ρ q.1 y))) at hr
  exact hr

private theorem fp81s21_param_config_row_joint_meas
    {S : Type} [MeasurableSpace S] {d N : ℕ}
    {ρ : S → Euc d → ℝ} {k : S → Euc d → Euc d → ℝ}
    (hρ : Measurable (fun q : S × Euc d => ρ q.1 q.2))
    (hρ0 : ∀ a x, 0 ≤ ρ a x)
    (hk : Measurable fun q : S × Euc d × Euc d => k q.1 q.2.1 q.2.2)
    (i : Fin N) :
    Measurable (fun q : S × EucConfig d N =>
      ∫ y, k q.1 (q.2 i) y ∂(HRS.Whole.withDensityReal (ρ q.1))) := by
  let ρ' : (S × EucConfig d N) → Euc d → ℝ := fun q y => ρ q.1 y
  let f : (S × EucConfig d N) → Euc d → ℝ := fun q y => k q.1 (q.2 i) y
  have hρ' : Measurable
      (fun q : (S × EucConfig d N) × Euc d => ρ' q.1 q.2) := by
    exact hρ.comp (measurable_fst.fst.prodMk measurable_snd)
  have hρ'0 : ∀ q y, 0 ≤ ρ' q y := fun q y => hρ0 q.1 y
  have hXi : Measurable fun q : (S × EucConfig d N) × Euc d => q.1.2 i :=
    (measurable_pi_apply i).comp measurable_fst.snd
  have hf : Measurable
      (fun q : (S × EucConfig d N) × Euc d => f q.1 q.2) := by
    exact hk.comp (measurable_fst.fst.prodMk (hXi.prodMk measurable_snd))
  have hr := fp81s21_moving_spatial_integral_meas
    (ρ := ρ') hρ' hρ'0 (f := f) hf
  change Measurable (fun q : S × EucConfig d N =>
    ∫ y, k q.1 (q.2 i) y ∂(HRS.Whole.withDensityReal (fun y => ρ q.1 y))) at hr
  exact hr

private theorem fp81s21_param_double_integral_joint_meas
    {S : Type} [MeasurableSpace S] {d : ℕ}
    {ρ : S → Euc d → ℝ} {k : S → Euc d → Euc d → ℝ}
    (hρ : Measurable (fun q : S × Euc d => ρ q.1 q.2))
    (hρ0 : ∀ a x, 0 ≤ ρ a x)
    (hk : Measurable fun q : S × Euc d × Euc d => k q.1 q.2.1 q.2.2) :
    Measurable (fun a : S =>
      ∫ x, ∫ y, k a x y ∂(HRS.Whole.withDensityReal (ρ a))
        ∂(HRS.Whole.withDensityReal (ρ a))) := by
  have hrow := fp81s21_param_pair_row_joint_meas hρ hρ0 hk
  exact fp81s21_moving_spatial_integral_meas hρ hρ0 hrow

private theorem fp81s21_param_config_pair_sum_joint_meas
    {S : Type} [MeasurableSpace S] {d N : ℕ}
    {k : S → Euc d → Euc d → ℝ}
    (hk : Measurable fun q : S × Euc d × Euc d => k q.1 q.2.1 q.2.2) :
    Measurable (fun q : S × EucConfig d N =>
      ∑ i, ∑ j ∈ Finset.univ.erase i, k q.1 (q.2 i) (q.2 j)) := by
  classical
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
  have hi : Measurable fun q : S × EucConfig d N => q.2 i :=
    (measurable_pi_apply i).comp measurable_snd
  have hj : Measurable fun q : S × EucConfig d N => q.2 j :=
    (measurable_pi_apply j).comp measurable_snd
  exact hk.comp (measurable_fst.prodMk (hi.prodMk hj))

private theorem fp81s21_param_config_row_sum_joint_meas
    {S : Type} [MeasurableSpace S] {d N : ℕ}
    {ρ : S → Euc d → ℝ} {k : S → Euc d → Euc d → ℝ}
    (hρ : Measurable (fun q : S × Euc d => ρ q.1 q.2))
    (hρ0 : ∀ a x, 0 ≤ ρ a x)
    (hk : Measurable fun q : S × Euc d × Euc d => k q.1 q.2.1 q.2.2) :
    Measurable (fun q : S × EucConfig d N =>
      ∑ i, ∫ y, k q.1 (q.2 i) y ∂(HRS.Whole.withDensityReal (ρ q.1))) := by
  classical
  exact Finset.measurable_sum _ fun i _ =>
    fp81s21_param_config_row_joint_meas hρ hρ0 hk i

/-- The explicit finite-sum and spatial-integral formula for a moving pair
energy is jointly measurable over any measurable parameter space. -/
theorem fp81s21_param_pairEnergy_formula_joint_meas
    {S : Type} [MeasurableSpace S] {d N : ℕ}
    {ρ : S → Euc d → ℝ} {k : S → Euc d → Euc d → ℝ}
    (hρ : Measurable (fun q : S × Euc d => ρ q.1 q.2))
    (hρ0 : ∀ a x, 0 ≤ ρ a x)
    (hk : Measurable fun q : S × Euc d × Euc d => k q.1 q.2.1 q.2.2) :
    Measurable (fun q : S × EucConfig d N =>
      (1 / (2 * (N : ℝ) ^ 2)) *
          (∑ i, ∑ j ∈ Finset.univ.erase i, k q.1 (q.2 i) (q.2 j)) -
        (1 / (N : ℝ)) *
          (∑ i, ∫ y, k q.1 (q.2 i) y ∂(HRS.Whole.withDensityReal (ρ q.1))) +
        (1 / 2) *
          (∫ x, ∫ y, k q.1 x y ∂(HRS.Whole.withDensityReal (ρ q.1))
            ∂(HRS.Whole.withDensityReal (ρ q.1)))) := by
  classical
  have hdouble := fp81s21_param_double_integral_joint_meas hρ hρ0 hk
  have hpp := fp81s21_param_config_pair_sum_joint_meas (d := d) (N := N) hk
  have hrows := fp81s21_param_config_row_sum_joint_meas
    (d := d) (N := N) hρ hρ0 hk
  exact ((hpp.const_mul _).sub (hrows.const_mul _)).add
    ((hdouble.comp measurable_fst).const_mul _)

/-- Pointwise, the displayed measurable formula is exactly the compiled
`pairEnergy` definition. -/
theorem fp81s21_param_pairEnergy_eq_formula
    {S : Type} [MeasurableSpace S] {d N : ℕ}
    {ρ : S → Euc d → ℝ} {k : S → Euc d → Euc d → ℝ}
    : (fun q : S × EucConfig d N =>
        pairEnergy (k q.1) q.2 (HRS.Whole.withDensityReal (ρ q.1))) =
      (fun q =>
        (1 / (2 * (N : ℝ) ^ 2)) *
            (∑ i, ∑ j ∈ Finset.univ.erase i, k q.1 (q.2 i) (q.2 j)) -
          (1 / (N : ℝ)) *
            (∑ i, ∫ y, k q.1 (q.2 i) y ∂(HRS.Whole.withDensityReal (ρ q.1))) +
          (1 / 2) *
            (∫ x, ∫ y, k q.1 x y ∂(HRS.Whole.withDensityReal (ρ q.1))
              ∂(HRS.Whole.withDensityReal (ρ q.1)))) := by
  funext q
  rfl

#print axioms fp81s21_param_pairEnergy_formula_joint_meas
#print axioms fp81s21_param_pairEnergy_eq_formula

end HRS.Fp81.S21

end
