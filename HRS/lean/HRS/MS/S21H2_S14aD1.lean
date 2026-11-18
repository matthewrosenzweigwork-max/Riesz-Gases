import HRS.MS.S21G2_K11bA
import HRS.Whole.Round2

/-!
# S21H2, packet R26-T3.S14a (part D1): the centered `L²` kernel and its action on mean-zero functions

For `k ∈ L²(μ⊗μ)` (`μ` a probability measure on `ℝ^d`): the marginals `m(x) = ∫ k(x,y)dμ(y)`, `m'(y) = ∫ k(x,y)dμ(x)` lie in `L²(μ)`,
the centered kernel `c = r2CenterKernel μ k` lies in `L²(μ⊗μ)`, a.e. slice `c(x,·)` lies in `L²_0(μ)`, and for `u ∈ L²_0(μ)`:
`∫ c(x,y) u(y) dμ(y) = ∫ k(x,y)u(y)dμ(y) - ∬ k(x',y)u(y)` for a.e. `x`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3

variable {d : ℕ} (μ : Measure (HRS.Euc d)) [IsProbabilityMeasure μ] {k : HRS.Euc d → HRS.Euc d → ℝ}

theorem s21h2_sq_integral_le {f : HRS.Euc d → ℝ} (hf : MemLp f 2 μ) :
    (∫ y, f y ∂μ) ^ 2 ≤ ∫ y, f y ^ 2 ∂μ := by
  have h := variance_eq_sub hf
  have h0 := variance_nonneg f μ
  simp only [Pi.pow_apply] at h
  linarith

theorem s21h2_slice_memLp (hk : MemLp (fun z : HRS.Euc d × HRS.Euc d => k z.1 z.2) 2 (μ.prod μ)) :
    ∀ᵐ x ∂μ, MemLp (fun y => k x y) 2 μ := by
  filter_upwards [hk.integrable_sq.prod_right_ae, hk.aestronglyMeasurable.prodMk_left] with x h1 h2
  exact (memLp_two_iff_integrable_sq h2).2 h1

theorem s21h2_m_memLp (hk : MemLp (fun z : HRS.Euc d × HRS.Euc d => k z.1 z.2) 2 (μ.prod μ)) :
    MemLp (fun x => ∫ y, k x y ∂μ) 2 μ := by
  have hm : AEStronglyMeasurable (fun x => ∫ y, k x y ∂μ) μ := hk.aestronglyMeasurable.integral_prod_right'
  refine (memLp_two_iff_integrable_sq hm).2 ?_
  refine Integrable.mono' (hk.integrable_sq.integral_prod_left) (hm.pow 2) ?_
  filter_upwards [s21h2_slice_memLp μ hk] with x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact s21h2_sq_integral_le μ hx

theorem s21h2_m'_memLp (hk : MemLp (fun z : HRS.Euc d × HRS.Euc d => k z.1 z.2) 2 (μ.prod μ)) :
    MemLp (fun y => ∫ x, k x y ∂μ) 2 μ := by
  have hk' : MemLp (fun z : HRS.Euc d × HRS.Euc d => (fun a b => k b a) z.1 z.2) 2 (μ.prod μ) := by
    have := hk.comp_measurePreserving (Measure.measurePreserving_swap (μ := μ) (ν := μ))
    exact this
  exact s21h2_m_memLp μ (k := fun a b => k b a) hk'

theorem s21h2_c_memLp (hk : MemLp (fun z : HRS.Euc d × HRS.Euc d => k z.1 z.2) 2 (μ.prod μ)) :
    MemLp (fun z : HRS.Euc d × HRS.Euc d => HRS.Whole.r2CenterKernel μ k z.1 z.2) 2 (μ.prod μ) := by
  have h1 := (s21h2_m_memLp μ hk).comp_fst μ
  have h2 := (s21h2_m'_memLp μ hk).comp_snd μ
  have h3 : MemLp (fun _ : HRS.Euc d × HRS.Euc d => ∫ x', ∫ y', k x' y' ∂μ ∂μ) 2 (μ.prod μ) :=
    memLp_const _
  exact ((hk.sub h1).sub h2).add h3

theorem s21h2_int_m' (hk : MemLp (fun z : HRS.Euc d × HRS.Euc d => k z.1 z.2) 2 (μ.prod μ)) :
    ∫ y, (∫ x, k x y ∂μ) ∂μ = ∫ x, ∫ y, k x y ∂μ ∂μ :=
  (integral_integral_swap (f := k) (hk.integrable one_le_two)).symm

theorem s21h2_c_slice (hk : MemLp (fun z : HRS.Euc d × HRS.Euc d => k z.1 z.2) 2 (μ.prod μ)) :
    ∀ᵐ x ∂μ, MemLp (fun y => HRS.Whole.r2CenterKernel μ k x y) 2 μ ∧
      ∫ y, HRS.Whole.r2CenterKernel μ k x y ∂μ = 0 := by
  filter_upwards [s21h2_slice_memLp μ hk] with x hx
  have hm' := s21h2_m'_memLp μ hk
  refine ⟨((hx.sub (memLp_const _)).sub hm').add (memLp_const _), ?_⟩
  have i1 : Integrable (fun y => k x y) μ := hx.integrable one_le_two
  have i3 : Integrable (fun y => ∫ x, k x y ∂μ) μ := hm'.integrable one_le_two
  show ∫ y, k x y - (∫ y', k x y' ∂μ) - (∫ x', k x' y ∂μ) + ∫ x', ∫ y', k x' y' ∂μ ∂μ ∂μ = 0
  have j1 : Integrable (fun y => k x y - ∫ y', k x y' ∂μ) μ := i1.sub (integrable_const _)
  have j2 : Integrable (fun y => k x y - (∫ y', k x y' ∂μ) - ∫ x', k x' y ∂μ) μ := j1.sub i3
  rw [integral_add j2 (integrable_const _), integral_sub j1 i3, integral_sub i1 (integrable_const _),
    s21h2_int_m' μ hk]
  simp

theorem s21h2_c_apply (hk : MemLp (fun z : HRS.Euc d × HRS.Euc d => k z.1 z.2) 2 (μ.prod μ))
    {u : HRS.Euc d → ℝ} (hu : MemLp u 2 μ) (hu0 : ∫ y, u y ∂μ = 0) :
    ∀ᵐ x ∂μ, ∫ y, HRS.Whole.r2CenterKernel μ k x y * u y ∂μ =
      (∫ y, k x y * u y ∂μ) - ∫ x', ∫ y, k x' y * u y ∂μ ∂μ := by
  have hm' := s21h2_m'_memLp μ hk
  have hui : Integrable u μ := hu.integrable one_le_two
  have i4 : Integrable (fun y => (∫ x, k x y ∂μ) * u y) μ := hm'.integrable_mul hu
  have hP : Integrable (fun z : HRS.Euc d × HRS.Euc d => k z.1 z.2 * ((1 : HRS.Euc d → ℝ) z.1 * u z.2))
      (μ.prod μ) := (s21g2_k11b_B_bound hk (memLp_const 1) hu).1
  have hP' : Integrable (Function.uncurry fun x' y => k x' y * u y) (μ.prod μ) :=
    hP.congr (ae_of_all _ fun z => by simp [Function.uncurry])
  have hswap : ∫ x', ∫ y, k x' y * u y ∂μ ∂μ = ∫ y, (∫ x, k x y ∂μ) * u y ∂μ := by
    rw [integral_integral_swap hP']
    exact integral_congr_ae (ae_of_all _ fun y => integral_mul_const _ _)
  filter_upwards [s21h2_slice_memLp μ hk] with x hx
  have i1 : Integrable (fun y => k x y * u y) μ := hx.integrable_mul hu
  have e : ∀ y, HRS.Whole.r2CenterKernel μ k x y * u y =
      k x y * u y - (∫ y', k x y' ∂μ) * u y - (∫ x, k x y ∂μ) * u y +
        (∫ x', ∫ y', k x' y' ∂μ ∂μ) * u y := fun y => by
    simp only [HRS.Whole.r2CenterKernel]; ring
  simp_rw [e]
  have j1 : Integrable (fun y => k x y * u y - (∫ y', k x y' ∂μ) * u y) μ := i1.sub (hui.const_mul _)
  have j2 : Integrable (fun y => k x y * u y - (∫ y', k x y' ∂μ) * u y - (∫ x, k x y ∂μ) * u y) μ :=
    j1.sub i4
  rw [integral_add j2 (hui.const_mul _), integral_sub j1 i4, integral_sub i1 (hui.const_mul _),
    integral_const_mul, integral_const_mul, hu0, hswap]
  ring

end HRS.MS.R26T3
