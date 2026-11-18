import HRS.MS.R2ChaosAux11
import HRS.MS.S21G2_K11a

/-!
# S21G2 K11b (part A) -- the `L²(μ⊗μ)` kernel bilinear form (R26-T3.K11b)

`B(f,g) = ∬ h(x,y) f(x) g(y)` for `h ∈ L²(μ⊗μ)`, `f, g ∈ L²(μ)`: integrable, `|B(f,g)| ≤ ‖h‖₂ ‖f‖₂ ‖g‖₂`.
Helper names carry the prefix `s21g2_k11b_`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3

section Bilinear

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ] {h : E → E → ℝ}

theorem s21g2_k11b_tensor_memLp {f g : E → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    MemLp (fun z : E × E => f z.1 * g z.2) 2 (μ.prod μ) ∧
      ∫ z : E × E, (f z.1 * g z.2) ^ 2 ∂(μ.prod μ) = (∫ x, f x ^ 2 ∂μ) * ∫ y, g y ^ 2 ∂μ := by
  have hi : Integrable (fun z : E × E => (f z.1) ^ 2 * (g z.2) ^ 2) (μ.prod μ) :=
    hf.integrable_sq.mul_prod hg.integrable_sq
  have hm : AEStronglyMeasurable (fun z : E × E => f z.1 * g z.2) (μ.prod μ) :=
    (hf.aestronglyMeasurable.comp_fst).mul hg.aestronglyMeasurable.comp_snd
  refine ⟨(memLp_two_iff_integrable_sq hm).2 (hi.congr (ae_of_all _ fun z => by ring)), ?_⟩
  simp_rw [mul_pow]
  exact integral_prod_mul (fun x => f x ^ 2) (fun y => g y ^ 2)

theorem s21g2_k11b_B_bound (hh : MemLp (fun z : E × E => h z.1 z.2) 2 (μ.prod μ))
    {f g : E → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun z : E × E => h z.1 z.2 * (f z.1 * g z.2)) (μ.prod μ) ∧
    |∫ z : E × E, h z.1 z.2 * (f z.1 * g z.2) ∂(μ.prod μ)| ≤
      Real.sqrt (∫ z : E × E, h z.1 z.2 ^ 2 ∂(μ.prod μ)) *
        (Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ y, g y ^ 2 ∂μ)) := by
  obtain ⟨hT, hTi⟩ := s21g2_k11b_tensor_memLp hf hg
  have hint : Integrable (fun z : E × E => h z.1 z.2 * (f z.1 * g z.2)) (μ.prod μ) := hh.integrable_mul hT
  refine ⟨hint, ?_⟩
  refine (abs_integral_le_integral_abs).trans ?_
  have h1 : MemLp (fun z : E × E => |h z.1 z.2|) (ENNReal.ofReal 2) (μ.prod μ) := by
    simpa [Real.norm_eq_abs] using hh.norm
  have h2 : MemLp (fun z : E × E => |f z.1 * g z.2|) (ENNReal.ofReal 2) (μ.prod μ) := by
    simpa [Real.norm_eq_abs] using hT.norm
  have := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ.prod μ) (p := 2) (q := 2) Real.HolderConjugate.two_two
    (ae_of_all _ fun z => abs_nonneg (h z.1 z.2)) (ae_of_all _ fun z => abs_nonneg (f z.1 * g z.2)) h1 h2
  have e : ∀ z : E × E, |h z.1 z.2 * (f z.1 * g z.2)| = |h z.1 z.2| * |f z.1 * g z.2| := fun z => abs_mul _ _
  simp_rw [e]
  refine this.trans (le_of_eq ?_)
  simp only [Real.rpow_two, sq_abs, hTi]
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sqrt_mul (integral_nonneg fun _ => sq_nonneg _)]

end Bilinear

section Expand

variable {d : ℕ} {μ : Measure (HRS.Euc d)} [IsProbabilityMeasure μ] {a : ℕ → HRS.Euc d → ℝ}

/-- Orthonormal expansion in `L²_0(μ)`: Pythagoras and Parseval for `F_n = ∑_{i<n} ⟪f, e_i⟫ e_i`. -/
theorem s21g2_k11b_expand (ha : HRS.Whole.IsR2ZeroMeanONB μ a) {f : HRS.Euc d → ℝ} (hf : MemLp f 2 μ)
    (hf0 : ∫ x, f x ∂μ = 0) :
    (∀ n, MemLp (fun x => ∑ i ∈ Finset.range n,
      (∫ y, f y * HRS.Whole.projMean μ (a i) y ∂μ) * HRS.Whole.projMean μ (a i) x) 2 μ) ∧
    (∀ n, ∫ x, (∑ i ∈ Finset.range n, (∫ y, f y * HRS.Whole.projMean μ (a i) y ∂μ) *
        HRS.Whole.projMean μ (a i) x) ^ 2 ∂μ ≤ ∫ x, f x ^ 2 ∂μ) ∧
    Tendsto (fun n => ∫ x, (∑ i ∈ Finset.range n, (∫ y, f y * HRS.Whole.projMean μ (a i) y ∂μ) *
        HRS.Whole.projMean μ (a i) x - f x) ^ 2 ∂μ) atTop (𝓝 0) := by
  obtain ⟨hat, hon, hcomp⟩ := ha
  set e : ℕ → HRS.Euc d → ℝ := fun i => HRS.Whole.projMean μ (a i) with he
  set γ : ℕ → ℝ := fun i => ∫ y, f y * e i y ∂μ with hγ
  have hem : ∀ i, MemLp (e i) 2 μ := fun i => HRS.MS.R2Chaos.s94_memLp_projMean (hat i)
  have hFm : ∀ n, MemLp (fun x => ∑ i ∈ Finset.range n, γ i * e i x) 2 μ := fun n =>
    memLp_finsetSum (f := fun i x => γ i * e i x) _ fun i _ => (hem i).const_mul (γ i)
  have hee : ∀ i j, Integrable (fun x => e i x * e j x) μ := fun i j => (hem i).integrable_mul (hem j)
  have hfe : ∀ i, Integrable (fun x => f x * e i x) μ := fun i => hf.integrable_mul (hem i)
  have hon' : ∀ i j, ∫ x, e i x * e j x ∂μ = if i = j then 1 else 0 := hon
  have hF2 : ∀ n, ∫ x, (∑ i ∈ Finset.range n, γ i * e i x) ^ 2 ∂μ = ∑ i ∈ Finset.range n, γ i ^ 2 := by
    intro n
    have : ∀ x, (∑ i ∈ Finset.range n, γ i * e i x) ^ 2 =
        ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, (γ i * γ j) * (e i x * e j x) := fun x => by
      rw [sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    simp_rw [this]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hee i j).const_mul _]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [integral_finsetSum _ fun j _ => (hee i j).const_mul _]
    simp_rw [integral_const_mul, hon']
    simp [Finset.sum_ite_eq, hi, sq]
  have hFf : ∀ n, ∫ x, f x * (∑ i ∈ Finset.range n, γ i * e i x) ∂μ = ∑ i ∈ Finset.range n, γ i ^ 2 := by
    intro n
    have : ∀ x, f x * (∑ i ∈ Finset.range n, γ i * e i x) = ∑ i ∈ Finset.range n, γ i * (f x * e i x) :=
      fun x => by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    simp_rw [this]
    rw [integral_finsetSum _ fun i _ => (hfe i).const_mul _]
    exact Finset.sum_congr rfl fun i _ => by rw [integral_const_mul]; simp [hγ, sq]
  have hpyth : ∀ n, ∫ x, (∑ i ∈ Finset.range n, γ i * e i x - f x) ^ 2 ∂μ =
      ∫ x, f x ^ 2 ∂μ - ∑ i ∈ Finset.range n, γ i ^ 2 := by
    intro n
    have hF := (hFm n).integrable_sq
    have hf2 := hf.integrable_sq
    have hcross : Integrable (fun x => f x * (∑ i ∈ Finset.range n, γ i * e i x)) μ :=
      hf.integrable_mul (hFm n)
    have : ∀ x, (∑ i ∈ Finset.range n, γ i * e i x - f x) ^ 2 =
        (∑ i ∈ Finset.range n, γ i * e i x) ^ 2 - 2 * (f x * (∑ i ∈ Finset.range n, γ i * e i x)) + f x ^ 2 :=
      fun x => by ring
    simp_rw [this]
    rw [integral_add (f := fun x => (∑ i ∈ Finset.range n, γ i * e i x) ^ 2 -
        2 * (f x * (∑ i ∈ Finset.range n, γ i * e i x))) (g := fun x => f x ^ 2)
      (hF.sub (hcross.const_mul 2)) hf2,
      integral_sub (f := fun x => (∑ i ∈ Finset.range n, γ i * e i x) ^ 2)
        (g := fun x => 2 * (f x * (∑ i ∈ Finset.range n, γ i * e i x))) hF (hcross.const_mul 2),
      integral_const_mul, hF2, hFf]
    ring
  refine ⟨hFm, fun n => ?_, ?_⟩
  · have := hpyth n
    have h0 : 0 ≤ ∫ x, (∑ i ∈ Finset.range n, γ i * e i x - f x) ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
    calc ∫ x, (∑ i ∈ Finset.range n, γ i * e i x) ^ 2 ∂μ = ∑ i ∈ Finset.range n, γ i ^ 2 := hF2 n
      _ ≤ ∫ x, f x ^ 2 ∂μ := by linarith
  · have hP := HRS.MS.R2Chaos.s94_parseval (μ := μ) hat hon hcomp hf hf0
    have hT := (tendsto_const_nhds (x := ∫ x, f x ^ 2 ∂μ)).sub hP
    rw [sub_self] at hT
    exact hT.congr fun n => (hpyth n).symm

end Expand

end HRS.MS.R26T3
