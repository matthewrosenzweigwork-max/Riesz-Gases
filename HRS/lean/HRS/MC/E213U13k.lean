import HRS.MC.E213U13j

/-!
# E213U13k: Wick coefficients lie in the second chaos; Fubini-orthogonality for time integrals
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false

noncomputable section

namespace HRS.MC.E213U13

section Fub

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {ξ : ℕ → Ω → ℝ}
  {ν : Measure ℝ} [SFinite ν]

/-- A time integral of second-chaos variables, dominated in `L²` by an integrable-in-time bound, is in the
second chaos (orthogonality + Fubini + dominated convergence). -/
theorem InQ2.of_prod_limit {hξ : IsStdGaussianSeq P ξ}
    {f : ℕ → Ω → ℝ → ℝ} {g B : Ω → ℝ → ℝ} {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hfm : ∀ n, Measurable (Function.uncurry (f n))) (hgm : Measurable (Function.uncurry g))
    (hBm : Measurable (Function.uncurry B)) (hB0 : ∀ ω v, 0 ≤ B ω v)
    (hfQ : ∀ n, ∀ᵐ v ∂ν, InQ2 hξ (fun ω => f n ω v))
    (hlim : ∀ ω v, Tendsto (fun n => f n ω v) atTop (𝓝 (g ω v)))
    (hdom : ∀ n ω v, |f n ω v| ≤ B ω v)
    (hBint : ∀ᵐ ω ∂P, Integrable (B ω) ν)
    (hBL2 : MemLp (fun ω => ∫ v, B ω v ∂ν) 2 P)
    (hZ : Z =ᵐ[P] fun ω => ∫ v, g ω v ∂ν) : InQ2 hξ Z := by
  classical
  refine ⟨hZ2, ?_⟩
  set Q : Submodule ℝ (Lp ℝ 2 P) := Qc (K2 hξ) with hQdef
  have hQclosed : IsClosed (Q : Set (Lp ℝ 2 P)) := Submodule.isClosed_topologicalClosure _
  haveI : CompleteSpace Q := hQclosed.completeSpace_coe
  haveI : Q.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace Q
  suffices h : hZ2.toLp Z ∈ Qᗮᗮ by rwa [Submodule.orthogonal_orthogonal] at h
  rw [Submodule.mem_orthogonal]
  intro w hw
  set wf : Ω → ℝ := (w : Ω → ℝ) with hwf
  have hwL : MemLp wf 2 P := Lp.memLp w
  have hwm : Measurable wf := (Lp.stronglyMeasurable w).measurable
  have hBdomm : AEStronglyMeasurable (fun p : Ω × ℝ => ‖wf p.1‖ * B p.1 p.2) (P.prod ν) :=
    (((hwm.comp measurable_fst).norm).mul hBm).aestronglyMeasurable
  have hBdom : Integrable (fun p : Ω × ℝ => ‖wf p.1‖ * B p.1 p.2) (P.prod ν) := by
    rw [integrable_prod_iff hBdomm]
    refine ⟨?_, ?_⟩
    · filter_upwards [hBint] with ω hω
      exact (hω.const_mul ‖wf ω‖)
    · have : (fun ω => ∫ v, ‖‖wf ω‖ * B ω v‖ ∂ν) = fun ω => ‖wf ω‖ * ∫ v, B ω v ∂ν := by
        funext ω
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun v => ?_)
        simp only [norm_mul, norm_norm, Real.norm_eq_abs, abs_of_nonneg (hB0 ω v), abs_abs]
      rw [this]
      exact hwL.norm.integrable_mul hBL2
  have hGint : ∀ n, Integrable (fun p : Ω × ℝ => wf p.1 * f n p.1 p.2) (P.prod ν) := by
    intro n
    refine hBdom.mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact ((hwm.comp measurable_fst).mul (hfm n)).aestronglyMeasurable
    · rw [norm_mul, Real.norm_eq_abs (f n p.1 p.2)]
      exact mul_le_mul_of_nonneg_left (hdom n p.1 p.2) (norm_nonneg _)
  have hgB : ∀ ω v, |g ω v| ≤ B ω v := fun ω v =>
    le_of_tendsto (continuous_abs.continuousAt.tendsto.comp (hlim ω v)) (Eventually.of_forall fun n => hdom n ω v)
  have hgint : Integrable (fun p : Ω × ℝ => wf p.1 * g p.1 p.2) (P.prod ν) := by
    refine hBdom.mono' ?_ (Eventually.of_forall fun p => ?_)
    · exact ((hwm.comp measurable_fst).mul hgm).aestronglyMeasurable
    · rw [norm_mul, Real.norm_eq_abs (g p.1 p.2)]
      exact mul_le_mul_of_nonneg_left (hgB p.1 p.2) (norm_nonneg _)
  have hT : Tendsto (fun n => ∫ p, wf p.1 * f n p.1 p.2 ∂(P.prod ν)) atTop
      (𝓝 (∫ p, wf p.1 * g p.1 p.2 ∂(P.prod ν))) := by
    refine tendsto_integral_of_dominated_convergence (fun p => ‖wf p.1‖ * B p.1 p.2)
      (fun n => (hGint n).aestronglyMeasurable) hBdom (fun n => Eventually.of_forall fun p => ?_)
      (Eventually.of_forall fun p => (hlim p.1 p.2).const_mul (wf p.1))
    rw [norm_mul, Real.norm_eq_abs (f n p.1 p.2)]
    exact mul_le_mul_of_nonneg_left (hdom n p.1 p.2) (norm_nonneg _)
  have hzero : ∀ n, ∫ p, wf p.1 * f n p.1 p.2 ∂(P.prod ν) = 0 := by
    intro n
    rw [integral_prod_symm _ (hGint n)]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hfQ n] with v hv
    obtain ⟨h1, hc⟩ := hv
    have := integral_mul_eq_inner w (h1.toLp _) (a := wf) (b := fun ω => f n ω v) Filter.EventuallyEq.rfl h1.coeFn_toLp
    simp only [Pi.zero_apply]
    rw [this]
    exact Submodule.inner_left_of_mem_orthogonal hc hw
  have hlimzero : ∫ p, wf p.1 * g p.1 p.2 ∂(P.prod ν) = 0 := by
    refine tendsto_nhds_unique hT ?_
    simp only [hzero]
    exact tendsto_const_nhds
  rw [← integral_mul_eq_inner w (hZ2.toLp Z) (a := wf) (b := Z) Filter.EventuallyEq.rfl hZ2.coeFn_toLp]
  calc ∫ ω, wf ω * Z ω ∂P = ∫ ω, wf ω * ∫ v, g ω v ∂ν ∂P :=
        integral_congr_ae (by filter_upwards [hZ] with ω h; rw [h])
    _ = ∫ ω, ∫ v, wf ω * g ω v ∂ν ∂P := by
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        simp only
        rw [integral_const_mul]
    _ = ∫ p, wf p.1 * g p.1 p.2 ∂(P.prod ν) := (integral_prod _ hgint).symm
    _ = 0 := hlimzero

end Fub

section Wick

open HRS HRS.Sec7

variable {d : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {ξ : ℕ → Ω → ℝ}

/-- A half-Wick quadratic form of a field whose Fourier coefficients lie in the first chaos lies in the
second chaos. -/
theorem InQ2.of_halfWick {hξ : IsStdGaussianSeq P ξ} {hm : ∀ i, Measurable (ξ i)} {r : ℝ}
    {η : Ω → NegSobolev d r}
    (hη : ∀ k, InQ1 hξ hm (fun ω => NegSobolev.fourierCoeff (η ω) k))
    {μ : Measure (Torus d)} {h : Torus d → Torus d → ℝ} {Q : Ω → ℝ}
    (hQm : AEStronglyMeasurable Q P) (hQ : IsHalfWick P η μ h Q) : InQ2 hξ Q := by
  classical
  refine InQ2.of_tendsto (l := atTop)
    (Y := fun (S : Finset (NonzeroLattice d)) ω => (1 / 2 : ℝ) * ∑ k ∈ S, ∑ l ∈ S,
      wickCoeff μ h k l * (NegSobolev.fourierCoeff (η ω) k * NegSobolev.fourierCoeff (η ω) l -
        ∫ ω', NegSobolev.fourierCoeff (η ω') k * NegSobolev.fourierCoeff (η ω') l ∂P)) ?_ hQm ?_
  · intro S
    refine InQ2.const_mul _ ?_
    refine InQ2.sum (Y := fun k ω => ∑ l ∈ S, wickCoeff μ h k l * (NegSobolev.fourierCoeff (η ω) k *
      NegSobolev.fourierCoeff (η ω) l - ∫ ω', NegSobolev.fourierCoeff (η ω') k *
        NegSobolev.fourierCoeff (η ω') l ∂P)) S fun k _ => ?_
    refine InQ2.sum (Y := fun l ω => wickCoeff μ h k l * (NegSobolev.fourierCoeff (η ω) k *
      NegSobolev.fourierCoeff (η ω) l - ∫ ω', NegSobolev.fourierCoeff (η ω') k *
        NegSobolev.fourierCoeff (η ω') l ∂P)) S fun l _ => ?_
    exact InQ2.const_mul _ (InQ2.mul_centered hξ hm (hη k) (hη l))
  · refine hQ.congr fun S => lintegral_congr fun ω => ?_
    rw [enorm_sub_rev, ENNReal.rpow_two]

end Wick

end HRS.MC.E213U13
