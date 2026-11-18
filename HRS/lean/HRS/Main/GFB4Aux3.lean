import HRS.Main.GFB4Aux2

/-!
# GFB4, part 3: the `L²`-limit of Itô sums against weakly continuous test paths is jointly Gaussian
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory Complex
open scoped ENNReal NNReal BigOperators Matrix RealInnerProductSpace

namespace HRS.GF

open HRS HRS.Uniform.Q54c HRS.Uniform.Q07c

theorem gfb4_enorm_sq_euclid {p : ℕ} (v : EuclideanSpace ℝ (Fin p)) :
    ‖v‖ₑ ^ 2 = ∑ a, ‖v a‖ₑ ^ 2 := by
  have h := EuclideanSpace.nnnorm_eq v
  have h2 : ‖v‖₊ ^ 2 = ∑ a, ‖v a‖₊ ^ 2 := by
    rw [h, NNReal.sq_sqrt]
  have : ‖v‖ₑ ^ 2 = ((‖v‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.coe_pow]; rfl
  rw [this, h2, ENNReal.coe_finset_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [ENNReal.coe_pow]; rfl

/-- From `L²` convergence of the coordinates to an a.e. convergent subsequence. -/
theorem gfb4_subseq_ae {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] {p : ℕ}
    {XN : ℕ → Ω → EuclideanSpace ℝ (Fin p)} {X : Ω → EuclideanSpace ℝ (Fin p)}
    (hXN : ∀ N, Measurable (XN N)) (hXm : Measurable X)
    (hL2 : ∀ a, Tendsto (fun N => ∫⁻ ω, ‖X ω a - XN N ω a‖ₑ ^ 2 ∂P) atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂P, Tendsto (fun k => XN (ns k) ω) atTop (𝓝 (X ω)) := by
  have hcoord : ∀ N a, Measurable fun ω => ‖X ω a - XN N ω a‖ₑ := fun N a => by
    have h1 : Measurable fun ω => X ω a := (measurable_pi_apply a).comp (PiLp.continuous_ofLp 2 _).measurable |>.comp hXm
    have h2 : Measurable fun ω => XN N ω a :=
      (measurable_pi_apply a).comp (PiLp.continuous_ofLp 2 _).measurable |>.comp (hXN N)
    exact (h1.sub h2).enorm
  have hsum : ∀ N, ∫⁻ ω, ‖XN N ω - X ω‖ₑ ^ 2 ∂P = ∑ a, ∫⁻ ω, ‖X ω a - XN N ω a‖ₑ ^ 2 ∂P := by
    intro N
    simp_rw [gfb4_enorm_sq_euclid]
    rw [lintegral_finsetSum']
    · refine Finset.sum_congr rfl fun a _ => ?_
      refine lintegral_congr fun ω => ?_
      simp only [PiLp.sub_apply]
      rw [enorm_sub_rev]
    · intro a _
      exact ((hcoord N a).pow_const 2).aemeasurable.congr (Filter.Eventually.of_forall fun ω => by
        simp only [PiLp.sub_apply]; rw [enorm_sub_rev])
  have hzero : Tendsto (fun N => eLpNorm (XN N - X) 2 P) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N => ∫⁻ ω, ‖XN N ω - X ω‖ₑ ^ 2 ∂P) atTop (𝓝 0) := by
      simp_rw [hsum]
      have := tendsto_finset_sum (Finset.univ : Finset (Fin p)) (fun a _ => hL2 a)
      simpa using this
    have e : ∀ N, eLpNorm (XN N - X) 2 P = (∫⁻ ω, ‖XN N ω - X ω‖ₑ ^ 2 ∂P) ^ (1 / 2 : ℝ) := by
      intro N
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) ENNReal.ofNat_ne_top
        ((((hXN N).sub hXm)).aestronglyMeasurable)]
      simp only [ENNReal.toReal_ofNat]
      have : ∀ ω, ‖(XN N - X) ω‖ₑ ^ (2 : ℝ) = ‖XN N ω - X ω‖ₑ ^ 2 := fun ω => by
        rw [ENNReal.rpow_two]; rfl
      simp_rw [this]
    simp_rw [e]
    have := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp h1
    have h0 : (0 : ℝ≥0∞) ^ (1 / 2 : ℝ) = 0 := ENNReal.zero_rpow_of_pos (by norm_num)
    rw [h0] at this
    exact this
  have hmeas := tendstoInMeasure_of_tendsto_eLpNorm (μ := P) (f := XN) (g := X) (p := 2)
    (by norm_num) hzero
  exact hmeas.exists_seq_tendsto_ae

theorem gfb4_charFun_limit_ae {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    {p : ℕ} {XN : ℕ → Ω → EuclideanSpace ℝ (Fin p)} {X : Ω → EuclideanSpace ℝ (Fin p)}
    (hXN : ∀ N, Measurable (XN N)) (hXm : Measurable X)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun N => XN N ω) atTop (𝓝 (X ω)))
    (Q : EuclideanSpace ℝ (Fin p) → ℝ) (QN : ℕ → EuclideanSpace ℝ (Fin p) → ℝ)
    (hQ : ∀ x, Tendsto (fun N => QN N x) atTop (𝓝 (Q x)))
    (hchar : ∀ N x, charFun (P.map (XN N)) x = Complex.exp (-(QN N x : ℂ) / 2))
    (x : EuclideanSpace ℝ (Fin p)) :
    charFun (P.map X) x = Complex.exp (-(Q x : ℂ) / 2) := by
  have e1 : charFun (P.map X) x = ∫ ω, Complex.exp (inner ℝ (X ω) (x) * Complex.I) ∂P := by
    rw [charFun_apply, integral_map hXm.aemeasurable]
    exact (by fun_prop : Continuous fun y : EuclideanSpace ℝ (Fin p) =>
      Complex.exp (inner ℝ (y) (x) * Complex.I)).aestronglyMeasurable
  have e2 : ∀ N, charFun (P.map (XN N)) x = ∫ ω, Complex.exp (inner ℝ (XN N ω) (x) * Complex.I) ∂P := by
    intro N
    rw [charFun_apply, integral_map (hXN N).aemeasurable]
    exact (by fun_prop : Continuous fun y : EuclideanSpace ℝ (Fin p) =>
      Complex.exp (inner ℝ (y) (x) * Complex.I)).aestronglyMeasurable
  have hT1 : Tendsto (fun N => ∫ ω, Complex.exp (inner ℝ (XN N ω) (x) * Complex.I) ∂P) atTop
      (𝓝 (∫ ω, Complex.exp (inner ℝ (X ω) (x) * Complex.I) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) (fun N => ?_)
      (integrable_const _) (fun N => Filter.Eventually.of_forall fun ω => ?_) ?_
    · exact (by fun_prop : Continuous fun y : EuclideanSpace ℝ (Fin p) =>
        Complex.exp (inner ℝ (y) (x) * Complex.I)).measurable.comp (hXN N) |>.aestronglyMeasurable
    · rw [Complex.norm_exp_ofReal_mul_I]
    · filter_upwards [hlim] with ω hω
      exact ((by fun_prop : Continuous fun y : EuclideanSpace ℝ (Fin p) =>
        Complex.exp (inner ℝ (y) (x) * Complex.I)).tendsto (X ω)).comp hω
  have hT2 : Tendsto (fun N => Complex.exp (-(QN N x : ℂ) / 2)) atTop (𝓝 (Complex.exp (-(Q x : ℂ) / 2))) := by
    have := (Complex.continuous_ofReal.tendsto _).comp (hQ x)
    exact ((Complex.continuous_exp.tendsto _).comp ((this.neg).div_const 2))
  rw [e1]
  refine tendsto_nhds_unique hT1 ?_
  refine hT2.congr fun N => ?_
  rw [← hchar N x, e2 N]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

theorem gfb4_measurable_of_weak {Z : Type*} [MeasurableSpace Z] {y : Z → H}
    (hw : ∀ x : H, Measurable fun σ => inner ℝ (y σ) x) : Measurable y := by
  obtain ⟨ι, hι, b, -⟩ := HilbertCLTAux.exists_hilbertBasis_type (H := H)
  have := hι
  refine measurable_of_inner_basis b fun i => ?_
  have : (fun z => inner ℝ (b i) (y z)) = fun z => inner ℝ (y z) (b i) :=
    funext fun z => real_inner_comm _ _
  rw [this]
  exact hw (b i)

end HRS.GF
