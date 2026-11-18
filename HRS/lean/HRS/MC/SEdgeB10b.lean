import HRS.MC.SEdgeB10a

/-!
# Packet B10b: leading CLT (relocated proof of `sed_B10b_clt`)

Levy's continuity theorem (`ProbabilityMeasure.tendsto_iff_tendsto_charFun`) reduces the weak convergence of the
law of `W_N` to the convergence of `E cos<xi,W_N>`, `E sin<xi,W_N>` to the same expectations under
`N(0,C)`; both are `C_b^5` tests, so B10a gives a rate `K/sqrt N`.  (The explicit Gaussian characteristic
function is not needed: B10a compares with the Gaussian expectation directly.)
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.SEdge.B10b

open HRS.Sec7

/-! ### `cos`, `sin` and their negatives: all derivatives bounded by one -/

def b10b_P (g : ℝ → ℝ) : Prop :=
  g = Real.cos ∨ g = (fun y => -Real.cos y) ∨ g = Real.sin ∨ g = (fun y => -Real.sin y)

theorem b10b_P_deriv {g : ℝ → ℝ} (hg : b10b_P g) : b10b_P (deriv g) := by
  rcases hg with rfl | rfl | rfl | rfl
  · right; right; right
    funext y; simp [Real.deriv_cos]
  · right; right; left
    funext y
    rw [deriv.fun_neg, Real.deriv_cos]
    simp
  · left
    exact Real.deriv_sin
  · right; left
    funext y
    rw [deriv.fun_neg, Real.deriv_sin]

theorem b10b_P_iter (n : ℕ) {g : ℝ → ℝ} (hg : b10b_P g) : b10b_P (iteratedDeriv n g) := by
  induction n with
  | zero => simpa using hg
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact b10b_P_deriv ih

theorem b10b_P_bound {g : ℝ → ℝ} (hg : b10b_P g) (y : ℝ) : |g y| ≤ 1 := by
  rcases hg with rfl | rfl | rfl | rfl
  · exact Real.abs_cos_le_one y
  · simpa using Real.abs_cos_le_one y
  · exact Real.abs_sin_le_one y
  · simpa using Real.abs_sin_le_one y

theorem b10b_P_contDiff {g : ℝ → ℝ} (hg : b10b_P g) : ContDiff ℝ ⊤ g := by
  rcases hg with rfl | rfl | rfl | rfl
  · exact Real.contDiff_cos
  · exact Real.contDiff_cos.neg
  · exact Real.contDiff_sin
  · exact Real.contDiff_sin.neg

theorem b10b_memCb {p : ℕ} (k : ℕ) {g : ℝ → ℝ} (hg : b10b_P g)
    (L : EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ) : MemCb k (fun x => g (L x)) := by
  refine ⟨(b10b_P_contDiff hg).of_le le_top |>.comp L.contDiff, fun j hj => ?_⟩
  refine ⟨‖L‖ ^ j, ?_⟩
  rintro _ ⟨x, rfl⟩
  have hcd : ContDiff ℝ j g := (b10b_P_contDiff hg).of_le le_top
  have e := L.iteratedFDeriv_comp_right (f := g) hcd x (i := j) le_rfl
  have e' : iteratedFDeriv ℝ j (fun x => g (L x)) x = iteratedFDeriv ℝ j (g ∘ L) x := rfl
  show ‖iteratedFDeriv ℝ j (fun x => g (L x)) x‖ ≤ ‖L‖ ^ j
  rw [e', e]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have h1 : ‖iteratedFDeriv ℝ j g (L x)‖ ≤ 1 := by
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    rw [Real.norm_eq_abs]
    exact b10b_P_bound (b10b_P_iter j hg) _
  calc ‖iteratedFDeriv ℝ j g (L x)‖ * ‖L‖ ^ j ≤ 1 * ‖L‖ ^ j :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = ‖L‖ ^ j := one_mul _

/-! ### characteristic function through cos and sin -/

theorem b10b_charFun {p : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin p))) [IsProbabilityMeasure μ]
    (t : EuclideanSpace ℝ (Fin p)) :
    charFun μ t = ((∫ x, Real.cos (inner ℝ x t) ∂μ : ℝ) : ℂ) +
      ((∫ x, Real.sin (inner ℝ x t) ∂μ : ℝ) : ℂ) * Complex.I := by
  have hc : Continuous (fun x : EuclideanSpace ℝ (Fin p) => inner ℝ x t) := by fun_prop
  have h1 : Integrable (fun x : EuclideanSpace ℝ (Fin p) => Real.cos (inner ℝ x t)) μ :=
    Integrable.of_bound (Real.continuous_cos.comp hc).aestronglyMeasurable 1
      (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using Real.abs_cos_le_one _)
  have h2 : Integrable (fun x : EuclideanSpace ℝ (Fin p) => Real.sin (inner ℝ x t)) μ :=
    Integrable.of_bound (Real.continuous_sin.comp hc).aestronglyMeasurable 1
      (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using Real.abs_sin_le_one _)
  rw [charFun_apply]
  have : ∀ x : EuclideanSpace ℝ (Fin p),
      Complex.exp (((inner ℝ x t : ℝ) : ℂ) * Complex.I) =
        ((Real.cos (inner ℝ x t) : ℝ) : ℂ) + ((Real.sin (inner ℝ x t) : ℝ) : ℂ) * Complex.I := by
    intro x
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp_rw [this]
  rw [integral_add h1.ofReal (h2.ofReal.mul_const _), integral_mul_const,
    integral_complex_ofReal, integral_complex_ofReal]

section Main

variable {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {β : ℝ} (hβ : 0 ≤ β)
  {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ)
include hd hs0 hs hβ hρ

theorem b10b_meas {p N : ℕ} (hN : 1 ≤ N) {φ : Fin p → Torus d → ℝ}
    (hφ : ∀ a, Torus.IsSmooth (φ a)) (Q : Measure (Config d N)) :
    Measurable (centeredStat Q φ) := by
  have hφc : ∀ a, Continuous (φ a) := fun a => HRS.Q66.q66_cont_of_smooth (hφ a)
  unfold centeredStat
  exact (PiLp.continuous_toLp 2 _).measurable.comp (measurable_pi_iff.2 fun a =>
    measurable_const.mul ((HRS.MC.SEdge.B5b.b5b_pair_meas hN (hφc a).measurable).sub
      measurable_const))

theorem b10b_conv {p : ℕ} {φ : Fin p → Torus d → ℝ} (hφ : ∀ a, Torus.IsSmooth (φ a))
    {F : EuclideanSpace ℝ (Fin p) → ℝ} (hF : MemCb 5 F) :
    Tendsto (fun n : ℕ => ∫ X, F (centeredStat (sed_Q d s (n + 1) β ρ) φ X)
        ∂(sed_Q d s (n + 1) β ρ)) atTop
      (𝓝 (∫ z, F z ∂(multivariateGaussian 0 (sed_Cmat d s β ρ φ)))) := by
  obtain ⟨K, hK⟩ := HRS.MC.SEdge.B10a.sed_B10a_rate_proof hd hs0 hs hβ hρ hφ hF
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) (g := fun n : ℕ => K / Real.sqrt (n + 1 : ℕ)) ?_
  · rw [Real.norm_eq_abs]
    exact hK (n + 1) (by omega)
  · refine tendsto_const_nhds.div_atTop ?_
    refine Real.tendsto_sqrt_atTop.comp ?_
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)

theorem sed_B10b_clt_proof {p : ℕ} {φ : Fin p → Torus d → ℝ} (hφ : ∀ a, Torus.IsSmooth (φ a))
    {Ψ : EuclideanSpace ℝ (Fin p) → ℝ} (hΨc : Continuous Ψ) (hΨb : ∃ M, ∀ z, |Ψ z| ≤ M) :
    Tendsto (fun N : ℕ => ∫ X, Ψ (centeredStat (sed_Q d s N β ρ) φ X) ∂(sed_Q d s N β ρ)) atTop
      (𝓝 (∫ z, Ψ z ∂(multivariateGaussian 0 (sed_Cmat d s β ρ φ)))) := by
  suffices key : Tendsto (fun n : ℕ => ∫ X, Ψ (centeredStat (sed_Q d s (n + 1) β ρ) φ X)
      ∂(sed_Q d s (n + 1) β ρ)) atTop
      (𝓝 (∫ z, Ψ z ∂(multivariateGaussian 0 (sed_Cmat d s β ρ φ)))) from
    (tendsto_add_atTop_iff_nat (f := fun N : ℕ => ∫ X, Ψ (centeredStat (sed_Q d s N β ρ) φ X)
      ∂(sed_Q d s N β ρ)) 1).1 key
  set G := multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) (sed_Cmat d s β ρ φ) with hG
  have hGp : IsProbabilityMeasure G := inferInstance
  have hQ : ∀ n : ℕ, IsProbabilityMeasure (sed_Q d s (n + 1) β ρ) := fun n =>
    HRS.MC.SEdge.B4b.b4b_isProb hd hs0 hs hβ hρ (n + 1) (by omega)
  have hWm : ∀ n : ℕ, Measurable (centeredStat (sed_Q d s (n + 1) β ρ) φ) := fun n =>
    b10b_meas hd hs0 hs hβ hρ (by omega) hφ _
  let μ : ℕ → ProbabilityMeasure (EuclideanSpace ℝ (Fin p)) := fun n =>
    ⟨(sed_Q d s (n + 1) β ρ).map (centeredStat (sed_Q d s (n + 1) β ρ) φ),
      (Measure.isProbabilityMeasure_map_iff (hWm n).aemeasurable).2 (hQ n)⟩
  let μ0 : ProbabilityMeasure (EuclideanSpace ℝ (Fin p)) := ⟨G, hGp⟩
  have hlim : Tendsto μ atTop (𝓝 μ0) := by
    refine ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 fun t => ?_
    have hmu : ∀ n, charFun (μ n : Measure (EuclideanSpace ℝ (Fin p))) t =
        ((∫ X, Real.cos (inner ℝ (centeredStat (sed_Q d s (n + 1) β ρ) φ X) t)
          ∂(sed_Q d s (n + 1) β ρ) : ℝ) : ℂ) +
        ((∫ X, Real.sin (inner ℝ (centeredStat (sed_Q d s (n + 1) β ρ) φ X) t)
          ∂(sed_Q d s (n + 1) β ρ) : ℝ) : ℂ) * Complex.I := by
      intro n
      have := hQ n
      have h0 : (μ n : Measure (EuclideanSpace ℝ (Fin p))) =
          (sed_Q d s (n + 1) β ρ).map (centeredStat (sed_Q d s (n + 1) β ρ) φ) := rfl
      have : IsProbabilityMeasure (μ n : Measure (EuclideanSpace ℝ (Fin p))) := (μ n).prop
      rw [b10b_charFun, h0]
      have hc : Continuous (fun x : EuclideanSpace ℝ (Fin p) => inner ℝ x t) := by fun_prop
      rw [integral_map (f := fun x : EuclideanSpace ℝ (Fin p) => Real.cos (inner ℝ x t))
          (hWm n).aemeasurable (Real.continuous_cos.comp hc).aestronglyMeasurable,
        integral_map (f := fun x : EuclideanSpace ℝ (Fin p) => Real.sin (inner ℝ x t))
          (hWm n).aemeasurable (Real.continuous_sin.comp hc).aestronglyMeasurable]
    have hmu0 : charFun (μ0 : Measure (EuclideanSpace ℝ (Fin p))) t =
        ((∫ x, Real.cos (inner ℝ x t) ∂G : ℝ) : ℂ) + ((∫ x, Real.sin (inner ℝ x t) ∂G : ℝ) : ℂ) *
          Complex.I := b10b_charFun G t
    simp_rw [hmu]
    rw [hmu0]
    have hinner : ∀ x : EuclideanSpace ℝ (Fin p), inner ℝ x t = innerSL ℝ t x := fun x => by
      rw [innerSL_apply_apply]; exact real_inner_comm t x
    have hcos : MemCb 5 (fun x : EuclideanSpace ℝ (Fin p) => Real.cos (inner ℝ x t)) := by
      have := b10b_memCb (p := p) 5 (g := Real.cos) (Or.inl rfl) (innerSL ℝ t)
      simpa only [hinner] using this
    have hsin : MemCb 5 (fun x : EuclideanSpace ℝ (Fin p) => Real.sin (inner ℝ x t)) := by
      have := b10b_memCb (p := p) 5 (g := Real.sin) (Or.inr (Or.inr (Or.inl rfl))) (innerSL ℝ t)
      simpa only [hinner] using this
    have ha := b10b_conv hd hs0 hs hβ hρ hφ hcos
    have hb := b10b_conv hd hs0 hs hβ hρ hφ hsin
    exact ((Complex.continuous_ofReal.tendsto _).comp ha).add
      (((Complex.continuous_ofReal.tendsto _).comp hb).mul_const _)
  obtain ⟨M, hM⟩ := hΨb
  let g : BoundedContinuousFunction (EuclideanSpace ℝ (Fin p)) ℝ :=
    BoundedContinuousFunction.ofNormedAddCommGroup Ψ hΨc M (fun x => by
      rw [Real.norm_eq_abs]; exact hM x)
  have hl := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hlim g
  have e : ∀ n : ℕ, ∫ ω, g ω ∂(μ n : Measure (EuclideanSpace ℝ (Fin p))) =
      ∫ X, Ψ (centeredStat (sed_Q d s (n + 1) β ρ) φ X) ∂(sed_Q d s (n + 1) β ρ) := fun n =>
    integral_map (hWm n).aemeasurable hΨc.aestronglyMeasurable
  exact Tendsto.congr e hl

end Main


end HRS.MC.SEdge.B10b
