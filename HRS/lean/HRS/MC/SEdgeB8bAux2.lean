import HRS.MC.SEdgeB8bAux1

/-!
# Packet B8b, helper file 2: the Hilbert-Schmidt bilinear form `∬ h f g` on `L²(μ)`
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.SEdge.B8b

open HRS.Q08 HRS.ResponseAux InnerProductSpace

section HS

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  {k : X → X → ℝ}

/-- the bilinear form `(f, g) ↦ ∬ k(x,y) f(x) g(y) dμ dμ` (product integral) -/
def b8b_Hf (μ : Measure X) (k : X → X → ℝ) (f g : X → ℝ) : ℝ :=
  ∫ z, k z.1 z.2 * f z.1 * g z.2 ∂(μ.prod μ)

theorem b8b_Hf_int (hk : MemLp (fun z : X × X => k z.1 z.2) 2 (μ.prod μ)) {f g : X → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun z : X × X => k z.1 z.2 * f z.1 * g z.2) (μ.prod μ) := by
  have := hk.integrable_mul (q08s_memLp_tensor hf hg)
  refine this.congr (Eventually.of_forall fun z => ?_)
  simp only [Pi.mul_apply]
  ring

theorem b8b_Hf_congr {f f' g g' : X → ℝ} (hf : f =ᵐ[μ] f') (hg : g =ᵐ[μ] g') :
    b8b_Hf μ k f g = b8b_Hf μ k f' g' := by
  unfold b8b_Hf
  refine integral_congr_ae ?_
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := μ)).ae_eq_comp hf
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := μ)).ae_eq_comp hg
  filter_upwards [h1, h2] with z a b
  simp only [Function.comp] at a b
  rw [a, b]

theorem b8b_Hf_sub_left (hk : MemLp (fun z : X × X => k z.1 z.2) 2 (μ.prod μ)) {f f' g : X → ℝ}
    (hf : MemLp f 2 μ) (hf' : MemLp f' 2 μ) (hg : MemLp g 2 μ) :
    b8b_Hf μ k (f - f') g = b8b_Hf μ k f g - b8b_Hf μ k f' g := by
  unfold b8b_Hf
  rw [← integral_sub (b8b_Hf_int hk hf hg) (b8b_Hf_int hk hf' hg)]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [Pi.sub_apply]
  ring

theorem b8b_Hf_sub_right (hk : MemLp (fun z : X × X => k z.1 z.2) 2 (μ.prod μ)) {f g g' : X → ℝ}
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (hg' : MemLp g' 2 μ) :
    b8b_Hf μ k f (g - g') = b8b_Hf μ k f g - b8b_Hf μ k f g' := by
  unfold b8b_Hf
  rw [← integral_sub (b8b_Hf_int hk hf hg) (b8b_Hf_int hk hf hg')]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [Pi.sub_apply]
  ring

theorem b8b_Hf_bound (hk : MemLp (fun z : X × X => k z.1 z.2) 2 (μ.prod μ)) (f g : Lp ℝ 2 μ) :
    |b8b_Hf μ k f g| ≤ ‖hk.toLp _‖ * ‖f‖ * ‖g‖ := by
  have hT : MemLp (fun z : X × X => f z.1 * g z.2) 2 (μ.prod μ) :=
    q08s_memLp_tensor (Lp.memLp f) (Lp.memLp g)
  have h1 : b8b_Hf μ k f g = inner ℝ (hk.toLp _) (hT.toLp _) := by
    rw [q08s_inner_toLp (μ.prod μ) hk hT]
    unfold b8b_Hf
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only
    ring
  have h2 : ‖hT.toLp (fun z : X × X => f z.1 * g z.2)‖ = ‖f‖ * ‖g‖ := by
    have h3 : ‖hT.toLp (fun z : X × X => f z.1 * g z.2)‖ ^ 2 = (‖f‖ * ‖g‖) ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, q08s_inner_toLp (μ.prod μ) hT hT, mul_pow,
        ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, b8b_inner_eq, b8b_inner_eq]
      have : ∀ z : X × X, f z.1 * g z.2 * (f z.1 * g z.2) = (f z.1 * f z.1) * (g z.2 * g z.2) := by
        intro z; ring
      simp_rw [this]
      exact integral_prod_mul (fun x => f x * f x) (fun y => g y * g y)
    exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 h3
  rw [h1]
  refine (abs_real_inner_le_norm _ _).trans ?_
  rw [h2]
  ring_nf
  exact le_rfl

theorem b8b_Hf_tendsto (hk : MemLp (fun z : X × X => k z.1 z.2) 2 (μ.prod μ))
    {F G : ℕ → Lp ℝ 2 μ} {f g : Lp ℝ 2 μ} (hF : Tendsto F atTop (𝓝 f))
    (hG : Tendsto G atTop (𝓝 g)) :
    Tendsto (fun L => b8b_Hf μ k (F L) (G L)) atTop (𝓝 (b8b_Hf μ k f g)) := by
  set N := ‖hk.toLp _‖ with hN
  have hd : ∀ L, b8b_Hf μ k (F L) (G L) - b8b_Hf μ k f g =
      b8b_Hf μ k ((F L - f : Lp ℝ 2 μ)) (G L) + b8b_Hf μ k f ((G L - g : Lp ℝ 2 μ)) := by
    intro L
    have e1 : b8b_Hf μ k ((F L - f : Lp ℝ 2 μ)) (G L) = b8b_Hf μ k ((F L : X → ℝ) - f) (G L) :=
      b8b_Hf_congr (Lp.coeFn_sub _ _) (Filter.EventuallyEq.refl _ _)
    have e2 : b8b_Hf μ k f ((G L - g : Lp ℝ 2 μ)) = b8b_Hf μ k f ((G L : X → ℝ) - g) :=
      b8b_Hf_congr (Filter.EventuallyEq.refl _ _) (Lp.coeFn_sub _ _)
    rw [e1, e2, b8b_Hf_sub_left hk (Lp.memLp _) (Lp.memLp _) (Lp.memLp _),
      b8b_Hf_sub_right hk (Lp.memLp _) (Lp.memLp _) (Lp.memLp _)]
    ring
  have ha : Tendsto (fun L => ‖F L - f‖) atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero] at hF; exact hF
  have hb : Tendsto (fun L => ‖G L - g‖) atTop (𝓝 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero] at hG; exact hG
  have hbd : ∀ L, |b8b_Hf μ k (F L) (G L) - b8b_Hf μ k f g| ≤
      N * (‖F L - f‖ * (‖g‖ + ‖G L - g‖) + ‖f‖ * ‖G L - g‖) := by
    intro L
    rw [hd L]
    refine (abs_add_le _ _).trans ?_
    have h1 := b8b_Hf_bound hk (F L - f) (G L)
    have h2 := b8b_Hf_bound hk f (G L - g)
    have h3 : ‖G L‖ ≤ ‖g‖ + ‖G L - g‖ := by
      have := norm_le_norm_add_norm_sub' (G L) g
      linarith [norm_sub_rev (G L) g]
    have hN0 : 0 ≤ N := norm_nonneg _
    have h4 : N * ‖F L - f‖ * ‖G L‖ ≤ N * ‖F L - f‖ * (‖g‖ + ‖G L - g‖) :=
      mul_le_mul_of_nonneg_left h3 (mul_nonneg hN0 (norm_nonneg _))
    nlinarith
  have hlim : Tendsto (fun L => N * (‖F L - f‖ * (‖g‖ + ‖G L - g‖) + ‖f‖ * ‖G L - g‖)) atTop
      (𝓝 0) := by
    have := ((ha.mul ((tendsto_const_nhds (x := ‖g‖)).add hb)).add
      ((tendsto_const_nhds (x := ‖f‖)).mul hb)).const_mul N
    simpa using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun L => norm_nonneg _) (fun L => ?_) hlim
  rw [Real.norm_eq_abs]
  exact hbd L

end HS

end HRS.MC.SEdge.B8b
