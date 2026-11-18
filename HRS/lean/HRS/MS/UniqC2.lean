import HRS.MS.UniqC1c

/-!
# Packet C2, part 1: pointwise and joint continuity of a family with weak continuity and uniform Lipschitz bound

Let `g : ℝ → ℝ^d → ℝ` be a family, indexed by `r ∈ S`, of differentiable functions with
`‖D g r‖ ≤ b1` uniformly, such that `r ↦ ∫ ψ g r` is continuous on `S` for every continuous compactly
supported `ψ`.  Then `(r,x) ↦ g r x` is continuous on `S × ℝ^d`.  (Pointwise values are recovered from
the weak ones by testing against an approximate identity, `ContDiffBump.normed`.)
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.UniqC2
open HRS HRS.Whole HRS.MP.RdGen

variable {d : ℕ}

/-- Lipschitz bound from a bound on the derivative. -/
lemma c2_lip {f : Euc d → ℝ} (hf : Differentiable ℝ f) {b : ℝ} (hb : ∀ y, ‖fderiv ℝ f y‖ ≤ b)
    (x y : Euc d) : |f x - f y| ≤ b * ‖x - y‖ := by
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := f) (C := b) (s := Set.univ)
    (x := y) (y := x) (fun z _ => hf z) (fun z _ => hb z) convex_univ (Set.mem_univ _)
    (Set.mem_univ _)
  simpa [Real.norm_eq_abs, norm_sub_rev] using this

/-- Approximate identity: for a continuous differentiable `f` with `‖Df‖ ≤ b` and `δ > 0` there is a
continuous compactly supported test function `ψ` with `|f y - ∫ ψ f| ≤ b δ`. -/
lemma c2_approx {f : Euc d → ℝ} (hf : Differentiable ℝ f) {b : ℝ} (hb : ∀ y, ‖fderiv ℝ f y‖ ≤ b)
    (hb0 : 0 ≤ b) (y : Euc d) {δ : ℝ} (hδ : 0 < δ) (ψ : Euc d → ℝ) (hψc : Continuous ψ)
    (hψk : HasCompactSupport ψ) (hψn : ∀ w, 0 ≤ ψ w) (hψ1 : ∫ w, ψ w = 1)
    (hψs : ∀ w, ψ w ≠ 0 → ‖w - y‖ < δ) :
    |f y - ∫ w, ψ w * f w| ≤ b * δ := by
  have hint : Integrable ψ := hψc.integrable_of_hasCompactSupport hψk
  have hint2 : Integrable (fun w => ψ w * f w) :=
    (hψc.mul hf.continuous).integrable_of_hasCompactSupport hψk.mul_right
  have e : f y - ∫ w, ψ w * f w = -∫ w, ψ w * (f w - f y) := by
    have : ∫ w, ψ w * (f w - f y) = (∫ w, ψ w * f w) - f y := by
      simp_rw [mul_sub]
      rw [integral_sub hint2 (hint.mul_const _), integral_mul_const, hψ1, one_mul]
    rw [this]; ring
  rw [e, abs_neg]
  have hb' : (∀ w, ‖ψ w * (f w - f y)‖ ≤ ψ w * (b * δ)) := by
    intro w
    by_cases h : ψ w = 0
    · simp [h]
    · rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hψn w)]
      refine mul_le_mul_of_nonneg_left ?_ (hψn w)
      have := c2_lip hf hb w y
      have h2 := hψs w h
      calc ‖f w - f y‖ = |f w - f y| := Real.norm_eq_abs _
        _ ≤ b * ‖w - y‖ := this
        _ ≤ b * δ := mul_le_mul_of_nonneg_left h2.le hb0
  have := norm_integral_le_of_norm_le (hint.mul_const (b * δ)) (Eventually.of_forall hb')
  rw [integral_mul_const, hψ1, one_mul] at this
  simpa [Real.norm_eq_abs] using this

/-- Existence of the approximate identity (`ContDiffBump`). -/
lemma c2_bump (y : Euc d) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ψ : Euc d → ℝ, Continuous ψ ∧ HasCompactSupport ψ ∧ (∀ w, 0 ≤ ψ w) ∧ ∫ w, ψ w = 1 ∧
      ∀ w, ψ w ≠ 0 → ‖w - y‖ < δ := by
  let f : ContDiffBump y := ⟨δ / 2, δ, by positivity, by linarith⟩
  refine ⟨f.normed volume, f.continuous_normed, f.hasCompactSupport_normed, f.nonneg_normed,
    f.integral_normed, fun w hw => ?_⟩
  have : w ∈ Function.support (f.normed volume) := hw
  rw [f.support_normed_eq] at this
  simpa [dist_eq_norm] using this

/-- **Pointwise continuity from weak continuity and a uniform Lipschitz bound.** -/
lemma c2_pointwise {S : Set ℝ} {g : ℝ → Euc d → ℝ} {b1 : ℝ} (hb1 : 0 ≤ b1)
    (hweak : ∀ ψ : Euc d → ℝ, Continuous ψ → HasCompactSupport ψ →
      ContinuousOn (fun r => ∫ x, ψ x * g r x) S)
    (hdiff : ∀ r ∈ S, Differentiable ℝ (g r)) (hlip : ∀ r ∈ S, ∀ y, ‖fderiv ℝ (g r) y‖ ≤ b1)
    (y : Euc d) : ContinuousOn (fun r => g r y) S := by
  rw [Metric.continuousOn_iff]
  intro r₀ hr₀ ε hε
  set δ : ℝ := ε / (3 * (b1 + 1)) with hδdef
  have hδ : 0 < δ := by positivity
  have hbδ : b1 * δ < ε / 3 := by
    have : b1 * δ = ε / 3 * (b1 / (b1 + 1)) := by rw [hδdef]; field_simp
    rw [this]
    have h1 : b1 / (b1 + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
    have : 0 < ε / 3 := by positivity
    nlinarith
  obtain ⟨ψ, hψc, hψk, hψn, hψ1, hψs⟩ := c2_bump y hδ
  obtain ⟨η, hη, hηr⟩ := Metric.continuousOn_iff.1 (hweak ψ hψc hψk) r₀ hr₀ (ε / 3) (by positivity)
  refine ⟨η, hη, fun r hr hrd => ?_⟩
  have h1 := c2_approx (hdiff r hr) (hlip r hr) hb1 y hδ ψ hψc hψk hψn hψ1 hψs
  have h2 := c2_approx (hdiff r₀ hr₀) (hlip r₀ hr₀) hb1 y hδ ψ hψc hψk hψn hψ1 hψs
  have h3 := hηr r hr hrd
  rw [Real.dist_eq] at h3 ⊢
  have e : g r y - g r₀ y = (g r y - ∫ w, ψ w * g r w) - (g r₀ y - ∫ w, ψ w * g r₀ w) +
      ((∫ w, ψ w * g r w) - ∫ w, ψ w * g r₀ w) := by ring
  rw [e]
  calc _ ≤ |(g r y - ∫ w, ψ w * g r w) - (g r₀ y - ∫ w, ψ w * g r₀ w)| +
        |(∫ w, ψ w * g r w) - ∫ w, ψ w * g r₀ w| := abs_add_le _ _
    _ ≤ (|g r y - ∫ w, ψ w * g r w| + |g r₀ y - ∫ w, ψ w * g r₀ w|) +
        |(∫ w, ψ w * g r w) - ∫ w, ψ w * g r₀ w| := by
          gcongr; exact abs_sub _ _
    _ < ε := by linarith

/-- **Joint continuity** of `(r,x) ↦ g r x` on `S × ℝ^d`. -/
lemma c2_joint {S : Set ℝ} {g : ℝ → Euc d → ℝ} {b1 : ℝ} (hb1 : 0 ≤ b1)
    (hweak : ∀ ψ : Euc d → ℝ, Continuous ψ → HasCompactSupport ψ →
      ContinuousOn (fun r => ∫ x, ψ x * g r x) S)
    (hdiff : ∀ r ∈ S, Differentiable ℝ (g r)) (hlip : ∀ r ∈ S, ∀ y, ‖fderiv ℝ (g r) y‖ ≤ b1) :
    ContinuousOn (fun p : ℝ × Euc d => g p.1 p.2) (S ×ˢ Set.univ) := by
  intro p₀ hp₀
  obtain ⟨r₀, x₀⟩ := p₀
  have hr₀ : r₀ ∈ S := hp₀.1
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨η, hη, hηr⟩ := Metric.continuousOn_iff.1
    (c2_pointwise hb1 hweak hdiff hlip x₀) r₀ hr₀ (ε / 2) (by positivity)
  set δ : ℝ := min η (ε / (2 * (b1 + 1))) with hδdef
  have hδ : 0 < δ := lt_min hη (by positivity)
  refine ⟨δ, hδ, fun ⟨r, x⟩ hp hd => ?_⟩
  have hr : r ∈ S := hp.1
  rw [Prod.dist_eq] at hd
  simp only at hd
  have hd1 : dist r r₀ < η := lt_of_lt_of_le (lt_of_le_of_lt (le_max_left _ _) hd) (min_le_left _ _)
  have hd2 : dist x x₀ < ε / (2 * (b1 + 1)) :=
    lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hd) (min_le_right _ _)
  have h1 := hηr r hr hd1
  have h2 := c2_lip (hdiff r hr) (hlip r hr) x x₀
  have h3 : b1 * ‖x - x₀‖ < ε / 2 := by
    rw [← dist_eq_norm]
    have : b1 * dist x x₀ ≤ (b1 + 1) * dist x x₀ := by
      nlinarith [dist_nonneg (x := x) (y := x₀)]
    have h4 : (b1 + 1) * dist x x₀ < ε / 2 := by
      calc (b1 + 1) * dist x x₀ < (b1 + 1) * (ε / (2 * (b1 + 1))) :=
            mul_lt_mul_of_pos_left hd2 (by linarith)
        _ = ε / 2 := by field_simp
    linarith
  rw [Real.dist_eq] at h1 ⊢
  have e : g r x - g r₀ x₀ = (g r x - g r x₀) + (g r x₀ - g r₀ x₀) := by ring
  rw [e]
  calc _ ≤ |g r x - g r x₀| + |g r x₀ - g r₀ x₀| := abs_add_le _ _
    _ < ε := by linarith

end HRS.MS.UniqC2
