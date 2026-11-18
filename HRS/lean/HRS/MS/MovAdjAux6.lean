import HRS.MS.MovAdjAux5

/-!
# S6.7 (packet P2, part 1): `L²`-valued calculus for families `τ ↦ a_τ √ρ`

Namespace `HRS.MS.MovAdj`, helpers `s67_`.  Infrastructure for the supplement row `S:W:lem:r2mov-global-adjoint`; not a manuscript row.

* `s67_inner_toLp`: `⟨F, G⟩_{L²} = ∫ F G` for the `Lp` representatives.
* `s67_hasDeriv_toLp`: if the pointwise difference quotients of a family `a_τ` are dominated by an `L²` function `G` and
  converge to `a'`, then `τ ↦ toLp (a_τ)` has right derivative `toLp a'` (dominated convergence for the squared norm).
* `s67_cont_toLp`: continuity of `τ ↦ toLp (a_τ)` from pointwise continuity and an `L²` domination.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovAdj

open HRS HRS.Whole

variable {d : ℕ}

theorem s67_inner_toLp {F G : Euc d → ℝ} (hF : MemLp F 2 (volume : Measure (Euc d)))
    (hG : MemLp G 2 (volume : Measure (Euc d))) :
    inner ℝ (hF.toLp F) (hG.toLp G) = ∫ x, F x * G x := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hF.coeFn_toLp, hG.coeFn_toLp] with x h1 h2
  rw [h1, h2]
  simp [mul_comm]

theorem s67_inner_toLp_left {F : Euc d → ℝ} (hF : MemLp F 2 (volume : Measure (Euc d)))
    (v : Lp ℝ 2 (volume : Measure (Euc d))) :
    inner ℝ (hF.toLp F) v = ∫ x, F x * v x := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hF.coeFn_toLp] with x h1
  rw [h1]
  simp [mul_comm]

theorem s67_hasDeriv_toLp {a : ℝ → Euc d → ℝ} {a' G : Euc d → ℝ} {σ δ : ℝ} (hδ : 0 < δ)
    (hmem : ∀ τ, MemLp (a τ) 2 (volume : Measure (Euc d))) (hG : MemLp G 2 (volume : Measure (Euc d)))
    (ha' : MemLp a' 2 (volume : Measure (Euc d)))
    (hdom : ∀ τ ∈ Set.Ioo σ (σ + δ), ∀ x, |a τ x - a σ x| ≤ (τ - σ) * G x)
    (hpt : ∀ x, Tendsto (fun τ => (τ - σ)⁻¹ * (a τ x - a σ x)) (𝓝[>] σ) (𝓝 (a' x)))
    (hbound : ∀ x, |a' x| ≤ G x) :
    HasDerivWithinAt (fun τ => (hmem τ).toLp (a τ)) (ha'.toLp a') (Set.Ici σ) σ := by
  rw [← hasDerivWithinAt_Ioi_iff_Ici, hasDerivWithinAt_iff_tendsto_slope]
  have hs : (Set.Ioi σ \ {σ}) = Set.Ioi σ := Set.diff_singleton_eq_self (by simp)
  rw [hs, tendsto_iff_norm_sub_tendsto_zero]
  set Dτ : ℝ → Euc d → ℝ := fun τ x => (τ - σ)⁻¹ * (a τ x - a σ x) - a' x with hD
  have hE : ∀ τ : ℝ, ‖slope (fun τ => (hmem τ).toLp (a τ)) σ τ - ha'.toLp a'‖ ^ 2 =
      ∫ x, Dτ τ x * Dτ τ x := by
    intro τ
    rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    have h1 : ∀ᵐ x ∂(volume : Measure (Euc d)),
        (slope (fun τ => (hmem τ).toLp (a τ)) σ τ - ha'.toLp a') x = Dτ τ x := by
      rw [slope_def_module]
      filter_upwards [Lp.coeFn_sub ((τ - σ)⁻¹ • ((hmem τ).toLp (a τ) - (hmem σ).toLp (a σ))) (ha'.toLp a'),
        Lp.coeFn_smul (τ - σ)⁻¹ ((hmem τ).toLp (a τ) - (hmem σ).toLp (a σ)),
        Lp.coeFn_sub ((hmem τ).toLp (a τ)) ((hmem σ).toLp (a σ)),
        (hmem τ).coeFn_toLp, (hmem σ).coeFn_toLp, ha'.coeFn_toLp] with x e1 e2 e3 e4 e5 e6
      rw [e1, Pi.sub_apply, e2, Pi.smul_apply, e3, Pi.sub_apply, e4, e5, e6]
      simp [hD]
    filter_upwards [h1] with x hx
    rw [hx]
    simp [sq]
  have key : Tendsto (fun τ : ℝ => ‖slope (fun τ => (hmem τ).toLp (a τ)) σ τ - ha'.toLp a'‖ ^ 2)
      (𝓝[>] σ) (𝓝 0) := by
    simp_rw [hE]
    have hlim := tendsto_integral_filter_of_dominated_convergence (μ := (volume : Measure (Euc d)))
      (l := 𝓝[>] σ) (F := fun τ x => Dτ τ x * Dτ τ x) (f := fun _ => (0 : ℝ))
      (fun x => 4 * (G x * G x)) ?_ ?_ ?_ ?_
    · simpa using hlim
    · refine Filter.Eventually.of_forall fun τ => ?_
      have : AEStronglyMeasurable (Dτ τ) volume :=
        ((((hmem τ).aestronglyMeasurable.sub (hmem σ).aestronglyMeasurable).const_mul ((τ - σ)⁻¹)).sub
          ha'.aestronglyMeasurable)
      exact this.mul this
    · filter_upwards [Ioo_mem_nhdsGT (show σ < σ + δ by linarith)] with τ hτ
      refine Filter.Eventually.of_forall fun x => ?_
      have hτ' : 0 < τ - σ := sub_pos.2 hτ.1
      have h1 : |(τ - σ)⁻¹ * (a τ x - a σ x)| ≤ G x := by
        rw [abs_mul, abs_inv, abs_of_pos hτ']
        rw [inv_mul_le_iff₀ hτ']
        exact hdom τ hτ x
      have h2 : |Dτ τ x| ≤ 2 * G x := by
        calc |Dτ τ x| ≤ |(τ - σ)⁻¹ * (a τ x - a σ x)| + |a' x| := abs_sub _ _
          _ ≤ G x + G x := add_le_add h1 (hbound x)
          _ = 2 * G x := by ring
      rw [Real.norm_eq_abs, abs_mul]
      have h3 : |Dτ τ x| * |Dτ τ x| ≤ (2 * G x) * (2 * G x) :=
        mul_le_mul h2 h2 (abs_nonneg _) ((abs_nonneg _).trans h2)
      nlinarith
    · exact (hG.integrable_mul hG).const_mul 4
    · refine Filter.Eventually.of_forall fun x => ?_
      have h := (hpt x).sub_const (a' x)
      simp only [sub_self] at h
      have := h.mul h
      simpa using this
  have h2 := (Real.continuous_sqrt.tendsto 0).comp key
  simp only [Real.sqrt_zero, Function.comp_def] at h2
  refine h2.congr' (Filter.Eventually.of_forall fun τ => ?_)
  simp [Real.sqrt_sq (norm_nonneg _)]

theorem s67_cont_toLp {a : ℝ → Euc d → ℝ} {H : Euc d → ℝ} {S : Set ℝ} {σ : ℝ}
    (hmem : ∀ τ, MemLp (a τ) 2 (volume : Measure (Euc d))) (hH : MemLp H 2 (volume : Measure (Euc d)))
    (hb : ∀ τ ∈ S, ∀ x, |a τ x| ≤ H x) (hσ : σ ∈ S)
    (hpt : ∀ x, ContinuousWithinAt (fun τ => a τ x) S σ) :
    ContinuousWithinAt (fun τ => (hmem τ).toLp (a τ)) S σ := by
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  have hE : ∀ τ : ℝ, ‖(hmem τ).toLp (a τ) - (hmem σ).toLp (a σ)‖ ^ 2 =
      ∫ x, (a τ x - a σ x) * (a τ x - a σ x) := by
    intro τ
    rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub ((hmem τ).toLp (a τ)) ((hmem σ).toLp (a σ)),
      (hmem τ).coeFn_toLp, (hmem σ).coeFn_toLp] with x e1 e2 e3
    rw [e1, Pi.sub_apply, e2, e3]
    simp [sq]
  have key : Tendsto (fun τ : ℝ => ‖(hmem τ).toLp (a τ) - (hmem σ).toLp (a σ)‖ ^ 2) (𝓝[S] σ) (𝓝 0) := by
    simp_rw [hE]
    have hlim := tendsto_integral_filter_of_dominated_convergence (μ := (volume : Measure (Euc d)))
      (l := 𝓝[S] σ) (F := fun τ x => (a τ x - a σ x) * (a τ x - a σ x)) (f := fun _ => (0 : ℝ))
      (fun x => 4 * (H x * H x)) ?_ ?_ ?_ ?_
    · simpa using hlim
    · refine Filter.Eventually.of_forall fun τ => ?_
      have : AEStronglyMeasurable (fun x => a τ x - a σ x) volume :=
        (hmem τ).aestronglyMeasurable.sub (hmem σ).aestronglyMeasurable
      exact this.mul this
    · filter_upwards [self_mem_nhdsWithin] with τ hτ
      refine Filter.Eventually.of_forall fun x => ?_
      have h1 : |a τ x - a σ x| ≤ 2 * H x := by
        calc |a τ x - a σ x| ≤ |a τ x| + |a σ x| := abs_sub _ _
          _ ≤ H x + H x := add_le_add (hb τ hτ x) (hb σ hσ x)
          _ = 2 * H x := by ring
      rw [Real.norm_eq_abs, abs_mul]
      have h3 : |a τ x - a σ x| * |a τ x - a σ x| ≤ (2 * H x) * (2 * H x) :=
        mul_le_mul h1 h1 (abs_nonneg _) ((abs_nonneg _).trans h1)
      nlinarith
    · exact (hH.integrable_mul hH).const_mul 4
    · refine Filter.Eventually.of_forall fun x => ?_
      have h := ((hpt x).tendsto).sub_const (a σ x)
      simp only [sub_self] at h
      have := h.mul h
      simpa using this
  have h2 := (Real.continuous_sqrt.tendsto 0).comp key
  simp only [Real.sqrt_zero, Function.comp_def] at h2
  refine h2.congr' (Filter.Eventually.of_forall fun τ => ?_)
  simp [Real.sqrt_sq (norm_nonneg _)]

/-- **Product rule for the `L²` pairing.** -/
theorem s67_hasDeriv_pairing {a : ℝ → Euc d → ℝ} {a' G : Euc d → ℝ} {σ δ : ℝ} (hδ : 0 < δ)
    (hmem : ∀ τ, MemLp (a τ) 2 (volume : Measure (Euc d))) (hG : MemLp G 2 (volume : Measure (Euc d)))
    (ha' : MemLp a' 2 (volume : Measure (Euc d)))
    (hdom : ∀ τ ∈ Set.Ioo σ (σ + δ), ∀ x, |a τ x - a σ x| ≤ (τ - σ) * G x)
    (hpt : ∀ x, Tendsto (fun τ => (τ - σ)⁻¹ * (a τ x - a σ x)) (𝓝[>] σ) (𝓝 (a' x)))
    (hbound : ∀ x, |a' x| ≤ G x) {b : ℝ → Lp ℝ 2 (volume : Measure (Euc d))}
    {b' : Lp ℝ 2 (volume : Measure (Euc d))} (hb : HasDerivWithinAt b b' (Set.Ici σ) σ) :
    HasDerivWithinAt (fun τ => inner ℝ ((hmem τ).toLp (a τ)) (b τ))
      (inner ℝ ((hmem σ).toLp (a σ)) b' + inner ℝ (ha'.toLp a') (b σ)) (Set.Ici σ) σ :=
  (s67_hasDeriv_toLp hδ hmem hG ha' hdom hpt hbound).inner ℝ hb

end HRS.MS.MovAdj
