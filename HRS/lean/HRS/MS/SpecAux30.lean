import HRS.MS.MovLinAux9

/-!
# S8P: symmetric generator on an invariant core implies a symmetric semigroup (S8.7, gap b1, part ii)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  Abstract Hilbert-space lemma, no Hille-Yosida.

`T : ℝ → E →L E` a strongly continuous semigroup on `[0,∞)`, `D ⊂ E` dense and `T`-invariant, every `v ∈ D` has a right
derivative `-T t w` of `τ ↦ T τ v` at every `t ≥ 0` (`s8p_IsGen T v w`: `w = G v`), and `B` a bounded symmetric operator with
`⟨G v, B v'⟩ = ⟨B v, G v'⟩` on `D`.  Then `⟨T t x, B y⟩ = ⟨x, B (T t y)⟩`.

Proof: `f(σ) = ⟨T σ v, B T(t-σ) v'⟩` is continuous on `[0,t]` with right derivative `0` (the symmetry of the generator at
`T σ v ∈ D`, `T(t-σ) v' ∈ D`), hence constant; then density.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped RealInnerProductSpace

namespace HRS.MS.Spec

open HRS.MS.MovLin

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- `w` is the generator applied to `v`: the right derivative of `τ ↦ T τ v` at every `t ≥ 0` is `-T t w`. -/
def s8p_IsGen (T : ℝ → E →L[ℝ] E) (v w : E) : Prop :=
  ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt (fun τ => T τ v) (-(T t w)) (Set.Ici t) t

theorem s8p_isGen_shift {T : ℝ → E →L[ℝ] E} (hadd : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → T (a + b) = T a * T b)
    {v w : E} (hg : s8p_IsGen T v w) {τ : ℝ} (hτ : 0 ≤ τ) : s8p_IsGen T (T τ v) (T τ w) := by
  intro u hu
  have h1 := hg (u + τ) (by linarith)
  have hh : HasDerivWithinAt (fun r : ℝ => r + τ) 1 (Set.Ici u) u :=
    ((hasDerivAt_id u).add_const τ).hasDerivWithinAt
  have h2 := h1.scomp u hh (fun r hr => by
    have : u ≤ r := hr
    show u + τ ≤ r + τ
    linarith)
  have e2 : (1 : ℝ) • (-(T (u + τ) w)) = -(T u (T τ w)) := by
    rw [one_smul, hadd u τ hu hτ]; rfl
  rw [e2] at h2
  refine h2.congr (fun r hr => ?_) ?_
  · have hr0 : 0 ≤ r := hu.trans hr
    simp only [Function.comp]
    rw [hadd r τ hr0 hτ]; rfl
  · simp only [Function.comp]
    rw [hadd u τ hu hτ]; rfl

theorem s8p_isGen_slope {T : ℝ → E →L[ℝ] E} (h0 : T 0 = 1) {v w : E} (hg : s8p_IsGen T v w) :
    Tendsto (fun h : ℝ => h⁻¹ • (T h v - v)) (𝓝[>] 0) (𝓝 (-w)) := by
  have := mov2d_slope_of_hasDerivWithinAt_Ici (hg 0 le_rfl)
  simp only [zero_add, h0, ContinuousLinearMap.one_apply] at this
  exact this

theorem s8p_isGen_unique {T : ℝ → E →L[ℝ] E} (h0 : T 0 = 1) {v w w' : E} (hw : s8p_IsGen T v w)
    (hw' : s8p_IsGen T v w') : w = w' := by
  have := (uniqueDiffWithinAt_Ici (0 : ℝ)).eq_deriv _ (hw 0 le_rfl) (hw' 0 le_rfl)
  simp only [h0, ContinuousLinearMap.one_apply] at this
  exact neg_injective this

/-- Right derivative zero of `σ ↦ ⟨T σ v, B T(t-σ) v'⟩`. -/
theorem s8p_symm_deriv (T : ℝ → E →L[ℝ] E) (B : E →L[ℝ] E)
    (hT0 : T 0 = 1) (hadd : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → T (a + b) = T a * T b)
    (hTc : ∀ x, ContinuousOn (fun t => T t x) (Set.Ici 0))
    (hB : ∀ x y : E, ⟪B x, y⟫ = ⟪x, B y⟫) (t : ℝ) (v v' : E) (σ : ℝ) (hσ : σ ∈ Set.Ico (0 : ℝ) t)
    (w_a w' : E) (ha : s8p_IsGen T (T σ v) w_a) (hw' : s8p_IsGen T v' w')
    (hsym : ⟪w_a, B (T (t - σ) v')⟫ = ⟪B (T σ v), T (t - σ) w'⟫) :
    HasDerivWithinAt (fun σ => ⟪T σ v, B (T (t - σ) v')⟫) 0 (Set.Ici σ) σ := by
  obtain ⟨M, hM⟩ := mov2d_unif_bound T hTc t
  set τ : ℝ := t - σ with hτ
  have hτpos : 0 < τ := by have := hσ.2; linarith
  set a : E := T σ v with ha_def
  apply mov2d_hasDerivWithinAt_Ici
  -- the two limits
  have hpos : ∀ᶠ h in 𝓝[>] (0 : ℝ), 0 < h ∧ h < τ := by
    filter_upwards [self_mem_nhdsWithin, Ioo_mem_nhdsGT hτpos] with h h1 h2
    exact ⟨h1, h2.2⟩
  have q1 : Tendsto (fun h : ℝ => h⁻¹ • (T h a - a)) (𝓝[>] 0) (𝓝 (-w_a)) := s8p_isGen_slope hT0 ha
  have hcont_c : Tendsto (fun h : ℝ => T (τ - h) v') (𝓝[>] 0) (𝓝 (T τ v')) := by
    have hc : ContinuousAt (fun r : ℝ => T r v') τ :=
      (hTc v').continuousAt (Ici_mem_nhds hτpos)
    have h3 : Tendsto (fun h : ℝ => τ - h) (𝓝[>] 0) (𝓝 τ) := by
      have : Tendsto (fun h : ℝ => τ - h) (𝓝 0) (𝓝 (τ - 0)) :=
        (continuous_const.sub continuous_id).tendsto 0
      rw [sub_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    exact hc.tendsto.comp h3
  have q2 : Tendsto (fun h : ℝ => T (τ - h) (h⁻¹ • (v' - T h v'))) (𝓝[>] 0) (𝓝 (T τ w')) := by
    set u : ℝ → E := fun h => h⁻¹ • (v' - T h v') with hu
    have hu_lim : Tendsto u (𝓝[>] 0) (𝓝 w') := by
      have := (s8p_isGen_slope hT0 hw').neg
      rw [neg_neg] at this
      refine this.congr' ?_
      filter_upwards with h
      simp only [hu]
      rw [← smul_neg, neg_sub]
    have hcw : Tendsto (fun h : ℝ => T (τ - h) w') (𝓝[>] 0) (𝓝 (T τ w')) := by
      have hc : ContinuousAt (fun r : ℝ => T r w') τ :=
        (hTc w').continuousAt (Ici_mem_nhds hτpos)
      have h3 : Tendsto (fun h : ℝ => τ - h) (𝓝[>] 0) (𝓝 τ) := by
        have : Tendsto (fun h : ℝ => τ - h) (𝓝 0) (𝓝 (τ - 0)) :=
          (continuous_const.sub continuous_id).tendsto 0
        rw [sub_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      exact hc.tendsto.comp h3
    have hdiff : Tendsto (fun h : ℝ => T (τ - h) (u h - w')) (𝓝[>] 0) (𝓝 0) := by
      have hB' : Tendsto (fun h : ℝ => |M| * ‖u h - w'‖) (𝓝[>] 0) (𝓝 0) := by
        have h0 : Tendsto (fun h : ℝ => u h - w') (𝓝[>] 0) (𝓝 0) := by simpa using hu_lim.sub_const w'
        have := (tendsto_zero_iff_norm_tendsto_zero.1 h0).const_mul |M|
        simpa using this
      refine squeeze_zero_norm' ?_ hB'
      filter_upwards [hpos] with h hh
      refine ((T (τ - h)).le_opNorm _).trans ?_
      exact mul_le_mul_of_nonneg_right ((hM _ ⟨by linarith [hh.2], by linarith [hh.1, hσ.1, hσ.2]⟩).trans (le_abs_self M))
        (norm_nonneg _)
    have := hdiff.add hcw
    rw [zero_add] at this
    refine this.congr' ?_
    filter_upwards with h
    rw [map_sub]; abel
  have qA : Tendsto (fun h : ℝ => ⟪h⁻¹ • (T h a - a), B (T (τ - h) v')⟫) (𝓝[>] 0)
      (𝓝 ⟪-w_a, B (T τ v')⟫) := q1.inner (B.continuous.tendsto _ |>.comp hcont_c)
  have qB : Tendsto (fun h : ℝ => ⟪a, B (T (τ - h) (h⁻¹ • (v' - T h v')))⟫) (𝓝[>] 0)
      (𝓝 ⟪a, B (T τ w')⟫) := tendsto_const_nhds.inner (B.continuous.tendsto _ |>.comp q2)
  have hlim := qA.add qB
  have hz : ⟪-w_a, B (T τ v')⟫ + ⟪a, B (T τ w')⟫ = 0 := by
    rw [inner_neg_left, ← hB a (T τ w')]
    have : ⟪w_a, B (T τ v')⟫ = ⟪B a, T τ w'⟫ := hsym
    rw [this]; ring
  rw [hz] at hlim
  refine hlim.congr' ?_
  filter_upwards [hpos] with h hh
  have hh0 : 0 ≤ h := hh.1.le
  have hτh : 0 ≤ τ - h := by linarith [hh.2]
  have e1 : T (σ + h) v = T h a := by
    rw [add_comm, hadd h σ hh0 hσ.1]; rfl
  have e2 : t - (σ + h) = τ - h := by rw [hτ]; ring
  have e3 : T τ v' = T h (T (τ - h) v') := by
    have := hadd h (τ - h) hh0 hτh
    rw [show h + (τ - h) = τ by ring] at this
    rw [this]; rfl
  have e4 : T h (T (τ - h) v') = T (τ - h) (T h v') := by
    have h1 := hadd h (τ - h) hh0 hτh
    have h2 := hadd (τ - h) h hτh hh0
    rw [show (τ - h) + h = h + (τ - h) by ring] at h2
    have : T h * T (τ - h) = T (τ - h) * T h := h1.symm.trans h2
    exact congrArg (fun A : E →L[ℝ] E => A v') this
  show _ = h⁻¹ • (⟪T (σ + h) v, B (T (t - (σ + h)) v')⟫ - ⟪T σ v, B (T (t - σ) v')⟫)
  rw [e1, e2, show t - σ = τ from hτ.symm, e3]
  rw [map_smul, map_sub, ← e4]
  simp only [real_inner_smul_left, real_inner_smul_right, inner_sub_left, inner_sub_right, map_sub, map_smul,
    smul_eq_mul]
  ring

/-- Symmetry of the semigroup on the invariant core. -/
theorem s8p_symm_core (T : ℝ → E →L[ℝ] E) (B : E →L[ℝ] E)
    (hT0 : T 0 = 1) (hadd : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → T (a + b) = T a * T b)
    (hTc : ∀ x, ContinuousOn (fun t => T t x) (Set.Ici 0))
    (hB : ∀ x y : E, ⟪B x, y⟫ = ⟪x, B y⟫) (D : Set E)
    (hinv : ∀ σ : ℝ, 0 ≤ σ → ∀ v ∈ D, T σ v ∈ D)
    (hgen : ∀ v ∈ D, ∃ w, s8p_IsGen T v w)
    (hsym : ∀ v ∈ D, ∀ v' ∈ D, ∀ w w' : E, s8p_IsGen T v w → s8p_IsGen T v' w' → ⟪w, B v'⟫ = ⟪B v, w'⟫)
    {v v' : E} (hv : v ∈ D) (hv' : v' ∈ D) {t : ℝ} (ht : 0 ≤ t) :
    ⟪T t v, B v'⟫ = ⟪v, B (T t v')⟫ := by
  have hcont : ContinuousOn (fun σ => ⟪T σ v, B (T (t - σ) v')⟫) (Set.Icc 0 t) := by
    have g1 : ContinuousOn (fun σ => T σ v) (Set.Icc 0 t) := (hTc v).mono (fun σ hσ => hσ.1)
    have g2 : ContinuousOn (fun σ => T (t - σ) v') (Set.Icc 0 t) :=
      (hTc v').comp (continuousOn_const.sub continuousOn_id) (fun σ hσ => by
        show 0 ≤ t - σ
        linarith [hσ.2])
    exact g1.inner (B.continuous.comp_continuousOn g2)
  have hder : ∀ σ ∈ Set.Ico (0 : ℝ) t,
      HasDerivWithinAt (fun σ => ⟪T σ v, B (T (t - σ) v')⟫) 0 (Set.Ici σ) σ := by
    intro σ hσ
    have haD := hinv σ hσ.1 v hv
    obtain ⟨w_a, hw_a⟩ := hgen _ haD
    obtain ⟨w', hw'⟩ := hgen v' hv'
    have hbD := hinv (t - σ) (by linarith [hσ.2]) v' hv'
    have hb := s8p_isGen_shift hadd hw' (show 0 ≤ t - σ by linarith [hσ.2])
    exact s8p_symm_deriv T B hT0 hadd hTc hB t v v' σ hσ w_a w' hw_a hw'
      (hsym _ haD _ hbD _ _ hw_a hb)
  have := constant_of_has_deriv_right_zero hcont hder t ⟨ht, le_rfl⟩
  simpa [hT0] using this

/-- **A symmetric generator gives a symmetric semigroup.** -/
theorem s8p_semigroup_symm (T : ℝ → E →L[ℝ] E) (B : E →L[ℝ] E)
    (hT0 : T 0 = 1) (hadd : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → T (a + b) = T a * T b)
    (hTc : ∀ x, ContinuousOn (fun t => T t x) (Set.Ici 0))
    (hB : ∀ x y : E, ⟪B x, y⟫ = ⟪x, B y⟫) (D : Set E) (hD : Dense D)
    (hinv : ∀ σ : ℝ, 0 ≤ σ → ∀ v ∈ D, T σ v ∈ D)
    (hgen : ∀ v ∈ D, ∃ w, s8p_IsGen T v w)
    (hsym : ∀ v ∈ D, ∀ v' ∈ D, ∀ w w' : E, s8p_IsGen T v w → s8p_IsGen T v' w' → ⟪w, B v'⟫ = ⟪B v, w'⟫)
    (x y : E) {t : ℝ} (ht : 0 ≤ t) : ⟪T t x, B y⟫ = ⟪x, B (T t y)⟫ := by
  have hF : Continuous (fun p : E × E => ⟪T t p.1, B p.2⟫ - ⟪p.1, B (T t p.2)⟫) := by
    have h1 : Continuous fun p : E × E => T t p.1 := (T t).continuous.comp continuous_fst
    have h2 : Continuous fun p : E × E => B p.2 := B.continuous.comp continuous_snd
    have h3 : Continuous fun p : E × E => B (T t p.2) :=
      B.continuous.comp ((T t).continuous.comp continuous_snd)
    exact (h1.inner h2).sub (continuous_fst.inner h3)
  have key := Continuous.ext_on (hD.prod hD) hF continuous_const (f := fun p : E × E =>
      ⟪T t p.1, B p.2⟫ - ⟪p.1, B (T t p.2)⟫) (g := fun _ => (0 : ℝ)) (fun p hp => by
    have := s8p_symm_core T B hT0 hadd hTc hB D hinv hgen hsym hp.1 hp.2 ht
    simp [this])
  have := congrFun key (x, y)
  simpa [sub_eq_zero] using this

end Abstract

end HRS.MS.Spec
