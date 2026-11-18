import HRS.Stochastic.QuadraticVariation

/-!
# Vector-valued Itô integrals, Itô processes, and Itô's formula

Package SI-01, part 5.

* `E` is a finite-dimensional real normed space (for the particle system `E = Fin N → Euc d`,
  the covering space of the configuration torus).  The `E`-valued (local) Itô integral of
  `Φ : ℝ → Ω → ι → E` is characterised through continuous linear functionals
  (`IsItoIntegralE`): `ℓ ∘ M` is the scalar local integral of `ℓ ∘ Φ` for every `ℓ : E →L[ℝ] ℝ`.
* An Itô process is `X_t = X₀ + ∫_0^t b_s ds + ∫_0^t Φ_s · dW_s` (`itoProcess`), with `b`
  progressive and pathwise locally integrable, `Φ` progressive and pathwise locally
  square-integrable.
* `C^{1,2}` regularity on `[0, T] × U` (`IsC12On`): `f` jointly continuous, `x ↦ f(t,x)` twice
  differentiable at every point of `U` with `D_x f`, `D_x² f` jointly continuous, and
  `t ↦ f(t,x)` differentiable on `[0, T]` (one-sided at the endpoints, `derivWithin … (Icc 0 T)`)
  with `∂_t f` jointly continuous.  This is exactly the regularity of the classical adjoint
  solutions of `Setup.lean` (`f ∈ C([0,t]; C_b²)`, `∂_r f ∈ C([0,t]; C_b⁰)`, M L1638, L1655) and
  of the backward heat functions `u(σ, x)` of M L10557, L10824; it is weaker than `ContDiff ℝ 2`
  jointly, which is nevertheless sufficient (`IsC12On.of_contDiff`).
* **Itô's formula** (`ito_formula`): a.s., for all `t ∈ [0, T]`,
  `f(t, X_t) = f(0, X_0) + ∫_0^t [∂_s f + D_x f[b_s] + ½ ∑_k D_x² f[Φ^k_s, Φ^k_s]](s, X_s) ds
     + ∫_0^t (k ↦ D_x f(s, X_s)[Φ^k_s]) · dW_s`,
  with the martingale term a local Itô integral (its integrand is only locally square-integrable
  in general; `isProgressiveL2_itoIntegrand` identifies it with the `L²` integral when `D_x f` is
  bounded and `Φ ∈ L²`, which covers every use in the manuscripts).  Uses: M L1682-1686
  (`B:eq:ito-step`), L5021, L6487, L10573, L10842, L11811, L11865.
* The **localised form** (`ito_formula_localized`): `f ∈ C^{1,2}([0,T] × U)` with `U` open and
  `X_{t ∧ τ}` confined to a compact `K ⊆ U`; the identity holds for `t ≤ τ` with the martingale
  term stopped at `τ`.  Uses: M L3137 ("for a stopping time on which every pair distance is at
  least ε, Itô's formula applies directly"), L11691, L11875-11879 (`Φ(Q_I)` up to
  `T ∧ η ∧ σ ∧ τ_n`).
* The **additive-noise form** (`ito_formula_additive`), in the exact shape of
  `IsStrongSolution.lift` (`Y_t = Y_0 + ∫_0^t b ds + ∑_k (W^k_t - W^k_0) σ_k`, time index `ℝ≥0`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ι : Type*} [Fintype ι]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-! ### `C^{1,2}` regularity -/

/-- `f ∈ C^{1,2}([0, T] × U)`: jointly continuous; for `t ∈ [0,T]` and `x ∈ U` (open),
`f t` is differentiable at `x` with derivative `fderiv ℝ (f t) x`, and `fderiv ℝ (f t)` is
differentiable at `x`, with `D_x f` and `D_x² f` jointly continuous on `[0,T] × U`; and
`t ↦ f t x` is differentiable within `[0, T]` at every `t ∈ [0, T]` with jointly continuous
derivative `derivWithin (fun r => f r x) (Set.Icc 0 T) t`. -/
structure IsC12On (T : ℝ) (U : Set E) (f : ℝ → E → ℝ) : Prop where
  cont : ContinuousOn (Function.uncurry f) (Set.Icc 0 T ×ˢ U)
  hasFDerivAt : ∀ t ∈ Set.Icc 0 T, ∀ x ∈ U, HasFDerivAt (f t) (fderiv ℝ (f t) x) x
  hasFDerivAt_fderiv : ∀ t ∈ Set.Icc 0 T, ∀ x ∈ U,
    HasFDerivAt (fderiv ℝ (f t)) (fderiv ℝ (fderiv ℝ (f t)) x) x
  cont_fderiv : ContinuousOn (fun p : ℝ × E => fderiv ℝ (f p.1) p.2) (Set.Icc 0 T ×ˢ U)
  cont_fderiv₂ : ContinuousOn (fun p : ℝ × E => fderiv ℝ (fderiv ℝ (f p.1)) p.2)
    (Set.Icc 0 T ×ˢ U)
  hasDerivWithinAt : ∀ x ∈ U, ∀ t ∈ Set.Icc 0 T,
    HasDerivWithinAt (fun r => f r x) (derivWithin (fun r => f r x) (Set.Icc 0 T) t)
      (Set.Icc 0 T) t
  cont_deriv : ContinuousOn (fun p : ℝ × E => derivWithin (fun r => f r p.2) (Set.Icc 0 T) p.1)
    (Set.Icc 0 T ×ˢ U)

theorem IsC12On.mono {T : ℝ} {U U' : Set E} {f : ℝ → E → ℝ} (hf : IsC12On T U f)
    (hU : U' ⊆ U) : IsC12On T U' f where
  cont := hf.cont.mono (Set.prod_mono subset_rfl hU)
  hasFDerivAt := fun t ht x hx => hf.hasFDerivAt t ht x (hU hx)
  hasFDerivAt_fderiv := fun t ht x hx => hf.hasFDerivAt_fderiv t ht x (hU hx)
  cont_fderiv := hf.cont_fderiv.mono (Set.prod_mono subset_rfl hU)
  cont_fderiv₂ := hf.cont_fderiv₂.mono (Set.prod_mono subset_rfl hU)
  hasDerivWithinAt := fun x hx t ht => hf.hasDerivWithinAt x (hU hx) t ht
  cont_deriv := hf.cont_deriv.mono (Set.prod_mono subset_rfl hU)

/-- A jointly `C²` function is `C^{1,2}` (proof of `IsC12On.of_contDiff`, stated first so that
`isC12On_of_contDiff` can use it). -/
theorem isC12On_of_contDiff_joint (T : ℝ) (U : Set E) (f : ℝ → E → ℝ)
    (hf : ContDiff ℝ 2 (Function.uncurry f)) : IsC12On T U f := by
  set g : ℝ × E → ℝ := Function.uncurry f with hg
  have hft : ∀ t, ContDiff ℝ 2 (f t) := fun t =>
    hf.comp (contDiff_const.prodMk contDiff_id)
  have hfx : ∀ x, ContDiff ℝ 2 (fun r => f r x) := fun x =>
    hf.comp (contDiff_id.prodMk contDiff_const)
  -- first derivative as a function of the pair
  set F1 : ℝ × E → E →L[ℝ] ℝ := fun p => (fderiv ℝ g p).comp (ContinuousLinearMap.inr ℝ ℝ E) with hF1
  have hD1 : ContDiff ℝ 1 (fderiv ℝ g) := hf.fderiv_right (by norm_num)
  have hF1c : ContDiff ℝ 1 F1 := by
    have : ContDiff ℝ 1 (fun p : ℝ × E => (ContinuousLinearMap.compL ℝ E (ℝ × E) ℝ).flip
        (ContinuousLinearMap.inr ℝ ℝ E) (fderiv ℝ g p)) := by
      exact (ContinuousLinearMap.contDiff _).comp hD1
    exact this
  have hF1eq : ∀ t, fderiv ℝ (f t) = fun x => F1 (t, x) := by
    intro t
    funext x
    have h1 : HasFDerivAt (fun x : E => g (t, x)) ((fderiv ℝ g (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ E)) x := by
      have hga : HasFDerivAt g (fderiv ℝ g (t, x)) (t, x) :=
        ((hf.differentiable (by norm_num)) (t, x)).hasFDerivAt
      have hin : HasFDerivAt (fun x : E => (t, x)) (ContinuousLinearMap.inr ℝ ℝ E) x :=
        (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
      exact hga.comp x hin
    exact h1.fderiv
  have hF1d : ContDiff ℝ 0 (fderiv ℝ F1) := hF1c.fderiv_right (by norm_num)
  have hF2c : Continuous (fun p : ℝ × E => (fderiv ℝ F1 p).comp (ContinuousLinearMap.inr ℝ ℝ E)) := by
    have : ContDiff ℝ 0 (fun p : ℝ × E => (ContinuousLinearMap.compL ℝ E (ℝ × E) (E →L[ℝ] ℝ)).flip
        (ContinuousLinearMap.inr ℝ ℝ E) (fderiv ℝ F1 p)) :=
      (ContinuousLinearMap.contDiff _).comp hF1d
    exact this.continuous
  have hF2eq : ∀ t x, fderiv ℝ (fderiv ℝ (f t)) x = (fderiv ℝ F1 (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
    intro t x
    rw [hF1eq t]
    have hga : HasFDerivAt F1 (fderiv ℝ F1 (t, x)) (t, x) :=
      ((hF1c.differentiable (by norm_num)) (t, x)).hasFDerivAt
    have hin : HasFDerivAt (fun x : E => (t, x)) (ContinuousLinearMap.inr ℝ ℝ E) x :=
      (hasFDerivAt_const t x).prodMk (hasFDerivAt_id x)
    exact (hga.comp x hin).fderiv
  refine ⟨hf.continuous.continuousOn, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t _ x _
    exact (((hft t).differentiable (by norm_num)) x).hasFDerivAt
  · intro t _ x _
    have : ContDiff ℝ 1 (fderiv ℝ (f t)) := (hft t).fderiv_right (by norm_num)
    exact ((this.differentiable (by norm_num)) x).hasFDerivAt
  · have : (fun p : ℝ × E => fderiv ℝ (f p.1) p.2) = F1 := by
      funext p; rw [hF1eq p.1]
    rw [this]
    exact hF1c.continuous.continuousOn
  · have : (fun p : ℝ × E => fderiv ℝ (fderiv ℝ (f p.1)) p.2) =
        fun p => (fderiv ℝ F1 p).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
      funext p; rw [hF2eq p.1 p.2]
    rw [this]
    exact hF2c.continuousOn
  · intro x _ t _
    exact ((((hfx x).differentiable (by norm_num)) t).differentiableWithinAt).hasDerivWithinAt
  · rcases lt_or_ge 0 T with hT | hT
    · have hc : Continuous (fun p : ℝ × E => fderiv ℝ g p (1, 0)) := by
        have : Continuous (fun p : ℝ × E => fderiv ℝ g p) := hD1.continuous
        exact this.clm_apply continuous_const
      refine hc.continuousOn.congr ?_
      intro p hp
      have hdiff : DifferentiableAt ℝ (fun r => f r p.2) p.1 :=
        ((hfx p.2).differentiable (by norm_num)) p.1
      show derivWithin (fun r => f r p.2) (Set.Icc 0 T) p.1 = fderiv ℝ g p (1, 0)
      rw [hdiff.derivWithin (uniqueDiffOn_Icc hT p.1 hp.1)]
      have hga : HasFDerivAt g (fderiv ℝ g (p.1, p.2)) (p.1, p.2) :=
        ((hf.differentiable (by norm_num)) (p.1, p.2)).hasFDerivAt
      have hin : HasFDerivAt (fun r : ℝ => (r, p.2)) (ContinuousLinearMap.inl ℝ ℝ E) p.1 :=
        (hasFDerivAt_id p.1).prodMk (hasFDerivAt_const p.2 p.1)
      have := (hga.comp p.1 hin).fderiv
      show fderiv ℝ (fun r => g (r, p.2)) p.1 1 = _
      have e : fderiv ℝ (fun r => g (r, p.2)) p.1 = fderiv ℝ g (p.1, p.2) ∘L ContinuousLinearMap.inl ℝ ℝ E := this
      rw [e]
      simp
    · have h0 : ∀ p ∈ Set.Icc (0:ℝ) T ×ˢ U, derivWithin (fun r => f r p.2) (Set.Icc 0 T) p.1 = 0 := by
        intro p hp
        apply derivWithin_zero_of_not_accPt
        intro hacc
        apply Set.Infinite.of_accPt hacc
        exact (Set.finite_singleton (0:ℝ)).subset (fun x hx => by
          have := hx.1; have := hx.2; simp only [Set.mem_singleton_iff]; linarith [hx.1, hx.2])
      exact continuousOn_const.congr h0


/-- A time-independent `C²` function is `C^{1,2}`. -/
theorem isC12On_of_contDiff (T : ℝ) (U : Set E) (g : E → ℝ) (hg : ContDiff ℝ 2 g) :
    IsC12On T U (fun _ x => g x) :=
  isC12On_of_contDiff_joint T U _ (hg.comp contDiff_snd)

/-- A jointly `C²` function is `C^{1,2}`. -/
theorem IsC12On.of_contDiff (T : ℝ) (U : Set E) (f : ℝ → E → ℝ)
    (hf : ContDiff ℝ 2 (Function.uncurry f)) : IsC12On T U f :=
  isC12On_of_contDiff_joint T U f hf

/-! ### Analytic core of Itô's formula -/

section Taylor

theorem exists_bound_clm {X F G : Type*} [TopologicalSpace X] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] {g : X → F →L[ℝ] G} {s : Set X}
    (hs : IsCompact s) (hg : ContinuousOn g s) : ∃ C : ℝ, ∀ x ∈ s, ‖g x‖ ≤ C :=
  hs.exists_bound_of_continuousOn hg

theorem continuousOn_norm_clm {X F G : Type*} [TopologicalSpace X] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] {g : X → F →L[ℝ] G} {s : Set X}
    (hg : ContinuousOn g s) : ContinuousOn (fun x => ‖g x‖) s :=
  continuous_norm.comp_continuousOn hg

variable {T : ℝ} {U K : Set E} {f : ℝ → E → ℝ}

/-- A compact subset of an open set has a compact closed thickening inside the open set. -/
theorem exists_compact_thickening (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ IsCompact (Metric.cthickening δ K) ∧ Metric.cthickening δ K ⊆ U := by
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_cthickening_subset_open hU hKU
  exact ⟨δ, hδ, hK.cthickening, hsub⟩

/-- Second-order Taylor expansion, uniform over `t ∈ [0,T]`, `x ∈ K`. -/
theorem taylor_uniform (hf : IsC12On T U f) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ t ∈ Set.Icc 0 T, ∀ x ∈ K, ∀ h : E, ‖h‖ < η →
      |f t (x + h) - f t x - fderiv ℝ (f t) x h - (1 / 2) * fderiv ℝ (fderiv ℝ (f t)) x h h|
        ≤ ε * ‖h‖ ^ 2 := by
  obtain ⟨δ, hδ, hK', hK'U⟩ := exists_compact_thickening hU hK hKU
  have hcomp : IsCompact (Set.Icc (0:ℝ) T ×ˢ Metric.cthickening δ K) :=
    isCompact_Icc.prod hK'
  have hcont : ContinuousOn (fun p : ℝ × E => fderiv ℝ (fderiv ℝ (f p.1)) p.2)
      (Set.Icc (0:ℝ) T ×ˢ Metric.cthickening δ K) :=
    hf.cont_fderiv₂.mono (Set.prod_mono subset_rfl hK'U)
  have huc := hcomp.uniformContinuousOn_of_continuous hcont
  have huc' : @UniformContinuousOn (ℝ × E) (E →L[ℝ] E →L[ℝ] ℝ) PseudoMetricSpace.toUniformSpace
      PseudoMetricSpace.toUniformSpace (fun p : ℝ × E => fderiv ℝ (fderiv ℝ (f p.1)) p.2)
      (Set.Icc (0:ℝ) T ×ˢ Metric.cthickening δ K) := huc
  obtain ⟨η₁, hη₁, hη₁'⟩ := Metric.uniformContinuousOn_iff.1 huc' ε hε
  refine ⟨min δ η₁, lt_min hδ hη₁, ?_⟩
  intro t ht x hx h hh
  have hhδ : ‖h‖ < δ := lt_of_lt_of_le hh (min_le_left _ _)
  have hhη : ‖h‖ < η₁ := lt_of_lt_of_le hh (min_le_right _ _)
  -- points on the segment lie in the thickening
  have hseg : ∀ s ∈ Set.Icc (0:ℝ) 1, x + s • h ∈ Metric.cthickening δ K := by
    intro s hs
    refine Metric.mem_cthickening_of_dist_le (x + s • h) x δ K hx ?_
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
    nlinarith [hs.2, norm_nonneg h]
  have hsegU : ∀ s ∈ Set.Icc (0:ℝ) 1, x + s • h ∈ U := fun s hs => hK'U (hseg s hs)
  set ε' := ε * ‖h‖ with hε'
  -- derivative of the first derivative along the segment
  set c : E →L[ℝ] ℝ := fderiv ℝ (fderiv ℝ (f t)) x h with hc
  set ψ : ℝ → E →L[ℝ] ℝ := fun s => fderiv ℝ (f t) (x + s • h) - s • c with hψ
  have hline : ∀ s : ℝ, HasDerivAt (fun s : ℝ => x + s • h) h s := by
    intro s
    simpa using ((hasDerivAt_id s).smul_const h).const_add x
  have hψd : ∀ s ∈ Set.Icc (0:ℝ) 1, HasDerivAt ψ
      (fderiv ℝ (fderiv ℝ (f t)) (x + s • h) h - c) s := by
    intro s hs
    have h1 : HasDerivAt (fun s : ℝ => fderiv ℝ (f t) (x + s • h))
        (fderiv ℝ (fderiv ℝ (f t)) (x + s • h) h) s :=
      (hf.hasFDerivAt_fderiv t ht _ (hsegU s hs)).comp_hasDerivAt s (hline s)
    have h2 : HasDerivAt (fun s : ℝ => s • c) c s := by
      simpa using (hasDerivAt_id s).smul_const c
    exact h1.sub h2
  have hψb : ∀ s ∈ Set.Icc (0:ℝ) 1,
      ‖fderiv ℝ (fderiv ℝ (f t)) (x + s • h) h - c‖ ≤ ε' := by
    intro s hs
    have hd : dist (t, x + s • h) (t, x) < η₁ := by
      rw [Prod.dist_eq]
      simp only [dist_self, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hs.1]
      refine lt_of_le_of_lt (max_le (by positivity) ?_) hhη
      nlinarith [hs.2, norm_nonneg h]
    have := hη₁' (t, x + s • h) ⟨ht, hseg s hs⟩ (t, x) ⟨ht, Metric.self_subset_cthickening _ hx⟩ hd
    have this' : ‖fderiv ℝ (fderiv ℝ (f t)) (x + s • h) - fderiv ℝ (fderiv ℝ (f t)) x‖ < ε := by
      exact (dist_eq_norm (fderiv ℝ (fderiv ℝ (f t)) (x + s • h)) (fderiv ℝ (fderiv ℝ (f t)) x)).symm.trans_lt this
    calc ‖fderiv ℝ (fderiv ℝ (f t)) (x + s • h) h - c‖
        = ‖(fderiv ℝ (fderiv ℝ (f t)) (x + s • h) - fderiv ℝ (fderiv ℝ (f t)) x) h‖ := by
          simp [hc]
      _ ≤ ‖fderiv ℝ (fderiv ℝ (f t)) (x + s • h) - fderiv ℝ (fderiv ℝ (f t)) x‖ * ‖h‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ ε * ‖h‖ := by gcongr
  have hψdiff : ∀ s ∈ Set.Icc (0:ℝ) 1, ‖ψ s - ψ 0‖ ≤ ε' * 1 := by
    intro s hs
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ) (f := ψ)
      (f' := fun s => fderiv ℝ (fderiv ℝ (f t)) (x + s • h) h - c) (s := Set.Icc (0:ℝ) 1)
      (x := 0) (y := s) (C := ε')
      (fun s hs => (hψd s hs).hasDerivWithinAt) hψb (convex_Icc 0 1) ⟨le_rfl, zero_le_one⟩ hs
    refine this.trans (mul_le_mul_of_nonneg_left ?_ (by rw [hε']; positivity))
    rw [sub_zero, Real.norm_eq_abs, abs_of_nonneg hs.1]; exact hs.2
  -- the remainder function
  set φ : ℝ → ℝ := fun s => f t (x + s • h) - s * fderiv ℝ (f t) x h - (1 / 2) * s ^ 2 * c h
    with hφ
  have hφd : ∀ s ∈ Set.Icc (0:ℝ) 1, HasDerivAt φ
      (fderiv ℝ (f t) (x + s • h) h - fderiv ℝ (f t) x h - s * c h) s := by
    intro s hs
    have h1 : HasDerivAt (fun s : ℝ => f t (x + s • h)) (fderiv ℝ (f t) (x + s • h) h) s :=
      (hf.hasFDerivAt t ht _ (hsegU s hs)).comp_hasDerivAt s (hline s)
    have h2 : HasDerivAt (fun s : ℝ => s * fderiv ℝ (f t) x h) (fderiv ℝ (f t) x h) s := by
      simpa using (hasDerivAt_id s).mul_const (fderiv ℝ (f t) x h)
    have h3 : HasDerivAt (fun s : ℝ => (1 / 2) * s ^ 2 * c h) (s * c h) s := by
      have := ((hasDerivAt_pow 2 s).const_mul (1 / 2 : ℝ)).mul_const (c h)
      convert this using 1
      simp
    exact (h1.sub h2).sub h3
  have hφb : ∀ s ∈ Set.Icc (0:ℝ) 1,
      ‖fderiv ℝ (f t) (x + s • h) h - fderiv ℝ (f t) x h - s * c h‖ ≤ ε * ‖h‖ ^ 2 := by
    intro s hs
    have e : fderiv ℝ (f t) (x + s • h) h - fderiv ℝ (f t) x h - s * c h = (ψ s - ψ 0) h := by
      simp [hψ]; ring
    rw [e]
    calc ‖(ψ s - ψ 0) h‖ ≤ ‖ψ s - ψ 0‖ * ‖h‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (ε' * 1) * ‖h‖ := by gcongr; exact hψdiff s hs
      _ = ε * ‖h‖ ^ 2 := by rw [hε']; ring
  have hfinal := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ) (f := φ)
      (f' := fun s => fderiv ℝ (f t) (x + s • h) h - fderiv ℝ (f t) x h - s * c h)
      (s := Set.Icc (0:ℝ) 1) (x := 0) (y := 1) (C := ε * ‖h‖ ^ 2)
      (fun s hs => (hφd s hs).hasDerivWithinAt) hφb (convex_Icc 0 1) ⟨le_rfl, zero_le_one⟩
      ⟨zero_le_one, le_rfl⟩
  simp only [hφ, Real.norm_eq_abs] at hfinal
  have e : f t (x + (1:ℝ) • h) - (1:ℝ) * fderiv ℝ (f t) x h - 1 / 2 * (1:ℝ) ^ 2 * c h -
      (f t (x + (0:ℝ) • h) - (0:ℝ) * fderiv ℝ (f t) x h - 1 / 2 * (0:ℝ) ^ 2 * c h) =
      f t (x + h) - f t x - fderiv ℝ (f t) x h - 1 / 2 * fderiv ℝ (fderiv ℝ (f t)) x h h := by
    simp [hc]; ring
  rw [e] at hfinal
  simpa [hc] using hfinal


/-- Mean value theorem in time. -/
theorem time_mvt (hf : IsC12On T U f) {a a' : ℝ} (ha : 0 ≤ a) (haa' : a ≤ a') (ha'T : a' ≤ T)
    {x : E} (hx : x ∈ U) :
    ∃ ξ ∈ Set.Icc a a', f a' x - f a x =
      derivWithin (fun r => f r x) (Set.Icc 0 T) ξ * (a' - a) := by
  rcases haa'.eq_or_lt with h | h
  · exact ⟨a, ⟨le_rfl, haa'⟩, by rw [h]; simp⟩
  · have hcont : ContinuousOn (fun r => f r x) (Set.Icc a a') := by
      have : ContinuousOn (fun r : ℝ => (r, x)) (Set.Icc a a') := by fun_prop
      refine hf.cont.comp this ?_
      intro r hr
      exact ⟨⟨ha.trans hr.1, hr.2.trans ha'T⟩, hx⟩
    obtain ⟨ξ, hξ, hξ'⟩ := exists_hasDerivAt_eq_slope (fun r => f r x)
      (fun r => derivWithin (fun r => f r x) (Set.Icc 0 T) r) h hcont (by
        intro r hr
        have hrI : r ∈ Set.Icc (0:ℝ) T := ⟨(ha.trans hr.1.le), (hr.2.le.trans ha'T)⟩
        have hnhds : Set.Icc (0:ℝ) T ∈ 𝓝 r :=
          Icc_mem_nhds (lt_of_le_of_lt ha hr.1) (lt_of_lt_of_le hr.2 ha'T)
        exact (hf.hasDerivWithinAt x hx r hrI).hasDerivAt hnhds)
    refine ⟨ξ, ⟨hξ.1.le, hξ.2.le⟩, ?_⟩
    rw [hξ']
    field_simp [(sub_pos.2 h).ne']

/-- Uniform continuity of the time derivative on `[0,T] × K`, `K ⊆ U` compact. -/
theorem uniformContinuousOn_timeDeriv (hf : IsC12On T U f) (hK : IsCompact K) (hKU : K ⊆ U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ s ∈ Set.Icc 0 T, ∀ y ∈ K, ∀ s' ∈ Set.Icc 0 T, ∀ y' ∈ K,
      |s - s'| < η → ‖y - y'‖ < η →
        |derivWithin (fun r => f r y) (Set.Icc 0 T) s - derivWithin (fun r => f r y')
          (Set.Icc 0 T) s'| < ε := by
  have hcomp : IsCompact (Set.Icc (0:ℝ) T ×ˢ K) := isCompact_Icc.prod hK
  have hcont := hf.cont_deriv.mono (Set.prod_mono subset_rfl hKU)
  have huc := hcomp.uniformContinuousOn_of_continuous hcont
  have huc' : @UniformContinuousOn (ℝ × E) ℝ PseudoMetricSpace.toUniformSpace
      PseudoMetricSpace.toUniformSpace (fun p : ℝ × E =>
        derivWithin (fun r => f r p.2) (Set.Icc 0 T) p.1) (Set.Icc (0:ℝ) T ×ˢ K) := huc
  obtain ⟨η, hη, hη'⟩ := Metric.uniformContinuousOn_iff.1 huc' ε hε
  refine ⟨η, hη, fun s hs y hy s' hs' y' hy' h1 h2 => ?_⟩
  have hd : dist (s, y) (s', y') < η := by
    rw [Prod.dist_eq]
    exact max_lt (by rwa [Real.dist_eq]) (by rwa [dist_eq_norm])
  have := hη' (s, y) ⟨hs, hy⟩ (s', y') ⟨hs', hy'⟩ hd
  simpa [Real.dist_eq] using this


/-- One step of the Itô–Taylor expansion, uniformly over `K`: for `x, x + (u + v) ∈ K` and
`a ≤ a'` close to each other with `u, v` small,
`f a' (x + u + v) - f a x` is `∂_t f(a,x) (a' - a) + Df(a,x) u + Df(a,x) v + ½ D²f(a,x)[v,v]`
up to an error `ε₁ (a' - a) + 2 ε₂ (‖u‖² + ‖v‖²) + C₂ (‖u‖ ‖v‖ + ½ ‖u‖²)`. -/
theorem ito_taylor_step (hf : IsC12On T U f) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {C₂ : ℝ}
    (hC₂ : ∀ t ∈ Set.Icc 0 T, ∀ x ∈ K, ‖fderiv ℝ (fderiv ℝ (f t)) x‖ ≤ C₂)
    {ε₁ ε₂ : ℝ} (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ θ : ℝ, 0 < θ ∧ ∀ a ∈ Set.Icc 0 T, ∀ a' ∈ Set.Icc 0 T, a ≤ a' →
      a' - a < ρ → ∀ x ∈ K, ∀ u v : E, ‖u‖ < θ → ‖v‖ < θ → x + (u + v) ∈ K →
        |f a' (x + (u + v)) - f a x - derivWithin (fun r => f r x) (Set.Icc 0 T) a * (a' - a)
            - fderiv ℝ (f a) x u - fderiv ℝ (f a) x v
            - (1 / 2) * fderiv ℝ (fderiv ℝ (f a)) x v v|
          ≤ ε₁ * (a' - a) + 2 * ε₂ * (‖u‖ ^ 2 + ‖v‖ ^ 2) + C₂ * (‖u‖ * ‖v‖) + C₂ * ‖u‖ ^ 2 / 2 := by
  obtain ⟨η₃, hη₃, hη₃'⟩ := uniformContinuousOn_timeDeriv hf hK hKU hε₁
  obtain ⟨η₂, hη₂, hη₂'⟩ := taylor_uniform hf hU hK hKU hε₂
  refine ⟨η₃, hη₃, min η₃ η₂ / 2, by positivity, ?_⟩
  intro a ha a' ha' haa' hlt x hx u v hu hv hxuv
  set θ := min η₃ η₂ / 2 with hθ
  have hθ3 : θ ≤ η₃ / 2 := by rw [hθ]; have := min_le_left η₃ η₂; linarith
  have hθ2 : θ ≤ η₂ / 2 := by rw [hθ]; have := min_le_right η₃ η₂; linarith
  have hhn : ‖u + v‖ < min η₃ η₂ := by
    calc ‖u + v‖ ≤ ‖u‖ + ‖v‖ := norm_add_le _ _
      _ < θ + θ := add_lt_add hu hv
      _ = min η₃ η₂ := by rw [hθ]; ring
  have hxU : x ∈ U := hKU hx
  -- split into time and space increments
  have e1 : f a' (x + (u + v)) - f a x = (f a' (x + (u + v)) - f a (x + (u + v))) +
      (f a (x + (u + v)) - f a x) := by ring
  obtain ⟨ξ, hξ, hξe⟩ := time_mvt hf ha.1 haa' ha'.2 (hKU hxuv)
  have hξT : ξ ∈ Set.Icc (0:ℝ) T := ⟨ha.1.trans hξ.1, hξ.2.trans ha'.2⟩
  have hdt : |derivWithin (fun r => f r (x + (u + v))) (Set.Icc 0 T) ξ -
      derivWithin (fun r => f r x) (Set.Icc 0 T) a| < ε₁ := by
    refine hη₃' ξ hξT _ hxuv a ha x hx ?_ ?_
    · rw [abs_lt]; constructor <;> linarith [hξ.1, hξ.2]
    · rw [add_sub_cancel_left]
      exact lt_of_lt_of_le hhn (min_le_left _ _)
  have hTay := hη₂' a ha x hx (u + v) (lt_of_lt_of_le hhn (min_le_right _ _))
  -- second derivative expansion
  have hD2 : |fderiv ℝ (fderiv ℝ (f a)) x (u + v) (u + v) - fderiv ℝ (fderiv ℝ (f a)) x v v|
      ≤ C₂ * (2 * (‖u‖ * ‖v‖) + ‖u‖ ^ 2) := by
    have e : fderiv ℝ (fderiv ℝ (f a)) x (u + v) (u + v) - fderiv ℝ (fderiv ℝ (f a)) x v v =
        fderiv ℝ (fderiv ℝ (f a)) x u v + fderiv ℝ (fderiv ℝ (f a)) x v u +
          fderiv ℝ (fderiv ℝ (f a)) x u u := by
      simp only [map_add, ContinuousLinearMap.add_apply]; ring
    rw [e]
    have hb : ∀ p q : E, |fderiv ℝ (fderiv ℝ (f a)) x p q| ≤ C₂ * (‖p‖ * ‖q‖) := by
      intro p q
      calc |fderiv ℝ (fderiv ℝ (f a)) x p q| = ‖fderiv ℝ (fderiv ℝ (f a)) x p q‖ :=
            (Real.norm_eq_abs _).symm
        _ ≤ ‖fderiv ℝ (fderiv ℝ (f a)) x p‖ * ‖q‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ (‖fderiv ℝ (fderiv ℝ (f a)) x‖ * ‖p‖) * ‖q‖ := by
            gcongr; exact ContinuousLinearMap.le_opNorm _ _
        _ ≤ C₂ * ‖p‖ * ‖q‖ := by gcongr; exact hC₂ a ha x hx
        _ = C₂ * (‖p‖ * ‖q‖) := by ring
    calc _ ≤ |fderiv ℝ (fderiv ℝ (f a)) x u v| + |fderiv ℝ (fderiv ℝ (f a)) x v u| +
          |fderiv ℝ (fderiv ℝ (f a)) x u u| := by
          refine (abs_add_three _ _ _)
      _ ≤ C₂ * (‖u‖ * ‖v‖) + C₂ * (‖v‖ * ‖u‖) + C₂ * (‖u‖ * ‖u‖) := by
          gcongr <;> apply hb
      _ = _ := by ring
  have hnh : ‖u + v‖ ^ 2 ≤ 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
    have h := norm_add_le u v
    have h0 := norm_nonneg (u + v)
    nlinarith [mul_le_mul h h h0 (add_nonneg (norm_nonneg u) (norm_nonneg v)),
      sq_nonneg (‖u‖ - ‖v‖)]
  have hlin : fderiv ℝ (f a) x (u + v) = fderiv ℝ (f a) x u + fderiv ℝ (f a) x v := map_add _ _ _
  -- assemble
  have hmain : f a' (x + (u + v)) - f a x - derivWithin (fun r => f r x) (Set.Icc 0 T) a * (a' - a)
            - fderiv ℝ (f a) x u - fderiv ℝ (f a) x v
            - (1 / 2) * fderiv ℝ (fderiv ℝ (f a)) x v v =
      (derivWithin (fun r => f r (x + (u + v))) (Set.Icc 0 T) ξ -
        derivWithin (fun r => f r x) (Set.Icc 0 T) a) * (a' - a) +
      (f a (x + (u + v)) - f a x - fderiv ℝ (f a) x (u + v) -
        (1 / 2) * fderiv ℝ (fderiv ℝ (f a)) x (u + v) (u + v)) +
      (1 / 2) * (fderiv ℝ (fderiv ℝ (f a)) x (u + v) (u + v) -
        fderiv ℝ (fderiv ℝ (f a)) x v v) := by
    rw [e1, hξe, hlin]; ring
  rw [hmain]
  have hsub : 0 ≤ a' - a := sub_nonneg.2 haa'
  calc _ ≤ |(derivWithin (fun r => f r (x + (u + v))) (Set.Icc 0 T) ξ -
        derivWithin (fun r => f r x) (Set.Icc 0 T) a) * (a' - a)| +
      |(f a (x + (u + v)) - f a x - fderiv ℝ (f a) x (u + v) -
        (1 / 2) * fderiv ℝ (fderiv ℝ (f a)) x (u + v) (u + v))| +
      |(1 / 2) * (fderiv ℝ (fderiv ℝ (f a)) x (u + v) (u + v) -
        fderiv ℝ (fderiv ℝ (f a)) x v v)| := abs_add_three _ _ _
    _ ≤ ε₁ * (a' - a) + ε₂ * ‖u + v‖ ^ 2 + (1 / 2) * (C₂ * (2 * (‖u‖ * ‖v‖) + ‖u‖ ^ 2)) := by
        gcongr
        · rw [abs_mul, abs_of_nonneg hsub]
          exact mul_le_mul_of_nonneg_right hdt.le hsub
        · rw [abs_mul]; simp only [abs_div, abs_one, abs_two]
          gcongr
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hnh hε₂.le]


end Taylor

section PartitionSums

namespace Partition

variable {t : ℝ} (π : Partition 0 t)

theorem pt_mem_Icc (_ht : 0 ≤ t) (i : Fin (π.n + 1)) : π.pt i ∈ Set.Icc 0 t := by
  refine ⟨?_, ?_⟩
  · have := π.mono (Fin.zero_le i); rwa [π.first] at this
  · have := π.mono (Fin.le_last i); rwa [π.last] at this

theorem sum_telescope' (F : ℝ → ℝ) :
    ∑ i : Fin π.n, (F (π.pt i.succ) - F (π.pt i.castSucc)) = F t - F 0 := by
  have := Partition.sum_telescope π.n (fun i => F (π.pt i))
  rw [π.last, π.first] at this
  exact this

theorem sumIncrements_eq (g : ℝ → ℝ → ℝ) :
    π.sumIncrements g = ∑ i : Fin π.n, g (π.pt i.castSucc) (π.pt i.succ) := rfl

theorem sum_integral_Ioc (ht : 0 ≤ t) {g : ℝ → ℝ} (hg : IntegrableOn g (Set.Icc 0 t)) :
    ∑ i : Fin π.n, ∫ s in Set.Ioc (π.pt i.castSucc) (π.pt i.succ), g s =
      ∫ s in Set.Icc 0 t, g s := by
  set p : ℕ → ℝ := fun k => π.pt ⟨min k π.n, by omega⟩ with hp
  have hp0 : p 0 = 0 := by simp [hp, π.first]
  have hpn : p π.n = t := by
    simp only [hp, min_self]; exact π.last
  have hmono : Monotone p := by
    intro k l hkl
    exact π.mono (by simp only [Fin.mk_le_mk]; omega)
  have hmem : ∀ k, p k ∈ Set.Icc 0 t := fun k => π.pt_mem_Icc ht _
  have hsum : ∑ i : Fin π.n, ∫ s in Set.Ioc (π.pt i.castSucc) (π.pt i.succ), g s =
      ∑ k ∈ Finset.range π.n, ∫ s in p k..p (k + 1), g s := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => ∫ s in p k..p (k + 1), g s) π.n]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : π.pt i.castSucc = p i := by
      simp only [hp]; congr 1; ext; simp
    have h2 : π.pt i.succ = p (i + 1) := by
      simp only [hp]; congr 1; ext; simp
    rw [h1, h2, intervalIntegral.integral_of_le (hmono (Nat.le_succ _))]
  rw [hsum, intervalIntegral.sum_integral_adjacent_intervals (a := p) (n := π.n)
    (fun k _ => ?_), hp0, hpn, intervalIntegral.integral_of_le ht, integral_Icc_eq_integral_Ioc]
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (hmono (Nat.le_succ _))]
  exact hg.mono_set (fun x (hx : p k < x ∧ x ≤ p (k + 1)) =>
    ⟨(hmem k).1.trans hx.1.le, hx.2.trans (hmem (k+1)).2⟩)

end Partition


/-- Riemann sums with left-endpoint tags converge to the integral. -/
theorem riemann_sum_tendsto {t : ℝ} (ht : 0 ≤ t) (π : ℕ → Partition 0 t)
    (hmesh : Tendsto (fun n => (π n).mesh) atTop (𝓝 0)) (H : ℝ → ℝ → ℝ) (β : ℝ → ℝ)
    (hβ : IntegrableOn β (Set.Icc 0 t)) (hβ0 : ∀ s, 0 ≤ β s)
    (hH0 : IntegrableOn (fun s => H s s) (Set.Icc 0 t))
    (hHa : ∀ a ∈ Set.Icc 0 t, IntegrableOn (H a) (Set.Icc 0 t))
    (hmod : ∀ ε : ℝ, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧ ∀ a ∈ Set.Icc 0 t, ∀ s ∈ Set.Icc 0 t, a ≤ s →
      s - a < ρ → |H a s - H s s| ≤ ε * β s) :
    Tendsto (fun n => ∑ i : Fin (π n).n,
      ∫ s in Set.Ioc ((π n).pt i.castSucc) ((π n).pt i.succ), H ((π n).pt i.castSucc) s)
      atTop (𝓝 (∫ s in Set.Icc 0 t, H s s)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set Bβ := ∫ s in Set.Icc 0 t, β s with hBβ
  have hBβ0 : 0 ≤ Bβ := setIntegral_nonneg measurableSet_Icc fun s _ => hβ0 s
  obtain ⟨ρ, hρ, hρ'⟩ := hmod (ε / (2 * (Bβ + 1))) (by positivity)
  have hev : ∀ᶠ n in atTop, (π n).mesh < ρ := (tendsto_order.1 hmesh).2 ρ hρ
  filter_upwards [hev] with n hn
  set P := π n
  have hmem : ∀ i : Fin P.n, P.pt i.castSucc ∈ Set.Icc 0 t ∧ P.pt i.succ ∈ Set.Icc 0 t :=
    fun i => ⟨P.pt_mem_Icc ht _, P.pt_mem_Icc ht _⟩
  have hIoc : ∀ i : Fin P.n, Set.Ioc (P.pt i.castSucc) (P.pt i.succ) ⊆ Set.Icc 0 t := by
    intro i x hx
    exact ⟨(hmem i).1.1.trans hx.1.le, hx.2.trans (hmem i).2.2⟩
  have e : (∑ i : Fin P.n, ∫ s in Set.Ioc (P.pt i.castSucc) (P.pt i.succ), H (P.pt i.castSucc) s)
      - ∫ s in Set.Icc 0 t, H s s =
      ∑ i : Fin P.n, ∫ s in Set.Ioc (P.pt i.castSucc) (P.pt i.succ),
        (H (P.pt i.castSucc) s - H s s) := by
    rw [← P.sum_integral_Ioc ht hH0, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_sub ((hHa _ (hmem i).1).mono_set (hIoc i)) (hH0.mono_set (hIoc i))]
  rw [dist_eq_norm, e]
  have hbd : ∀ i : Fin P.n, ‖∫ s in Set.Ioc (P.pt i.castSucc) (P.pt i.succ),
        (H (P.pt i.castSucc) s - H s s)‖ ≤
      (ε / (2 * (Bβ + 1))) * ∫ s in Set.Ioc (P.pt i.castSucc) (P.pt i.succ), β s := by
    intro i
    rw [← integral_const_mul]
    refine norm_integral_le_of_norm_le ((hβ.mono_set (hIoc i)).const_mul _) ?_
    refine (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun s hs => ?_)
    rw [Real.norm_eq_abs]
    refine hρ' _ (hmem i).1 s (hIoc i hs) hs.1.le ?_
    calc s - P.pt i.castSucc ≤ P.pt i.succ - P.pt i.castSucc := by linarith [hs.2]
      _ ≤ P.mesh := P.le_mesh i
      _ < ρ := hn
  calc ‖∑ i : Fin P.n, ∫ s in Set.Ioc (P.pt i.castSucc) (P.pt i.succ),
        (H (P.pt i.castSucc) s - H s s)‖
      ≤ ∑ i : Fin P.n, ‖∫ s in Set.Ioc (P.pt i.castSucc) (P.pt i.succ),
        (H (P.pt i.castSucc) s - H s s)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin P.n, (ε / (2 * (Bβ + 1))) *
        ∫ s in Set.Ioc (P.pt i.castSucc) (P.pt i.succ), β s := Finset.sum_le_sum fun i _ => hbd i
    _ = (ε / (2 * (Bβ + 1))) * ∫ s in Set.Icc 0 t, β s := by
        rw [← Finset.mul_sum, P.sum_integral_Ioc ht hβ]
    _ < ε := by
        rw [← hBβ]
        have : Bβ / (Bβ + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
        calc ε / (2 * (Bβ + 1)) * Bβ = (ε / 2) * (Bβ / (Bβ + 1)) := by field_simp
          _ < (ε / 2) * 1 := by gcongr
          _ < ε := by linarith


end PartitionSums

section ItoDet

variable {T : ℝ} {U K : Set E} {f : ℝ → E → ℝ}

/-- The remainder of the Itô–Taylor expansion along one partition is small, uniformly over
partitions of small mesh. -/
theorem ito_remainder_bound (hf : IsC12On T U f) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) {X B M : ℝ → E} {b : ℝ → E}
    (hXK : ∀ s ∈ Set.Icc 0 t, X s ∈ K) (hXBM : ∀ s ∈ Set.Icc 0 t, X s = B s + M s)
    (hBc : ContinuousOn B (Set.Icc 0 t)) (hMc : ContinuousOn M (Set.Icc 0 t))
    (hb : IntegrableOn b (Set.Icc 0 t))
    (hBinc : ∀ a a', 0 ≤ a → a ≤ a' → a' ≤ t → B a' - B a = ∫ s in Set.Ioc a a', b s) :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ ε : ℝ, 0 < ε → ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ P : Partition 0 t, P.mesh < ρ₀ →
      ∀ C₃ : ℝ, P.sumIncrements (fun a a' => ‖M a' - M a‖ ^ 2) ≤ C₃ →
      |(f t (X t) - f 0 (X 0)) -
        P.sumIncrements (fun a a' => derivWithin (fun r => f r (X a)) (Set.Icc 0 T) a * (a' - a))
        - P.sumIncrements (fun a a' => fderiv ℝ (f a) (X a) (B a' - B a))
        - P.sumIncrements (fun a a' => fderiv ℝ (f a) (X a) (M a' - M a))
        - (1 / 2) * P.sumIncrements (fun a a' =>
            fderiv ℝ (fderiv ℝ (f a)) (X a) (M a' - M a) (M a' - M a))|
        ≤ ε * (t + 2 + 2 * C₃ + 2 * C₂) := by
  -- the bound `C₂` on the second derivative
  have hcompTK : IsCompact (Set.Icc (0:ℝ) T ×ˢ K) := isCompact_Icc.prod hK
  obtain ⟨C₂', hC₂'⟩ := exists_bound_clm hcompTK
    (hf.cont_fderiv₂.mono (Set.prod_mono subset_rfl hKU))
  set C₂ := max C₂' 0 with hC₂def
  have hC₂0 : 0 ≤ C₂ := le_max_right _ _
  have hC₂ : ∀ s ∈ Set.Icc 0 T, ∀ x ∈ K, ‖fderiv ℝ (fderiv ℝ (f s)) x‖ ≤ C₂ := by
    intro s hs x hx
    exact (hC₂' (s, x) ⟨hs, hx⟩).trans (le_max_left _ _)
  refine ⟨C₂, hC₂0, fun ε hε => ?_⟩
  set V := ∫ s in Set.Icc 0 t, ‖b s‖ with hV
  have hV0 : 0 ≤ V := setIntegral_nonneg measurableSet_Icc fun s _ => norm_nonneg _
  -- choose the step parameters
  obtain ⟨ρ, hρ, θ, hθ, hstep⟩ := ito_taylor_step hf hU hK hKU hC₂ hε hε
  set θ' := min θ (min ε 1 / (V + 1)) with hθ'
  have hθ'pos : 0 < θ' := lt_min hθ (by positivity)
  have hθ'θ : θ' ≤ θ := min_le_left _ _
  have hθ'V : θ' * V ≤ min ε 1 := by
    have h1 : θ' ≤ min ε 1 / (V + 1) := min_le_right _ _
    calc θ' * V ≤ θ' * (V + 1) := by nlinarith
      _ ≤ min ε 1 / (V + 1) * (V + 1) := by gcongr
      _ = min ε 1 := by field_simp
  -- uniform continuity of `B` and `M`
  have hcompt : IsCompact (Set.Icc (0:ℝ) t) := isCompact_Icc
  obtain ⟨ρB, hρB, hρB'⟩ := Metric.uniformContinuousOn_iff.1
    (hcompt.uniformContinuousOn_of_continuous hBc) θ' hθ'pos
  obtain ⟨ρM, hρM, hρM'⟩ := Metric.uniformContinuousOn_iff.1
    (hcompt.uniformContinuousOn_of_continuous hMc) θ' hθ'pos
  refine ⟨min ρ (min ρB ρM), lt_min hρ (lt_min hρB hρM), fun P hP C₃ hC₃ => ?_⟩
  have hPρ : P.mesh < ρ := lt_of_lt_of_le hP (min_le_left _ _)
  have hPB : P.mesh < ρB := lt_of_lt_of_le hP ((min_le_right _ _).trans (min_le_left _ _))
  have hPM : P.mesh < ρM := lt_of_lt_of_le hP ((min_le_right _ _).trans (min_le_right _ _))
  have hmem : ∀ i : Fin (P.n + 1), P.pt i ∈ Set.Icc 0 t := fun i => P.pt_mem_Icc ht0 i
  have hlen : ∀ i : Fin P.n, P.pt i.succ - P.pt i.castSucc ≤ P.mesh := fun i => P.le_mesh i
  have hle : ∀ i : Fin P.n, P.pt i.castSucc ≤ P.pt i.succ := fun i => P.pt_le i
  -- the per-interval error
  set ΔB : Fin P.n → E := fun i => B (P.pt i.succ) - B (P.pt i.castSucc) with hΔB
  set ΔM : Fin P.n → E := fun i => M (P.pt i.succ) - M (P.pt i.castSucc) with hΔM
  have hΔBθ : ∀ i, ‖ΔB i‖ < θ' := by
    intro i
    have := hρB' _ (hmem i.succ) _ (hmem i.castSucc)
      (by rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 (hle i))]; exact lt_of_le_of_lt (hlen i) hPB)
    simpa [hΔB, dist_eq_norm] using this
  have hΔMθ : ∀ i, ‖ΔM i‖ < θ' := by
    intro i
    have := hρM' _ (hmem i.succ) _ (hmem i.castSucc)
      (by rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.2 (hle i))]; exact lt_of_le_of_lt (hlen i) hPM)
    simpa [hΔM, dist_eq_norm] using this
  have hXi : ∀ i : Fin P.n, X (P.pt i.succ) = X (P.pt i.castSucc) + (ΔB i + ΔM i) := by
    intro i
    rw [hXBM _ (hmem i.succ), hXBM _ (hmem i.castSucc)]
    simp only [hΔB, hΔM]; abel
  set e : Fin P.n → ℝ := fun i =>
    f (P.pt i.succ) (X (P.pt i.succ)) - f (P.pt i.castSucc) (X (P.pt i.castSucc))
      - derivWithin (fun r => f r (X (P.pt i.castSucc))) (Set.Icc 0 T) (P.pt i.castSucc) *
          (P.pt i.succ - P.pt i.castSucc)
      - fderiv ℝ (f (P.pt i.castSucc)) (X (P.pt i.castSucc)) (ΔB i)
      - fderiv ℝ (f (P.pt i.castSucc)) (X (P.pt i.castSucc)) (ΔM i)
      - (1 / 2) * fderiv ℝ (fderiv ℝ (f (P.pt i.castSucc))) (X (P.pt i.castSucc)) (ΔM i) (ΔM i)
    with he
  have hsum_e : (f t (X t) - f 0 (X 0)) -
        P.sumIncrements (fun a a' => derivWithin (fun r => f r (X a)) (Set.Icc 0 T) a * (a' - a))
        - P.sumIncrements (fun a a' => fderiv ℝ (f a) (X a) (B a' - B a))
        - P.sumIncrements (fun a a' => fderiv ℝ (f a) (X a) (M a' - M a))
        - (1 / 2) * P.sumIncrements (fun a a' =>
            fderiv ℝ (fderiv ℝ (f a)) (X a) (M a' - M a) (M a' - M a)) = ∑ i, e i := by
    have htel := P.sum_telescope' (fun s => f s (X s))
    simp only [Partition.sumIncrements_eq, he, Finset.mul_sum, Finset.sum_sub_distrib]
    rw [← htel]
    simp only [hΔB, hΔM, Finset.sum_sub_distrib]
  rw [hsum_e]
  -- bound each error
  set w : Fin P.n → ℝ := fun i => P.pt i.succ - P.pt i.castSucc with hw
  have hbound : ∀ i, |e i| ≤ ε * w i + 2 * ε * (‖ΔB i‖ ^ 2 + ‖ΔM i‖ ^ 2) +
      C₂ * (‖ΔB i‖ * ‖ΔM i‖) + C₂ * ‖ΔB i‖ ^ 2 / 2 := by
    intro i
    have hai : P.pt i.castSucc ∈ Set.Icc 0 T := ⟨(hmem _).1, (hmem _).2.trans htT⟩
    have hai' : P.pt i.succ ∈ Set.Icc 0 T := ⟨(hmem _).1, (hmem _).2.trans htT⟩
    have := hstep _ hai _ hai' (hle i) (lt_of_le_of_lt (hlen i) hPρ) (X (P.pt i.castSucc))
      (hXK _ (hmem _)) (ΔB i) (ΔM i) ((hΔBθ i).trans_le hθ'θ) ((hΔMθ i).trans_le hθ'θ)
      (by rw [← hXi i]; exact hXK _ (hmem _))
    rw [← hXi i] at this
    simpa [he, hw] using this
  -- sums
  have hsumw : ∑ i, w i = t := by simpa [hw] using P.sum_length
  have hsump : ∑ i, ‖ΔB i‖ ≤ V := by
    have h1 : ∀ i : Fin P.n, ‖ΔB i‖ ≤ ∫ s in Set.Ioc (P.pt i.castSucc) (P.pt i.succ), ‖b s‖ := by
      intro i
      simp only [hΔB]
      rw [hBinc _ _ (hmem _).1 (hle i) (hmem _).2]
      exact norm_integral_le_integral_norm _
    calc ∑ i, ‖ΔB i‖ ≤ ∑ i : Fin P.n, ∫ s in Set.Ioc (P.pt i.castSucc) (P.pt i.succ), ‖b s‖ :=
          Finset.sum_le_sum fun i _ => h1 i
      _ = V := P.sum_integral_Ioc ht0 hb.norm
  have hmin1 : min ε 1 ≤ ε := min_le_left _ _
  have hmin2 : min ε 1 ≤ 1 := min_le_right _ _
  calc |∑ i, e i| ≤ ∑ i, |e i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (ε * w i + 2 * ε * (‖ΔB i‖ ^ 2 + ‖ΔM i‖ ^ 2) +
          C₂ * (‖ΔB i‖ * ‖ΔM i‖) + C₂ * ‖ΔB i‖ ^ 2 / 2) := Finset.sum_le_sum fun i _ => hbound i
    _ ≤ ε * t + 2 * ε * (θ' * V + C₃) + C₂ * (θ' * V) + C₂ * (θ' * V) / 2 := by
        have h1 : ∑ i, ‖ΔB i‖ ^ 2 ≤ θ' * V := by
          calc ∑ i, ‖ΔB i‖ ^ 2 ≤ ∑ i, θ' * ‖ΔB i‖ := Finset.sum_le_sum fun i _ => by
                nlinarith [hΔBθ i, norm_nonneg (ΔB i)]
            _ = θ' * ∑ i, ‖ΔB i‖ := by rw [Finset.mul_sum]
            _ ≤ θ' * V := by gcongr
        have h2 : ∑ i, ‖ΔB i‖ * ‖ΔM i‖ ≤ θ' * V := by
          calc ∑ i, ‖ΔB i‖ * ‖ΔM i‖ ≤ ∑ i, θ' * ‖ΔB i‖ := Finset.sum_le_sum fun i _ => by
                nlinarith [hΔMθ i, norm_nonneg (ΔB i), norm_nonneg (ΔM i)]
            _ = θ' * ∑ i, ‖ΔB i‖ := by rw [Finset.mul_sum]
            _ ≤ θ' * V := by gcongr
        have h3 : ∑ i, ‖ΔM i‖ ^ 2 ≤ C₃ := by simpa [hΔM, Partition.sumIncrements_eq] using hC₃
        have h4 : ∑ x, C₂ * ‖ΔB x‖ ^ 2 / 2 = C₂ * (∑ x, ‖ΔB x‖ ^ 2) / 2 := by
          rw [← Finset.sum_div, ← Finset.mul_sum]
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hsumw]
        rw [h4]
        nlinarith [h1, h2, h3, hε.le, hC₂0, mul_le_mul_of_nonneg_left h1 hC₂0,
          mul_le_mul_of_nonneg_left h2 hC₂0]
    _ ≤ ε * (t + 2 + 2 * C₃ + 2 * C₂) := by
        nlinarith [hθ'V, hmin1, hmin2, hε, hC₂0, mul_le_mul_of_nonneg_left hθ'V hC₂0,
          mul_le_mul_of_nonneg_left hθ'V hε.le]


/-- **The deterministic core of Itô's formula.** -/
theorem ito_deterministic (hf : IsC12On T U f) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) {X B M : ℝ → E} {b : ℝ → E}
    (hXK : ∀ s ∈ Set.Icc 0 t, X s ∈ K) (hXBM : ∀ s ∈ Set.Icc 0 t, X s = B s + M s)
    (hBc : ContinuousOn B (Set.Icc 0 t)) (hMc : ContinuousOn M (Set.Icc 0 t))
    (hb : IntegrableOn b (Set.Icc 0 t))
    (hBinc : ∀ a a', 0 ≤ a → a ≤ a' → a' ≤ t → B a' - B a = ∫ s in Set.Ioc a a', b s)
    (π : ℕ → Partition 0 t) (hmesh : Tendsto (fun n => (π n).mesh) atTop (𝓝 0)) {N Q : ℝ}
    (H1 : Tendsto (fun n => (π n).sumIncrements fun a a' => fderiv ℝ (f a) (X a) (M a' - M a))
      atTop (𝓝 N))
    (H2 : Tendsto (fun n => (π n).sumIncrements fun a a' =>
      fderiv ℝ (fderiv ℝ (f a)) (X a) (M a' - M a) (M a' - M a)) atTop (𝓝 Q))
    (H3 : ∃ C : ℝ, ∀ᶠ n in atTop, (π n).sumIncrements (fun a a' => ‖M a' - M a‖ ^ 2) ≤ C) :
    f t (X t) = f 0 (X 0) + (∫ s in Set.Icc 0 t, derivWithin (fun r => f r (X s)) (Set.Icc 0 T) s)
      + (∫ s in Set.Icc 0 t, fderiv ℝ (f s) (X s) (b s)) + N + Q / 2 := by
  obtain ⟨C₂, hC₂0, hrem⟩ := ito_remainder_bound hf hU hK hKU ht0 htT hXK hXBM hBc hMc hb hBinc
  obtain ⟨C₃', hC₃'⟩ := H3
  set C₃ := max C₃' 0 with hC₃def
  have hC₃0 : 0 ≤ C₃ := le_max_right _ _
  have hC₃ : ∀ᶠ n in atTop, (π n).sumIncrements (fun a a' => ‖M a' - M a‖ ^ 2) ≤ C₃ :=
    hC₃'.mono fun n hn => hn.trans (le_max_left _ _)
  have hcompt : IsCompact (Set.Icc (0:ℝ) t) := isCompact_Icc
  have hmapsU : ∀ s ∈ Set.Icc (0:ℝ) t, (s, X s) ∈ Set.Icc (0:ℝ) T ×ˢ U :=
    fun s hs => ⟨⟨hs.1, hs.2.trans htT⟩, hKU (hXK s hs)⟩
  have hXc : ContinuousOn X (Set.Icc 0 t) := (hBc.add hMc).congr fun s hs => hXBM s hs
  have hpair : ContinuousOn (fun s => (s, X s)) (Set.Icc (0:ℝ) t) :=
    continuousOn_id.prodMk hXc
  have hDt : ContinuousOn (fun s => derivWithin (fun r => f r (X s)) (Set.Icc 0 T) s)
      (Set.Icc 0 t) := hf.cont_deriv.comp hpair hmapsU
  have hDf : ContinuousOn (fun s => fderiv ℝ (f s) (X s)) (Set.Icc 0 t) :=
    hf.cont_fderiv.comp hpair hmapsU
  -- Riemann sums: time derivative
  have hA : Tendsto (fun n => (π n).sumIncrements (fun a a' =>
      derivWithin (fun r => f r (X a)) (Set.Icc 0 T) a * (a' - a))) atTop
      (𝓝 (∫ s in Set.Icc 0 t, derivWithin (fun r => f r (X s)) (Set.Icc 0 T) s)) := by
    have huc := hcompt.uniformContinuousOn_of_continuous hDt
    have huc' : @UniformContinuousOn ℝ ℝ PseudoMetricSpace.toUniformSpace
        PseudoMetricSpace.toUniformSpace (fun s => derivWithin (fun r => f r (X s)) (Set.Icc 0 T) s)
        (Set.Icc (0:ℝ) t) := huc
    have := riemann_sum_tendsto ht0 π hmesh
      (fun a _ => derivWithin (fun r => f r (X a)) (Set.Icc 0 T) a) (fun _ => (1:ℝ))
      (integrableOn_const (by simp)) (fun _ => zero_le_one)
      (hDt.integrableOn_Icc) (fun a _ => integrableOn_const (by simp)) (by
        intro ε hε
        obtain ⟨ρ, hρ, hρ'⟩ := Metric.uniformContinuousOn_iff.1 huc' ε hε
        refine ⟨ρ, hρ, fun a ha s hs has hlt => ?_⟩
        have := hρ' a ha s hs (by rw [Real.dist_eq, abs_of_nonpos (by linarith)]; linarith)
        rw [Real.dist_eq] at this
        simpa using this.le)
    refine this.congr fun n => ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [setIntegral_const, Real.volume_real_Ioc_of_le ((π n).pt_le i), smul_eq_mul, mul_comm]
  -- Riemann sums: drift
  have hBsum : Tendsto (fun n => (π n).sumIncrements (fun a a' =>
      fderiv ℝ (f a) (X a) (B a' - B a))) atTop
      (𝓝 (∫ s in Set.Icc 0 t, fderiv ℝ (f s) (X s) (b s))) := by
    have huc := hcompt.uniformContinuousOn_of_continuous hDf
    have huc' : @UniformContinuousOn ℝ (E →L[ℝ] ℝ) PseudoMetricSpace.toUniformSpace
        PseudoMetricSpace.toUniformSpace (fun s => fderiv ℝ (f s) (X s)) (Set.Icc (0:ℝ) t) := huc
    obtain ⟨C₁, hC₁⟩ := exists_bound_clm hcompt hDf
    have hmeas : AEStronglyMeasurable (fun s => fderiv ℝ (f s) (X s) (b s))
        (volume.restrict (Set.Icc 0 t)) :=
      (ContinuousLinearMap.id ℝ (E →L[ℝ] ℝ)).aestronglyMeasurable_comp₂
        (hDf.aestronglyMeasurable measurableSet_Icc) hb.aestronglyMeasurable
    have hint0 : IntegrableOn (fun s => fderiv ℝ (f s) (X s) (b s)) (Set.Icc 0 t) := by
      refine Integrable.mono' (hb.norm.const_mul C₁) hmeas ?_
      refine (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ fun s hs => ?_)
      calc ‖fderiv ℝ (f s) (X s) (b s)‖ ≤ ‖fderiv ℝ (f s) (X s)‖ * ‖b s‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ C₁ * ‖b s‖ := by gcongr; exact hC₁ s hs
    have := riemann_sum_tendsto ht0 π hmesh
      (fun a s => fderiv ℝ (f a) (X a) (b s)) (fun s => ‖b s‖) hb.norm (fun _ => norm_nonneg _)
      hint0 (fun a _ => (fderiv ℝ (f a) (X a)).integrable_comp hb) (by
        intro ε hε
        obtain ⟨ρ, hρ, hρ'⟩ := Metric.uniformContinuousOn_iff.1 huc' ε hε
        refine ⟨ρ, hρ, fun a ha s hs has hlt => ?_⟩
        have h1 := hρ' a ha s hs (by rw [Real.dist_eq, abs_of_nonpos (by linarith)]; linarith)
        have h2 : ‖fderiv ℝ (f a) (X a) - fderiv ℝ (f s) (X s)‖ < ε :=
          (dist_eq_norm _ _).symm.trans_lt h1
        calc |fderiv ℝ (f a) (X a) (b s) - fderiv ℝ (f s) (X s) (b s)|
            = ‖(fderiv ℝ (f a) (X a) - fderiv ℝ (f s) (X s)) (b s)‖ := by
              rw [Real.norm_eq_abs]; simp
          _ ≤ ‖fderiv ℝ (f a) (X a) - fderiv ℝ (f s) (X s)‖ * ‖b s‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ ε * ‖b s‖ := by gcongr)
    refine this.congr fun n => ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    have hmem := (π n).pt_mem_Icc ht0
    have hbi : Integrable b (volume.restrict (Set.Ioc ((π n).pt i.castSucc) ((π n).pt i.succ))) :=
      hb.mono_set (fun x hx => ⟨(hmem _).1.trans hx.1.le, hx.2.trans (hmem _).2⟩)
    beta_reduce
    rw [ContinuousLinearMap.integral_comp_comm (fderiv ℝ (f ((π n).pt i.castSucc))
      (X ((π n).pt i.castSucc))) hbi,
      ← hBinc _ _ (hmem _).1 ((π n).pt_le i) (hmem _).2]
  -- the remainder tends to zero
  have hRem : Tendsto (fun n => (f t (X t) - f 0 (X 0)) -
        (π n).sumIncrements (fun a a' => derivWithin (fun r => f r (X a)) (Set.Icc 0 T) a * (a' - a))
        - (π n).sumIncrements (fun a a' => fderiv ℝ (f a) (X a) (B a' - B a))
        - (π n).sumIncrements (fun a a' => fderiv ℝ (f a) (X a) (M a' - M a))
        - (1 / 2) * (π n).sumIncrements (fun a a' =>
            fderiv ℝ (fderiv ℝ (f a)) (X a) (M a' - M a) (M a' - M a))) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε' hε'
    set Γ := t + 2 + 2 * C₃ + 2 * C₂ with hΓ
    have hΓ0 : 0 ≤ Γ := by positivity
    obtain ⟨ρ₀, hρ₀, hP⟩ := hrem (ε' / (Γ + 1)) (by positivity)
    filter_upwards [(tendsto_order.1 hmesh).2 ρ₀ hρ₀, hC₃] with n hn1 hn2
    have := hP (π n) hn1 C₃ hn2
    rw [Real.dist_eq, sub_zero]
    refine lt_of_le_of_lt this ?_
    calc ε' / (Γ + 1) * (t + 2 + 2 * C₃ + 2 * C₂) = ε' * (Γ / (Γ + 1)) := by
          rw [← hΓ]; field_simp
      _ < ε' * 1 := by
          gcongr
          rw [div_lt_one (by positivity)]; linarith
      _ = ε' := mul_one _
  have hsum := (((hA.add hBsum).add H1).add (H2.const_mul (1 / 2))).add hRem
  have hconst : Tendsto (fun _ : ℕ => f t (X t) - f 0 (X 0)) atTop
      (𝓝 ((∫ s in Set.Icc 0 t, derivWithin (fun r => f r (X s)) (Set.Icc 0 T) s) +
        (∫ s in Set.Icc 0 t, fderiv ℝ (f s) (X s) (b s)) + N + 1 / 2 * Q + 0)) := by
    refine hsum.congr fun n => ?_
    ring
  have := tendsto_nhds_unique tendsto_const_nhds hconst
  linarith

end ItoDet

/-! ### `E`-valued integrals -/

/-- `E`-valued integrands, progressive and pathwise locally square-integrable. -/
structure IsProgressiveLocL2E (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (Φ : ℝ → Ω → ι → E) :
    Prop where
  prog : IsProgressive ℱ Φ
  sq : ∀ T : ℝ, ∀ᵐ ω ∂P, ∫⁻ s in Set.Icc 0 T, ∑ k, ‖Φ s ω k‖ₑ ^ 2 < ∞

/-- `M` is the `E`-valued local Itô integral of `Φ`: for every continuous linear functional `ℓ`,
`ℓ ∘ M` is the scalar local integral of `ℓ ∘ Φ`. -/
structure IsItoIntegralE (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → ι → ℝ)
    (Φ : ℝ → Ω → ι → E) (M : ℝ → Ω → E) : Prop where
  cont : ∀ ω, Continuous fun t => M t ω
  adapted : Adapted ℱ M
  zero : ∀ t : ℝ, t ≤ 0 → ∀ ω, M t ω = 0
  functional : ∀ ℓ : E →L[ℝ] ℝ,
    IsLocalItoIntegral P ℱ W (fun s ω k => ℓ (Φ s ω k)) (fun t ω => ℓ (M t ω))

open Classical in
/-- The `E`-valued local Itô integral `t ↦ ∫_0^t Φ_s · dW_s = ∑_k ∫_0^t Φ^k_s dW^k_s`. -/
def localItoIntegralE (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → ι → ℝ)
    (Φ : ℝ → Ω → ι → E) : ℝ → Ω → E :=
  if h : ∃ M, IsItoIntegralE P ℱ W Φ M then h.choose else 0

/-- The coordinate functionals of the basis `Module.finBasis ℝ E`. -/
def coordCLM (j : Fin (Module.finrank ℝ E)) : E →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap ((Module.finBasis ℝ E).coord j)

theorem coordCLM_apply (j : Fin (Module.finrank ℝ E)) (x : E) :
    coordCLM j x = (Module.finBasis ℝ E).repr x j := rfl

theorem sum_coordCLM_smul (x : E) :
    ∑ j, coordCLM j x • (Module.finBasis ℝ E) j = x := by
  simpa [coordCLM_apply] using (Module.finBasis ℝ E).sum_repr x

theorem eq_of_coordCLM_eq {x y : E} (h : ∀ j, coordCLM j x = coordCLM j y) : x = y := by
  rw [← sum_coordCLM_smul x, ← sum_coordCLM_smul y]
  exact Finset.sum_congr rfl fun j _ => by rw [h j]

theorem clm_eq_sum_coordCLM (ℓ : E →L[ℝ] ℝ) :
    ℓ = ∑ j, ℓ ((Module.finBasis ℝ E) j) • coordCLM j := by
  ext x
  conv_lhs => rw [← sum_coordCLM_smul x]
  simp [map_sum, mul_comm]

theorem isProgressive_comp_measurable {ℱ : Filtration ℝ mΩ} {β γ : Type*} [MeasurableSpace β]
    [MeasurableSpace γ] {u : ℝ → Ω → β} (hu : IsProgressive ℱ u) {g : β → γ}
    (hg : Measurable g) : IsProgressive ℱ (fun s ω => g (u s ω)) :=
  fun i => hg.comp (hu i)

theorem IsProgressiveLocL2E.comp {P : Measure Ω} {ℱ : Filtration ℝ mΩ} {Φ : ℝ → Ω → ι → E}
    (hΦ : IsProgressiveLocL2E P ℱ Φ) (ℓ : E →L[ℝ] ℝ) :
    IsProgressiveLocL2 P ℱ (fun s ω k => ℓ (Φ s ω k)) := by
  refine ⟨?_, fun T => ?_⟩
  · exact isProgressive_comp_measurable hΦ.prog (g := fun v : ι → E => fun k => ℓ (v k))
      (measurable_pi_iff.2 fun k => ℓ.continuous.measurable.comp (measurable_pi_apply k))
  · filter_upwards [hΦ.sq T] with ω hω
    calc ∫⁻ s in Set.Icc 0 T, ∑ k, ‖ℓ (Φ s ω k)‖ₑ ^ 2
        ≤ ∫⁻ s in Set.Icc 0 T, ‖ℓ‖ₑ ^ 2 * ∑ k, ‖Φ s ω k‖ₑ ^ 2 := by
          refine lintegral_mono fun s => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun k _ => ?_
          calc ‖ℓ (Φ s ω k)‖ₑ ^ 2 ≤ (‖ℓ‖ₑ * ‖Φ s ω k‖ₑ) ^ 2 := by
                gcongr; exact ℓ.le_opENorm _
            _ = ‖ℓ‖ₑ ^ 2 * ‖Φ s ω k‖ₑ ^ 2 := by ring
      _ = ‖ℓ‖ₑ ^ 2 * ∫⁻ s in Set.Icc 0 T, ∑ k, ‖Φ s ω k‖ₑ ^ 2 := by
          rw [lintegral_const_mul' _ _ (by simp)]
      _ < ∞ := ENNReal.mul_lt_top (by simp) hω


section VectorIntegral

variable {P : Measure Ω} {ℱ : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ι → ℝ} {Φ : ℝ → Ω → ι → E}

/-- A process indistinguishable from a local integral (and continuous, adapted, zero on the
negative axis) is again a local integral. -/
theorem IsLocalItoIntegral.congr_ae {Φ' : ℝ → Ω → ι → ℝ} {M M' : ℝ → Ω → ℝ}
    (hM : IsLocalItoIntegral P ℱ W Φ' M) (hc : ∀ ω, Continuous fun t => M' t ω)
    (had : Adapted ℱ M') (hz : ∀ t : ℝ, t ≤ 0 → ∀ ω, M' t ω = 0)
    (hae : ∀ᵐ ω ∂P, ∀ t, M t ω = M' t ω) : IsLocalItoIntegral P ℱ W Φ' M' := by
  refine ⟨hc, had, hz, fun τ hτ hτ2 => ?_⟩
  filter_upwards [hM.stopped τ hτ hτ2, hae] with ω h1 h2 t
  rw [← h1 t]
  unfold stoppedProcess
  rw [h2]

/-- The scalar local integral of `ℓ ∘ Φ`. -/
abbrev Lint (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → ι → ℝ) (Φ : ℝ → Ω → ι → E)
    (ℓ : E →L[ℝ] ℝ) : ℝ → Ω → ℝ :=
  localItoIntegral P ℱ W (fun s ω k => ℓ (Φ s ω k))

theorem Lint_add [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveLocL2E P ℱ Φ) (ℓ₁ ℓ₂ : E →L[ℝ] ℝ) :
    ∀ᵐ ω ∂P, ∀ t, Lint P ℱ W Φ (ℓ₁ + ℓ₂) t ω = Lint P ℱ W Φ ℓ₁ t ω + Lint P ℱ W Φ ℓ₂ t ω := by
  have := localItoIntegral_add hW (hΦ.comp ℓ₁) (hΦ.comp ℓ₂)
  have e : (fun s ω k => (ℓ₁ + ℓ₂) (Φ s ω k)) =
      fun s ω => (fun k => ℓ₁ (Φ s ω k)) + fun k => ℓ₂ (Φ s ω k) := by
    funext s ω k; simp
  simp only [Lint]
  rw [e]
  exact this

theorem Lint_smul [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveLocL2E P ℱ Φ) (c : ℝ) (ℓ : E →L[ℝ] ℝ) :
    ∀ᵐ ω ∂P, ∀ t, Lint P ℱ W Φ (c • ℓ) t ω = c * Lint P ℱ W Φ ℓ t ω := by
  have := localItoIntegral_smul hW (hΦ.comp ℓ) c
  have e : (fun s ω k => (c • ℓ) (Φ s ω k)) = fun s ω => c • (fun k => ℓ (Φ s ω k)) := by
    funext s ω k; simp
  simp only [Lint]
  rw [e]
  exact this

theorem Lint_zero [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveLocL2E P ℱ Φ) :
    ∀ᵐ ω ∂P, ∀ t, Lint P ℱ W Φ 0 t ω = 0 := by
  filter_upwards [Lint_smul hW hΦ 0 0] with ω h t
  have e : (0 : ℝ) • (0 : E →L[ℝ] ℝ) = 0 := zero_smul _ _
  rw [e] at h
  rw [h t]; simp

theorem Lint_sum [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveLocL2E P ℱ Φ) {κ : Type*} (S : Finset κ) (c : κ → ℝ)
    (ℓ : κ → E →L[ℝ] ℝ) :
    ∀ᵐ ω ∂P, ∀ t, Lint P ℱ W Φ (∑ j ∈ S, c j • ℓ j) t ω =
      ∑ j ∈ S, c j * Lint P ℱ W Φ (ℓ j) t ω := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Lint_zero hW hΦ
  | insert a S ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [ih, Lint_add hW hΦ (c a • ℓ a) (∑ j ∈ S, c j • ℓ j), Lint_smul hW hΦ (c a) (ℓ a)]
      with ω h1 h2 h3 t
    rw [Finset.sum_insert ha, h2 t, h1 t, h3 t]


theorem Lint_eq_sum [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveLocL2E P ℱ Φ) (ℓ : E →L[ℝ] ℝ) :
    ∀ᵐ ω ∂P, ∀ t, Lint P ℱ W Φ ℓ t ω =
      ∑ j, ℓ ((Module.finBasis ℝ E) j) * Lint P ℱ W Φ (coordCLM j) t ω := by
  have := Lint_sum hW hΦ Finset.univ (fun j => ℓ ((Module.finBasis ℝ E) j)) (fun j => coordCLM j)
  rw [← clm_eq_sum_coordCLM ℓ] at this
  exact this

theorem IsItoIntegralE.ae_eq_forall' [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveLocL2E P ℱ Φ) {M M' : ℝ → Ω → E} (hM : IsItoIntegralE P ℱ W Φ M)
    (hM' : IsItoIntegralE P ℱ W Φ M') : ∀ᵐ ω ∂P, ∀ t, M t ω = M' t ω := by
  have h : ∀ j, ∀ᵐ ω ∂P, ∀ t, coordCLM j (M t ω) = coordCLM j (M' t ω) := fun j =>
    IsLocalItoIntegral.ae_eq_forall hW (hΦ.comp (coordCLM j)) (hM.functional (coordCLM j))
      (hM'.functional (coordCLM j))
  filter_upwards [ae_all_iff.2 h] with ω hω t
  exact eq_of_coordCLM_eq fun j => hω j t

theorem exists_isItoIntegralE [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveLocL2E P ℱ Φ) : ∃ M, IsItoIntegralE P ℱ W Φ M := by
  refine ⟨fun t ω => ∑ j, Lint P ℱ W Φ (coordCLM j) t ω • (Module.finBasis ℝ E) j, ?_, ?_, ?_, ?_⟩
  · intro ω
    exact continuous_finsetSum _ fun j _ =>
      (continuous_localItoIntegral P ℱ W _ ω).smul continuous_const
  · intro t
    exact Finset.measurable_sum _ fun j _ =>
      ((adapted_localItoIntegral P ℱ W _ t)).smul_const _
  · intro t ht ω
    simp [localItoIntegral_of_nonpos P ℱ W _ ht]
  · intro ℓ
    refine IsLocalItoIntegral.congr_ae (isLocalItoIntegral_localItoIntegral hW (hΦ.comp ℓ)) ?_ ?_ ?_ ?_
    · intro ω
      simp only [map_sum, map_smul, smul_eq_mul]
      exact continuous_finsetSum _ fun j _ =>
        (continuous_localItoIntegral P ℱ W _ ω).mul continuous_const
    · intro t
      simp only [map_sum, map_smul, smul_eq_mul]
      exact Finset.measurable_sum _ fun j _ =>
        ((adapted_localItoIntegral P ℱ W _ t)).mul_const _
    · intro t ht ω
      simp [localItoIntegral_of_nonpos P ℱ W _ ht]
    · filter_upwards [Lint_eq_sum hW hΦ ℓ] with ω hω t
      simp only [map_sum, map_smul, smul_eq_mul]
      refine (hω t).trans ?_
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _


theorem isItoIntegralE_localItoIntegralE [IsProbabilityMeasure P]
    (hW : IsBrownianFiltration P ℱ W) (hΦ : IsProgressiveLocL2E P ℱ Φ) :
    IsItoIntegralE P ℱ W Φ (localItoIntegralE P ℱ W Φ) := by
  unfold localItoIntegralE
  split_ifs with h
  · exact h.choose_spec
  · exact absurd (exists_isItoIntegralE hW hΦ) h

theorem continuous_localItoIntegralE (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → ι → ℝ)
    (Φ : ℝ → Ω → ι → E) (ω : Ω) : Continuous fun t => localItoIntegralE P ℱ W Φ t ω := by
  unfold localItoIntegralE
  split_ifs with h
  · exact h.choose_spec.cont ω
  · exact continuous_const

theorem adapted_localItoIntegralE (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → ι → ℝ)
    (Φ : ℝ → Ω → ι → E) : Adapted ℱ (localItoIntegralE P ℱ W Φ) := by
  unfold localItoIntegralE
  split_ifs with h
  · exact h.choose_spec.adapted
  · exact fun t => measurable_const

theorem localItoIntegralE_of_nonpos (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → ι → ℝ)
    (Φ : ℝ → Ω → ι → E) {t : ℝ} (ht : t ≤ 0) (ω : Ω) : localItoIntegralE P ℱ W Φ t ω = 0 := by
  unfold localItoIntegralE
  split_ifs with h
  · exact h.choose_spec.zero t ht ω
  · rfl

/-- Functionals of the vector integral are scalar integrals. -/
theorem localItoIntegralE_apply [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveLocL2E P ℱ Φ) (ℓ : E →L[ℝ] ℝ) :
    ∀ᵐ ω ∂P, ∀ t, ℓ (localItoIntegralE P ℱ W Φ t ω) =
      localItoIntegral P ℱ W (fun s ω k => ℓ (Φ s ω k)) t ω :=
  IsLocalItoIntegral.ae_eq_forall hW (hΦ.comp ℓ)
    ((isItoIntegralE_localItoIntegralE hW hΦ).functional ℓ)
    (isLocalItoIntegral_localItoIntegral hW (hΦ.comp ℓ))

/-- The integral of a constant `σ : ι → E` is `∑_k W^k_t • σ_k`: additive noise. -/
theorem localItoIntegralE_const [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (σ : ι → E) :
    ∀ᵐ ω ∂P, ∀ t, localItoIntegralE P ℱ W (fun _ _ => σ) t ω =
      ∑ k, ofNNRealTime W t ω k • σ k := by
  have hΦ : IsProgressiveLocL2E P ℱ (fun _ _ => σ) := by
    refine ⟨isProgressive_const ℱ σ, fun T => ae_of_all _ fun ω => ?_⟩
    rw [lintegral_const]
    exact ENNReal.mul_lt_top (by simp) (by simp)
  have h : ∀ j, ∀ᵐ ω ∂P, ∀ t, coordCLM j (localItoIntegralE P ℱ W (fun _ _ => σ) t ω) =
      coordCLM j (∑ k, ofNNRealTime W t ω k • σ k) := by
    intro j
    filter_upwards [localItoIntegralE_apply hW hΦ (coordCLM j),
      localItoIntegral_eq_itoIntegral hW (IsProgressiveL2.const P ℱ (fun k => coordCLM j (σ k))),
      itoIntegral_const hW (fun k => coordCLM j (σ k))] with ω h1 h2 h3 t
    rw [h1 t]
    have e : localItoIntegral P ℱ W (fun s ω k => coordCLM j ((fun (_ : ℝ) (_ : Ω) => σ) s ω k)) t ω
        = itoIntegral P ℱ W (fun (_ : ℝ) (_ : Ω) => fun k => coordCLM j (σ k)) t ω := h2 t
    rw [e, h3 t]
    simp [map_sum, mul_comm]
  filter_upwards [ae_all_iff.2 h] with ω hω t
  exact eq_of_coordCLM_eq fun j => hω j t

/-- In `ℝ^m` the vector integral is the vector of coordinate integrals. -/
theorem localItoIntegralE_euclidean [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    {m : ℕ} (Φ : ℝ → Ω → ι → EuclideanSpace ℝ (Fin m)) (hΦ : IsProgressiveLocL2E P ℱ Φ)
    (a : Fin m) :
    ∀ᵐ ω ∂P, ∀ t, localItoIntegralE P ℱ W Φ t ω a =
      localItoIntegral P ℱ W (fun s ω k => Φ s ω k a) t ω :=
  localItoIntegralE_apply hW hΦ (EuclideanSpace.proj a)

end VectorIntegral

/-! ### Itô processes -/

/-- Drifts: progressive and pathwise locally integrable. -/
structure IsProgressiveLocL1 (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (b : ℝ → Ω → E) : Prop where
  prog : IsProgressive ℱ b
  int : ∀ T : ℝ, ∀ᵐ ω ∂P, IntegrableOn (fun s => b s ω) (Set.Icc 0 T)

/-- The Itô process `X_t = X₀ + ∫_0^t b_s ds + ∫_0^t Φ_s · dW_s` (equal to `X₀` for `t ≤ 0`). -/
def itoProcess (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → ι → ℝ) (X₀ : Ω → E)
    (b : ℝ → Ω → E) (Φ : ℝ → Ω → ι → E) : ℝ → Ω → E :=
  fun t ω => X₀ ω + (∫ s in Set.Icc 0 t, b s ω) + localItoIntegralE P ℱ W Φ t ω

section ItoProcess

variable {P : Measure Ω} {ℱ : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ι → ℝ}

theorem measurable_progressive_min_gen {β : Type*} [MeasurableSpace β] {u : ℝ → Ω → β}
    (hu : IsProgressive ℱ u) (T : ℝ) : Measurable fun x : ℝ × Ω => u (min x.1 T) x.2 := by
  have hq : Measurable[Prod.instMeasurableSpace, Subtype.instMeasurableSpace.prod (ℱ T)]
      fun x : ℝ × Ω => ((⟨min x.1 T, Set.mem_Iic.2 (min_le_right _ _)⟩ : Set.Iic T), x.2) :=
    Measurable.prodMk (Measurable.subtype_mk (measurable_fst.min measurable_const))
      (measurable_snd.mono le_rfl (ℱ.le T))
  exact (hu T).comp hq

theorem isProgressive_driftIntegral {b : ℝ → Ω → E} (hb : IsProgressive ℱ b) :
    IsProgressive ℱ (fun t ω => ∫ s in Set.Icc 0 t, b s ω) := by
  intro i
  let mS : MeasurableSpace (Set.Iic i × Ω) := Subtype.instMeasurableSpace.prod (ℱ i)
  have hset : MeasurableSet {q : (Set.Iic i × Ω) × ℝ | 0 ≤ q.2 ∧ q.2 ≤ ((q.1.1 : Set.Iic i) : ℝ)} := by
    refine MeasurableSet.inter ?_ ?_
    · exact measurableSet_le measurable_const measurable_snd
    · exact measurableSet_le measurable_snd ((measurable_subtype_coe).comp (measurable_fst.comp measurable_fst))
  have hq : Measurable (fun q : (Set.Iic i × Ω) × ℝ =>
      ((⟨min q.2 i, Set.mem_Iic.2 (min_le_right _ _)⟩ : Set.Iic i), q.1.2)) :=
    Measurable.prodMk (Measurable.subtype_mk (measurable_snd.min measurable_const))
      (measurable_snd.comp measurable_fst)
  have hF : Measurable (fun q : (Set.Iic i × Ω) × ℝ => b (min q.2 i) q.1.2) := (hb i).comp hq
  have hG : StronglyMeasurable (Function.uncurry fun (p : Set.Iic i × Ω) (s : ℝ) =>
      Set.indicator {q : (Set.Iic i × Ω) × ℝ | 0 ≤ q.2 ∧ q.2 ≤ ((q.1.1 : Set.Iic i) : ℝ)}
        (fun q => b (min q.2 i) q.1.2) (p, s)) :=
    (hF.indicator hset).stronglyMeasurable
  have := (hG.integral_prod_right (ν := (volume : Measure ℝ))).measurable
  convert this using 1
  funext p
  show ∫ s in Set.Icc 0 (p.1 : ℝ), b s p.2 = _
  rw [← integral_indicator measurableSet_Icc]
  refine integral_congr_ae (ae_of_all _ fun s => ?_)
  simp only [Set.indicator, Set.mem_Icc, Set.mem_setOf_eq, Function.uncurry]
  by_cases h : 0 ≤ s ∧ s ≤ (p.1 : ℝ)
  · rw [if_pos h, if_pos h, min_eq_left (h.2.trans p.1.2)]
  · rw [if_neg h, if_neg h]


theorem continuous_driftIntegral {b : ℝ → E} (hb : ∀ N : ℕ, IntegrableOn b (Set.Icc 0 (N : ℝ))) :
    Continuous fun t : ℝ => ∫ s in Set.Icc 0 t, b s := by
  set b' : ℝ → E := Set.indicator (Set.Ioi 0) b with hb'
  have hint : ∀ x y : ℝ, IntervalIntegrable b' volume x y := by
    intro x y
    obtain ⟨N, hN⟩ := exists_nat_ge (max |x| |y|)
    have hg : Integrable (Set.indicator (Set.Ioc 0 (N : ℝ)) b) volume :=
      (integrable_indicator_iff measurableSet_Ioc).2 ((hb N).mono_set Set.Ioc_subset_Icc_self)
    have hsub : Set.uIoc x y ⊆ Set.Icc (-(N : ℝ)) N := by
      intro z hz
      have h1 : |x| ≤ N := (le_max_left _ _).trans hN
      have h2 : |y| ≤ N := (le_max_right _ _).trans hN
      rw [Set.mem_uIoc] at hz
      rw [abs_le] at h1 h2
      constructor <;> rcases hz with hz | hz <;> linarith [hz.1, hz.2]
    rw [intervalIntegrable_iff]
    refine (hg.integrableOn (s := Set.uIoc x y)).congr_fun ?_ measurableSet_uIoc
    intro z hz
    have hz' := hsub hz
    simp only [hb', Set.indicator, Set.mem_Ioi, Set.mem_Ioc]
    by_cases h0 : 0 < z
    · rw [if_pos h0, if_pos ⟨h0, hz'.2⟩]
    · rw [if_neg h0, if_neg (fun h => h0 h.1)]
  have key : ∀ t : ℝ, (∫ s in Set.Icc 0 t, b s) = ∫ s in (0:ℝ)..t, b' s := by
    intro t
    rcases le_or_gt 0 t with ht | ht
    · rw [intervalIntegral.integral_of_le ht, integral_Icc_eq_integral_Ioc]
      refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
      simp [hb', hs.1]
    · rw [Set.Icc_eq_empty (not_le.2 ht), Measure.restrict_empty, integral_zero_measure,
        intervalIntegral.integral_of_ge ht.le]
      rw [setIntegral_eq_zero_of_forall_eq_zero, neg_zero]
      intro s hs
      simp [hb', not_lt.2 hs.2]
  simp_rw [key]
  exact intervalIntegral.continuous_primitive hint 0


theorem itoProcess_zero (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → ι → ℝ) (X₀ : Ω → E)
    (b : ℝ → Ω → E) (Φ : ℝ → Ω → ι → E) (ω : Ω) : itoProcess P ℱ W X₀ b Φ 0 ω = X₀ ω := by
  simp [itoProcess, localItoIntegralE_of_nonpos P ℱ W Φ (le_refl (0:ℝ))]

theorem isProgressive_itoProcess (X₀ : Ω → E) (hX₀ : ∀ t : ℝ, Measurable[ℱ t] X₀) (b : ℝ → Ω → E)
    (hb : IsProgressive ℱ b) (Φ : ℝ → Ω → ι → E) :
    IsProgressive ℱ (itoProcess P ℱ W X₀ b Φ) := by
  have h1 : IsProgressive ℱ (fun (_ : ℝ) ω => X₀ ω) := fun i => (hX₀ i).comp measurable_snd
  have h3 : IsProgressive ℱ (localItoIntegralE P ℱ W Φ) :=
    (StronglyAdapted.isStronglyProgressive_of_continuous
      (fun t => (adapted_localItoIntegralE P ℱ W Φ t).stronglyMeasurable)
      (fun ω => continuous_localItoIntegralE P ℱ W Φ ω)).isProgressive
  exact (h1.add (isProgressive_driftIntegral hb)).add h3

theorem adapted_itoProcess (X₀ : Ω → E) (hX₀ : ∀ t : ℝ, Measurable[ℱ t] X₀) (b : ℝ → Ω → E)
    (hb : IsProgressive ℱ b) (Φ : ℝ → Ω → ι → E) : Adapted ℱ (itoProcess P ℱ W X₀ b Φ) :=
  (isProgressive_itoProcess X₀ hX₀ b hb Φ).adapted

theorem continuous_itoProcess (X₀ : Ω → E) (b : ℝ → Ω → E) (hb : IsProgressiveLocL1 P ℱ b)
    (Φ : ℝ → Ω → ι → E) : ∀ᵐ ω ∂P, Continuous fun t => itoProcess P ℱ W X₀ b Φ t ω := by
  filter_upwards [ae_all_iff.2 (fun N : ℕ => hb.int N)] with ω hω
  exact (continuous_const.add (continuous_driftIntegral hω)).add
    (continuous_localItoIntegralE P ℱ W Φ ω)

end ItoProcess

/-! ### Probabilistic tools for Itô's formula (weighted quadratic variation, step sums) -/

section CommonSubsequence

variable {P : Measure Ω}

/-- Countably many sequences converging in measure have a common subsequence converging a.e. -/
theorem exists_subseq_ae_countable {κ : Type*} [Countable κ] {Y : κ → ℕ → Ω → ℝ}
    {y : κ → Ω → ℝ} (h : ∀ c, TendstoInMeasure P (Y c) atTop (y c)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ c, ∀ᵐ ω ∂P, Tendsto (fun n => Y c (φ n) ω) atTop (𝓝 (y c ω)) := by
  obtain ⟨e, he⟩ := Countable.exists_injective_nat κ
  have key : ∀ n : ℕ, ∀ᶠ k in atTop, ∀ c, e c ≤ n →
      P {ω | (2 : ℝ≥0∞)⁻¹ ^ n ≤ edist (Y c k ω) (y c ω)} ≤ (2 : ℝ≥0∞)⁻¹ ^ n := by
    intro n
    have hfin : {c | e c ≤ n}.Finite := (Set.finite_Iic n).preimage he.injOn
    have := (Filter.eventually_all_finite hfin (l := atTop)
      (p := fun c k => P {ω | (2 : ℝ≥0∞)⁻¹ ^ n ≤ edist (Y c k ω) (y c ω)} ≤ (2 : ℝ≥0∞)⁻¹ ^ n)).2 ?_
    · filter_upwards [this] with k hk c hc using hk c hc
    · intro c _
      have hc := h c ((2 : ℝ≥0∞)⁻¹ ^ n) (ENNReal.pow_pos (by simp) _)
      rw [ENNReal.tendsto_atTop_zero] at hc
      obtain ⟨N, hN⟩ := hc ((2 : ℝ≥0∞)⁻¹ ^ n) (pos_iff_ne_zero.mpr <| pow_ne_zero _ <| by simp)
      exact eventually_atTop.2 ⟨N, hN⟩
  obtain ⟨φ, hφ, hφn⟩ := Filter.extraction_forall_of_eventually key
  refine ⟨φ, hφ, fun c => ?_⟩
  classical
  set S : ℕ → Set Ω := fun n => if e c ≤ n then
    {ω | (2 : ℝ≥0∞)⁻¹ ^ n ≤ edist (Y c (φ n) ω) (y c ω)} else ∅ with hS
  have hμS : ∀ n, P (S n) ≤ (2 : ℝ≥0∞)⁻¹ ^ n := by
    intro n
    by_cases hn : e c ≤ n
    · simp only [hS, hn, if_true]; exact hφn n c hn
    · simp [hS, hn]
  have hμs : P (limsup S atTop) = 0 := by
    refine measure_limsup_atTop_eq_zero (ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hμS))
    simpa only [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv] using ENNReal.ofNat_ne_top
  have h_lt : ∀ ε : ℝ≥0∞, 0 < ε → ∃ k : ℕ, 2 * (2 : ℝ≥0∞)⁻¹ ^ k < ε := by
    intro ε hε
    obtain ⟨k, h_k⟩ : ∃ k : ℕ, (2 : ℝ≥0∞)⁻¹ ^ k < ε := ENNReal.exists_inv_two_pow_lt hε.ne'
    refine ⟨k + 1, lt_of_eq_of_lt ?_ h_k⟩
    rw [pow_succ', ← mul_assoc, ENNReal.mul_inv_cancel, one_mul]
    · positivity
    · simp
  have hae : ∀ᵐ ω ∂P, ω ∉ limsup S atTop := by
    rw [ae_iff]; simpa using hμs
  filter_upwards [hae] with ω hω
  refine EMetric.tendsto_atTop.mpr fun ε hε => ?_
  rw [limsup_eq_iInf_iSup_of_nat] at hω
  simp only [Set.iSup_eq_iUnion, Set.iInf_eq_iInter, Set.mem_iInter, Set.mem_iUnion,
    not_forall, not_exists] at hω
  obtain ⟨N, hNx⟩ := hω
  obtain ⟨k, hk_lt⟩ := h_lt ε hε
  refine ⟨max (max N (e c)) (k - 1), fun n hn => lt_of_le_of_lt ?_ hk_lt⟩
  have hn1 : N ≤ n := (le_max_left _ _).trans ((le_max_left _ _).trans hn)
  have hn2 : e c ≤ n := (le_max_right _ _).trans ((le_max_left _ _).trans hn)
  have hn3 : k - 1 ≤ n := (le_max_right _ _).trans hn
  have := hNx n hn1
  simp only [hS, hn2, if_true, Set.mem_ofPred_eq, not_le] at this
  refine this.le.trans ?_
  nth_rw 2 [← pow_one (2 : ℝ≥0∞)]
  rw [mul_comm, ← ENNReal.inv_pow, ← ENNReal.inv_pow, ENNReal.inv_le_iff_le_mul, ← mul_assoc,
    mul_comm (_ ^ n), mul_assoc, ← ENNReal.inv_le_iff_le_mul, inv_inv, ← pow_add]
  · gcongr
    · simp
    · omega
  all_goals simp

end CommonSubsequence


section WeightedQV

/-- The dyadic point `k t / 2^m`. -/
def rr (t : ℝ) (m k : ℕ) : ℝ := (k : ℝ) * (t / 2 ^ m)

theorem rr_mono {t : ℝ} (ht : 0 ≤ t) (m : ℕ) : Monotone (rr t m) := by
  intro k l hkl
  unfold rr
  have : (0:ℝ) ≤ t / 2 ^ m := by positivity
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hkl) this

theorem dyadic_pt (t : ℝ) (ht : 0 ≤ t) (m : ℕ) (i : Fin (2 ^ m + 1)) :
    (Partition.dyadic 0 t ht m).pt i = rr t m i := by
  simp [Partition.dyadic, rr]

theorem rr_pow {t : ℝ} (m d k : ℕ) : rr t (m + d) (k * 2 ^ d) = rr t m k := by
  unfold rr
  push_cast
  rw [pow_add]
  field_simp

/-- Alignment of fine dyadic points with coarse dyadic blocks. -/
theorem dyadic_align {t : ℝ} (ht : 0 ≤ t) {m N : ℕ} (hmN : m ≤ N) (i : ℕ) (hi : i < 2 ^ N) :
    ∃ k : ℕ, k < 2 ^ m ∧ rr t m k ≤ rr t N i ∧ rr t N (i + 1) ≤ rr t m (k + 1) ∧
      ∀ k' : ℕ, k' < 2 ^ m → k' ≠ k → rr t m (k' + 1) ≤ rr t N i ∨ rr t N (i + 1) ≤ rr t m k' := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmN
  have hd : 0 < 2 ^ d := by positivity
  refine ⟨i / 2 ^ d, ?_, ?_, ?_, ?_⟩
  · rw [Nat.div_lt_iff_lt_mul hd, ← pow_add]; exact hi
  · rw [← rr_pow m d]
    exact rr_mono ht _ (Nat.div_mul_le_self i (2 ^ d))
  · rw [← rr_pow m d]
    exact rr_mono ht _ (by
      have := Nat.lt_mul_div_succ i hd
      rw [mul_comm] at this
      exact Nat.succ_le_of_lt this)
  · intro k' hk' hne
    rcases lt_or_gt_of_ne hne with h | h
    · left
      refine (rr_mono ht m (Nat.succ_le_of_lt h)).trans ?_
      rw [← rr_pow m d]
      exact rr_mono ht _ (Nat.div_mul_le_self i (2 ^ d))
    · right
      refine le_trans ?_ (rr_mono ht m (Nat.succ_le_of_lt h))
      rw [← rr_pow m d]
      exact rr_mono ht _ (by
        have := Nat.lt_mul_div_succ i hd
        rw [mul_comm] at this
        exact Nat.succ_le_of_lt this)


theorem dyadic_sumIncrements {t : ℝ} (ht : 0 ≤ t) (N : ℕ) (g : ℝ → ℝ → ℝ) :
    (Partition.dyadic 0 t ht N).sumIncrements g =
      ∑ i ∈ Finset.range (2 ^ N), g (rr t N i) (rr t N (i + 1)) := by
  unfold Partition.sumIncrements
  rw [← Fin.sum_univ_eq_sum_range (fun i => g (rr t N i) (rr t N (i + 1))) (2 ^ N)]
  refine Finset.sum_congr rfl fun (i : Fin (2 ^ N)) _ => ?_
  have h1 := dyadic_pt t ht N i.castSucc
  have h2 := dyadic_pt t ht N i.succ
  simp only [Fin.val_castSucc, Fin.val_succ] at h1 h2
  exact congrArg₂ g h1 h2

theorem rr_succ (t : ℝ) (m k : ℕ) : rr t m (k + 1) = rr t m k + t / 2 ^ m := by
  unfold rr; push_cast; ring

/-- The increment process of `u` over the block `(r, r']`. -/
def blkProc (u : ℝ → ℝ) (r r' x : ℝ) : ℝ := u (min x r') - u (min x r)

theorem blkProc_in {u : ℝ → ℝ} {r r' s s' : ℝ} (h1 : r ≤ s) (h2 : s ≤ s') (h3 : s' ≤ r') :
    blkProc u r r' s' - blkProc u r r' s = u s' - u s := by
  unfold blkProc
  rw [min_eq_left h3, min_eq_right (h1.trans h2), min_eq_left (h2.trans h3), min_eq_right h1]
  ring

theorem blkProc_out {u : ℝ → ℝ} {r r' s s' : ℝ} (hrr : r ≤ r') (h2 : s ≤ s')
    (h : r' ≤ s ∨ s' ≤ r) :
    blkProc u r r' s' - blkProc u r r' s = 0 := by
  unfold blkProc
  rcases h with h | h
  · rw [min_eq_right h, min_eq_right (hrr.trans h), min_eq_right (h.trans h2),
      min_eq_right (hrr.trans (h.trans h2))]
    ring
  · have a1 : min s' r' = s' := min_eq_left (h.trans hrr)
    have a2 : min s' r = s' := min_eq_left h
    have a3 : min s r' = s := min_eq_left (h2.trans (h.trans hrr))
    have a4 : min s r = s := min_eq_left (h2.trans h)
    rw [a1, a2, a3, a4]; ring


theorem block_collapse {t : ℝ} (ht : 0 ≤ t) {m N : ℕ} (hmN : m ≤ N) (A u v : ℝ → ℝ) (i : ℕ)
    (hi : i < 2 ^ N) :
    ∃ k, k < 2 ^ m ∧ rr t m k ≤ rr t N i ∧ rr t N i ≤ rr t m k + t / 2 ^ m ∧
      ∑ k' ∈ Finset.range (2 ^ m), A (rr t m k') *
        ((blkProc u (rr t m k') (rr t m (k' + 1)) (rr t N (i + 1)) -
            blkProc u (rr t m k') (rr t m (k' + 1)) (rr t N i)) *
         (blkProc v (rr t m k') (rr t m (k' + 1)) (rr t N (i + 1)) -
            blkProc v (rr t m k') (rr t m (k' + 1)) (rr t N i))) =
      A (rr t m k) * ((u (rr t N (i + 1)) - u (rr t N i)) * (v (rr t N (i + 1)) - v (rr t N i))) := by
  obtain ⟨k, hk, h1, h2, h3⟩ := dyadic_align ht hmN i hi
  have hle : rr t N i ≤ rr t N (i + 1) := rr_mono ht N (Nat.le_succ i)
  refine ⟨k, hk, h1, ?_, ?_⟩
  · have := h2; rw [rr_succ t m k] at this
    exact (rr_mono ht N (Nat.le_succ i)).trans this
  · rw [Finset.sum_eq_single k]
    · rw [blkProc_in h1 hle h2, blkProc_in h1 hle h2]
    · intro k' hk' hne
      have := h3 k' (Finset.mem_range.1 hk') hne
      rw [blkProc_out (rr_mono ht m (Nat.le_succ k')) hle (by tauto)]
      ring
    · intro h; exact absurd (Finset.mem_range.2 hk) h


theorem rr_mem {t : ℝ} (ht : 0 ≤ t) (N i : ℕ) (hi : i ≤ 2 ^ N) : rr t N i ∈ Set.Icc (0 : ℝ) t := by
  refine ⟨?_, ?_⟩
  · unfold rr; positivity
  · have : rr t N i ≤ rr t N (2 ^ N) := rr_mono ht N hi
    have h2 : rr t N (2 ^ N) = t := by unfold rr; push_cast; field_simp
    linarith

theorem weighted_err {t : ℝ} (ht : 0 ≤ t) {A u v : ℝ → ℝ} {ε' : ℝ} {m N : ℕ} (hmN : m ≤ N)
    (hmod : ∀ x ∈ Set.Icc (0 : ℝ) t, ∀ y ∈ Set.Icc (0 : ℝ) t, |x - y| ≤ t / 2 ^ m →
      |A x - A y| ≤ ε') :
    |(Partition.dyadic 0 t ht N).sumIncrements (fun s s' => A s * ((u s' - u s) * (v s' - v s))) -
      ∑ k ∈ Finset.range (2 ^ m), A (rr t m k) * (Partition.dyadic 0 t ht N).sumIncrements
        (fun s s' => (blkProc u (rr t m k) (rr t m (k + 1)) s' -
              blkProc u (rr t m k) (rr t m (k + 1)) s) *
            (blkProc v (rr t m k) (rr t m (k + 1)) s' -
              blkProc v (rr t m k) (rr t m (k + 1)) s))| ≤
    ε' * (Partition.dyadic 0 t ht N).sumIncrements (fun s s' => |u s' - u s| * |v s' - v s|) := by
  simp only [dyadic_sumIncrements, Finset.mul_sum]
  rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i < 2 ^ N := Finset.mem_range.1 hi
  obtain ⟨k, hk, h1, h2, h3⟩ := block_collapse ht hmN A u v i hi'
  rw [h3, ← sub_mul, abs_mul, ← mul_assoc, abs_mul]
  have hx := rr_mem ht N i hi'.le
  have hy := rr_mem ht m k (by have : k ≤ 2 ^ m := hk.le; exact this)
  have : |A (rr t N i) - A (rr t m k)| ≤ ε' := by
    refine hmod _ hx _ hy ?_
    rw [abs_le]; constructor <;> linarith
  calc |A (rr t N i) - A (rr t m k)| * (|u (rr t N (i + 1)) - u (rr t N i)| * |v (rr t N (i + 1)) - v (rr t N i)|)
      ≤ ε' * (|u (rr t N (i + 1)) - u (rr t N i)| * |v (rr t N (i + 1)) - v (rr t N i)|) := by
        gcongr
    _ = _ := by ring


/-- Deterministic weighted quadratic covariation along dyadic partitions. -/
theorem weighted_qv_det {t : ℝ} (ht : 0 ≤ t) {A : ℝ → ℝ} (hA : ContinuousOn A (Set.Icc 0 t))
    {u v g : ℝ → ℝ} (hg : IntegrableOn g (Set.Icc 0 t)) {C : ℝ}
    (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop)
    (hB : ∀ m, ∀ k : ℕ, k < 2 ^ m →
      Tendsto (fun N => (Partition.dyadic 0 t ht (φ N)).sumIncrements
        (fun s s' => (blkProc u (rr t m k) (rr t m (k + 1)) s' -
              blkProc u (rr t m k) (rr t m (k + 1)) s) *
            (blkProc v (rr t m k) (rr t m (k + 1)) s' -
              blkProc v (rr t m k) (rr t m (k + 1)) s))) atTop
        (𝓝 (∫ s in Set.Ioc (rr t m k) (rr t m (k + 1)), g s)))
    (hCu : ∀ᶠ N in atTop, (Partition.dyadic 0 t ht (φ N)).sumIncrements (fun s s' => (u s' - u s) ^ 2) ≤ C)
    (hCv : ∀ᶠ N in atTop, (Partition.dyadic 0 t ht (φ N)).sumIncrements (fun s s' => (v s' - v s) ^ 2) ≤ C) :
    Tendsto (fun N => (Partition.dyadic 0 t ht (φ N)).sumIncrements
      (fun s s' => A s * ((u s' - u s) * (v s' - v s)))) atTop
      (𝓝 (∫ s in Set.Icc 0 t, A s * g s)) := by
  have huc : UniformContinuousOn A (Set.Icc 0 t) := isCompact_Icc.uniformContinuousOn_of_continuous hA
  have hmesh : Tendsto (fun m => (Partition.dyadic 0 t ht m).mesh) atTop (𝓝 0) := by
    simp only [Partition.mesh_dyadic, sub_zero]
    exact tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  have hH0 : IntegrableOn (fun s => A s * g s) (Set.Icc 0 t) :=
    hg.continuousOn_mul hA isCompact_Icc
  have hRiem : Tendsto (fun m => ∑ k ∈ Finset.range (2 ^ m), A (rr t m k) *
      ∫ s in Set.Ioc (rr t m k) (rr t m (k + 1)), g s) atTop (𝓝 (∫ s in Set.Icc 0 t, A s * g s)) := by
    have := riemann_sum_tendsto ht (fun m => Partition.dyadic 0 t ht m) hmesh
      (fun a s => A a * g s) (fun s => |g s|) hg.norm (fun s => abs_nonneg _) hH0
      (fun a _ => hg.const_mul _) (by
        intro ε hε
        obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.1 huc ε hε
        refine ⟨δ, hδ, fun a ha s hs _ hsa => ?_⟩
        have := hδ' a ha s hs (by rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (by linarith)]; exact hsa)
        rw [Real.dist_eq] at this
        rw [← sub_mul, abs_mul]
        exact mul_le_mul_of_nonneg_right this.le (abs_nonneg _))
    convert this using 2 with m
    have h := dyadic_sumIncrements ht m (fun a b => ∫ s in Set.Ioc a b, A a * g s)
    refine Eq.trans ?_ (h.symm.trans rfl)
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul]
  have hCnn : 0 ≤ C := by
    obtain ⟨N, hN⟩ := hCu.exists
    refine le_trans ?_ hN
    rw [dyadic_sumIncrements]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have ht2 : Tendsto (fun m : ℕ => t / 2 ^ m) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  rw [Metric.tendsto_atTop]
  intro ε hε
  set ε1 : ℝ := ε / (3 * (C + 1)) with hε1
  have hε1pos : 0 < ε1 := by positivity
  obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.1 huc ε1 hε1pos
  have hev : ∀ᶠ m : ℕ in atTop, t / 2 ^ m < δ ∧
      dist (∑ k ∈ Finset.range (2 ^ m), A (rr t m k) *
        ∫ s in Set.Ioc (rr t m k) (rr t m (k + 1)), g s) (∫ s in Set.Icc 0 t, A s * g s) < ε / 3 :=
    (ht2.eventually (gt_mem_nhds hδ)).and
      ((Metric.tendsto_nhds.1 hRiem) (ε / 3) (by positivity))
  obtain ⟨m, hm1, hm2⟩ := hev.exists
  have hT : Tendsto (fun N => ∑ k ∈ Finset.range (2 ^ m), A (rr t m k) *
      (Partition.dyadic 0 t ht (φ N)).sumIncrements
        (fun s s' => (blkProc u (rr t m k) (rr t m (k + 1)) s' -
              blkProc u (rr t m k) (rr t m (k + 1)) s) *
            (blkProc v (rr t m k) (rr t m (k + 1)) s' -
              blkProc v (rr t m k) (rr t m (k + 1)) s))) atTop
      (𝓝 (∑ k ∈ Finset.range (2 ^ m), A (rr t m k) *
        ∫ s in Set.Ioc (rr t m k) (rr t m (k + 1)), g s)) :=
    tendsto_finset_sum _ fun k hk => (hB m k (Finset.mem_range.1 hk)).const_mul _
  have hev2 : ∀ᶠ N in atTop, m ≤ φ N ∧
      (Partition.dyadic 0 t ht (φ N)).sumIncrements (fun s s' => (u s' - u s) ^ 2) ≤ C ∧
      (Partition.dyadic 0 t ht (φ N)).sumIncrements (fun s s' => (v s' - v s) ^ 2) ≤ C ∧
      dist (∑ k ∈ Finset.range (2 ^ m), A (rr t m k) *
      (Partition.dyadic 0 t ht (φ N)).sumIncrements
        (fun s s' => (blkProc u (rr t m k) (rr t m (k + 1)) s' -
              blkProc u (rr t m k) (rr t m (k + 1)) s) *
            (blkProc v (rr t m k) (rr t m (k + 1)) s' -
              blkProc v (rr t m k) (rr t m (k + 1)) s)))
        (∑ k ∈ Finset.range (2 ^ m), A (rr t m k) *
        ∫ s in Set.Ioc (rr t m k) (rr t m (k + 1)), g s) < ε / 3 :=
    (hφ.eventually (eventually_ge_atTop m)).and (hCu.and (hCv.and
      ((Metric.tendsto_nhds.1 hT) (ε / 3) (by positivity))))
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hev2
  refine ⟨N0, fun N hN => ?_⟩
  obtain ⟨hmN, hu, hv, hTN⟩ := hN0 N hN
  have hmod : ∀ x ∈ Set.Icc (0 : ℝ) t, ∀ y ∈ Set.Icc (0 : ℝ) t, |x - y| ≤ t / 2 ^ m →
      |A x - A y| ≤ ε1 := by
    intro x hx y hy hxy
    have := hδ' x hx y hy (by rw [Real.dist_eq]; exact lt_of_le_of_lt hxy hm1)
    rw [Real.dist_eq] at this
    exact this.le
  have herr := weighted_err (A := A) (u := u) (v := v) ht hmN hmod
  have hsum : (Partition.dyadic 0 t ht (φ N)).sumIncrements (fun s s' => |u s' - u s| * |v s' - v s|) ≤ C := by
    rw [dyadic_sumIncrements] at hu hv ⊢
    calc ∑ i ∈ Finset.range (2 ^ φ N), |u (rr t (φ N) (i + 1)) - u (rr t (φ N) i)| * |v (rr t (φ N) (i + 1)) - v (rr t (φ N) i)|
        ≤ ∑ i ∈ Finset.range (2 ^ φ N), ((u (rr t (φ N) (i + 1)) - u (rr t (φ N) i)) ^ 2 / 2 +
            (v (rr t (φ N) (i + 1)) - v (rr t (φ N) i)) ^ 2 / 2) := by
          refine Finset.sum_le_sum fun i _ => ?_
          nlinarith [sq_abs (u (rr t (φ N) (i + 1)) - u (rr t (φ N) i)), sq_abs (v (rr t (φ N) (i + 1)) - v (rr t (φ N) i)),
            sq_nonneg (|u (rr t (φ N) (i + 1)) - u (rr t (φ N) i)| - |v (rr t (φ N) (i + 1)) - v (rr t (φ N) i)|)]
      _ = (∑ i ∈ Finset.range (2 ^ φ N), (u (rr t (φ N) (i + 1)) - u (rr t (φ N) i)) ^ 2) / 2 +
          (∑ i ∈ Finset.range (2 ^ φ N), (v (rr t (φ N) (i + 1)) - v (rr t (φ N) i)) ^ 2) / 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_div, Finset.sum_div]
      _ ≤ C := by linarith
  have h1 : ε1 * (Partition.dyadic 0 t ht (φ N)).sumIncrements (fun s s' => |u s' - u s| * |v s' - v s|) ≤ ε / 3 := by
    calc _ ≤ ε1 * C := by gcongr
      _ ≤ ε1 * (C + 1) := by gcongr; linarith
      _ = ε / 3 := by rw [hε1]; field_simp
  rw [Real.dist_eq] at hTN hm2 ⊢
  have key : ∀ S T L I : ℝ, |S - T| ≤ ε / 3 → |T - L| < ε / 3 → |L - I| < ε / 3 → |S - I| < ε := by
    intro S T L I h1 h2 h3
    have := abs_add_three (S - T) (T - L) (L - I)
    have e : S - I = (S - T) + (T - L) + (L - I) := by ring
    rw [e]; linarith
  exact key _ _ _ _ (herr.trans h1) hTN hm2




theorem dyadic_cell {t : ℝ} (ht : 0 ≤ t) (N : ℕ) {s : ℝ} (hs0 : 0 < s) (hst : s ≤ t) :
    ∃ i, i < 2 ^ N ∧ rr t N i < s ∧ s ≤ rr t N (i + 1) := by
  have htp : 0 < t := lt_of_lt_of_le hs0 hst
  have h2 : (0 : ℝ) < 2 ^ N := by positivity
  set x : ℝ := s * 2 ^ N / t with hx
  have hx0 : 0 < x := by positivity
  have hxN : x ≤ 2 ^ N := by
    rw [hx, div_le_iff₀ htp]; nlinarith
  have hc : 0 < ⌈x⌉₊ := Nat.ceil_pos.2 hx0
  refine ⟨⌈x⌉₊ - 1, ?_, ?_, ?_⟩
  · have : ⌈x⌉₊ ≤ 2 ^ N := Nat.ceil_le.2 (by exact_mod_cast hxN)
    omega
  · have h1 := Nat.ceil_lt_add_one hx0.le
    have : ((⌈x⌉₊ - 1 : ℕ) : ℝ) = (⌈x⌉₊ : ℝ) - 1 := by
      rw [Nat.cast_sub hc]; simp
    unfold rr
    rw [this]
    have : ((⌈x⌉₊ : ℝ) - 1) < x := by linarith
    rw [hx] at this
    rw [lt_div_iff₀ htp] at this
    calc ((⌈x⌉₊ : ℝ) - 1) * (t / 2 ^ N) = ((⌈x⌉₊ : ℝ) - 1) * t / 2 ^ N := by ring
      _ < s := by rw [div_lt_iff₀ h2]; linarith
  · have h1 := Nat.le_ceil x
    have : ((⌈x⌉₊ - 1 : ℕ) + 1 : ℕ) = ⌈x⌉₊ := by omega
    unfold rr
    rw [this]
    rw [hx, div_le_iff₀ htp] at h1
    calc s = s * 2 ^ N / 2 ^ N := by field_simp
      _ ≤ (⌈x⌉₊ : ℝ) * t / 2 ^ N := by gcongr
      _ = (⌈x⌉₊ : ℝ) * (t / 2 ^ N) := by ring

theorem sum_indicator_cell {t : ℝ} (ht : 0 ≤ t) (N : ℕ) {s : ℝ} (hs0 : 0 < s) (hst : s ≤ t)
    (x : ℕ → ℝ) :
    ∃ i, i < 2 ^ N ∧ rr t N i < s ∧ s ≤ rr t N (i + 1) ∧
      ∑ i' ∈ Finset.range (2 ^ N), (Set.Ioc (rr t N i') (rr t N (i' + 1))).indicator
        (fun _ => x i') s = x i := by
  obtain ⟨i, hi, h1, h2⟩ := dyadic_cell ht N hs0 hst
  refine ⟨i, hi, h1, h2, ?_⟩
  rw [Finset.sum_eq_single i]
  · simp [Set.indicator_of_mem, h1, h2]
  · intro i' _ hne
    rw [Set.indicator_of_notMem]
    intro hmem
    rcases lt_or_gt_of_ne hne with h | h
    · have := rr_mono ht N (Nat.succ_le_of_lt h)
      linarith [hmem.2, hmem.1]
    · have := rr_mono ht N (Nat.succ_le_of_lt h)
      linarith [hmem.2, hmem.1]
  · intro h; exact absurd (Finset.mem_range.2 hi) h

end WeightedQV

section Tools

variable {P : Measure Ω} {ℱ : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ι → ℝ}

theorem measurable_of_progressive {β : Type*} [MeasurableSpace β] [TopologicalSpace β]
    [TopologicalSpace.PseudoMetrizableSpace β] [BorelSpace β] {u : ℝ → Ω → β}
    (hu : IsProgressive ℱ u) : Measurable fun x : ℝ × Ω => u x.1 x.2 := by
  refine measurable_of_tendsto_metrizable (f := fun n : ℕ => fun x : ℝ × Ω => u (min x.1 n) x.2)
    (fun n => measurable_progressive_min_gen hu n) ?_
  rw [tendsto_pi_nhds]; intro x
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop ⌈x.1⌉₊] with n hn
  rw [min_eq_left]; exact (Nat.le_ceil _).trans (by exact_mod_cast hn)

theorem enorm_sq_add_le (x y : ℝ) : ‖x + y‖ₑ ^ 2 ≤ 2 * ‖x‖ₑ ^ 2 + 2 * ‖y‖ₑ ^ 2 := by
  simp only [SimpleIntegrand.enorm_sq_eq']
  rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (x - y)])

/-- Two `L²`-limits of a.e.-equal sequences agree a.e. -/
theorem ae_eq_of_L2_limits {Y Z : Ω → ℝ} {Yn Zn : ℕ → Ω → ℝ} (hY : Measurable Y)
    (hZ : Measurable Z) (hYn : ∀ n, Measurable (Yn n)) (h : ∀ n, Yn n =ᵐ[P] Zn n)
    (hY' : Tendsto (fun n => ∫⁻ ω, ‖Yn n ω - Y ω‖ₑ ^ 2 ∂P) atTop (𝓝 0))
    (hZ' : Tendsto (fun n => ∫⁻ ω, ‖Zn n ω - Z ω‖ₑ ^ 2 ∂P) atTop (𝓝 0)) : Y =ᵐ[P] Z := by
  have hle : ∀ n, ∫⁻ ω, ‖Y ω - Z ω‖ₑ ^ 2 ∂P ≤
      2 * ∫⁻ ω, ‖Yn n ω - Y ω‖ₑ ^ 2 ∂P + 2 * ∫⁻ ω, ‖Zn n ω - Z ω‖ₑ ^ 2 ∂P := by
    intro n
    have hm : Measurable fun ω => ‖Yn n ω - Y ω‖ₑ ^ 2 := ((hYn n).sub hY).enorm.pow_const 2
    rw [← lintegral_const_mul _ hm]
    have hZn : AEMeasurable (Zn n) P := (hYn n).aemeasurable.congr (h n)
    have hm2 : AEMeasurable (fun ω => ‖Zn n ω - Z ω‖ₑ ^ 2) P :=
      ((hZn.sub hZ.aemeasurable).enorm).pow_const 2
    rw [← lintegral_const_mul' _ _ (by simp)]
    rw [← lintegral_add_left' (hm.const_mul 2).aemeasurable]
    refine lintegral_mono_ae ?_
    filter_upwards [h n] with ω hω
    have e : Y ω - Z ω = -(Yn n ω - Y ω) + (Zn n ω - Z ω) := by rw [← hω]; ring
    rw [e]
    refine (enorm_sq_add_le _ _).trans ?_
    rw [enorm_neg]
  have h0 : ∫⁻ ω, ‖Y ω - Z ω‖ₑ ^ 2 ∂P ≤ 0 := by
    have := (ENNReal.Tendsto.const_mul hY' (Or.inr (by simp : (2 : ℝ≥0∞) ≠ ∞))).add
      (ENNReal.Tendsto.const_mul hZ' (Or.inr (by simp : (2 : ℝ≥0∞) ≠ ∞)))
    rw [mul_zero, add_zero] at this
    exact ge_of_tendsto' this hle
  have h1 : ∫⁻ ω, ‖Y ω - Z ω‖ₑ ^ 2 ∂P = 0 := le_antisymm h0 bot_le
  have hm : Measurable fun ω => ‖Y ω - Z ω‖ₑ ^ 2 := (hY.sub hZ).enorm.pow_const 2
  rw [lintegral_eq_zero_iff hm] at h1
  filter_upwards [h1] with ω hω
  have : ‖Y ω - Z ω‖ₑ = 0 := by simpa using hω
  simpa [sub_eq_zero] using this

theorem tendsto_lintegral_sq_mul {ξn : ℕ → Ω → ℝ} {ξ : Ω → ℝ} {C : ℝ}
    (hξn : ∀ n, Measurable (ξn n)) (hξ : Measurable ξ) (hbd : ∀ n ω, |ξn n ω - ξ ω| ≤ C)
    (hconv : ∀ ω, Tendsto (fun n => ξn n ω) atTop (𝓝 (ξ ω))) {g : Ω → ℝ≥0∞}
    (hg : Measurable g) (hgi : ∫⁻ ω, g ω ∂P ≠ ∞) :
    Tendsto (fun n => ∫⁻ ω, ‖ξn n ω - ξ ω‖ₑ ^ 2 * g ω ∂P) atTop (𝓝 0) := by
  have := tendsto_lintegral_of_dominated_convergence (μ := P)
    (F := fun n ω => ‖ξn n ω - ξ ω‖ₑ ^ 2 * g ω) (f := fun _ => 0) (fun ω => ‖C‖ₑ ^ 2 * g ω)
    (fun n => (((hξn n).sub hξ).enorm.pow_const 2).mul hg)
    (fun n => ae_of_all _ fun ω => by
      dsimp only
      gcongr
      rw [← ofReal_norm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (by simpa using (hbd n ω).trans (le_abs_self C)))
    (by rw [lintegral_const_mul _ hg]; exact ENNReal.mul_ne_top (by simp) hgi) ?_
  · simpa using this
  · filter_upwards [ae_lt_top hg hgi] with ω hω
    have h1 : Tendsto (fun n => ‖ξn n ω - ξ ω‖ₑ ^ 2) atTop (𝓝 0) := by
      have : Tendsto (fun n => ξn n ω - ξ ω) atTop (𝓝 0) := by
        simpa using (hconv ω).sub_const (ξ ω)
      have h2 : Tendsto (fun n => ‖ξn n ω - ξ ω‖ₑ) atTop (𝓝 0) := by
        have h3 := (continuous_enorm.tendsto (0 : ℝ)).comp this
        rw [enorm_zero] at h3
        exact h3
      have h4 := ((ENNReal.continuous_pow 2).tendsto 0).comp h2
      rw [zero_pow (by norm_num)] at h4
      exact h4
    simpa using ENNReal.Tendsto.mul_const h1 (Or.inr hω.ne)

variable {Φ : ℝ → Ω → ι → ℝ}

theorem sqIntegralOn_mul_left (P : Measure Ω) (ξ : Ω → ℝ) (Φ : ℝ → Ω → ι → ℝ) (T : ℝ) :
    sqIntegralOn P (fun s ω k => ξ ω * Φ s ω k) T =
      ∫⁻ ω, ‖ξ ω‖ₑ ^ 2 * (∫⁻ s in Set.Icc 0 T, ∑ k, ‖Φ s ω k‖ₑ ^ 2) ∂P := by
  unfold sqIntegralOn
  refine lintegral_congr fun ω => ?_
  rw [← lintegral_const_mul' _ _ (by simp)]
  refine lintegral_congr fun s => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [enorm_mul, mul_pow]

theorem measurable_sqInt (hΦ : IsProgressive ℱ Φ) (T : ℝ) :
    Measurable fun ω => ∫⁻ s in Set.Icc 0 T, ∑ k, ‖Φ s ω k‖ₑ ^ 2 := by
  have hm := measurable_of_progressive hΦ
  have : Measurable fun x : ℝ × Ω => ∑ k, ‖Φ x.1 x.2 k‖ₑ ^ 2 :=
    Finset.measurable_sum _ fun k _ =>
      (((measurable_pi_apply k).comp hm).enorm).pow_const 2
  exact this.lintegral_prod_left' (μ := volume.restrict (Set.Icc (0 : ℝ) T))

theorem isProgressive_pi {γ : Type*} {u : γ → ℝ → Ω → ℝ} (h : ∀ k, IsProgressive ℱ (u k)) :
    IsProgressive ℱ (fun s ω k => u k s ω) :=
  fun i => by
    letI : MeasurableSpace (Set.Iic i × Ω) := Subtype.instMeasurableSpace.prod (ℱ i)
    exact measurable_pi_iff.2 fun k => h k i

theorem IsProgressiveL2.mul_bdd (hΦ : IsProgressiveL2 P ℱ Φ) {Θ : ℝ → Ω → ℝ}
    (hΘ : IsProgressive ℱ Θ) {C : ℝ} (hC : ∀ s ω, |Θ s ω| ≤ C) :
    IsProgressiveL2 P ℱ (fun s ω k => Θ s ω * Φ s ω k) := by
  refine ⟨isProgressive_pi fun k => hΘ.mul (isProgressive_coord hΦ.prog k), fun T => ?_⟩
  · refine lt_of_le_of_lt ?_ (ENNReal.mul_lt_top (b := sqIntegralOn P Φ T)
      (by simp : ‖C‖ₑ ^ 2 < ∞) (hΦ.sq T))
    unfold sqIntegralOn
    rw [← lintegral_const_mul' _ _ (by simp)]
    refine lintegral_mono fun ω => ?_
    rw [← lintegral_const_mul' _ _ (by simp)]
    refine lintegral_mono fun s => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [enorm_mul, mul_pow]
    gcongr
    rw [← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (by simpa using (hC s ω).trans (le_abs_self C))

theorem IsProgressiveLocL2.mul_bdd (hΦ : IsProgressiveLocL2 P ℱ Φ) {Θ : ℝ → Ω → ℝ}
    (hΘ : IsProgressive ℱ Θ) {C : ℝ} (hC : ∀ s ω, |Θ s ω| ≤ C) :
    IsProgressiveLocL2 P ℱ (fun s ω k => Θ s ω * Φ s ω k) := by
  refine ⟨isProgressive_pi fun k => hΘ.mul (isProgressive_coord hΦ.prog k), fun T => ?_⟩
  · filter_upwards [hΦ.sq T] with ω hω
    refine lt_of_le_of_lt ?_ (ENNReal.mul_lt_top (b := ∫⁻ s in Set.Icc 0 T, ∑ k, ‖Φ s ω k‖ₑ ^ 2)
      (by simp : ‖C‖ₑ ^ 2 < ∞) hω)
    rw [← lintegral_const_mul' _ _ (by simp)]
    refine lintegral_mono fun s => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [enorm_mul, mul_pow]
    gcongr
    rw [← ofReal_norm, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (by simpa using (hC s ω).trans (le_abs_self C))

theorem exists_simpleFunc_approx_real {α : Type*} [MeasurableSpace α] {ξ : α → ℝ}
    (hξ : Measurable ξ) :
    ∃ ξn : ℕ → SimpleFunc α ℝ, (∀ x, Tendsto (fun n => ξn n x) atTop (𝓝 (ξ x))) ∧
      ∀ n x, |ξn n x| ≤ 2 * |ξ x| :=
  ⟨fun n => SimpleFunc.approxOn ξ hξ Set.univ 0 (Set.mem_univ _) n,
   fun x => SimpleFunc.tendsto_approxOn hξ (Set.mem_univ 0) (by simp),
   fun n x => by
    simpa [two_mul] using SimpleFunc.norm_approxOn_zero_le hξ (Set.mem_univ (0 : ℝ)) x n⟩

theorem isProgressive_mul_meas (hΦ : IsProgressive ℱ Φ) {a : ℝ} {ξ : Ω → ℝ}
    (hξ : Measurable[ℱ a] ξ) (h0 : ∀ s ≤ a, ∀ ω, Φ s ω = 0) :
    IsProgressive ℱ (fun s ω k => ξ ω * Φ s ω k) := by
  refine isProgressive_pi fun k => fun i => ?_
  letI : MeasurableSpace (Set.Iic i × Ω) := Subtype.instMeasurableSpace.prod (ℱ i)
  by_cases hai : a ≤ i
  · have h1 : Measurable fun p : Set.Iic i × Ω => ξ p.2 :=
      (hξ.mono (ℱ.mono hai) le_rfl).comp measurable_snd
    exact h1.mul (isProgressive_coord hΦ k i)
  · have : (fun p : Set.Iic i × Ω => ξ p.2 * Φ p.1 p.2 k) = fun _ => 0 := by
      funext p
      rw [h0 _ (le_of_lt (lt_of_le_of_lt p.1.2 (not_le.1 hai))) p.2]
      simp
    rw [this]
    exact measurable_const

theorem isProgressiveL2_mul_meas (hΦ : IsProgressiveL2 P ℱ Φ) {a : ℝ} {ξ : Ω → ℝ}
    (hξ : Measurable[ℱ a] ξ) (h0 : ∀ s ≤ a, ∀ ω, Φ s ω = 0) {C : ℝ} (hC : ∀ ω, |ξ ω| ≤ C) :
    IsProgressiveL2 P ℱ (fun s ω k => ξ ω * Φ s ω k) := by
  refine ⟨isProgressive_mul_meas hΦ.prog hξ h0, fun T => ?_⟩
  rw [sqIntegralOn_mul_left]
  calc ∫⁻ ω, ‖ξ ω‖ₑ ^ 2 * (∫⁻ s in Set.Icc 0 T, ∑ k, ‖Φ s ω k‖ₑ ^ 2) ∂P
      ≤ ∫⁻ ω, ‖C‖ₑ ^ 2 * (∫⁻ s in Set.Icc 0 T, ∑ k, ‖Φ s ω k‖ₑ ^ 2) ∂P := by
        refine lintegral_mono fun ω => ?_
        gcongr
        rw [← ofReal_norm, ← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (by simpa using (hC ω).trans (le_abs_self C))
    _ = ‖C‖ₑ ^ 2 * sqIntegralOn P Φ T := by
        rw [lintegral_const_mul' _ _ (by simp)]; rfl
    _ < ∞ := ENNReal.mul_lt_top (by simp) (hΦ.sq T)

variable [IsProbabilityMeasure P]

theorem itoIntegral_indicator_event (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveL2 P ℱ Φ) {a : ℝ} (h0 : ∀ s ≤ a, ∀ ω, Φ s ω = 0)
    {A : Set Ω} (hA : MeasurableSet[ℱ a] A) (t : ℝ) :
    ∀ᵐ ω ∂P, itoIntegral P ℱ W (fun s ω k => A.indicator (fun ω => Φ s ω k) ω) t ω =
      A.indicator (fun ω => itoIntegral P ℱ W Φ t ω) ω := by
  classical
  let σ : Ω → WithTop ℝ := fun ω => if ω ∈ Aᶜ then ((a : ℝ) : WithTop ℝ) else ⊤
  have hσ : IsStoppingTime ℱ σ := by
    intro i
    by_cases hai : a ≤ i
    · have : {ω | σ ω ≤ (i : WithTop ℝ)} = Aᶜ := by
        ext ω
        by_cases hω : ω ∈ A
        · simp [σ, hω]
        · simp [σ, hω, WithTop.coe_le_coe, hai]
      rw [this]
      exact ℱ.mono hai _ (@MeasurableSet.compl Ω _ (ℱ a) hA)
    · have : {ω | σ ω ≤ (i : WithTop ℝ)} = ∅ := by
        ext ω
        by_cases hω : ω ∈ A
        · simp [σ, hω]
        · simp [σ, hω, WithTop.coe_le_coe, hai]
      rw [this]
      exact @MeasurableSet.empty Ω (ℱ i)
  have hint : stopIntegrand Φ σ = fun s ω k => A.indicator (fun ω => Φ s ω k) ω := by
    funext s ω k
    by_cases hω : ω ∈ A
    · simp [stopIntegrand, σ, hω, Set.indicator_of_mem]
    · by_cases hs : s ≤ a
      · simp [stopIntegrand, σ, hω, WithTop.coe_le_coe, hs, h0 s hs ω]
      · simp [stopIntegrand, σ, hω, WithTop.coe_le_coe, hs]
  have hmain := itoIntegral_stopIntegrand hW hΦ hσ
  rw [hint] at hmain
  have hzero : ∀ᵐ ω ∂P, itoIntegral P ℱ W Φ (min t a) ω = 0 := by
    have hiso := lintegral_itoIntegral_sq hW hΦ (min t a)
    have hsq : sqIntegralOn P Φ (min t a) = 0 := by
      unfold sqIntegralOn
      have : ∀ ω, ∫⁻ s in Set.Icc 0 (min t a), ∑ k, ‖Φ s ω k‖ₑ ^ 2 = 0 := fun ω => by
        rw [setLIntegral_congr_fun measurableSet_Icc (g := fun _ => 0)
          (fun s hs => by simp [h0 s (hs.2.trans (min_le_right _ _)) ω])]
        simp
      simp [this]
    rw [hsq] at hiso
    have hm : Measurable fun ω => ‖itoIntegral P ℱ W Φ (min t a) ω‖ₑ ^ 2 :=
      (((adapted_itoIntegral P ℱ W Φ (min t a)).mono (ℱ.le _) le_rfl).enorm).pow_const 2
    rw [lintegral_eq_zero_iff hm] at hiso
    filter_upwards [hiso] with ω hω
    simpa using hω
  filter_upwards [hmain, hzero] with ω h1 h2
  rw [h1 t]
  by_cases hω : ω ∈ A
  · have : σ ω = ⊤ := by simp [σ, hω]
    rw [stoppedProcess_apply_top this, Set.indicator_of_mem hω]
  · have : σ ω = ((a : ℝ) : WithTop ℝ) := by simp [σ, hω]
    rw [stoppedProcess_apply_coe this, Set.indicator_of_notMem hω, h2]

theorem simpleFunc_real_induction {α : Type*} [MeasurableSpace α] {motive : (α → ℝ) → Prop}
    (hc : ∀ (c : ℝ) (S : Set α), MeasurableSet S → motive (S.indicator fun _ => c))
    (hadd : ∀ f g : SimpleFunc α ℝ, motive f → motive g → motive (⇑f + ⇑g))
    (f : SimpleFunc α ℝ) : motive f := by
  refine SimpleFunc.induction (motive := fun f => motive f) ?_ ?_ f
  · intro c S hS
    convert hc c S hS using 1
    ext ω
    by_cases h : ω ∈ S <;> simp [SimpleFunc.piecewise_apply, h]
  · intro f g _ hf hg
    exact hadd f g hf hg

theorem itoIntegral_mul_simple (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveL2 P ℱ Φ) {a : ℝ} (h0 : ∀ s ≤ a, ∀ ω, Φ s ω = 0)
    (f : @SimpleFunc Ω (ℱ a) ℝ) (t : ℝ) :
    ∀ᵐ ω ∂P, itoIntegral P ℱ W (fun s ω k => f ω * Φ s ω k) t ω =
      f ω * itoIntegral P ℱ W Φ t ω := by
  refine @simpleFunc_real_induction Ω (ℱ a)
    (fun f => ∀ᵐ ω ∂P, itoIntegral P ℱ W (fun s ω k => f ω * Φ s ω k) t ω =
      f ω * itoIntegral P ℱ W Φ t ω) ?_ ?_ f
  · intro c S hS
    have hL2 : IsProgressiveL2 P ℱ (fun s ω k => S.indicator (fun ω => Φ s ω k) ω) := by
      have hm1 : Measurable[ℱ a] (S.indicator fun _ => (1 : ℝ)) :=
        measurable_const.indicator hS
      have := isProgressiveL2_mul_meas hΦ (a := a) (ξ := S.indicator fun _ => (1 : ℝ))
        hm1 h0 (C := 1)
        (fun ω => by by_cases h : ω ∈ S <;> simp [h])
      convert this using 3 with s ω k
      by_cases h : ω ∈ S <;> simp [h]
    have e : (fun s ω k => S.indicator (fun _ => c) ω * Φ s ω k) =
        fun s ω => c • (fun k => S.indicator (fun ω => Φ s ω k) ω) := by
      funext s ω k
      by_cases h : ω ∈ S <;> simp [h]
    rw [e]
    have h1 := itoIntegral_smul hW hL2 c
    have h2 := itoIntegral_indicator_event hW hΦ h0 hS t
    filter_upwards [h1, h2] with ω h1 h2
    rw [h1 t, h2]
    by_cases h : ω ∈ S <;> simp [h]
  · intro f g hf hg
    obtain ⟨Cf, hCf⟩ := @SimpleFunc.exists_forall_norm_le Ω ℝ (ℱ a) _ f
    obtain ⟨Cg, hCg⟩ := @SimpleFunc.exists_forall_norm_le Ω ℝ (ℱ a) _ g
    have hLf := isProgressiveL2_mul_meas hΦ (@SimpleFunc.measurable Ω ℝ (ℱ a) _ f) h0 hCf
    have hLg := isProgressiveL2_mul_meas hΦ (@SimpleFunc.measurable Ω ℝ (ℱ a) _ g) h0 hCg
    have h1 := itoIntegral_add hW hLf hLg
    have e : (fun s ω k => (⇑f + ⇑g) ω * Φ s ω k) =
        fun s ω => (fun k => f ω * Φ s ω k) + (fun k => g ω * Φ s ω k) := by
      funext s ω k; simp [add_mul]
    rw [e]
    filter_upwards [h1, hf, hg] with ω h1 hf hg
    rw [h1 t, hf, hg]
    simp [add_mul]

/-- Pulling a bounded `ℱ_a`-measurable factor inside the Itô integral of an integrand vanishing
before `a`. -/
theorem itoIntegral_mul_meas (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveL2 P ℱ Φ) {a : ℝ} (h0 : ∀ s ≤ a, ∀ ω, Φ s ω = 0)
    {ξ : Ω → ℝ} (hξ : Measurable[ℱ a] ξ) {C : ℝ} (hC : ∀ ω, |ξ ω| ≤ C) (t : ℝ) :
    ∀ᵐ ω ∂P, itoIntegral P ℱ W (fun s ω k => ξ ω * Φ s ω k) t ω =
      ξ ω * itoIntegral P ℱ W Φ t ω := by
  obtain ⟨ξn, hξn1, hξn2⟩ := @exists_simpleFunc_approx_real Ω (ℱ a) ξ hξ
  have hξnm : ∀ n, Measurable[ℱ a] (ξn n) := fun n => @SimpleFunc.measurable Ω ℝ (ℱ a) _ (ξn n)
  have hC' : ∀ ω, |ξ ω| ≤ |C| := fun ω => (hC ω).trans (le_abs_self C)
  have hξnb : ∀ n ω, |ξn n ω| ≤ 2 * |C| := fun n ω => (hξn2 n ω).trans (by linarith [hC' ω])
  have hdb : ∀ n ω, |ξn n ω - ξ ω| ≤ 3 * |C| := fun n ω =>
    (abs_sub _ _).trans (by linarith [hξnb n ω, hC' ω])
  have hξm : Measurable ξ := hξ.mono (ℱ.le a) le_rfl
  have hξnm' : ∀ n, Measurable (ξn n) := fun n => (hξnm n).mono (ℱ.le a) le_rfl
  have hL2n : ∀ n, IsProgressiveL2 P ℱ (fun s ω k => ξn n ω * Φ s ω k) := fun n =>
    isProgressiveL2_mul_meas hΦ (hξnm n) h0 (hξnb n)
  have hL2 : IsProgressiveL2 P ℱ (fun s ω k => ξ ω * Φ s ω k) :=
    isProgressiveL2_mul_meas hΦ hξ h0 hC
  have hnegm : Measurable[ℱ a] (fun ω => -ξ ω) := hξ.neg
  have hL2neg : IsProgressiveL2 P ℱ (fun s ω k => (-ξ ω) * Φ s ω k) :=
    isProgressiveL2_mul_meas hΦ hnegm h0 (C := |C|) (fun ω => by simpa using hC' ω)
  have hdm : ∀ n, Measurable[ℱ a] (fun ω => ξn n ω - ξ ω) := fun n => (hξnm n).sub hξ
  have hL2d : ∀ n, IsProgressiveL2 P ℱ (fun s ω k => (ξn n ω - ξ ω) * Φ s ω k) := fun n =>
    isProgressiveL2_mul_meas hΦ (hdm n) h0 (hdb n)
  set V := itoIntegral P ℱ W Φ t with hV
  set Y := itoIntegral P ℱ W (fun s ω k => ξ ω * Φ s ω k) t with hYdef
  have hVm : Measurable V := (adapted_itoIntegral P ℱ W Φ t).mono (ℱ.le t) le_rfl
  have hYm : Measurable Y := (adapted_itoIntegral P ℱ W _ t).mono (ℱ.le t) le_rfl
  have hsmul := itoIntegral_smul hW hL2 (-1)
  have e1 : (fun s ω => (-1 : ℝ) • (fun k => ξ ω * Φ s ω k)) = fun s ω k => (-ξ ω) * Φ s ω k := by
    funext s ω k; simp
  rw [e1] at hsmul
  have hlin : ∀ n, ∀ᵐ ω ∂P, itoIntegral P ℱ W (fun s ω k => ξn n ω * Φ s ω k) t ω - Y ω =
      itoIntegral P ℱ W (fun s ω k => (ξn n ω - ξ ω) * Φ s ω k) t ω := by
    intro n
    have hadd := itoIntegral_add hW (hL2n n) hL2neg
    have e2 : (fun s ω => (fun k => ξn n ω * Φ s ω k) + (fun k => (-ξ ω) * Φ s ω k)) =
        fun s ω k => (ξn n ω - ξ ω) * Φ s ω k := by
      funext s ω k; simp [sub_mul, neg_mul]; ring
    rw [e2] at hadd
    filter_upwards [hadd, hsmul] with ω h1 h2
    rw [h1 t, h2 t]; simp [hYdef]; ring
  have hg : ∫⁻ ω, (∫⁻ s in Set.Icc 0 t, ∑ k, ‖Φ s ω k‖ₑ ^ 2) ∂P ≠ ∞ := hΦ.sq t |>.ne
  have hY' : Tendsto (fun n => ∫⁻ ω, ‖itoIntegral P ℱ W (fun s ω k => ξn n ω * Φ s ω k) t ω - Y ω‖ₑ ^ 2 ∂P)
      atTop (𝓝 0) := by
    have := tendsto_lintegral_sq_mul (P := P) hξnm' hξm hdb hξn1 (measurable_sqInt hΦ.prog t) hg
    refine this.congr fun n => ?_
    refine Eq.symm ?_
    calc ∫⁻ ω, ‖itoIntegral P ℱ W (fun s ω k => ξn n ω * Φ s ω k) t ω - Y ω‖ₑ ^ 2 ∂P
        = ∫⁻ ω, ‖itoIntegral P ℱ W (fun s ω k => (ξn n ω - ξ ω) * Φ s ω k) t ω‖ₑ ^ 2 ∂P :=
          lintegral_congr_ae (by filter_upwards [hlin n] with ω h; rw [h])
      _ = sqIntegralOn P (fun s ω k => (ξn n ω - ξ ω) * Φ s ω k) t :=
          lintegral_itoIntegral_sq hW (hL2d n) t
      _ = _ := sqIntegralOn_mul_left P (fun ω => ξn n ω - ξ ω) Φ t
  have hgV : ∫⁻ ω, ‖V ω‖ₑ ^ 2 ∂P ≠ ∞ := by
    rw [hV, lintegral_itoIntegral_sq hW hΦ t]; exact (hΦ.sq t).ne
  have hZ' : Tendsto (fun n => ∫⁻ ω, ‖ξn n ω * V ω - ξ ω * V ω‖ₑ ^ 2 ∂P) atTop (𝓝 0) := by
    have := tendsto_lintegral_sq_mul (P := P) hξnm' hξm hdb hξn1
      (hVm.enorm.pow_const 2) hgV
    refine this.congr fun n => ?_
    refine lintegral_congr fun ω => ?_
    rw [← sub_mul, enorm_mul, mul_pow]
  exact ae_eq_of_L2_limits (Yn := fun n => itoIntegral P ℱ W (fun s ω k => ξn n ω * Φ s ω k) t)
    (Zn := fun n ω => ξn n ω * V ω) (Z := fun ω => ξ ω * V ω) hYm (hξm.mul hVm)
    (fun n => (adapted_itoIntegral P ℱ W _ t).mono (ℱ.le t) le_rfl)
    (fun n => itoIntegral_mul_simple hW hΦ h0 (ξn n) t) hY' hZ'


/-- The step integrand `ξ · 1_{(a, a']} · Φ`. -/
def blockInt (a a' : ℝ) (ξ : Ω → ℝ) (Φ : ℝ → Ω → ι → ℝ) : ℝ → Ω → ι → ℝ :=
  fun s ω k => ξ ω * (Set.Ioc a a').indicator (fun _ => Φ s ω k) s

theorem isProgressive_indicator_Ioc (ℱ : Filtration ℝ mΩ) (a a' : ℝ) :
    IsProgressive ℱ (fun (s : ℝ) (_ : Ω) => (Set.Ioc a a').indicator (fun _ => (1 : ℝ)) s) := by
  intro i
  letI : MeasurableSpace (Set.Iic i × Ω) := Subtype.instMeasurableSpace.prod (ℱ i)
  have : Measurable fun p : Set.Iic i × Ω => (Set.Ioc a a').indicator (fun _ => (1 : ℝ)) (p.1 : ℝ) :=
    (measurable_const.indicator measurableSet_Ioc).comp (measurable_subtype_coe.comp measurable_fst)
  exact this

theorem isProgressiveL2_blockInt (hΦ : IsProgressiveL2 P ℱ Φ) {a a' : ℝ} (ha : 0 ≤ a)
    {ξ : Ω → ℝ} (hξ : Measurable[ℱ a] ξ) {C : ℝ} (hC : ∀ ω, |ξ ω| ≤ C) :
    IsProgressiveL2 P ℱ (blockInt a a' ξ Φ) := by
  have hΓ : IsProgressiveL2 P ℱ (fun s ω k => (Set.Ioc a a').indicator (fun _ => (1 : ℝ)) s *
      Φ s ω k) := hΦ.mul_bdd (isProgressive_indicator_Ioc ℱ a a') (C := 1) (fun s ω => by
        by_cases h : s ∈ Set.Ioc a a' <;> simp [h])
  have h0 : ∀ s ≤ a, ∀ ω, (fun s ω k => (Set.Ioc a a').indicator (fun _ => (1 : ℝ)) s *
      Φ s ω k) s ω = 0 := by
    intro s hs ω
    funext k
    have : s ∉ Set.Ioc a a' := fun h => absurd h.1 (not_lt.2 hs)
    simp [this]
  have := isProgressiveL2_mul_meas hΓ hξ h0 hC
  convert this using 3 with s ω k
  unfold blockInt
  by_cases h : s ∈ Set.Ioc a a' <;> simp [h]

theorem itoIntegral_blockInt (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveL2 P ℱ Φ) {a a' : ℝ} (ha : 0 ≤ a) (haa' : a ≤ a')
    {ξ : Ω → ℝ} (hξ : Measurable[ℱ a] ξ) {C : ℝ} (hC : ∀ ω, |ξ ω| ≤ C) (t : ℝ) :
    ∀ᵐ ω ∂P, itoIntegral P ℱ W (blockInt a a' ξ Φ) t ω =
      ξ ω * (itoIntegral P ℱ W Φ (min t a') ω - itoIntegral P ℱ W Φ (min t a) ω) := by
  have hΓ : IsProgressiveL2 P ℱ (fun s ω k => (Set.Ioc a a').indicator (fun _ => (1 : ℝ)) s *
      Φ s ω k) := hΦ.mul_bdd (isProgressive_indicator_Ioc ℱ a a') (C := 1) (fun s ω => by
        by_cases h : s ∈ Set.Ioc a a' <;> simp [h])
  have h0 : ∀ s ≤ a, ∀ ω, (fun s ω k => (Set.Ioc a a').indicator (fun _ => (1 : ℝ)) s *
      Φ s ω k) s ω = 0 := by
    intro s hs ω
    funext k
    have : s ∉ Set.Ioc a a' := fun h => absurd h.1 (not_lt.2 hs)
    simp [this]
  have h1 := itoIntegral_mul_meas hW hΓ h0 hξ hC t
  have h2 := itoIntegral_indicator_Ioc hW hΦ ha haa'
  have e : (fun s ω k => ξ ω * (fun s ω k => (Set.Ioc a a').indicator (fun _ => (1 : ℝ)) s *
      Φ s ω k) s ω k) = blockInt a a' ξ Φ := by
    funext s ω k
    unfold blockInt
    by_cases h : s ∈ Set.Ioc a a' <;> simp [h]
  rw [e] at h1
  have e2 : (fun s ω k => (Set.Ioc a a').indicator (fun _ => (1 : ℝ)) s * Φ s ω k) =
      fun s ω => Set.indicator (Set.Ioc a a') (fun _ => Φ s ω) s := by
    funext s ω k
    by_cases h : s ∈ Set.Ioc a a' <;> simp [h]
  rw [e2] at h1
  filter_upwards [h1, h2] with ω h1 h2
  rw [h1, h2 t]

theorem itoIntegral_finset_sum (hW : IsBrownianFiltration P ℱ W) {γ : Type*} (S : Finset γ)
    {Ψ : γ → ℝ → Ω → ι → ℝ} (h : ∀ c ∈ S, IsProgressiveL2 P ℱ (Ψ c)) :
    IsProgressiveL2 P ℱ (fun t ω => ∑ c ∈ S, Ψ c t ω) ∧
      ∀ᵐ ω ∂P, ∀ t, itoIntegral P ℱ W (fun t ω => ∑ c ∈ S, Ψ c t ω) t ω =
        ∑ c ∈ S, itoIntegral P ℱ W (Ψ c) t ω := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have hz : IsProgressiveL2 P ℱ (fun (_ : ℝ) (_ : Ω) (_ : ι) => (0 : ℝ)) :=
      IsProgressiveL2.of_bounded P (isProgressive_const ℱ (fun _ : ι => (0 : ℝ))) 0
        (fun _ _ _ => by simp)
    refine ⟨by simp only [Finset.sum_empty]; exact hz, ?_⟩
    have := itoIntegral_smul hW hz 0
    filter_upwards [this] with ω h t
    have := h t
    simp only [zero_smul, zero_mul] at this
    simpa using this
  | insert a S ha ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun c hc => h c (Finset.mem_insert_of_mem hc))
    have hA := h a (Finset.mem_insert_self a S)
    have e : (fun t ω => ∑ c ∈ insert a S, Ψ c t ω) = fun t ω => Ψ a t ω +
        (fun t ω => ∑ c ∈ S, Ψ c t ω) t ω := by
      funext t ω; rw [Finset.sum_insert ha]
    rw [e]
    refine ⟨hA.add ih1, ?_⟩
    filter_upwards [itoIntegral_add hW hA ih1, ih2] with ω h1 h2 t
    rw [h1 t, h2 t, Finset.sum_insert ha]

theorem tendstoInMeasure_of_L2 {Zn : ℕ → Ω → ℝ} {Z : Ω → ℝ} (hn : ∀ n, Measurable (Zn n))
    (hZ : Measurable Z)
    (h : Tendsto (fun n => ∫⁻ ω, ‖Zn n ω - Z ω‖ₑ ^ 2 ∂P) atTop (𝓝 0)) :
    TendstoInMeasure P Zn atTop Z := by
  intro ε hε
  by_cases htop : ε = ∞
  · simp [htop]
  have hε2 : ε ^ 2 ≠ 0 := pow_ne_zero _ hε.ne'
  have hle : ∀ n, P {ω | ε ≤ edist (Zn n ω) (Z ω)} ≤
      (∫⁻ ω, ‖Zn n ω - Z ω‖ₑ ^ 2 ∂P) * (ε ^ 2)⁻¹ := by
    intro n
    have hm : AEMeasurable (fun ω => ‖Zn n ω - Z ω‖ₑ ^ 2) P :=
      (((hn n).sub hZ).enorm.pow_const 2).aemeasurable
    have := mul_meas_ge_le_lintegral₀ hm (ε ^ 2)
    rw [mul_comm, ← ENNReal.le_div_iff_mul_le (Or.inl hε2) (Or.inl (ENNReal.pow_ne_top htop))] at this
    refine le_trans (measure_mono fun ω hω => ?_) (this.trans_eq (by rw [div_eq_mul_inv]))
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [edist_eq_enorm_sub] at hω
    exact pow_le_pow_left' hω 2
  have hlim : Tendsto (fun n => (∫⁻ ω, ‖Zn n ω - Z ω‖ₑ ^ 2 ∂P) * (ε ^ 2)⁻¹) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.mul_const h (Or.inr (ENNReal.inv_ne_top.2 hε2))
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun n => bot_le) hle

/-- Dominated convergence for `sqIntegralOn`, with almost-sure (in `ω`) domination and
convergence. -/
theorem tendsto_sqIntegralOn_of_dominated_ae {Fn : ℕ → ℝ → Ω → ι → ℝ} {F : ℝ → Ω → ι → ℝ}
    (T : ℝ) (hFn : ∀ n, Measurable fun x : ℝ × Ω => Fn n x.1 x.2)
    (hF : Measurable fun x : ℝ × Ω => F x.1 x.2)
    {D : ℝ → Ω → ℝ≥0∞} (hD : Measurable fun x : ℝ × Ω => D x.1 x.2)
    (hDfin : ∫⁻ ω, (∫⁻ s in Set.Icc 0 T, D s ω) ∂P ≠ ∞)
    (hle : ∀ n, ∀ᵐ ω ∂P, ∀ s ∈ Set.Icc 0 T, qn (Fn n s ω - F s ω) ≤ D s ω)
    (hconv : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc 0 T)),
      Tendsto (fun n => Fn n s ω) atTop (𝓝 (F s ω))) :
    Tendsto (fun n => sqIntegralOn P (fun s ω => Fn n s ω - F s ω) T) atTop (𝓝 0) := by
  have hmeas_n : ∀ n, Measurable fun x : ℝ × Ω => qn (Fn n x.1 x.2 - F x.1 x.2) := fun n =>
    measurable_qn.comp ((hFn n).sub hF)
  have houter : ∀ n, Measurable fun ω => ∫⁻ s in Set.Icc 0 T, qn (Fn n s ω - F s ω) :=
    fun n => (hmeas_n n).lintegral_prod_left'
  have hDm : Measurable fun ω => ∫⁻ s in Set.Icc 0 T, D s ω := hD.lintegral_prod_left'
  have hgood := ae_lt_top hDm hDfin
  have hle' := ae_all_iff.2 hle
  have := tendsto_lintegral_of_dominated_convergence (μ := P)
    (F := fun n ω => ∫⁻ s in Set.Icc 0 T, qn (Fn n s ω - F s ω)) (f := fun _ => 0)
    (fun ω => ∫⁻ s in Set.Icc 0 T, D s ω) houter
    (fun n => by
      filter_upwards [hle'] with ω hω
      exact lintegral_mono_ae
        ((ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ fun s hs => hω n s hs))) hDfin ?_
  · simpa [sqIntegralOn, qn] using this
  · filter_upwards [hgood, hle', hconv] with ω hω hω' hc
    have h0 := tendsto_lintegral_of_dominated_convergence (μ := volume.restrict (Set.Icc 0 T))
      (F := fun n s => qn (Fn n s ω - F s ω)) (f := fun _ => 0) (fun s => D s ω)
      (fun n => measurable_qn.comp (((hFn n).comp measurable_prodMk_right).sub
        (hF.comp measurable_prodMk_right)))
      (fun n => (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ fun s hs => hω' n s hs))
      hω.ne ?_
    · simpa using h0
    · filter_upwards [hc] with s hs
      have : Tendsto (fun n => Fn n s ω - F s ω) atTop (𝓝 (F s ω - F s ω)) :=
        hs.sub tendsto_const_nhds
      rw [sub_self] at this
      have h2 := (continuous_qn.tendsto 0).comp this
      have e0 : qn (0 : ι → ℝ) = 0 := by simp [qn]
      rw [e0] at h2
      exact h2

theorem qn_mul_left (r : ℝ) (v : ι → ℝ) : qn (fun k => r * v k) = ‖r‖ₑ ^ 2 * qn v := by
  unfold qn
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [enorm_mul, mul_pow]

/-- The step weight `∑_i 1_{(t_i, t_{i+1}]}(s) c(t_i)` along the dyadic partition. -/
def stepW (t : ℝ) (N : ℕ) (c : ℝ → Ω → ℝ) : ℝ → Ω → ℝ := fun s ω =>
  ∑ i ∈ Finset.range (2 ^ N), (Set.Ioc (rr t N i) (rr t N (i + 1))).indicator
    (fun _ => c (rr t N i) ω) s

theorem stepW_eq_zero {t : ℝ} (ht : 0 ≤ t) (N : ℕ) (c : ℝ → Ω → ℝ) {s : ℝ}
    (hs : s ∉ Set.Ioc 0 t) (ω : Ω) : stepW t N c s ω = 0 := by
  unfold stepW
  refine Finset.sum_eq_zero fun i hi => Set.indicator_of_notMem (fun hmem => hs ?_) _
  have hi' : i < 2 ^ N := Finset.mem_range.1 hi
  have h0 := (rr_mem ht N i hi'.le).1
  have h1 := (rr_mem ht N (i + 1) (Nat.succ_le_of_lt hi')).2
  exact ⟨lt_of_le_of_lt h0 hmem.1, hmem.2.trans h1⟩

theorem stepW_cell {t : ℝ} (ht : 0 ≤ t) (N : ℕ) (c : ℝ → Ω → ℝ) {s : ℝ} (hs0 : 0 < s)
    (hst : s ≤ t) (ω : Ω) :
    ∃ i, i < 2 ^ N ∧ rr t N i < s ∧ s ≤ rr t N (i + 1) ∧ stepW t N c s ω = c (rr t N i) ω := by
  obtain ⟨i, hi, h1, h2, h3⟩ := sum_indicator_cell ht N hs0 hst (fun i => c (rr t N i) ω)
  exact ⟨i, hi, h1, h2, h3⟩

theorem abs_stepW_le {t : ℝ} (ht : 0 ≤ t) (N : ℕ) {c : ℝ → Ω → ℝ} {Cc : ℝ}
    (hC : ∀ s ω, |c s ω| ≤ Cc) (s : ℝ) (ω : Ω) : |stepW t N c s ω| ≤ Cc := by
  by_cases hs : s ∈ Set.Ioc 0 t
  · obtain ⟨i, _, _, _, h⟩ := stepW_cell ht N c hs.1 hs.2 ω
    rw [h]; exact hC _ _
  · rw [stepW_eq_zero ht N c hs ω]
    simpa using (abs_nonneg _).trans (hC 0 ω)

theorem stepW_tendsto {t : ℝ} (ht : 0 ≤ t) {c : ℝ → Ω → ℝ} {ω : Ω}
    (hcont : ContinuousOn (fun s => c s ω) (Set.Icc 0 t)) {s : ℝ} (hs0 : 0 < s) (hst : s ≤ t) :
    Tendsto (fun N => stepW t N c s ω) atTop (𝓝 (c s ω)) := by
  have hex : ∀ N, ∃ i, i < 2 ^ N ∧ rr t N i < s ∧ s ≤ rr t N (i + 1) ∧
      stepW t N c s ω = c (rr t N i) ω := fun N => stepW_cell ht N c hs0 hst ω
  choose i hi h1 h2 h3 using hex
  have hmem : ∀ N, rr t N (i N) ∈ Set.Icc 0 t := fun N => rr_mem ht N (i N) (hi N).le
  have hclose : ∀ N, |rr t N (i N) - s| ≤ t / 2 ^ N := by
    intro N
    have := rr_succ t N (i N)
    rw [abs_le]; constructor <;> linarith [h1 N, h2 N]
  have ht2 : Tendsto (fun N : ℕ => t / 2 ^ N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  have hlim : Tendsto (fun N => rr t N (i N)) atTop (𝓝 s) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun N => dist_nonneg) (fun N => ?_) ht2
    rw [Real.dist_eq]; exact hclose N
  have hs : s ∈ Set.Icc 0 t := ⟨hs0.le, hst⟩
  have hlim' : Tendsto (fun N => rr t N (i N)) atTop (𝓝[Set.Icc 0 t] s) :=
    tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall hmem⟩
  have := (hcont s hs).tendsto.comp hlim'
  refine this.congr fun N => ?_
  simp [h3 N]

theorem isProgressiveL2_sub (hΦ₁ : IsProgressiveL2 P ℱ Φ) {Φ₂ : ℝ → Ω → ι → ℝ}
    (hΦ₂ : IsProgressiveL2 P ℱ Φ₂) :
    IsProgressiveL2 P ℱ (fun s ω k => Φ s ω k - Φ₂ s ω k) := by
  have e : (fun s ω k => Φ s ω k - Φ₂ s ω k) = fun s ω => Φ s ω + (-1 : ℝ) • Φ₂ s ω := by
    funext s ω k; simp [sub_eq_add_neg]
  rw [e]
  exact hΦ₁.add (hΦ₂.smul (-1))

theorem itoIntegral_sub (hW : IsBrownianFiltration P ℱ W) (hΦ₁ : IsProgressiveL2 P ℱ Φ)
    {Φ₂ : ℝ → Ω → ι → ℝ} (hΦ₂ : IsProgressiveL2 P ℱ Φ₂) :
    ∀ᵐ ω ∂P, ∀ t, itoIntegral P ℱ W (fun s ω k => Φ s ω k - Φ₂ s ω k) t ω =
      itoIntegral P ℱ W Φ t ω - itoIntegral P ℱ W Φ₂ t ω := by
  have h1 := itoIntegral_add hW hΦ₁ (hΦ₂.smul (-1))
  have h2 := itoIntegral_smul hW hΦ₂ (-1)
  have e : (fun s ω => Φ s ω + (-1 : ℝ) • Φ₂ s ω) = fun s ω k => Φ s ω k - Φ₂ s ω k := by
    funext s ω k; simp [sub_eq_add_neg]
  rw [e] at h1
  filter_upwards [h1, h2] with ω a b t
  rw [a t, b t]; ring

theorem tendstoInMeasure_stepSum (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveL2 P ℱ Φ) {t : ℝ} (ht : 0 ≤ t)
    {c : ℝ → Ω → ℝ} (hc : IsProgressive ℱ c) {Cc : ℝ} (hCc : ∀ s ω, |c s ω| ≤ Cc)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun s => c s ω) (Set.Icc 0 t)) :
    TendstoInMeasure P (fun N ω => (Partition.dyadic 0 t ht N).sumIncrements
      (fun s s' => c s ω * (itoIntegral P ℱ W Φ s' ω - itoIntegral P ℱ W Φ s ω))) atTop
      (itoIntegral P ℱ W (fun s ω k => c s ω * Φ s ω k) t) := by
  have hcΦ : IsProgressiveL2 P ℱ (fun s ω k => c s ω * Φ s ω k) := hΦ.mul_bdd hc hCc
  have hblkL2 : ∀ N, ∀ i ∈ Finset.range (2 ^ N), IsProgressiveL2 P ℱ
      (blockInt (rr t N i) (rr t N (i + 1)) (c (rr t N i)) Φ) := by
    intro N i hi
    have hi' : i < 2 ^ N := Finset.mem_range.1 hi
    exact isProgressiveL2_blockInt hΦ (rr_mem ht N i hi'.le).1 (hc.adapted _) (fun ω => hCc _ ω)
  have hFn_eq : ∀ N, (fun s ω => ∑ i ∈ Finset.range (2 ^ N),
      blockInt (rr t N i) (rr t N (i + 1)) (c (rr t N i)) Φ s ω) =
      fun s ω k => stepW t N c s ω * Φ s ω k := by
    intro N
    funext s ω k
    simp only [Finset.sum_apply, stepW, Finset.sum_mul, blockInt]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : s ∈ Set.Ioc (rr t N i) (rr t N (i + 1)) <;> simp [h]
  have hFnL2 : ∀ N, IsProgressiveL2 P ℱ (fun s ω k => stepW t N c s ω * Φ s ω k) := fun N => by
    rw [← hFn_eq N]; exact (itoIntegral_finset_sum hW _ (hblkL2 N)).1
  -- identification of the discrete sums with the integral of the step integrand
  have hYN : ∀ N, ∀ᵐ ω ∂P, itoIntegral P ℱ W (fun s ω k => stepW t N c s ω * Φ s ω k) t ω =
      (Partition.dyadic 0 t ht N).sumIncrements
        (fun s s' => c s ω * (itoIntegral P ℱ W Φ s' ω - itoIntegral P ℱ W Φ s ω)) := by
    intro N
    have h1 := (itoIntegral_finset_sum hW _ (hblkL2 N)).2
    rw [hFn_eq N] at h1
    have h2 : ∀ᵐ ω ∂P, ∀ i : ℕ, i < 2 ^ N →
        itoIntegral P ℱ W (blockInt (rr t N i) (rr t N (i + 1)) (c (rr t N i)) Φ) t ω =
        c (rr t N i) ω * (itoIntegral P ℱ W Φ (rr t N (i + 1)) ω -
          itoIntegral P ℱ W Φ (rr t N i) ω) := by
      refine ae_all_iff.2 fun i => ?_
      by_cases hi : i < 2 ^ N
      · have hmem := rr_mem ht N i hi.le
        have hmem' := rr_mem ht N (i + 1) (Nat.succ_le_of_lt hi)
        filter_upwards [itoIntegral_blockInt hW hΦ hmem.1 (rr_mono ht N (Nat.le_succ i))
          (hc.adapted (rr t N i)) (fun ω => hCc _ ω) t] with ω h _
        rw [h, min_eq_right hmem.2, min_eq_right hmem'.2]
      · exact ae_of_all _ fun ω h => absurd h hi
    filter_upwards [h1, h2] with ω h1 h2
    rw [h1 t, dyadic_sumIncrements]
    exact Finset.sum_congr rfl fun i hi => h2 i (Finset.mem_range.1 hi)
  refine TendstoInMeasure.congr (fun N => hYN N) EventuallyEq.rfl ?_
  refine tendstoInMeasure_of_L2 (fun N => (adapted_itoIntegral P ℱ W _ t).mono (ℱ.le t) le_rfl)
    ((adapted_itoIntegral P ℱ W _ t).mono (ℱ.le t) le_rfl) ?_
  have hsub : ∀ N, ∫⁻ ω, ‖itoIntegral P ℱ W (fun s ω k => stepW t N c s ω * Φ s ω k) t ω -
      itoIntegral P ℱ W (fun s ω k => c s ω * Φ s ω k) t ω‖ₑ ^ 2 ∂P =
      sqIntegralOn P (fun s ω k => stepW t N c s ω * Φ s ω k - c s ω * Φ s ω k) t := by
    intro N
    have h1 := itoIntegral_sub hW (hFnL2 N) hcΦ
    have h2 := lintegral_itoIntegral_sq hW (isProgressiveL2_sub (hFnL2 N) hcΦ) t
    rw [← h2]
    refine lintegral_congr_ae ?_
    filter_upwards [h1] with ω h
    rw [h t]
  simp_rw [hsub]
  have hΦm := measurable_of_progressive hΦ.prog
  refine tendsto_sqIntegralOn_of_dominated_ae (P := P) (D := fun s ω => ‖2 * Cc‖ₑ ^ 2 * qn (Φ s ω)) t
    (fun N => measurable_of_progressive (hFnL2 N).prog) (measurable_of_progressive hcΦ.prog)
    (measurable_qn.comp hΦm |>.const_mul _) ?_ ?_ ?_
  · have hmq : Measurable fun ω => ∫⁻ s in Set.Icc 0 t, qn (Φ s ω) := measurable_sqInt hΦ.prog t
    have : ∫⁻ ω, (∫⁻ s in Set.Icc 0 t, ‖2 * Cc‖ₑ ^ 2 * qn (Φ s ω)) ∂P =
        ‖2 * Cc‖ₑ ^ 2 * sqIntegralOn P Φ t := by
      rw [sqIntegralOn_eq_qn, ← lintegral_const_mul _ hmq]
      refine lintegral_congr fun ω => ?_
      rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top enorm_ne_top)]
    rw [this]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top enorm_ne_top) (hΦ.sq t).ne
  · intro N
    refine ae_of_all _ fun ω s hs => ?_
    have e : (fun k => stepW t N c s ω * Φ s ω k) - (fun k => c s ω * Φ s ω k) =
        fun k => (stepW t N c s ω - c s ω) * Φ s ω k := by
      funext k; simp [sub_mul]
    show qn ((fun k => stepW t N c s ω * Φ s ω k) - (fun k => c s ω * Φ s ω k)) ≤ _
    rw [e, qn_mul_left]
    gcongr
    rw [← ofReal_norm, ← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := abs_stepW_le ht N hCc s ω
    have h2 := hCc s ω
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    calc |stepW t N c s ω - c s ω| ≤ |stepW t N c s ω| + |c s ω| := abs_sub _ _
      _ ≤ |2 * Cc| := by
        have : 0 ≤ Cc := (abs_nonneg _).trans h2
        rw [abs_of_nonneg (show (0 : ℝ) ≤ 2 * Cc by linarith)]; linarith
  · filter_upwards [hcont] with ω hω
    have h0 : ∀ᵐ s ∂(volume : Measure ℝ), s ∉ ({0} : Set ℝ) :=
      (Set.countable_singleton (0 : ℝ)).ae_notMem volume
    filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae h0] with s hs hs0
    have hpos : 0 < s := lt_of_le_of_ne hs.1 (fun h => hs0 (by simp [← h]))
    exact tendsto_pi_nhds.2 fun k => (stepW_tendsto ht hω hpos hs.2).mul_const (Φ s ω k)

theorem tendstoInMeasure_blockQV (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveL2 P ℱ Φ) {Φ' : ℝ → Ω → ι → ℝ} (hΦ' : IsProgressiveL2 P ℱ Φ')
    {t : ℝ} (ht : 0 ≤ t) {r r' : ℝ} (hr : 0 ≤ r) (hrr : r ≤ r') (hr't : r' ≤ t) :
    TendstoInMeasure P (fun N ω => (Partition.dyadic 0 t ht N).sumIncrements
      (fun s s' => (blkProc (fun x => itoIntegral P ℱ W Φ x ω) r r' s' -
            blkProc (fun x => itoIntegral P ℱ W Φ x ω) r r' s) *
          (blkProc (fun x => itoIntegral P ℱ W Φ' x ω) r r' s' -
            blkProc (fun x => itoIntegral P ℱ W Φ' x ω) r r' s))) atTop
      (fun ω => ∫ s in Set.Ioc r r', ∑ k, Φ s ω k * Φ' s ω k) := by
  have hind : ∀ {Ψ : ℝ → Ω → ι → ℝ}, IsProgressiveL2 P ℱ Ψ →
      IsProgressiveL2 P ℱ (fun s ω => Set.indicator (Set.Ioc r r') (fun _ => Ψ s ω) s) := by
    intro Ψ hΨ
    have := hΨ.mul_bdd (isProgressive_indicator_Ioc ℱ r r') (C := 1) (fun s ω => by
      by_cases h : s ∈ Set.Ioc r r' <;> simp [h])
    have e : (fun s ω => Set.indicator (Set.Ioc r r') (fun _ => Ψ s ω) s) =
        fun s ω k => (Set.Ioc r r').indicator (fun _ => (1 : ℝ)) s * Ψ s ω k := by
      funext s ω k
      by_cases h : s ∈ Set.Ioc r r' <;> simp [h]
    rw [e]; exact this
  have hmesh : Tendsto (fun m => (Partition.dyadic 0 t ht m).mesh) atTop (𝓝 0) := by
    simp only [Partition.mesh_dyadic, sub_zero]
    exact tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  have hmain := tendstoInMeasure_sumIncrements_mul hW (hind hΦ) (hind hΦ') ht
    (fun N => Partition.dyadic 0 t ht N) hmesh
  have h1 := itoIntegral_indicator_Ioc hW hΦ hr hrr
  have h2 := itoIntegral_indicator_Ioc hW hΦ' hr hrr
  refine TendstoInMeasure.congr (fun N => ?_) ?_ hmain
  · filter_upwards [h1, h2] with ω a b
    unfold Partition.sumIncrements
    refine Finset.sum_congr rfl fun i _ => ?_
    dsimp only
    rw [a, a, b, b]; rfl
  · refine Eventually.of_forall fun ω => ?_
    show covProcess _ _ t ω = _
    unfold covProcess
    have e : (fun s => ∑ k, Set.indicator (Set.Ioc r r') (fun _ => Φ s ω) s k *
        Set.indicator (Set.Ioc r r') (fun _ => Φ' s ω) s k) =
        Set.indicator (Set.Ioc r r') (fun s => ∑ k, Φ s ω k * Φ' s ω k) := by
      funext s
      by_cases h : s ∈ Set.Ioc r r' <;> simp [h]
    rw [e, setIntegral_indicator measurableSet_Ioc,
      Set.inter_eq_right.2 (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc hr hr't))]


section DetCoord

theorem sumIncrements_finset_sum {t : ℝ} (π : Partition 0 t) {γ : Type*} (S : Finset γ)
    (g : γ → ℝ → ℝ → ℝ) :
    π.sumIncrements (fun a a' => ∑ j ∈ S, g j a a') = ∑ j ∈ S, π.sumIncrements (g j) := by
  unfold Partition.sumIncrements
  exact Finset.sum_comm

theorem sumIncrements_mono {t : ℝ} (π : Partition 0 t) {g h : ℝ → ℝ → ℝ}
    (hgh : ∀ a a', g a a' ≤ h a a') : π.sumIncrements g ≤ π.sumIncrements h :=
  Finset.sum_le_sum fun i _ => hgh _ _

theorem sumIncrements_const_mul {t : ℝ} (π : Partition 0 t) (c : ℝ) (g : ℝ → ℝ → ℝ) :
    π.sumIncrements (fun a a' => c * g a a') = c * π.sumIncrements g := by
  unfold Partition.sumIncrements
  rw [Finset.mul_sum]

theorem ito_det_coord {T : ℝ} {U K : Set E} {f : ℝ → E → ℝ} (hf : IsC12On T U f)
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T)
    {X B : ℝ → E} {V : Fin (Module.finrank ℝ E) → ℝ → ℝ} {b : ℝ → E}
    (hXK : ∀ s ∈ Set.Icc 0 t, X s ∈ K)
    (hXBM : ∀ s ∈ Set.Icc 0 t, X s = B s + ∑ j, V j s • Module.finBasis ℝ E j)
    (hBc : ContinuousOn B (Set.Icc 0 t)) (hVc : ∀ j, ContinuousOn (V j) (Set.Icc 0 t))
    (hb : IntegrableOn b (Set.Icc 0 t))
    (hBinc : ∀ a a', 0 ≤ a → a ≤ a' → a' ≤ t → B a' - B a = ∫ s in Set.Ioc a a', b s)
    (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop)
    {Nj : Fin (Module.finrank ℝ E) → ℝ} {Qjl : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ}
    (H1 : ∀ j, Tendsto (fun n => (Partition.dyadic 0 t ht0 (φ n)).sumIncrements
      (fun a a' => fderiv ℝ (f a) (X a) (Module.finBasis ℝ E j) * (V j a' - V j a))) atTop (𝓝 (Nj j)))
    (H2 : ∀ j l, Tendsto (fun n => (Partition.dyadic 0 t ht0 (φ n)).sumIncrements
      (fun a a' => fderiv ℝ (fderiv ℝ (f a)) (X a) (Module.finBasis ℝ E j) (Module.finBasis ℝ E l) *
        ((V j a' - V j a) * (V l a' - V l a)))) atTop (𝓝 (Qjl j l)))
    (H3 : ∀ j, ∃ C : ℝ, ∀ᶠ n in atTop, (Partition.dyadic 0 t ht0 (φ n)).sumIncrements
      (fun a a' => (V j a' - V j a) ^ 2) ≤ C) :
    f t (X t) = f 0 (X 0) + (∫ s in Set.Icc 0 t, derivWithin (fun r => f r (X s)) (Set.Icc 0 T) s)
      + (∫ s in Set.Icc 0 t, fderiv ℝ (f s) (X s) (b s)) + ∑ j, Nj j + (∑ j, ∑ l, Qjl j l) / 2 := by
  set eb : Fin (Module.finrank ℝ E) → E := fun j => Module.finBasis ℝ E j with heb
  set M : ℝ → E := fun s => ∑ j, V j s • eb j with hM
  have hMc : ContinuousOn M (Set.Icc 0 t) :=
    continuousOn_finset_sum _ fun j _ => (hVc j).smul continuousOn_const
  have hMdiff : ∀ a a', M a' - M a = ∑ j, (V j a' - V j a) • eb j := by
    intro a a'
    simp only [hM, ← Finset.sum_sub_distrib, sub_smul]
  have hmesh : Tendsto (fun n => (Partition.dyadic 0 t ht0 (φ n)).mesh) atTop (𝓝 0) := by
    simp only [Partition.mesh_dyadic, sub_zero]
    exact (tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)).comp hφ
  have H1' : Tendsto (fun n => (Partition.dyadic 0 t ht0 (φ n)).sumIncrements fun a a' =>
      fderiv ℝ (f a) (X a) (M a' - M a)) atTop (𝓝 (∑ j, Nj j)) := by
    have e : ∀ n, (Partition.dyadic 0 t ht0 (φ n)).sumIncrements (fun a a' =>
        fderiv ℝ (f a) (X a) (M a' - M a)) = ∑ j, (Partition.dyadic 0 t ht0 (φ n)).sumIncrements
          (fun a a' => fderiv ℝ (f a) (X a) (eb j) * (V j a' - V j a)) := by
      intro n
      rw [← sumIncrements_finset_sum]
      unfold Partition.sumIncrements
      refine Finset.sum_congr rfl fun i _ => ?_
      dsimp only
      rw [hMdiff, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, smul_eq_mul, mul_comm]
    simp_rw [e]
    exact tendsto_finset_sum _ fun j _ => H1 j
  have H2' : Tendsto (fun n => (Partition.dyadic 0 t ht0 (φ n)).sumIncrements fun a a' =>
      fderiv ℝ (fderiv ℝ (f a)) (X a) (M a' - M a) (M a' - M a)) atTop
      (𝓝 (∑ j, ∑ l, Qjl j l)) := by
    have e : ∀ n, (Partition.dyadic 0 t ht0 (φ n)).sumIncrements (fun a a' =>
        fderiv ℝ (fderiv ℝ (f a)) (X a) (M a' - M a) (M a' - M a)) =
        ∑ j, ∑ l, (Partition.dyadic 0 t ht0 (φ n)).sumIncrements
          (fun a a' => fderiv ℝ (fderiv ℝ (f a)) (X a) (eb j) (eb l) *
            ((V j a' - V j a) * (V l a' - V l a))) := by
      intro n
      simp_rw [← sumIncrements_finset_sum]
      unfold Partition.sumIncrements
      refine Finset.sum_congr rfl fun i _ => ?_
      dsimp only
      rw [hMdiff]
      simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
        smul_eq_mul]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
    simp_rw [e]
    exact tendsto_finset_sum _ fun j _ => tendsto_finset_sum _ fun l _ => H2 j l
  have H3' : ∃ C : ℝ, ∀ᶠ n in atTop, (Partition.dyadic 0 t ht0 (φ n)).sumIncrements
      (fun a a' => ‖M a' - M a‖ ^ 2) ≤ C := by
    choose C hC using H3
    set mm : ℝ := ∑ j, ‖eb j‖ with hmm
    refine ⟨mm ^ 2 * Module.finrank ℝ E * ∑ j, C j, ?_⟩
    have hev : ∀ᶠ n in atTop, ∀ j, (Partition.dyadic 0 t ht0 (φ n)).sumIncrements
        (fun a a' => (V j a' - V j a) ^ 2) ≤ C j := eventually_all.2 hC
    filter_upwards [hev] with n hn
    have hmm0 : 0 ≤ mm := Finset.sum_nonneg fun j _ => norm_nonneg _
    have hpt : ∀ a a', ‖M a' - M a‖ ^ 2 ≤ mm ^ 2 * Module.finrank ℝ E *
        ∑ j, (V j a' - V j a) ^ 2 := by
      intro a a'
      rw [hMdiff]
      have h1 : ‖∑ j, (V j a' - V j a) • eb j‖ ≤ mm * ∑ j, |V j a' - V j a| := by
        refine (norm_sum_le _ _).trans ?_
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun j _ => ?_
        rw [norm_smul, Real.norm_eq_abs, mul_comm]
        refine mul_le_mul ?_ le_rfl (abs_nonneg _) hmm0
        exact Finset.single_le_sum (f := fun j => ‖eb j‖) (fun j _ => norm_nonneg _)
          (Finset.mem_univ j)
      have h2 : (∑ j, |V j a' - V j a|) ^ 2 ≤ Module.finrank ℝ E * ∑ j, (V j a' - V j a) ^ 2 := by
        have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun j => |V j a' - V j a|)
        simpa [sq_abs] using this
      calc ‖∑ j, (V j a' - V j a) • eb j‖ ^ 2 ≤ (mm * ∑ j, |V j a' - V j a|) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h1 2
        _ = mm ^ 2 * (∑ j, |V j a' - V j a|) ^ 2 := by ring
        _ ≤ mm ^ 2 * (Module.finrank ℝ E * ∑ j, (V j a' - V j a) ^ 2) := by gcongr
        _ = _ := by ring
    calc (Partition.dyadic 0 t ht0 (φ n)).sumIncrements (fun a a' => ‖M a' - M a‖ ^ 2)
        ≤ (Partition.dyadic 0 t ht0 (φ n)).sumIncrements (fun a a' => mm ^ 2 * Module.finrank ℝ E *
          ∑ j, (V j a' - V j a) ^ 2) := sumIncrements_mono _ hpt
      _ = mm ^ 2 * Module.finrank ℝ E * ∑ j, (Partition.dyadic 0 t ht0 (φ n)).sumIncrements
          (fun a a' => (V j a' - V j a) ^ 2) := by
        rw [sumIncrements_const_mul, sumIncrements_finset_sum]
      _ ≤ _ := by gcongr with j; exact hn j
  exact ito_deterministic hf hU hK hKU ht0 htT hXK hXBM hBc hMc hb hBinc
    (fun n => Partition.dyadic 0 t ht0 (φ n)) hmesh H1' H2' H3'

end DetCoord


section Det2

theorem blk0_eq {t : ℝ} (ht : 0 ≤ t) (N : ℕ) (u v : ℝ → ℝ) :
    (Partition.dyadic 0 t ht N).sumIncrements
      (fun s s' => (blkProc u (rr t 0 0) (rr t 0 (0 + 1)) s' - blkProc u (rr t 0 0) (rr t 0 (0 + 1)) s) *
        (blkProc v (rr t 0 0) (rr t 0 (0 + 1)) s' - blkProc v (rr t 0 0) (rr t 0 (0 + 1)) s)) =
    (Partition.dyadic 0 t ht N).sumIncrements (fun s s' => (u s' - u s) * (v s' - v s)) := by
  rw [dyadic_sumIncrements, dyadic_sumIncrements]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < 2 ^ N := Finset.mem_range.1 hi
  have h0 := rr_mem ht N i hi'.le
  have h1 := rr_mem ht N (i + 1) (Nat.succ_le_of_lt hi')
  have hle := rr_mono ht N (Nat.le_succ i)
  have e0 : rr t 0 0 = 0 := by simp [rr]
  have e1 : rr t 0 (0 + 1) = t := by simp [rr]
  rw [e0, e1, blkProc_in h0.1 hle h1.2, blkProc_in h0.1 hle h1.2]

theorem bound_from_block {t : ℝ} (ht : 0 ≤ t) (u : ℝ → ℝ) (φ : ℕ → ℕ) {L : ℝ}
    (h : Tendsto (fun n => (Partition.dyadic 0 t ht (φ n)).sumIncrements
      (fun s s' => (blkProc u (rr t 0 0) (rr t 0 (0 + 1)) s' - blkProc u (rr t 0 0) (rr t 0 (0 + 1)) s) *
        (blkProc u (rr t 0 0) (rr t 0 (0 + 1)) s' - blkProc u (rr t 0 0) (rr t 0 (0 + 1)) s)))
      atTop (𝓝 L)) :
    ∃ C : ℝ, ∀ᶠ n in atTop, (Partition.dyadic 0 t ht (φ n)).sumIncrements
      (fun s s' => (u s' - u s) ^ 2) ≤ C := by
  refine ⟨L + 1, ?_⟩
  filter_upwards [h.eventually (gt_mem_nhds (lt_add_one L))] with n hn
  rw [blk0_eq] at hn
  refine le_trans (le_of_eq ?_) hn.le
  unfold Partition.sumIncrements
  exact Finset.sum_congr rfl fun i _ => by ring

theorem drift_increment {bp : ℝ → E} {a a' : ℝ} (ha : 0 ≤ a) (haa' : a ≤ a')
    (hb : IntegrableOn bp (Set.Icc 0 a')) :
    (∫ s in Set.Icc 0 a', bp s) - (∫ s in Set.Icc 0 a, bp s) = ∫ s in Set.Ioc a a', bp s := by
  have hU : Set.Icc (0 : ℝ) a ∪ Set.Ioc a a' = Set.Icc 0 a' := Set.Icc_union_Ioc_eq_Icc ha haa'
  have hdisj : Disjoint (Set.Icc (0 : ℝ) a) (Set.Ioc a a') :=
    Set.disjoint_left.2 fun x hx hx' => absurd hx.2 (not_le.2 hx'.1)
  rw [← hU, setIntegral_union hdisj measurableSet_Ioc
    (hb.mono_set (Set.Icc_subset_Icc_right haa')) (hb.mono_set (fun x hx => ⟨ha.trans hx.1.le, hx.2⟩))]
  abel

theorem ito_path_integrable {T : ℝ} {U K : Set E} {f : ℝ → E → ℝ} (hf : IsC12On T U f)
    (hKU : K ⊆ U) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) {Xp : ℝ → E}
    (hXK : ∀ s ∈ Set.Icc 0 t, Xp s ∈ K) (hXc : ContinuousOn Xp (Set.Icc 0 t)) {bp : ℝ → E}
    (hb : IntegrableOn bp (Set.Icc 0 t)) :
    IntegrableOn (fun s => derivWithin (fun r => f r (Xp s)) (Set.Icc 0 T) s) (Set.Icc 0 t) ∧
      IntegrableOn (fun s => fderiv ℝ (f s) (Xp s) (bp s)) (Set.Icc 0 t) := by
  have hcompt : IsCompact (Set.Icc (0:ℝ) t) := isCompact_Icc
  have hmapsU : ∀ s ∈ Set.Icc (0:ℝ) t, (s, Xp s) ∈ Set.Icc (0:ℝ) T ×ˢ U :=
    fun s hs => ⟨⟨hs.1, hs.2.trans htT⟩, hKU (hXK s hs)⟩
  have hpair : ContinuousOn (fun s => (s, Xp s)) (Set.Icc (0:ℝ) t) :=
    continuousOn_id.prodMk hXc
  have hDt : ContinuousOn (fun s => derivWithin (fun r => f r (Xp s)) (Set.Icc 0 T) s)
      (Set.Icc 0 t) := hf.cont_deriv.comp hpair hmapsU
  have hDf : ContinuousOn (fun s => fderiv ℝ (f s) (Xp s)) (Set.Icc 0 t) :=
    hf.cont_fderiv.comp hpair hmapsU
  refine ⟨hDt.integrableOn_Icc, ?_⟩
  obtain ⟨C₁, hC₁⟩ := exists_bound_clm hcompt hDf
  have hmeas : AEStronglyMeasurable (fun s => fderiv ℝ (f s) (Xp s) (bp s))
      (volume.restrict (Set.Icc 0 t)) :=
    (ContinuousLinearMap.id ℝ (E →L[ℝ] ℝ)).aestronglyMeasurable_comp₂
      (hDf.aestronglyMeasurable measurableSet_Icc) hb.aestronglyMeasurable
  refine Integrable.mono' (hb.norm.const_mul C₁) hmeas ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ fun s hs => ?_)
  calc ‖fderiv ℝ (f s) (Xp s) (bp s)‖ ≤ ‖fderiv ℝ (f s) (Xp s)‖ * ‖bp s‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ C₁ * ‖bp s‖ := by gcongr; exact hC₁ s hs

theorem bilin_expand (B : E →L[ℝ] E →L[ℝ] ℝ) (x : E) :
    B x x = ∑ j, ∑ l, (coordCLM j x * coordCLM l x) * B (Module.finBasis ℝ E j) (Module.finBasis ℝ E l) := by
  have h := sum_coordCLM_smul x
  conv_lhs => rw [← h]
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring

theorem ito_det2 {T : ℝ} {U K : Set E} {f : ℝ → E → ℝ} (hf : IsC12On T U f)
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T)
    {Xp bp : ℝ → E} {Φp : ℝ → ι → E} {X0 : E} {V : Fin (Module.finrank ℝ E) → ℝ → ℝ}
    (hXK : ∀ s ∈ Set.Icc 0 t, Xp s ∈ K)
    (hXdec : ∀ s ∈ Set.Icc 0 t, Xp s = (X0 + ∫ u in Set.Icc 0 s, bp u) +
      ∑ j, V j s • Module.finBasis ℝ E j)
    (hbint : ∀ N : ℕ, IntegrableOn bp (Set.Icc 0 (N : ℝ)))
    (hVc : ∀ j, Continuous (V j))
    (hgint : ∀ j l, IntegrableOn
      (fun s => ∑ k, coordCLM j (Φp s k) * coordCLM l (Φp s k)) (Set.Icc 0 t))
    (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop) {Nj : Fin (Module.finrank ℝ E) → ℝ}
    (H1 : ∀ j, Tendsto (fun n => (Partition.dyadic 0 t ht0 (φ n)).sumIncrements
      (fun a a' => fderiv ℝ (f a) (Xp a) (Module.finBasis ℝ E j) * (V j a' - V j a)))
      atTop (𝓝 (Nj j)))
    (hB : ∀ j l, ∀ m, ∀ k : ℕ, k < 2 ^ m →
      Tendsto (fun n => (Partition.dyadic 0 t ht0 (φ n)).sumIncrements
        (fun s s' => (blkProc (V j) (rr t m k) (rr t m (k + 1)) s' -
              blkProc (V j) (rr t m k) (rr t m (k + 1)) s) *
            (blkProc (V l) (rr t m k) (rr t m (k + 1)) s' -
              blkProc (V l) (rr t m k) (rr t m (k + 1)) s))) atTop
        (𝓝 (∫ s in Set.Ioc (rr t m k) (rr t m (k + 1)),
          ∑ k', coordCLM j (Φp s k') * coordCLM l (Φp s k')))) :
    IntegrableOn (fun s => derivWithin (fun r => f r (Xp s)) (Set.Icc 0 T) s +
        fderiv ℝ (f s) (Xp s) (bp s) +
        (1 / 2) * ∑ k, fderiv ℝ (fderiv ℝ (f s)) (Xp s) (Φp s k) (Φp s k)) (Set.Icc 0 t) ∧
    f t (Xp t) = f 0 (Xp 0) + (∫ s in Set.Icc 0 t, (derivWithin (fun r => f r (Xp s)) (Set.Icc 0 T) s +
        fderiv ℝ (f s) (Xp s) (bp s) +
        (1 / 2) * ∑ k, fderiv ℝ (fderiv ℝ (f s)) (Xp s) (Φp s k) (Φp s k))) + ∑ j, Nj j := by
  have hb : IntegrableOn bp (Set.Icc 0 t) :=
    (hbint ⌈t⌉₊).mono_set (Set.Icc_subset_Icc_right (Nat.le_ceil t))
  have hBc : ContinuousOn (fun s => X0 + ∫ u in Set.Icc 0 s, bp u) (Set.Icc 0 t) :=
    (continuous_const.add (continuous_driftIntegral hbint)).continuousOn
  have hVcon : ∀ j, ContinuousOn (V j) (Set.Icc 0 t) := fun j => (hVc j).continuousOn
  have hXc : ContinuousOn Xp (Set.Icc 0 t) :=
    (hBc.add (continuousOn_finset_sum _ fun j _ => (hVcon j).smul continuousOn_const)).congr hXdec
  have hBinc : ∀ a a', 0 ≤ a → a ≤ a' → a' ≤ t →
      (X0 + ∫ u in Set.Icc 0 a', bp u) - (X0 + ∫ u in Set.Icc 0 a, bp u) = ∫ s in Set.Ioc a a', bp s := by
    intro a a' ha haa' ha't
    rw [add_sub_add_left_eq_sub]
    exact drift_increment ha haa' (hb.mono_set (Set.Icc_subset_Icc_right ha't))
  have hmapsU : ∀ s ∈ Set.Icc (0:ℝ) t, (s, Xp s) ∈ Set.Icc (0:ℝ) T ×ˢ U :=
    fun s hs => ⟨⟨hs.1, hs.2.trans htT⟩, hKU (hXK s hs)⟩
  have hpair : ContinuousOn (fun s => (s, Xp s)) (Set.Icc (0:ℝ) t) :=
    continuousOn_id.prodMk hXc
  have hDf2 : ContinuousOn (fun s => fderiv ℝ (fderiv ℝ (f s)) (Xp s)) (Set.Icc 0 t) :=
    hf.cont_fderiv₂.comp hpair hmapsU
  have hA : ∀ j l, ContinuousOn (fun s => fderiv ℝ (fderiv ℝ (f s)) (Xp s) (Module.finBasis ℝ E j) (Module.finBasis ℝ E l))
      (Set.Icc 0 t) := fun j l =>
    (hDf2.clm_apply continuousOn_const).clm_apply continuousOn_const
  -- bounds
  have hbound : ∀ j, ∃ C : ℝ, ∀ᶠ n in atTop, (Partition.dyadic 0 t ht0 (φ n)).sumIncrements
      (fun a a' => (V j a' - V j a) ^ 2) ≤ C := fun j =>
    bound_from_block ht0 (V j) φ (hB j j 0 0 (by norm_num))
  choose C hC using hbound
  -- second order
  have H2 : ∀ j l, Tendsto (fun n => (Partition.dyadic 0 t ht0 (φ n)).sumIncrements
      (fun a a' => fderiv ℝ (fderiv ℝ (f a)) (Xp a) (Module.finBasis ℝ E j) (Module.finBasis ℝ E l) *
        ((V j a' - V j a) * (V l a' - V l a)))) atTop
      (𝓝 (∫ s in Set.Icc 0 t, fderiv ℝ (fderiv ℝ (f s)) (Xp s) (Module.finBasis ℝ E j) (Module.finBasis ℝ E l) *
        ∑ k, coordCLM j (Φp s k) * coordCLM l (Φp s k))) := fun j l =>
    weighted_qv_det ht0 (hA j l) (hgint j l) (C := max (C j) (C l)) φ hφ (hB j l)
      ((hC j).mono fun n hn => hn.trans (le_max_left _ _))
      ((hC l).mono fun n hn => hn.trans (le_max_right _ _))
  have hmain := ito_det_coord hf hU hK hKU ht0 htT hXK hXdec hBc hVcon hb hBinc φ hφ H1 H2
    (fun j => ⟨C j, hC j⟩)
  obtain ⟨hdw, hfb⟩ := ito_path_integrable hf hKU ht0 htT hXK hXc hb
  have hgA : ∀ j l, IntegrableOn (fun s => fderiv ℝ (fderiv ℝ (f s)) (Xp s) (Module.finBasis ℝ E j) (Module.finBasis ℝ E l) *
      ∑ k, coordCLM j (Φp s k) * coordCLM l (Φp s k)) (Set.Icc 0 t) := fun j l =>
    (hgint j l).continuousOn_mul (hA j l) isCompact_Icc
  have hexp : ∀ s, ∑ k, fderiv ℝ (fderiv ℝ (f s)) (Xp s) (Φp s k) (Φp s k) =
      ∑ j, ∑ l, fderiv ℝ (fderiv ℝ (f s)) (Xp s) (Module.finBasis ℝ E j) (Module.finBasis ℝ E l) *
        ∑ k, coordCLM j (Φp s k) * coordCLM l (Φp s k) := by
    intro s
    simp_rw [bilin_expand (fderiv ℝ (fderiv ℝ (f s)) (Xp s))]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hqint : IntegrableOn (fun s => ∑ j, ∑ l, fderiv ℝ (fderiv ℝ (f s)) (Xp s) (Module.finBasis ℝ E j) (Module.finBasis ℝ E l) *
      ∑ k, coordCLM j (Φp s k) * coordCLM l (Φp s k)) (Set.Icc 0 t) :=
    integrable_finset_sum _ fun j _ => integrable_finset_sum _ fun l _ => hgA j l
  have hdrift : IntegrableOn (fun s => derivWithin (fun r => f r (Xp s)) (Set.Icc 0 T) s +
        fderiv ℝ (f s) (Xp s) (bp s) +
        (1 / 2) * ∑ k, fderiv ℝ (fderiv ℝ (f s)) (Xp s) (Φp s k) (Φp s k)) (Set.Icc 0 t) := by
    simp_rw [hexp]
    exact (hdw.add hfb).add (hqint.const_mul _)
  refine ⟨hdrift, ?_⟩
  rw [hmain]
  simp_rw [hexp]
  have hs1 : IntegrableOn (fun s => derivWithin (fun r => f r (Xp s)) (Set.Icc 0 T) s +
      fderiv ℝ (f s) (Xp s) (bp s)) (Set.Icc 0 t) := hdw.add hfb
  have hs2 : IntegrableOn (fun s => (1 / 2 : ℝ) * ∑ j, ∑ l,
      fderiv ℝ (fderiv ℝ (f s)) (Xp s) (Module.finBasis ℝ E j) (Module.finBasis ℝ E l) *
        ∑ k, coordCLM j (Φp s k) * coordCLM l (Φp s k)) (Set.Icc 0 t) := hqint.const_mul _
  rw [integral_add hs1 hs2, integral_add hdw hfb, integral_const_mul,
    integral_finset_sum _ (fun j _ => integrable_finset_sum _ fun l _ => hgA j l)]
  simp_rw [integral_finset_sum _ (fun l _ => hgA _ l)]
  ring

end Det2

end Tools


/-! ### Itô's formula -/

/-- The drift of Itô's formula,
`∂_s f(s, X_s) + D_x f(s, X_s)[b_s] + ½ ∑_k D_x² f(s, X_s)[Φ^k_s, Φ^k_s]`
(time derivative within `[0, T]`). -/
def itoDrift (T : ℝ) (f : ℝ → E → ℝ) (X : ℝ → Ω → E) (b : ℝ → Ω → E) (Φ : ℝ → Ω → ι → E) :
    ℝ → Ω → ℝ :=
  fun s ω => derivWithin (fun r => f r (X s ω)) (Set.Icc 0 T) s +
    fderiv ℝ (f s) (X s ω) (b s ω) +
    (1 / 2) * ∑ k, fderiv ℝ (fderiv ℝ (f s)) (X s ω) (Φ s ω k) (Φ s ω k)

/-- The integrand of the martingale term of Itô's formula, `k ↦ 1_{[0,T]}(s) D_x f(s, X_s)[Φ^k_s]`,
restricted to the times `s` at which `X_s ∈ K` (`K = univ` in the global formula; the indicator
makes the integrand measurable in the localised formula, where `f` is only regular on `U ⊇ K`). -/
def itoIntegrand (T : ℝ) (K : Set E) (f : ℝ → E → ℝ) (X : ℝ → Ω → E) (Φ : ℝ → Ω → ι → E) :
    ℝ → Ω → ι → ℝ :=
  fun s ω k => Set.indicator (Set.Icc 0 T)
    (fun s => Set.indicator {ω | X s ω ∈ K} (fun ω => fderiv ℝ (f s) (X s ω) (Φ s ω k)) ω) s

section CFun

/-- The `j`-th coefficient of the Itô integrand: `1_{[0,T]}(s) 1_{X_s ∈ K} D_x f(s, X_s)[e_j]`. -/
def cfun (T : ℝ) (K : Set E) (f : ℝ → E → ℝ) (X : ℝ → Ω → E) (j : Fin (Module.finrank ℝ E)) :
    ℝ → Ω → ℝ :=
  fun s ω => Set.indicator (Set.Icc 0 T) (fun s =>
    Set.indicator {ω | X s ω ∈ K} (fun ω => fderiv ℝ (f s) (X s ω) (Module.finBasis ℝ E j)) ω) s

theorem cfun_eq (T : ℝ) (K : Set E) (f : ℝ → E → ℝ) (X : ℝ → Ω → E) (j : Fin (Module.finrank ℝ E))
    (s : ℝ) (ω : Ω) :
    cfun T K f X j s ω = Set.indicator (Set.Icc 0 T ×ˢ K)
      (fun p : ℝ × E => fderiv ℝ (f p.1) p.2 (Module.finBasis ℝ E j)) (s, X s ω) := by
  unfold cfun
  by_cases h1 : s ∈ Set.Icc 0 T <;> by_cases h2 : X s ω ∈ K <;> simp [Set.indicator, h1, h2]

theorem cfun_bound {T : ℝ} {U K : Set E} {f : ℝ → E → ℝ} (hf : IsC12On T U f)
    (hK : IsCompact K) (hKU : K ⊆ U) (X : ℝ → Ω → E) :
    ∃ C : ℝ, ∀ j s ω, |cfun T K f X j s ω| ≤ C := by
  have hS : IsCompact (Set.Icc (0 : ℝ) T ×ˢ K) := isCompact_Icc.prod hK
  have hcont : ∀ j : Fin (Module.finrank ℝ E), ∃ C : ℝ, ∀ p ∈ Set.Icc (0 : ℝ) T ×ˢ K,
      ‖fderiv ℝ (f p.1) p.2 (Module.finBasis ℝ E j)‖ ≤ C := fun j => by
    refine hS.exists_bound_of_continuousOn ?_
    exact (hf.cont_fderiv.mono (Set.prod_mono subset_rfl hKU)).clm_apply continuousOn_const
  choose C hC using hcont
  refine ⟨∑ j, |C j|, fun j s ω => ?_⟩
  rw [cfun_eq]
  by_cases h : (s, X s ω) ∈ Set.Icc (0 : ℝ) T ×ˢ K
  · rw [Set.indicator_of_mem h]
    exact (hC j _ h).trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun j => |C j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)))
  · rw [Set.indicator_of_notMem h]
    simpa using Finset.sum_nonneg fun j _ => abs_nonneg (C j)

theorem measurable_cfun_fn {T : ℝ} {U K : Set E} {f : ℝ → E → ℝ} (hf : IsC12On T U f)
    (hK : IsClosed K) (hKU : K ⊆ U) (j : Fin (Module.finrank ℝ E)) :
    Measurable (Set.indicator (Set.Icc 0 T ×ˢ K)
      (fun p : ℝ × E => fderiv ℝ (f p.1) p.2 (Module.finBasis ℝ E j))) := by
  classical
  rw [← Set.piecewise_eq_indicator]
  refine ContinuousOn.measurable_piecewise ?_ continuous_zero.continuousOn
    (isClosed_Icc.prod hK).measurableSet
  exact (hf.cont_fderiv.mono (Set.prod_mono subset_rfl hKU)).clm_apply continuousOn_const

variable {P : Measure Ω} {ℱ : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ι → ℝ}

theorem isProgressive_cfun {T : ℝ} {U K : Set E} {f : ℝ → E → ℝ} (hf : IsC12On T U f)
    (hK : IsClosed K) (hKU : K ⊆ U) {X : ℝ → Ω → E} (hX : IsProgressive ℱ X)
    (j : Fin (Module.finrank ℝ E)) : IsProgressive ℱ (cfun T K f X j) := by
  have hm := measurable_cfun_fn hf hK hKU j
  intro i
  letI : MeasurableSpace (Set.Iic i × Ω) := Subtype.instMeasurableSpace.prod (ℱ i)
  have h1 : Measurable fun p : Set.Iic i × Ω => ((p.1 : ℝ), X p.1 p.2) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk (hX i)
  have := hm.comp h1
  convert this using 1
  funext p
  simp [cfun_eq]

theorem continuousOn_cfun {T : ℝ} {U K : Set E} {f : ℝ → E → ℝ} (hf : IsC12On T U f)
    (hKU : K ⊆ U) {X : ℝ → Ω → E} {ω : Ω} {t : ℝ} (htT : t ≤ T)
    (hXK : ∀ s ∈ Set.Icc 0 T, X s ω ∈ K) (hXc : ContinuousOn (fun s => X s ω) (Set.Icc 0 t))
    (j : Fin (Module.finrank ℝ E)) : ContinuousOn (fun s => cfun T K f X j s ω) (Set.Icc 0 t) := by
  have hmaps : ∀ s ∈ Set.Icc (0 : ℝ) t, (s, X s ω) ∈ Set.Icc (0 : ℝ) T ×ˢ U :=
    fun s hs => ⟨⟨hs.1, hs.2.trans htT⟩, hKU (hXK s ⟨hs.1, hs.2.trans htT⟩)⟩
  have hpair : ContinuousOn (fun s => (s, X s ω)) (Set.Icc (0 : ℝ) t) :=
    continuousOn_id.prodMk hXc
  have := (hf.cont_fderiv.comp hpair hmaps).clm_apply
    (continuousOn_const (c := Module.finBasis ℝ E j))
  refine this.congr fun s hs => ?_
  have hsT : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans htT⟩
  rw [cfun_eq, Set.indicator_of_mem (show (s, X s ω) ∈ Set.Icc (0 : ℝ) T ×ˢ K from ⟨hsT, hXK s hsT⟩)]
  rfl

theorem itoIntegrand_eq_sum (T : ℝ) (K : Set E) (f : ℝ → E → ℝ) (X : ℝ → Ω → E)
    (Φ : ℝ → Ω → ι → E) :
    itoIntegrand T K f X Φ = fun s ω k => ∑ j, cfun T K f X j s ω * coordCLM j (Φ s ω k) := by
  funext s ω k
  unfold itoIntegrand cfun
  by_cases h1 : s ∈ Set.Icc 0 T <;> by_cases h2 : X s ω ∈ K
  · simp only [Set.indicator_of_mem h1, Set.indicator, Set.mem_setOf_eq, h2, if_true]
    conv_lhs => rw [← sum_coordCLM_smul (Φ s ω k)]
    simp [map_sum, map_smul, mul_comm]
  · simp [Set.indicator, h1, h2]
  · simp [Set.indicator, h1]
  · simp [Set.indicator, h1]

end CFun

section Core

variable {P : Measure Ω} {ℱ : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ι → ℝ}

theorem dyadic_sumIncrements_congr {t : ℝ} (ht : 0 ≤ t) (N : ℕ) {g g' : ℝ → ℝ → ℝ}
    (h : ∀ a ∈ Set.Icc 0 t, ∀ a' ∈ Set.Icc 0 t, g a a' = g' a a') :
    (Partition.dyadic 0 t ht N).sumIncrements g = (Partition.dyadic 0 t ht N).sumIncrements g' := by
  rw [dyadic_sumIncrements, dyadic_sumIncrements]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.1 hi
  exact h _ (rr_mem ht N i hi'.le) _ (rr_mem ht N (i + 1) hi')

/-- The block quadratic-variation sums along dyadic partitions. -/
def blkSeq (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → ι → ℝ)
    (Ψ Ψ' : ℝ → Ω → ι → ℝ) (t : ℝ) (ht : 0 ≤ t) (r r' : ℝ) : ℕ → Ω → ℝ :=
  fun N ω => (Partition.dyadic 0 t ht N).sumIncrements
      (fun s s' => (blkProc (fun x => itoIntegral P ℱ W Ψ x ω) r r' s' -
            blkProc (fun x => itoIntegral P ℱ W Ψ x ω) r r' s) *
          (blkProc (fun x => itoIntegral P ℱ W Ψ' x ω) r r' s' -
            blkProc (fun x => itoIntegral P ℱ W Ψ' x ω) r r' s))

/-- The step-weight sums along dyadic partitions. -/
def stepSeq (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → ι → ℝ)
    (Ψ : ℝ → Ω → ι → ℝ) (c : ℝ → Ω → ℝ) (t : ℝ) (ht : 0 ≤ t) : ℕ → Ω → ℝ :=
  fun N ω => (Partition.dyadic 0 t ht N).sumIncrements
      (fun s s' => c s ω * (itoIntegral P ℱ W Ψ s' ω - itoIntegral P ℱ W Ψ s ω))


theorem ito_core_fixed [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) {T : ℝ}
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) {f : ℝ → E → ℝ}
    (hf : IsC12On T U f) {X : ℝ → Ω → E} (hXp : IsProgressive ℱ X) {b : ℝ → Ω → E}
    {Φ : ℝ → Ω → ι → E}
    (hΦ : ∀ j, IsProgressiveL2 P ℱ (fun s ω k => coordCLM j (Φ s ω k)))
    (hb : ∀ N : ℕ, ∀ᵐ ω ∂P, IntegrableOn (fun s => b s ω) (Set.Icc 0 (N : ℝ)))
    (hXK : ∀ᵐ ω ∂P, (∀ s ∈ Set.Icc 0 T, X s ω ∈ K) ∨ (∀ s ∈ Set.Icc 0 T, X s ω ∉ K))
    (hXdec : ∀ᵐ ω ∂P, ∀ s, X s ω = (X 0 ω + ∫ u in Set.Icc 0 s, b u ω) +
      ∑ j, itoIntegral P ℱ W (fun s ω k => coordCLM j (Φ s ω k)) s ω • Module.finBasis ℝ E j)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ∀ᵐ ω ∂P, (∀ s ∈ Set.Icc 0 T, X s ω ∈ K) →
      IntegrableOn (fun s => itoDrift T f X b Φ s ω) (Set.Icc 0 t) ∧
      f t (X t ω) = f 0 (X 0 ω) + (∫ s in Set.Icc 0 t, itoDrift T f X b Φ s ω) +
        itoIntegral P ℱ W (itoIntegrand T K f X Φ) t ω := by
  obtain ⟨Cc, hCc⟩ := cfun_bound hf hK hKU X
  have hcprog := fun j => isProgressive_cfun hf hK.isClosed hKU hXp j
  have hcΦ : ∀ j, IsProgressiveL2 P ℱ
      (fun s ω k => cfun T K f X j s ω * coordCLM j (Φ s ω k)) :=
    fun j => (hΦ j).mul_bdd (hcprog j) (hCc j)
  have hbae : ∀ᵐ ω ∂P, ∀ N : ℕ, IntegrableOn (fun s => b s ω) (Set.Icc 0 (N : ℝ)) :=
    ae_all_iff.2 hb
  -- continuity of the path
  have hcontX : ∀ᵐ ω ∂P, ContinuousOn (fun s => X s ω) (Set.Icc 0 t) := by
    filter_upwards [hbae, hXdec] with ω h1 h2
    have : Continuous fun s => X s ω := by
      have h3 : Continuous fun s => (X 0 ω + ∫ u in Set.Icc 0 s, b u ω) +
          ∑ j, itoIntegral P ℱ W (fun s ω k => coordCLM j (Φ s ω k)) s ω • Module.finBasis ℝ E j :=
        (continuous_const.add (continuous_driftIntegral h1)).add
          (continuous_finsetSum _ fun j _ => (continuous_itoIntegral P ℱ W _ ω).smul continuous_const)
      exact h3.congr fun s => (h2 s).symm
    exact this.continuousOn
  have hcontc : ∀ j, ∀ᵐ ω ∂P, ContinuousOn (fun s => cfun T K f X j s ω) (Set.Icc 0 t) := by
    intro j
    filter_upwards [hcontX, hXK] with ω h1 h2
    rcases h2 with h2 | h2
    · exact continuousOn_cfun hf hKU htT h2 h1 j
    · refine (continuousOn_const (c := (0 : ℝ))).congr fun s hs => ?_
      rw [cfun_eq, Set.indicator_of_notMem (fun h => h2 s ⟨hs.1, hs.2.trans htT⟩ h.2)]
  have hgint : ∀ j l, ∀ᵐ ω ∂P, ∀ T' : ℝ, IntegrableOn
      (fun s => ∑ k, coordCLM j (Φ s ω k) * coordCLM l (Φ s ω k)) (Set.Icc 0 T') :=
    fun j l => ae_integrableOn_mul (hΦ j).locL2 (hΦ l).locL2
  -- the family of sequences
  let κ := (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) × {p : ℕ × ℕ // p.2 < 2 ^ p.1}) ⊕
    Fin (Module.finrank ℝ E)
  let Y : κ → ℕ → Ω → ℝ := Sum.elim
    (fun q => blkSeq P ℱ W (fun s ω k => coordCLM q.1 (Φ s ω k))
      (fun s ω k => coordCLM q.2.1 (Φ s ω k)) t ht0
      (rr t q.2.2.1.1 q.2.2.1.2) (rr t q.2.2.1.1 (q.2.2.1.2 + 1)))
    (fun j => stepSeq P ℱ W (fun s ω k => coordCLM j (Φ s ω k)) (cfun T K f X j) t ht0)
  let y : κ → Ω → ℝ := Sum.elim
    (fun q ω => ∫ s in Set.Ioc (rr t q.2.2.1.1 q.2.2.1.2) (rr t q.2.2.1.1 (q.2.2.1.2 + 1)),
      ∑ k, coordCLM q.1 (Φ s ω k) * coordCLM q.2.1 (Φ s ω k))
    (fun j => itoIntegral P ℱ W (fun s ω k => cfun T K f X j s ω * coordCLM j (Φ s ω k)) t)
  have hconv : ∀ c : κ, TendstoInMeasure P (Y c) atTop (y c) := by
    rintro (⟨j, l, ⟨⟨m, k⟩, hk⟩⟩ | j)
    · have hk1 : k ≤ 2 ^ m := hk.le
      exact tendstoInMeasure_blockQV hW (hΦ j) (hΦ l) ht0 (rr_mem ht0 m k hk1).1
        (rr_mono ht0 m (Nat.le_succ k)) (rr_mem ht0 m (k + 1) hk).2
    · exact tendstoInMeasure_stepSum hW (hΦ j) ht0 (hcprog j) (hCc j) (hcontc j)
  obtain ⟨φ, hφm, hφ⟩ := exists_subseq_ae_countable (P := P) (Y := Y) (y := y) hconv
  have hφall := ae_all_iff.2 hφ
  have hgall : ∀ᵐ ω ∂P, ∀ j l, ∀ T' : ℝ, IntegrableOn
      (fun s => ∑ k, coordCLM j (Φ s ω k) * coordCLM l (Φ s ω k)) (Set.Icc 0 T') :=
    ae_all_iff.2 fun j => ae_all_iff.2 fun l => hgint j l
  have hsum := (itoIntegral_finset_sum hW (Finset.univ : Finset (Fin (Module.finrank ℝ E)))
    (Ψ := fun j s ω k => cfun T K f X j s ω * coordCLM j (Φ s ω k)) (fun j _ => hcΦ j)).2
  filter_upwards [hφall, hgall, hbae, hXdec, hsum] with ω hφω hgω hbω hdec hsω hKω
  have hXKt : ∀ s ∈ Set.Icc 0 t, X s ω ∈ K := fun s hs => hKω s ⟨hs.1, hs.2.trans htT⟩
  have hH1 : ∀ j, Tendsto (fun n => (Partition.dyadic 0 t ht0 (φ n)).sumIncrements
      (fun a a' => fderiv ℝ (f a) (X a ω) (Module.finBasis ℝ E j) *
        (itoIntegral P ℱ W (fun s ω k => coordCLM j (Φ s ω k)) a' ω -
          itoIntegral P ℱ W (fun s ω k => coordCLM j (Φ s ω k)) a ω))) atTop
      (𝓝 (itoIntegral P ℱ W (fun s ω k => cfun T K f X j s ω * coordCLM j (Φ s ω k)) t ω)) := by
    intro j
    refine (hφω (Sum.inr j)).congr fun n => ?_
    show (Partition.dyadic 0 t ht0 (φ n)).sumIncrements
      (fun s s' => cfun T K f X j s ω * (itoIntegral P ℱ W (fun s ω k => coordCLM j (Φ s ω k)) s' ω -
        itoIntegral P ℱ W (fun s ω k => coordCLM j (Φ s ω k)) s ω)) = _
    refine dyadic_sumIncrements_congr ht0 (φ n) fun a ha a' _ => ?_
    have hmem : (a, X a ω) ∈ Set.Icc (0 : ℝ) T ×ˢ K := ⟨⟨ha.1, ha.2.trans htT⟩, hXKt a ha⟩
    rw [cfun_eq, Set.indicator_of_mem hmem]
  have key := ito_det2 hf hU hK hKU ht0 htT (Xp := fun s => X s ω) (bp := fun s => b s ω)
    (Φp := fun s => Φ s ω) (X0 := X 0 ω)
    (V := fun j s => itoIntegral P ℱ W (fun s ω k => coordCLM j (Φ s ω k)) s ω)
    hXKt (fun s _ => hdec s) hbω (fun j => continuous_itoIntegral P ℱ W _ ω)
    (fun j l => (hgω j l t))
    φ hφm.tendsto_atTop (Nj := fun j =>
      itoIntegral P ℱ W (fun s ω k => cfun T K f X j s ω * coordCLM j (Φ s ω k)) t ω) hH1
    (fun j l m k hk => hφω (Sum.inl (j, l, ⟨(m, k), hk⟩)))
  refine ⟨key.1, ?_⟩
  rw [key.2]
  congr 1
  have e : itoIntegrand T K f X Φ = fun s ω => ∑ j, (fun k => cfun T K f X j s ω * coordCLM j (Φ s ω k)) := by
    rw [itoIntegrand_eq_sum]; funext s ω k; simp
  rw [e, hsω t]

theorem continuousOn_setIntegral_Icc {g : ℝ → ℝ} {T : ℝ} (hg : IntegrableOn g (Set.Icc 0 T)) :
    ContinuousOn (fun t => ∫ s in Set.Icc 0 t, g s) (Set.Icc 0 T) := by
  have hint : Integrable (Set.indicator (Set.Icc 0 T) g) :=
    (integrable_indicator_iff measurableSet_Icc).2 hg
  have hc := continuous_driftIntegral (b := Set.indicator (Set.Icc 0 T) g)
    (fun N => hint.integrableOn)
  refine hc.continuousOn.congr fun t ht => ?_
  refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
  exact (Set.indicator_of_mem (show s ∈ Set.Icc (0:ℝ) T from ⟨hs.1, hs.2.trans ht.2⟩) g).symm

theorem eqOn_Icc_of_rat {T : ℝ} (hT : 0 ≤ T) {F G : ℝ → ℝ} (hF : ContinuousOn F (Set.Icc 0 T))
    (hG : ContinuousOn G (Set.Icc 0 T))
    (h : ∀ q : ℚ, 0 ≤ (q : ℝ) → (q : ℝ) ≤ T → F q = G q) : ∀ t ∈ Set.Icc 0 T, F t = G t := by
  have hs : Set.EqOn F G (Set.Icc 0 T ∩ Set.range ((↑) : ℚ → ℝ)) := by
    rintro x ⟨hx, q, rfl⟩
    exact h q hx.1 hx.2
  refine Set.EqOn.of_subset_closure hs hF hG Set.inter_subset_left ?_
  rcases hT.eq_or_lt with hT0 | hT0
  · subst hT0
    intro x hx
    have : x = 0 := hx.2.antisymm hx.1
    subst this
    exact subset_closure ⟨⟨le_rfl, le_rfl⟩, 0, by simp⟩
  · have hd : Dense (Set.range ((↑) : ℚ → ℝ)) := Rat.denseRange_cast
    have h1 : Set.Ioo 0 T ⊆ closure (Set.Ioo 0 T ∩ Set.range ((↑) : ℚ → ℝ)) :=
      hd.open_subset_closure_inter isOpen_Ioo
    have h2 : Set.Icc 0 T ⊆ closure (Set.Icc 0 T ∩ Set.range ((↑) : ℚ → ℝ)) := by
      calc Set.Icc 0 T = closure (Set.Ioo 0 T) := (closure_Ioo hT0.ne).symm
        _ ⊆ closure (closure (Set.Ioo 0 T ∩ Set.range ((↑) : ℚ → ℝ))) := closure_mono h1
        _ = closure (Set.Ioo 0 T ∩ Set.range ((↑) : ℚ → ℝ)) := closure_closure
        _ ⊆ _ := closure_mono (Set.inter_subset_inter_left _ Set.Ioo_subset_Icc_self)
    exact h2

theorem ito_core [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) {T : ℝ} (hT : 0 ≤ T)
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) {f : ℝ → E → ℝ}
    (hf : IsC12On T U f) {X : ℝ → Ω → E} (hXp : IsProgressive ℱ X) {b : ℝ → Ω → E}
    {Φ : ℝ → Ω → ι → E}
    (hΦ : ∀ j, IsProgressiveL2 P ℱ (fun s ω k => coordCLM j (Φ s ω k)))
    (hb : ∀ N : ℕ, ∀ᵐ ω ∂P, IntegrableOn (fun s => b s ω) (Set.Icc 0 (N : ℝ)))
    (hXK : ∀ᵐ ω ∂P, (∀ s ∈ Set.Icc 0 T, X s ω ∈ K) ∨ (∀ s ∈ Set.Icc 0 T, X s ω ∉ K))
    (hXdec : ∀ᵐ ω ∂P, ∀ s, X s ω = (X 0 ω + ∫ u in Set.Icc 0 s, b u ω) +
      ∑ j, itoIntegral P ℱ W (fun s ω k => coordCLM j (Φ s ω k)) s ω • Module.finBasis ℝ E j) :
    ∀ᵐ ω ∂P, (∀ s ∈ Set.Icc 0 T, X s ω ∈ K) →
      IntegrableOn (fun s => itoDrift T f X b Φ s ω) (Set.Icc 0 T) ∧
      ∀ t ∈ Set.Icc 0 T, f t (X t ω) = f 0 (X 0 ω) + (∫ s in Set.Icc 0 t, itoDrift T f X b Φ s ω) +
        itoIntegral P ℱ W (itoIntegrand T K f X Φ) t ω := by
  have hq : ∀ q : ℚ, ∀ᵐ ω ∂P, (∀ s ∈ Set.Icc 0 T, X s ω ∈ K) → 0 ≤ (q : ℝ) → (q : ℝ) ≤ T →
      f q (X q ω) = f 0 (X 0 ω) + (∫ s in Set.Icc 0 (q : ℝ), itoDrift T f X b Φ s ω) +
        itoIntegral P ℱ W (itoIntegrand T K f X Φ) q ω := by
    intro q
    by_cases h : 0 ≤ (q : ℝ) ∧ (q : ℝ) ≤ T
    · filter_upwards [ito_core_fixed hW hU hK hKU hf hXp hΦ hb hXK hXdec h.1 h.2] with ω hω hKω _ _
      exact (hω hKω).2
    · exact Filter.Eventually.of_forall fun ω _ h1 h2 => absurd ⟨h1, h2⟩ h
  filter_upwards [ito_core_fixed hW hU hK hKU hf hXp hΦ hb hXK hXdec hT le_rfl, ae_all_iff.2 hq,
    hXdec, ae_all_iff.2 hb] with ω hint hqω hdec hbω hKω
  have hint := hint hKω
  refine ⟨hint.1, ?_⟩
  have hXc : Continuous fun s => X s ω := by
    have h3 : Continuous fun s => (X 0 ω + ∫ u in Set.Icc 0 s, b u ω) +
        ∑ j, itoIntegral P ℱ W (fun s ω k => coordCLM j (Φ s ω k)) s ω • Module.finBasis ℝ E j :=
      (continuous_const.add (continuous_driftIntegral hbω)).add
        (continuous_finsetSum _ fun j _ => (continuous_itoIntegral P ℱ W _ ω).smul continuous_const)
    exact h3.congr fun s => (hdec s).symm
  have hF : ContinuousOn (fun s => f s (X s ω)) (Set.Icc 0 T) := by
    have hmaps : ∀ s ∈ Set.Icc (0 : ℝ) T, (s, X s ω) ∈ Set.Icc (0 : ℝ) T ×ˢ U :=
      fun s hs => ⟨hs, hKU (hKω s hs)⟩
    exact hf.cont.comp (continuousOn_id.prodMk hXc.continuousOn) hmaps
  have hG : ContinuousOn (fun s => f 0 (X 0 ω) + (∫ u in Set.Icc 0 s, itoDrift T f X b Φ u ω) +
      itoIntegral P ℱ W (itoIntegrand T K f X Φ) s ω) (Set.Icc 0 T) :=
    ((continuousOn_const.add (continuousOn_setIntegral_Icc hint.1)).add
      (continuous_itoIntegral P ℱ W _ ω).continuousOn)
  exact eqOn_Icc_of_rat hT hF hG fun q h1 h2 => hqω q hKω h1 h2

end Core



section Loc1

variable {P : Measure Ω} {ℱ : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ι → ℝ}

theorem stoppedProcess_coe_gen {β : Type*} {M : ℝ → Ω → β} {σ : Ω → WithTop ℝ} {ω : Ω} {c : ℝ}
    (h : σ ω = c) (u : ℝ) : stoppedProcess M σ u ω = M (min u c) ω := by
  have : min (u : WithTop ℝ) (σ ω) = ((min u c : ℝ) : WithTop ℝ) := by
    rw [h]; exact (WithTop.coe_min u c).symm
  unfold stoppedProcess
  rw [this]
  rfl

theorem stoppedProcess_top_gen {β : Type*} {M : ℝ → Ω → β} {σ : Ω → WithTop ℝ} {ω : Ω}
    (h : σ ω = ⊤) (u : ℝ) : stoppedProcess M σ u ω = M u ω := by
  simp [stoppedProcess, h]

/-- Stopping a (generic) function of time at `σ`: `1_{s ≤ σ} g_s`. -/
def stopFun {β : Type*} [Zero β] (g : ℝ → Ω → β) (σ : Ω → WithTop ℝ) : ℝ → Ω → β :=
  fun s ω => Set.indicator {ω | (s : WithTop ℝ) ≤ σ ω} (g s) ω

theorem itoProcess_of_nonpos (X₀ : Ω → E) (b : ℝ → Ω → E) (Φ : ℝ → Ω → ι → E) {t : ℝ} (ht : t ≤ 0)
    (ω : Ω) : itoProcess P ℱ W X₀ b Φ t ω = X₀ ω := by
  simp only [itoProcess, localItoIntegralE_of_nonpos P ℱ W Φ ht, add_zero]
  rcases ht.lt_or_eq with h | h
  · rw [Set.Icc_eq_empty (not_le.2 h)]; simp
  · subst h; simp

theorem isProgressive_stoppedProcess_E {X : ℝ → Ω → E} (hX : IsProgressive ℱ X)
    {σ : Ω → WithTop ℝ} (hσ : IsStoppingTime ℱ σ) : IsProgressive ℱ (stoppedProcess X σ) :=
  (hX.isStronglyProgressive.stoppedProcess hσ).isProgressive

theorem isProgressive_stopFun_E {b : ℝ → Ω → E} (hb : IsProgressive ℱ b)
    {σ : Ω → WithTop ℝ} (hσ : IsStoppingTime ℱ σ) : IsProgressive ℱ (stopFun b σ) := by
  intro i
  have h := (isProgressive_indicator_le_stoppingTime ℱ hσ i).smul (hb i)
  convert h using 1
  funext p
  by_cases hp : (p.1 : WithTop ℝ) ≤ σ p.2 <;> simp [stopFun, Set.indicator, hp]


theorem IsProgressiveL2.of_dom {Ψ I : ℝ → Ω → ι → ℝ} (hΨ : IsProgressiveL2 P ℱ Ψ)
    (hI : IsProgressive ℱ I) {C : ℝ≥0∞} (hC : C ≠ ∞) (hle : ∀ s ω k, ‖I s ω k‖ₑ ≤ C * ‖Ψ s ω k‖ₑ) :
    IsProgressiveL2 P ℱ I := by
  refine ⟨hI, fun T => ?_⟩
  have : sqIntegralOn P I T ≤ C ^ 2 * sqIntegralOn P Ψ T := by
    unfold sqIntegralOn
    rw [← lintegral_const_mul' _ _ (ENNReal.pow_ne_top hC)]
    refine lintegral_mono fun ω => ?_
    rw [← lintegral_const_mul' _ _ (ENNReal.pow_ne_top hC)]
    refine lintegral_mono fun s => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    calc ‖I s ω k‖ₑ ^ 2 ≤ (C * ‖Ψ s ω k‖ₑ) ^ 2 := by gcongr; exact hle s ω k
      _ = _ := by rw [mul_pow]
  exact lt_of_le_of_lt this (ENNReal.mul_lt_top (ENNReal.pow_lt_top hC.lt_top) (hΨ.sq T))

theorem IsProgressiveLocL2.of_dom {Ψ I : ℝ → Ω → ι → ℝ} (hΨ : IsProgressiveLocL2 P ℱ Ψ)
    (hI : IsProgressive ℱ I) {C : ℝ≥0∞} (hC : C ≠ ∞) (hle : ∀ s ω k, ‖I s ω k‖ₑ ≤ C * ‖Ψ s ω k‖ₑ) :
    IsProgressiveLocL2 P ℱ I := by
  refine ⟨hI, fun T => ?_⟩
  filter_upwards [hΨ.sq T] with ω hω
  have : ∫⁻ s in Set.Icc 0 T, ∑ k, ‖I s ω k‖ₑ ^ 2 ≤
      C ^ 2 * ∫⁻ s in Set.Icc 0 T, ∑ k, ‖Ψ s ω k‖ₑ ^ 2 := by
    rw [← lintegral_const_mul' _ _ (ENNReal.pow_ne_top hC)]
    refine lintegral_mono fun s => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    calc ‖I s ω k‖ₑ ^ 2 ≤ (C * ‖Ψ s ω k‖ₑ) ^ 2 := by gcongr; exact hle s ω k
      _ = _ := by rw [mul_pow]
  exact lt_of_le_of_lt this (ENNReal.mul_lt_top (ENNReal.pow_lt_top hC.lt_top) hω)

/-- The pointwise norm of an `E`-valued locally square-integrable integrand. -/
theorem IsProgressiveLocL2E.norm {Φ : ℝ → Ω → ι → E} (hΦ : IsProgressiveLocL2E P ℱ Φ) :
    IsProgressiveLocL2 P ℱ (fun s ω k => ‖Φ s ω k‖) := by
  refine ⟨isProgressive_comp_measurable hΦ.prog (g := fun v : ι → E => fun k => ‖v k‖)
    (measurable_pi_iff.2 fun k => (measurable_norm).comp (measurable_pi_apply k)), fun T => ?_⟩
  simpa using hΦ.sq T

theorem IsProgressiveLocL2E.coord_dom {Φ : ℝ → Ω → ι → E} (j : Fin (Module.finrank ℝ E)) (s : ℝ)
    (ω : Ω) (k : ι) :
    ‖coordCLM j (Φ s ω k)‖ₑ ≤ ‖coordCLM j‖ₑ * ‖‖Φ s ω k‖‖ₑ := by
  rw [enorm_norm]
  exact (coordCLM j).le_opENorm _


/-- The (real) time at which the stopped process is evaluated: `s ∧ σ`. -/
def stopT (σ : Ω → WithTop ℝ) (s : ℝ) (ω : Ω) : ℝ :=
  stoppedProcess (fun u (_ : Ω) => u) σ s ω

theorem stopT_top {σ : Ω → WithTop ℝ} {ω : Ω} (h : σ ω = ⊤) (s : ℝ) : stopT σ s ω = s :=
  stoppedProcess_top_gen h s

theorem stopT_coe {σ : Ω → WithTop ℝ} {ω : Ω} {c : ℝ} (h : σ ω = c) (s : ℝ) :
    stopT σ s ω = min s c :=
  stoppedProcess_coe_gen h s

theorem stopT_le (σ : Ω → WithTop ℝ) (s : ℝ) (ω : Ω) : stopT σ s ω ≤ s := by
  cases h : σ ω with
  | top => rw [stopT_top h]
  | coe c => rw [stopT_coe h]; exact min_le_left _ _

theorem stopT_le_stop {σ : Ω → WithTop ℝ} (s : ℝ) (ω : Ω) : (stopT σ s ω : WithTop ℝ) ≤ σ ω := by
  cases h : σ ω with
  | top => exact le_top
  | coe c => rw [stopT_coe h]; exact_mod_cast min_le_right _ _

theorem stopT_of_le {σ : Ω → WithTop ℝ} {s : ℝ} {ω : Ω} (h : (s : WithTop ℝ) ≤ σ ω) :
    stopT σ s ω = s := by
  cases hσ : σ ω with
  | top => exact stopT_top hσ s
  | coe c => rw [hσ] at h; rw [stopT_coe hσ]; exact min_eq_left (by exact_mod_cast h)

theorem stopT_nonneg {σ : Ω → WithTop ℝ} {s : ℝ} {ω : Ω} (hs : 0 ≤ s) (h : (0 : WithTop ℝ) ≤ σ ω) :
    0 ≤ stopT σ s ω := by
  cases hσ : σ ω with
  | top => rw [stopT_top hσ]; exact hs
  | coe c => rw [hσ] at h; rw [stopT_coe hσ]; exact le_min hs (by exact_mod_cast h)

theorem measurableSet_le_stop (σ : Ω → WithTop ℝ) (ω : Ω) :
    MeasurableSet {s : ℝ | (s : WithTop ℝ) ≤ σ ω} := by
  cases h : σ ω with
  | top => simp
  | coe c =>
    have : {s : ℝ | (s : WithTop ℝ) ≤ (c : WithTop ℝ)} = Set.Iic c := by
      ext s; simp
    rw [this]; exact measurableSet_Iic

theorem integral_stopFun (b : ℝ → Ω → E) (σ : Ω → WithTop ℝ) (s : ℝ) (ω : Ω) :
    ∫ u in Set.Icc 0 s, stopFun b σ u ω = ∫ u in Set.Icc 0 (stopT σ s ω), b u ω := by
  cases h : σ ω with
  | top =>
    rw [stopT_top h]
    refine setIntegral_congr_fun measurableSet_Icc fun u _ => ?_
    simp [stopFun, h]
  | coe c =>
    rw [stopT_coe h]
    have e : ∫ u in Set.Icc 0 s, stopFun b σ u ω =
        ∫ u in Set.Icc 0 s, Set.indicator (Set.Iic c) (fun u => b u ω) u := by
      refine setIntegral_congr_fun measurableSet_Icc fun u _ => ?_
      simp [stopFun, h, Set.indicator]
    rw [e, integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
    congr 2
    ext u; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, min_def]
    split_ifs <;> constructor <;> intro h <;> refine ⟨?_, ?_⟩ <;> (try constructor) <;> linarith [h.1, h.2]


theorem stopFun_apply_of_le {β : Type*} [Zero β] {g : ℝ → Ω → β} {σ : Ω → WithTop ℝ} {s : ℝ} {ω : Ω}
    (h : (s : WithTop ℝ) ≤ σ ω) : stopFun g σ s ω = g s ω := by
  simp [stopFun, h]

theorem stopFun_apply_of_not_le {β : Type*} [Zero β] {g : ℝ → Ω → β} {σ : Ω → WithTop ℝ} {s : ℝ}
    {ω : Ω} (h : ¬ (s : WithTop ℝ) ≤ σ ω) : stopFun g σ s ω = 0 := by
  simp [stopFun, h]

theorem itoIntegrand_stop (T : ℝ) (K : Set E) (f : ℝ → E → ℝ) (X : ℝ → Ω → E)
    (Φ : ℝ → Ω → ι → E) (σ : Ω → WithTop ℝ) :
    itoIntegrand T K f (stoppedProcess X σ) (stopFun Φ σ) =
      stopIntegrand (itoIntegrand T K f X Φ) σ := by
  funext s ω k
  by_cases h : (s : WithTop ℝ) ≤ σ ω
  · have hX : stoppedProcess X σ s ω = X s ω := MeasureTheory.stoppedProcess_eq_of_le h
    simp [itoIntegrand, stopIntegrand, Set.indicator, h, stopFun_apply_of_le h, hX]
    split_ifs <;> first | rfl | (exfalso; simp_all)
  · simp [itoIntegrand, stopIntegrand, stopFun_apply_of_not_le h, h]

theorem ito_stopped [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) {T : ℝ} (hT : 0 ≤ T)
    {U K : Set E} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) {f : ℝ → E → ℝ}
    (hf : IsC12On T U f) {X₀ : Ω → E} (hX₀ : ∀ t : ℝ, Measurable[ℱ t] X₀) {b : ℝ → Ω → E}
    (hb : IsProgressiveLocL1 P ℱ b) {Φ : ℝ → Ω → ι → E} (hΦ : IsProgressiveLocL2E P ℱ Φ)
    {σ : Ω → WithTop ℝ} (hσ : IsStoppingTime ℱ σ)
    (hΦσ : ∀ j, IsProgressiveL2 P ℱ (stopIntegrand (fun s ω k => coordCLM j (Φ s ω k)) σ))
    (hXK : ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc 0 T, (t : WithTop ℝ) ≤ σ ω →
      itoProcess P ℱ W X₀ b Φ t ω ∈ K) :
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc 0 T, (t : WithTop ℝ) ≤ σ ω →
      IntegrableOn (fun s => itoDrift T f (itoProcess P ℱ W X₀ b Φ) b Φ s ω) (Set.Icc 0 t) ∧
      f t (itoProcess P ℱ W X₀ b Φ t ω) = f 0 (X₀ ω) +
        (∫ s in Set.Icc 0 t, itoDrift T f (itoProcess P ℱ W X₀ b Φ) b Φ s ω) +
        itoIntegral P ℱ W
          (stopIntegrand (itoIntegrand T K f (itoProcess P ℱ W X₀ b Φ) Φ) σ) t ω := by
  set X := itoProcess P ℱ W X₀ b Φ with hXdef
  have hXprog : IsProgressive ℱ X := isProgressive_itoProcess X₀ hX₀ b hb.prog Φ
  have hX'p : IsProgressive ℱ (stoppedProcess X σ) := isProgressive_stoppedProcess_E hXprog hσ
  have hΦ'c : ∀ j, (fun s ω k => coordCLM j (stopFun Φ σ s ω k)) =
      stopIntegrand (fun s ω k => coordCLM j (Φ s ω k)) σ := by
    intro j; funext s ω k
    by_cases h : (s : WithTop ℝ) ≤ σ ω
    · simp [stopFun, stopIntegrand, Set.indicator, h]
    · simp [stopFun, stopIntegrand, Set.indicator, h]
  have hΦ' : ∀ j, IsProgressiveL2 P ℱ (fun s ω k => coordCLM j (stopFun Φ σ s ω k)) :=
    fun j => by rw [hΦ'c j]; exact hΦσ j
  have hb' : ∀ N : ℕ, ∀ᵐ ω ∂P, IntegrableOn (fun s => stopFun b σ s ω) (Set.Icc 0 (N : ℝ)) := by
    intro N
    filter_upwards [hb.int N] with ω hω
    have : (fun s => stopFun b σ s ω) =
        Set.indicator {s : ℝ | (s : WithTop ℝ) ≤ σ ω} (fun s => b s ω) := by
      funext s; simp [stopFun, Set.indicator]
    rw [this]
    exact hω.indicator (measurableSet_le_stop σ ω)
  have hKleft : ∀ᵐ ω ∂P, (0 : WithTop ℝ) ≤ σ ω →
      ∀ s ∈ Set.Icc 0 T, stoppedProcess X σ s ω ∈ K := by
    filter_upwards [hXK] with ω hω h0 s hs
    have hm : stoppedProcess X σ s ω = X (stopT σ s ω) ω := rfl
    rw [hm]
    exact hω _ ⟨stopT_nonneg hs.1 h0, (stopT_le σ s ω).trans hs.2⟩ (stopT_le_stop s ω)
  have hK' : ∀ᵐ ω ∂P, (∀ s ∈ Set.Icc 0 T, stoppedProcess X σ s ω ∈ K) ∨
      (∀ s ∈ Set.Icc 0 T, stoppedProcess X σ s ω ∉ K) := by
    filter_upwards [hKleft] with ω hω
    by_cases h0 : (0 : WithTop ℝ) ≤ σ ω
    · exact Or.inl (hω h0)
    · obtain ⟨c, hc, hc0⟩ : ∃ c : ℝ, σ ω = c ∧ c < 0 := by
        cases hσω : σ ω with
        | top => exact absurd (hσω ▸ le_top) h0
        | coe c =>
          rw [hσω] at h0
          exact ⟨c, rfl, not_le.1 (fun h => h0 (by exact_mod_cast h))⟩
      have hconst : ∀ s ∈ Set.Icc 0 T, stoppedProcess X σ s ω = X c ω := fun s hs => by
        show X (stopT σ s ω) ω = _
        rw [stopT_coe hc, min_eq_right (by linarith [hs.1])]
      by_cases hin : X c ω ∈ K
      · left; intro s hs; rw [hconst s hs]; exact hin
      · right; intro s hs; rw [hconst s hs]; exact hin
  have hdec' : ∀ᵐ ω ∂P, ∀ s, stoppedProcess X σ s ω = (stoppedProcess X σ 0 ω +
      ∫ u in Set.Icc 0 s, stopFun b σ u ω) +
      ∑ j, itoIntegral P ℱ W (fun s ω k => coordCLM j (stopFun Φ σ s ω k)) s ω •
        Module.finBasis ℝ E j := by
    have h1 : ∀ j, ∀ᵐ ω ∂P, ∀ t, coordCLM j (localItoIntegralE P ℱ W Φ t ω) =
        localItoIntegral P ℱ W (fun s ω k => coordCLM j (Φ s ω k)) t ω :=
      fun j => localItoIntegralE_apply hW hΦ (coordCLM j)
    have h2 := fun j => localItoIntegral_stopIntegrand hW (hΦ.comp (coordCLM j)) hσ
    have h3 := fun j => localItoIntegral_eq_itoIntegral hW (hΦσ j)
    filter_upwards [ae_all_iff.2 h1, ae_all_iff.2 h2, ae_all_iff.2 h3] with ω a1 a2 a3 s
    have e0 : stoppedProcess X σ 0 ω = X₀ ω := itoProcess_of_nonpos X₀ b Φ (stopT_le σ 0 ω) ω
    rw [e0, integral_stopFun]
    show X (stopT σ s ω) ω = _
    simp only [hXdef, itoProcess]
    congr 1
    conv_lhs => rw [← sum_coordCLM_smul (localItoIntegralE P ℱ W Φ (stopT σ s ω) ω)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hΦ'c j, a1 j (stopT σ s ω), ← a3 j s, a2 j s]
    rfl
  have hcore := ito_core hW hT hU hK hKU hf hX'p hΦ' hb' hK' hdec'
  filter_upwards [hcore, hKleft] with ω hω hKl t ht hts
  have h0 : (0 : WithTop ℝ) ≤ σ ω := le_trans (by exact_mod_cast ht.1) hts
  obtain ⟨hint, heq⟩ := hω (hKl h0)
  have hdr : ∀ s ∈ Set.Icc 0 t, itoDrift T f (stoppedProcess X σ) (stopFun b σ) (stopFun Φ σ) s ω =
      itoDrift T f X b Φ s ω := by
    intro s hs
    have hs' : (s : WithTop ℝ) ≤ σ ω := le_trans (by exact_mod_cast hs.2) hts
    have hX : stoppedProcess X σ s ω = X s ω := MeasureTheory.stoppedProcess_eq_of_le hs'
    unfold itoDrift
    rw [hX]
    simp only [stopFun_apply_of_le hs']
  have e0 : stoppedProcess X σ 0 ω = X₀ ω := itoProcess_of_nonpos X₀ b Φ (stopT_le σ 0 ω) ω
  refine ⟨(hint.mono_set (Set.Icc_subset_Icc_right ht.2)).congr_fun hdr measurableSet_Icc, ?_⟩
  have := heq t ht
  rw [MeasureTheory.stoppedProcess_eq_of_le hts, e0, itoIntegrand_stop,
    setIntegral_congr_fun measurableSet_Icc hdr] at this
  exact this

end Loc1


section ItoIntegrandProps

variable {P : Measure Ω} {ℱ : Filtration ℝ mΩ}

theorem isProgressive_coordE {Φ : ℝ → Ω → ι → E} (hΦ : IsProgressive ℱ Φ)
    (j : Fin (Module.finrank ℝ E)) (k : ι) : IsProgressive ℱ (fun s ω => coordCLM j (Φ s ω k)) :=
  fun i => (coordCLM j).continuous.measurable.comp ((measurable_pi_apply k).comp (hΦ i))

theorem isProgressive_itoIntegrand {T : ℝ} {U K : Set E} {f : ℝ → E → ℝ} (hf : IsC12On T U f)
    (hK : IsClosed K) (hKU : K ⊆ U) {X : ℝ → Ω → E} (hX : IsProgressive ℱ X)
    {Φ : ℝ → Ω → ι → E} (hΦ : IsProgressive ℱ Φ) : IsProgressive ℱ (itoIntegrand T K f X Φ) := by
  rw [itoIntegrand_eq_sum]
  exact isProgressive_pi fun k => IsProgressive.finsetSum fun j _ =>
    (isProgressive_cfun hf hK hKU hX j).mul (isProgressive_coordE hΦ j k)

theorem enorm_itoIntegrand_le {T : ℝ} {K : Set E} {f : ℝ → E → ℝ} {X : ℝ → Ω → E}
    {Φ : ℝ → Ω → ι → E} {C : ℝ} (s : ℝ) (ω : Ω) (k : ι)
    (hC : s ∈ Set.Icc 0 T → X s ω ∈ K → ‖fderiv ℝ (f s) (X s ω)‖ ≤ C) :
    ‖itoIntegrand T K f X Φ s ω k‖ₑ ≤ ‖C‖ₑ * ‖‖Φ s ω k‖‖ₑ := by
  by_cases h1 : s ∈ Set.Icc 0 T <;> by_cases h2 : X s ω ∈ K
  · have : itoIntegrand T K f X Φ s ω k = fderiv ℝ (f s) (X s ω) (Φ s ω k) := by
      simp [itoIntegrand, Set.indicator, h1, h2]
    rw [this, enorm_norm]
    calc ‖fderiv ℝ (f s) (X s ω) (Φ s ω k)‖ₑ ≤ ‖fderiv ℝ (f s) (X s ω)‖ₑ * ‖Φ s ω k‖ₑ :=
          ContinuousLinearMap.le_opENorm _ _
      _ ≤ ‖C‖ₑ * ‖Φ s ω k‖ₑ := by
          gcongr
          rw [enorm_le_iff_norm_le]
          exact (hC h1 h2).trans (by simpa using le_abs_self C)
  all_goals
    have : itoIntegrand T K f X Φ s ω k = 0 := by simp [itoIntegrand, Set.indicator, h1, h2]
    rw [this]; simp

/-- The martingale integrand of Itô's formula is in the local `L²` class.  `X` is required to be
progressive (as first stated with `Adapted ℱ X` only, the claim was false: see `SPEC.md` §6). -/
theorem isProgressiveLocL2_itoIntegrand {T : ℝ} (K : Set E) (hK : IsClosed K) (U : Set E)
    (hKU : K ⊆ U) (f : ℝ → E → ℝ) (hf : IsC12On T U f) (X : ℝ → Ω → E)
    (hX : IsProgressive ℱ X) (hXc : ∀ᵐ ω ∂P, Continuous fun t => X t ω) (Φ : ℝ → Ω → ι → E)
    (hΦ : IsProgressiveLocL2E P ℱ Φ) : IsProgressiveLocL2 P ℱ (itoIntegrand T K f X Φ) := by
  refine ⟨isProgressive_itoIntegrand hf hK hKU hX hΦ.prog, fun T' => ?_⟩
  filter_upwards [hXc, hΦ.sq T'] with ω hXω hΦω
  set A : Set ℝ := Set.Icc 0 T ∩ {s | X s ω ∈ K} with hA
  have hAc : IsCompact A :=
    isCompact_Icc.inter_right (hK.preimage hXω)
  have hcont : ContinuousOn (fun s => ‖fderiv ℝ (f s) (X s ω)‖) A := by
    have hmaps : ∀ s ∈ A, (s, X s ω) ∈ Set.Icc (0 : ℝ) T ×ˢ U :=
      fun s hs => ⟨hs.1, hKU hs.2⟩
    have := hf.cont_fderiv.comp (continuousOn_id.prodMk hXω.continuousOn) hmaps
    exact this.norm
  obtain ⟨C, hC⟩ := hAc.exists_bound_of_continuousOn hcont
  have hle : ∀ s, ∑ k, ‖itoIntegrand T K f X Φ s ω k‖ₑ ^ 2 ≤ ‖C‖ₑ ^ 2 * ∑ k, ‖Φ s ω k‖ₑ ^ 2 := by
    intro s
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    calc ‖itoIntegrand T K f X Φ s ω k‖ₑ ^ 2 ≤ (‖C‖ₑ * ‖‖Φ s ω k‖‖ₑ) ^ 2 := by
          gcongr
          exact enorm_itoIntegrand_le s ω k (fun h1 h2 => by simpa using hC s ⟨h1, h2⟩)
      _ = _ := by rw [mul_pow, enorm_norm]
  calc ∫⁻ s in Set.Icc 0 T', ∑ k, ‖itoIntegrand T K f X Φ s ω k‖ₑ ^ 2
      ≤ ∫⁻ s in Set.Icc 0 T', ‖C‖ₑ ^ 2 * ∑ k, ‖Φ s ω k‖ₑ ^ 2 := lintegral_mono hle
    _ = ‖C‖ₑ ^ 2 * ∫⁻ s in Set.Icc 0 T', ∑ k, ‖Φ s ω k‖ₑ ^ 2 := by
        rw [lintegral_const_mul' _ _ (by simp)]
    _ < ∞ := ENNReal.mul_lt_top (by simp) hΦω

/-- When `D_x f` is bounded on `[0, T] × E` and `Φ` is in the `L²` class, the martingale integrand
is in the `L²` class, so the martingale term of `ito_formula` is the `L²` Itô integral
(`localItoIntegral_eq_itoIntegral`).  `X` is required to be progressive (see `SPEC.md` §6). -/
theorem isProgressiveL2_itoIntegrand {T : ℝ} (f : ℝ → E → ℝ)
    (hf : IsC12On T Set.univ f) (C : ℝ)
    (hC : ∀ t ∈ Set.Icc 0 T, ∀ x, ‖fderiv ℝ (f t) x‖ ≤ C) (X : ℝ → Ω → E)
    (hX : IsProgressive ℱ X) (Φ : ℝ → Ω → ι → E) (hΦ : IsProgressiveLocL2E P ℱ Φ)
    (hΦ2 : ∀ T, ∫⁻ ω, (∫⁻ s in Set.Icc 0 T, ∑ k, ‖Φ s ω k‖ₑ ^ 2) ∂P < ∞) :
    IsProgressiveL2 P ℱ (itoIntegrand T Set.univ f X Φ) := by
  have hΨ : IsProgressiveL2 P ℱ (fun s ω k => ‖Φ s ω k‖) :=
    ⟨hΦ.norm.prog, fun T' => by simpa [sqIntegralOn] using hΦ2 T'⟩
  exact hΨ.of_dom (isProgressive_itoIntegrand hf isClosed_univ (Set.subset_univ _) hX hΦ.prog)
    (C := ‖C‖ₑ) (by simp) (fun s ω k => enorm_itoIntegrand_le s ω k (fun h1 _ => hC s h1 _))

theorem exists_bound_fderiv {T : ℝ} {U K : Set E} {f : ℝ → E → ℝ} (hf : IsC12On T U f)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℝ, ∀ s ∈ Set.Icc 0 T, ∀ x ∈ K, ‖fderiv ℝ (f s) x‖ ≤ C := by
  have := (isCompact_Icc.prod hK).exists_bound_of_continuousOn
    ((hf.cont_fderiv.mono (Set.prod_mono subset_rfl hKU)).norm)
  obtain ⟨C, hC⟩ := this
  exact ⟨C, fun s hs x hx => by simpa using hC (s, x) ⟨hs, hx⟩⟩

theorem isProgressiveL2_stop_itoIntegrand {T : ℝ} {U K : Set E} {f : ℝ → E → ℝ}
    (hf : IsC12On T U f) (hK : IsCompact K) (hKU : K ⊆ U) {X : ℝ → Ω → E}
    (hX : IsProgressive ℱ X) {Φ : ℝ → Ω → ι → E} (hΦ : IsProgressive ℱ Φ)
    {σ : Ω → WithTop ℝ} (hσ : IsStoppingTime ℱ σ)
    (hψ : IsProgressiveL2 P ℱ (stopIntegrand (fun s ω k => ‖Φ s ω k‖) σ)) :
    IsProgressiveL2 P ℱ (stopIntegrand (itoIntegrand T K f X Φ) σ) := by
  obtain ⟨C, hC⟩ := exists_bound_fderiv hf hK hKU
  refine hψ.of_dom (isProgressive_stopIntegrand (isProgressive_itoIntegrand hf hK.isClosed hKU hX hΦ)
    hσ) (C := ‖C‖ₑ) (by simp) (fun s ω k => ?_)
  by_cases h : (s : WithTop ℝ) ≤ σ ω
  · have e1 : stopIntegrand (itoIntegrand T K f X Φ) σ s ω k = itoIntegrand T K f X Φ s ω k := by
      simp [stopIntegrand, Set.indicator, h]
    have e2 : stopIntegrand (fun s ω k => ‖Φ s ω k‖) σ s ω k = ‖Φ s ω k‖ := by
      simp [stopIntegrand, Set.indicator, h]
    rw [e1, e2]
    exact enorm_itoIntegrand_le s ω k (fun h1 h2 => hC s h1 _ h2)
  · simp [stopIntegrand, Set.indicator, h]

end ItoIntegrandProps

section FormulaProofs

theorem stopIntegrand_of_not_le {Ψ : ℝ → Ω → ι → ℝ} {σ : Ω → WithTop ℝ} {s : ℝ} {ω : Ω}
    (h : ¬ (s : WithTop ℝ) ≤ σ ω) : stopIntegrand Ψ σ s ω = 0 := by
  simp [stopIntegrand, h]

variable {P : Measure Ω} {ℱ : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ι → ℝ}

theorem ito_formula_localized_proof [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    {T : ℝ}
    (hT : 0 ≤ T) (U : Set E) (hU : IsOpen U) (K : Set E) (hK : IsCompact K) (hKU : K ⊆ U)
    (f : ℝ → E → ℝ) (hf : IsC12On T U f) (X₀ : Ω → E) (hX₀ : ∀ t : ℝ, Measurable[ℱ t] X₀)
    (b : ℝ → Ω → E) (hb : IsProgressiveLocL1 P ℱ b) (Φ : ℝ → Ω → ι → E)
    (hΦ : IsProgressiveLocL2E P ℱ Φ) (τ : Ω → WithTop ℝ) (hτ : IsStoppingTime ℱ τ)
    (hXK : ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc 0 T, (t : WithTop ℝ) ≤ τ ω → itoProcess P ℱ W X₀ b Φ t ω ∈ K) :
    let X := itoProcess P ℱ W X₀ b Φ
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc 0 T, (t : WithTop ℝ) ≤ τ ω →
      IntegrableOn (fun s => itoDrift T f X b Φ s ω) (Set.Icc 0 t) ∧
      f t (X t ω) = f 0 (X₀ ω) + (∫ s in Set.Icc 0 t, itoDrift T f X b Φ s ω) +
        localItoIntegral P ℱ W (stopIntegrand (itoIntegrand T K f X Φ) τ) t ω := by
  intro X
  have hXprog : IsProgressive ℱ X := isProgressive_itoProcess X₀ hX₀ b hb.prog Φ
  have hψ := hΦ.norm
  have hρ : ∀ n : ℕ, IsStoppingTime ℱ (locTime (fun s ω k => ‖Φ s ω k‖) n) :=
    fun n => isStoppingTime_locTime hW.complete hψ n
  have hσ : ∀ n : ℕ, IsStoppingTime ℱ (fun ω => min (τ ω) (locTime (fun s ω k => ‖Φ s ω k‖) n ω)) :=
    fun n => hτ.min (hρ n)
  have hψσ : ∀ n : ℕ, IsProgressiveL2 P ℱ (stopIntegrand (fun s ω k => ‖Φ s ω k‖)
      (fun ω => min (τ ω) (locTime (fun s ω k => ‖Φ s ω k‖) n ω))) :=
    fun n => isProgressiveL2_stopIntegrand_of_le hW.complete hψ (hσ n) n (fun ω => min_le_right _ _)
  have hΦσ : ∀ n : ℕ, ∀ j, IsProgressiveL2 P ℱ (stopIntegrand (fun s ω k => coordCLM j (Φ s ω k))
      (fun ω => min (τ ω) (locTime (fun s ω k => ‖Φ s ω k‖) n ω))) := by
    intro n j
    refine (hψσ n).of_dom (isProgressive_stopIntegrand (hΦ.comp (coordCLM j)).prog (hσ n))
      (C := ‖coordCLM j‖ₑ) (by simp) (fun s ω k => ?_)
    by_cases h : (s : WithTop ℝ) ≤ min (τ ω) (locTime (fun s ω k => ‖Φ s ω k‖) n ω)
    · simp only [stopIntegrand, Set.indicator, Set.mem_setOf_eq, h, if_true]
      rw [enorm_norm]
      exact (coordCLM j).le_opENorm _
    · have e2 : stopIntegrand (fun s ω k => coordCLM j (Φ s ω k))
          (fun ω => min (τ ω) (locTime (fun s ω k => ‖Φ s ω k‖) n ω)) s ω = 0 :=
        stopIntegrand_of_not_le (σ := fun ω => min (τ ω) (locTime (fun s ω k => ‖Φ s ω k‖) n ω)) h
      have e3 : stopIntegrand (fun s ω k => ‖Φ s ω k‖)
          (fun ω => min (τ ω) (locTime (fun s ω k => ‖Φ s ω k‖) n ω)) s ω = 0 :=
        stopIntegrand_of_not_le (σ := fun ω => min (τ ω) (locTime (fun s ω k => ‖Φ s ω k‖) n ω)) h
      rw [e2, e3]; simp
  have hmain : ∀ n : ℕ, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc 0 T,
      (t : WithTop ℝ) ≤ min (τ ω) (locTime (fun s ω k => ‖Φ s ω k‖) n ω) →
      IntegrableOn (fun s => itoDrift T f X b Φ s ω) (Set.Icc 0 t) ∧
      f t (X t ω) = f 0 (X₀ ω) + (∫ s in Set.Icc 0 t, itoDrift T f X b Φ s ω) +
        itoIntegral P ℱ W (stopIntegrand (itoIntegrand T K f X Φ)
          (fun ω => min (τ ω) (locTime (fun s ω k => ‖Φ s ω k‖) n ω))) t ω := by
    intro n
    refine ito_stopped hW hT hU hK hKU hf hX₀ hb hΦ (hσ n) (hΦσ n) ?_
    filter_upwards [hXK] with ω hω t ht hts
    exact hω t ht (hts.trans (min_le_left _ _))
  have hΨ : IsProgressiveLocL2 P ℱ (itoIntegrand T K f X Φ) :=
    isProgressiveLocL2_itoIntegrand K hK.isClosed U hKU f hf X hXprog
      (continuous_itoProcess X₀ b hb Φ) Φ hΦ
  have hid : ∀ n : ℕ, ∀ᵐ ω ∂P, ∀ t : ℝ,
      (t : WithTop ℝ) ≤ min (τ ω) (locTime (fun s ω k => ‖Φ s ω k‖) n ω) →
      itoIntegral P ℱ W (stopIntegrand (itoIntegrand T K f X Φ)
          (fun ω => min (τ ω) (locTime (fun s ω k => ‖Φ s ω k‖) n ω))) t ω =
        localItoIntegral P ℱ W (stopIntegrand (itoIntegrand T K f X Φ) τ) t ω := by
    intro n
    have hL2 := isProgressiveL2_stop_itoIntegrand hf hK hKU hXprog hΦ.prog (hσ n) (hψσ n)
    filter_upwards [localItoIntegral_eq_itoIntegral hW hL2,
      localItoIntegral_stopIntegrand hW hΨ (hσ n), localItoIntegral_stopIntegrand hW hΨ hτ]
      with ω h1 h2 h3 t ht
    rw [← h1 t, h2 t, h3 t,
      stoppedProcess_eq_of_le (σ := fun ω => min (τ ω) (locTime (fun s ω k => ‖Φ s ω k‖) n ω)) ht,
      stoppedProcess_eq_of_le (ht.trans (min_le_left _ _))]
  filter_upwards [ae_all_iff.2 hmain, ae_all_iff.2 hid, locTime_exhaust hψ] with ω hm hi hex t ht hτt
  obtain ⟨n, hn⟩ := hex t
  have hle : (t : WithTop ℝ) ≤ min (τ ω) (locTime (fun s ω k => ‖Φ s ω k‖) n ω) := le_min hτt hn
  obtain ⟨h1, h2⟩ := hm n t ht hle
  exact ⟨h1, by rw [h2, hi n t hle]⟩

theorem exists_radius_times {Y : ℝ → Ω → ℝ} (hY : Adapted ℱ Y)
    (hc : ∀ ω, Continuous fun t => Y t ω) (hY0 : ∀ t, Measurable[ℱ t] (Y 0)) :
    ∃ τ : ℕ → Ω → WithTop ℝ, (∀ n, IsStoppingTime ℱ (τ n)) ∧
      (∀ (n : ℕ) (ω : Ω) (t : ℝ), 0 ≤ t → (t : WithTop ℝ) ≤ τ n ω → Y t ω ≤ n) ∧
      (∀ (ω : Ω) (T : ℝ), ∃ n : ℕ, (T : WithTop ℝ) ≤ τ n ω) := by
  classical
  obtain ⟨m, hm⟩ : ∃ m : ℝ, m < 0 := ⟨-1, by norm_num⟩
  refine ⟨fun n ω => if (n : ℝ) ≤ Y 0 ω then (m : WithTop ℝ)
    else hittingAfter Y (Set.Ici (n : ℝ)) 0 ω, ?_, ?_, ?_⟩
  · intro n i
    have hA : MeasurableSet[ℱ i] {ω | (n : ℝ) ≤ Y 0 ω} :=
      measurableSet_le measurable_const (hY0 i)
    have h0 : MeasurableSet[ℱ i] {ω | hittingAfter Y (Set.Ici (n : ℝ)) 0 ω ≤ (i : WithTop ℝ)} :=
      isStoppingTime_hittingAfter_Ici ℱ Y hY hc n i
    have e : {ω | (if (n : ℝ) ≤ Y 0 ω then (m : WithTop ℝ)
        else hittingAfter Y (Set.Ici (n : ℝ)) 0 ω) ≤ (i : WithTop ℝ)} =
        ({ω | (n : ℝ) ≤ Y 0 ω} ∩ {_ω | m ≤ i}) ∪
          ({ω | (n : ℝ) ≤ Y 0 ω}ᶜ ∩ {ω | hittingAfter Y (Set.Ici (n : ℝ)) 0 ω ≤ (i : WithTop ℝ)}) := by
      ext ω
      by_cases h : (n : ℝ) ≤ Y 0 ω <;> simp [h]
    rw [e]
    exact (hA.inter (MeasurableSet.const _)).union (hA.compl.inter h0)
  · intro n ω t ht0 hle
    by_cases h : (n : ℝ) ≤ Y 0 ω
    · simp only [h, if_true] at hle
      exfalso
      have : t ≤ m := by exact_mod_cast hle
      linarith
    · simp only [h, if_false] at hle
      cases hc' : hittingAfter Y (Set.Ici (n : ℝ)) 0 ω with
      | top =>
        have := (hittingAfter_eq_top_iff (u := Y) (s := Set.Ici (n : ℝ)) (n := 0) (ω := ω)).1 hc' t ht0
        exact (not_le.1 this).le
      | coe c =>
        rw [hc'] at hle
        exact le_of_le_hittingAfter (hc ω) n (not_le.1 h).le hc' ht0 (by exact_mod_cast hle)
  · intro ω T
    obtain ⟨n0, hn0⟩ := hittingAfter_Ici_tendsto_top Y ω (hc ω) T
    obtain ⟨n1, hn1⟩ := exists_nat_gt (Y 0 ω)
    refine ⟨max n0 n1, ?_⟩
    have h : ¬ (((max n0 n1 : ℕ) : ℝ) ≤ Y 0 ω) := by
      rw [not_le]
      exact lt_of_lt_of_le hn1 (by exact_mod_cast le_max_right n0 n1)
    simp only [h, if_false]
    exact hn0.trans (hittingAfter_anti Y 0 (Set.Ici_subset_Ici.2 (Nat.cast_le.2 (le_max_left n0 n1))) ω)

open Classical in
theorem isStoppingTime_modify {τ : Ω → WithTop ℝ} (hτ : IsStoppingTime ℱ τ) {N : Set Ω}
    (hN : ∀ t, MeasurableSet[ℱ t] N) (m : ℝ) :
    IsStoppingTime ℱ (fun ω => if ω ∈ N then (m : WithTop ℝ) else τ ω) := by
  classical
  intro i
  have e : {ω | (if ω ∈ N then (m : WithTop ℝ) else τ ω) ≤ (i : WithTop ℝ)} =
      (N ∩ {_ω | (m : WithTop ℝ) ≤ i}) ∪ (Nᶜ ∩ {ω | τ ω ≤ (i : WithTop ℝ)}) := by
    ext ω
    by_cases h : ω ∈ N <;> simp [h]
  rw [e]
  exact ((hN i).inter (MeasurableSet.const _)).union ((hN i).compl.inter (hτ i))

theorem sqIntegralOn_congr_ae {Φ Φ' : ℝ → Ω → ι → ℝ} (h : ∀ᵐ ω ∂P, ∀ s, Φ s ω = Φ' s ω) (T : ℝ) :
    sqIntegralOn P Φ T = sqIntegralOn P Φ' T := by
  unfold sqIntegralOn
  refine lintegral_congr_ae ?_
  filter_upwards [h] with ω hω
  simp_rw [hω]

theorem localItoIntegral_congr_null [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    {Ψ Ψ' : ℝ → Ω → ι → ℝ} (hΨ' : IsProgressiveLocL2 P ℱ Ψ') {N : Set Ω}
    (hNm : MeasurableSet N) (hN0 : P N = 0) (h : ∀ s, ∀ ω ∉ N, Ψ s ω = Ψ' s ω)
    (hneg : ∀ s < 0, ∀ ω, Ψ s ω = 0) (hneg' : ∀ s < 0, ∀ ω, Ψ' s ω = 0) :
    ∀ᵐ ω ∂P, ∀ t, localItoIntegral P ℱ W Ψ t ω = localItoIntegral P ℱ W Ψ' t ω := by
  classical
  have hNae : ∀ᵐ ω ∂P, ω ∉ N := measure_eq_zero_iff_ae_notMem.1 hN0
  have hstop : ∀ τ : Ω → WithTop ℝ, ∀ᵐ ω ∂P, ∀ s, stopIntegrand Ψ τ s ω = stopIntegrand Ψ' τ s ω := by
    intro τ
    filter_upwards [hNae] with ω hω s
    by_cases hc : (s : WithTop ℝ) ≤ τ ω <;> simp [stopIntegrand, Set.indicator, hc, h s ω hω]
  have hL' := isLocalItoIntegral_localItoIntegral hW hΨ'
  have hA : IsLocalItoIntegral P ℱ W Ψ (localItoIntegral P ℱ W Ψ') := by
    refine ⟨hL'.cont, hL'.adapted, hL'.zero, fun τ hτ hL2 => ?_⟩
    have hL2' : IsProgressiveL2 P ℱ (stopIntegrand Ψ' τ) :=
      ⟨isProgressive_stopIntegrand hΨ'.prog hτ, fun T => by
        rw [← sqIntegralOn_congr_ae (hstop τ) T]; exact hL2.sq T⟩
    have h0 : ∀ T, sqIntegralOn P (fun s ω => stopIntegrand Ψ' τ s ω - stopIntegrand Ψ τ s ω) T
        = 0 := by
      intro T
      rw [sqIntegralOn_congr_ae (Φ' := fun _ _ => 0)]
      · simp [sqIntegralOn]
      · filter_upwards [hstop τ] with ω hω s
        simp [hω s]
    filter_upwards [localItoIntegral_stopIntegrand hW hΨ' hτ,
      localItoIntegral_eq_itoIntegral hW hL2', itoIntegral_congr hW hL2' hL2 h0] with ω h1 h2 h3 t
    rw [← h1 t, h2 t, h3 t]
  have hex : ∃ M, IsLocalItoIntegral P ℱ W Ψ M := ⟨_, hA⟩
  have hM : IsLocalItoIntegral P ℱ W Ψ (localItoIntegral P ℱ W Ψ) := by
    unfold localItoIntegral
    rw [dif_pos hex]
    exact hex.choose_spec
  have hbase := fun n : ℕ => isProgressiveL2_stopIntegrand_locTime hW.complete hΨ' n
  let ρ : ℕ → Ω → WithTop ℝ := fun n ω => if ω ∈ N then (((-1 : ℝ)) : WithTop ℝ) else locTime Ψ' n ω
  have hρ : ∀ n, IsStoppingTime ℱ (ρ n) := fun n =>
    isStoppingTime_modify (isStoppingTime_locTime hW.complete hΨ' n)
      (fun t => hW.complete t N hNm hN0) (-1)
  have heq : ∀ n, stopIntegrand Ψ (ρ n) = stopIntegrand Ψ' (ρ n) := by
    intro n
    funext s ω
    by_cases hω : ω ∈ N
    · funext k
      by_cases hs : s < 0
      · simp [stopIntegrand, Set.indicator, hneg s hs, hneg' s hs]
      · have : ¬ ((s : WithTop ℝ) ≤ ρ n ω) := by
          simp only [ρ, hω, ite_true]
          intro hle
          have : s ≤ -1 := by exact_mod_cast hle
          exact hs (by linarith)
        simp [stopIntegrand, this]
    · by_cases hc : (s : WithTop ℝ) ≤ ρ n ω <;> simp [stopIntegrand, Set.indicator, hc, h s ω hω]
  have hprog : ∀ n, IsProgressiveL2 P ℱ (stopIntegrand Ψ (ρ n)) := by
    intro n
    rw [heq n]
    refine (hbase n).of_dom (isProgressive_stopIntegrand hΨ'.prog (hρ n)) (C := 1) (by simp)
      (fun s ω k => ?_)
    by_cases hω : ω ∈ N
    · by_cases hs : s < 0
      · simp [stopIntegrand, Set.indicator, hneg' s hs]
      · have : ¬ ((s : WithTop ℝ) ≤ ρ n ω) := by
          simp only [ρ, hω, ite_true]
          intro hle
          have : s ≤ -1 := by exact_mod_cast hle
          exact hs (by linarith)
        simp [stopIntegrand, this]
    · have e : ρ n ω = locTime Ψ' n ω := by simp [ρ, hω]
      by_cases hc : (s : WithTop ℝ) ≤ locTime Ψ' n ω <;>
        simp [stopIntegrand, Set.indicator, e, hc]
  refine ae_eq_forall_of_stopped (ρ := ρ) ?_ (fun n => ?_)
  · filter_upwards [hNae, locTime_exhaust hΨ'] with ω hω hex T
    obtain ⟨n, hn⟩ := hex T
    exact ⟨n, by simpa [ρ, hω] using hn⟩
  · filter_upwards [hM.stopped (ρ n) (hρ n) (hprog n), hA.stopped (ρ n) (hρ n) (hprog n)]
      with ω h1 h2 t
    rw [h1 t, h2 t]

end FormulaProofs


section Formula

variable {P : Measure Ω} {ℱ : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ι → ℝ}

/-- **Itô's formula** for `f ∈ C^{1,2}([0,T] × E)` and `X = X₀ + ∫ b + ∫ Φ dW`: a.s. the drift
is integrable on `[0, T]` and for all `t ∈ [0, T]`
`f(t, X_t) = f(0, X₀) + ∫_0^t itoDrift + ∫_0^t D_x f(s, X_s)[Φ_s] · dW_s`. -/
theorem ito_formula [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) {T : ℝ}
    (hT : 0 ≤ T) (f : ℝ → E → ℝ) (hf : IsC12On T Set.univ f) (X₀ : Ω → E)
    (hX₀ : ∀ t : ℝ, Measurable[ℱ t] X₀) (b : ℝ → Ω → E) (hb : IsProgressiveLocL1 P ℱ b)
    (Φ : ℝ → Ω → ι → E) (hΦ : IsProgressiveLocL2E P ℱ Φ) :
    let X := itoProcess P ℱ W X₀ b Φ
    ∀ᵐ ω ∂P, IntegrableOn (fun s => itoDrift T f X b Φ s ω) (Set.Icc 0 T) ∧
      ∀ t ∈ Set.Icc 0 T, f t (X t ω) = f 0 (X₀ ω) +
        (∫ s in Set.Icc 0 t, itoDrift T f X b Φ s ω) +
        localItoIntegral P ℱ W (itoIntegrand T Set.univ f X Φ) t ω := by
  intro X
  classical
  have hXprog : IsProgressive ℱ X := isProgressive_itoProcess X₀ hX₀ b hb.prog Φ
  obtain ⟨N, hNm, hN0, hNc⟩ : ∃ N : Set Ω, MeasurableSet N ∧ P N = 0 ∧
      ∀ ω ∉ N, Continuous fun t => X t ω := by
    have h := continuous_itoProcess X₀ b hb Φ (P := P) (W := W)
    refine ⟨toMeasurable P {ω | ¬ Continuous fun t => X t ω}, measurableSet_toMeasurable _ _, ?_, ?_⟩
    · rw [measure_toMeasurable]; exact ae_iff.1 h
    · intro ω hω; by_contra hc; exact hω (subset_toMeasurable _ _ hc)
  have hN : ∀ t, MeasurableSet[ℱ t] N := fun t => hW.complete t N hNm hN0
  let Y : ℝ → Ω → ℝ := fun t ω => if ω ∈ N then 0 else ‖X t ω‖
  have hYad : Adapted ℱ Y := fun t =>
    Measurable.ite (m := ℱ t) (hN t) measurable_const (measurable_norm.comp (hXprog.adapted t))
  have hYc : ∀ ω, Continuous fun t => Y t ω := by
    intro ω
    by_cases h : ω ∈ N
    · simp [Y, h]; exact continuous_const
    · simp only [Y, h, ite_false]; exact (hNc ω h).norm
  have hY0 : ∀ t, Measurable[ℱ t] (Y 0) := fun t =>
    Measurable.ite (m := ℱ t) (hN t) measurable_const (by
      have : X 0 = X₀ := funext fun ω => itoProcess_zero P ℱ W X₀ b Φ ω
      show Measurable[ℱ t] (fun ω => ‖X 0 ω‖)
      rw [this]; exact measurable_norm.comp (hX₀ t))
  obtain ⟨τ, hτ, hτle, hτex⟩ := exists_radius_times hYad hYc hY0
  have hXK : ∀ n : ℕ, ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc 0 T, (t : WithTop ℝ) ≤ τ n ω →
      X t ω ∈ Metric.closedBall (0 : E) n := by
    intro n
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω t ht hle
    have := hτle n ω t ht.1 hle
    simpa [Y, hω] using this
  have hloc := fun n : ℕ => ito_formula_localized_proof hW hT Set.univ isOpen_univ _
    (isCompact_closedBall (0 : E) n) (Set.subset_univ _) f hf X₀ hX₀ b hb Φ hΦ (τ n) (hτ n) (hXK n)
  have hXc := continuous_itoProcess X₀ b hb Φ (P := P) (W := W)
  have hΨ : IsProgressiveLocL2 P ℱ (itoIntegrand T Set.univ f X Φ) :=
    isProgressiveLocL2_itoIntegrand Set.univ isClosed_univ Set.univ (Set.Subset.refl _) f hf X
      hXprog hXc Φ hΦ
  have hΨn : ∀ n : ℕ, IsProgressiveLocL2 P ℱ (itoIntegrand T (Metric.closedBall (0 : E) n) f X Φ) :=
    fun n => isProgressiveLocL2_itoIntegrand _ Metric.isClosed_closedBall Set.univ
      (Set.subset_univ _) f hf X hXprog hXc Φ hΦ
  have hid : ∀ n : ℕ, ∀ᵐ ω ∂P, ∀ t : ℝ, (t : WithTop ℝ) ≤ τ n ω →
      localItoIntegral P ℱ W (stopIntegrand (itoIntegrand T (Metric.closedBall (0 : E) n) f X Φ)
        (τ n)) t ω = localItoIntegral P ℱ W (itoIntegrand T Set.univ f X Φ) t ω := by
    intro n
    have hcongr := localItoIntegral_congr hW ((hΨn n).stopIntegrand (hτ n))
      (hΨ.stopIntegrand (hτ n)) (by
        filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω
        refine Filter.Eventually.of_forall fun s => ?_
        funext k
        by_cases h1 : (s : WithTop ℝ) ≤ τ n ω
        · by_cases h2 : s ∈ Set.Icc 0 T
          · have h3 : X s ω ∈ Metric.closedBall (0 : E) n := by
              have := hτle n ω s h2.1 h1
              simpa [Y, hω] using this
            have h4 : ‖X s ω‖ ≤ n := by simpa using h3
            simp [stopIntegrand, itoIntegrand, Set.indicator, h1, h2, not_lt.2 h4]
          · simp [stopIntegrand, itoIntegrand, Set.indicator, h1, h2]
        · simp [stopIntegrand, h1])
    filter_upwards [hcongr, localItoIntegral_stopIntegrand hW hΨ (hτ n)] with ω h1 h2 t ht
    rw [h1 t, h2 t, stoppedProcess_eq_of_le ht]
  filter_upwards [ae_all_iff.2 hloc, ae_all_iff.2 hid] with ω hl hi
  obtain ⟨n0, hn0⟩ := hτex ω T
  refine ⟨((hl n0) T ⟨hT, le_rfl⟩ hn0).1, fun t ht => ?_⟩
  obtain ⟨n, hn⟩ := hτex ω t
  obtain ⟨_, h2⟩ := hl n t ht hn
  rw [h2, hi n t hn]

/-- **Itô's formula, localised**: `f ∈ C^{1,2}([0,T] × U)`, `U` open, and the Itô process stays
in a compact `K ⊆ U` up to the stopping time `τ`; then a.s. for all `t ∈ [0, T]` with `t ≤ τ`,
`f(t, X_t) = f(0, X₀) + ∫_0^t itoDrift + ∫_0^t 1_{s ≤ τ} D_x f(s, X_s)[Φ_s] · dW_s`. -/
theorem ito_formula_localized [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) {T : ℝ}
    (hT : 0 ≤ T) (U : Set E) (hU : IsOpen U) (K : Set E) (hK : IsCompact K) (hKU : K ⊆ U)
    (f : ℝ → E → ℝ) (hf : IsC12On T U f) (X₀ : Ω → E) (hX₀ : ∀ t : ℝ, Measurable[ℱ t] X₀)
    (b : ℝ → Ω → E) (hb : IsProgressiveLocL1 P ℱ b) (Φ : ℝ → Ω → ι → E)
    (hΦ : IsProgressiveLocL2E P ℱ Φ) (τ : Ω → WithTop ℝ) (hτ : IsStoppingTime ℱ τ)
    (hXK : ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc 0 T, (t : WithTop ℝ) ≤ τ ω → itoProcess P ℱ W X₀ b Φ t ω ∈ K) :
    let X := itoProcess P ℱ W X₀ b Φ
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc 0 T, (t : WithTop ℝ) ≤ τ ω →
      IntegrableOn (fun s => itoDrift T f X b Φ s ω) (Set.Icc 0 t) ∧
      f t (X t ω) = f 0 (X₀ ω) + (∫ s in Set.Icc 0 t, itoDrift T f X b Φ s ω) +
        localItoIntegral P ℱ W (stopIntegrand (itoIntegrand T K f X Φ) τ) t ω := by
  exact ito_formula_localized_proof hW hT U hU K hK hKU f hf X₀ hX₀ b hb Φ hΦ τ hτ hXK

/-- **Itô's formula with additive noise**, in the shape of `IsStrongSolution.lift`
(`HRS/Dynamics/Setup.lean`): `X : ℝ≥0 → Ω → E` measurable with, a.s. for all `t ≤ T`,
`X_t = X_0 + ∫_0^t b_s ds + ∑_k (W^k_t - W^k_0) σ_k`, `b` progressive with integrable paths on
`[0, T]`, `X_0` `ℱ_t`-measurable; then a.s. for all `t ≤ T`
`f(t, X_t) = f(0, X_0) + ∫_0^t [∂_s f + D_x f[b_s] + ½ ∑_k D_x² f[σ_k, σ_k]](s, X_s) ds
  + ∫_0^t (k ↦ D_x f(s, X_s)[σ_k]) · dW_s`
(M L1682-1686 `B:eq:ito-step` with `σ_{(i,j)} = √(2/β_N) e_{(i,j)}`; L11811). -/
theorem ito_formula_additive [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) {T : ℝ}
    (hT : 0 ≤ T) (f : ℝ → E → ℝ) (hf : IsC12On T Set.univ f) (σ : ι → E)
    (X : ℝ≥0 → Ω → E) (hXmeas : ∀ t, Measurable (X t))
    (hX₀ : ∀ t : ℝ, Measurable[ℱ t] (X 0)) (b : ℝ≥0 → Ω → E)
    (hb : IsProgressive ℱ (ofNNRealTime b))
    (hbint : ∀ᵐ ω ∂P, IntegrableOn (fun s : ℝ => b (Real.toNNReal s) ω) (Set.Icc 0 T))
    (hX : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T →
      X t ω = X 0 ω + (∫ s in Set.Icc (0 : ℝ) t, b (Real.toNNReal s) ω) +
        ∑ k, (W t ω k - W 0 ω k) • σ k) :
    ∀ᵐ ω ∂P,
      IntegrableOn (fun s => itoDrift T f (ofNNRealTime X) (ofNNRealTime b) (fun _ _ => σ) s ω)
        (Set.Icc 0 T) ∧
      ∀ t : ℝ≥0, (t : ℝ) ≤ T →
        f t (X t ω) = f 0 (X 0 ω) +
          (∫ s in Set.Icc (0 : ℝ) t,
            itoDrift T f (ofNNRealTime X) (ofNNRealTime b) (fun _ _ => σ) s ω) +
          localItoIntegral P ℱ W (itoIntegrand T Set.univ f (ofNNRealTime X) (fun _ _ => σ)) t ω := by
  classical
  let b' : ℝ → Ω → E := fun s ω => if s ≤ T then b (Real.toNNReal s) ω else 0
  have hb'prog : IsProgressive ℱ b' := by
    intro i
    letI : MeasurableSpace (Set.Iic i × Ω) := Subtype.instMeasurableSpace.prod (ℱ i)
    have h1 := hb i
    have hs : MeasurableSet {p : Set.Iic i × Ω | (p.1 : ℝ) ≤ T} :=
      (measurable_subtype_coe.comp measurable_fst) measurableSet_Iic
    exact Measurable.ite hs h1 measurable_const
  have hb'int : ∀ T' : ℝ, ∀ᵐ ω ∂P, IntegrableOn (fun s => b' s ω) (Set.Icc 0 T') := by
    intro T'
    filter_upwards [hbint] with ω hω
    have e : (fun s => b' s ω) = Set.indicator (Set.Iic T) (fun s => b (Real.toNNReal s) ω) := by
      funext s; simp [b', Set.indicator]
    rw [e, IntegrableOn, integrable_indicator_iff measurableSet_Iic, IntegrableOn,
      Measure.restrict_restrict measurableSet_Iic]
    refine hω.mono_set ?_
    intro s hs
    exact ⟨hs.2.1, hs.1⟩
  have hb' : IsProgressiveLocL1 P ℱ b' := ⟨hb'prog, hb'int⟩
  have hΦ : IsProgressiveLocL2E P ℱ (fun (_ : ℝ) (_ : Ω) => σ) := by
    refine ⟨isProgressive_const ℱ σ, fun T => ae_of_all _ fun ω => ?_⟩
    rw [lintegral_const]
    exact ENNReal.mul_lt_top (by simp) (by simp)
  have hIto := ito_formula hW hT f hf (X 0) hX₀ b' hb' (fun _ _ => σ) hΦ
  dsimp only at hIto
  have hXt : ∀ᵐ ω ∂P, ∀ s ∈ Set.Icc (0 : ℝ) T, ofNNRealTime X s ω =
      itoProcess P ℱ W (X 0) b' (fun _ _ => σ) s ω := by
    filter_upwards [hX, localItoIntegralE_const hW σ] with ω h1 h2 s hs
    have h3 := h1 (Real.toNNReal s) (by rw [Real.coe_toNNReal _ hs.1]; exact hs.2)
    have h4 : (∫ r in Set.Icc (0 : ℝ) (Real.toNNReal s : ℝ), b (Real.toNNReal r) ω) =
        ∫ r in Set.Icc (0 : ℝ) s, b' r ω := by
      rw [Real.coe_toNNReal _ hs.1]
      refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
      simp [b', hr.2.trans hs.2]
    simp only [ofNNRealTime_apply, itoProcess]
    rw [h3, h4, h2 s, hW.zero]
    simp
  obtain ⟨N, hNm, hN0, hN⟩ : ∃ N : Set Ω, MeasurableSet N ∧ P N = 0 ∧
      ∀ ω ∉ N, ∀ s ∈ Set.Icc (0 : ℝ) T, ofNNRealTime X s ω =
        itoProcess P ℱ W (X 0) b' (fun _ _ => σ) s ω := by
    refine ⟨toMeasurable P {ω | ¬ ∀ s ∈ Set.Icc (0 : ℝ) T, ofNNRealTime X s ω =
        itoProcess P ℱ W (X 0) b' (fun _ _ => σ) s ω}, measurableSet_toMeasurable _ _, ?_, ?_⟩
    · rw [measure_toMeasurable]; exact ae_iff.1 hXt
    · intro ω hω; by_contra hc; exact hω (subset_toMeasurable _ _ hc)
  have hXprog : IsProgressive ℱ (itoProcess P ℱ W (X 0) b' (fun _ _ => σ)) :=
    isProgressive_itoProcess (X 0) hX₀ b' hb'prog _
  have hΨ' : IsProgressiveLocL2 P ℱ
      (itoIntegrand T Set.univ f (itoProcess P ℱ W (X 0) b' (fun _ _ => σ)) (fun _ _ => σ)) :=
    isProgressiveLocL2_itoIntegrand Set.univ isClosed_univ Set.univ (Set.Subset.refl _) f hf _
      hXprog (continuous_itoProcess (X 0) b' hb' _) _ hΦ
  have hL := localItoIntegral_congr_null hW hΨ' hNm hN0 (Ψ := itoIntegrand T Set.univ f (ofNNRealTime X) (fun _ _ => σ))
    (fun s ω hω => by
      funext k
      by_cases hs : s ∈ Set.Icc 0 T
      · have e := hN ω hω s hs
        simp only [ofNNRealTime_apply] at e
        simp [itoIntegrand, Set.indicator, hs, e]
      · simp [itoIntegrand, Set.indicator, hs])
    (fun s hs ω => by
      funext k; simp [itoIntegrand, Set.indicator, not_le.2 hs, Set.mem_Icc])
    (fun s hs ω => by
      funext k; simp [itoIntegrand, Set.indicator, not_le.2 hs, Set.mem_Icc])
  filter_upwards [hIto, hL, measure_eq_zero_iff_ae_notMem.1 hN0] with ω hI hl hω
  have hd : ∀ s ∈ Set.Icc (0 : ℝ) T,
      itoDrift T f (itoProcess P ℱ W (X 0) b' (fun _ _ => σ)) b' (fun _ _ => σ) s ω =
      itoDrift T f (ofNNRealTime X) (ofNNRealTime b) (fun _ _ => σ) s ω := by
    intro s hs
    have e1 := hN ω hω s hs
    have e2 : b' s ω = ofNNRealTime b s ω := by simp [b', hs.2]
    unfold itoDrift
    rw [← e1, e2]
  refine ⟨hI.1.congr_fun hd measurableSet_Icc, fun t ht => ?_⟩
  have ht' : (t : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨t.2, ht⟩
  have h5 := hI.2 (t : ℝ) ht'
  have e3 : itoProcess P ℱ W (X 0) b' (fun _ _ => σ) (t : ℝ) ω = X t ω := by
    rw [← hN ω hω t ht']; simp
  rw [e3] at h5
  rw [h5, hl (t : ℝ)]
  congr 2
  exact setIntegral_congr_fun measurableSet_Icc fun s hs => hd s ⟨hs.1, hs.2.trans ht⟩

/-- Additive noise, time-independent `g ∈ C²(E)`: the drift is
`D g(X_s)[b_s] + ½ ∑_k D² g(X_s)[σ_k, σ_k]` (M L11805-11811 for `Q_I`, S L11165 for `|x|²`). -/
theorem ito_formula_additive_time_independent [IsProbabilityMeasure P]
    (hW : IsBrownianFiltration P ℱ W) {T : ℝ} (hT : 0 ≤ T) (g : E → ℝ) (hg : ContDiff ℝ 2 g)
    (σ : ι → E) (X : ℝ≥0 → Ω → E) (hXmeas : ∀ t, Measurable (X t))
    (hX₀ : ∀ t : ℝ, Measurable[ℱ t] (X 0)) (b : ℝ≥0 → Ω → E)
    (hb : IsProgressive ℱ (ofNNRealTime b))
    (hbint : ∀ᵐ ω ∂P, IntegrableOn (fun s : ℝ => b (Real.toNNReal s) ω) (Set.Icc 0 T))
    (hX : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T →
      X t ω = X 0 ω + (∫ s in Set.Icc (0 : ℝ) t, b (Real.toNNReal s) ω) +
        ∑ k, (W t ω k - W 0 ω k) • σ k) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T →
      g (X t ω) = g (X 0 ω) +
        (∫ s in Set.Icc (0 : ℝ) t, fderiv ℝ g (X (Real.toNNReal s) ω) (b (Real.toNNReal s) ω) +
          (1 / 2) * ∑ k, fderiv ℝ (fderiv ℝ g) (X (Real.toNNReal s) ω) (σ k) (σ k)) +
        localItoIntegral P ℱ W
          (itoIntegrand T Set.univ (fun _ x => g x) (ofNNRealTime X) (fun _ _ => σ)) t ω := by
  have h := ito_formula_additive hW hT (fun _ x => g x) (isC12On_of_contDiff T Set.univ g hg) σ X
    hXmeas hX₀ b hb hbint hX
  filter_upwards [h] with ω hω t ht
  rw [(hω.2 t ht)]
  congr 2
  refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
  simp [itoDrift]

end Formula

end HRS
