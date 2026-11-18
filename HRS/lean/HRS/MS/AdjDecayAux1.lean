import HRS.MS.AdjVerifAux2

/-!
# AD-3, part 1: the engine for the Duhamel integral `∫_r^t lcSg r u (S u) du` (supplement S4.12)

Infrastructure for `adjoint_decay_proof` (S4.12); not a manuscript row.

**Statement** (`ad3_int_engine`).  Same data as `lc_engine` (`lcSg` of the LC engine, constant viscosity `ν`),
and a family of sources `S u` (`u ∈ [r,t]`) which are `C^k`, jointly continuous on `[0,t] × ℝ^d`, with
`decayNormE k b (S u) ≤ ofReal D` uniformly in `u ∈ [r,t]`.  Then `x ↦ ∫_r^t lcSg r u (S u) x du` is `C^k` and
`⟨x⟩^{b+j} ‖D^j (∫_r^t lcSg r u (S u) du)(x)‖ ≤ C D` for `j ≤ k`, with `C` depending only on
`d, s, Q, k, T, ν*, b, Λc, ΛB`.

Proof.  The pair `(u, ω) ↦ S_u (X_u^{r,x}(ω))` on `(Ioc r t, dx) × (Ω, P)` is differentiated under the integral
sign (`lc4_iteratedFDeriv_integral` with the product measure, pathwise bound from `lc_chain_decay` and the
sup-moment `lc_sup_moment`, exactly as in `lc_engine`), and Fubini identifies the result with the interval
integral of `lcSg`.  Differentiation under the `du`-integral needs no joint continuity of derivatives in `u`
because the whole `(u, ω)` integral is treated at once.

Statement adjustments: `r < t` is assumed (the case `r = t` is empty); `ν` is a constant `0 ≤ ν ≤ ν*`.
-/

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open HRS HRS.Whole HRS.MS.Lc HRS.MD.EQLawPath HRS.MS.PoisKolm HRS.MS.AdjVerif

noncomputable section

universe u

namespace HRS.MS.AdjDecay

variable {d : ℕ}

/-- **AD-3 (engine for the Duhamel integral).**  See the file docstring. -/
theorem ad3_int_engine (s : ℝ) (hs : 0 ≤ s) (Q : Matrix (Fin d) (Fin d) ℝ) (k : ℕ)
    (T νstar bexp Λc ΛB : ℝ) (hb : 0 < bexp) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → Fin d → ℝ) (ν : ℝ) (c : ℝ → Euc d)
      (B : ℝ → Euc d → Euc d),
      IsBrownianFiltration P ℱ W → 0 ≤ ν → ν ≤ νstar →
      LcHyp Q k Λc ΛB c B →
      (∀ v, 0 ≤ v → decayNormVecE (k + 1) (s + 1) (B v) ≤ ENNReal.ofReal ΛB) →
      ∀ (S : ℝ → Euc d → ℝ) (D : ℝ), 0 ≤ D →
      ∀ r t : ℝ, 0 ≤ r → r < t → t ≤ T →
      ContinuousOn (fun p : ℝ × Euc d => S p.1 p.2) (Icc 0 t ×ˢ univ) →
      (∀ u ∈ Icc r t, ContDiff ℝ (k : WithTop ℕ∞) (S u) ∧
        decayNormE k bexp (S u) ≤ ENNReal.ofReal D) →
      ContDiff ℝ (k : WithTop ℕ∞)
        (fun x => ∫ u in r..t, lcSg P W (fun _ => ν) Q c B r u (S u) x) ∧
      ∀ j ≤ k, ∀ x : Euc d, jbracket x ^ (bexp + (j : ℝ)) *
        ‖iteratedFDeriv ℝ j
          (fun x => ∫ u in r..t, lcSg P W (fun _ => ν) Q c B r u (S u) x) x‖ ≤ C * D := by
  obtain ⟨C0, hC01, N, hN⟩ := lc_chain_decay Q k s hs T Λc ΛB bexp hb.le
  obtain ⟨Cm, hCm⟩ := lc_sup_moment.{u} d N T νstar
  obtain ⟨Cu, hCu0, hCu⟩ := lc_U_bound Q T
  set A : ℝ := max 1 Cu with hA
  have hA1 : 1 ≤ A := le_max_left _ _
  have hAu : Cu ≤ A := le_max_right _ _
  have hC00 : 0 ≤ C0 := by linarith
  refine ⟨max T 0 * (C0 * A ^ N * max Cm 0), by positivity, ?_⟩
  intro Ω mΩ P hP ℱ W ν c B hW hν0 hνs H hdec S D hD r t hr hrt htT hSc hSd
  have hν : Continuous (fun _ : ℝ => ν) := continuous_const
  have hνb : ∀ _r : ℝ, 0 ≤ ν ∧ ν ≤ νstar := fun _ => ⟨hν0, hνs⟩
  have hrt' : r ≤ t := hrt.le
  set G : Ω → ℝ → Euc d := fun ω v => lcNoiseE W (fun _ => ν) v ω with hGdef
  have hGm : ∀ v, Measurable fun ω => G ω v := fun v => lc_noiseE_measurable hW v
  have hGc : ∀ ω, Continuous (G ω) := fun ω => lc_noiseE_cont hW hν ω
  set Sup : Ω → ℝ := fun ω => ⨆ v ∈ Icc (0 : ℝ) T, ‖lcNoiseE W (fun _ => ν) v ω‖ with hSup
  have hSup0 : ∀ ω, 0 ≤ Sup ω := fun ω =>
    lc3_sup_nonneg (g := fun v => lcNoiseE W (fun _ => ν) v ω) T
  obtain ⟨hint, hmom⟩ := hCm P ℱ W (fun _ => ν) hW hν hνb
  set K0 : ℝ := C0 * A ^ N * D with hK0
  have hK00 : 0 ≤ K0 := by positivity
  set Φ : ℝ × Ω → ℝ := fun q => K0 * (1 + Sup q.2) ^ N with hΦdef
  -- the clamped time
  set cl : ℝ → ℝ := fun v => max r (min v t) with hcl
  have hclc : Continuous cl := continuous_const.max (continuous_id.min continuous_const)
  have hclm : ∀ v, cl v ∈ Icc r t := fun v => ⟨le_max_left _ _, max_le hrt' (min_le_right _ _)⟩
  have hclid : ∀ v ∈ Ioc r t, cl v = v := fun v hv => by
    simp only [hcl]; rw [min_eq_left hv.2, max_eq_right hv.1.le]
  set μ : Measure ℝ := volume.restrict (Ioc r t) with hμ
  haveI : IsFiniteMeasure μ := by rw [hμ]; infer_instance
  have hΦint : Integrable Φ (μ.prod P) := (hint.const_mul K0).comp_snd μ
  set G' : ℝ × Ω → Euc d → ℝ := fun q y =>
    S (cl q.1) (lcFlow Q c B (G q.2) r (cl q.1) y) with hG'
  have hGfun : ∀ q, ContDiff ℝ (k : WithTop ℕ∞) (G' q) := fun q =>
    (hSd _ (hclm q.1)).1.comp
      ((lcFlow_contDiff H (hGc q.2) hr (hclm q.1).1).of_le (by exact_mod_cast Nat.le_succ k))
  have hpt : ∀ q : ℝ × Ω, ∀ j ≤ k, ∀ x, jbracket x ^ (bexp + (j : ℝ)) *
      ‖iteratedFDeriv ℝ j (G' q) x‖ ≤ Φ q := by
    intro q j hj x
    have hκ : ∀ w ∈ Icc r (cl q.1), ‖lcU Q (G q.2) r w‖ ≤ Cu * Sup q.2 := fun w hw =>
      hCu (hGc q.2) r w hr hw.1 (hw.2.trans ((hclm q.1).2.trans htT))
    have h1 := hN c B H hdec (G q.2) (hGc q.2) r (cl q.1) (Cu * Sup q.2) hr (hclm q.1).1
      ((hclm q.1).2.trans htT) hκ (S (cl q.1)) (hSd _ (hclm q.1)).1 j hj x
    have h1' := h1.trans (mul_le_mul' le_rfl (hSd _ (hclm q.1)).2)
    have hS1 := hSup0 q.2
    have hbase : 0 ≤ 1 + Cu * Sup q.2 := by positivity
    have hle : 1 + Cu * Sup q.2 ≤ A * (1 + Sup q.2) := by nlinarith
    have hpow : (1 + Cu * Sup q.2) ^ N ≤ A ^ N * (1 + Sup q.2) ^ N := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hbase hle N
    rw [← ENNReal.ofReal_mul (by positivity)] at h1'
    have h2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1'
    refine h2.trans ?_
    calc C0 * (1 + Cu * Sup q.2) ^ N * D ≤ C0 * (A ^ N * (1 + Sup q.2) ^ N) * D := by gcongr
      _ = Φ q := by rw [hΦdef, hK0]; ring
  have hbd : ∀ i ≤ k, ∀ q x, ‖iteratedFDeriv ℝ i (G' q) x‖ ≤ Φ q := by
    intro i hi q x
    have h1 := hpt q i hi x
    have hjb : 1 ≤ jbracket x ^ (bexp + (i : ℝ)) :=
      Real.one_le_rpow (lc2_jb_ge_one x) (by positivity)
    have : 0 ≤ ‖iteratedFDeriv ℝ i (G' q) x‖ := norm_nonneg _
    nlinarith
  -- joint measurability
  have hSc' : Continuous fun p : ℝ × Euc d => S (cl p.1) p.2 := by
    have hq : Continuous fun p : ℝ × Euc d => (cl p.1, p.2) :=
      (hclc.comp continuous_fst).prodMk continuous_snd
    exact ContinuousOn.comp_continuous hSc hq
      (fun p => ⟨⟨hr.trans (hclm p.1).1, (hclm p.1).2.trans le_rfl⟩, mem_univ _⟩)
  have hXm : Measurable (fun p : ℝ × (Ω × Euc d) =>
      lcFlow Q c B (G p.2.1) r (cl p.1) p.2.2) := by
    have hcont : ∀ p : Ω × Euc d, Continuous fun v : ℝ => lcFlow Q c B (G p.1) r (cl v) p.2 := fun p => by
      have := (lcFlowExt_continuous_v H (hGc p.1) hr p.2).comp hclc
      refine this.congr (fun v => ?_)
      exact lcFlowExt_of_ge (hclm v).1 p.2
    have hmeas : ∀ v, Measurable fun p : Ω × Euc d => lcFlow Q c B (G p.1) r (cl v) p.2 := fun v =>
      lc4_meas_flow H hGm hGc hr (hclm v).1
    exact measurable_uncurry_of_continuous_of_measurable
      (u := fun (v : ℝ) (p : Ω × Euc d) => lcFlow Q c B (G p.1) r (cl v) p.2) hcont hmeas
  have hjointm : Measurable (fun p : (ℝ × Ω) × Euc d => G' p.1 p.2) := by
    have h3 : Measurable fun p : (ℝ × Ω) × Euc d => (p.1.1, (p.1.2, p.2)) := by fun_prop
    have h4 := hXm.comp h3
    exact hSc'.measurable.comp ((measurable_fst.comp measurable_fst).prodMk h4)
  have hjoint : StronglyMeasurable (fun p : (ℝ × Ω) × Euc d => G' p.1 p.2) :=
    hjointm.stronglyMeasurable
  have hmeas : ∀ i ≤ k, ∀ x, AEStronglyMeasurable (fun q => iteratedFDeriv ℝ i (G' q) x)
      (μ.prod P) := by
    intro i hi x
    have := PoisSg.sg_stronglyMeasurable_iteratedFDeriv G' hjoint i
      (fun q => (hGfun q).of_le (by exact_mod_cast hi))
    exact (this.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  obtain ⟨hcd, hform⟩ := lc4_iteratedFDeriv_integral (μ := μ.prod P) G' k hGfun hΦint hbd hmeas
  -- Fubini
  have hFint : ∀ x, Integrable (fun q => G' q x) (μ.prod P) := fun x =>
    Integrable.mono' hΦint
      ((hjoint.comp_measurable (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
      (Eventually.of_forall fun q => by
        have := hbd 0 (Nat.zero_le _) q x
        rwa [norm_iteratedFDeriv_zero] at this)
  have hfun : (fun x => ∫ u in r..t, lcSg P W (fun _ => ν) Q c B r u (S u) x) =
      fun x => ∫ q, G' q x ∂(μ.prod P) := by
    funext x
    rw [integral_prod _ (hFint x), intervalIntegral.integral_of_le hrt']
    refine (setIntegral_congr_fun measurableSet_Ioc (fun v hv => ?_)).symm
    simp only [hG', hclid v hv, lcSg, hGdef]
  rw [hfun]
  refine ⟨hcd, fun j hj x => ?_⟩
  rw [hform j hj x]
  have hjb : 0 ≤ jbracket x ^ (bexp + (j : ℝ)) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hmom' : ∫ ω, (1 + Sup ω) ^ N ∂P ≤ max Cm 0 := hmom.trans (le_max_left _ _)
  have hmu : μ.real univ = t - r := by
    rw [hμ, Measure.real, Measure.restrict_apply_univ, Real.volume_Ioc]
    exact ENNReal.toReal_ofReal (by linarith)
  have hΦI : ∫ q, Φ q ∂(μ.prod P) = (t - r) * (K0 * ∫ ω, (1 + Sup ω) ^ N ∂P) := by
    rw [integral_prod _ hΦint]
    simp only [hΦdef]
    rw [integral_const, hmu]
    simp only [integral_const_mul, smul_eq_mul]
  have hCpos : 0 ≤ max T 0 * (C0 * A ^ N * max Cm 0) := by positivity
  calc jbracket x ^ (bexp + (j : ℝ)) * ‖∫ q, iteratedFDeriv ℝ j (G' q) x ∂(μ.prod P)‖
      ≤ jbracket x ^ (bexp + (j : ℝ)) * ∫ q, ‖iteratedFDeriv ℝ j (G' q) x‖ ∂(μ.prod P) :=
        mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) hjb
    _ = ∫ q, jbracket x ^ (bexp + (j : ℝ)) * ‖iteratedFDeriv ℝ j (G' q) x‖ ∂(μ.prod P) :=
        (integral_const_mul _ _).symm
    _ ≤ ∫ q, Φ q ∂(μ.prod P) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun q => ?_) hΦint
          (Eventually.of_forall fun q => hpt q j hj x)
        exact mul_nonneg hjb (norm_nonneg _)
    _ = (t - r) * (K0 * ∫ ω, (1 + Sup ω) ^ N ∂P) := hΦI
    _ ≤ max T 0 * (K0 * max Cm 0) := by
        have h0 : 0 ≤ ∫ ω, (1 + Sup ω) ^ N ∂P := integral_nonneg fun ω => by
          have := hSup0 ω; positivity
        have h1 : t - r ≤ max T 0 := by
          have := le_max_left T 0
          linarith
        have h2 : K0 * ∫ ω, (1 + Sup ω) ^ N ∂P ≤ K0 * max Cm 0 :=
          mul_le_mul_of_nonneg_left hmom' hK00
        have h3 : 0 ≤ K0 * ∫ ω, (1 + Sup ω) ^ N ∂P := mul_nonneg hK00 h0
        exact mul_le_mul h1 h2 h3 (le_max_right T 0)
    _ = (max T 0 * (C0 * A ^ N * max Cm 0)) * D := by rw [hK0]; ring

/-! ### Deterministic chain rule (the case `ν = 0`) -/

/-- Chain rule for `v' ↦ F v' (γ v')` when `F` has a Fréchet derivative `Fx v' y` in `y` for `v'` near `v`,
`Fx` is continuous at `(v, γ v)`, `F · (γ v)` has time derivative `Ft` at `v`, and `γ` has derivative `γ'`. -/
theorem ad3_chain {F : ℝ → Euc d → ℝ} {Fx : ℝ → Euc d → (Euc d →L[ℝ] ℝ)} {Ft : ℝ} {γ : ℝ → Euc d}
    {γ' : Euc d} {v : ℝ} (hFx : ∀ᶠ v' in 𝓝 v, ∀ y, HasFDerivAt (F v') (Fx v' y) y)
    (hcont : ContinuousAt (fun p : ℝ × Euc d => Fx p.1 p.2) (v, γ v))
    (hFt : HasDerivAt (fun v' => F v' (γ v)) Ft v) (hγ : HasDerivAt γ γ' v) :
    HasDerivAt (fun v' => F v' (γ v')) (Ft + Fx v (γ v) γ') v := by
  set y₀ := γ v with hy₀
  set L₀ := Fx v y₀ with hL₀
  have hL : HasDerivAt (fun v' => L₀ (γ v')) (L₀ γ') v := L₀.hasFDerivAt.comp_hasDerivAt v hγ
  have hL' := hasDerivAt_iff_isLittleO.1 hL
  have hγ' := hasDerivAt_iff_isLittleO.1 hγ
  have he : (fun v' => (F v' (γ v') - F v' y₀) - L₀ (γ v' - y₀)) =o[𝓝 v] (fun v' => v' - v) := by
    rw [Asymptotics.isLittleO_iff]
    intro ε hε
    set M : ℝ := ‖γ'‖ + 1 with hM
    have hM0 : 0 < M := by positivity
    have hε' : 0 < ε / M := div_pos hε hM0
    obtain ⟨δ, hδ, hδp⟩ := Metric.continuousAt_iff.1 hcont (ε / M) hε'
    have h1 := (Asymptotics.isLittleO_iff.1 hγ') zero_lt_one
    have h2 : ∀ᶠ v' in 𝓝 v, |v' - v| < δ := by
      have : ∀ᶠ v' in 𝓝 v, dist v' v < δ := Metric.ball_mem_nhds v hδ
      exact this.mono fun v' h => by rwa [Real.dist_eq] at h
    have h3 : ∀ᶠ v' in 𝓝 v, γ v' ∈ Metric.ball y₀ δ :=
      hγ.continuousAt.eventually (Metric.ball_mem_nhds _ hδ)
    filter_upwards [hFx, h1, h2, h3] with v' hFx' h1' h2' h3'
    have hball : ∀ y ∈ Metric.ball y₀ δ, ‖Fx v' y - L₀‖ ≤ ε / M := by
      intro y hy
      have hd : dist (v', y) (v, y₀) < δ := by
        rw [Prod.dist_eq]
        exact max_lt (by rw [Real.dist_eq]; exact h2') (by rwa [Metric.mem_ball] at hy)
      have := hδp hd
      rw [dist_eq_norm] at this
      exact this.le
    have hmv := (convex_ball y₀ δ).norm_image_sub_le_of_norm_hasFDerivWithin_le
      (f := fun y => F v' y - L₀ y) (f' := fun y => Fx v' y - L₀) (s := Metric.ball y₀ δ)
      (C := ε / M) (x := y₀) (y := γ v')
      (fun y _ => ((hFx' y).sub L₀.hasFDerivAt).hasFDerivWithinAt) hball
      (Metric.mem_ball_self hδ) h3'
    have e1 : (F v' (γ v') - F v' y₀) - L₀ (γ v' - y₀) =
        (F v' (γ v') - L₀ (γ v')) - (F v' y₀ - L₀ y₀) := by
      rw [map_sub]; ring
    rw [Real.norm_eq_abs, e1]
    have hb : ‖γ v' - y₀‖ ≤ M * ‖v' - v‖ := by
      have h4 : ‖γ v' - y₀‖ ≤ ‖γ v' - γ v - (v' - v) • γ'‖ + ‖(v' - v) • γ'‖ := by
        have := norm_add_le (γ v' - γ v - (v' - v) • γ') ((v' - v) • γ')
        simpa using this
      rw [norm_smul] at h4
      rw [hM]
      nlinarith [norm_nonneg (v' - v), norm_nonneg γ']
    calc ‖(F v' (γ v') - L₀ (γ v')) - (F v' y₀ - L₀ y₀)‖ ≤ ε / M * ‖γ v' - y₀‖ := by
          simpa using hmv
      _ ≤ ε / M * (M * ‖v' - v‖) := mul_le_mul_of_nonneg_left hb hε'.le
      _ = ε * ‖v' - v‖ := by field_simp
  have hψ : HasDerivAt (fun v' => F v' (γ v') - F v' y₀) (L₀ γ') v := by
    rw [hasDerivAt_iff_isLittleO]
    refine (he.add hL').congr_left (fun v' => ?_)
    simp only [smul_eq_mul, map_sub]
    have : F v (γ v) - F v y₀ = 0 := by rw [hy₀]; ring
    rw [this]; ring
  have := hψ.add hFt
  convert this using 1
  · funext v'; simp
  · ring

/-- With constant viscosity `0` the noise vanishes. -/
theorem ad3_noise_zero {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
    {W : ℝ≥0 → Ω → Fin d → ℝ} (hW : IsBrownianFiltration P ℱ W) (v : ℝ) (ω : Ω) :
    lcNoiseE W (fun _ => (0 : ℝ)) v ω = 0 := by
  ext k
  simp [lcNoiseE, lcNoise, lcTau, hW.zero]

/-- **AD-3 (verification for `ν = 0`).**  The analogue of `ad_verification_sg` when `C.ν = 0`: the noise vanishes,
`lcSg r u g x = g (X_u^{r,x})` with `X` the (deterministic) flow, and the representation is the chain rule
`d/dv f(v, X_v) = S_v(X_v)` integrated over `[r,t]`.  (`ad_verification_sg` needs `0 < C.ν`, because it reads
the Ito formula in the time scale `2 ν v`.) -/
theorem ad3_verification_zero {Ω : Type u} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → Fin d → ℝ)
    (hW : IsBrownianFiltration P ℱ W) (Q : Matrix (Fin d) (Fin d) ℝ) (k : ℕ) (Λc ΛB : ℝ)
    (c : ℝ → Euc d) (B : ℝ → Euc d → Euc d) (H : LcHyp Q k Λc ΛB c B)
    (C : WholeCoeff d) (hν : C.ν = 0) {t : ℝ}
    (hdrift : ∀ u ∈ Icc 0 t, ∀ y, C.drift u y = B u y - lcQ Q y - c u)
    {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ} (hf : IsClassicalAdjointW C t φ f)
    (S : ℝ → Euc d → ℝ)
    (hS : ∀ u ∈ Icc 0 t, ∀ y, generatorW C u (f u) y = C.ν * Laplacian.laplacian (f u) y +
      inner ℝ (C.drift u y) (gradient (f u) y) - S u y)
    {r : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t) (x : Euc d) :
    IntervalIntegrable (fun u => lcSg P W (fun _ => C.ν) Q c B r u (S u) x) volume r t ∧
    f r x = lcSg P W (fun _ => C.ν) Q c B r t φ x -
      ∫ u in r..t, lcSg P W (fun _ => C.ν) Q c B r u (S u) x := by
  set X : ℝ → Euc d := fun u => lcFlow Q c B (fun _ => (0 : Euc d)) r u x with hX
  have hlcSg : ∀ u (g : Euc d → ℝ), lcSg P W (fun _ => C.ν) Q c B r u g x = g (X u) := by
    intro u g
    have hfun : ∀ ω, (fun v => lcNoiseE W (fun _ => C.ν) v ω) = fun _ => (0 : Euc d) := by
      intro ω; funext v; rw [hν]; exact ad3_noise_zero hW v ω
    simp only [lcSg, hfun, hX]
    simp
  have hg0 : Continuous (fun _ : ℝ => (0 : Euc d)) := continuous_const
  have hfun1 : (fun u => lcSg P W (fun _ => C.ν) Q c B r u (S u) x) = fun u => S u (X u) :=
    funext fun u => hlcSg u (S u)
  rw [hfun1, hlcSg t φ]
  rcases hrt.eq_or_lt with h | hlt
  · subst h
    refine ⟨IntervalIntegrable.refl, ?_⟩
    have h1 : X r = x := lcFlow_self H hg0 hr x
    rw [intervalIntegral.integral_same, h1, hf.terminal]
    simp
  have ht : 0 < t := lt_of_le_of_lt hr hlt
  have hf12 := ad2_isC12On ht hf
  have hSc := ad2_S_cont H C ht hdrift hf S hS
  -- continuity of the flow
  have hXc : Continuous fun u => lcFlowExt Q c B (fun _ => (0 : Euc d)) r u x :=
    lcFlowExt_continuous_v H hg0 hr x
  have hXcI : ContinuousOn X (Icc r t) :=
    hXc.continuousOn.congr fun u hu => (lcFlowExt_of_ge hu.1 x).symm
  -- derivative of the flow
  have hsol := lcFlow_isPathSolution H hg0 hr x
  have hXd : ∀ v ∈ Ioo r t, HasDerivAt X (C.drift v (X v)) v := by
    intro v hv
    have hτ : 0 < v - r := sub_pos.2 hv.1
    set Y : ℝ → Euc d := fun τ => lcFlow Q c B (fun _ => (0 : Euc d)) r (r + τ) x with hY
    have hYeq : ∀ τ : ℝ, 0 ≤ τ → Y τ = x + ∫ s in (0 : ℝ)..τ, lcB Q c B r s (Y s) := by
      intro τ hτ0
      obtain ⟨-, -, h⟩ := hsol.2 τ hτ0 (WithTop.coe_lt_top _)
      rw [← setIntegral_Icc_eq_interval hτ0]
      simpa [lcW] using h
    have hYc : ∀ τ' : ℝ, 0 ≤ τ' → ContinuousOn Y (Icc 0 τ') := fun τ' hτ' =>
      (hsol.2 τ' hτ' (WithTop.coe_lt_top _)).1
    have hI : ContinuousOn (fun s => lcB Q c B r s (Y s)) (Icc 0 (v - r + 1)) :=
      lcB_continuous H hr (fun τ hτ => hτ.1) (hYc _ (by linarith))
    have hIo : ContinuousOn (fun s => lcB Q c B r s (Y s)) (Ioo 0 (v - r + 1)) :=
      hI.mono Ioo_subset_Icc_self
    have hmem : v - r ∈ Ioo (0 : ℝ) (v - r + 1) := ⟨hτ, by linarith⟩
    have hint : IntervalIntegrable (fun s => lcB Q c B r s (Y s)) volume 0 (v - r) :=
      (hI.mono (fun s hs => by
        rw [Set.uIcc_of_le hτ.le] at hs
        exact ⟨hs.1, by linarith [hs.2]⟩ : Set.uIcc 0 (v - r) ⊆ Icc 0 (v - r + 1))).intervalIntegrable
    have hD := intervalIntegral.integral_hasDerivAt_right hint
      ((hIo.stronglyMeasurableAtFilter isOpen_Ioo _ hmem))
      (hIo.continuousAt (Ioo_mem_nhds hmem.1 hmem.2))
    have hD' : HasDerivAt Y (lcB Q c B r (v - r) (Y (v - r))) (v - r) := by
      refine (hD.const_add x).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hτ] with τ hτ'
      exact hYeq τ (le_of_lt hτ')
    have hD'' := hD'.comp_sub_const v r
    have e1 : (fun v' => Y (v' - r)) = X := by
      funext v'; simp [hY, hX]
    rw [e1] at hD''
    have e2 : Y (v - r) = X v := by simp [hY, hX]
    rw [e2] at hD''
    have e3 : C.drift v (X v) = lcB Q c B r (v - r) (X v) := by
      rw [hdrift v ⟨hr.trans hv.1.le, hv.2.le⟩]
      simp only [lcB, add_sub_cancel]
      abel
    rw [e3]; exact hD''
  -- the chain rule at interior points
  have hh : ∀ v ∈ Ioo r t, HasDerivAt (fun v' => f v' (X v')) (S v (X v)) v := by
    intro v hv
    have hv0 : v ∈ Ioo 0 t := ⟨hr.trans_lt hv.1, hv.2⟩
    have hFx : ∀ᶠ v' in 𝓝 v, ∀ y, HasFDerivAt (f v') (fderiv ℝ (f v') y) y := by
      filter_upwards [Ioo_mem_nhds hv0.1 hv0.2] with v' hv'
      exact fun y => hf12.hasFDerivAt v' ⟨hv'.1.le, hv'.2.le⟩ y (mem_univ _)
    have hcont : ContinuousAt (fun p : ℝ × Euc d => fderiv ℝ (f p.1) p.2) (v, X v) := by
      refine hf12.cont_fderiv.continuousAt ?_
      exact prod_mem_nhds (Icc_mem_nhds hv0.1 hv0.2) univ_mem
    have hFt : HasDerivAt (fun v' => f v' (X v)) (-(generatorW C v (f v) (X v))) v :=
      hf.time_deriv (X v) v hv0
    have hch := ad3_chain hFx hcont hFt (hXd v hv)
    have hSv := hS v ⟨hv0.1.le, hv0.2.le⟩ (X v)
    rw [hν, kl_inner_gradient] at hSv
    convert hch using 1
    rw [hSv]; ring
  -- fundamental theorem of calculus
  have hhc : ContinuousOn (fun v => f v (X v)) (Icc r t) := by
    have h1 : ContinuousOn (fun v => (v, X v)) (Icc r t) := continuousOn_id.prodMk hXcI
    exact hf12.cont.comp h1 (fun v hv => ⟨⟨hr.trans hv.1, hv.2⟩, mem_univ _⟩)
  have hSX : ContinuousOn (fun u => S u (X u)) (Icc r t) := by
    have h1 : ContinuousOn (fun v => (v, X v)) (Icc r t) := continuousOn_id.prodMk hXcI
    exact hSc.comp h1 (fun v hv => ⟨⟨hr.trans hv.1, hv.2⟩, mem_univ _⟩)
  have hSI : IntervalIntegrable (fun u => S u (X u)) volume r t :=
    (by rwa [Set.uIcc_of_le hrt] : ContinuousOn (fun u => S u (X u)) (Set.uIcc r t)).intervalIntegrable
  refine ⟨hSI, ?_⟩
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hrt hhc
    (fun v hv => (hh v hv).hasDerivWithinAt) hSI
  have h1 : X r = x := lcFlow_self H hg0 hr x
  rw [hftc, hf.terminal, h1]
  ring

end HRS.MS.AdjDecay
