import HRS.MS.LcEngAux3
import HRS.MS.PoisKolmAux2
import HRS.Appendix.B15DAux3

/-!
# AD-2, part 1: `C^{1,2}` regularity of classical adjoint solutions and the Dynkin form of Ito

Infrastructure for `adjoint_decay` (S4.12), consumed by AD-3 through `ad_verification`
(`AdjVerifAux2`).  Helper lemmas carry the prefix `ad2_`.

* `ad2_isC12On`: a classical adjoint solution (`IsClassicalAdjointW C t φ f`, `0 < t`) is `C^{1,2}` on
  `[0,t] × ℝ^d` in the sense of `IsC12On`, with `derivWithin (f · x) (Icc 0 t) s = -generatorW C s (f s) x`
  (endpoint derivatives from `hasDerivWithinAt_Ici_of_tendsto_deriv`).
* `ad2_isC12On_reparam`: the affine time change `s ↦ f (r + s/a)` of an `IsC12On` function is `IsC12On`
  on `[0, a (t-r)]`, with the chain rule for the time derivative.
* `ad2_dynkin`: Dynkin form of `ito_formula_additive` for a time dependent `f ∈ IsC12On T univ` with bounded
  space gradient along a strong solution of `dY = b(s,Y) ds + dW` (unit noise directions `lcSigma d`): the
  Ito remainder is integrable with mean zero.
* `ad2_sdrift`, `ad2_sdrift_isLipschitz`: the drift `a⁻¹ lcB r (u/a) z` of the engine equation in the time
  scale `s = a (v - r)` of the unit Brownian motion (`a = 2ν`).
* `ad2_strong_eq_flow`: the strong solution `Y` of `dY = a⁻¹ lcB r (s/a, Y) ds + dW'`, `W' = W_{2νr+·} - W_{2νr}`,
  satisfies a.s. `Y_{2ντ} = lcFlow Q c B G r (r+τ) x` for the noise `G = lcNoiseE W (fun _ => ν)` of the
  engine (pathwise uniqueness `lc_flow_unique`; the noise `lcNoise` has variance `2ν v` per coordinate).
-/

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open HRS HRS.Whole HRS.MS.Lc HRS.MS.PoisKolm HRS.MD.EQLawPath

noncomputable section
namespace HRS.MS.AdjVerif

variable {d : ℕ}

theorem ad2_fderiv_eq {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (g : Euc d → F) (x : Euc d) :
    fderiv ℝ g x = continuousMultilinearCurryFin1 ℝ (Euc d) F (iteratedFDeriv ℝ 1 g x) := by
  ext v
  simp [continuousMultilinearCurryFin1_apply]

theorem ad2_fderiv2_eq (g : Euc d → ℝ) (x : Euc d) :
    fderiv ℝ (fderiv ℝ g) x = continuousMultilinearCurryFin1 ℝ (Euc d) (Euc d →L[ℝ] ℝ)
      ((continuousMultilinearCurryRightEquiv' ℝ 1 (Euc d) ℝ) (iteratedFDeriv ℝ (1 + 1) g x)) := by
  have h := iteratedFDeriv_succ_eq_comp_right (𝕜 := ℝ) (f := g) (n := 1) (x := x)
  have h2 : iteratedFDeriv ℝ 1 (fun y => fderiv ℝ g y) x =
      (continuousMultilinearCurryRightEquiv' ℝ 1 (Euc d) ℝ) (iteratedFDeriv ℝ (1 + 1) g x) := by
    rw [h]; simp
  rw [← h2]
  exact ad2_fderiv_eq (fderiv ℝ g) x

theorem ad2_continuousOn_of_subtype {t : ℝ} {β : Type*} [TopologicalSpace β] {F : ℝ → Euc d → β}
    (h : Continuous fun p : Set.Icc (0 : ℝ) t × Euc d => F p.1 p.2) :
    ContinuousOn (fun p : ℝ × Euc d => F p.1 p.2) (Icc 0 t ×ˢ univ) := by
  refine continuousOn_iff_continuous_domRestrict.2 ?_
  refine h.comp (f := fun q : ↥(Icc 0 t ×ˢ (univ : Set (Euc d))) => ((⟨q.1.1, q.2.1⟩ : Set.Icc (0 : ℝ) t), q.1.2)) (Continuous.prodMk ?_ ?_)
  · exact Continuous.subtype_mk (continuous_fst.comp continuous_subtype_val) _
  · exact continuous_snd.comp continuous_subtype_val


theorem ad2_continuousOn_slice {t : ℝ} {β : Type*} [TopologicalSpace β] {F : ℝ → Euc d → β}
    (h : Continuous fun p : Set.Icc (0 : ℝ) t × Euc d => F p.1 p.2) (x : Euc d) :
    ContinuousOn (fun s => F s x) (Icc 0 t) :=
  (ad2_continuousOn_of_subtype h).comp (continuousOn_id.prodMk continuousOn_const)
    (fun _ hr => ⟨hr, mem_univ _⟩)

/-- Time derivative of a classical adjoint solution at every point of `[0,t]`. -/
theorem ad2_hasDerivWithinAt {C : WholeCoeff d} {t : ℝ} (ht : 0 < t) {φ : Euc d → ℝ}
    {f : ℝ → Euc d → ℝ} (hf : IsClassicalAdjointW C t φ f) (x : Euc d) :
    ∀ s ∈ Icc 0 t, HasDerivWithinAt (fun r => f r x) (-(generatorW C s (f s) x)) (Icc 0 t) s := by
  have hc0 : Continuous fun p : Set.Icc (0 : ℝ) t × Euc d => f p.1 p.2 := by
    have h := hf.cont_c2 0 (by norm_num)
    have e : (fun p : Set.Icc (0 : ℝ) t × Euc d => f p.1 p.2) = fun p =>
        continuousMultilinearCurryFin0 ℝ (Euc d) ℝ (iteratedFDeriv ℝ 0 (f p.1) p.2) := by
      funext p; simp [continuousMultilinearCurryFin0_apply]
    rw [e]; exact (continuousMultilinearCurryFin0 ℝ (Euc d) ℝ).continuous.comp h
  have hfx : ContinuousOn (fun r => f r x) (Icc 0 t) := ad2_continuousOn_slice (F := f) hc0 x
  have hGx : ContinuousOn (fun s => generatorW C s (f s) x) (Icc 0 t) :=
    ad2_continuousOn_slice (F := fun s y => generatorW C s (f s) y) hf.cont_time_deriv x
  have hd : ∀ s ∈ Ioo 0 t, HasDerivAt (fun r => f r x) (-(generatorW C s (f s) x)) s :=
    fun s hs => hf.time_deriv x s hs
  have hdiff : DifferentiableOn ℝ (fun r => f r x) (Ioo 0 t) :=
    fun s hs => (hd s hs).differentiableAt.differentiableWithinAt
  have hderiv : ∀ s ∈ Ioo 0 t, deriv (fun r => f r x) s = -(generatorW C s (f s) x) :=
    fun s hs => (hd s hs).deriv
  intro s hs
  rcases hs.1.eq_or_lt with h0 | h0
  · subst h0
    have h1 : HasDerivWithinAt (fun r => f r x) (-(generatorW C 0 (f 0) x)) (Ici 0) 0 := by
      refine hasDerivWithinAt_Ici_of_tendsto_deriv hdiff
        ((hfx 0 ⟨le_rfl, ht.le⟩).mono Ioo_subset_Icc_self) (Ioo_mem_nhdsGT ht) ?_
      have hT : Tendsto (fun s => -(generatorW C s (f s) x)) (𝓝[>] 0)
          (𝓝 (-(generatorW C 0 (f 0) x))) := by
        have := (hGx 0 ⟨le_rfl, ht.le⟩).neg
        refine this.tendsto.mono_left (nhdsWithin_le_iff.2 ?_)
        exact mem_of_superset (Ioo_mem_nhdsGT ht) Ioo_subset_Icc_self
      refine hT.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT ht] with s hs'
      exact (hderiv s hs').symm
    exact h1.mono Icc_subset_Ici_self
  · rcases hs.2.eq_or_lt with h1 | h1
    · subst h1
      have h2 : HasDerivWithinAt (fun r => f r x) (-(generatorW C s (f s) x)) (Iic s) s := by
        refine hasDerivWithinAt_Iic_of_tendsto_deriv hdiff
          ((hfx s ⟨ht.le, le_rfl⟩).mono Ioo_subset_Icc_self) (Ioo_mem_nhdsLT ht) ?_
        have hT : Tendsto (fun s => -(generatorW C s (f s) x)) (𝓝[<] s)
            (𝓝 (-(generatorW C s (f s) x))) := by
          have := (hGx s ⟨ht.le, le_rfl⟩).neg
          refine this.tendsto.mono_left (nhdsWithin_le_iff.2 ?_)
          exact mem_of_superset (Ioo_mem_nhdsLT ht) Ioo_subset_Icc_self
        refine hT.congr' ?_
        filter_upwards [Ioo_mem_nhdsLT ht] with s hs'
        exact (hderiv s hs').symm
      exact h2.mono Icc_subset_Iic_self
    · exact (hd s ⟨h0, h1⟩).hasDerivWithinAt


theorem ad2_derivWithin_eq {C : WholeCoeff d} {t : ℝ} (ht : 0 < t) {φ : Euc d → ℝ}
    {f : ℝ → Euc d → ℝ} (hf : IsClassicalAdjointW C t φ f) (x : Euc d) {s : ℝ} (hs : s ∈ Icc 0 t) :
    derivWithin (fun r => f r x) (Icc 0 t) s = -(generatorW C s (f s) x) :=
  (ad2_hasDerivWithinAt ht hf x s hs).derivWithin (uniqueDiffOn_Icc ht s hs)

/-- A classical adjoint solution is `C^{1,2}` on `[0,t] × ℝ^d` in the sense of `IsC12On`. -/
theorem ad2_isC12On {C : WholeCoeff d} {t : ℝ} (ht : 0 < t) {φ : Euc d → ℝ}
    {f : ℝ → Euc d → ℝ} (hf : IsClassicalAdjointW C t φ f) : IsC12On t Set.univ f := by
  have hc0 : Continuous fun p : Set.Icc (0 : ℝ) t × Euc d => f p.1 p.2 := by
    have h := hf.cont_c2 0 (by norm_num)
    have e : (fun p : Set.Icc (0 : ℝ) t × Euc d => f p.1 p.2) = fun p =>
        continuousMultilinearCurryFin0 ℝ (Euc d) ℝ (iteratedFDeriv ℝ 0 (f p.1) p.2) := by
      funext p; simp [continuousMultilinearCurryFin0_apply]
    rw [e]; exact (continuousMultilinearCurryFin0 ℝ (Euc d) ℝ).continuous.comp h
  have hc1 : Continuous fun p : Set.Icc (0 : ℝ) t × Euc d => fderiv ℝ (f p.1) p.2 := by
    have h := hf.cont_c2 1 (by norm_num)
    have e : (fun p : Set.Icc (0 : ℝ) t × Euc d => fderiv ℝ (f p.1) p.2) = fun p =>
        continuousMultilinearCurryFin1 ℝ (Euc d) ℝ (iteratedFDeriv ℝ 1 (f p.1) p.2) := by
      funext p; exact ad2_fderiv_eq _ _
    rw [e]; exact (continuousMultilinearCurryFin1 ℝ (Euc d) ℝ).continuous.comp h
  have hc2 : Continuous fun p : Set.Icc (0 : ℝ) t × Euc d => fderiv ℝ (fderiv ℝ (f p.1)) p.2 := by
    have h := hf.cont_c2 2 le_rfl
    have e : (fun p : Set.Icc (0 : ℝ) t × Euc d => fderiv ℝ (fderiv ℝ (f p.1)) p.2) = fun p =>
        continuousMultilinearCurryFin1 ℝ (Euc d) (Euc d →L[ℝ] ℝ)
          ((continuousMultilinearCurryRightEquiv' ℝ 1 (Euc d) ℝ)
            (iteratedFDeriv ℝ (1 + 1) (f p.1) p.2)) := by
      funext p; exact ad2_fderiv2_eq _ _
    rw [e]
    exact (continuousMultilinearCurryFin1 ℝ (Euc d) (Euc d →L[ℝ] ℝ)).continuous.comp
      ((continuousMultilinearCurryRightEquiv' ℝ 1 (Euc d) ℝ).continuous.comp h)
  have hG : Continuous fun p : Set.Icc (0 : ℝ) t × Euc d => generatorW C p.1 (f p.1) p.2 :=
    hf.cont_time_deriv
  refine ⟨ad2_continuousOn_of_subtype (F := f) hc0, ?_, ?_,
    ad2_continuousOn_of_subtype (F := fun s y => fderiv ℝ (f s) y) hc1,
    ad2_continuousOn_of_subtype (F := fun s y => fderiv ℝ (fderiv ℝ (f s)) y) hc2, ?_, ?_⟩
  · intro r hr x _
    exact (((hf.c2 r hr).differentiable (by norm_num)) x).hasFDerivAt
  · intro r hr x _
    have : ContDiff ℝ 1 (fderiv ℝ (f r)) := (hf.c2 r hr).fderiv_right (by norm_num)
    exact ((this.differentiable (by norm_num)) x).hasFDerivAt
  · intro x _ s hs
    rw [ad2_derivWithin_eq ht hf x hs]
    exact ad2_hasDerivWithinAt ht hf x s hs
  · have h := ad2_continuousOn_of_subtype (F := fun s y => -(generatorW C s (f s) y)) hG.neg
    refine h.congr ?_
    intro p hp
    exact ad2_derivWithin_eq ht hf p.2 hp.1


theorem ad2_theta_maps {t r a : ℝ} (hr : 0 ≤ r) (ha : 0 < a) :
    MapsTo (fun s : ℝ => r + s / a) (Icc 0 (a * (t - r))) (Icc 0 t) := by
  intro s hs
  refine ⟨by have := div_nonneg hs.1 ha.le; linarith, ?_⟩
  have : s / a ≤ t - r := by
    rw [div_le_iff₀ ha]; nlinarith [hs.2]
  linarith

theorem ad2_reparam_hasDeriv {t r a : ℝ} {f : ℝ → Euc d → ℝ} (hf : IsC12On t Set.univ f)
    (hr : 0 ≤ r) (ha : 0 < a) (y : Euc d) {s : ℝ} (hs : s ∈ Icc 0 (a * (t - r))) :
    HasDerivWithinAt (fun s' => f (r + s' / a) y)
      (a⁻¹ * derivWithin (fun v => f v y) (Icc 0 t) (r + s / a)) (Icc 0 (a * (t - r))) s := by
  have h1 := hf.hasDerivWithinAt y (mem_univ y) (r + s / a) (ad2_theta_maps hr ha hs)
  have h2 : HasDerivWithinAt (fun s' : ℝ => r + s' / a) (1 / a) (Icc 0 (a * (t - r))) s :=
    (((hasDerivAt_id s).div_const a).const_add r).hasDerivWithinAt
  have := h1.scomp s h2 (ad2_theta_maps hr ha)
  have h3 : a⁻¹ * derivWithin (fun v => f v y) (Icc 0 t) (r + s / a) =
      (1 / a) • derivWithin (fun v => f v y) (Icc 0 t) (r + s / a) := by
    simp [one_div]
  rw [h3]
  exact this

theorem ad2_isC12On_reparam {t r a : ℝ} {f : ℝ → Euc d → ℝ} (hf : IsC12On t Set.univ f)
    (hr : 0 ≤ r) (ha : 0 < a) (hrt : r < t) :
    IsC12On (a * (t - r)) Set.univ (fun s y => f (r + s / a) y) ∧
    ∀ y, ∀ s ∈ Icc 0 (a * (t - r)),
      derivWithin (fun s' => f (r + s' / a) y) (Icc 0 (a * (t - r))) s =
        a⁻¹ * derivWithin (fun v => f v y) (Icc 0 t) (r + s / a) := by
  have hT : 0 < a * (t - r) := mul_pos ha (by linarith)
  have hq : Continuous fun p : ℝ × Euc d => (r + p.1 / a, p.2) :=
    (continuous_const.add (continuous_fst.div_const a)).prodMk continuous_snd
  have hmem : MapsTo (fun p : ℝ × Euc d => (r + p.1 / a, p.2)) (Icc 0 (a * (t - r)) ×ˢ univ)
      (Icc 0 t ×ˢ univ) := fun p hp => ⟨ad2_theta_maps hr ha hp.1, mem_univ _⟩
  have hder : ∀ y, ∀ s ∈ Icc 0 (a * (t - r)),
      derivWithin (fun s' => f (r + s' / a) y) (Icc 0 (a * (t - r))) s =
        a⁻¹ * derivWithin (fun v => f v y) (Icc 0 t) (r + s / a) := fun y s hs =>
    (ad2_reparam_hasDeriv hf hr ha y hs).derivWithin (uniqueDiffOn_Icc hT s hs)
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, hder⟩
  · exact hf.cont.comp hq.continuousOn hmem
  · intro s hs x _
    exact hf.hasFDerivAt _ (ad2_theta_maps hr ha hs) x (mem_univ x)
  · intro s hs x _
    exact hf.hasFDerivAt_fderiv _ (ad2_theta_maps hr ha hs) x (mem_univ x)
  · exact hf.cont_fderiv.comp hq.continuousOn hmem
  · exact hf.cont_fderiv₂.comp hq.continuousOn hmem
  · intro x _ s hs
    rw [hder x s hs]
    exact ad2_reparam_hasDeriv hf hr ha x hs
  · have h := (continuousOn_const (c := a⁻¹)).mul (hf.cont_deriv.comp hq.continuousOn hmem)
    refine h.congr ?_
    intro p hp
    exact hder p.2 p.1 hp.1


/-! ### Dynkin form of Itô's formula for a time-dependent `C^{1,2}` function -/

theorem ad2_dynkin {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → Fin d → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {b : ℝ → Euc d → Euc d} (hb : IsLipschitzDrift b) {x : Euc d} {Y : ℝ → Ω → Euc d}
    (hY : IsAdditiveSDESolution P ℱ W' b (lcSigma d) (fun _ => x) (fun _ => ⊤) Y)
    {T : ℝ} (hT : 0 ≤ T) {f : ℝ → Euc d → ℝ} (hf : IsC12On T Set.univ f) {C : ℝ}
    (hC : ∀ s ∈ Set.Icc 0 T, ∀ y, ‖fderiv ℝ (f s) y‖ ≤ C) :
    ∃ M : Ω → ℝ, Integrable M P ∧ ∫ ω, M ω ∂P = 0 ∧
      ∀ᵐ ω ∂P, IntegrableOn (fun s => derivWithin (fun r => f r (Y s ω)) (Set.Icc 0 T) s +
          fderiv ℝ (f s) (Y s ω) (b s (Y s ω)) +
          (1 / 2) * ∑ k, fderiv ℝ (fderiv ℝ (f s)) (Y s ω) (lcSigma d k) (lcSigma d k))
          (Set.Icc 0 T) ∧
        f T (Y T ω) = f 0 x +
        (∫ s in Set.Icc (0 : ℝ) T, (derivWithin (fun r => f r (Y s ω)) (Set.Icc 0 T) s +
          fderiv ℝ (f s) (Y s ω) (b s (Y s ω)) +
          (1 / 2) * ∑ k, fderiv ℝ (fderiv ℝ (f s)) (Y s ω) (lcSigma d k) (lcSigma d k))) + M ω := by
  have hYc : ∀ ω, ∀ u : ℝ, 0 ≤ u → ContinuousOn (fun s => Y s ω) (Set.Icc 0 u) := fun ω u hu =>
    hY.cont ω u hu (WithTop.coe_lt_top _)
  have hYcI : ∀ ω, ContinuousOn (fun s => Y s ω) (Set.Ici 0) := fun ω =>
    b15d2_contOn_Ici (fun u hu => hYc ω u hu)
  have hY0 : Y 0 = fun _ => x := funext hY.init
  have hY0' : ∀ s : ℝ, Measurable[ℱ s] (Y 0) := fun s => by rw [hY0]; exact measurable_const
  have hYad : ∀ u : ℝ, 0 ≤ u → Measurable[ℱ u] (Y u) := fun u _ => hY.adapted u
  have hXprog : IsProgressive ℱ (ofNNRealTime (fun u : ℝ≥0 => Y (u : ℝ))) := by
    have e : ofNNRealTime (fun u : ℝ≥0 => Y (u : ℝ)) = fun s ω => Y (max s 0) ω := by
      funext s ω
      simp [ofNNRealTime, Real.coe_toNNReal']
    rw [e]
    exact b15d2_isProgressive_clampPath hY0' hYad hYcI
  have hbq : Continuous (fun p : ℝ × Euc d => b (max p.1 0) p.2) :=
    hb.cont.comp_continuous ((continuous_fst.max continuous_const).prodMk continuous_snd)
      (fun p => ⟨Set.mem_Ici.2 (le_max_right _ _), Set.mem_univ _⟩)
  have hbprog : IsProgressive ℱ
      (ofNNRealTime (fun (u : ℝ≥0) (ω : Ω) => b (u : ℝ) (Y (u : ℝ) ω))) := by
    have h := isProgressive_comp_measurable' (ofNNRealTime (fun u : ℝ≥0 => Y (u : ℝ))) hXprog
      (fun (s : ℝ) y => b (max s 0) y) hbq.measurable
    have e : ofNNRealTime (fun (u : ℝ≥0) (ω : Ω) => b (u : ℝ) (Y (u : ℝ) ω)) =
        fun s ω => b (max s 0) (ofNNRealTime (fun u : ℝ≥0 => Y (u : ℝ)) s ω) := by
      funext s ω
      simp [ofNNRealTime, Real.coe_toNNReal']
    rw [e]; exact h
  have hclampD : Continuous (fun q : ℝ × Euc d => fderiv ℝ (f (clampTI T q.1)) q.2) := by
    have hq : Continuous (fun q : ℝ × Euc d => (clampTI T q.1, q.2)) :=
      ((continuous_clampTI T).comp continuous_fst).prodMk continuous_snd
    exact ContinuousOn.comp_continuous hf.cont_fderiv hq
      (fun q => ⟨clampTI_mem hT q.1, mem_univ _⟩)
  let g : ℝ → Euc d → Fin d → ℝ := fun s y k =>
    if s ∈ Set.Icc 0 T then fderiv ℝ (f (clampTI T s)) y (lcSigma d k) else 0
  have hΨeq : ∀ s ω k, itoIntegrand T Set.univ f (ofNNRealTime (fun u : ℝ≥0 => Y (u : ℝ)))
      (fun _ _ => lcSigma d) s ω k = g s (ofNNRealTime (fun u : ℝ≥0 => Y (u : ℝ)) s ω) k := by
    intro s ω k
    by_cases hs : s ∈ Set.Icc 0 T
    · simp only [itoIntegrand, g, if_pos hs, Set.indicator_of_mem hs, Set.mem_univ, Set.setOf_true,
        Set.indicator_univ, clampTI_of_mem hs, ofNNRealTime_apply]
    · simp only [itoIntegrand, g, if_neg hs, Set.indicator_of_notMem hs]
  have hΨprog : IsProgressive ℱ (fun s ω k => itoIntegrand T Set.univ f
      (ofNNRealTime (fun u : ℝ≥0 => Y (u : ℝ))) (fun _ _ => lcSigma d) s ω k) := by
    have hk : ∀ k : Fin d, IsProgressive ℱ (fun s ω =>
        itoIntegrand T Set.univ f (ofNNRealTime (fun u : ℝ≥0 => Y (u : ℝ)))
          (fun _ _ => lcSigma d) s ω k) := by
      intro k
      have hc := hclampD.clm_apply (continuous_const (y := lcSigma d k))
      have hm : Measurable (Function.uncurry (fun (s : ℝ) (y : Euc d) =>
          if s ∈ Set.Icc 0 T then fderiv ℝ (f (clampTI T s)) y (lcSigma d k) else 0)) :=
        Measurable.ite (measurableSet_Icc.preimage measurable_fst) hc.measurable measurable_const
      have hg := isProgressive_comp_measurable' (ofNNRealTime (fun u : ℝ≥0 => Y (u : ℝ))) hXprog
        (fun (s : ℝ) (y : Euc d) =>
          if s ∈ Set.Icc 0 T then fderiv ℝ (f (clampTI T s)) y (lcSigma d k) else 0) hm
      have e : (fun s ω => itoIntegrand T Set.univ f (ofNNRealTime (fun u : ℝ≥0 => Y (u : ℝ)))
          (fun _ _ => lcSigma d) s ω k)
          = fun s ω => (fun (s : ℝ) (y : Euc d) =>
            if s ∈ Set.Icc 0 T then fderiv ℝ (f (clampTI T s)) y (lcSigma d k) else 0)
              s (ofNNRealTime (fun u : ℝ≥0 => Y (u : ℝ)) s ω) := by
        funext s ω
        exact hΨeq s ω k
      rw [e]
      exact hg
    exact isProgressive_pi hk
  have hΨbd : ∀ s ω k, |itoIntegrand T Set.univ f (ofNNRealTime (fun u : ℝ≥0 => Y (u : ℝ)))
      (fun _ _ => lcSigma d) s ω k| ≤ max C 0 * ∑ j : Fin d, ‖lcSigma d j‖ := by
    intro s ω k
    rw [hΨeq s ω k]
    simp only [g]
    split_ifs with hs
    · have hb' : ‖fderiv ℝ (f (clampTI T s)) (ofNNRealTime (fun u : ℝ≥0 => Y (u : ℝ)) s ω)‖ ≤
          max C 0 := (hC (clampTI T s) (clampTI_mem hT s) _).trans (le_max_left _ _)
      calc |fderiv ℝ (f (clampTI T s)) (ofNNRealTime (fun u : ℝ≥0 => Y (u : ℝ)) s ω) (lcSigma d k)|
          ≤ ‖fderiv ℝ (f (clampTI T s)) (ofNNRealTime (fun u : ℝ≥0 => Y (u : ℝ)) s ω)‖
              * ‖lcSigma d k‖ := by
            rw [← Real.norm_eq_abs]
            exact ContinuousLinearMap.le_opNorm _ _
        _ ≤ max C 0 * ‖lcSigma d k‖ :=
            mul_le_mul hb' le_rfl (norm_nonneg _) ((norm_nonneg _).trans hb')
        _ ≤ max C 0 * ∑ j : Fin d, ‖lcSigma d j‖ :=
            mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun j _ => norm_nonneg _)
              (Finset.mem_univ k)) (le_max_right _ _)
    · simp only [abs_zero]
      exact mul_nonneg (le_max_right _ _) (Finset.sum_nonneg fun j _ => norm_nonneg _)
  have hΨL2 : IsProgressiveL2 P ℱ (fun s ω k => itoIntegrand T Set.univ f
      (ofNNRealTime (fun u : ℝ≥0 => Y (u : ℝ))) (fun _ _ => lcSigma d) s ω k) :=
    IsProgressiveL2.of_bounded P hΨprog _ hΨbd
  have hXmeas : ∀ u : ℝ≥0, Measurable (fun ω => Y (u : ℝ) ω) := fun u =>
    (hY.adapted (u : ℝ)).mono (ℱ.le _) le_rfl
  have hX₀ : ∀ s : ℝ, Measurable[ℱ s] (fun ω => Y ((0 : ℝ≥0) : ℝ) ω) := fun s => by
    have e : (fun ω => Y ((0 : ℝ≥0) : ℝ) ω) = fun _ => x := by
      rw [NNReal.coe_zero]; exact hY0
    rw [e]
    exact measurable_const
  have hbint : ∀ᵐ ω ∂P, IntegrableOn
      (fun s : ℝ => b (Real.toNNReal s : ℝ) (Y (Real.toNNReal s : ℝ) ω)) (Set.Icc 0 T) := by
    filter_upwards [hY.eq] with ω hω
    have h := (hω T hT (WithTop.coe_lt_top _)).1
    refine h.congr_fun (fun s hs => ?_) measurableSet_Icc
    rw [Real.coe_toNNReal _ hs.1]
  have hX : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, (u : ℝ) ≤ T →
      Y (u : ℝ) ω = Y ((0 : ℝ≥0) : ℝ) ω
        + (∫ s in Set.Icc (0 : ℝ) (u : ℝ), b (Real.toNNReal s : ℝ) (Y (Real.toNNReal s : ℝ) ω))
        + ∑ k, (W' u ω k - W' 0 ω k) • lcSigma d k := by
    filter_upwards [hY.eq] with ω hω u hu
    have h := hω (u : ℝ) u.2 (WithTop.coe_lt_top _)
    have hint : ∫ s in Set.Icc (0 : ℝ) (u : ℝ), b s (Y s ω)
        = ∫ s in Set.Icc (0 : ℝ) (u : ℝ), b (Real.toNNReal s : ℝ) (Y (Real.toNNReal s : ℝ) ω) :=
      setIntegral_congr_fun measurableSet_Icc (fun s hs => by
        rw [Real.coe_toNNReal _ hs.1])
    have h2 : Y (u : ℝ) ω = x + (∫ s in Set.Icc (0 : ℝ) (u : ℝ), b s (Y s ω))
        + ∑ k, ofNNRealTime W' (u : ℝ) ω k • lcSigma d k := h.2
    have h0 : Y ((0 : ℝ≥0) : ℝ) ω = x := by
      rw [NNReal.coe_zero]; exact congrFun hY0 ω
    rw [h2, h0, hint]
    simp [ofNNRealTime, hW'.zero]
  have hito := ito_formula_additive (P := P) (ℱ := ℱ) hW' (T := T) hT f hf (lcSigma d)
    (fun (u : ℝ≥0) (ω : Ω) => Y (u : ℝ) ω) hXmeas hX₀
    (fun (u : ℝ≥0) (ω : Ω) => b (u : ℝ) (Y (u : ℝ) ω)) hbprog hbint hX
  have hloc := localItoIntegral_eq_itoIntegral hW' hΨL2
  refine ⟨fun ω => localItoIntegral P ℱ W' (itoIntegrand T Set.univ f
      (ofNNRealTime (fun u : ℝ≥0 => Y (u : ℝ))) (fun _ _ => lcSigma d)) T ω, ?_, ?_, ?_⟩
  · refine (memLp_two_itoIntegral hW' hΨL2 T).integrable one_le_two |>.congr ?_
    filter_upwards [hloc] with ω hω
    exact (hω T).symm
  · rw [integral_congr_ae (by filter_upwards [hloc] with ω hω using hω T)]
    exact integral_itoIntegral hW' hΨL2 T
  · filter_upwards [hito] with ω hω
    have h := hω.2 (Real.toNNReal T) (by rw [Real.coe_toNNReal _ hT])
    have h0 : Y ((0 : ℝ≥0) : ℝ) ω = x := by
      rw [NNReal.coe_zero]; exact congrFun hY0 ω
    simp only [Real.coe_toNNReal _ hT, h0] at h
    have hD : ∫ s in Set.Icc (0 : ℝ) T, itoDrift T f
        (ofNNRealTime (fun u : ℝ≥0 => Y (u : ℝ))) (ofNNRealTime (fun (u : ℝ≥0) (ω : Ω) =>
          b (u : ℝ) (Y (u : ℝ) ω))) (fun _ _ => lcSigma d) s ω
        = ∫ s in Set.Icc (0 : ℝ) T, (derivWithin (fun r => f r (Y s ω)) (Set.Icc 0 T) s +
          fderiv ℝ (f s) (Y s ω) (b s (Y s ω)) +
          (1 / 2) * ∑ k, fderiv ℝ (fderiv ℝ (f s)) (Y s ω) (lcSigma d k) (lcSigma d k)) :=
      setIntegral_congr_fun measurableSet_Icc (fun s hs => by
        simp only [itoDrift, ofNNRealTime_apply, Real.coe_toNNReal _ hs.1])
    rw [hD] at h
    refine ⟨?_, h⟩
    refine hω.1.congr_fun (fun s hs => ?_) measurableSet_Icc
    simp only [itoDrift, ofNNRealTime_apply, Real.coe_toNNReal _ hs.1]

/-! ### The drift in the time scale of the unit Brownian motion -/

/-- The drift `u, z ↦ a⁻¹ lcB r (u/a) z` of the time-scaled equation `s = a (v - r)`. -/
def ad2_sdrift (Q : Matrix (Fin d) (Fin d) ℝ) (c : ℝ → Euc d) (B : ℝ → Euc d → Euc d) (r a : ℝ)
    (u : ℝ) (z : Euc d) : Euc d :=
  a⁻¹ • lcB Q c B r (u / a) z

theorem ad2_sdrift_isLipschitz {Q : Matrix (Fin d) (Fin d) ℝ} {k : ℕ} {Λc ΛB : ℝ} {c : ℝ → Euc d}
    {B : ℝ → Euc d → Euc d} (H : LcHyp Q k Λc ΛB c B) {r a : ℝ} (hr : 0 ≤ r) (ha : 0 < a) :
    IsLipschitzDrift (ad2_sdrift Q c B r a) where
  cont := by
    have hq : Continuous fun p : ℝ × Euc d => (p.1 / a, p.2) :=
      (continuous_fst.div_const a).prodMk continuous_snd
    have hm : MapsTo (fun p : ℝ × Euc d => (p.1 / a, p.2)) (Ici 0 ×ˢ univ) (Ici 0 ×ˢ univ) :=
      fun p hp => ⟨div_nonneg hp.1 ha.le, mem_univ _⟩
    show ContinuousOn (fun p : ℝ × Euc d => a⁻¹ • lcB Q c B r (p.1 / a) p.2) _
    exact (continuousOn_const (c := a⁻¹)).smul ((lcB_continuousOn_prod H hr).comp hq.continuousOn hm)
  lip T := by
    obtain ⟨L, hL⟩ := (lcB_isLipschitz H hr).lip (T / a)
    refine ⟨(a⁻¹).toNNReal * L, fun t ht => LipschitzWith.of_dist_le_mul fun z z' => ?_⟩
    have h1 := (hL (t / a) ⟨div_nonneg ht.1 ha.le, div_le_div_of_nonneg_right ht.2 ha.le⟩).dist_le_mul z z'
    unfold ad2_sdrift
    rw [dist_smul₀, Real.norm_of_nonneg (inv_nonneg.2 ha.le)]
    push_cast
    rw [Real.coe_toNNReal _ (inv_nonneg.2 ha.le), mul_assoc]
    exact mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 ha.le)


theorem ad2_lcTau_const (ν v : ℝ) : lcTau (fun _ => ν) v = 2 * ν * v := by
  simp [lcTau]; ring

/-- The restarted noise at the real time `v = r + τ`, coordinatewise, in terms of the shifted Brownian
motion `W_{a₀ + s} - W_{a₀}` at time `s = 2 ν τ`. -/
theorem ad2_noise_coord {Ω : Type*} {W : ℝ≥0 → Ω → Fin d → ℝ} {ν r : ℝ} (hν : 0 < ν) (hr : 0 ≤ r)
    {τ : ℝ} (hτ : 0 ≤ τ) (ω : Ω) (k : Fin d) :
    lcNoiseE W (fun _ => ν) (r + τ) ω k - lcNoiseE W (fun _ => ν) r ω k =
      shiftProc W (2 * ν * r).toNNReal (2 * ν * τ).toNNReal ω k := by
  have h1 : 0 ≤ 2 * ν * r := by positivity
  have h2 : 0 ≤ 2 * ν * τ := by positivity
  simp only [lcNoiseE, lcNoise, shiftProc, PiLp.toLp_apply, ad2_lcTau_const, Pi.sub_apply]
  rw [← Real.toNNReal_add h1 h2]
  congr 3
  ring

theorem ad2_strong_eq_flow {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → Fin d → ℝ}
    (hW : IsBrownianFiltration P ℱ W) {Q : Matrix (Fin d) (Fin d) ℝ} {k : ℕ} {Λc ΛB : ℝ}
    {c : ℝ → Euc d} {B : ℝ → Euc d → Euc d} (H : LcHyp Q k Λc ΛB c B) {ν : ℝ} (hν : 0 < ν)
    {r : ℝ} (hr : 0 ≤ r) (x : Euc d) {Y : ℝ → Ω → Euc d}
    (hY : IsAdditiveSDESolution P (shiftFil ℱ (2 * ν * r).toNNReal)
      (shiftProc W (2 * ν * r).toNNReal) (ad2_sdrift Q c B r (2 * ν)) (lcSigma d)
      (fun _ => x) (fun _ => ⊤) Y) :
    ∀ᵐ ω ∂P, ∀ τ : ℝ, 0 ≤ τ →
      Y (2 * ν * τ) ω = lcFlow Q c B (fun v => lcNoiseE W (fun _ => ν) v ω) r (r + τ) x := by
  have ha : 0 < 2 * ν := by positivity
  filter_upwards [hY.isPathSolution] with ω hω
  set g : ℝ → Euc d := fun v => lcNoiseE W (fun _ => ν) v ω with hgdef
  have hg : Continuous g := lc_noiseE_cont hW continuous_const ω
  set y : ℝ → Euc d := fun τ => Y (2 * ν * τ) ω with hydef
  have hmaps : ∀ t : ℝ, 0 ≤ t → MapsTo (fun τ : ℝ => 2 * ν * τ) (Icc 0 t) (Icc 0 (2 * ν * t)) :=
    fun t ht τ hτ => ⟨by have := hτ.1; positivity, mul_le_mul_of_nonneg_left hτ.2 ha.le⟩
  have hcont : ∀ t : ℝ, 0 ≤ t → ContinuousOn y (Icc 0 t) := fun t ht =>
    (hω.2 (2 * ν * t) (by positivity) (WithTop.coe_lt_top _)).1.comp
      (continuous_const.mul continuous_id).continuousOn (hmaps t ht)
  have hsol : IsPathSolution (lcB Q c B r) (lcSigma d) (lcW g r) x ⊤ y := by
    refine ⟨by simpa [hydef] using hω.1, fun t ht _ => ?_⟩
    have hc := hcont t ht
    have hint : ContinuousOn (fun τ => lcB Q c B r τ (y τ)) (Icc 0 t) :=
      lcB_continuous H hr (fun τ hτ => hτ.1) hc
    refine ⟨hc, hint.integrableOn_Icc, ?_⟩
    obtain ⟨_, _, heq⟩ := hω.2 (2 * ν * t) (by positivity) (WithTop.coe_lt_top _)
    -- change of variables
    have hcv : ∫ s in Icc (0 : ℝ) (2 * ν * t), ad2_sdrift Q c B r (2 * ν) s (Y s ω) =
        ∫ τ in Icc (0 : ℝ) t, lcB Q c B r τ (y τ) := by
      rw [setIntegral_Icc_eq_interval (by positivity), setIntegral_Icc_eq_interval ht]
      have := intervalIntegral.integral_comp_mul_left
        (fun s : ℝ => ad2_sdrift Q c B r (2 * ν) s (Y s ω)) (a := 0) (b := t) ha.ne'
      have e : ∀ τ : ℝ, ad2_sdrift Q c B r (2 * ν) (2 * ν * τ) (Y (2 * ν * τ) ω) =
          (2 * ν)⁻¹ • lcB Q c B r τ (y τ) := by
        intro τ
        simp only [ad2_sdrift, hydef]
        rw [mul_div_cancel_left₀ _ ha.ne']
      simp only [e, intervalIntegral.integral_smul, mul_zero] at this
      exact ((smul_right_inj (inv_ne_zero ha.ne')).1 this).symm
    have hnoise : ∀ i : Fin d, lcW g r (Real.toNNReal t) i =
        shiftProc W (2 * ν * r).toNNReal (2 * ν * t).toNNReal ω i := by
      intro i
      simp only [lcW, Real.coe_toNNReal _ ht, hgdef]
      exact ad2_noise_coord hν hr ht ω i
    have heq' : Y (2 * ν * t) ω = x + (∫ s in Icc (0 : ℝ) (2 * ν * t),
        ad2_sdrift Q c B r (2 * ν) s (Y s ω)) +
        ∑ i, shiftProc W (2 * ν * r).toNNReal (2 * ν * t).toNNReal ω i • lcSigma d i := heq
    show Y (2 * ν * t) ω = x + _ + _
    rw [heq', hcv]
    simp only [hnoise]
  intro τ hτ
  exact lc_flow_unique H hg hr hsol τ hτ

end HRS.MS.AdjVerif
