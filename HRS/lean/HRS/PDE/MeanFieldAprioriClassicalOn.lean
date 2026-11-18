import HRS.PDE.MeanFieldAprioriClassical

/-!
# A priori bounds for the finite-regularity mean-field equation, packet AP1aOn
(time-local port of the path lemmas of `MeanFieldAprioriClassical.lean`; package MF-01,
`MeanFieldAprioriAmendment.md` §2.1).

`MFSolOn` / `MFSolRealOn` are solutions on `[0,T]`; the lemmas are the AP1a path lemmas with the
time set `Set.Ici 0` replaced by `Set.Icc 0 T` (or by an arbitrary time set `S`).
Imports only `MeanFieldAprioriClassical`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ComplexConjugate

namespace HRS.PDE.MFApriori

variable {d : ℕ}
open Aux

/-- A solution of the integrated mean-field equation on `[0,T]` with initial density `ρ⁰`
(the four fields of `MFLocal.IsMFSolutionHKOn d s V ν K (coeffOf ρ₀) ρc T`, verbatim, so that
the two are interconvertible by `⟨h.init, h.cont, h.integrable, h.eq⟩` in a file importing both). -/
structure MFSolOn (d : ℕ) (s : ℝ) (V : Torus d → ℝ) (ν K : ℝ) (ρ₀ : Torus d → ℝ)
    (ρc : ℝ → Coeff d) (T : ℝ) : Prop where
  init : ρc 0 = coeffOf ρ₀
  cont : ContinuousInHsOn K ρc (Set.Icc 0 T)
  integrable : ∀ k, ∀ t ∈ Set.Icc 0 T,
    IntegrableOn (fun σ => mfRhsCoeff d s V ν (ρc σ) k) (Set.Icc 0 t)
  eq : ∀ k, ∀ t ∈ Set.Icc 0 T,
    ρc t k = coeffOf ρ₀ k + ∫ σ in (0 : ℝ)..t, mfRhsCoeff d s V ν (ρc σ) k

/-- A real solution on `[0,T]`. -/
structure MFSolRealOn (d : ℕ) (s : ℝ) (V : Torus d → ℝ) (ν K : ℝ) (ρ₀ : Torus d → ℝ)
    (ρc : ℝ → Coeff d) (T : ℝ) : Prop where
  sol : MFSolOn d s V ν K ρ₀ ρc T
  real : ∀ t ∈ Set.Icc 0 T, IsRealCoeff (ρc t)

theorem continuousInHsOn_mono_set {m : ℝ} {F : ℝ → Coeff d} {S S' : Set ℝ}
    (h : ContinuousInHsOn m F S) (hS : S' ⊆ S) : ContinuousInHsOn m F S' :=
  ⟨fun τ hτ => h.1 τ (hS hτ), fun τ0 hτ0 => (h.2 τ0 (hS hτ0)).mono_left (nhdsWithin_mono _ hS)⟩

theorem IsMFSolutionHK.toSolOn {s : ℝ} {V : Torus d → ℝ} {ν K : ℝ} {ρ₀ : Torus d → ℝ}
    {ρc : ℝ → Coeff d} (H : IsMFSolutionHK d s V ν K ρ₀ ρc) (T : ℝ) :
    MFSolOn d s V ν K ρ₀ ρc T where
  init := H.init
  cont := continuousInHsOn_mono_set H.cont (fun _ hτ => hτ.1)
  integrable := fun k t ht => H.integrable k t ht.1
  eq := fun k t ht => H.eq k t ht.1

theorem MFSolReal.toOn {s : ℝ} {V : Torus d → ℝ} {ν K : ℝ} {ρ₀ : Torus d → ℝ}
    {ρc : ℝ → Coeff d} (H : MFSolReal d s V ν K ρ₀ ρc) (T : ℝ) :
    MFSolRealOn d s V ν K ρ₀ ρc T where
  sol := IsMFSolutionHK.toSolOn H.sol T
  real := fun t ht => H.real t ht.1

theorem MFSolOn.mono {s : ℝ} {V : Torus d → ℝ} {ν K : ℝ} {ρ₀ : Torus d → ℝ} {ρc : ℝ → Coeff d}
    {T : ℝ} (H : MFSolOn d s V ν K ρ₀ ρc T) {T' : ℝ} (h : T' ≤ T) :
    MFSolOn d s V ν K ρ₀ ρc T' where
  init := H.init
  cont := continuousInHsOn_mono_set H.cont (Set.Icc_subset_Icc le_rfl h)
  integrable := fun k t ht => H.integrable k t ⟨ht.1, ht.2.trans h⟩
  eq := fun k t ht => H.eq k t ⟨ht.1, ht.2.trans h⟩

theorem MFSolRealOn.mono {s : ℝ} {V : Torus d → ℝ} {ν K : ℝ} {ρ₀ : Torus d → ℝ}
    {ρc : ℝ → Coeff d} {T : ℝ} (H : MFSolRealOn d s V ν K ρ₀ ρc T) {T' : ℝ} (h : T' ≤ T) :
    MFSolRealOn d s V ν K ρ₀ ρc T' where
  sol := H.sol.mono h
  real := fun t ht => H.real t ⟨ht.1, ht.2.trans h⟩

/-- A path which is a solution on every `[0,T]` is a global solution (same proof as
`MFLocal.isMFSolutionHK_of_forall_on`). -/
theorem isMFSolutionHK_of_forall_solOn {s : ℝ} {V : Torus d → ℝ} {ν K : ℝ}
    {ρ₀ : Torus d → ℝ} {ρc : ℝ → Coeff d} (h : ∀ T, 0 ≤ T → MFSolOn d s V ν K ρ₀ ρc T) :
    IsMFSolutionHK d s V ν K ρ₀ ρc where
  init := (h 0 le_rfl).init
  cont := by
    refine ⟨fun τ hτ => (h τ hτ).cont.1 τ ⟨hτ, le_rfl⟩, fun τ0 hτ0 => ?_⟩
    have hτ0' : (0 : ℝ) ≤ τ0 := hτ0
    have hc := (h (τ0 + 1) (by linarith)).cont.2 τ0 ⟨hτ0', by linarith⟩
    refine hc.mono_left ?_
    rw [nhdsWithin_le_iff]
    exact mem_nhdsWithin.2 ⟨Set.Iio (τ0 + 1), isOpen_Iio, by simp, fun x hx => ⟨hx.2, hx.1.le⟩⟩
  integrable := fun k t ht => (h t ht).integrable k t ⟨ht, le_rfl⟩
  eq := fun k t ht => (h t ht).eq k t ⟨ht, le_rfl⟩

/-- `rhs_continuousInHsOn` for an arbitrary time set (the AP1a proof uses only `H.cont`). -/
theorem rhs_continuousInHsOn' (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℕ)
    (hK : (d : ℝ) / 2 + 1 < K) (V : Torus d → ℝ) (hV : Torus.IsCk (K + 2) V) (ν : ℝ)
    (ρc : ℝ → Coeff d) (S : Set ℝ) (hcont : ContinuousInHsOn K ρc S) :
    ContinuousInHsOn ((K : ℝ) - 2) (fun σ => mfRhsCoeff d s V ν (ρc σ)) S := by
  have hVK := memHs_of_isCk_nat K V hV
  obtain ⟨Cb, hCb0, hCb⟩ := exists_rhs_bound hd s hs0 hsd K hK V hVK ν
  refine ⟨fun τ hτ => (hCb _ (hcont.1 τ hτ)).1, fun τ0 hτ0 => ?_⟩
  set R : ℝ := hsNorm K (ρc τ0) + 1 with hR
  obtain ⟨C, hC0, hC⟩ := exists_rhs_lipschitz hd s hs0 hsd K hK V hVK ν R
  have hT := hcont.2 τ0 hτ0
  have hev : ∀ᶠ τ in 𝓝[S] τ0, hsNorm K (ρc τ - ρc τ0) < 1 :=
    hT.eventually (gt_mem_nhds one_pos)
  have hmem : ∀ᶠ τ in 𝓝[S] τ0, τ ∈ S := self_mem_nhdsWithin
  have hbound : ∀ᶠ τ in 𝓝[S] τ0, hsNorm (K - 2 : ℝ) (mfRhsCoeff d s V ν (ρc τ) -
      mfRhsCoeff d s V ν (ρc τ0)) ≤ C * hsNorm K (ρc τ - ρc τ0) := by
    filter_upwards [hev, hmem] with τ hτ hτm
    have h1 := hsNorm_le_add_sub K (hcont.1 τ hτm) (hcont.1 τ0 hτ0)
    exact (hC _ _ (hcont.1 τ hτm) (hcont.1 τ0 hτ0) (by rw [hR]; linarith) (by rw [hR]; linarith)).2
  have hlim : Tendsto (fun τ => C * hsNorm K (ρc τ - ρc τ0)) (𝓝[S] τ0) (𝓝 0) := by
    simpa using hT.const_mul C
  exact squeeze_zero' (Eventually.of_forall fun τ => hsNorm_nonneg _ _) hbound hlim

theorem exists_bound_of_continuousInHsOn_Icc (m : ℝ) (F : ℝ → Coeff d) (T : ℝ)
    (h : ContinuousInHsOn m F (Set.Icc 0 T)) :
    ∃ B : ℝ, ∀ t ∈ Set.Icc 0 T, hsNorm m (F t) ≤ B := by
  have hc : ContinuousOn (fun τ => hsNorm m (F τ)) (Set.Icc 0 T) := fun τ hτ =>
    continuousWithinAt_hsNorm h hτ
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  exact ⟨B, fun t ht => (le_abs_self _).trans (by simpa using hB t ht)⟩

theorem rhs_mode_continuousOn_on (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℕ)
    (hK : (d : ℝ) / 2 + 1 < K) (V ρ₀ : Torus d → ℝ) (hV : Torus.IsCk (K + 2) V) (ν : ℝ)
    (ρc : ℝ → Coeff d) {T : ℝ} (H : MFSolOn d s V ν K ρ₀ ρc T) (k : Lattice d) :
    ContinuousOn (fun σ => mfRhsCoeff d s V ν (ρc σ) k) (Set.Icc 0 T) :=
  Aux.continuousOn_mode (rhs_continuousInHsOn' hd s hs0 hsd K hK V hV ν ρc _ H.cont) k

theorem coeff_sub_eq_integral_on (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℕ)
    (hK : (d : ℝ) / 2 + 1 < K) (V ρ₀ : Torus d → ℝ) (hV : Torus.IsCk (K + 2) V) (ν : ℝ)
    (ρc : ℝ → Coeff d) {T : ℝ} (H : MFSolOn d s V ν K ρ₀ ρc T) (k : Lattice d) {t y : ℝ}
    (ht : t ∈ Set.Icc 0 T) (hy : y ∈ Set.Icc 0 T) :
    ρc y k - ρc t k = ∫ σ in t..y, mfRhsCoeff d s V ν (ρc σ) k := by
  have hc := rhs_mode_continuousOn_on hd s hs0 hsd K hK V ρ₀ hV ν ρc H k
  have h0 : (0 : ℝ) ∈ Set.Icc 0 T := ⟨le_rfl, ht.1.trans ht.2⟩
  have hi : ∀ a b : ℝ, a ∈ Set.Icc 0 T → b ∈ Set.Icc 0 T →
      IntervalIntegrable (fun σ => mfRhsCoeff d s V ν (ρc σ) k) volume a b := fun a b ha hb =>
    (hc.mono (Set.uIcc_subset_Icc ha hb)).intervalIntegrable
  rw [H.eq k y hy, H.eq k t ht, add_sub_add_left_eq_sub,
    intervalIntegral.integral_interval_sub_left (hi 0 y h0 hy) (hi 0 t h0 ht)]

theorem hasDerivAt_coeff_on (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℕ)
    (hK : (d : ℝ) / 2 + 1 < K) (V ρ₀ : Torus d → ℝ) (hV : Torus.IsCk (K + 2) V) (ν : ℝ)
    (ρc : ℝ → Coeff d) {T : ℝ} (H : MFSolOn d s V ν K ρ₀ ρc T) (k : Lattice d) {t : ℝ}
    (ht : t ∈ Set.Ioo 0 T) :
    HasDerivAt (fun τ => ρc τ k) (mfRhsCoeff d s V ν (ρc t) k) t := by
  have hc := rhs_mode_continuousOn_on hd s hs0 hsd K hK V ρ₀ hV ν ρc H k
  have hco : ContinuousOn (fun σ => mfRhsCoeff d s V ν (ρc σ) k) (Set.Ioo 0 T) :=
    hc.mono Set.Ioo_subset_Icc_self
  have hat : Set.Ioo (0 : ℝ) T ∈ 𝓝 t := Ioo_mem_nhds ht.1 ht.2
  have hint : IntervalIntegrable (fun σ => mfRhsCoeff d s V ν (ρc σ) k) volume 0 t :=
    (hc.mono (Set.uIcc_subset_Icc ⟨le_rfl, ht.1.le.trans ht.2.le⟩
      (Set.Ioo_subset_Icc_self ht))).intervalIntegrable
  have h1 := intervalIntegral.integral_hasDerivAt_right hint
    (hco.stronglyMeasurableAtFilter isOpen_Ioo t ht) (hco.continuousAt hat)
  have h2 := h1.const_add (coeffOf ρ₀ k)
  refine h2.congr_of_eventuallyEq ?_
  filter_upwards [hat] with τ hτ
  exact H.eq k τ (Set.Ioo_subset_Icc_self hτ)

theorem coeff_zero_eq_on (hd : 1 ≤ d) (s : ℝ) (V ρ₀ : Torus d → ℝ) (ν K : ℝ)
    (ρc : ℝ → Coeff d) {T : ℝ} (H : MFSolOn d s V ν K ρ₀ ρc T) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    ρc t 0 = coeffOf ρ₀ 0 := by
  have h0 : ∀ σ, mfRhsCoeff d s V ν (ρc σ) 0 = 0 := by
    intro σ
    have hn : Lattice.enorm (0 : Lattice d) = 0 := by
      simp [Lattice.enorm, Lattice.toEuc]; rfl
    simp [mfRhsCoeff, laplaceCoeff, derivCoeff, hn]
  rw [H.eq 0 t ht]
  simp only [h0]
  simp

/-- `continuousOn_toFun_prod` for an arbitrary time set. -/
theorem continuousOn_toFun_prod' (m : ℝ) (hm : (d : ℝ) / 2 < m) (F : ℝ → Coeff d) (S : Set ℝ)
    (h : ContinuousInHsOn m F S) :
    ContinuousOn (fun p : ℝ × Torus d => toFun (F p.1) p.2) (S ×ˢ Set.univ) := by
  obtain ⟨Cℓ, hCℓ0, hCℓ⟩ := exists_l1_le m hm
  rintro ⟨t0, x0⟩ ⟨ht0, -⟩
  have ht0' : t0 ∈ S := ht0
  have hsum : ∀ τ ∈ S, Summable fun k => ‖F τ k‖ := fun τ hτ => (hCℓ _ (h.1 τ hτ)).1
  rw [ContinuousWithinAt, nhdsWithin_prod_eq, nhdsWithin_univ, tendsto_iff_dist_tendsto_zero]
  have hA : Tendsto (fun p : ℝ × Torus d => Cℓ * hsNorm m (F p.1 - F t0))
      (𝓝[S] t0 ×ˢ 𝓝 x0) (𝓝 0) := by
    have := (h.2 t0 ht0').const_mul Cℓ
    rw [mul_zero] at this
    exact this.comp (tendsto_fst : Tendsto (fun p : ℝ × Torus d => p.1)
      (𝓝[S] t0 ×ˢ 𝓝 x0) (𝓝[S] t0))
  have hcont := continuous_toFun (F t0) (hsum t0 ht0')
  have hB : Tendsto (fun p : ℝ × Torus d => dist (toFun (F t0) p.2) (toFun (F t0) x0))
      (𝓝[S] t0 ×ˢ 𝓝 x0) (𝓝 0) := by
    have h1 : Tendsto (fun x : Torus d => dist (toFun (F t0) x) (toFun (F t0) x0)) (𝓝 x0) (𝓝 0) := by
      have := (hcont.tendsto x0).dist tendsto_const_nhds (b := toFun (F t0) x0)
      simpa using this
    exact h1.comp (tendsto_snd : Tendsto (fun p : ℝ × Torus d => p.2)
      (𝓝[S] t0 ×ˢ 𝓝 x0) (𝓝 x0))
  have hev : ∀ᶠ p in (𝓝[S] t0 ×ˢ 𝓝 x0 : Filter (ℝ × Torus d)), p.1 ∈ S :=
    (tendsto_fst (f := (𝓝[S] t0 : Filter ℝ)) (g := (𝓝 x0 : Filter (Torus d)))).eventually
      self_mem_nhdsWithin
  refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ (hA.add hB |>.trans_eq (by simp))
  filter_upwards [hev] with p hp
  refine (dist_triangle _ (toFun (F t0) p.2) _).trans (add_le_add ?_ le_rfl)
  rw [Real.dist_eq, ← toFun_sub _ _ (hsum _ hp) (hsum t0 ht0')]
  refine (HRS.PDE.MFProduct.abs_toFun_le _ (hCℓ _ (memHs_sub (h.1 _ hp) (h.1 t0 ht0'))).1 _).trans ?_
  exact (hCℓ _ (memHs_sub (h.1 _ hp) (h.1 t0 ht0'))).2

theorem hasDerivAt_mfPath_on (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℕ)
    (hK : (d : ℝ) / 2 + 2 < K) (V ρ₀ : Torus d → ℝ) (hV : Torus.IsCk (K + 2) V) (ν : ℝ)
    (ρc : ℝ → Coeff d) {T : ℝ} (H : MFSolRealOn d s V ν K ρ₀ ρc T) (x : Torus d) {t : ℝ}
    (ht : t ∈ Set.Ioo 0 T) :
    HasDerivAt (fun τ => mfPath ρc τ x) (toFun (mfRhsCoeff d s V ν (ρc t)) x) t := by
  have hK1 : (d : ℝ) / 2 + 1 < K := by linarith
  have htI : t ∈ Set.Icc 0 T := Set.Ioo_subset_Icc_self ht
  have hr := rhs_continuousInHsOn' hd s hs0 hsd K hK1 V hV ν ρc _ H.sol.cont
  set m : ℝ := (K : ℝ) - 2 with hm
  have hmd : (d : ℝ) / 2 < m := by rw [hm]; linarith
  have hKd : (d : ℝ) / 2 < K := by linarith
  obtain ⟨Cℓ, hCℓ0, hCℓ⟩ := exists_l1_le m hmd
  have hsumK : ∀ τ ∈ Set.Icc 0 T, Summable fun k => ‖ρc τ k‖ := fun τ hτ =>
    summable_norm_of_memHs K hKd _ (H.sol.cont.1 τ hτ)
  have hsumr : ∀ τ ∈ Set.Icc 0 T, Summable fun k => ‖mfRhsCoeff d s V ν (ρc τ) k‖ := fun τ hτ =>
    (hCℓ _ (hr.1 τ hτ)).1
  rw [hasDerivAt_iff_tendsto_slope, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  set η : ℝ := ε / (Cℓ + 1) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨δ0, hδ0, hδ0'⟩ := Metric.tendsto_nhdsWithin_nhds.mp (hr.2 t htI) η hη0
  refine ⟨min δ0 (min t (T - t)), lt_min hδ0 (lt_min ht.1 (sub_pos.mpr ht.2)), fun y hyt hyd => ?_⟩
  have hyt' : y ≠ t := hyt
  have hy1 : |y - t| < δ0 := by
    have := lt_of_lt_of_le hyd (min_le_left _ _); rwa [Real.dist_eq] at this
  have hy2 : |y - t| < min t (T - t) := by
    have := lt_of_lt_of_le hyd (min_le_right _ _); rwa [Real.dist_eq] at this
  have hy2a : |y - t| < t := hy2.trans_le (min_le_left _ _)
  have hy2b : |y - t| < T - t := hy2.trans_le (min_le_right _ _)
  have hy0 : 0 < y := by
    have := (abs_lt.mp hy2a).1; linarith
  have hyT : y < T := by
    have := (abs_lt.mp hy2b).2; linarith
  have hyI : y ∈ Set.Icc 0 T := ⟨hy0.le, hyT.le⟩
  have hsub : y - t ≠ 0 := sub_ne_zero.mpr hyt'
  set G : ℝ → Coeff d := fun σ => mfRhsCoeff d s V ν (ρc σ) - mfRhsCoeff d s V ν (ρc t) with hG
  have hsubI : Set.uIcc t y ⊆ Set.Icc 0 T := Set.uIcc_subset_Icc htI hyI
  have hGc : ContinuousInHsOn m G (Set.uIcc t y) := by
    have h := continuousInHsOn_sub_const hr _ (hr.1 t htI)
    exact ⟨fun τ hτ => h.1 τ (hsubI hτ), fun τ0 hτ0 => (h.2 τ0 (hsubI hτ0)).mono_left
      (nhdsWithin_mono _ hsubI)⟩
  have hGη : ∀ σ ∈ Set.uIcc t y, hsNorm m (G σ) ≤ η := by
    intro σ hσ
    have hσ0 := hsubI hσ
    have hdist : dist σ t < δ0 := by
      rw [Real.dist_eq]
      refine lt_of_le_of_lt ?_ hy1
      rw [Set.mem_uIcc] at hσ
      rcases hσ with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; linarith
      · rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
    have := hδ0' hσ0 hdist
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hsNorm_nonneg _ _)] at this
    exact this.le
  obtain ⟨hM1, hM2⟩ := hsNorm_integral_le m G t y η hGc hGη
  -- the difference quotient as a coefficient sequence
  set a : ℝ := (y - t)⁻¹ with ha
  set D : Coeff d := fun k => (a : ℂ) * (ρc y k - ρc t k) - mfRhsCoeff d s V ν (ρc t) k with hD
  have hDeq : D = fun k => (a : ℂ) * (∫ σ in t..y, G σ k) := by
    funext k
    have hcont := rhs_mode_continuousOn_on hd s hs0 hsd K hK1 V ρ₀ hV ν ρc H.sol k
    have hint : IntervalIntegrable (fun σ => mfRhsCoeff d s V ν (ρc σ) k) volume t y :=
      (hcont.mono hsubI).intervalIntegrable
    have hGk : ∫ σ in t..y, G σ k = (∫ σ in t..y, mfRhsCoeff d s V ν (ρc σ) k) -
        (y - t) * mfRhsCoeff d s V ν (ρc t) k := by
      simp only [hG, Pi.sub_apply]
      rw [intervalIntegral.integral_sub hint intervalIntegrable_const, intervalIntegral.integral_const]
      simp
    rw [hGk, ← coeff_sub_eq_integral_on hd s hs0 hsd K hK1 V ρ₀ hV ν ρc H.sol k htI hyI]
    simp only [hD, ha]
    have hc : ((y : ℂ) - (t : ℂ)) ≠ 0 := by exact_mod_cast hsub
    push_cast
    field_simp
  have hDmem : MemHs m D ∧ hsNorm m D ≤ |a| * (|y - t| * η) := by
    rw [hDeq]
    obtain ⟨h1, h2⟩ := hs_const_mul m a _ hM1
    exact ⟨h1, h2.trans (mul_le_mul_of_nonneg_left hM2 (abs_nonneg _))⟩
  have hDb : |a| * (|y - t| * η) = η := by
    rw [ha, abs_inv, ← mul_assoc, inv_mul_cancel₀ (abs_ne_zero.mpr hsub), one_mul]
  -- pointwise value
  have hval : toFun D x = (toFun (ρc y) x - toFun (ρc t) x) / (y - t) -
      toFun (mfRhsCoeff d s V ν (ρc t)) x := by
    have := toFun_lin (ρc y) (ρc t) (mfRhsCoeff d s V ν (ρc t)) a (hsumK y hyI)
      (hsumK t htI) (hsumr t htI) x
    simp only [hD]
    rw [this, ha]
    ring
  obtain ⟨hl1, hl2⟩ := hCℓ D hDmem.1
  have hbound : |toFun D x| ≤ Cℓ * η := by
    refine (HRS.PDE.MFProduct.abs_toFun_le D hl1 x).trans (hl2.trans ?_)
    exact mul_le_mul_of_nonneg_left (hDmem.2.trans (le_of_eq hDb)) hCℓ0
  rw [Real.dist_eq, slope_def_field]
  have : mfPath ρc y x = toFun (ρc y) x := rfl
  have h2 : mfPath ρc t x = toFun (ρc t) x := rfl
  rw [this, h2, ← hval]
  refine lt_of_le_of_lt hbound ?_
  rw [hη]
  have : Cℓ * (ε / (Cℓ + 1)) = ε * (Cℓ / (Cℓ + 1)) := by ring
  rw [this]
  have : Cℓ / (Cℓ + 1) < 1 := by rw [div_lt_one (by linarith)]; linarith
  nlinarith


theorem continuousOn_mfPath_prod_on (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (K : ℕ)
    (hK : (d : ℝ) / 2 + 2 < K) (V ρ₀ : Torus d → ℝ) (hV : Torus.IsCk (K + 2) V) (ν : ℝ)
    (ρc : ℝ → Coeff d) {T : ℝ} (H : MFSolRealOn d s V ν K ρ₀ ρc T) :
    ContinuousOn (fun p : ℝ × Torus d => mfPath ρc p.1 p.2) (Set.Icc 0 T ×ˢ Set.univ) ∧
    ContinuousOn (fun p : ℝ × Torus d => toFun (mfRhsCoeff d s V ν (ρc p.1)) p.2)
      (Set.Icc 0 T ×ˢ Set.univ) :=
  ⟨continuousOn_toFun_prod' K (by linarith) ρc _ H.sol.cont,
    continuousOn_toFun_prod' ((K : ℝ) - 2) (by linarith) _ _
      (rhs_continuousInHsOn' hd s hs0 hsd K (by linarith) V hV ν ρc _ H.sol.cont)⟩

/-- Time shift: the solution restarted at `t₀ ∈ [0,T]` is a solution on `[0, T - t₀]` with
initial density `ρ^{t₀}` (`coeffOf (mfPath ρc t₀) = ρc t₀` by `coeffOf_toFun`, `K > d/2`). -/
theorem MFSolRealOn.shift {s : ℝ} {V : Torus d → ℝ} {ν K : ℝ} (hK : (d : ℝ) / 2 < K)
    {ρ₀ : Torus d → ℝ} {ρc : ℝ → Coeff d} {T : ℝ} (H : MFSolRealOn d s V ν K ρ₀ ρc T) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Set.Icc 0 T) :
    MFSolRealOn d s V ν K (mfPath ρc t₀) (fun τ => ρc (t₀ + τ)) (T - t₀) := by
  have hsum : Summable fun k => ‖ρc t₀ k‖ := summable_norm_of_memHs K hK _ (H.sol.cont.1 t₀ ht₀)
  have hco : coeffOf (mfPath ρc t₀) = ρc t₀ := coeffOf_toFun _ (H.real t₀ ht₀) hsum
  have hmem : ∀ τ ∈ Set.Icc 0 (T - t₀), t₀ + τ ∈ Set.Icc 0 T := fun τ hτ =>
    ⟨add_nonneg ht₀.1 hτ.1, by linarith [hτ.2]⟩
  refine ⟨⟨?_, ?_, ?_, ?_⟩, fun t ht => H.real _ (hmem t ht)⟩
  · rw [hco]; simp
  · refine ⟨fun τ hτ => H.sol.cont.1 _ (hmem τ hτ), fun τ0 hτ0 => ?_⟩
    have h := H.sol.cont.2 (t₀ + τ0) (hmem τ0 hτ0)
    have ht : Tendsto (fun τ : ℝ => t₀ + τ) (𝓝[Set.Icc 0 (T - t₀)] τ0)
        (𝓝[Set.Icc 0 T] (t₀ + τ0)) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨((continuous_const.add continuous_id).tendsto τ0).mono_left nhdsWithin_le_nhds,
        eventually_nhdsWithin_of_forall hmem⟩
    have := h.comp ht
    exact this
  · intro k t ht
    have ht' := hmem t ht
    have hI : IntervalIntegrable (fun σ => mfRhsCoeff d s V ν (ρc σ) k) volume (t₀ + 0) (t₀ + t) := by
      have h1 := (intervalIntegrable_iff_integrableOn_Icc_of_le ht'.1).2 (H.sol.integrable k _ ht')
      refine h1.mono_set ?_
      rw [Set.uIcc_of_le ht'.1, Set.uIcc_of_le (by linarith [ht.1])]
      exact Set.Icc_subset_Icc (by linarith [ht₀.1]) le_rfl
    have h2 := hI.comp_add_left t₀
    simp only [add_zero, add_sub_cancel_left, sub_self] at h2
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le ht.1).1 h2
  · intro k t ht
    have ht' := hmem t ht
    have hint : ∀ a b : ℝ, a ∈ Set.Icc 0 T → b ∈ Set.Icc 0 T →
        IntervalIntegrable (fun σ => mfRhsCoeff d s V ν (ρc σ) k) volume a b := by
      intro a b ha hb
      have h0 := fun u (hu : u ∈ Set.Icc 0 T) =>
        (intervalIntegrable_iff_integrableOn_Icc_of_le hu.1).2 (H.sol.integrable k u hu)
      have ha0 := (h0 a ha).symm
      have hb0 := h0 b hb
      exact ha0.trans hb0
    have e1 := H.sol.eq k _ ht'
    have e2 := H.sol.eq k _ ht₀
    have e3 := intervalIntegral.integral_add_adjacent_intervals (hint 0 t₀ ⟨le_rfl, ht₀.1.trans ht₀.2⟩ ht₀)
      (hint t₀ (t₀ + t) ht₀ ht')
    have e4 : ∫ σ in (0 : ℝ)..t, mfRhsCoeff d s V ν (ρc (t₀ + σ)) k =
        ∫ σ in t₀..(t₀ + t), mfRhsCoeff d s V ν (ρc σ) k := by
      rw [intervalIntegral.integral_comp_add_left (fun σ => mfRhsCoeff d s V ν (ρc σ) k) t₀]
      simp
    rw [e4, hco]
    linear_combination e1 - e2 - e3
