import HRS.MS.FixEqP2Aux1

/-!
# S5.7 `fixed_equation` (worker S57P), part 5: stability of classical adjoint solutions in the terminal time

Abstract version of `HRS/MS/GoMeasAux3.lean` (`s55m_*`): the coefficient `C` enters only through `S57pGen C T` (uniform
generator bound and continuity of the generator along converging families, both proved for `fixedEqCoeff` in `FixEqP2Aux1`),
uniqueness of classical adjoint solutions (`S52bUniq C T`, an explicit hypothesis) and uniform `C^{n+1}` bounds of the orbits.
`s57p_stab_seq`: along a sequence `t_i -> t_0` of terminal times, a subsequence of the orbits `U^{r,t_i} psi_{t_i}` converges
(with all derivatives up to order `n`, pointwise) to `U^{r,t_0} psi_{t_0}`; hence the jets are continuous in the terminal time
(`s57p_jet_continuousOn`).  Pointwise convergence of derivatives is all one can have for `Q != 0` (the transport moves
points at speed `|x|`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.FixEq

open HRS HRS.Whole HRS.MP.RdGen HRS.MS.Go HRS.MS.Fcau

variable {d : ℕ}

/-- the generator facts used by the stability argument -/
structure S57pGen (C : WholeCoeff d) (T : ℝ) : Prop where
  bound : ∃ K : ℝ, 0 ≤ K ∧ ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ (B : ℝ) (u : Euc d → ℝ), 0 ≤ B → ContDiff ℝ 4 u →
    (∀ n ≤ 4, ∀ x, ‖iteratedFDeriv ℝ n u x‖ ≤ B) →
    RgW (fun x => 1 + ‖x‖) 1 (B * K) (generatorW C τ u)
  tendsto : ∀ {B : ℝ}, 0 ≤ B → ∀ {τ : ℕ → ℝ} {τ₀ : ℝ}, (∀ m, τ m ∈ Set.Icc (0 : ℝ) T) →
    τ₀ ∈ Set.Icc (0 : ℝ) T → Tendsto τ atTop (𝓝 τ₀) → ∀ {u : ℕ → Euc d → ℝ} {u₀ : Euc d → ℝ},
    (∀ m, ContDiff ℝ 3 (u m) ∧ ∀ n ≤ 3, ∀ x, ‖iteratedFDeriv ℝ n (u m) x‖ ≤ B) →
    (ContDiff ℝ 3 u₀ ∧ ∀ n ≤ 3, ∀ x, ‖iteratedFDeriv ℝ n u₀ x‖ ≤ B) →
    (∀ y, Tendsto (fun m => iteratedFDeriv ℝ 1 (u m) y) atTop (𝓝 (iteratedFDeriv ℝ 1 u₀ y))) →
    ∀ x : Euc d, Tendsto (fun m => iteratedFDeriv ℝ 2 (u m) x) atTop (𝓝 (iteratedFDeriv ℝ 2 u₀ x)) →
    Tendsto (fun m => generatorW C (τ m) (u m) x) atTop (𝓝 (generatorW C τ₀ u₀ x))

theorem s57p_cont_gen {C : WholeCoeff d} {T : ℝ} (G : S57pGen C T) {B K L : ℝ}
    (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hgen : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ u : Euc d → ℝ, ContDiff ℝ 4 u →
      (∀ n ≤ 4, ∀ x, ‖iteratedFDeriv ℝ n u x‖ ≤ B) →
      RgW (fun x => 1 + ‖x‖) 1 (B * K) (generatorW (C) τ u))
    {g : ℝ → Euc d → ℝ}
    (hG : ∀ r', ContDiff ℝ 4 (g r') ∧ ∀ j ≤ 4, ∀ x, ‖iteratedFDeriv ℝ j (g r') x‖ ≤ B)
    (hgr : ∀ r r' x, |g r x - g r' x| ≤ L * (1 + ‖x‖) * |r - r'|) :
    Continuous fun p : Set.Icc (0 : ℝ) T × Euc d => generatorW (C) p.1 (g p.1) p.2 := by
  refine continuous_iff_seqContinuous.2 fun pm p₀ hp => ?_
  have hτ : Tendsto (fun m => ((pm m).1 : ℝ)) atTop (𝓝 (p₀.1 : ℝ)) :=
    ((continuous_subtype_val.comp continuous_fst).tendsto _).comp hp
  have hx : Tendsto (fun m => (pm m).2) atTop (𝓝 p₀.2) := (continuous_snd.tendsto _).comp hp
  have hcv := s55m_conv_tau hB hG hgr hτ
  have h1 : Tendsto (fun m => generatorW (C) ((pm m).1 : ℝ) (g (pm m).1) p₀.2) atTop
      (𝓝 (generatorW (C) (p₀.1 : ℝ) (g p₀.1) p₀.2)) :=
    G.tendsto hB (fun m => (pm m).1.2) p₀.1.2 hτ
      (u := fun m => g (pm m).1) (u₀ := g p₀.1)
      (fun m => ⟨(hG _).1.of_le (by norm_num), fun n hn x => (hG _).2 n (by omega) x⟩)
      ⟨(hG _).1.of_le (by norm_num), fun n hn x => (hG _).2 n (by omega) x⟩
      (fun y => hcv 1 (by norm_num) y) p₀.2 (hcv 2 le_rfl p₀.2)
  have hδ : Tendsto (fun m => ‖(pm m).2 - p₀.2‖) atTop (𝓝 0) := by
    simpa using (hx.sub_const p₀.2).norm
  have h2 : ∀ m, |generatorW (C) ((pm m).1 : ℝ) (g (pm m).1) (pm m).2 -
      generatorW (C) ((pm m).1 : ℝ) (g (pm m).1) p₀.2| ≤
      B * K * (1 + ‖p₀.2‖ + ‖(pm m).2 - p₀.2‖) * ‖(pm m).2 - p₀.2‖ := by
    intro m
    have hr := hgen _ (pm m).1.2 (g (pm m).1) (hG _).1 (hG _).2
    set R : ℝ := max ‖(pm m).2‖ ‖p₀.2‖ with hR
    have hRle : 1 + R ≤ 1 + ‖p₀.2‖ + ‖(pm m).2 - p₀.2‖ := by
      have : ‖(pm m).2‖ ≤ ‖p₀.2‖ + ‖(pm m).2 - p₀.2‖ := by
        calc ‖(pm m).2‖ = ‖p₀.2 + ((pm m).2 - p₀.2)‖ := by congr 1; abel
          _ ≤ _ := norm_add_le _ _
      have h0 := norm_nonneg ((pm m).2 - p₀.2)
      rw [hR]
      rcases le_total ‖(pm m).2‖ ‖p₀.2‖ with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
    have hdiff : Differentiable ℝ (generatorW (C) ((pm m).1 : ℝ) (g (pm m).1)) :=
      hr.1.differentiable (by norm_num)
    have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
      (f := generatorW (C) ((pm m).1 : ℝ) (g (pm m).1)) (C := B * K * (1 + R))
      (s := Metric.closedBall (0 : Euc d) R) (x := p₀.2) (y := (pm m).2) (fun z _ => hdiff z) (fun z hz => by
        have h1' := hr.2 1 le_rfl z
        rw [norm_iteratedFDeriv_one] at h1'
        have hz' : ‖z‖ ≤ R := by simpa using hz
        refine h1'.trans ?_
        have : 0 ≤ B * K := mul_nonneg hB hK
        exact mul_le_mul_of_nonneg_left (by linarith) this) (convex_closedBall _ _)
        (by simp [hR]) (by simp [hR])
    rw [Real.norm_eq_abs] at this
    refine this.trans ?_
    have : 0 ≤ B * K := mul_nonneg hB hK
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRle this) (norm_nonneg _)
  have h3 : Tendsto (fun m => B * K * (1 + ‖p₀.2‖ + ‖(pm m).2 - p₀.2‖) * ‖(pm m).2 - p₀.2‖) atTop (𝓝 0) := by
    simpa using (((tendsto_const_nhds (x := 1 + ‖p₀.2‖)).add hδ).const_mul (B * K)).mul hδ
  have h4 := tendsto_iff_norm_sub_tendsto_zero.1 h1
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  refine squeeze_zero (fun _ => norm_nonneg _) (fun m => ?_) (by simpa using h3.add h4)
  calc _ ≤ |generatorW (C) ((pm m).1 : ℝ) (g (pm m).1) (pm m).2 -
        generatorW (C) ((pm m).1 : ℝ) (g (pm m).1) p₀.2| +
      |generatorW (C) ((pm m).1 : ℝ) (g (pm m).1) p₀.2 -
        generatorW (C) (p₀.1 : ℝ) (g p₀.1) p₀.2| := by
          rw [Function.comp_apply, Real.norm_eq_abs]
          exact abs_sub_le _ _ _
    _ ≤ _ := add_le_add (h2 m) le_rfl

theorem s57p_limit_ftc {C : WholeCoeff d} {T : ℝ} (G : S57pGen C T) {B K t₀ : ℝ}
    (hB : 0 ≤ B) (hK : 0 ≤ K) (ht₀ : t₀ ∈ Set.Icc (0 : ℝ) T)
    (hgen : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ u : Euc d → ℝ, ContDiff ℝ 4 u →
      (∀ n ≤ 4, ∀ x, ‖iteratedFDeriv ℝ n u x‖ ≤ B) →
      RgW (fun x => 1 + ‖x‖) 1 (B * K) (generatorW (C) τ u))
    {F : ℕ → ℝ → Euc d → ℝ} {g : ℝ → Euc d → ℝ}
    (hF : ∀ n r', ContDiff ℝ 5 (F n r') ∧ ∀ j ≤ 5, ∀ x, ‖iteratedFDeriv ℝ j (F n r') x‖ ≤ B)
    (hFg : ∀ r' x, Tendsto (fun n => F n r' x) atTop (𝓝 (g r' x)))
    (hG' : ∀ r', ContDiff ℝ 4 (g r') ∧ (∀ j ≤ 4, ∀ x, ‖iteratedFDeriv ℝ j (g r') x‖ ≤ B) ∧
      ∀ j ≤ 4, ∀ x, Tendsto (fun n => iteratedFDeriv ℝ j (F n r') x) atTop
        (𝓝 (iteratedFDeriv ℝ j (g r') x)))
    (hftc : ∀ r₁ r₂ x, 0 ≤ r₁ → r₁ ≤ r₂ → r₂ < t₀ → ∀ᶠ n in atTop,
      F n r₁ x - F n r₂ x = ∫ τ in r₁..r₂, generatorW (C) τ (F n τ) x ∧
        ContinuousOn (fun τ => generatorW (C) τ (F n τ) x) (Set.Icc r₁ r₂))
    {r₁ r₂ : ℝ} (h1 : 0 ≤ r₁) (h12 : r₁ ≤ r₂) (h2 : r₂ < t₀) (x : Euc d) :
    g r₁ x - g r₂ x = ∫ τ in r₁..r₂, generatorW (C) τ (g τ) x := by
  have hmemT : ∀ τ ∈ Set.Ioc r₁ r₂, τ ∈ Set.Icc (0 : ℝ) T := fun τ hτ =>
    ⟨h1.trans hτ.1.le, hτ.2.trans (h2.le.trans ht₀.2)⟩
  have hlim : Tendsto (fun n => ∫ τ in r₁..r₂, generatorW (C) τ (F n τ) x) atTop
      (𝓝 (∫ τ in r₁..r₂, generatorW (C) τ (g τ) x)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => B * K * (1 + ‖x‖)) ?_ ?_ intervalIntegrable_const ?_
    · filter_upwards [hftc r₁ r₂ x h1 h12 h2] with n hn
      rw [Set.uIoc_of_le h12]
      exact (hn.2.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
    · refine Eventually.of_forall fun n => Eventually.of_forall fun τ hτ => ?_
      rw [Set.uIoc_of_le h12] at hτ
      have hr := hgen τ (hmemT τ hτ) (F n τ) ((hF n τ).1.of_le (by norm_num))
        (fun j hj x => (hF n τ).2 j (by omega) x)
      have := hr.2 0 (by norm_num) x
      rwa [norm_iteratedFDeriv_zero] at this
    · refine Eventually.of_forall fun τ hτ => ?_
      rw [Set.uIoc_of_le h12] at hτ
      refine G.tendsto hB (τ := fun _ => τ) (fun _ => hmemT τ hτ) (hmemT τ hτ)
        tendsto_const_nhds (u := fun n => F n τ) (u₀ := g τ)
        (fun n => ⟨(hF n τ).1.of_le (by norm_num), fun j hj x => (hF n τ).2 j (by omega) x⟩)
        ⟨(hG' τ).1.of_le (by norm_num), fun j hj x => (hG' τ).2.1 j (by omega) x⟩
        (fun y => (hG' τ).2.2 1 (by norm_num) y) x ((hG' τ).2.2 2 (by norm_num) x)
  have h3 : Tendsto (fun n => F n r₁ x - F n r₂ x) atTop (𝓝 (g r₁ x - g r₂ x)) :=
    (hFg _ _).sub (hFg _ _)
  have h4 := hlim.congr' ((hftc r₁ r₂ x h1 h12 h2).mono fun n hn => hn.1.symm)
  exact tendsto_nhds_unique h3 h4

theorem s57p_limit {C : WholeCoeff d} {T : ℝ} (G : S57pGen C T) {B K L t₀ : ℝ}
    (hB : 0 ≤ B) (hK : 0 ≤ K) (ht₀ : t₀ ∈ Set.Icc (0 : ℝ) T)
    (hgen : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ u : Euc d → ℝ, ContDiff ℝ 4 u →
      (∀ n ≤ 4, ∀ x, ‖iteratedFDeriv ℝ n u x‖ ≤ B) →
      RgW (fun x => 1 + ‖x‖) 1 (B * K) (generatorW (C) τ u))
    {F : ℕ → ℝ → Euc d → ℝ} {g : ℝ → Euc d → ℝ} {ψ₀ : Euc d → ℝ}
    (hF : ∀ n r', ContDiff ℝ 5 (F n r') ∧ ∀ j ≤ 5, ∀ x, ‖iteratedFDeriv ℝ j (F n r') x‖ ≤ B)
    (hFg : ∀ r' x, Tendsto (fun n => F n r' x) atTop (𝓝 (g r' x)))
    (hgr : ∀ r r' x, |g r x - g r' x| ≤ L * (1 + ‖x‖) * |r - r'|)
    (hftc : ∀ r₁ r₂ x, 0 ≤ r₁ → r₁ ≤ r₂ → r₂ < t₀ → ∀ᶠ n in atTop,
      F n r₁ x - F n r₂ x = ∫ τ in r₁..r₂, generatorW (C) τ (F n τ) x ∧
        ContinuousOn (fun τ => generatorW (C) τ (F n τ) x) (Set.Icc r₁ r₂))
    (hterm : g t₀ = ψ₀) : IsClassicalAdjointW (C) t₀ ψ₀ g := by
  have hG' := fun r' => s55m_limit_G hB hF hFg r'
  have hG : ∀ r', ContDiff ℝ 4 (g r') ∧ ∀ j ≤ 4, ∀ x, ‖iteratedFDeriv ℝ j (g r') x‖ ≤ B :=
    fun r' => ⟨(hG' r').1, (hG' r').2.1⟩
  have hcg := s57p_cont_gen G hB hK hgen hG hgr
  have hincl : Continuous fun p : Set.Icc (0 : ℝ) t₀ × Euc d =>
      ((⟨p.1.1, p.1.2.1, p.1.2.2.trans ht₀.2⟩ : Set.Icc (0 : ℝ) T), p.2) :=
    ((continuous_subtype_val.comp continuous_fst).subtype_mk _).prodMk continuous_snd
  have hcL : ∀ x, ContinuousOn (fun τ => generatorW (C) τ (g τ) x) (Set.Icc (0 : ℝ) T) := by
    intro x
    rw [continuousOn_iff_continuous_domRestrict]
    have hp : Continuous fun r : Set.Icc (0 : ℝ) T => ((r, x) : Set.Icc (0 : ℝ) T × Euc d) :=
      continuous_id.prodMk continuous_const
    exact Continuous.congr (hcg.comp hp) (fun r => rfl)
  refine ⟨fun r hr => (hG r).1.of_le (by norm_num), fun j hj => ⟨B, fun r hr x => (hG r).2 j (by omega) x⟩,
    fun j hj => ?_, hterm, ?_, ?_, ?_⟩
  · exact (s55m_cont_jet hB hG hgr (by omega)).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  · intro x r hr
    set r₂ : ℝ := (r + t₀) / 2 with hr₂
    have hr2 : r < r₂ ∧ r₂ < t₀ := ⟨by rw [hr₂]; linarith [hr.2], by rw [hr₂]; linarith [hr.2]⟩
    have hT : t₀ ≤ T := ht₀.2
    have hI : ∀ r'' ∈ Set.Icc (0 : ℝ) r₂, g r'' x = g r₂ x - ∫ τ in r₂..r'', generatorW (C) τ (g τ) x := by
      intro r'' hr''
      have := s57p_limit_ftc G hB hK ht₀ hgen hF hFg hG' hftc hr''.1 hr''.2 hr2.2 x
      rw [intervalIntegral.integral_symm]; linarith
    have hcont : ContinuousOn (fun τ => generatorW (C) τ (g τ) x) (Set.Icc (0 : ℝ) T) := hcL x
    have hrT : r ∈ Set.Ioo (0 : ℝ) T := ⟨hr.1, hr.2.trans_le hT⟩
    have hd : HasDerivAt (fun r'' => ∫ τ in r₂..r'', generatorW (C) τ (g τ) x)
        (generatorW (C) r (g r) x) r := by
      refine intervalIntegral.integral_hasDerivAt_right ?_ ?_ ?_
      · refine (hcont.mono ?_).intervalIntegrable
        rw [Set.uIcc_of_ge hr2.1.le]
        exact Set.Icc_subset_Icc hr.1.le (hr2.2.le.trans hT)
      · exact (hcont.mono Set.Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo r hrT
      · exact hcont.continuousAt (Icc_mem_nhds hrT.1 hrT.2)
    have hd2 := (hasDerivAt_const r (g r₂ x)).sub hd
    refine (hd2.congr_deriv (by ring)).congr_of_eventuallyEq ?_
    filter_upwards [Icc_mem_nhds hr.1 hr2.1] with r'' hr''
    exact hI r'' hr''
  · exact Continuous.congr (hcg.comp hincl) (fun p => rfl)
  · refine ⟨B * K, fun r hr x => ?_⟩
    have hrT : r ∈ Set.Icc (0 : ℝ) T := ⟨hr.1, hr.2.trans ht₀.2⟩
    have := (hgen r hrT (g r) (hG r).1 (hG r).2).2 0 (by norm_num) x
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this

/-! ### Convergence of a subsequence of the clipped family -/

/-- generalisation of `s55m_limit_G`: convergence of the derivatives up to order `n` from `C^{n+1}` bounds -/
theorem s57p_limit_G (n : ℕ) {B : ℝ} (hB : 0 ≤ B) {F : ℕ → Euc d → ℝ} {g : Euc d → ℝ}
    (hF : ∀ i, ContDiff ℝ (n + 1 : ℕ) (F i) ∧ ∀ j ≤ n + 1, ∀ x, ‖iteratedFDeriv ℝ j (F i) x‖ ≤ B)
    (hFg : ∀ x, Tendsto (fun i => F i x) atTop (𝓝 (g x))) :
    ContDiff ℝ n g ∧ (∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j g x‖ ≤ B) ∧
      ∀ j ≤ n, ∀ x, Tendsto (fun i => iteratedFDeriv ℝ j (F i) x) atTop (𝓝 (iteratedFDeriv ℝ j g x)) := by
  obtain ⟨h1, h2⟩ := s55m_dl n hB (F := ℝ) (h := F) (h₀ := g)
    (fun i => by simpa using (hF i).1) (fun i j hj x => (hF i).2 j (by omega) x) hFg
  exact ⟨by simpa using h1, fun j hj x => s55m_dl_bound (fun i => (hF i).2 j (by omega) x) (h2 j hj x), h2⟩

/-- **Stability in the terminal time** (abstract `s55m_seq`).  The orbits `fam t = U^{·,t} ψ_t` are classical adjoint
solutions, bounded in `C^{n+1}` uniformly in `t`, `ψ_t` is pointwise continuous in `t`, and classical solutions are
unique.  Then along `t_i → t₀` a subsequence of `U^{r,t_i} ψ_{t_i}` converges with all derivatives up to order `n`. -/
theorem s57p_stab_seq {C : WholeCoeff d} {T : ℝ} (G : S57pGen C T) (huniq : HRS.MS.S52B.S52bUniq C T)
    {n : ℕ} (hn4 : 4 ≤ n) {B : ℝ} (hB0 : 0 ≤ B) (ψ : ℝ → Euc d → ℝ)
    (hψc : ∀ y, ContinuousOn (fun t => ψ t y) (Set.Icc (0 : ℝ) T))
    (hcl : ∀ t ∈ Set.Icc (0 : ℝ) T, IsClassicalAdjointW C t (ψ t) (fun r => propagatorW C r t (ψ t)))
    (hsl : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ r' ∈ Set.Icc (0 : ℝ) t, ContDiff ℝ (n + 1 : ℕ) (propagatorW C r' t (ψ t)) ∧
      ∀ j ≤ n + 1, ∀ y, ‖iteratedFDeriv ℝ j (propagatorW C r' t (ψ t)) y‖ ≤ B)
    {r t₀ : ℝ} (hr0 : 0 ≤ r) (ht₀ : t₀ ∈ Set.Ioc r T) {tn : ℕ → ℝ}
    (htn : ∀ i, tn i ∈ Set.Ioc r T) (hlim : Tendsto tn atTop (𝓝 t₀)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ j ≤ n, ∀ x, Tendsto (fun i => iteratedFDeriv ℝ j
        (propagatorW C r (tn (ns i)) (ψ (tn (ns i)))) x) atTop
      (𝓝 (iteratedFDeriv ℝ j (propagatorW C r t₀ (ψ t₀)) x)) := by
  obtain ⟨K, hK0, hgen⟩ := G.bound
  set fam : ℝ → ℝ → Euc d → ℝ := fun t r' => propagatorW C r' t (ψ t) with hfamdef
  have hmemT : ∀ i, tn i ∈ Set.Icc (0 : ℝ) T := fun i => ⟨hr0.trans (htn i).1.le, (htn i).2⟩
  have ht₀T : t₀ ∈ Set.Icc (0 : ℝ) T := ⟨hr0.trans ht₀.1.le, ht₀.2⟩
  have hsl5 : ∀ i, ∀ r' ∈ Set.Icc (0 : ℝ) (tn i), ContDiff ℝ 5 (fam (tn i) r') ∧
      ∀ j ≤ 5, ∀ y, ‖iteratedFDeriv ℝ j (fam (tn i) r') y‖ ≤ B := by
    intro i r' hr'
    obtain ⟨h1, h2⟩ := hsl _ (hmemT i) r' hr'
    exact ⟨h1.of_le (by exact_mod_cast (by omega : 5 ≤ n + 1)), fun j hj y => h2 j (by omega) y⟩
  have hgl : ∀ i, ∀ τ ∈ Set.Icc (0 : ℝ) (tn i), ∀ y, |generatorW C τ (fam (tn i) τ) y| ≤ B * K * (1 + ‖y‖) := by
    intro i τ hτ y
    have hτT : τ ∈ Set.Icc (0 : ℝ) T := ⟨hτ.1, hτ.2.trans (hmemT i).2⟩
    obtain ⟨h1, h2⟩ := hsl5 i τ hτ
    have := (hgen τ hτT B (fam (tn i) τ) hB0 (h1.of_le (by norm_num)) (fun j hj => h2 j (by omega))).2 0
      (by norm_num) y
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  set cl : ℕ → ℝ → ℝ := fun i r' => max 0 (min r' (tn i)) with hcl_def
  have hclmem : ∀ i r', cl i r' ∈ Set.Icc (0 : ℝ) (tn i) := fun i r' =>
    ⟨le_max_left _ _, max_le (hmemT i).1 (min_le_right _ _)⟩
  set F : ℕ → ℝ → Euc d → ℝ := fun i r' => fam (tn i) (cl i r') with hFdef
  set L : ℝ := max B (B * K) with hL
  have hL0 : 0 ≤ L := le_max_of_le_left hB0
  have hFb : ∀ i r' y, |F i r' y| ≤ B := by
    intro i r' y
    have := (hsl5 i _ (hclmem i r')).2 0 (by norm_num) y
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hFr : ∀ i r' r'' y, |F i r' y - F i r'' y| ≤ L * (1 + ‖y‖) * |r' - r''| := by
    have key : ∀ i r' r'' y, r' ≤ r'' → |F i r' y - F i r'' y| ≤ L * (1 + ‖y‖) * |r' - r''| := by
      intro i r' r'' y hle
      have hcle : cl i r' ≤ cl i r'' := max_le_max le_rfl (min_le_min_right _ hle)
      have h1 := s55m_lip_r (hcl _ (hmemT i)) (BL := B * K) (hgl i) (hclmem i r').1 hcle (hclmem i r'').2 y
      have h2 := s55m_clip_le (tn i) r' r'' hle
      rw [abs_of_nonpos (sub_nonpos.2 hle), neg_sub]
      refine h1.trans ?_
      have : 0 ≤ B * K * (1 + ‖y‖) := by positivity
      calc B * K * (1 + ‖y‖) * (cl i r'' - cl i r') ≤ B * K * (1 + ‖y‖) * (r'' - r') :=
            mul_le_mul_of_nonneg_left h2 this
        _ ≤ L * (1 + ‖y‖) * (r'' - r') := by
            have h3 : B * K ≤ L := le_max_right _ _
            have h4 : 0 ≤ r'' - r' := sub_nonneg.2 hle
            gcongr
    intro i r' r'' y
    rcases le_total r' r'' with h | h
    · exact key i r' r'' y h
    · rw [abs_sub_comm (F i r' y), abs_sub_comm r' r'']; exact key i r'' r' y h
  have hFx : ∀ i r' y y', |F i r' y - F i r' y'| ≤ L * ‖y - y'‖ := by
    intro i r' y y'
    have hs := hsl5 i _ (hclmem i r')
    refine (s55m_lip_x (u := F i r') (B := B) (hs.1.differentiable (by norm_num)) (fun z => ?_) y y').trans ?_
    · have := hs.2 1 (by norm_num) z
      rwa [norm_iteratedFDeriv_one] at this
    · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  obtain ⟨ns, hns, g, hpt, hgr, -, -⟩ := s55m_ex F hL0 hFb hFr hFx
  set F' : ℕ → ℝ → Euc d → ℝ := fun i => F (ns i) with hF'
  have hF'b : ∀ i r', ContDiff ℝ 5 (F' i r') ∧ ∀ j ≤ 5, ∀ y, ‖iteratedFDeriv ℝ j (F' i r') y‖ ≤ B :=
    fun i r' => hsl5 (ns i) _ (hclmem (ns i) r')
  have htns : Tendsto (fun i => tn (ns i)) atTop (𝓝 t₀) := hlim.comp hns.tendsto_atTop
  have hftc : ∀ r₁ r₂ y, 0 ≤ r₁ → r₁ ≤ r₂ → r₂ < t₀ → ∀ᶠ i in atTop,
      F' i r₁ y - F' i r₂ y = ∫ τ in r₁..r₂, generatorW C τ (F' i τ) y ∧
        ContinuousOn (fun τ => generatorW C τ (F' i τ) y) (Set.Icc r₁ r₂) := by
    intro r₁ r₂ y h1 h12 h2
    filter_upwards [htns.eventually (Ioi_mem_nhds h2)] with i hi
    have hi' : r₂ ≤ tn (ns i) := le_of_lt hi
    have hcl_id : ∀ τ ∈ Set.Icc r₁ r₂, cl (ns i) τ = τ := by
      intro τ hτ
      show max 0 (min τ (tn (ns i))) = τ
      rw [min_eq_left (hτ.2.trans hi'), max_eq_right (h1.trans hτ.1)]
    have hFeq : ∀ τ ∈ Set.Icc r₁ r₂, F' i τ = fam (tn (ns i)) τ := fun τ hτ => by
      show fam (tn (ns i)) (cl (ns i) τ) = _
      rw [hcl_id τ hτ]
    refine ⟨?_, ?_⟩
    · rw [hFeq r₁ ⟨le_rfl, h12⟩, hFeq r₂ ⟨h12, le_rfl⟩, s55m_ftc (hcl _ (hmemT (ns i))) h1 h12 hi' y]
      refine intervalIntegral.integral_congr fun τ hτ => ?_
      rw [Set.uIcc_of_le h12] at hτ
      simp only [hFeq τ hτ]
      rfl
    · refine ((s55m_contL (hcl _ (hmemT (ns i))) y).mono (Set.Icc_subset_Icc h1 hi')).congr fun τ hτ => ?_
      simp only [hFeq τ hτ]
      rfl
  have hterm : g t₀ = ψ t₀ := by
    funext y
    have hψt : Tendsto (fun i => ψ (tn (ns i)) y) atTop (𝓝 (ψ t₀ y)) :=
      ((hψc y t₀ ht₀T).tendsto).comp (tendsto_nhdsWithin_iff.2 ⟨htns, Eventually.of_forall fun i => hmemT _⟩)
    have h1 : Tendsto (fun i => F' i t₀ y - ψ (tn (ns i)) y) atTop (𝓝 (g t₀ y - ψ t₀ y)) :=
      (hpt (t₀) y).sub hψt
    have h2 : Tendsto (fun i => F' i t₀ y - ψ (tn (ns i)) y) atTop (𝓝 0) := by
      have h0 : Tendsto (fun i => B * K * (1 + ‖y‖) * |t₀ - tn (ns i)|) atTop (𝓝 0) := by
        have := ((htns.const_sub t₀).abs).const_mul (B * K * (1 + ‖y‖))
        simpa using this
      refine squeeze_zero_norm (fun i => ?_) h0
      have hterm_i : ψ (tn (ns i)) = fam (tn (ns i)) (tn (ns i)) := ((hcl _ (hmemT (ns i))).terminal).symm
      rw [hterm_i, Real.norm_eq_abs]
      have := s55m_lip_r_abs (hcl _ (hmemT (ns i))) (BL := B * K) (hgl (ns i)) (by positivity) (hclmem (ns i) t₀)
        ⟨(hmemT (ns i)).1, le_rfl⟩ y
      refine this.trans ?_
      have h3 := s55m_clip_abs (tn (ns i)) t₀ (tn (ns i))
      have h4 : max 0 (min (tn (ns i)) (tn (ns i))) = tn (ns i) := by
        rw [min_self, max_eq_right (hmemT _).1]
      rw [h4] at h3
      exact mul_le_mul_of_nonneg_left h3 (by positivity)
    have := tendsto_nhds_unique h1 h2
    linarith
  have hcl' : IsClassicalAdjointW C t₀ (ψ t₀) g :=
    s57p_limit G hB0 hK0 ht₀T (fun τ hτ u hu hub => hgen τ hτ B u hB0 hu hub) (F := F') hF'b hpt hgr hftc hterm
  have hfg : ∀ r' ∈ Set.Icc (0 : ℝ) t₀, propagatorW C r' t₀ (ψ t₀) = g r' :=
    fun r' hr' => huniq t₀ ht₀T (ψ t₀) _ g (propagatorW_isClassical ⟨_, hcl _ ht₀T⟩) hcl' r' hr'
  have hrle : ∀ i, F' i r = fam (tn (ns i)) r := fun i => by
    show fam (tn (ns i)) (cl (ns i) r) = _
    have : cl (ns i) r = r := by
      show max 0 (min r (tn (ns i))) = r
      rw [min_eq_left (htn _).1.le, max_eq_right hr0]
    rw [this]
  have hG1 := s57p_limit_G n hB0 (F := fun i => F' i r) (g := g r)
    (fun i => hsl _ (hmemT (ns i)) _ (hclmem (ns i) r)) (hpt r)
  refine ⟨ns, hns, fun j hj x => ?_⟩
  have := hG1.2.2 j hj x
  rw [hfg r ⟨hr0, ht₀.1.le⟩]
  refine this.congr fun i => ?_
  rw [hrle i]

/-- continuity of the jets of the orbit in the terminal time -/
theorem s57p_jet_continuousOn {C : WholeCoeff d} {T : ℝ} (G : S57pGen C T) (huniq : HRS.MS.S52B.S52bUniq C T)
    {n : ℕ} (hn4 : 4 ≤ n) {B : ℝ} (hB0 : 0 ≤ B) (ψ : ℝ → Euc d → ℝ)
    (hψc : ∀ y, ContinuousOn (fun t => ψ t y) (Set.Icc (0 : ℝ) T))
    (hcl : ∀ t ∈ Set.Icc (0 : ℝ) T, IsClassicalAdjointW C t (ψ t) (fun r => propagatorW C r t (ψ t)))
    (hsl : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ r' ∈ Set.Icc (0 : ℝ) t, ContDiff ℝ (n + 1 : ℕ) (propagatorW C r' t (ψ t)) ∧
      ∀ j ≤ n + 1, ∀ y, ‖iteratedFDeriv ℝ j (propagatorW C r' t (ψ t)) y‖ ≤ B)
    {r : ℝ} (hr0 : 0 ≤ r) {j : ℕ} (hj : j ≤ n) (x : Euc d) :
    ContinuousOn (fun t => iteratedFDeriv ℝ j (propagatorW C r t (ψ t)) x) (Set.Ioc r T) := by
  intro t₀ ht₀
  rw [ContinuousWithinAt, tendsto_iff_seq_tendsto]
  intro tn htn
  obtain ⟨hlim, hev⟩ := tendsto_nhdsWithin_iff.1 htn
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hev
  set tn' : ℕ → ℝ := fun i => tn (i + n₀) with htn'
  have hlim' : Tendsto tn' atTop (𝓝 t₀) := hlim.comp (tendsto_add_atTop_nat n₀)
  have hmem : ∀ i, tn' i ∈ Set.Ioc r T := fun i => hn₀ _ (by omega)
  rw [← tendsto_add_atTop_iff_nat n₀]
  refine tendsto_of_subseq_tendsto fun ns₁ hns₁ => ?_
  obtain ⟨ns, hns, h⟩ := s57p_stab_seq G huniq hn4 hB0 ψ hψc hcl hsl hr0 ht₀ (tn := fun i => tn' (ns₁ i))
    (fun i => hmem _) (hlim'.comp hns₁)
  exact ⟨ns, h j hj x⟩

end HRS.MS.FixEq
