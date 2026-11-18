import HRS.MS.GoMeasAux3
import HRS.MS.UlWitAux1
import HRS.MS.UlTail
import HRS.MS.FcauTie

/-!
# UL-W (part 2): compactness and limits of classical adjoint solutions for an explicit coefficient

Generic versions (for an arbitrary `WholeCoeff` satisfying `UlwGenHyp`) of the S55M limit machinery of
`GoMeasAux3` (`s55m_cont_gen`, `s55m_limit_ftc`, `s55m_limit`), which there are stated for the coefficients of a
`WholeSetup` (whose `adjoint` field is `UlAdjointInput`, so cannot be used for the witness).  Plus
`ulw_compact`: a sequence of classical adjoint solutions with a common terminal time, uniformly bounded in `C_b^5`,
with terminal data converging pointwise, has a subsequence converging pointwise to a classical adjoint solution.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

namespace HRS.MS.UlW

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.DualityRd HRS.MP.RdGen HRS.MS.Go

variable {d : ℕ}

/-- The two properties of a generator used by the limit machinery (`s55m_gen_rgW`, `s55m_gen_tendsto_S`):
a uniform weighted `C^1` bound for `C^4` functions with bounded derivatives, and convergence of `generatorW` along
converging families (nonlocal term included). -/
structure UlwGenHyp (C : WholeCoeff d) (T K : ℝ) : Prop where
  K0 : 0 ≤ K
  bound : ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ (B : ℝ) (u : Euc d → ℝ), 0 ≤ B → ContDiff ℝ 4 u →
    (∀ n ≤ 4, ∀ x, ‖iteratedFDeriv ℝ n u x‖ ≤ B) →
    RgW (fun x => 1 + ‖x‖) 1 (B * K) (generatorW C τ u)
  tend : ∀ (B : ℝ), 0 ≤ B → ∀ {τ : ℕ → ℝ} {τ₀ : ℝ}, (∀ m, τ m ∈ Set.Icc (0 : ℝ) T) →
    τ₀ ∈ Set.Icc (0 : ℝ) T → Tendsto τ atTop (𝓝 τ₀) → ∀ {u : ℕ → Euc d → ℝ} {u₀ : Euc d → ℝ},
    (∀ m, ContDiff ℝ 3 (u m) ∧ ∀ n ≤ 3, ∀ x, ‖iteratedFDeriv ℝ n (u m) x‖ ≤ B) →
    (ContDiff ℝ 3 u₀ ∧ ∀ n ≤ 3, ∀ x, ‖iteratedFDeriv ℝ n u₀ x‖ ≤ B) →
    (∀ y, Tendsto (fun m => iteratedFDeriv ℝ 1 (u m) y) atTop (𝓝 (iteratedFDeriv ℝ 1 u₀ y))) →
    ∀ x, Tendsto (fun m => iteratedFDeriv ℝ 2 (u m) x) atTop (𝓝 (iteratedFDeriv ℝ 2 u₀ x)) →
    Tendsto (fun m => generatorW C (τ m) (u m) x) atTop (𝓝 (generatorW C τ₀ u₀ x))

theorem ulw_cont_gen {C : WholeCoeff d} {T K : ℝ} (hU : UlwGenHyp C T K) {B L : ℝ}
    (hB : 0 ≤ B)
    {g : ℝ → Euc d → ℝ}
    (hG : ∀ r', ContDiff ℝ 4 (g r') ∧ ∀ j ≤ 4, ∀ x, ‖iteratedFDeriv ℝ j (g r') x‖ ≤ B)
    (hgr : ∀ r r' x, |g r x - g r' x| ≤ L * (1 + ‖x‖) * |r - r'|) :
    Continuous fun p : Set.Icc (0 : ℝ) T × Euc d => generatorW C p.1 (g p.1) p.2 := by
  refine continuous_iff_seqContinuous.2 fun pm p₀ hp => ?_
  have hτ : Tendsto (fun m => ((pm m).1 : ℝ)) atTop (𝓝 (p₀.1 : ℝ)) :=
    ((continuous_subtype_val.comp continuous_fst).tendsto _).comp hp
  have hx : Tendsto (fun m => (pm m).2) atTop (𝓝 p₀.2) := (continuous_snd.tendsto _).comp hp
  have hcv := s55m_conv_tau hB hG hgr hτ
  have h1 : Tendsto (fun m => generatorW C ((pm m).1 : ℝ) (g (pm m).1) p₀.2) atTop
      (𝓝 (generatorW C (p₀.1 : ℝ) (g p₀.1) p₀.2)) :=
    hU.tend B hB (fun m => (pm m).1.2) p₀.1.2 hτ
      (u := fun m => g (pm m).1) (u₀ := g p₀.1)
      (fun m => ⟨(hG _).1.of_le (by norm_num), fun n hn x => (hG _).2 n (by omega) x⟩)
      ⟨(hG _).1.of_le (by norm_num), fun n hn x => (hG _).2 n (by omega) x⟩
      (fun y => hcv 1 (by norm_num) y) p₀.2 (hcv 2 le_rfl p₀.2)
  have hδ : Tendsto (fun m => ‖(pm m).2 - p₀.2‖) atTop (𝓝 0) := by
    simpa using (hx.sub_const p₀.2).norm
  have h2 : ∀ m, |generatorW C ((pm m).1 : ℝ) (g (pm m).1) (pm m).2 -
      generatorW C ((pm m).1 : ℝ) (g (pm m).1) p₀.2| ≤
      B * K * (1 + ‖p₀.2‖ + ‖(pm m).2 - p₀.2‖) * ‖(pm m).2 - p₀.2‖ := by
    intro m
    have hr := hU.bound _ (pm m).1.2 B (g (pm m).1) hB (hG _).1 (hG _).2
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
    have hdiff : Differentiable ℝ (generatorW C ((pm m).1 : ℝ) (g (pm m).1)) :=
      hr.1.differentiable (by norm_num)
    have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
      (f := generatorW C ((pm m).1 : ℝ) (g (pm m).1)) (C := B * K * (1 + R))
      (s := Metric.closedBall (0 : Euc d) R) (x := p₀.2) (y := (pm m).2) (fun z _ => hdiff z) (fun z hz => by
        have h1' := hr.2 1 le_rfl z
        rw [norm_iteratedFDeriv_one] at h1'
        have hz' : ‖z‖ ≤ R := by simpa using hz
        refine h1'.trans ?_
        have : 0 ≤ B * K := mul_nonneg hB hU.K0
        exact mul_le_mul_of_nonneg_left (by linarith) this) (convex_closedBall _ _)
        (by simp [hR]) (by simp [hR])
    rw [Real.norm_eq_abs] at this
    refine this.trans ?_
    have : 0 ≤ B * K := mul_nonneg hB hU.K0
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRle this) (norm_nonneg _)
  have h3 : Tendsto (fun m => B * K * (1 + ‖p₀.2‖ + ‖(pm m).2 - p₀.2‖) * ‖(pm m).2 - p₀.2‖) atTop (𝓝 0) := by
    simpa using (((tendsto_const_nhds (x := 1 + ‖p₀.2‖)).add hδ).const_mul (B * K)).mul hδ
  have h4 := tendsto_iff_norm_sub_tendsto_zero.1 h1
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  refine squeeze_zero (fun _ => norm_nonneg _) (fun m => ?_) (by simpa using h3.add h4)
  calc _ ≤ |generatorW C ((pm m).1 : ℝ) (g (pm m).1) (pm m).2 -
        generatorW C ((pm m).1 : ℝ) (g (pm m).1) p₀.2| +
      |generatorW C ((pm m).1 : ℝ) (g (pm m).1) p₀.2 -
        generatorW C (p₀.1 : ℝ) (g p₀.1) p₀.2| := by
          rw [Function.comp_apply, Real.norm_eq_abs]
          exact abs_sub_le _ _ _
    _ ≤ _ := add_le_add (h2 m) le_rfl

theorem ulw_limit_ftc {C : WholeCoeff d} {T K : ℝ} (hU : UlwGenHyp C T K) {B t₀ : ℝ}
    (hB : 0 ≤ B) (ht₀ : t₀ ∈ Set.Icc (0 : ℝ) T)
    {F : ℕ → ℝ → Euc d → ℝ} {g : ℝ → Euc d → ℝ}
    (hF : ∀ n r', ContDiff ℝ 5 (F n r') ∧ ∀ j ≤ 5, ∀ x, ‖iteratedFDeriv ℝ j (F n r') x‖ ≤ B)
    (hFg : ∀ r' x, Tendsto (fun n => F n r' x) atTop (𝓝 (g r' x)))
    (hG' : ∀ r', ContDiff ℝ 4 (g r') ∧ (∀ j ≤ 4, ∀ x, ‖iteratedFDeriv ℝ j (g r') x‖ ≤ B) ∧
      ∀ j ≤ 4, ∀ x, Tendsto (fun n => iteratedFDeriv ℝ j (F n r') x) atTop
        (𝓝 (iteratedFDeriv ℝ j (g r') x)))
    (hftc : ∀ r₁ r₂ x, 0 ≤ r₁ → r₁ ≤ r₂ → r₂ < t₀ → ∀ᶠ n in atTop,
      F n r₁ x - F n r₂ x = ∫ τ in r₁..r₂, generatorW C τ (F n τ) x ∧
        ContinuousOn (fun τ => generatorW C τ (F n τ) x) (Set.Icc r₁ r₂))
    {r₁ r₂ : ℝ} (h1 : 0 ≤ r₁) (h12 : r₁ ≤ r₂) (h2 : r₂ < t₀) (x : Euc d) :
    g r₁ x - g r₂ x = ∫ τ in r₁..r₂, generatorW C τ (g τ) x := by
  have hmemT : ∀ τ ∈ Set.Ioc r₁ r₂, τ ∈ Set.Icc (0 : ℝ) T := fun τ hτ =>
    ⟨h1.trans hτ.1.le, hτ.2.trans (h2.le.trans ht₀.2)⟩
  have hlim : Tendsto (fun n => ∫ τ in r₁..r₂, generatorW C τ (F n τ) x) atTop
      (𝓝 (∫ τ in r₁..r₂, generatorW C τ (g τ) x)) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => B * K * (1 + ‖x‖)) ?_ ?_ intervalIntegrable_const ?_
    · filter_upwards [hftc r₁ r₂ x h1 h12 h2] with n hn
      rw [Set.uIoc_of_le h12]
      exact (hn.2.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
    · refine Eventually.of_forall fun n => Eventually.of_forall fun τ hτ => ?_
      rw [Set.uIoc_of_le h12] at hτ
      have hr := hU.bound τ (hmemT τ hτ) B (F n τ) hB ((hF n τ).1.of_le (by norm_num))
        (fun j hj x => (hF n τ).2 j (by omega) x)
      have := hr.2 0 (by norm_num) x
      rwa [norm_iteratedFDeriv_zero] at this
    · refine Eventually.of_forall fun τ hτ => ?_
      rw [Set.uIoc_of_le h12] at hτ
      refine hU.tend B hB (τ := fun _ => τ) (fun _ => hmemT τ hτ) (hmemT τ hτ)
        tendsto_const_nhds (u := fun n => F n τ) (u₀ := g τ)
        (fun n => ⟨(hF n τ).1.of_le (by norm_num), fun j hj x => (hF n τ).2 j (by omega) x⟩)
        ⟨(hG' τ).1.of_le (by norm_num), fun j hj x => (hG' τ).2.1 j (by omega) x⟩
        (fun y => (hG' τ).2.2 1 (by norm_num) y) x ((hG' τ).2.2 2 (by norm_num) x)
  have h3 : Tendsto (fun n => F n r₁ x - F n r₂ x) atTop (𝓝 (g r₁ x - g r₂ x)) :=
    (hFg _ _).sub (hFg _ _)
  have h4 := hlim.congr' ((hftc r₁ r₂ x h1 h12 h2).mono fun n hn => hn.1.symm)
  exact tendsto_nhds_unique h3 h4

theorem ulw_limit {C : WholeCoeff d} {T K : ℝ} (hU : UlwGenHyp C T K) {B L t₀ : ℝ}
    (hB : 0 ≤ B) (ht₀ : t₀ ∈ Set.Icc (0 : ℝ) T)
    {F : ℕ → ℝ → Euc d → ℝ} {g : ℝ → Euc d → ℝ} {ψ₀ : Euc d → ℝ}
    (hF : ∀ n r', ContDiff ℝ 5 (F n r') ∧ ∀ j ≤ 5, ∀ x, ‖iteratedFDeriv ℝ j (F n r') x‖ ≤ B)
    (hFg : ∀ r' x, Tendsto (fun n => F n r' x) atTop (𝓝 (g r' x)))
    (hgr : ∀ r r' x, |g r x - g r' x| ≤ L * (1 + ‖x‖) * |r - r'|)
    (hftc : ∀ r₁ r₂ x, 0 ≤ r₁ → r₁ ≤ r₂ → r₂ < t₀ → ∀ᶠ n in atTop,
      F n r₁ x - F n r₂ x = ∫ τ in r₁..r₂, generatorW C τ (F n τ) x ∧
        ContinuousOn (fun τ => generatorW C τ (F n τ) x) (Set.Icc r₁ r₂))
    (hterm : g t₀ = ψ₀) : IsClassicalAdjointW C t₀ ψ₀ g := by
  have hG' := fun r' => s55m_limit_G hB hF hFg r'
  have hG : ∀ r', ContDiff ℝ 4 (g r') ∧ ∀ j ≤ 4, ∀ x, ‖iteratedFDeriv ℝ j (g r') x‖ ≤ B :=
    fun r' => ⟨(hG' r').1, (hG' r').2.1⟩
  have hcg := ulw_cont_gen hU hB hG hgr
  have hincl : Continuous fun p : Set.Icc (0 : ℝ) t₀ × Euc d =>
      ((⟨p.1.1, p.1.2.1, p.1.2.2.trans ht₀.2⟩ : Set.Icc (0 : ℝ) T), p.2) :=
    ((continuous_subtype_val.comp continuous_fst).subtype_mk _).prodMk continuous_snd
  have hcL : ∀ x, ContinuousOn (fun τ => generatorW C τ (g τ) x) (Set.Icc (0 : ℝ) T) := by
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
    have hI : ∀ r'' ∈ Set.Icc (0 : ℝ) r₂, g r'' x = g r₂ x - ∫ τ in r₂..r'', generatorW C τ (g τ) x := by
      intro r'' hr''
      have := ulw_limit_ftc hU hB ht₀ hF hFg hG' hftc hr''.1 hr''.2 hr2.2 x
      rw [intervalIntegral.integral_symm]; linarith
    have hcont : ContinuousOn (fun τ => generatorW C τ (g τ) x) (Set.Icc (0 : ℝ) T) := hcL x
    have hrT : r ∈ Set.Ioo (0 : ℝ) T := ⟨hr.1, hr.2.trans_le hT⟩
    have hd : HasDerivAt (fun r'' => ∫ τ in r₂..r'', generatorW C τ (g τ) x)
        (generatorW C r (g r) x) r := by
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
    have := (hU.bound r hrT B (g r) hB (hG r).1 (hG r).2).2 0 (by norm_num) x
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this

/-! ### Compactness -/

/-- **Compactness of classical adjoint solutions.**  `u n` are classical adjoint solutions of `C` on `[0,t]` with terminal
data `ψ n`, uniformly bounded in `C^5` (bound `B`), `ψ n → φ` pointwise.  Then a subsequence converges pointwise on
`[0,t] × ℝ^d` to a classical adjoint solution with terminal datum `φ`, which is `C^4` with the same bounds. -/
theorem ulw_compact {C : WholeCoeff d} {T K : ℝ} (hU : UlwGenHyp C T K) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T)
    {B : ℝ} (hB0 : 0 ≤ B) {φ : Euc d → ℝ} {ψ : ℕ → Euc d → ℝ} {u : ℕ → ℝ → Euc d → ℝ}
    (hcl : ∀ n, IsClassicalAdjointW C t (ψ n) (u n))
    (hsl : ∀ n, ∀ r ∈ Set.Icc (0 : ℝ) t, ContDiff ℝ 5 (u n r) ∧
      ∀ j ≤ 5, ∀ y, ‖iteratedFDeriv ℝ j (u n r) y‖ ≤ B)
    (hψ : ∀ x, Tendsto (fun n => ψ n x) atTop (𝓝 (φ x))) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∃ g : ℝ → Euc d → ℝ, IsClassicalAdjointW C t φ g ∧
      (∀ r ∈ Set.Icc (0 : ℝ) t, ∀ x, Tendsto (fun i => u (ns i) r x) atTop (𝓝 (g r x))) ∧
      ∀ r ∈ Set.Icc (0 : ℝ) t, ContDiff ℝ 4 (g r) ∧ ∀ j ≤ 4, ∀ x, ‖iteratedFDeriv ℝ j (g r) x‖ ≤ B := by
  have hgl : ∀ n, ∀ τ ∈ Set.Icc (0 : ℝ) t, ∀ y, |generatorW C τ (u n τ) y| ≤ B * K * (1 + ‖y‖) := by
    intro n τ hτ y
    have hτT : τ ∈ Set.Icc (0 : ℝ) T := ⟨hτ.1, hτ.2.trans ht.2⟩
    obtain ⟨h1, h2⟩ := hsl n τ hτ
    have := (hU.bound τ hτT B (u n τ) hB0 (h1.of_le (by norm_num)) (fun j hj => h2 j (by omega))).2 0
      (by norm_num) y
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  set cl : ℝ → ℝ := fun r' => max 0 (min r' t) with hcl_def
  have hclmem : ∀ r', cl r' ∈ Set.Icc (0 : ℝ) t := fun r' =>
    ⟨le_max_left _ _, max_le ht.1 (min_le_right _ _)⟩
  set F : ℕ → ℝ → Euc d → ℝ := fun n r' => u n (cl r') with hFdef
  set L : ℝ := max B (B * K) with hL
  have hL0 : 0 ≤ L := le_max_of_le_left hB0
  have hFb : ∀ n r' y, |F n r' y| ≤ B := by
    intro n r' y
    have := (hsl n _ (hclmem r')).2 0 (by norm_num) y
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hFr : ∀ n r' r'' y, |F n r' y - F n r'' y| ≤ L * (1 + ‖y‖) * |r' - r''| := by
    have key : ∀ n r' r'' y, r' ≤ r'' → |F n r' y - F n r'' y| ≤ L * (1 + ‖y‖) * |r' - r''| := by
      intro n r' r'' y hle
      have hcle : cl r' ≤ cl r'' := max_le_max le_rfl (min_le_min_right _ hle)
      have h1 := s55m_lip_r (hcl n) (BL := B * K) (hgl n) (hclmem r').1 hcle (hclmem r'').2 y
      have h2 := s55m_clip_le t r' r'' hle
      rw [abs_of_nonpos (sub_nonpos.2 hle), neg_sub]
      refine h1.trans ?_
      have : 0 ≤ B * K * (1 + ‖y‖) := by
        have := hU.K0
        positivity
      calc B * K * (1 + ‖y‖) * (cl r'' - cl r') ≤ B * K * (1 + ‖y‖) * (r'' - r') :=
            mul_le_mul_of_nonneg_left h2 this
        _ ≤ L * (1 + ‖y‖) * (r'' - r') := by
            have h3 : B * K ≤ L := le_max_right _ _
            have h4 : 0 ≤ r'' - r' := sub_nonneg.2 hle
            gcongr
    intro n r' r'' y
    rcases le_total r' r'' with h | h
    · exact key n r' r'' y h
    · rw [abs_sub_comm (F n r' y), abs_sub_comm r' r'']; exact key n r'' r' y h
  have hFx : ∀ n r' y y', |F n r' y - F n r' y'| ≤ L * ‖y - y'‖ := by
    intro n r' y y'
    have hs := hsl n _ (hclmem r')
    refine (s55m_lip_x (u := F n r') (B := B) (hs.1.differentiable (by norm_num)) (fun z => ?_) y y').trans ?_
    · have := hs.2 1 (by norm_num) z
      rwa [norm_iteratedFDeriv_one] at this
    · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  obtain ⟨ns, hns, g, hpt, hgr, -, -⟩ := s55m_ex F hL0 hFb hFr hFx
  set F' : ℕ → ℝ → Euc d → ℝ := fun i => F (ns i) with hF'
  have hF'b : ∀ i r', ContDiff ℝ 5 (F' i r') ∧ ∀ j ≤ 5, ∀ y, ‖iteratedFDeriv ℝ j (F' i r') y‖ ≤ B :=
    fun i r' => hsl (ns i) _ (hclmem r')
  have hftc : ∀ r₁ r₂ y, 0 ≤ r₁ → r₁ ≤ r₂ → r₂ < t → ∀ᶠ i in atTop,
      F' i r₁ y - F' i r₂ y = ∫ τ in r₁..r₂, generatorW C τ (F' i τ) y ∧
        ContinuousOn (fun τ => generatorW C τ (F' i τ) y) (Set.Icc r₁ r₂) := by
    intro r₁ r₂ y h1 h12 h2
    refine Eventually.of_forall fun i => ?_
    have hi' : r₂ ≤ t := h2.le
    have hcl_id : ∀ τ ∈ Set.Icc r₁ r₂, cl τ = τ := by
      intro τ hτ
      show max 0 (min τ t) = τ
      rw [min_eq_left (hτ.2.trans hi'), max_eq_right (h1.trans hτ.1)]
    have hFeq : ∀ τ ∈ Set.Icc r₁ r₂, F' i τ = u (ns i) τ := fun τ hτ => by
      show u (ns i) (cl τ) = _
      rw [hcl_id τ hτ]
    refine ⟨?_, ?_⟩
    · rw [hFeq r₁ ⟨le_rfl, h12⟩, hFeq r₂ ⟨h12, le_rfl⟩, s55m_ftc (hcl (ns i)) h1 h12 hi' y]
      refine intervalIntegral.integral_congr fun τ hτ => ?_
      rw [Set.uIcc_of_le h12] at hτ
      simp only [hFeq τ hτ]
    · refine ((s55m_contL (hcl (ns i)) y).mono (Set.Icc_subset_Icc h1 hi')).congr fun τ hτ => ?_
      simp only [hFeq τ hτ]
  have hterm : g t = φ := by
    funext y
    have h1 : Tendsto (fun i => F' i t y) atTop (𝓝 (g t y)) := hpt t y
    have h2 : Tendsto (fun i => F' i t y) atTop (𝓝 (φ y)) := by
      have e : ∀ i, F' i t y = ψ (ns i) y := fun i => by
        show u (ns i) (cl t) y = _
        have : cl t = t := by
          show max 0 (min t t) = t
          rw [min_self, max_eq_right ht.1]
        rw [this, (hcl (ns i)).terminal]
      simp only [e]
      exact (hψ y).comp hns.tendsto_atTop
    exact tendsto_nhds_unique h1 h2
  have hcl' : IsClassicalAdjointW C t φ g := ulw_limit hU hB0 ht (F := F') hF'b hpt hgr hftc hterm
  refine ⟨ns, hns, g, hcl', fun r hr x => ?_, fun r hr => ?_⟩
  · have hrle : ∀ i, F (ns i) r x = u (ns i) r x := fun i => by
      show u (ns i) (cl r) x = _
      have : cl r = r := by
        show max 0 (min r t) = r
        rw [min_eq_left hr.2, max_eq_right hr.1]
      rw [this]
    exact (hpt r x).congr hrle
  · have hG1 := s55m_limit_G hB0 hF'b hpt r
    exact ⟨hG1.1, hG1.2.1⟩

/-! ### The stationary Schwartz coefficient -/

/-- A Schwartz function has finite weighted sup norms of every order, for every weight exponent `L ≥ 0`. -/
theorem ulw_schwartz_wsup (ψ : SchwartzMap (Euc d) ℝ) (n : ℕ) {L : ℝ} (_hL : 0 ≤ L) :
    ContDiff ℝ n ⇑ψ ∧ ∃ Λ : ℝ, weightedSupE n L ⇑ψ ≤ ENNReal.ofReal Λ := by
  have hr := HRS.MS.Ul.ult_schwartz_rapid ψ
  refine ⟨ψ.smooth n, ?_⟩
  choose C hC using fun m : ℕ => hr.2 m ⌈L⌉₊
  refine ⟨∑ m ∈ Finset.range (n + 1), |C m|, ?_⟩
  unfold weightedSupE derivSupE
  refine iSup_le fun j => iSup_le fun i => iSup_le fun x => ?_
  apply ENNReal.ofReal_le_ofReal
  have hjb1 : 1 ≤ jbracket x := HRS.MS.Adj.ad1_one_le_jb x
  have hjb2 : jbracket x ≤ 1 + ‖x‖ := by
    unfold jbracket
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [norm_nonneg x]
  have h1 : jbracket x ^ L ≤ (1 + ‖x‖) ^ ⌈L⌉₊ := by
    calc jbracket x ^ L ≤ jbracket x ^ ((⌈L⌉₊ : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hjb1 (Nat.le_ceil L)
      _ = jbracket x ^ ⌈L⌉₊ := Real.rpow_natCast _ _
      _ ≤ (1 + ‖x‖) ^ ⌈L⌉₊ := pow_le_pow_left₀ (by linarith) hjb2 _
  have h2 : |partialDeriv i ⇑ψ x| ≤ ‖iteratedFDeriv ℝ (j : ℕ) ⇑ψ x‖ := by
    have := (iteratedFDeriv ℝ (j : ℕ) ⇑ψ x).le_opNorm (fun l => EuclideanSpace.single (i l) 1)
    simpa [partialDeriv, EuclideanSpace.norm_single] using this
  have h3 := hC (j : ℕ) x
  have hj : (j : ℕ) ∈ Finset.range (n + 1) := Finset.mem_range.2 (by omega)
  have h4 : |C (j : ℕ)| ≤ ∑ m ∈ Finset.range (n + 1), |C m| :=
    Finset.single_le_sum (f := fun m => |C m|) (fun _ _ => abs_nonneg _) hj
  calc jbracket x ^ L * |partialDeriv i ⇑ψ x|
      ≤ (1 + ‖x‖) ^ ⌈L⌉₊ * ‖iteratedFDeriv ℝ (j : ℕ) ⇑ψ x‖ :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ ≤ C (j : ℕ) := h3
    _ ≤ |C (j : ℕ)| := le_abs_self _
    _ ≤ _ := h4

/-- `UlwGenHyp` for the coefficient of the stationary path of a Schwartz density. -/
theorem ulw_genHyp (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (M Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q.IsSymm) (c₀ : Euc d) {ν : ℝ} (hν : 0 ≤ ν) {ρ : Euc d → ℝ}
    (hρ : ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = ρ) (T : ℝ) :
    ∃ K : ℝ, UlwGenHyp ((⟨s, M, quadV Q c₀, ν⟩ : WholeDyn d).coeff (fun _ => ρ)) T K := by
  obtain ⟨ψ, rfl⟩ := hρ
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hdL : (d : ℝ) + 3 ≤ (d : ℝ) + 3 := le_rfl
  obtain ⟨hcd3, Λ0, hw⟩ := ulw_schwartz_wsup ψ 3 (L := (d : ℝ) + 3) (by linarith)
  set Λ3 : ℝ := (∑ j ∈ Finset.range 4, (d : ℝ) ^ j + 1) * max Λ0 0 with hΛ3
  have hreg3 := s55_regular_slice (n := 3) le_rfl hdL hcd3 hw
  set A : ℝ := (d : ℝ) ^ 3 * max Λ3 0 * 2 ^ ((d : ℝ) + 3) with hAdef
  have hA : 0 ≤ A := by positivity
  have hdec : RgDecay 3 (fun _ => A) ⇑ψ :=
    rg_rho_decay hd (r := 3) (Λ := max Λ3 0) hreg3.1 hreg3.2.1
      (by have := u4_cbNorm_nonneg 3 ⇑ψ; linarith [hreg3.2.2, le_max_left Λ3 0, hΛ3])
  have hMB0 : 0 ≤ ∑ i, ∑ j, |M i j| := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  obtain ⟨ΛV, G₀, hV⟩ := s55f_vhyp_quadV hQ c₀ 2
  have hV' : VHypRd (1 + 1) (max ΛV 0) (max G₀ 0) (quadV Q c₀) :=
    rg_VHyp_mono hV (by norm_num) (le_max_left _ _) (le_max_left _ _)
  refine ⟨rgK d s (∑ i, ∑ j, |M i j|) (max ΛV 0) (max G₀ 0) ν A 1,
    ⟨rgK_nonneg hs0 hMB0 (le_max_right _ _) (le_max_right _ _) hν hA 1, fun τ hτ B u hB hu hub => ?_,
      fun B hB τ τ₀ hτ hτ₀ hτt u u₀ hu hu₀ h1 x h2 => ?_⟩⟩
  · exact rg_gen_core hd hs0 hsd (k := 1) le_rfl hMB0 (le_max_right _ _) (le_max_right _ _) hA hB
      (D := ⟨s, M, quadV Q c₀, ν⟩) rfl (s55f_matBound _) hV' hν le_rfl (ρ := fun _ => ⇑ψ) (τ := τ) hdec
      (by norm_num; exact hu) (fun n hn x => hub n (by omega) x)
  · exact s55m_gen_tendsto hd (⟨s, M, quadV Q c₀, ν⟩ : WholeDyn d) hs0 hsd (s55f_matBound _) hMB0 hA hB
      (T := T) (ρ := fun _ => ⇑ψ) (fun _ _ => hdec) (fun y => continuousOn_const) hτ hτ₀ hτt hu hu₀ h1 x h2

/-- `CoeffHypRd` for the stationary path of a Schwartz probability density. -/
theorem ulw_coeffHyp (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) {ρ : Euc d → ℝ}
    (hρd : HRS.Whole.IsProbDensity ρ) (hρ : ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = ρ) (T : ℝ) :
    ∃ Λ : ℝ, CoeffHypRd s m Λ T (fun _ => ρ) := by
  obtain ⟨ψ, rfl⟩ := hρ
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  obtain ⟨hcd, Λ0, hw⟩ := ulw_schwartz_wsup ψ (m + 3) (L := (d : ℝ) + 3) (by linarith)
  have hreg := s55f_regular_slice (n := m + 3) (m + 3) le_rfl (le_refl _) hcd hw
  obtain ⟨-, -, -, hbdd, -⟩ := HRS.MS.Ul.tail_conv hd hs0 hsd ψ
  obtain ⟨Bf, hBf⟩ := hbdd 0
  set Λr : ℝ := (∑ j ∈ Finset.range (m + 3 + 1), (d : ℝ) ^ j + 1) * max Λ0 0 with hΛr
  refine ⟨max Λr (|(rieszConst d s)⁻¹| * Bf), ⟨fun _ _ => hρd, ⟨fun t ht => ?_, fun hs t ht x => ?_⟩, ?_⟩⟩
  · exact ⟨hreg.1, hreg.2.1, hreg.2.2.trans (le_max_left _ _)⟩
  · unfold fracForceRd
    rw [norm_smul, Real.norm_eq_abs]
    refine le_trans ?_ (le_max_right _ _)
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    simpa [norm_iteratedFDeriv_zero] using hBf x
  · intro ψ' _ _
    exact continuousOn_const

end HRS.MS.UlW
