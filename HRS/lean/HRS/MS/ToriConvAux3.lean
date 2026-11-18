import HRS.MS.ToriConvAux2

/-!
# MS-TORI-DRIFTCONV, helper file 3: convergence of all derivatives, by induction on the order

`tcv_main n`: under the level hypothesis `tcv_Lvl n gL g`, the whole-space operator `T^E g` is `C^n` and
`D^n (T^{Q_L} g_L) → D^n (T^E g)` locally uniformly.  The differentiability of `T^E g` is obtained from the locally
uniform limit `T^{Q_L} (D g_L) → T^E (D g)` (`hasFDerivAt_of_tendstoUniformlyOnFilter`), the induction runs over
all Banach targets `W` (`W' = E →L W`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ToriConv

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.ToriCoefA HRS.MS.ToriCoefB

variable {d : ℕ}

/-- Uniformly small tails of a family of nonnegative functions (cube) and of its limit (whole space). -/
def tcv_Tail (d : ℕ) (NL : ℝ → Euc d → ℝ) (N : Euc d → ℝ) : Prop :=
  ∀ K : Set (Euc d), IsCompact K → ∀ ε : ℝ, 0 < ε → ∃ R₀ : ℝ, ∀ R : ℝ, R₀ ≤ R →
    ∃ L₂ : ℝ, ∀ L : ℝ, L₂ ≤ L → ∀ x ∈ K,
      (∫ z in tcb_Q d L ∩ {z : Euc d | R < ‖z‖}, NL L (x - z)) ≤ ε ∧
      ∫ z in {z : Euc d | R < ‖z‖}, N (x - z) ≤ ε

/-- Locally uniform convergence in the `∀ K ∀ ε ∃ L₀` form. -/
def tcv_LocUnif {W : Type} [NormedAddCommGroup W] (d : ℕ) (hL : ℝ → Euc d → W) (h : Euc d → W) : Prop :=
  ∀ K : Set (Euc d), IsCompact K → ∀ η : ℝ, 0 < η → ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
    ∀ y ∈ K, ‖hL L y - h y‖ ≤ η

/-- The level-`n` hypothesis. -/
def tcv_Lvl (d : ℕ) (n : ℕ) {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (gL : ℝ → Euc d → W) (g : Euc d → W) : Prop :=
  ∃ L₁ Bd : ℝ, 1 ≤ L₁ ∧
    (∀ L : ℝ, L₁ ≤ L → ContDiff ℝ ((n + 2 : ℕ) : WithTop ℕ∞) (gL L)) ∧
    ContDiff ℝ ((n + 2 : ℕ) : WithTop ℕ∞) g ∧
    (∀ L : ℝ, L₁ ≤ L → ∀ i ≤ n + 2, ∀ y, ‖iteratedFDeriv ℝ i (gL L) y‖ ≤ Bd) ∧
    (∀ i ≤ n + 2, ∀ y, ‖iteratedFDeriv ℝ i g y‖ ≤ Bd) ∧
    (∀ i ≤ n, Integrable (fun y => ‖iteratedFDeriv ℝ i g y‖)) ∧
    (∀ i ≤ n, tcv_LocUnif d (fun L => iteratedFDeriv ℝ i (gL L)) (iteratedFDeriv ℝ i g)) ∧
    (∀ i ≤ n, tcv_Tail d (fun L y => ‖iteratedFDeriv ℝ i (gL L) y‖) (fun y => ‖iteratedFDeriv ℝ i g y‖))

theorem tcv_iter_fderiv_sub_norm {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f g : Euc d → W) (n : ℕ) (x : Euc d) :
    ‖iteratedFDeriv ℝ n (fderiv ℝ f) x - iteratedFDeriv ℝ n (fderiv ℝ g) x‖ =
      ‖iteratedFDeriv ℝ (n + 1) f x - iteratedFDeriv ℝ (n + 1) g x‖ := by
  rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right]
  simp only [Function.comp_apply]
  rw [← (continuousMultilinearCurryRightEquiv' ℝ n (Euc d) W).symm.map_sub,
    LinearIsometryEquiv.norm_map]

theorem tcv_iter_zero_sub_norm {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f g : Euc d → W) (x : Euc d) :
    ‖iteratedFDeriv ℝ 0 f x - iteratedFDeriv ℝ 0 g x‖ = ‖f x - g x‖ := by
  rw [iteratedFDeriv_zero_eq_comp, iteratedFDeriv_zero_eq_comp]
  simp only [Function.comp_apply]
  rw [← (continuousMultilinearCurryFin0 ℝ (Euc d) W).symm.map_sub, LinearIsometryEquiv.norm_map]

theorem tcv_cd_diff {n : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {f : Euc d → W}
    (h : ContDiff ℝ ((n + 2 : ℕ) : WithTop ℕ∞) f) : Differentiable ℝ f :=
  h.differentiable (by exact_mod_cast (by omega : n + 2 ≠ 0))

theorem tcv_Lvl_fderiv {n : ℕ} {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {gL : ℝ → Euc d → W} {g : Euc d → W} (h : tcv_Lvl d (n + 1) gL g) :
    tcv_Lvl d n (fun L => fderiv ℝ (gL L)) (fderiv ℝ g) := by
  obtain ⟨L₁, Bd, hL₁, hcd, hcdg, hb, hbg, hint, hloc, htail⟩ := h
  refine ⟨L₁, Bd, hL₁, fun L hL => ?_, ?_, fun L hL i hi y => ?_, fun i hi y => ?_, fun i hi => ?_,
    fun i hi => ?_, fun i hi => ?_⟩
  · refine (hcd L hL).fderiv_right ?_
    push_cast
    exact le_of_eq (by ring)
  · refine hcdg.fderiv_right ?_
    push_cast
    exact le_of_eq (by ring)
  · rw [norm_iteratedFDeriv_fderiv]
    exact hb L hL (i + 1) (by omega) y
  · rw [norm_iteratedFDeriv_fderiv]
    exact hbg (i + 1) (by omega) y
  · have e : (fun y => ‖iteratedFDeriv ℝ i (fderiv ℝ g) y‖) =
        fun y => ‖iteratedFDeriv ℝ (i + 1) g y‖ := by
      funext y; exact norm_iteratedFDeriv_fderiv
    rw [e]
    exact hint (i + 1) (by omega)
  · intro K hK η hη
    obtain ⟨L₀, hL₀⟩ := hloc (i + 1) (by omega) K hK η hη
    refine ⟨L₀, fun L hL y hy => ?_⟩
    rw [tcv_iter_fderiv_sub_norm]
    exact hL₀ L hL y hy
  · have e1 : (fun L (y : Euc d) => ‖iteratedFDeriv ℝ i (fderiv ℝ (gL L)) y‖) =
        fun L y => ‖iteratedFDeriv ℝ (i + 1) (gL L) y‖ := by
      funext L y; exact norm_iteratedFDeriv_fderiv
    have e2 : (fun y : Euc d => ‖iteratedFDeriv ℝ i (fderiv ℝ g) y‖) =
        fun y => ‖iteratedFDeriv ℝ (i + 1) g y‖ := by
      funext y; exact norm_iteratedFDeriv_fderiv
    rw [e1, e2]
    exact htail (i + 1) (by omega)

/-- From uniform convergence on compacts to `TendstoLocallyUniformly`. -/
theorem tcv_tlu {W : Type} [NormedAddCommGroup W] (F : ℝ → Euc d → W) (f : Euc d → W)
    (h : ∀ K : Set (Euc d), IsCompact K → ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ x ∈ K,
      ‖F L x - f x‖ ≤ ε) :
    TendstoLocallyUniformly F f atTop := by
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨L₀, hL₀⟩ := h K hK (ε / 2) (by positivity)
  filter_upwards [eventually_ge_atTop L₀] with L hL x hx
  rw [dist_eq_norm, norm_sub_rev]
  have := hL₀ L hL x hx
  linarith

/-- Order `0` convergence from the level data. -/
theorem tcv_conv0_of_lvl {s : ℝ} {kL : ℝ → Euc d → ℝ} {kE : Euc d → ℝ} {Kf Cn : ℝ} (hd : 1 ≤ d)
    (hsd : s < d) (hk : tcv_Kerns d s kL kE Kf Cn) {n : ℕ} {W : Type} [NormedAddCommGroup W]
    [NormedSpace ℝ W] [CompleteSpace W] {gL : ℝ → Euc d → W} {g : Euc d → W}
    (h : tcv_Lvl d n gL g) (K : Set (Euc d)) (hK : IsCompact K) (ε : ℝ) (hε : 0 < ε) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ x ∈ K,
      ‖tcb_T L (kL L) (gL L) x - tcv_TE kE g x‖ ≤ ε := by
  obtain ⟨L₁, Bd, hL₁, hcd, hcdg, hb, hbg, hint, hloc, htail⟩ := h
  have hb0 : ∀ L : ℝ, L₁ ≤ L → ∀ y, ‖gL L y‖ ≤ Bd := fun L hL y => by
    have := hb L hL 0 (by omega) y
    rwa [norm_iteratedFDeriv_zero] at this
  have hb1 : ∀ L : ℝ, L₁ ≤ L → ∀ y, ‖fderiv ℝ (gL L) y‖ ≤ Bd := fun L hL y => by
    have := hb L hL 1 (by omega) y
    rwa [norm_iteratedFDeriv_one] at this
  have hg0 : ∀ y, ‖g y‖ ≤ Bd := fun y => by
    have := hbg 0 (by omega) y
    rwa [norm_iteratedFDeriv_zero] at this
  have hg1 : ∀ y, ‖fderiv ℝ g y‖ ≤ Bd := fun y => by
    have := hbg 1 (by omega) y
    rwa [norm_iteratedFDeriv_one] at this
  have hgint : Integrable g := by
    have h0 := hint 0 (by omega)
    simp only [norm_iteratedFDeriv_zero] at h0
    exact (integrable_norm_iff (tcv_cd_diff hcdg).continuous.aestronglyMeasurable).1 h0
  refine tcv_conv0 hd hsd hk gL g Bd Bd L₁ (fun L hL => tcv_cd_diff (hcd L hL)) hb0 hb1
    (tcv_cd_diff hcdg) hg0 hg1 hgint ?_ ?_ K hK ε hε
  · intro K' hK' η hη
    obtain ⟨L₀, hL₀⟩ := hloc 0 (by omega) K' hK' η hη
    refine ⟨L₀, fun L hL y hy => ?_⟩
    have := hL₀ L hL y hy
    rwa [tcv_iter_zero_sub_norm] at this
  · intro K' hK' η hη
    obtain ⟨R₀, hR₀⟩ := htail 0 (by omega) K' hK' η hη
    refine ⟨R₀, fun R hR => ?_⟩
    obtain ⟨L₂, hL₂⟩ := hR₀ R hR
    refine ⟨L₂, fun L hL x hx => ?_⟩
    have := hL₂ L hL x hx
    simpa only [norm_iteratedFDeriv_zero] using this

/-- `T^{Q_L} g` is `C^n` (only differentiability of `T g` and bounds on `g` enter). -/
theorem tcv_T_contDiff {L : ℝ} {k : Euc d → ℝ} {Kf : ℝ} (hk : tcb_Kern L k Kf) (Bd : ℝ) :
    ∀ (n : ℕ) (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] (g : Euc d → W),
      ContDiff ℝ ((n + 2 : ℕ) : WithTop ℕ∞) g →
      (∀ i ≤ n + 2, ∀ y, ‖iteratedFDeriv ℝ i g y‖ ≤ Bd) →
      ContDiff ℝ (n : WithTop ℕ∞) (tcb_T L k g) := by
  intro n
  induction n with
  | zero =>
    intro W _ _ _ g hg hD
    have hg2 : ContDiff ℝ 2 g := by exact_mod_cast hg
    have h0 : ∀ y, ‖g y‖ ≤ Bd := fun y => by
      have := hD 0 (by omega) y
      rwa [norm_iteratedFDeriv_zero] at this
    have h1 : ∀ y, ‖fderiv ℝ g y‖ ≤ Bd := fun y => by
      have := hD 1 (by omega) y
      rwa [norm_iteratedFDeriv_one] at this
    have h2 : ∀ y, ‖fderiv ℝ (fderiv ℝ g) y‖ ≤ Bd := fun y => by
      rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
      exact hD 2 (by omega) y
    have hdiff := tcb_hasFDerivAt hk g hg2 Bd Bd Bd h0 h1 h2
    have : Continuous (tcb_T L k g) := continuous_iff_continuousAt.2 fun x => (hdiff x).continuousAt
    exact contDiff_zero.2 this
  | succ n ih =>
    intro W _ _ _ g hg hD
    have hg2 : ContDiff ℝ 2 g := by
      refine hg.of_le ?_
      exact_mod_cast (by omega : 2 ≤ n + 1 + 2)
    have h0 : ∀ y, ‖g y‖ ≤ Bd := fun y => by
      have := hD 0 (by omega) y
      rwa [norm_iteratedFDeriv_zero] at this
    have h1 : ∀ y, ‖fderiv ℝ g y‖ ≤ Bd := fun y => by
      have := hD 1 (by omega) y
      rwa [norm_iteratedFDeriv_one] at this
    have h2 : ∀ y, ‖fderiv ℝ (fderiv ℝ g) y‖ ≤ Bd := fun y => by
      rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
      exact hD 2 (by omega) y
    have hdiff := tcb_hasFDerivAt hk g hg2 Bd Bd Bd h0 h1 h2
    have hfd : fderiv ℝ (tcb_T L k g) = tcb_T L k (fderiv ℝ g) := funext fun x => (hdiff x).fderiv
    have hg' : ContDiff ℝ ((n + 2 : ℕ) : WithTop ℕ∞) (fderiv ℝ g) := by
      refine hg.fderiv_right ?_
      push_cast
      exact le_of_eq (by ring)
    have hD' : ∀ i ≤ n + 2, ∀ y, ‖iteratedFDeriv ℝ i (fderiv ℝ g) y‖ ≤ Bd := fun i hi y => by
      rw [norm_iteratedFDeriv_fderiv]
      exact hD (i + 1) (by omega) y
    have IH := ih (Euc d →L[ℝ] W) (fderiv ℝ g) hg' hD'
    have : ContDiff ℝ ((n : WithTop ℕ∞) + 1) (tcb_T L k g) := by
      rw [contDiff_succ_iff_fderiv]
      refine ⟨fun x => (hdiff x).differentiableAt, by simp, ?_⟩
      rw [hfd]
      exact IH
    exact_mod_cast this

theorem tcv_hasFDerivAt_lvl {L : ℝ} {k : Euc d → ℝ} {Kf : ℝ} (hk : tcb_Kern L k Kf) {n : ℕ}
    {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W] {g : Euc d → W}
    (hg : ContDiff ℝ ((n + 2 : ℕ) : WithTop ℕ∞) g) {Bd : ℝ}
    (hD : ∀ i ≤ n + 2, ∀ y, ‖iteratedFDeriv ℝ i g y‖ ≤ Bd) (x : Euc d) :
    HasFDerivAt (tcb_T L k g) (tcb_T L k (fderiv ℝ g) x) x := by
  have hg2 : ContDiff ℝ 2 g := by
    refine hg.of_le ?_
    exact_mod_cast (by omega : 2 ≤ n + 2)
  have h0 : ∀ y, ‖g y‖ ≤ Bd := fun y => by
    have := hD 0 (by omega) y
    rwa [norm_iteratedFDeriv_zero] at this
  have h1 : ∀ y, ‖fderiv ℝ g y‖ ≤ Bd := fun y => by
    have := hD 1 (by omega) y
    rwa [norm_iteratedFDeriv_one] at this
  have h2 : ∀ y, ‖fderiv ℝ (fderiv ℝ g) y‖ ≤ Bd := fun y => by
    rw [← norm_iteratedFDeriv_one, norm_iteratedFDeriv_fderiv]
    exact hD 2 (by omega) y
  exact tcb_hasFDerivAt hk g hg2 Bd Bd Bd h0 h1 h2 x

theorem tcv_pt_tendsto {W : Type} [NormedAddCommGroup W] (F : ℝ → Euc d → W) (f : Euc d → W)
    (h : ∀ K : Set (Euc d), IsCompact K → ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ x ∈ K,
      ‖F L x - f x‖ ≤ ε) (y : Euc d) : Tendsto (fun L => F L y) atTop (𝓝 (f y)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨L₀, hL₀⟩ := h {y} isCompact_singleton (ε / 2) (by positivity)
  refine ⟨L₀, fun L hL => ?_⟩
  rw [dist_eq_norm]
  have := hL₀ L hL y rfl
  linarith

theorem tcv_main {s : ℝ} {kL : ℝ → Euc d → ℝ} {kE : Euc d → ℝ} {Kf Cn : ℝ} (hd : 1 ≤ d)
    (hsd : s < d) (hk : tcv_Kerns d s kL kE Kf Cn) :
    ∀ (n : ℕ) (W : Type) [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
      (gL : ℝ → Euc d → W) (g : Euc d → W), tcv_Lvl d n gL g →
      ContDiff ℝ (n : WithTop ℕ∞) (tcv_TE kE g) ∧
      ∀ K : Set (Euc d), IsCompact K → ∀ ε : ℝ, 0 < ε → ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → ∀ x ∈ K,
        ‖iteratedFDeriv ℝ n (tcb_T L (kL L) (gL L)) x - iteratedFDeriv ℝ n (tcv_TE kE g) x‖ ≤ ε := by
  intro n
  induction n with
  | zero =>
    intro W _ _ _ gL g hlvl
    have hc0 := tcv_conv0_of_lvl hd hsd hk hlvl
    obtain ⟨L₁, Bd, hL₁, hcd, hcdg, hb, hbg, hint, hloc, htail⟩ := hlvl
    have hcontL : ∀ L : ℝ, L₁ ≤ L → Continuous (tcb_T L (kL L) (gL L)) := fun L hL =>
      continuous_iff_continuousAt.2 fun x =>
        (tcv_hasFDerivAt_lvl (hk.kern L (hL₁.trans hL)) (hcd L hL) (hb L hL) x).continuousAt
    have hcont : Continuous (tcv_TE kE g) :=
      (tcv_tlu _ _ hc0).continuous ((eventually_ge_atTop L₁).mono hcontL).frequently
    refine ⟨contDiff_zero.2 hcont, fun K hK ε hε => ?_⟩
    obtain ⟨L₀, hL₀⟩ := hc0 K hK ε hε
    refine ⟨L₀, fun L hL x hx => ?_⟩
    rw [tcv_iter_zero_sub_norm]
    exact hL₀ L hL x hx
  | succ n ih =>
    intro W _ _ _ gL g hlvl
    have hlvl' := tcv_Lvl_fderiv hlvl
    have hc0 := tcv_conv0_of_lvl hd hsd hk hlvl
    have hc1 := tcv_conv0_of_lvl hd hsd hk hlvl'
    obtain ⟨IHc, IHb⟩ := ih (Euc d →L[ℝ] W) (fun L => fderiv ℝ (gL L)) (fderiv ℝ g) hlvl'
    obtain ⟨L₁, Bd, hL₁, hcd, hcdg, hb, hbg, hint, hloc, htail⟩ := hlvl
    have hderL : ∀ L : ℝ, L₁ ≤ L → ∀ x, HasFDerivAt (tcb_T L (kL L) (gL L))
        (tcb_T L (kL L) (fderiv ℝ (gL L)) x) x := fun L hL x =>
      tcv_hasFDerivAt_lvl (hk.kern L (hL₁.trans hL)) (hcd L hL) (hb L hL) x
    have hderE : ∀ x, HasFDerivAt (tcv_TE kE g) (tcv_TE kE (fderiv ℝ g) x) x := by
      intro x
      refine hasFDerivAt_of_tendstoUniformlyOnFilter (l := atTop)
        (f := fun L => tcb_T L (kL L) (gL L)) (f' := fun L => tcb_T L (kL L) (fderiv ℝ (gL L)))
        (g := tcv_TE kE g) (g' := tcv_TE kE (fderiv ℝ g)) (x := x) ?_ ?_ ?_
      · exact tendstoLocallyUniformly_iff_filter.1 (tcv_tlu _ _ hc1) x
      · have h1 : ∀ᶠ n : ℝ × Euc d in atTop ×ˢ 𝓝 x, L₁ ≤ n.1 :=
          (eventually_ge_atTop L₁).prod_inl _
        exact h1.mono fun n hn => hderL n.1 hn n.2
      · exact Filter.Eventually.of_forall fun y => tcv_pt_tendsto _ _ hc0 y
    have hfdE : fderiv ℝ (tcv_TE kE g) = tcv_TE kE (fderiv ℝ g) := funext fun x => (hderE x).fderiv
    refine ⟨?_, fun K hK ε hε => ?_⟩
    · have : ContDiff ℝ ((n : WithTop ℕ∞) + 1) (tcv_TE kE g) := by
        rw [contDiff_succ_iff_fderiv]
        refine ⟨fun x => (hderE x).differentiableAt, by simp, ?_⟩
        rw [hfdE]
        exact IHc
      exact_mod_cast this
    · obtain ⟨L₀, hL₀⟩ := IHb K hK ε hε
      refine ⟨max L₀ L₁, fun L hL x hx => ?_⟩
      have hLL1 : L₁ ≤ L := (le_max_right _ _).trans hL
      have hfdL : fderiv ℝ (tcb_T L (kL L) (gL L)) = tcb_T L (kL L) (fderiv ℝ (gL L)) :=
        funext fun y => (hderL L hLL1 y).fderiv
      rw [← tcv_iter_fderiv_sub_norm, hfdL, hfdE]
      exact hL₀ L ((le_max_left _ _).trans hL) x hx

end HRS.MS.ToriConv
