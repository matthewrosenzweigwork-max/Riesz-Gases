import HRS.MS.WadAux108

/-!
# S8.3, packet S8F-9: closure of weighted `C^N` sequences (vector valued)

`s8f_limit_C0`, `s8f_limit_C1`: the order-0 and order-1 closure lemmas (`s8d_limit_C1` for functions with values in a complete normed space).
`s8f_closure`: if `u_n ∈ C^N` converge pointwise to `U` and `‖D^i u_n - D^i u_m‖ ≤ (e_n + e_m) c ⟨y⟩^M` for all `i ≤ N`, then `U ∈ C^N` and
`‖D^i U - D^i u_n‖ ≤ e_n c ⟨y⟩^M` (the order-`N` analogue of `s8d_limit_C1`, by induction on `N` applied to the derivatives).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8f_norm_iter0_sub {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (g1 g2 : Euc d → F) (y : Euc d) :
    ‖iteratedFDeriv ℝ 0 g1 y - iteratedFDeriv ℝ 0 g2 y‖ = ‖g1 y - g2 y‖ := by
  rw [iteratedFDeriv_zero_eq_comp, iteratedFDeriv_zero_eq_comp]
  simp only [Function.comp_apply]
  rw [← dist_eq_norm, ← dist_eq_norm, LinearIsometryEquiv.dist_map]

theorem s8f_norm_iter_sub' {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (k : ℕ) (g1 g2 : Euc d → F)
    (y : Euc d) :
    ‖iteratedFDeriv ℝ k (fderiv ℝ g1) y - iteratedFDeriv ℝ k (fderiv ℝ g2) y‖ =
      ‖iteratedFDeriv ℝ (k + 1) g1 y - iteratedFDeriv ℝ (k + 1) g2 y‖ := by
  rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right]
  simp only [Function.comp_apply]
  rw [← dist_eq_norm, ← dist_eq_norm, LinearIsometryEquiv.dist_map]

theorem s8f_limit_C0 {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {M c : ℝ} (hM : 0 ≤ M) (hc : 0 ≤ c)
    {u : ℕ → Euc d → F} {U : Euc d → F} {e : ℕ → ℝ} (he0 : ∀ n, 0 ≤ e n) (he : Tendsto e atTop (𝓝 0))
    (hu : ∀ n, Continuous (u n)) (hpt : ∀ x, Tendsto (fun n => u n x) atTop (𝓝 (U x)))
    (hcau : ∀ n m y, ‖u n y - u m y‖ ≤ (e n + e m) * c * jbracket y ^ M) :
    Continuous U ∧ ∀ n y, ‖U y - u n y‖ ≤ e n * c * jbracket y ^ M := by
  have hbd : ∀ n y, ‖U y - u n y‖ ≤ e n * c * jbracket y ^ M := fun n y => by
    have hl : Tendsto (fun m => ‖u m y - u n y‖) atTop (𝓝 ‖U y - u n y‖) := ((hpt y).sub_const _).norm
    have hr : Tendsto (fun m => (e m + e n) * c * jbracket y ^ M) atTop
        (𝓝 ((0 + e n) * c * jbracket y ^ M)) := ((he.add_const _).mul_const _).mul_const _
    have := le_of_tendsto_of_tendsto' hl hr (fun m => hcau m n y)
    simpa using this
  refine ⟨?_, hbd⟩
  have hlu : TendstoLocallyUniformly u U atTop := by
    rw [Metric.tendstoLocallyUniformly_iff]
    intro ε hε x₀
    set Λ : ℝ := (3 * jbracket x₀) ^ M with hΛ
    have hΛ0 : 0 ≤ Λ := Real.rpow_nonneg (by have := s83_jb_pos x₀; positivity) _
    refine ⟨Metric.ball x₀ 1, Metric.ball_mem_nhds x₀ one_pos, ?_⟩
    have hev := he.eventually (gt_mem_nhds (show (0 : ℝ) < ε / (c * Λ + 1) by positivity))
    filter_upwards [hev] with n hn y hy
    rw [Metric.mem_ball, dist_eq_norm] at hy
    have hjy : jbracket y ^ M ≤ Λ :=
      Real.rpow_le_rpow (s83_jb_pos y).le (s83_jb_le_three hy) hM
    rw [dist_eq_norm]
    refine (hbd n y).trans_lt ?_
    have h3 : e n * (c * Λ) < ε := by
      have := (lt_div_iff₀ (show (0 : ℝ) < c * Λ + 1 by positivity)).1 hn
      nlinarith [he0 n, mul_nonneg hc hΛ0]
    calc e n * c * jbracket y ^ M = e n * (c * jbracket y ^ M) := by ring
      _ ≤ e n * (c * Λ) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hjy hc) (he0 n)
      _ < ε := h3
  exact hlu.continuous (Filter.Eventually.of_forall hu).frequently

theorem s8f_limit_C1 {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {M c : ℝ}
    (hM : 0 ≤ M) (hc : 0 ≤ c) {u : ℕ → Euc d → F} {U : Euc d → F}
    {e : ℕ → ℝ} (he0 : ∀ n, 0 ≤ e n) (hea : Antitone e) (he : Tendsto e atTop (𝓝 0))
    (hu : ∀ n, ContDiff ℝ 1 (u n)) (hpt : ∀ x, Tendsto (fun n => u n x) atTop (𝓝 (U x)))
    (hcau : ∀ n m y, ‖fderiv ℝ (u n) y - fderiv ℝ (u m) y‖ ≤ (e n + e m) * c * jbracket y ^ M) :
    ∃ g : Euc d → Euc d →L[ℝ] F, Continuous g ∧ (∀ y, HasFDerivAt U (g y) y) ∧
      (∀ y, Tendsto (fun n => fderiv ℝ (u n) y) atTop (𝓝 (g y))) ∧
      ∀ n y, ‖g y - fderiv ℝ (u n) y‖ ≤ e n * c * jbracket y ^ M := by
  have hJ0 : ∀ y : Euc d, 0 ≤ c * jbracket y ^ M := fun y =>
    mul_nonneg hc (Real.rpow_nonneg (s83_jb_pos y).le _)
  have hcs : ∀ y, CauchySeq (fun n => fderiv ℝ (u n) y) := fun y => by
    refine cauchySeq_of_le_tendsto_0 (fun N => 2 * e N * (c * jbracket y ^ M)) (fun n m N hn hm => ?_) ?_
    · rw [dist_eq_norm]
      refine (hcau n m y).trans ?_
      have h1 := hea hn
      have h2 := hea hm
      have := hJ0 y
      nlinarith [mul_nonneg (sub_nonneg.2 h1) this, mul_nonneg (sub_nonneg.2 h2) this]
    · simpa using (he.const_mul 2).mul_const (c * jbracket y ^ M)
  choose g hg using fun y => cauchySeq_tendsto_of_complete (hcs y)
  have hbd : ∀ n y, ‖g y - fderiv ℝ (u n) y‖ ≤ e n * c * jbracket y ^ M := fun n y => by
    have hl : Tendsto (fun m => ‖fderiv ℝ (u m) y - fderiv ℝ (u n) y‖) atTop
        (𝓝 ‖g y - fderiv ℝ (u n) y‖) := ((hg y).sub_const _).norm
    have hr : Tendsto (fun m => (e m + e n) * c * jbracket y ^ M) atTop
        (𝓝 ((0 + e n) * c * jbracket y ^ M)) := ((he.add_const _).mul_const _).mul_const _
    have := le_of_tendsto_of_tendsto' hl hr (fun m => hcau m n y)
    simpa using this
  have hlu : TendstoLocallyUniformly (fun n => fderiv ℝ (u n)) g atTop := by
    rw [Metric.tendstoLocallyUniformly_iff]
    intro ε hε x₀
    set Λ : ℝ := (3 * jbracket x₀) ^ M with hΛ
    have hΛ0 : 0 ≤ Λ := Real.rpow_nonneg (by have := s83_jb_pos x₀; positivity) _
    refine ⟨Metric.ball x₀ 1, Metric.ball_mem_nhds x₀ one_pos, ?_⟩
    have hev := he.eventually (gt_mem_nhds (show (0 : ℝ) < ε / (c * Λ + 1) by positivity))
    filter_upwards [hev] with n hn y hy
    rw [Metric.mem_ball, dist_eq_norm] at hy
    have hjy : jbracket y ^ M ≤ Λ :=
      Real.rpow_le_rpow (s83_jb_pos y).le (s83_jb_le_three hy) hM
    rw [dist_eq_norm]
    refine (hbd n y).trans_lt ?_
    have h3 : e n * (c * Λ) < ε := by
      have := (lt_div_iff₀ (show (0 : ℝ) < c * Λ + 1 by positivity)).1 hn
      nlinarith [he0 n, mul_nonneg hc hΛ0]
    calc e n * c * jbracket y ^ M = e n * (c * jbracket y ^ M) := by ring
      _ ≤ e n * (c * Λ) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hjy hc) (he0 n)
      _ < ε := h3
  have hcont : Continuous g := hlu.continuous (Filter.Eventually.of_forall fun n =>
    (hu n).continuous_fderiv one_ne_zero).frequently
  refine ⟨g, hcont, fun y => ?_, hg, hbd⟩
  exact hasFDerivAt_of_tendstoLocallyUniformlyOn isOpen_univ (tendstoLocallyUniformlyOn_univ.2 hlu)
    (fun n x _ => (((hu n).differentiable one_ne_zero) x).hasFDerivAt) (fun x _ => hpt x) (Set.mem_univ y)

theorem s8f_closure {M c : ℝ} (hM : 0 ≤ M) (hc : 0 ≤ c) {e : ℕ → ℝ} (he0 : ∀ n, 0 ≤ e n)
    (hea : Antitone e) (he : Tendsto e atTop (𝓝 0)) : ∀ (N : ℕ) {F : Type} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {u : ℕ → Euc d → F} {U : Euc d → F},
    (∀ n, ContDiff ℝ N (u n)) → (∀ x, Tendsto (fun n => u n x) atTop (𝓝 (U x))) →
    (∀ n m, ∀ i ≤ N, ∀ y, ‖iteratedFDeriv ℝ i (u n) y - iteratedFDeriv ℝ i (u m) y‖ ≤
      (e n + e m) * c * jbracket y ^ M) →
    ContDiff ℝ N U ∧ ∀ n, ∀ i ≤ N, ∀ y,
      ‖iteratedFDeriv ℝ i U y - iteratedFDeriv ℝ i (u n) y‖ ≤ e n * c * jbracket y ^ M := by
  intro N
  induction N with
  | zero =>
    intro F _ _ _ u U hu hpt hcau
    have hcau0 : ∀ n m y, ‖u n y - u m y‖ ≤ (e n + e m) * c * jbracket y ^ M := fun n m y => by
      have := hcau n m 0 le_rfl y
      rwa [s8f_norm_iter0_sub] at this
    obtain ⟨hcont, hbd⟩ := s8f_limit_C0 hM hc he0 he (fun n => (hu n).continuous) hpt hcau0
    refine ⟨contDiff_zero.2 hcont, fun n i hi y => ?_⟩
    have : i = 0 := by omega
    subst this
    rw [s8f_norm_iter0_sub]
    exact hbd n y
  | succ N ih =>
    intro F _ _ _ u U hu hpt hcau
    have hu1 : ∀ n, ContDiff ℝ 1 (u n) := fun n => (hu n).of_le (by norm_cast; omega)
    have hcau1 : ∀ n m y, ‖fderiv ℝ (u n) y - fderiv ℝ (u m) y‖ ≤ (e n + e m) * c * jbracket y ^ M :=
      fun n m y => by
        have := hcau n m 1 (by omega) y
        rw [← s8f_norm_iter_sub' 0, s8f_norm_iter0_sub] at this
        exact this
    obtain ⟨g, hgc, hgd, hgl, hgb⟩ := s8f_limit_C1 hM hc he0 hea he hu1 hpt hcau1
    have hfd : fderiv ℝ U = g := funext fun y => (hgd y).fderiv
    have hUd : Differentiable ℝ U := fun y => (hgd y).differentiableAt
    -- the derivatives
    have hv : ∀ n, ContDiff ℝ N (fderiv ℝ (u n)) := fun n => (hu n).fderiv_right (by norm_cast)
    obtain ⟨hgN, hgbd⟩ := ih (F := Euc d →L[ℝ] F) (u := fun n => fderiv ℝ (u n)) (U := g) hv hgl
      (fun n m i hi y => by
        rw [s8f_norm_iter_sub']
        exact hcau n m (i + 1) (by omega) y)
    refine ⟨?_, fun n i hi y => ?_⟩
    · have h1 : ((N + 1 : ℕ) : WithTop ℕ∞) = (N : WithTop ℕ∞) + 1 := by push_cast; rfl
      rw [h1, contDiff_succ_iff_fderiv]
      exact ⟨hUd, fun h => absurd h (by simp), by rw [hfd]; exact hgN⟩
    · rcases i with _ | i
      · rw [s8f_norm_iter0_sub]
        have := hgb
        -- order zero: from the limit of the values
        have hcau0 : ∀ n m y, ‖u n y - u m y‖ ≤ (e n + e m) * c * jbracket y ^ M := fun n m y => by
          have := hcau n m 0 (by omega) y
          rwa [s8f_norm_iter0_sub] at this
        have hbd0 : ∀ n y, ‖U y - u n y‖ ≤ e n * c * jbracket y ^ M := fun n y => by
          have hl : Tendsto (fun m => ‖u m y - u n y‖) atTop (𝓝 ‖U y - u n y‖) :=
            ((hpt y).sub_const _).norm
          have hr : Tendsto (fun m => (e m + e n) * c * jbracket y ^ M) atTop
              (𝓝 ((0 + e n) * c * jbracket y ^ M)) := ((he.add_const _).mul_const _).mul_const _
          have := le_of_tendsto_of_tendsto' hl hr (fun m => hcau0 m n y)
          simpa using this
        exact hbd0 n y
      · rw [← s8f_norm_iter_sub', hfd]
        exact hgbd n i (by omega) y

end HRS.MS.Wad
