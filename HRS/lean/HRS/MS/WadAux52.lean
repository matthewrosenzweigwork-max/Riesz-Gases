import HRS.MS.WadAux51

/-!
# S8.3, packet S8D-1, part 2: weighted `C¹` limits

`s8d_limit_C1`: if `u_n ∈ C¹` converge pointwise to `U` and the gradients satisfy the weighted Cauchy bound
`‖Du_n - Du_m‖ ≤ (e_n+e_m) c ⟨y⟩^M` (`e_n ↓ 0`), then `U` is `C¹`, `D u_n → DU` locally uniformly and
`‖DU - Du_n‖ ≤ e_n c ⟨y⟩^M`.
`s8d_decay_of_approx`: weighted uniform limits of functions with `‖h_n‖/⟨y⟩^M → 0` at infinity have the
same property.  `s8d_memCMj1`: criterion for `MemCMj M 1`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8d_limit_C1 {M c : ℝ} (hM : 0 ≤ M) (hc : 0 ≤ c) {u : ℕ → Euc d → ℝ} {U : Euc d → ℝ}
    {e : ℕ → ℝ} (he0 : ∀ n, 0 ≤ e n) (hea : Antitone e) (he : Tendsto e atTop (𝓝 0))
    (hu : ∀ n, ContDiff ℝ 1 (u n)) (hpt : ∀ x, Tendsto (fun n => u n x) atTop (𝓝 (U x)))
    (hcau : ∀ n m y, ‖fderiv ℝ (u n) y - fderiv ℝ (u m) y‖ ≤ (e n + e m) * c * jbracket y ^ M) :
    ∃ g : Euc d → Euc d →L[ℝ] ℝ, Continuous g ∧ (∀ y, HasFDerivAt U (g y) y) ∧
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

theorem s8d_decay_of_approx {M c : ℝ} {g : ℕ → Euc d → ℝ} {h : Euc d → ℝ} {e : ℕ → ℝ}
    (he0 : ∀ n, 0 ≤ e n) (he : Tendsto e atTop (𝓝 0))
    (hg : ∀ n, Tendsto (fun x => g n x / jbracket x ^ M) (cocompact (Euc d)) (𝓝 0))
    (hw : ∀ n x, |h x - g n x| ≤ e n * c * jbracket x ^ M) (hc : 0 ≤ c) :
    Tendsto (fun x => h x / jbracket x ^ M) (cocompact (Euc d)) (𝓝 0) := by
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨n, hn⟩ := (he.eventually (gt_mem_nhds (show (0 : ℝ) < ε / (2 * (c + 1)) by positivity))).exists
  have hgn := Metric.tendsto_nhds.1 (hg n) (ε / 2) (by positivity)
  filter_upwards [hgn] with x hx
  rw [Real.dist_eq, sub_zero] at hx ⊢
  have hp : 0 < jbracket x ^ M := Real.rpow_pos_of_pos (s83_jb_pos x) _
  have e1 : h x / jbracket x ^ M = g n x / jbracket x ^ M + (h x - g n x) / jbracket x ^ M := by
    rw [← add_div]; congr 1; ring
  have h4 : |(h x - g n x) / jbracket x ^ M| ≤ e n * c := by
    rw [abs_div, abs_of_pos hp, div_le_iff₀ hp]
    exact hw n x
  have h5 : e n * c < ε / 2 := by
    have := (lt_div_iff₀ (show (0 : ℝ) < 2 * (c + 1) by positivity)).1 hn
    have := he0 n
    nlinarith
  rw [e1]
  calc |g n x / jbracket x ^ M + (h x - g n x) / jbracket x ^ M|
      ≤ |g n x / jbracket x ^ M| + |(h x - g n x) / jbracket x ^ M| := abs_add_le _ _
    _ < ε := by linarith

/-- `MemCMj M 1` from `C¹`, `C_M` and weighted decay of the gradient. -/
theorem s8d_memCMj1 {M : ℝ} {f : Euc d → ℝ} (h1 : ContDiff ℝ 1 f) (h0 : MemCM M f)
    (hD : Tendsto (fun x => ‖fderiv ℝ f x‖ / jbracket x ^ M) (cocompact (Euc d)) (𝓝 0)) :
    MemCMj M 1 f := by
  refine ⟨h1, fun i hi idx => ?_⟩
  have hi' : i = 0 ∨ i = 1 := by omega
  rcases hi' with rfl | rfl
  · have := h0.2
    refine this.congr fun x => ?_
    simp [partialDeriv, iteratedFDeriv_zero_apply]
  · refine squeeze_zero_norm (fun x => ?_) hD
    have hp : 0 < jbracket x ^ M := Real.rpow_pos_of_pos (s83_jb_pos x) _
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hp]
    refine div_le_div_of_nonneg_right ?_ hp.le
    simp only [partialDeriv, iteratedFDeriv_one_apply]
    have hv : ‖(EuclideanSpace.single (idx 0) (1 : ℝ) : Euc d)‖ = 1 := by simp
    have := (fderiv ℝ f x).le_opNorm (EuclideanSpace.single (idx 0) (1 : ℝ) : Euc d)
    rw [hv, mul_one, Real.norm_eq_abs] at this
    exact this

end HRS.MS.Wad
