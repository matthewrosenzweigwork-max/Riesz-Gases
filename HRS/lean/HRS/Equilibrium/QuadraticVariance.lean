/-
# HRS.Equilibrium.QuadraticVariance -- Proposition 4.3 (EQ-03)

Proposition 4.3 `M:A:prop:quadratic` (main paper TeX lines 3764-3833): for a symmetric kernel `h` with
`|h(x,y)| ≤ B(1 + |x-y|^{-s})` (`B(1 + |log|x-y||)` for `s = 0`) off the diagonal,
both `ν = μ` and `ν = Q_{N,β}(μ)^{(1)}` satisfy `N Var_{Q_{N,β}(μ)}[D_N(h;ν)] ≤ C B² δ_N`
(`quadStat_variance`), and the transport kernel `h_v = (v(x) - v(y))·∇g(x-y)` of a smooth field `v`
is admissible (`quadStat_variance_transport`).

The two theorems used to live at the end of `HRS.Equilibrium.PoleCavity`; the proof needs the heat split,
the weak specification and the calibrated reference, which import that module, so they were moved here
verbatim (same names and statements), as for `HRS.Equilibrium.PoleVariance`.

## Route (source proof, TeX lines 3783-3833)

Parts (sections of this file): `QuadKernel` (envelope integrals), `QuadWeak` (resampling), `QuadRow`
(row bounds), `QuadRef` (weak-ensemble bound), `QuadChange`, `QuadCrude`, `QuadFinal`, `QuadLarge`
(assembly for large `N`), then the two target theorems.

1. Weak split `g = g_L + q - c` (`exists_split_params`, `κ ≤ 1/2`); calibrated reference
   `R_N = pinnedLaw V (β/N) N ∅` with the weak potential `V = weakPotK` (field `t_N·Ξ`, `|t_N·Ξ| ≤ 1` for
   `N ≥ N₀`), `Q_N ≤ e^{4β g_L(0)} R_N` (`riesz_Q_le_smul_RN_eventually`).
2. Omitted-diagonal identity (`quadStat_eq_row_add_rest`, `A:eq:D-diagonal`) and Wu's resampling inequality
   (`weak_resampling`): `Var_R D_N ≤ (8/N⁴) ∑_i E_R |row_i|²` (`evariance_quad_le`, `A:eq:outer-row`).
3. Disintegration of `R` over `x_i = x` (`lintegral_pinned_succ`): the row variance by pinned linear variance
   (`weak_linear_variance_symm`, `second_moment_pinned`) with the retained repulsion
   `e^{-λ q(x-y)} ≤ e^{λ C}e^{-λ e(x-y)}` (`variance_integral_le`, the radial integral `A:eq:radial`
   as the distribution-function bound `∫ min(e,K)² ≲ gFun K` of `ReferenceMarginal`).
4. Row mean (`mean_one_le`, `A:eq:row-mean`): near part by the bounded one-point densities, far part by the
   `O(1/N)` total variation of `rvh_pin_comparison` (`tv_pin_le`); level `K = N^{1/p}`, `p = pOf d s`.
5. `quad_weak_bound`: `N Var_R D_N(h;π^R) ≤ C B² δ_N` (`A:eq:reference-quadratic`; the power comparison
   `N^{2/p} ≤ N gFun N`, `rpow_two_div_le`).
6. Change of the centering measure to `ν ∈ {μ, π_N}` (`evariance_quad_change`, `change_term_le`): a
   one-coordinate statistic with test `∫ h(·,y) d(ν - π^R)`, Schur's test and Proposition 4.2
   (`reference_marginal_density_L2`, `firstMarginal_density_L2`; the latter is a `sorry`-ed spec in
   `PoleCavity`, proved in parallel).
7. Transfer `Var_Q ≤ e^{4β g_L(0)} Var_R`; the finitely many `N < N₁` by `Q_N ≤ K_N R_N` and the crude
   second-moment bound `quad_crude_Q`.
-/
import HRS.Equilibrium.PoleVariance
import HRS.Equilibrium.ReferenceMarginal
import HRS.Equilibrium.ReferenceGlue
import HRS.Equilibrium.MarginalDensity

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.Quad

/-! ## Part `QuadKernel` -/

section QuadKernel

open Function



open HRS HRS.External HRS.External.RefMarg HRS.External.HeatSplit

variable {d : ℕ} {s : ℝ}

/-! ### The envelope as a function of `z` -/

/-- The singular envelope `e(z) = singEnvelope s |z|`. -/
def envT (s : ℝ) (z : Torus d) : ℝ := singEnvelope s (Torus.eucDist z 0)

theorem eucDist_sub (x y : Torus d) : Torus.eucDist x y = Torus.eucDist (x - y) 0 := by
  unfold Torus.eucDist
  simp

theorem eucDist_neg (z : Torus d) : Torus.eucDist (-z) 0 = Torus.eucDist z 0 := by
  unfold Torus.eucDist
  simp [norm_neg]

theorem measurable_eucDist0 : Measurable fun z : Torus d => Torus.eucDist z 0 := by
  have : Continuous fun z : Torus d => Torus.eucDist z 0 := by
    unfold Torus.eucDist
    refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => ?_)
    refine (continuous_norm.comp ((continuous_apply i).sub continuous_const)).pow 2
  exact this.measurable

theorem measurable_singEnvelope : Measurable (singEnvelope s) := by
  unfold singEnvelope
  by_cases hs : s = 0
  · simp only [hs, if_true]
    exact measurable_const.add (Real.measurable_log.abs)
  · simp only [hs, if_false]
    exact measurable_const.add (Measurable.pow_const measurable_id _)

theorem measurable_envT : Measurable (envT (d := d) s) :=
  measurable_singEnvelope.comp measurable_eucDist0

theorem one_le_envT (z : Torus d) : 1 ≤ envT s z :=
  one_le_singEnvelope' (Real.sqrt_nonneg _)

theorem envT_neg (z : Torus d) : envT s (-z) = envT s z := by
  unfold envT; rw [eucDist_neg]

theorem envT_sub_comm (x y : Torus d) : envT s (x - y) = envT s (y - x) := by
  rw [← neg_sub y x, envT_neg]

/-! ### Distribution-function bounds -/

section Dist

variable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)

/-- Weak-`L^p` bound of the envelope. -/
theorem weakLp_envT (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ K0 : ℝ, 0 < K0 ∧ ∀ r : ℝ, 0 < r →
      (volume : Measure (Torus d)) {z : Torus d | r < envT s z} ≤
        ENNReal.ofReal (K0 * r ^ (-(pOf d s))) :=
  weakLp_of_envelope hd hs0 hsd (B := 1) zero_le_one (q := envT s)
    (fun x _ => by rw [one_mul]; rfl)

/-- Truncated second moment `∫ min(e, K)² ≤ c · gFun K`. -/
theorem lintegral_minsq_envT (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ K : ℝ, 1 ≤ K →
      ∫⁻ z : Torus d, ENNReal.ofReal (min (envT s z) K ^ 2) ≤ ENNReal.ofReal (c₁ * gFun d s K) := by
  obtain ⟨K0, hK0, hw⟩ := weakLp_envT hd hs0 hsd
  obtain ⟨c₁, hc₁, hc⟩ := second_moment_gFun hd hs0 hsd hK0
  refine ⟨c₁, hc₁, fun K hK => ?_⟩
  exact (lintegral_minsq_le measurable_envT (fun z => zero_le_one.trans (one_le_envT z)) hK
    (one_lt_pOf hd hs0 hsd) hK0 hw).trans (ENNReal.ofReal_le_ofReal (hc K hK))

/-- Tail `∫ (e - K)₊ ≤ c K^{1-p}`. -/
theorem lintegral_tail_envT (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ c₂ : ℝ, 0 < c₂ ∧ ∀ K : ℝ, 0 < K →
      ∫⁻ z : Torus d, ENNReal.ofReal (envT s z - K) ≤ ENNReal.ofReal (c₂ * K ^ (1 - pOf d s)) := by
  obtain ⟨K0, hK0, hw⟩ := weakLp_envT hd hs0 hsd
  have hp := one_lt_pOf hd hs0 hsd
  refine ⟨K0 * (pOf d s / (pOf d s - 1)), by
    have : 0 < pOf d s - 1 := by linarith
    positivity, fun K hK => ?_⟩
  refine (lintegral_tail_le measurable_envT (fun z => zero_le_one.trans (one_le_envT z)) hK hp hK0 hw).trans
    (le_of_eq ?_)
  congr 1
  ring

/-- Measure of the set where the envelope exceeds `K`. -/
theorem volume_envT_gt (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ K0 : ℝ, 0 < K0 ∧ ∀ K : ℝ, 0 < K →
      (volume : Measure (Torus d)) {z : Torus d | K < envT s z} ≤
        ENNReal.ofReal (K0 * K ^ (-(pOf d s))) := by
  obtain ⟨K0, hK0, hw⟩ := weakLp_envT hd hs0 hsd
  exact ⟨K0, hK0, hw⟩

/-- `e` is integrable on the torus. -/
theorem lintegral_envT_le (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ c₃ : ℝ, 0 < c₃ ∧ ∫⁻ z : Torus d, ENNReal.ofReal (envT s z) ≤ ENNReal.ofReal c₃ := by
  obtain ⟨c₂, hc₂, hc⟩ := lintegral_tail_envT hd hs0 hsd
  refine ⟨1 + c₂ * (1 : ℝ) ^ (1 - pOf d s), by positivity, ?_⟩
  have h1 : ∀ z : Torus d, ENNReal.ofReal (envT s z) ≤ 1 + ENNReal.ofReal (envT s z - 1) := by
    intro z
    calc ENNReal.ofReal (envT s z) = ENNReal.ofReal (1 + (envT s z - 1)) := by congr 1; ring
      _ ≤ ENNReal.ofReal 1 + ENNReal.ofReal (envT s z - 1) := ENNReal.ofReal_add_le
      _ = _ := by simp
  calc ∫⁻ z : Torus d, ENNReal.ofReal (envT s z)
      ≤ ∫⁻ z : Torus d, (1 + ENNReal.ofReal (envT s z - 1)) := lintegral_mono h1
    _ = (∫⁻ z : Torus d, (1 : ℝ≥0∞)) + ∫⁻ z : Torus d, ENNReal.ofReal (envT s z - 1) := by
        rw [lintegral_add_left measurable_const]
    _ ≤ 1 + ENNReal.ofReal (c₂ * (1 : ℝ) ^ (1 - pOf d s)) := by
        have e1 : (∫⁻ z : Torus d, (1 : ℝ≥0∞)) = 1 := by simp
        rw [e1]
        gcongr
        exact hc 1 one_pos
    _ = ENNReal.ofReal (1 + c₂ * (1 : ℝ) ^ (1 - pOf d s)) := by
        rw [ENNReal.ofReal_add (by norm_num) (by positivity)]; simp

end Dist


/-! ### Retained repulsion: `∫ e² e^{-λ e} ≲ gFun K` -/

section Repulsion

/-- `u² e^{-λ u} ≤ min(u, K)²` for `K ≥ 2/λ`, `u ≥ 0`. -/
theorem sq_mul_exp_le {lam K u : ℝ} (hlam : 0 < lam) (hK : 2 / lam ≤ K) (hu : 0 ≤ u) :
    u ^ 2 * Real.exp (-lam * u) ≤ min u K ^ 2 := by
  rcases le_total u K with h | h
  · rw [min_eq_left h]
    have : Real.exp (-lam * u) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    nlinarith [sq_nonneg u]
  · rw [min_eq_right h]
    have ht : (lam * u / 2) ≤ Real.exp (lam * u / 2) := by
      have := Real.add_one_le_exp (lam * u / 2)
      linarith
    have h2 : u * Real.exp (-(lam * u / 2)) ≤ 2 / lam := by
      have hpos : 0 < Real.exp (lam * u / 2) := Real.exp_pos _
      rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hpos, div_mul_eq_mul_div, le_div_iff₀ hlam]
      nlinarith
    have h3 : u ^ 2 * Real.exp (-lam * u) = (u * Real.exp (-(lam * u / 2))) ^ 2 := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2
      push_cast; ring
    rw [h3]
    have h4 : 0 ≤ u * Real.exp (-(lam * u / 2)) := mul_nonneg hu (Real.exp_pos _).le
    have h5 : u * Real.exp (-(lam * u / 2)) ≤ K := h2.trans hK
    nlinarith

/-- **Retained-repulsion integral** (`A:eq:radial` as a distribution-function bound):
for `K ≥ max(1, 2/λ)`, `∫ e(x-y)² e^{-λ e(x-y)} dμ(y) ≤ Λ c₁ gFun K`. -/
theorem repulsion_integral (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ (ρ : Torus d → ℝ) (Λ : ℝ), (∀ y, ρ y ≤ Λ) → ∀ (lam K : ℝ), 0 < lam → 1 ≤ K →
      2 / lam ≤ K → ∀ x : Torus d,
      ∫⁻ y, ENNReal.ofReal (envT s (x - y) ^ 2 * Real.exp (-lam * envT s (x - y))) ∂(withDensityReal ρ) ≤
        ENNReal.ofReal Λ * ENNReal.ofReal (c₁ * gFun d s K) := by
  obtain ⟨c₁, hc₁, hc⟩ := lintegral_minsq_envT hd hs0 hsd
  refine ⟨c₁, hc₁, fun ρ Λ hΛ lam K hlam hK1 hK x => ?_⟩
  refine (KernelAux2.lintegral_conv_le ρ Λ hΛ
    (fun z => ENNReal.ofReal (envT s z ^ 2 * Real.exp (-lam * envT s z))) x).trans ?_
  gcongr
  refine (lintegral_mono fun z => ENNReal.ofReal_le_ofReal
    (sq_mul_exp_le hlam hK (zero_le_one.trans (one_le_envT z)))).trans (hc K hK1)

end Repulsion

/-! ### A Schur bound -/

section Schur

/-- Schur test in `ℝ≥0∞` form for a translation kernel: if `∫ k(x-y) dμ(y) ≤ A` and
`∫ k(x-y) dμ(x) ≤ A`, then `∫ (∫ k(x-y) f(y) dμ(y))² dμ(x) ≤ A² ∫ f² dμ`. -/
theorem schur_sq {ν : Measure (Torus d)} [SFinite ν] {k f : Torus d → ℝ≥0∞} (hk : Measurable k)
    (hf : Measurable f) {A : ℝ≥0∞}
    (h1 : ∀ x, ∫⁻ y, k (x - y) ∂ν ≤ A) (h2 : ∀ y, ∫⁻ x, k (x - y) ∂ν ≤ A) :
    ∫⁻ x, (∫⁻ y, k (x - y) * f y ∂ν) ^ 2 ∂ν ≤ A ^ 2 * ∫⁻ y, f y ^ 2 ∂ν := by
  have hkm : Measurable fun p : Torus d × Torus d => k (p.1 - p.2) :=
    hk.comp (measurable_fst.sub measurable_snd)
  have hpt : ∀ x, (∫⁻ y, k (x - y) * f y ∂ν) ^ 2 ≤ A * ∫⁻ y, k (x - y) * f y ^ 2 ∂ν := by
    intro x
    have hφ : Measurable fun y => k (x - y) := hk.comp (measurable_const.sub measurable_id)
    have := PoleCavityAux.weighted_cs ν (fun y => k (x - y)) f hφ hf
    exact this.trans (mul_le_mul' (h1 x) le_rfl)
  calc ∫⁻ x, (∫⁻ y, k (x - y) * f y ∂ν) ^ 2 ∂ν
      ≤ ∫⁻ x, A * ∫⁻ y, k (x - y) * f y ^ 2 ∂ν ∂ν := lintegral_mono hpt
    _ = A * ∫⁻ x, ∫⁻ y, k (x - y) * f y ^ 2 ∂ν ∂ν := by
        rw [lintegral_const_mul]
        exact Measurable.lintegral_prod_right' (f := fun p : Torus d × Torus d => k (p.1 - p.2) * f p.2 ^ 2)
          (hkm.mul ((hf.comp measurable_snd).pow_const 2))
    _ = A * ∫⁻ y, ∫⁻ x, k (x - y) * f y ^ 2 ∂ν ∂ν := by
        congr 1
        refine lintegral_lintegral_swap ?_
        exact (hkm.mul ((hf.comp measurable_snd).pow_const 2)).aemeasurable
    _ ≤ A * ∫⁻ y, A * f y ^ 2 ∂ν := by
        gcongr with y
        have hm : Measurable fun x : Torus d => k (x - y) := hk.comp (measurable_id.sub measurable_const)
        rw [lintegral_mul_const _ hm]
        exact mul_le_mul' (h2 y) le_rfl
    _ = A ^ 2 * ∫⁻ y, f y ^ 2 ∂ν := by
        rw [lintegral_const_mul _ (hf.pow_const 2), ← mul_assoc, sq]

end Schur


/-! ### Lower envelope of the Riesz kernel -/

section Lower

theorem exists_box_rep (z : Torus d) : ∃ y ∈ KernelAux.Box d, KernelAux.boxPt y = z := by
  refine ⟨fun i => ((AddCircle.equivIoc (1 : ℝ) (-1 / 2) (z i) : Set.Ioc (-1 / 2 : ℝ) (-1 / 2 + 1)) : ℝ),
    fun i => ?_, ?_⟩
  · exact (AddCircle.equivIoc (1 : ℝ) (-1 / 2) (z i)).2
  · funext i
    simp [KernelAux.boxPt]

theorem eucDist_boxPt_eq {y : Fin d → ℝ} (hy : ∀ i, |y i| ≤ 1 / 2) :
    Torus.eucDist (KernelAux.boxPt y) 0 = ‖(WithLp.toLp 2 y : Euc d)‖ := by
  rw [eucDist_boxPt hy, EuclideanSpace.norm_eq]
  simp [Real.norm_eq_abs, sq_abs]

/-- **Lower envelope**: `g(z) ≥ e(z) - C` for `z ≠ 0`. -/
theorem periodicRiesz_lower_env (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C : ℝ, ∀ z : Torus d, z ≠ 0 → envT s z - C ≤ periodicRiesz d s z := by
  have hd0 : 0 < d := by omega
  obtain ⟨r, δ, hδ, hr, hsing⟩ : ∃ (r : Torus d → ℝ) (δ : ℝ), 0 < δ ∧ Torus.IsSmooth r ∧
      ∀ x : Euc d, ‖x‖ < δ → x ≠ 0 →
        periodicRiesz d s (Torus.mk x) = (if s = 0 then -Real.log ‖x‖ else ‖x‖ ^ (-s)) + r (Torus.mk x) := by
    by_cases hs : s = 0
    · subst hs
      obtain ⟨r, δ, h1, h2, h3⟩ := periodicLog_local_singularity (d := d) hd
      exact ⟨r, δ, h1, h2, fun x hx hx0 => by simpa using h3 x hx hx0⟩
    · obtain ⟨r, δ, h1, h2, h3⟩ := periodicRiesz_local_singularity hd (lt_of_le_of_ne hs0 (Ne.symm hs)) hsd
      exact ⟨r, δ, h1, h2, fun x hx hx0 => by simpa [hs] using h3 x hx hx0⟩
  have hrc : Continuous r := PoleCavityAux.continuous_of_lift'
    (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift r) from hr).continuous
  obtain ⟨Mr, hMr⟩ := isCompact_univ.exists_bound_of_continuousOn (f := r) hrc.continuousOn
  obtain ⟨Bg, hBg⟩ := periodicRiesz_ge (d := d) (s := s) hd hs0 hsd
  have hE : (Real.sqrt d / 2) ≥ 0 := by positivity
  -- constants
  set C0 : ℝ := 1 + 2 * max (Real.log δ) 0 + ‖Mr‖ with hC0
  set C1 : ℝ := 1 + δ ^ (-s) + |Real.log δ| + |Real.log (Real.sqrt d / 2)| + Bg with hC1
  refine ⟨max C0 C1 + ‖Mr‖ + |Bg|, fun z hz => ?_⟩
  obtain ⟨y, hyB, rfl⟩ := exists_box_rep z
  have hyb : ∀ i, |y i| ≤ 1 / 2 := fun i => KernelAux.Box_abs_le hyB i
  set ye : Euc d := WithLp.toLp 2 y with hye
  have hmk : Torus.mk ye = KernelAux.boxPt y := by
    funext i
    simp [Torus.mk, KernelAux.boxPt, hye]
  have hed : Torus.eucDist (KernelAux.boxPt y) 0 = ‖ye‖ := eucDist_boxPt_eq hyb
  have hrb : |r (KernelAux.boxPt y)| ≤ ‖Mr‖ := by
    have := hMr (KernelAux.boxPt y) trivial
    simpa [Real.norm_eq_abs] using this.trans (le_abs_self _ |>.trans (by simp))
  have hyne : ye ≠ 0 := by
    intro h0
    apply hz
    funext i
    have := congrFun (congrArg (fun v : Euc d => (v : Fin d → ℝ)) h0) i
    simp [KernelAux.boxPt, hye] at this ⊢
    simp [this]
  have hpos : 0 < ‖ye‖ := norm_pos_iff.2 hyne
  have hMr0 : 0 ≤ ‖Mr‖ := norm_nonneg _
  have hmax0 : 0 ≤ max (Real.log δ) 0 := le_max_right _ _
  by_cases hA : ‖ye‖ < δ
  · have hsg := hsing ye hA hyne
    rw [hmk] at hsg
    rw [hsg]
    unfold envT singEnvelope
    rw [hed]
    have hlb := (abs_le.mp hrb).1
    by_cases hs : s = 0
    · simp only [hs, if_true]
      have hlogle : Real.log ‖ye‖ ≤ Real.log δ := Real.log_le_log hpos hA.le
      have habs : |Real.log ‖ye‖| ≤ -Real.log ‖ye‖ + 2 * max (Real.log δ) 0 := by
        rcases le_total (Real.log ‖ye‖) 0 with h | h
        · rw [abs_of_nonpos h]; linarith
        · rw [abs_of_nonneg h]
          have := le_max_left (Real.log δ) 0
          linarith
      have : 0 ≤ ‖Mr‖ + |Bg| + (max C0 C1 - C0) := by
        have := le_max_left C0 C1; positivity
      nlinarith [le_max_left C0 C1, abs_nonneg Bg]
    · simp only [hs, if_false]
      have : 1 ≤ C0 := by nlinarith
      nlinarith [le_max_left C0 C1, abs_nonneg Bg]
  · push Not at hA
    have hg := hBg (KernelAux.boxPt y)
    unfold envT singEnvelope
    rw [hed]
    have hEle : ‖ye‖ ≤ Real.sqrt d / 2 := by
      rw [← hed]; exact eucDist_le_half_sqrt _
    by_cases hs : s = 0
    · simp only [hs, if_true]
      have hl1 : Real.log δ ≤ Real.log ‖ye‖ := Real.log_le_log hδ hA
      have hl2 : Real.log ‖ye‖ ≤ Real.log (Real.sqrt d / 2) := Real.log_le_log hpos hEle
      have := abs_le_max_abs_abs hl1 hl2
      have h3 : max |Real.log δ| |Real.log (Real.sqrt d / 2)| ≤ |Real.log δ| + |Real.log (Real.sqrt d / 2)| :=
        max_le (by linarith [abs_nonneg (Real.log (Real.sqrt d / 2))])
          (by linarith [abs_nonneg (Real.log δ)])
      have : 0 ≤ ‖Mr‖ + |Bg| := by positivity
      have hC1' : C1 = 1 + 1 + |Real.log δ| + |Real.log (Real.sqrt d / 2)| + Bg := by
        rw [hC1, hs]; simp
      have hm1 := le_max_right C0 C1
      rw [hs] at hg
      linarith [abs_nonneg Bg, le_abs_self Bg, abs_nonneg (Real.log δ), abs_nonneg (Real.log (Real.sqrt d / 2))]
    · simp only [hs, ite_false]
      have h3 : ‖ye‖ ^ (-s) ≤ δ ^ (-s) := Real.rpow_le_rpow_of_nonpos hδ hA (by linarith [lt_of_le_of_ne hs0 (Ne.symm hs)])
      have hm1 := le_max_right C0 C1
      linarith [abs_nonneg Bg, le_abs_self Bg, abs_nonneg (Real.log δ), abs_nonneg (Real.log (Real.sqrt d / 2))]

end Lower

end QuadKernel

/-! ## Part `QuadWeak` -/

section QuadWeak

open Function



open HRS HRS.External HRS.External.PoleVar

variable {d : ℕ}

/-! ### The centered kernel and the row -/

/-- `H(x) = ∫ h(x,y) dπ(y)`. -/
def Hc (h : Torus d → Torus d → ℝ) (π : Measure (Torus d)) (x : Torus d) : ℝ := ∫ y, h x y ∂π

/-- `h₀ = ∬ h dπ dπ`. -/
def h0c (h : Torus d → Torus d → ℝ) (π : Measure (Torus d)) : ℝ := ∫ x, ∫ y, h x y ∂π ∂π

/-- The doubly centered kernel `h_c(x,y) = h(x,y) - H(x) - H(y) + h₀`. -/
def cK (h : Torus d → Torus d → ℝ) (π : Measure (Torus d)) (x y : Torus d) : ℝ :=
  h x y - Hc h π x - Hc h π y + h0c h π

/-- The row `∑_{j≠i} h_c(x_i,x_j) - H(x_i)` of `A:eq:outer-row`. -/
def rowFun (h : Torus d → Torus d → ℝ) (π : Measure (Torus d)) {N : ℕ} (i : Fin N) (Y : Config d N) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, cK h π (Y i) (Y j) - Hc h π (Y i)

/-- The part of `D_N` that does not depend on `x_i`. -/
def restFun (h : Torus d → Torus d → ℝ) (π : Measure (Torus d)) {N : ℕ} (i : Fin N) (Y : Config d N) : ℝ :=
  (1 / (N : ℝ) ^ 2) * ∑ a ∈ Finset.univ.erase i, ∑ b ∈ (Finset.univ.erase i).erase a, h (Y a) (Y b)
    - 2 * ((N : ℝ) - 1) / (N : ℝ) ^ 2 * ∑ a ∈ Finset.univ.erase i, Hc h π (Y a)
    + (1 - 2 * ((N : ℝ) - 1) / (N : ℝ) ^ 2) * h0c h π

theorem measurable_h_pair {h : Torus d → Torus d → ℝ} (hm : Measurable (Function.uncurry h)) {N : ℕ}
    (i j : Fin N) : Measurable fun X : Config d N => h (X i) (X j) :=
  Measurable.comp (g := Function.uncurry h) hm (f := fun X : Config d N => (X i, X j))
    ((measurable_pi_apply (X := fun _ : Fin N => Torus d) i).prodMk
      (measurable_pi_apply (X := fun _ : Fin N => Torus d) j))

theorem measurable_h_x {h : Torus d → Torus d → ℝ} (hm : Measurable (Function.uncurry h)) (x : Torus d) :
    Measurable (h x) :=
  Measurable.comp (g := Function.uncurry h) hm (f := fun y : Torus d => (x, y))
    (measurable_const.prodMk measurable_id)

theorem measurable_Hc {h : Torus d → Torus d → ℝ} (hm : Measurable (Function.uncurry h))
    (π : Measure (Torus d)) [SFinite π] : Measurable (Hc h π) := by
  unfold Hc
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := π)).measurable

theorem measurable_quadStat {h : Torus d → Torus d → ℝ} (hm : Measurable (Function.uncurry h))
    (π : Measure (Torus d)) [SFinite π] {N : ℕ} : Measurable (fun X : Config d N => quadStat h π X) := by
  unfold quadStat
  have hH := measurable_Hc hm π
  refine Measurable.add (Measurable.sub ?_ ?_) measurable_const
  · refine Measurable.const_mul (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_) _
    exact measurable_h_pair hm i j
  · refine Measurable.const_mul (Measurable.const_mul (Finset.measurable_sum _ fun i _ => ?_) _) _
    exact hH.comp (measurable_pi_apply i)

theorem measurable_rowFun {h : Torus d → Torus d → ℝ} (hm : Measurable (Function.uncurry h))
    (π : Measure (Torus d)) [SFinite π] {N : ℕ} (i : Fin N) : Measurable (rowFun h π i) := by
  unfold rowFun cK
  have hH := measurable_Hc hm π
  refine Measurable.sub (Finset.measurable_sum _ fun j _ => ?_) (hH.comp (measurable_pi_apply i))
  refine Measurable.add (Measurable.sub (Measurable.sub ?_ (hH.comp (measurable_pi_apply i)))
    (hH.comp (measurable_pi_apply j))) measurable_const
  exact measurable_h_pair hm i j

/-- Splitting the double sum over ordered pairs `a ≠ b` at the index `i`. -/
theorem sum_sum_erase_split {N : ℕ} (i : Fin N) (f : Fin N → Fin N → ℝ) :
    ∑ a, ∑ b ∈ Finset.univ.erase a, f a b
      = ∑ b ∈ Finset.univ.erase i, f i b + ∑ a ∈ Finset.univ.erase i, f a i
        + ∑ a ∈ Finset.univ.erase i, ∑ b ∈ (Finset.univ.erase i).erase a, f a b := by
  have h1 : ∑ a, ∑ b ∈ Finset.univ.erase a, f a b
      = ∑ b ∈ Finset.univ.erase i, f i b + ∑ a ∈ Finset.univ.erase i, ∑ b ∈ Finset.univ.erase a, f a b :=
    (Finset.add_sum_erase Finset.univ (fun a => ∑ b ∈ Finset.univ.erase a, f a b) (Finset.mem_univ i)).symm
  have h2 : ∀ a ∈ Finset.univ.erase i, ∑ b ∈ Finset.univ.erase a, f a b
      = f a i + ∑ b ∈ (Finset.univ.erase i).erase a, f a b := by
    intro a ha
    have hai : a ≠ i := Finset.ne_of_mem_erase ha
    have hmem : i ∈ Finset.univ.erase a := Finset.mem_erase.2 ⟨hai.symm, Finset.mem_univ i⟩
    rw [← Finset.add_sum_erase (Finset.univ.erase a) (fun b => f a b) hmem, Finset.erase_right_comm]
  rw [h1, Finset.sum_congr rfl h2, Finset.sum_add_distrib]
  ring

/-- **Omitted-diagonal identity** (`A:eq:D-diagonal`), single-site form: for a symmetric kernel,
`D_N(h;π)(Y) = (2/N²) row_i(Y) + rest_i(Y)`. -/
theorem quadStat_eq_row_add_rest {h : Torus d → Torus d → ℝ} (hsym : ∀ x y, h x y = h y x)
    (π : Measure (Torus d)) {N : ℕ} (hN : 0 < N) (i : Fin N) (Y : Config d N) :
    quadStat h π Y = (2 / (N : ℝ) ^ 2) * rowFun h π i Y + restFun h π i Y := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  unfold quadStat rowFun restFun cK Hc h0c
  rw [sum_sum_erase_split i (fun a b => h (Y a) (Y b))]
  have e1 : ∑ a ∈ Finset.univ.erase i, h (Y a) (Y i) = ∑ b ∈ Finset.univ.erase i, h (Y i) (Y b) :=
    Finset.sum_congr rfl fun a _ => hsym _ _
  rw [e1]
  have hcard : ((Finset.univ.erase i).card : ℝ) = (N : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp [Nat.cast_sub hN]
  have e2 : ∑ j ∈ Finset.univ.erase i, (h (Y i) (Y j) - ∫ y, h (Y i) y ∂π - ∫ y, h (Y j) y ∂π
      + ∫ x, ∫ y, h x y ∂π ∂π)
      = ∑ j ∈ Finset.univ.erase i, h (Y i) (Y j) - ((N : ℝ) - 1) * ∫ y, h (Y i) y ∂π
        - ∑ j ∈ Finset.univ.erase i, ∫ y, h (Y j) y ∂π + ((N : ℝ) - 1) * ∫ x, ∫ y, h x y ∂π ∂π := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul, hcard]
  rw [e2]
  have e3 : ∑ a, ∫ y, h (Y a) y ∂π = ∫ y, h (Y i) y ∂π + ∑ a ∈ Finset.univ.erase i, ∫ y, h (Y a) y ∂π :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
  rw [e3]
  field_simp
  ring

theorem restFun_update {h : Torus d → Torus d → ℝ} (π : Measure (Torus d)) {N : ℕ} (i : Fin N)
    (Y : Config d N) (z : Torus d) : restFun h π i (update Y i z) = restFun h π i Y := by
  unfold restFun
  have h1 : ∀ a ∈ Finset.univ.erase i, update Y i z a = Y a := fun a ha =>
    update_of_ne (Finset.ne_of_mem_erase ha) _ _
  have h2 : ∑ a ∈ Finset.univ.erase i, ∑ b ∈ (Finset.univ.erase i).erase a, h (update Y i z a) (update Y i z b)
      = ∑ a ∈ Finset.univ.erase i, ∑ b ∈ (Finset.univ.erase i).erase a, h (Y a) (Y b) := by
    refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
    rw [h1 a ha, h1 b (Finset.mem_of_mem_erase hb)]
  have h3 : ∑ a ∈ Finset.univ.erase i, Hc h π (update Y i z a) = ∑ a ∈ Finset.univ.erase i, Hc h π (Y a) :=
    Finset.sum_congr rfl fun a ha => by rw [h1 a ha]
  rw [h2, h3]


/-! ### Wu's inequality for the quadratic statistic -/

section Resample

variable {μ : Measure (Torus d)} [IsProbabilityMeasure μ]

theorem enorm_sq_const_mul (c r : ℝ) (hc : 0 ≤ c) :
    ‖c * r‖ₑ ^ 2 = ENNReal.ofReal (c ^ 2) * ‖r‖ₑ ^ 2 := by
  rw [enorm_mul, mul_pow, Real.enorm_of_nonneg hc, ENNReal.ofReal_pow hc]

/-- **`A:eq:outer-row`**: single-site resampling reduces the variance of `D_N(h;π)` under the weak
ensemble `R` to the second moments of the rows,
`Var_R D_N ≤ (8/N⁴) ∑_i E_R |row_i|²`. -/
theorem evariance_quad_le (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {N : ℕ} (hN0 : 0 < N)
    (hκ : weakKappa V β ≤ 1 / 2) {h : Torus d → Torus d → ℝ} (hm : Measurable (Function.uncurry h))
    (hsym : ∀ x y, h x y = h y x) (π : Measure (Torus d)) [IsProbabilityMeasure π] :
    evariance (fun X : Config d N => quadStat h π X)
        (pinnedLaw V (β / N) N (fun e : Empty => e.elim)) ≤
      ENNReal.ofReal (8 / (N : ℝ) ^ 4) * ∑ i, ∫⁻ Y, ‖rowFun h π i Y‖ₑ ^ 2
        ∂(pinnedLaw V (β / N) N (fun e : Empty => e.elim)) := by
  have hlam : 0 ≤ β / N := div_nonneg hβ (Nat.cast_nonneg N)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN0
  have hψ := isField_pinField V hlam (fun e : Empty => e.elim)
  set S := fieldSpec (V := V) hψ hlam N with hS
  have hSP : S.P = pinnedLaw V (β / N) N (fun e : Empty => e.elim) := rfl
  have hF : Measurable (fun X : Config d N => quadStat h π X) := measurable_quadStat hm π
  have h1 := weak_resampling (B := Empty) V hβ hN0 (by simp) (fun e : Empty => e.elim) hκ _ hF
  refine h1.trans ?_
  have hper : ∀ i : Fin N, ∫⁻ x, evariance (fun z => quadStat h π (update x i z))
      (siteKernel μ (pinnedDensity V (β / N) N (fun e : Empty => e.elim)) i x)
        ∂(pinnedLaw V (β / N) N (fun e : Empty => e.elim))
      ≤ ENNReal.ofReal (4 / (N : ℝ) ^ 4) * ∫⁻ Y, ‖rowFun h π i Y‖ₑ ^ 2
        ∂(pinnedLaw V (β / N) N (fun e : Empty => e.elim)) := by
    intro i
    have hG : ∀ x, siteKernel μ (pinnedDensity V (β / N) N (fun e : Empty => e.elim)) i x = S.G i x :=
      fun x => rfl
    have hrow := measurable_rowFun hm π (N := N) i
    have hpt : ∀ x, evariance (fun z => quadStat h π (update x i z))
        (siteKernel μ (pinnedDensity V (β / N) N (fun e : Empty => e.elim)) i x)
        ≤ ∫⁻ z, ENNReal.ofReal (4 / (N : ℝ) ^ 4) * ‖rowFun h π i (update x i z)‖ₑ ^ 2 ∂(S.G i x) := by
      intro x
      rw [hG]
      refine (evariance_le_lintegral_sub (S.G i x) (hF.comp (measurable_update x)).aestronglyMeasurable
        (restFun h π i x)).trans (le_of_eq ?_)
      refine lintegral_congr fun z => ?_
      have e1 := quadStat_eq_row_add_rest hsym π hN0 i (update x i z)
      rw [restFun_update] at e1
      simp only [Function.comp]
      rw [e1, add_sub_cancel_right, enorm_sq_const_mul _ _ (by positivity)]
      congr 2
      field_simp
      norm_num
    calc _ ≤ ∫⁻ x, ∫⁻ z, ENNReal.ofReal (4 / (N : ℝ) ^ 4) * ‖rowFun h π i (update x i z)‖ₑ ^ 2 ∂(S.G i x)
          ∂(pinnedLaw V (β / N) N (fun e : Empty => e.elim)) := lintegral_mono hpt
      _ = ∫⁻ Y, ENNReal.ofReal (4 / (N : ℝ) ^ 4) * ‖rowFun h π i Y‖ₑ ^ 2
          ∂(pinnedLaw V (β / N) N (fun e : Empty => e.elim)) := by
        rw [← hSP]
        exact S.invariant i (fun Y => ENNReal.ofReal (4 / (N : ℝ) ^ 4) * ‖rowFun h π i Y‖ₑ ^ 2)
          (measurable_const.mul (hrow.enorm.pow_const 2))
      _ = _ := by
        rw [lintegral_const_mul _ (hrow.enorm.pow_const 2)]
  calc 2 * ∑ i, ∫⁻ x, evariance (fun z => quadStat h π (update x i z))
        (siteKernel μ (pinnedDensity V (β / N) N (fun e : Empty => e.elim)) i x)
          ∂(pinnedLaw V (β / N) N (fun e : Empty => e.elim))
      ≤ 2 * ∑ i : Fin N, (ENNReal.ofReal (4 / (N : ℝ) ^ 4) * ∫⁻ Y, ‖rowFun h π i Y‖ₑ ^ 2
          ∂(pinnedLaw V (β / N) N (fun e : Empty => e.elim))) := by
        gcongr with i _
        exact hper i
    _ = _ := by
        rw [← Finset.mul_sum, ← mul_assoc]
        congr 1
        rw [show (8 : ℝ) / (N : ℝ) ^ 4 = 2 * (4 / (N : ℝ) ^ 4) by ring,
          ENNReal.ofReal_mul (by norm_num)]
        simp

end Resample


/-! ### Disintegration of the pinned ensemble -/

section Disint

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ] {B : Type*} [Fintype B]

/-- **Disintegration** (`lintegral` form of `pinned_marginal_succ`): the `(n+1)`-particle pinned
ensemble is the mixture, over the value `x` of coordinate `i` with weight `pinWeight`, of the
`n`-particle ensembles with the extra pin `x`. -/
theorem lintegral_pinned_succ (V : WeakPotential μ) {lam : ℝ} (hlam : 0 ≤ lam) (a : B → E) {n : ℕ}
    (i : Fin (n + 1)) {Φ : (Fin (n + 1) → E) → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∫⁻ Y, Φ Y ∂(pinnedLaw V lam (n + 1) a)
      = ∫⁻ x, pinWeight V lam a n x *
          ∫⁻ y, Φ (insertAt i x y) ∂(pinnedLaw V lam n (pinsWith a x)) ∂μ := by
  have hψ := isField_pinField V hlam a
  have hψx : ∀ x, IsField μ (pinField V lam (pinsWith a x)) V.M
      (V.M' + lam * Fintype.card (Option B) * V.γ) := fun x => isField_pinField V hlam _
  change ∫⁻ Y, Φ Y ∂(fieldLaw V (pinField V lam a) lam (n + 1)) = _
  unfold fieldLaw
  have hdm := measurable_fieldDensity hψ.measurable V lam (n + 1)
  rw [lintegral_withDensity_eq_lintegral_mul _ hdm hΦ]
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => E) i with he
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ) i
  have hsymm : ∀ (x : E) (y : Fin n → E), e.symm (x, y) = insertAt i x y := fun _ _ => rfl
  set h : (Fin (n + 1) → E) → ℝ≥0∞ := fieldDensity V (pinField V lam a) lam (n + 1) * Φ with hh
  have hhm : Measurable h := hdm.mul hΦ
  have step1 : ∫⁻ y, h y ∂(Measure.pi fun _ : Fin (n + 1) => μ)
      = ∫⁻ p, h (e.symm p) ∂(μ.prod (Measure.pi fun _ : Fin n => μ)) := by
    have := hmp.lintegral_comp_emb e.measurableEmbedding (fun p => h (e.symm p))
    rw [← this]
    exact lintegral_congr fun y => by rw [e.symm_apply_apply]
  rw [step1, lintegral_prod (fun p => h (e.symm p)) (hhm.comp e.symm.measurable).aemeasurable]
  refine lintegral_congr fun x => ?_
  simp only [hsymm]
  have hΦx : Measurable fun y : Fin n → E => Φ (insertAt i x y) :=
    hΦ.comp (e.symm.measurable.comp (measurable_const.prodMk measurable_id))
  have hdx := measurable_fieldDensity (hψx x).measurable V lam n
  change ∫⁻ y, h (insertAt i x y) ∂(Measure.pi fun _ : Fin n => μ) = _
  have hP : (pinnedLaw V lam n (pinsWith a x)) = (Measure.pi fun _ : Fin n => μ).withDensity
      (fieldDensity V (pinField V lam (pinsWith a x)) lam n) := rfl
  rw [hP, lintegral_withDensity_eq_lintegral_mul _ hdx hΦx, ← lintegral_const_mul _ (hdx.mul hΦx)]
  refine lintegral_congr fun y => ?_
  simp only [hh, Pi.mul_apply, fieldDensity]
  rw [fieldWeight_insertAt]
  unfold pinWeight
  have hn0 : fieldNorm V (pinField V lam (pinsWith a x)) lam n ≠ 0 :=
    (fieldNorm_pos (hψx x).measurable V lam n).ne'
  have hnt : fieldNorm V (pinField V lam (pinsWith a x)) lam n ≠ ⊤ :=
    (fieldNorm_lt_top (hψx x) hlam n).ne
  calc ENNReal.ofReal (Real.exp (pinField V lam a x)) *
        fieldWeight V (pinField V lam (pinsWith a x)) lam y *
        (fieldNorm V (pinField V lam a) lam (n + 1))⁻¹ * Φ (insertAt i x y)
      = (fieldNorm V (pinField V lam (pinsWith a x)) lam n *
          (fieldNorm V (pinField V lam (pinsWith a x)) lam n)⁻¹) *
        (ENNReal.ofReal (Real.exp (pinField V lam a x)) *
        fieldWeight V (pinField V lam (pinsWith a x)) lam y *
        (fieldNorm V (pinField V lam a) lam (n + 1))⁻¹ * Φ (insertAt i x y)) := by
        rw [ENNReal.mul_inv_cancel hn0 hnt, one_mul]
    _ = _ := by ring

end Disint


/-! ### Second moment of a linear statistic under a pinned ensemble -/

section SecondMoment

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ] {B : Type*} [Fintype B]

/-- Every one-coordinate marginal of the pinned ensemble is dominated by `e^{M' + βγ + ψ} μ`
(the retained pin factors `e^{-λ q(·,a_b)}` are inside `ψ = pinField`). -/
theorem pinned_marginal_le_density (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {N n : ℕ} (hN0 : 0 < N)
    (hN : n + Fintype.card B ≤ N) (a : B → E) (k : Fin n) :
    (pinnedLaw V (β / N) n a).map (fun y => y k) ≤
      μ.withDensity (fun z => ENNReal.ofReal (Real.exp (V.M' + β * V.γ + pinField V (β / N) a z))) := by
  have hlam : 0 ≤ β / N := div_nonneg hβ (Nat.cast_nonneg N)
  have hψ := isField_pinField V hlam a
  refine Measure.le_iff.2 fun A hA => ?_
  rw [withDensity_apply _ hA]
  exact field_marginal_le (V := V) hψ hlam (weak_Lambda_le V hβ hN0 hN) k hA

theorem lintegral_enorm_sq_eq_ofReal {α : Type*} [MeasurableSpace α] {ν : Measure α} {X : α → ℝ}
    (hX : MemLp X 2 ν) : ∫⁻ z, ‖X z‖ₑ ^ 2 ∂ν = ENNReal.ofReal (∫ z, X z ^ 2 ∂ν) := by
  have hint : Integrable (fun z => X z ^ 2) ν := hX.integrable_sq
  rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun z => sq_nonneg _)]
  refine lintegral_congr fun z => ?_
  rw [← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]

/-- **Second moment of a linear statistic under a pinned ensemble**: variance by Wu's linear inequality
(`2n ∫ |f|² dπ`, with the retained pin factor in `π ≤ e^{..} e^{ψ} μ`), plus the square of the mean. -/
theorem second_moment_pinned (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {N n : ℕ} [NeZero n] (hN0 : 0 < N)
    (hN : n + Fintype.card B ≤ N) (a : B → E) (hκ : weakKappa V β ≤ 1 / 2)
    {f : E → ℝ} (hf : Measurable f) (c : ℝ) :
    ∫⁻ y, ‖∑ k, f (y k) - c‖ₑ ^ 2 ∂(pinnedLaw V (β / N) n a)
      ≤ ENNReal.ofReal (2 * n) * ∫⁻ z, ‖f z‖ₑ ^ 2 *
          ENNReal.ofReal (Real.exp (V.M' + β * V.γ + pinField V (β / N) a z)) ∂μ
        + ENNReal.ofReal ((∑ k, ∫ z, f z ∂((pinnedLaw V (β / N) n a).map (fun y => y k)) - c) ^ 2) := by
  have hlam : 0 ≤ β / N := div_nonneg hβ (Nat.cast_nonneg N)
  have hPr := isProb_pinnedLaw V hlam n a
  set P := pinnedLaw V (β / N) n a with hP
  set A := ∫⁻ z, ‖f z‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (V.M' + β * V.γ + pinField V (β / N) a z)) ∂μ with hA
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne n
  by_cases hAtop : A = ⊤
  · rw [hAtop, ENNReal.mul_top (by simpa using hn0)]
    simp
  have hS : Measurable fun y : Fin n → E => ∑ k, f (y k) :=
    Finset.measurable_sum _ fun k _ => hf.comp (measurable_pi_apply k)
  -- second moment of f against each marginal
  have hmarg : ∀ k : Fin n, ∫⁻ z, ‖f z‖ₑ ^ 2 ∂(P.map (fun y => y k)) ≤ A := by
    intro k
    calc ∫⁻ z, ‖f z‖ₑ ^ 2 ∂(P.map (fun y => y k))
        ≤ ∫⁻ z, ‖f z‖ₑ ^ 2 ∂(μ.withDensity fun z => ENNReal.ofReal
            (Real.exp (V.M' + β * V.γ + pinField V (β / N) a z))) :=
          lintegral_mono' (pinned_marginal_le_density V hβ hN0 hN a k) le_rfl
      _ = A := by
          rw [lintegral_withDensity_eq_lintegral_mul₀]
          · simp only [Pi.mul_apply]
            exact lintegral_congr fun z => mul_comm _ _
          · exact (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
              (measurable_const.add (isField_pinField V hlam a).measurable))).aemeasurable
          · exact (hf.enorm.pow_const 2).aemeasurable
  have hfL2 : ∀ k : Fin n, MemLp f 2 (P.map (fun y => y k)) := by
    intro k
    refine (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).2 ⟨hf.aestronglyMeasurable.pow 2, ?_⟩
    simp only [HasFiniteIntegral, enorm_pow]
    exact lt_of_le_of_lt (hmarg k) (lt_top_iff_ne_top.2 hAtop)
  have hfi : ∀ k : Fin n, Integrable (fun y : Fin n → E => f (y k)) P := by
    intro k
    have := (hfL2 k).integrable (by norm_num)
    exact (integrable_map_measure hf.aestronglyMeasurable (measurable_pi_apply k).aemeasurable).1 this
  -- variance bound
  have hvar : evariance (fun y : Fin n → E => ∑ k, f (y k)) P ≤ ENNReal.ofReal (2 * n) * A := by
    have h1 := weak_linear_variance_symm (B := B) V hβ hN0 hN a hκ f hf
    refine h1.trans ?_
    have h2 : evariance f (P.map (fun x => x 0)) ≤ A := by
      refine (evariance_le_lintegral_sub (P.map (fun x => x 0)) hf.aestronglyMeasurable 0).trans ?_
      simpa using hmarg 0
    have e : (2 : ℝ≥0∞) * n = ENNReal.ofReal (2 * n) := by
      rw [ENNReal.ofReal_mul (by norm_num)]; simp
    rw [e]
    gcongr
  have hvtop : evariance (fun y : Fin n → E => ∑ k, f (y k)) P < ⊤ :=
    lt_of_le_of_lt hvar (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.2 hAtop))
  have hSmem : MemLp (fun y : Fin n → E => ∑ k, f (y k)) 2 P :=
    (evariance_lt_top_iff_memLp hS.aestronglyMeasurable).1 hvtop
  have hSc : MemLp (fun y : Fin n → E => ∑ k, f (y k) - c) 2 P := hSmem.sub (memLp_const c)
  rw [lintegral_enorm_sq_eq_ofReal hSc]
  have hmean : ∫ y, ∑ k, f (y k) ∂P = ∑ k, ∫ z, f z ∂(P.map (fun y => y k)) := by
    rw [integral_finsetSum _ fun k _ => hfi k]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_map (measurable_pi_apply k).aemeasurable hf.aestronglyMeasurable]
  have e1 := variance_eq_sub hSc
  have e2 : variance (fun y : Fin n → E => ∑ k, f (y k) - c) P = variance (fun y : Fin n → E => ∑ k, f (y k)) P :=
    variance_sub_const hS.aestronglyMeasurable c
  have hint : ∫ y, (∑ k, f (y k) - c) ^ 2 ∂P
      = variance (fun y : Fin n → E => ∑ k, f (y k)) P + (∫ y, ∑ k, f (y k) ∂P - c) ^ 2 := by
    have := e1
    simp only [Pi.pow_apply] at this
    rw [integral_sub (hSmem.integrable (by norm_num)) (integrable_const c)] at this
    have hc : ∫ _y, c ∂P = c := by simp
    rw [hc] at this
    rw [e2] at this
    linarith
  rw [hint, hmean, ENNReal.ofReal_add (variance_nonneg _ _) (sq_nonneg _), ofReal_variance hSmem]
  gcongr

end SecondMoment


/-! ### The row second moment -/

section Row

variable {μ : Measure (Torus d)} [IsProbabilityMeasure μ]

theorem sum_erase_insertAt {E : Type*} [MeasurableSpace E] {n : ℕ} (i : Fin (n + 1)) (x : E) (y : Fin n → E) (u : E → ℝ) :
    ∑ j ∈ Finset.univ.erase i, u (insertAt i x y j) = ∑ k, u (y k) := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ i), Fin.sum_univ_succAbove _ i]
  simp

/-- **Row second moment** (`A:eq:outer-row`, pinned): if for every pin value `x` the variance integral
`∫ |h_c(x,y)|² e^{M'+βγ+ψ_x(y)} dμ(y) ≤ 𝒱` (with the retained pin factor inside `ψ_x`) and the mean
`|∑_k ∫ h_c(x,·) dπ^x_k - H(x)| ≤ 𝓜`, then `E_R |row_i|² ≤ 2n 𝒱 + 𝓜²`. -/
theorem row_lintegral_le (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} [NeZero n]
    (hκ : weakKappa V β ≤ 1 / 2) {h : Torus d → Torus d → ℝ} (hm : Measurable (Function.uncurry h))
    (π : Measure (Torus d)) [IsProbabilityMeasure π] (i : Fin (n + 1)) {𝒱 : ℝ≥0∞} {𝓜 : ℝ}
    (hV : ∀ x, ∫⁻ y, ‖cK h π x y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
        pinField V (β / ((n + 1 : ℕ) : ℝ)) (pinsWith (fun e : Empty => e.elim) x) y)) ∂μ ≤ 𝒱)
    (hM : ∀ x, |∑ k : Fin n, ∫ y, cK h π x y ∂((pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) n
        (pinsWith (fun e : Empty => e.elim) x)).map (fun Y => Y k)) - Hc h π x| ≤ 𝓜) :
    ∫⁻ Y, ‖rowFun h π i Y‖ₑ ^ 2 ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim))
      ≤ ENNReal.ofReal (2 * n) * 𝒱 + ENNReal.ofReal (𝓜 ^ 2) := by
  have hN0 : 0 < n + 1 := Nat.succ_pos n
  have hlam : 0 ≤ β / ((n + 1 : ℕ) : ℝ) := div_nonneg hβ (Nat.cast_nonneg _)
  have hΦ : Measurable fun Y : Fin (n + 1) → Torus d => ‖rowFun h π i Y‖ₑ ^ 2 :=
    (measurable_rowFun hm π i).enorm.pow_const 2
  rw [lintegral_pinned_succ V hlam (fun e : Empty => e.elim) i hΦ]
  have hx : ∀ x : Torus d, ∫⁻ y, ‖rowFun h π i (insertAt i x y)‖ₑ ^ 2
      ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) n (pinsWith (fun e : Empty => e.elim) x))
      ≤ ENNReal.ofReal (2 * n) * 𝒱 + ENNReal.ofReal (𝓜 ^ 2) := by
    intro x
    have hrow : ∀ y : Fin n → Torus d, rowFun h π i (insertAt i x y) = ∑ k, cK h π x (y k) - Hc h π x := by
      intro y
      unfold rowFun
      rw [insertAt_same, sum_erase_insertAt i x y (fun z => cK h π x z)]
    simp_rw [hrow]
    have hcm : Measurable (cK h π x) := by
      unfold cK
      have hH := measurable_Hc hm π
      exact ((measurable_h_x hm x).sub measurable_const |>.sub hH).add measurable_const
    have hcard : n + Fintype.card (Option Empty) ≤ n + 1 := by simp
    refine (second_moment_pinned (B := Option Empty) V hβ (N := n + 1) hN0 hcard
      (pinsWith (fun e : Empty => e.elim) x) hκ hcm (Hc h π x)).trans ?_
    refine add_le_add (mul_le_mul' le_rfl (hV x)) (ENNReal.ofReal_le_ofReal ?_)
    have := abs_le.1 (hM x)
    exact sq_le_sq' this.1 this.2
  calc ∫⁻ x, pinWeight V (β / ((n + 1 : ℕ) : ℝ)) (fun e : Empty => e.elim) n x *
        ∫⁻ y, ‖rowFun h π i (insertAt i x y)‖ₑ ^ 2
          ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) n (pinsWith (fun e : Empty => e.elim) x)) ∂μ
      ≤ ∫⁻ x, pinWeight V (β / ((n + 1 : ℕ) : ℝ)) (fun e : Empty => e.elim) n x *
        (ENNReal.ofReal (2 * n) * 𝒱 + ENNReal.ofReal (𝓜 ^ 2)) ∂μ :=
        lintegral_mono fun x => mul_le_mul' le_rfl (hx x)
    _ ≤ ENNReal.ofReal (2 * n) * 𝒱 + ENNReal.ofReal (𝓜 ^ 2) := by
        by_cases hC : ENNReal.ofReal (2 * n) * 𝒱 + ENNReal.ofReal (𝓜 ^ 2) = ⊤
        · rw [hC]; exact le_top
        · rw [lintegral_mul_const' _ _ hC, lintegral_pinWeight V hlam (fun e : Empty => e.elim) i (0 : Fin n),
            one_mul]

end Row

end QuadWeak

/-! ## Part `QuadRow` -/

section QuadRow

open Function



open HRS HRS.External HRS.External.RefMarg HRS.External.PoleVar

variable {d : ℕ} {s : ℝ}

/-! ### Transfer of translation-kernel integrals to dominated measures -/

section Transfer

/-- `∫ F(x - y) dν(y) ≤ Cp Λ ∫ F` for `ν ≤ Cp · ρ dx`, `ρ ≤ Λ`. -/
theorem lintegral_sub_le {ρ : Torus d → ℝ} {Λ : ℝ} (hΛ : ∀ y, ρ y ≤ Λ) {ν : Measure (Torus d)} {Cp : ℝ}
    (hν : ν ≤ ENNReal.ofReal Cp • withDensityReal ρ) (F : Torus d → ℝ≥0∞) (x : Torus d) :
    ∫⁻ y, F (x - y) ∂ν ≤ ENNReal.ofReal Cp * (ENNReal.ofReal Λ * ∫⁻ y, F y) := by
  calc ∫⁻ y, F (x - y) ∂ν ≤ ∫⁻ y, F (x - y) ∂(ENNReal.ofReal Cp • withDensityReal ρ) :=
        lintegral_mono' hν le_rfl
    _ = ENNReal.ofReal Cp * ∫⁻ y, F (x - y) ∂(withDensityReal ρ) := by
        rw [lintegral_smul_measure, smul_eq_mul]
    _ ≤ _ := by
        gcongr
        exact KernelAux2.lintegral_conv_le ρ Λ hΛ F x

theorem ae_ne_of_le {ρ : Torus d → ℝ} (hd : 1 ≤ d) {ν : Measure (Torus d)} {Cp : ℝ}
    (hν : ν ≤ ENNReal.ofReal Cp • withDensityReal ρ) (x : Torus d) : ∀ᵐ y ∂ν, y ≠ x := by
  rw [ae_iff]
  have h0 : ν {y | ¬ y ≠ x} = 0 := by
    have : {y : Torus d | ¬ y ≠ x} = {x} := by ext y; simp
    rw [this]
    refine le_antisymm ?_ bot_le
    refine (hν {x}).trans ?_
    rw [Measure.smul_apply, smul_eq_mul, Calib.atomless_withDensityReal hd ρ x, mul_zero]
  exact h0

end Transfer

/-! ### The one-point function `H` -/

section HBound

/-- Bounded `∫ env` against a dominated measure. -/
theorem lintegral_env_le (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ c : ℝ, 0 < c ∧ ∀ {ρ : Torus d → ℝ} {Λ : ℝ}, (∀ y, ρ y ≤ Λ) → 0 ≤ Λ →
      ∀ {ν : Measure (Torus d)} {Cp : ℝ}, ν ≤ ENNReal.ofReal Cp • withDensityReal ρ → 0 ≤ Cp →
      ∀ x : Torus d, ∫⁻ y, ENNReal.ofReal (envT s (x - y)) ∂ν ≤ ENNReal.ofReal (c * Cp * Λ) := by
  obtain ⟨c₃, hc₃, hc⟩ := lintegral_envT_le hd hs0 hsd
  refine ⟨c₃, hc₃, fun {ρ Λ} hΛ hΛ0 {ν Cp} hν hCp x => ?_⟩
  refine (lintegral_sub_le hΛ hν (fun z => ENNReal.ofReal (envT s z)) x).trans ?_
  calc ENNReal.ofReal Cp * (ENNReal.ofReal Λ * ∫⁻ y, ENNReal.ofReal (envT s y))
      ≤ ENNReal.ofReal Cp * (ENNReal.ofReal Λ * ENNReal.ofReal c₃) := by gcongr
    _ = ENNReal.ofReal (c₃ * Cp * Λ) := by
        rw [← ENNReal.ofReal_mul hΛ0, ← ENNReal.ofReal_mul hCp]
        congr 1; ring

/-- `|H(x)| ≤ c B` for `|h| ≤ B e` and `π ≤ Cp μ`. -/
theorem Hc_bound (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ c : ℝ, 0 < c ∧ ∀ {ρ : Torus d → ℝ} {Λ : ℝ}, (∀ y, ρ y ≤ Λ) → 0 ≤ Λ →
      ∀ {π : Measure (Torus d)} {Cp : ℝ}, π ≤ ENNReal.ofReal Cp • withDensityReal ρ → 0 ≤ Cp →
      ∀ {B : ℝ}, 0 ≤ B → ∀ {h : Torus d → Torus d → ℝ},
      (∀ x y, x ≠ y → |h x y| ≤ B * singEnvelope s (Torus.eucDist x y)) →
      ∀ x : Torus d, |Hc h π x| ≤ c * Cp * Λ * B := by
  obtain ⟨c, hc, hcb⟩ := lintegral_env_le hd hs0 hsd
  refine ⟨c, hc, fun {ρ Λ} hΛ hΛ0 {π Cp} hπ hCp {B} hB {h} hh x => ?_⟩
  have hae := ae_ne_of_le (by omega) hπ x
  unfold Hc
  have h1 := norm_integral_le_lintegral_norm (μ := π) (fun y => h x y)
  have h2 : ∫⁻ y, ENNReal.ofReal ‖h x y‖ ∂π ≤ ENNReal.ofReal B * ENNReal.ofReal (c * Cp * Λ) := by
    calc ∫⁻ y, ENNReal.ofReal ‖h x y‖ ∂π
        ≤ ∫⁻ y, ENNReal.ofReal B * ENNReal.ofReal (envT s (x - y)) ∂π := by
          refine lintegral_mono_ae ?_
          filter_upwards [hae] with y hy
          rw [← ENNReal.ofReal_mul hB, Real.norm_eq_abs]
          refine ENNReal.ofReal_le_ofReal ?_
          have := hh x y (Ne.symm hy)
          rw [eucDist_sub] at this
          exact this
      _ = ENNReal.ofReal B * ∫⁻ y, ENNReal.ofReal (envT s (x - y)) ∂π := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ _ := by gcongr; exact hcb hΛ hΛ0 hπ hCp x
  have h3 : (∫⁻ y, ENNReal.ofReal ‖h x y‖ ∂π).toReal ≤ c * Cp * Λ * B := by
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) (h2.trans ?_)
    rw [← ENNReal.ofReal_mul hB]
    refine le_of_eq ?_
    congr 1; ring
  rw [← Real.norm_eq_abs]
  exact h1.trans h3

end HBound


/-! ### The retained-repulsion variance integral -/

section VarInt

/-- **Retained repulsion** (`A:eq:radial` at `t = 1`): if `|f(y)| ≤ b e(x-y)` and the weight satisfies
`ψ(y) ≤ M₀ - λ e(x-y)` (`y ≠ x`), then `∫ |f|² e^{ψ} dμ ≤ c Λ b² e^{M₀} gFun K` for `K ≥ max(1, 2/λ)`. -/
theorem variance_integral_le (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ c : ℝ, 0 < c ∧ ∀ {ρ : Torus d → ℝ} {Λ : ℝ}, (∀ y, ρ y ≤ Λ) → 0 ≤ Λ →
      ∀ {b : ℝ}, 0 ≤ b → ∀ {x : Torus d} {lam K M0 : ℝ}, 0 < lam → 1 ≤ K → 2 / lam ≤ K →
      ∀ {f ψ : Torus d → ℝ}, (∀ y, y ≠ x → |f y| ≤ b * envT s (x - y)) →
        (∀ y, y ≠ x → ψ y ≤ M0 - lam * envT s (x - y)) →
      ∫⁻ y, ‖f y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (ψ y)) ∂(withDensityReal ρ)
        ≤ ENNReal.ofReal (c * Λ * b ^ 2 * Real.exp M0 * gFun d s K) := by
  obtain ⟨c₁, hc₁, hc⟩ := repulsion_integral hd hs0 hsd
  refine ⟨c₁, hc₁, fun {ρ Λ} hΛ hΛ0 {b} hb {x lam K M0} hlam hK1 hK2 {f ψ} hf hψ => ?_⟩
  have hae : ∀ᵐ y ∂(withDensityReal ρ), y ≠ x := ae_ne_pt (Calib.atomless_withDensityReal (by omega) ρ) x
  have hpt : ∀ᵐ y ∂(withDensityReal ρ), ‖f y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (ψ y)) ≤
      ENNReal.ofReal (b ^ 2 * Real.exp M0) *
        ENNReal.ofReal (envT s (x - y) ^ 2 * Real.exp (-lam * envT s (x - y))) := by
    filter_upwards [hae] with y hy
    have h1 := hf y hy
    have h2 := hψ y hy
    have e : ‖f y‖ₑ ^ 2 = ENNReal.ofReal (f y ^ 2) := by
      rw [← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]
    rw [e, ← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have he0 : 0 ≤ envT s (x - y) := zero_le_one.trans (one_le_envT _)
    have h3 : f y ^ 2 ≤ b ^ 2 * envT s (x - y) ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg _) h1 2
      rwa [mul_pow, sq_abs] at this
    have h4 : Real.exp (ψ y) ≤ Real.exp M0 * Real.exp (-lam * envT s (x - y)) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith)
    calc f y ^ 2 * Real.exp (ψ y) ≤ (b ^ 2 * envT s (x - y) ^ 2) * (Real.exp M0 * Real.exp (-lam * envT s (x - y))) :=
          mul_le_mul h3 h4 (Real.exp_pos _).le (by positivity)
      _ = _ := by ring
  calc ∫⁻ y, ‖f y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (ψ y)) ∂(withDensityReal ρ)
      ≤ ∫⁻ y, ENNReal.ofReal (b ^ 2 * Real.exp M0) *
        ENNReal.ofReal (envT s (x - y) ^ 2 * Real.exp (-lam * envT s (x - y))) ∂(withDensityReal ρ) :=
        lintegral_mono_ae hpt
    _ = ENNReal.ofReal (b ^ 2 * Real.exp M0) *
        ∫⁻ y, ENNReal.ofReal (envT s (x - y) ^ 2 * Real.exp (-lam * envT s (x - y))) ∂(withDensityReal ρ) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (b ^ 2 * Real.exp M0) * (ENNReal.ofReal Λ * ENNReal.ofReal (c₁ * gFun d s K)) := by
        gcongr
        exact hc ρ Λ hΛ lam K hlam hK1 hK2 x
    _ = _ := by
        rw [← ENNReal.ofReal_mul hΛ0, ← ENNReal.ofReal_mul (by positivity)]
        congr 1; ring

end VarInt


/-! ### The mean of a row: near part by bounded densities, far part by total variation -/

section Mean

/-- Tail of the envelope: `∫_{e > K} e ≤ c K^{1-p}`. -/
theorem env_tail_lintegral (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ c : ℝ, 0 < c ∧ ∀ K : ℝ, 1 ≤ K →
      ∫⁻ z : Torus d, {z : Torus d | K < envT s z}.indicator (fun z => ENNReal.ofReal (envT s z)) z
        ≤ ENNReal.ofReal (c * K ^ (1 - pOf d s)) := by
  obtain ⟨c₂, hc₂, hc2⟩ := lintegral_tail_envT hd hs0 hsd
  obtain ⟨K0, hK0, hvol⟩ := volume_envT_gt hd hs0 hsd
  refine ⟨c₂ + K0, by positivity, fun K hK => ?_⟩
  have hK0' : 0 < K := by linarith
  have hmeas : MeasurableSet {z : Torus d | K < envT s z} := measurableSet_lt measurable_const measurable_envT
  have hpt : ∀ z : Torus d, {z : Torus d | K < envT s z}.indicator (fun z => ENNReal.ofReal (envT s z)) z
      ≤ ENNReal.ofReal (envT s z - K) + ENNReal.ofReal K * {z : Torus d | K < envT s z}.indicator 1 z := by
    intro z
    by_cases hz : K < envT s z
    · rw [Set.indicator_of_mem (show z ∈ {z : Torus d | K < envT s z} from hz),
        Set.indicator_of_mem (show z ∈ {z : Torus d | K < envT s z} from hz)]
      simp only [Pi.one_apply, mul_one]
      calc ENNReal.ofReal (envT s z) = ENNReal.ofReal ((envT s z - K) + K) := by congr 1; ring
        _ ≤ _ := ENNReal.ofReal_add_le
    · rw [Set.indicator_of_notMem (show z ∉ {z : Torus d | K < envT s z} from hz)]
      exact bot_le
  have hmI : Measurable ({z : Torus d | K < envT s z}.indicator (1 : Torus d → ℝ≥0∞)) :=
    measurable_const.indicator hmeas
  calc ∫⁻ z : Torus d, {z : Torus d | K < envT s z}.indicator (fun z => ENNReal.ofReal (envT s z)) z
      ≤ ∫⁻ z : Torus d, (ENNReal.ofReal (envT s z - K) +
          ENNReal.ofReal K * {z : Torus d | K < envT s z}.indicator 1 z) := lintegral_mono hpt
    _ = (∫⁻ z : Torus d, ENNReal.ofReal (envT s z - K)) +
          ENNReal.ofReal K * volume {z : Torus d | K < envT s z} := by
        rw [lintegral_add_right _ (hmI.const_mul _), lintegral_const_mul _ hmI, lintegral_indicator_one hmeas]
    _ ≤ ENNReal.ofReal (c₂ * K ^ (1 - pOf d s)) + ENNReal.ofReal K * ENNReal.ofReal (K0 * K ^ (-(pOf d s))) := by
        gcongr
        · exact hc2 K hK0'
        · exact hvol K hK0'
    _ = ENNReal.ofReal ((c₂ + K0) * K ^ (1 - pOf d s)) := by
        have e : K * (K0 * K ^ (-(pOf d s))) = K0 * K ^ (1 - pOf d s) := by
          rw [show (1 : ℝ) - pOf d s = 1 + -(pOf d s) by ring, Real.rpow_add hK0', Real.rpow_one]; ring
        rw [← ENNReal.ofReal_mul hK0'.le, e, ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring


/-- Integrability of a function with the envelope bound against a dominated measure. -/
theorem integrable_of_env_bound (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∀ {ρ : Torus d → ℝ} {Λ : ℝ}, (∀ y, ρ y ≤ Λ) → 0 ≤ Λ → ∀ {ν : Measure (Torus d)} {Cp : ℝ},
      ν ≤ ENNReal.ofReal Cp • withDensityReal ρ → 0 ≤ Cp → ∀ {b : ℝ}, 0 ≤ b → ∀ {x : Torus d}
      {f : Torus d → ℝ}, Measurable f → (∀ y, y ≠ x → |f y| ≤ b * envT s (x - y)) → Integrable f ν := by
  obtain ⟨c, hc, hcb⟩ := lintegral_env_le hd hs0 hsd
  intro ρ Λ hΛ hΛ0 ν Cp hν hCp b hb x f hfm hf
  refine ⟨hfm.aestronglyMeasurable, ?_⟩
  have hae := ae_ne_of_le (by omega) hν x
  have : ∫⁻ y, ‖f y‖ₑ ∂ν ≤ ENNReal.ofReal b * ENNReal.ofReal (c * Cp * Λ) := by
    calc ∫⁻ y, ‖f y‖ₑ ∂ν ≤ ∫⁻ y, ENNReal.ofReal b * ENNReal.ofReal (envT s (x - y)) ∂ν := by
          refine lintegral_mono_ae ?_
          filter_upwards [hae] with y hy
          rw [← ENNReal.ofReal_mul hb, Real.enorm_eq_ofReal_abs]
          exact ENNReal.ofReal_le_ofReal (hf y hy)
      _ = ENNReal.ofReal b * ∫⁻ y, ENNReal.ofReal (envT s (x - y)) ∂ν := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ _ := by gcongr; exact hcb hΛ hΛ0 hν hCp x
  exact lt_of_le_of_lt this (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)

/-- The far part of the row mean: `∫ |f 1_{e > K}| dν ≤ c Cp Λ b K^{1-p}`. -/
theorem tail_integral_le (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ c : ℝ, 0 < c ∧ ∀ {ρ : Torus d → ℝ} {Λ : ℝ}, (∀ y, ρ y ≤ Λ) → 0 ≤ Λ →
      ∀ {ν : Measure (Torus d)} {Cp : ℝ}, ν ≤ ENNReal.ofReal Cp • withDensityReal ρ → 0 ≤ Cp →
      ∀ {b : ℝ}, 0 ≤ b → ∀ {x : Torus d} {K : ℝ}, 1 ≤ K → ∀ {f : Torus d → ℝ},
      (∀ y, y ≠ x → |f y| ≤ b * envT s (x - y)) →
      ∫⁻ y, ENNReal.ofReal ‖{y : Torus d | y ≠ x ∧ envT s (x - y) ≤ K}ᶜ.indicator f y‖ ∂ν
        ≤ ENNReal.ofReal (c * Cp * Λ * b * K ^ (1 - pOf d s)) := by
  obtain ⟨c, hc, hcb⟩ := env_tail_lintegral hd hs0 hsd
  refine ⟨c, hc, fun {ρ Λ} hΛ hΛ0 {ν Cp} hν hCp {b} hb {x K} hK {f} hf => ?_⟩
  have hae := ae_ne_of_le (by omega) hν x
  set F : Torus d → ℝ≥0∞ := {z : Torus d | K < envT s z}.indicator (fun z => ENNReal.ofReal (envT s z)) with hF
  have hpt : ∀ᵐ y ∂ν, ENNReal.ofReal ‖{y : Torus d | y ≠ x ∧ envT s (x - y) ≤ K}ᶜ.indicator f y‖
      ≤ ENNReal.ofReal b * F (x - y) := by
    filter_upwards [hae] with y hy
    by_cases hyT : y ∈ {y : Torus d | y ≠ x ∧ envT s (x - y) ≤ K}
    · rw [Set.indicator_of_notMem (by simpa using hyT)]
      simp
    · have hK' : K < envT s (x - y) := by
        by_contra hcon
        exact hyT ⟨hy, not_lt.1 hcon⟩
      rw [Set.indicator_of_mem (show y ∈ {y : Torus d | y ≠ x ∧ envT s (x - y) ≤ K}ᶜ from hyT)]
      rw [hF, Set.indicator_of_mem (show x - y ∈ {z : Torus d | K < envT s z} from hK'), ← ENNReal.ofReal_mul hb]
      exact ENNReal.ofReal_le_ofReal (by rw [Real.norm_eq_abs]; exact hf y hy)
  calc ∫⁻ y, ENNReal.ofReal ‖{y : Torus d | y ≠ x ∧ envT s (x - y) ≤ K}ᶜ.indicator f y‖ ∂ν
      ≤ ∫⁻ y, ENNReal.ofReal b * F (x - y) ∂ν := lintegral_mono_ae hpt
    _ = ENNReal.ofReal b * ∫⁻ y, F (x - y) ∂ν := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal b * (ENNReal.ofReal Cp * (ENNReal.ofReal Λ * ∫⁻ y, F y)) := by
        gcongr
        exact lintegral_sub_le hΛ hν F x
    _ ≤ ENNReal.ofReal b * (ENNReal.ofReal Cp * (ENNReal.ofReal Λ * ENNReal.ofReal (c * K ^ (1 - pOf d s)))) := by
        gcongr
        exact hcb K hK
    _ = _ := by
        rw [← ENNReal.ofReal_mul hΛ0, ← ENNReal.ofReal_mul hCp, ← ENNReal.ofReal_mul hb]
        congr 1; ring


/-- **Mean of the row, one coordinate**: near part by the bounded densities, far part by the
total-variation closeness `ε` of `ν` to `π`. -/
theorem mean_one_le (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ c : ℝ, 0 < c ∧ ∀ {ρ : Torus d → ℝ} {Λ : ℝ}, (∀ y, ρ y ≤ Λ) → 0 ≤ Λ → ∀ {Cp : ℝ}, 0 ≤ Cp →
      ∀ {b : ℝ}, 0 ≤ b → ∀ {x : Torus d} {ε K : ℝ}, 0 ≤ ε → 1 ≤ K →
      ∀ {π ν : Measure (Torus d)} [IsProbabilityMeasure π] [IsProbabilityMeasure ν],
      π ≤ ENNReal.ofReal Cp • withDensityReal ρ → ν ≤ ENNReal.ofReal Cp • withDensityReal ρ →
      (∀ A : Set (Torus d), MeasurableSet A → |ν.real A - π.real A| ≤ ε) →
      ∀ {f : Torus d → ℝ}, Measurable f → (∀ y, y ≠ x → |f y| ≤ b * envT s (x - y)) →
      |∫ y, f y ∂ν - ∫ y, f y ∂π| ≤ 2 * b * K * ε + 2 * (c * Cp * Λ * b * K ^ (1 - pOf d s)) := by
  obtain ⟨c, hc, hct⟩ := tail_integral_le hd hs0 hsd
  refine ⟨c, hc, fun {ρ Λ} hΛ hΛ0 {Cp} hCp {b} hb {x ε K} hε hK {π ν} _ _ hπ hν hTV {f} hfm hf => ?_⟩
  set T : Set (Torus d) := {y : Torus d | y ≠ x ∧ envT s (x - y) ≤ K} with hT
  have hTm : MeasurableSet T :=
    (measurableSet_singleton x).compl.inter (measurableSet_le (measurable_envT.comp (measurable_const.sub measurable_id)) measurable_const)
  set f1 : Torus d → ℝ := T.indicator f with hf1
  set f2 : Torus d → ℝ := Tᶜ.indicator f with hf2
  have hsplit : ∀ y, f y = f1 y + f2 y := fun y => by
    have := congrFun (Set.indicator_self_add_compl T f) y
    exact this.symm
  have hf1m : Measurable f1 := hfm.indicator hTm
  have hf2m : Measurable f2 := hfm.indicator hTm.compl
  have hf1b : ∀ y, |f1 y| ≤ b * K := by
    intro y
    by_cases hy : y ∈ T
    · rw [hf1, Set.indicator_of_mem hy]
      exact (hf y hy.1).trans (mul_le_mul_of_nonneg_left hy.2 hb)
    · rw [hf1, Set.indicator_of_notMem hy]; simp; positivity
  have hfi : ∀ (κ : Measure (Torus d)), κ ≤ ENNReal.ofReal Cp • withDensityReal ρ → Integrable f κ :=
    fun κ hκ => integrable_of_env_bound hd hs0 hsd hΛ hΛ0 hκ hCp hb hfm hf
  have hf1i : ∀ (κ : Measure (Torus d)) [IsProbabilityMeasure κ], Integrable f1 κ := fun κ _ =>
    Integrable.of_bound hf1m.aestronglyMeasurable (b * K) (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hf1b y)
  have hf2i : ∀ (κ : Measure (Torus d)), κ ≤ ENNReal.ofReal Cp • withDensityReal ρ → Integrable f2 κ :=
    fun κ hκ => (hfi κ hκ).indicator hTm.compl
  have hint : ∀ (κ : Measure (Torus d)) [IsProbabilityMeasure κ], κ ≤ ENNReal.ofReal Cp • withDensityReal ρ →
      ∫ y, f y ∂κ = ∫ y, f1 y ∂κ + ∫ y, f2 y ∂κ := by
    intro κ _ hκ
    rw [← integral_add (hf1i κ) (hf2i κ hκ)]
    exact integral_congr_ae (Filter.Eventually.of_forall hsplit)
  have htail : ∀ (κ : Measure (Torus d)), κ ≤ ENNReal.ofReal Cp • withDensityReal ρ →
      |∫ y, f2 y ∂κ| ≤ c * Cp * Λ * b * K ^ (1 - pOf d s) := by
    intro κ hκ
    have h1 := norm_integral_le_lintegral_norm (μ := κ) f2
    have h2 := hct hΛ hΛ0 hκ hCp hb hK hf
    rw [← Real.norm_eq_abs]
    refine h1.trans (ENNReal.toReal_le_of_le_ofReal (by positivity) h2)
  have hD : 0 ≤ 2 * b * K := by positivity
  have h1 := abs_integral_sub_le_of_tv ν π (c := ε) (D := 2 * b * K) hD hTV hf1m (h := f1) (fun z z' => by
    have h1 := abs_le.1 (hf1b z)
    have h2 := abs_le.1 (hf1b z')
    rw [abs_le]; constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2])
  rw [hint ν hν, hint π hπ]
  have e : ∫ y, f1 y ∂ν + ∫ y, f2 y ∂ν - (∫ y, f1 y ∂π + ∫ y, f2 y ∂π)
      = (∫ y, f1 y ∂ν - ∫ y, f1 y ∂π) + ∫ y, f2 y ∂ν - ∫ y, f2 y ∂π := by ring
  rw [e]
  have h3 := htail ν hν
  have h4 := htail π hπ
  have h5 := abs_le.1 h1
  have h6 := abs_le.1 h3
  have h7 := abs_le.1 h4
  rw [abs_le]
  constructor <;> nlinarith [h5.1, h5.2, h6.1, h6.2, h7.1, h7.2, mul_comm ε (2 * b * K)]

end Mean

/-! ### Assembly for the weak ensemble -/

section Assembly

variable {μ : Measure (Torus d)} [IsProbabilityMeasure μ]

/-- `N Var_R[D_N(h;π)] ≤ (8/N²)(2n 𝒱 + 𝓜²)` from the row bounds. -/
theorem quad_reference_le (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} [NeZero n]
    (hκ : weakKappa V β ≤ 1 / 2) {h : Torus d → Torus d → ℝ} (hm : Measurable (Function.uncurry h))
    (hsym : ∀ x y, h x y = h y x) (π : Measure (Torus d)) [IsProbabilityMeasure π] {𝒱 : ℝ≥0∞} {𝓜 : ℝ}
    (hV : ∀ x, ∫⁻ y, ‖cK h π x y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
        pinField V (β / ((n + 1 : ℕ) : ℝ)) (pinsWith (fun e : Empty => e.elim) x) y)) ∂μ ≤ 𝒱)
    (hM : ∀ x, |∑ k : Fin n, ∫ y, cK h π x y ∂((pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) n
        (pinsWith (fun e : Empty => e.elim) x)).map (fun Y => Y k)) - Hc h π x| ≤ 𝓜) :
    ((n + 1 : ℕ) : ℝ≥0∞) * evariance (fun X : Config d (n + 1) => quadStat h π X)
        (pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim))
      ≤ ENNReal.ofReal (8 / ((n + 1 : ℕ) : ℝ) ^ 2) * (ENNReal.ofReal (2 * n) * 𝒱 + ENNReal.ofReal (𝓜 ^ 2)) := by
  have hN0 : 0 < n + 1 := Nat.succ_pos n
  have hN' : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hN0
  have h1 := evariance_quad_le V hβ hN0 hκ hm hsym π
  have h2 : ∀ i : Fin (n + 1), ∫⁻ Y, ‖rowFun h π i Y‖ₑ ^ 2
      ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim))
      ≤ ENNReal.ofReal (2 * n) * 𝒱 + ENNReal.ofReal (𝓜 ^ 2) :=
    fun i => row_lintegral_le V hβ hκ hm π i hV hM
  set Ω := ENNReal.ofReal (2 * n) * 𝒱 + ENNReal.ofReal (𝓜 ^ 2) with hΩ
  calc ((n + 1 : ℕ) : ℝ≥0∞) * evariance (fun X : Config d (n + 1) => quadStat h π X)
        (pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim))
      ≤ ((n + 1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal (8 / ((n + 1 : ℕ) : ℝ) ^ 4) *
          ∑ i : Fin (n + 1), Ω) := by
        gcongr
        refine h1.trans ?_
        gcongr with i _
        exact h2 i
    _ = ENNReal.ofReal (8 / ((n + 1 : ℕ) : ℝ) ^ 2) * Ω := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have e : ((n + 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((n + 1 : ℕ) : ℝ) := (ENNReal.ofReal_natCast _).symm
        rw [e, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul hN'.le, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        field_simp

/-- **Pair second moment** under the weak ensemble (no smallness needed): by disintegration at
coordinate `a`, the pair `(y_a, y_b)` has second moment of `h` bounded by the per-pin integral. -/
theorem pair_lintegral_le (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (a b : Fin (n + 1)) (hab : a ≠ b)
    {h : Torus d → Torus d → ℝ} (hm : Measurable (Function.uncurry h)) {𝒲 : ℝ≥0∞}
    (hW : ∀ x, ∫⁻ z, ‖h x z‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
        pinField V (β / ((n + 1 : ℕ) : ℝ)) (pinsWith (fun e : Empty => e.elim) x) z)) ∂μ ≤ 𝒲) :
    ∫⁻ Y, ‖h (Y a) (Y b)‖ₑ ^ 2 ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)) ≤ 𝒲 := by
  have hN0 : 0 < n + 1 := Nat.succ_pos n
  have hlam : 0 ≤ β / ((n + 1 : ℕ) : ℝ) := div_nonneg hβ (Nat.cast_nonneg _)
  obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hab.symm
  have hΦ : Measurable fun Y : Fin (n + 1) → Torus d => ‖h (Y a) (Y b)‖ₑ ^ 2 :=
    ((measurable_h_pair hm a b).enorm).pow_const 2
  rw [lintegral_pinned_succ V hlam (fun e : Empty => e.elim) a hΦ]
  have hx : ∀ x : Torus d, ∫⁻ y, ‖h (insertAt a x y a) (insertAt a x y b)‖ₑ ^ 2
      ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) n (pinsWith (fun e : Empty => e.elim) x)) ≤ 𝒲 := by
    intro x
    have e : ∀ y : Fin n → Torus d, ‖h (insertAt a x y a) (insertAt a x y b)‖ₑ ^ 2 = ‖h x (y k)‖ₑ ^ 2 := by
      intro y
      rw [insertAt_same, ← hk, insertAt_succAbove]
    simp_rw [e]
    have hcard : n + Fintype.card (Option Empty) ≤ n + 1 := by simp
    have hmeas : Measurable fun z => ‖h x z‖ₑ ^ 2 := ((measurable_h_x hm x).enorm).pow_const 2
    have hdom := pinned_marginal_le_density (B := Option Empty) V hβ hN0 (n := n) hcard
      (pinsWith (fun e : Empty => e.elim) x) k
    calc ∫⁻ y, ‖h x (y k)‖ₑ ^ 2 ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) n (pinsWith (fun e : Empty => e.elim) x))
        = ∫⁻ z, ‖h x z‖ₑ ^ 2 ∂((pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) n
            (pinsWith (fun e : Empty => e.elim) x)).map (fun Y => Y k)) := by
          rw [lintegral_map hmeas (measurable_pi_apply k)]
      _ ≤ ∫⁻ z, ‖h x z‖ₑ ^ 2 ∂(μ.withDensity fun z => ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
            pinField V (β / ((n + 1 : ℕ) : ℝ)) (pinsWith (fun e : Empty => e.elim) x) z))) :=
          lintegral_mono' hdom le_rfl
      _ = ∫⁻ z, ‖h x z‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
            pinField V (β / ((n + 1 : ℕ) : ℝ)) (pinsWith (fun e : Empty => e.elim) x) z)) ∂μ := by
          rw [lintegral_withDensity_eq_lintegral_mul₀]
          · simp only [Pi.mul_apply]
            exact lintegral_congr fun z => mul_comm _ _
          · exact (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
              (measurable_const.add (isField_pinField V hlam _).measurable))).aemeasurable
          · exact hmeas.aemeasurable
      _ ≤ 𝒲 := hW x
  calc ∫⁻ x, pinWeight V (β / ((n + 1 : ℕ) : ℝ)) (fun e : Empty => e.elim) n x *
        ∫⁻ y, ‖h (insertAt a x y a) (insertAt a x y b)‖ₑ ^ 2
          ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) n (pinsWith (fun e : Empty => e.elim) x)) ∂μ
      ≤ ∫⁻ x, pinWeight V (β / ((n + 1 : ℕ) : ℝ)) (fun e : Empty => e.elim) n x * 𝒲 ∂μ :=
        lintegral_mono fun x => mul_le_mul' le_rfl (hx x)
    _ ≤ 𝒲 := by
        by_cases hC : 𝒲 = ⊤
        · rw [hC]; exact le_top
        · rw [lintegral_mul_const' _ _ hC, lintegral_pinWeight V hlam (fun e : Empty => e.elim) a (k : Fin n), one_mul]

end Assembly

/-! ### Exchangeability and the total-variation comparison -/

section TVcmp

variable {μ : Measure (Torus d)} [IsProbabilityMeasure μ]

/-- All one-coordinate marginals of the weak ensemble with no pins coincide. -/
theorem pinned_marginal_eq (V : WeakPotential μ) {lam : ℝ} (hlam : 0 ≤ lam) (n : ℕ) (i j : Fin n) :
    (pinnedLaw V lam n (fun e : Empty => e.elim)).map (fun Y => Y i)
      = (pinnedLaw V lam n (fun e : Empty => e.elim)).map (fun Y => Y j) := by
  have hψ := isField_pinField V hlam (fun e : Empty => e.elim)
  exact map_eval_eq_of_symm μ (pinnedDensity V lam n (fun e : Empty => e.elim))
    (measurable_fieldDensity hψ.measurable V _ n) (fun σ y => fieldDensity_comp_perm V _ _ σ y) i j

/-- **Total-variation comparison** (`A:eq:weak-pin-comparison`): the conditional law of `y_k` given
`y_0 = x` is within `2κ/N` of the one-point marginal `π`. -/
theorem tv_pin_le (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {n : ℕ} (hκ : weakKappa V β ≤ 1 / 2)
    (x : Torus d) (k : Fin n) {A : Set (Torus d)} (hA : MeasurableSet A) :
    |((pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) n (pinsWith (fun e : Empty => e.elim) x)).map (fun Y => Y k)).real A
        - ((pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)).map
            (fun Y => Y 0)).real A| ≤ 2 * weakKappa V β / ((n + 1 : ℕ) : ℝ) := by
  have hlam : 0 ≤ β / ((n + 1 : ℕ) : ℝ) := div_nonneg hβ (Nat.cast_nonneg _)
  have h := rvh_pin_comparison (B := Empty) V hβ (N := n + 1) (n := n) (Nat.succ_pos n) (by simp)
    (fun e : Empty => e.elim) hκ (0 : Fin (n + 1)) k x hA
  rw [pinned_marginal_eq V hlam (n + 1) ((0 : Fin (n + 1)).succAbove k) 0] at h
  exact h

end TVcmp

/-! ### Arithmetic of the rates -/

section Arith

theorem rpow_two_div_le (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {N : ℝ} (hN : 1 ≤ N) :
    N ^ (2 / pOf d s) ≤ N * gFun d s N := by
  have hN0 : 0 < N := by linarith
  have hg1 := one_le_gFun hd hs0 hsd hN
  rcases pOf_cases hd hs0 hsd with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
  · have hg : gFun d s N = 1 := by unfold gFun; simp [h1]
    rw [hg, mul_one]
    calc N ^ (2 / pOf d s) ≤ N ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN (by rw [div_le_one (by linarith)]; linarith)
      _ = N := Real.rpow_one N
  · have : 2 / pOf d s = 1 := by rw [h2]; norm_num
    rw [this, Real.rpow_one]
    nlinarith
  · have hs : 0 < s := by
      have : (0 : ℝ) < d / 2 := by
        have : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
        positivity
      linarith
    have hg : gFun d s N = N ^ (2 - (d : ℝ) / s) := by
      unfold gFun
      have h4 : ¬ s < (d : ℝ) / 2 := by linarith
      have h5 : s ≠ (d : ℝ) / 2 := by linarith
      simp [h4, h5]
    have hp1 := one_lt_pOf hd hs0 hsd
    rw [hg, ← h2, ← Real.rpow_one_add' hN0.le (by linarith [h3])]
    refine Real.rpow_le_rpow_of_exponent_le hN ?_
    rw [div_le_iff₀ (by linarith)]
    nlinarith [mul_pos (sub_pos.2 hp1) (sub_pos.2 h3)]

end Arith

/-! ### Centered kernel: zero mean and envelope -/

section Centered

theorem integral_cK_eq_zero {h : Torus d → Torus d → ℝ} (π : Measure (Torus d)) [IsProbabilityMeasure π]
    (x : Torus d) (hh : Integrable (h x) π) (hHi : Integrable (Hc h π) π) :
    ∫ y, cK h π x y ∂π = 0 := by
  unfold cK
  have e1 : ∫ y, (h x y - Hc h π x - Hc h π y + h0c h π) ∂π
      = (∫ y, h x y ∂π) - Hc h π x - ∫ y, Hc h π y ∂π + h0c h π := by
    have i1 : Integrable (fun y => h x y - Hc h π x) π := hh.sub (integrable_const _)
    have i2 : Integrable (fun y => h x y - Hc h π x - Hc h π y) π := i1.sub hHi
    rw [integral_add i2 (integrable_const _), integral_sub i1 hHi, integral_sub hh (integrable_const _)]
    simp
  rw [e1]
  unfold h0c Hc
  ring

theorem abs_h0c_le {h : Torus d → Torus d → ℝ} (π : Measure (Torus d)) [IsProbabilityMeasure π] {HB : ℝ}
    (hHB : ∀ x, |Hc h π x| ≤ HB) : |h0c h π| ≤ HB := by
  have : h0c h π = ∫ x, Hc h π x ∂π := rfl
  rw [this, ← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (C := HB) (Filter.Eventually.of_forall fun x => ?_)).trans (by simp)
  rw [Real.norm_eq_abs]; exact hHB x

theorem abs_cK_le {h : Torus d → Torus d → ℝ} (π : Measure (Torus d)) [IsProbabilityMeasure π] {B HB : ℝ}
    (hB : 0 ≤ B) (hHB : ∀ x, |Hc h π x| ≤ HB)
    (hh : ∀ x y, x ≠ y → |h x y| ≤ B * singEnvelope s (Torus.eucDist x y)) (x y : Torus d) (hxy : y ≠ x) :
    |cK h π x y| ≤ (B + 3 * HB) * envT s (x - y) := by
  unfold cK
  have h1 := hh x y (Ne.symm hxy)
  rw [eucDist_sub] at h1
  have h2 := hHB x
  have h3 := hHB y
  have h4 := abs_h0c_le π hHB
  have he : 1 ≤ envT s (x - y) := one_le_envT _
  have hHB0 : 0 ≤ HB := (abs_nonneg _).trans h2
  have : |h x y - Hc h π x - Hc h π y + h0c h π| ≤ |h x y| + |Hc h π x| + |Hc h π y| + |h0c h π| := by
    calc _ ≤ |h x y - Hc h π x - Hc h π y| + |h0c h π| := abs_add_le _ _
      _ ≤ |h x y - Hc h π x| + |Hc h π y| + |h0c h π| := by gcongr; exact abs_sub _ _
      _ ≤ |h x y| + |Hc h π x| + |Hc h π y| + |h0c h π| := by gcongr; exact abs_sub _ _
  unfold envT at he ⊢
  nlinarith

end Centered

end QuadRow

/-! ## Part `QuadRef` -/

section QuadRef

open Function



open HRS HRS.External HRS.External.RefMarg HRS.External.PoleVar

variable {d : ℕ} {s : ℝ}

theorem rpow_identity {N p : ℝ} (hN : 0 < N) (hp : 0 < p) :
    N * (N ^ (1 / p)) ^ (1 - p) = N ^ (1 / p) := by
  rw [← Real.rpow_mul hN.le, ← Real.rpow_one_add' hN.le]
  · congr 1
    field_simp
    ring
  · have : 1 + 1 / p * (1 - p) = 1 / p := by field_simp; ring
    rw [this]; positivity

set_option maxHeartbeats 1600000 in
theorem quad_weak_bound (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β) (ρ : Torus d → ℝ)
    (hρ : IsProbDensity ρ) {Λ : ℝ} (hΛ : ∀ y, ρ y ≤ Λ) (hΛ0 : 0 ≤ Λ) (Mmax M'max γmax Cq : ℝ)
    (hCq : 0 ≤ Cq) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : WeakPotential (withDensityReal ρ)), V.M ≤ Mmax → V.M' ≤ M'max → V.γ ≤ γmax →
      (∀ x y : Torus d, x ≠ y → envT s (x - y) - Cq ≤ V.q x y) →
      ∀ {n : ℕ}, 1 ≤ n → weakKappa V β ≤ 1 / 2 →
      ∀ (B : ℝ), 0 ≤ B → ∀ (h : Torus d → Torus d → ℝ), Measurable (Function.uncurry h) →
      (∀ x y, h x y = h y x) →
      (∀ x y, x ≠ y → |h x y| ≤ B * singEnvelope s (Torus.eucDist x y)) →
      ((n + 1 : ℕ) : ℝ≥0∞) * evariance (fun X : Config d (n + 1) => quadStat h
          ((pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)).map (fun X => X 0)) X)
          (pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim))
        ≤ ENNReal.ofReal (C * B ^ 2 * deltaN d s (n + 1)) := by
  haveI hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ
  obtain ⟨cH, hcH, hHc⟩ := Hc_bound hd hs0 hsd
  obtain ⟨c₁, hc₁, hvar⟩ := variance_integral_le hd hs0 hsd
  obtain ⟨c₂, hc₂, hmean⟩ := mean_one_le hd hs0 hsd
  set cc : ℝ := max 1 (2 / β) with hcc
  have hcc0 : 0 < cc := lt_max_of_lt_left one_pos
  obtain ⟨cg, hcg, hgm⟩ := gFun_mul_le hd hs0 hsd hcc0
  set γ' : ℝ := max γmax 0 with hγ'
  set Cp : ℝ := Real.exp (Mmax + M'max + β * γ') with hCp
  have hCp0 : 0 < Cp := Real.exp_pos _
  set HB : ℝ := cH * Cp * Λ with hHB
  have hHB0 : 0 ≤ HB := by positivity
  set bb : ℝ := 1 + 3 * HB with hbb
  have hbb1 : 1 ≤ bb := by linarith
  set M0 : ℝ := Mmax + M'max + β * γ' + β * Cq with hM0
  set C6 : ℝ := 2 * bb + 2 * c₂ * Cp * Λ * bb + HB with hC6
  have hC60 : 0 ≤ C6 := by positivity
  refine ⟨16 * c₁ * Λ * bb ^ 2 * Real.exp M0 * cg + 8 * C6 ^ 2 + 1, by positivity, ?_⟩
  intro V hVM hVM' hVγ hq n hn hκ B hB h hm hsym hh
  haveI : NeZero n := ⟨by omega⟩
  have hN0 : 0 < n + 1 := Nat.succ_pos n
  have hNR : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hN0
  have hNpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by linarith
  set lam : ℝ := β / ((n + 1 : ℕ) : ℝ) with hlam
  have hlam0 : 0 < lam := by positivity
  have hlamβ : lam ≤ β := by
    rw [hlam, div_le_iff₀ hNpos]; exact le_mul_of_one_le_right hβ.le hNR
  set R := pinnedLaw V lam (n + 1) (fun e : Empty => e.elim) with hR
  haveI hRp : IsProbabilityMeasure R := isProb_pinnedLaw V hlam0.le (n + 1) _
  set π : Measure (Torus d) := R.map (fun X => X 0) with hπ
  haveI hπp : IsProbabilityMeasure π := inferInstance
  have hVC : Real.exp (V.M + V.M' + β * V.γ) ≤ Cp := by
    refine Real.exp_le_exp.2 ?_
    have h1 : β * V.γ ≤ β * γ' := mul_le_mul_of_nonneg_left (hVγ.trans (le_max_left _ _)) hβ.le
    linarith
  have hπle : π ≤ ENNReal.ofReal Cp • withDensityReal ρ := by
    have h1 := marginal_le_smul (B := Empty) V hβ.le hN0 (n := n + 1) (by simp) (fun e : Empty => e.elim) 0
    refine h1.trans ?_
    refine Measure.le_iff'.2 fun A => ?_
    simp only [Measure.smul_apply, smul_eq_mul]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal hVC) le_rfl
  have hνle : ∀ (x : Torus d) (k : Fin n), (pinnedLaw V lam n (pinsWith (fun e : Empty => e.elim) x)).map
      (fun Y => Y k) ≤ ENNReal.ofReal Cp • withDensityReal ρ := by
    intro x k
    have h1 := pinned_marginal_le_density (B := Option Empty) V hβ.le hN0 (n := n)
      (by simp) (pinsWith (fun e : Empty => e.elim) x) k
    refine Measure.le_iff.2 fun A hA => (h1 A).trans ?_
    rw [withDensity_apply _ hA, Measure.smul_apply, smul_eq_mul]
    calc ∫⁻ z in A, ENNReal.ofReal (Real.exp (V.M' + β * V.γ + pinField V lam
          (pinsWith (fun e : Empty => e.elim) x) z)) ∂(withDensityReal ρ)
        ≤ ∫⁻ _z in A, ENNReal.ofReal Cp ∂(withDensityReal ρ) := by
          refine lintegral_mono fun z => ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
          have h2 := (isField_pinField V hlam0.le (pinsWith (fun e : Empty => e.elim) x)).le z
          have h3 : β * V.γ ≤ β * γ' := mul_le_mul_of_nonneg_left (hVγ.trans (le_max_left _ _)) hβ.le
          linarith
      _ = ENNReal.ofReal Cp * withDensityReal ρ A := by rw [setLIntegral_const, mul_comm]
  -- the one-point function and the centered kernel
  have hHcB : ∀ x, |Hc h π x| ≤ HB * B := fun x => by
    have := hHc hΛ hΛ0 hπle hCp0.le hB hh x
    simpa [hHB] using this
  have hcK : ∀ x y : Torus d, y ≠ x → |cK h π x y| ≤ (bb * B) * envT s (x - y) := by
    intro x y hy
    have := abs_cK_le (s := s) π hB hHcB hh x y hy
    have e : B + 3 * (HB * B) = bb * B := by rw [hbb]; ring
    rwa [e] at this
  have hHm : Measurable (Hc h π) := measurable_Hc hm π
  have hHi : Integrable (Hc h π) π :=
    Integrable.of_bound hHm.aestronglyMeasurable (HB * B) (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hHcB x)
  have hhint : ∀ x, Integrable (h x) π := fun x =>
    integrable_of_env_bound hd hs0 hsd hΛ hΛ0 hπle hCp0.le hB (measurable_h_x hm x) (fun y hy => by
      have := hh x y (Ne.symm hy)
      rwa [eucDist_sub] at this)
  have hzero : ∀ x, ∫ y, cK h π x y ∂π = 0 := fun x => integral_cK_eq_zero π x (hhint x) hHi
  -- the variance integral with retained repulsion
  set N : ℝ := ((n + 1 : ℕ) : ℝ) with hNdef
  have hccN1 : 1 ≤ cc * N := by
    have : 1 ≤ cc := le_max_left _ _
    exact one_le_mul_of_one_le_of_one_le this hNR
  have hccN2 : 2 / lam ≤ cc * N := by
    rw [hlam, div_div_eq_mul_div, div_le_iff₀ hβ]
    have h1 : 2 / β ≤ cc := le_max_right _ _
    have h2 : 2 ≤ cc * β := by
      rw [div_le_iff₀ hβ] at h1; exact h1
    calc 2 * N ≤ (cc * β) * N := mul_le_mul_of_nonneg_right h2 hNpos.le
      _ = cc * N * β := by ring
  have hVx : ∀ x : Torus d, ∫⁻ y, ‖cK h π x y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (V.M' + β * V.γ +
      pinField V lam (pinsWith (fun e : Empty => e.elim) x) y)) ∂(withDensityReal ρ)
      ≤ ENNReal.ofReal (c₁ * Λ * (bb * B) ^ 2 * Real.exp M0 * (cg * gFun d s N)) := by
    intro x
    have h1 := hvar hΛ hΛ0 (b := bb * B) (by positivity) (x := x) (lam := lam) (K := cc * N) (M0 := M0)
      hlam0 hccN1 hccN2 (f := cK h π x) (ψ := fun y => V.M' + β * V.γ +
        pinField V lam (pinsWith (fun e : Empty => e.elim) x) y) (fun y hy => hcK x y hy) (fun y hy => by
        rw [pinField_pinsWith, pinField_empty]
        have h2 := V.φ_le y
        have h3 := hq y x hy
        rw [envT_sub_comm y x] at h3
        have h4 : β * V.γ ≤ β * γ' := mul_le_mul_of_nonneg_left (hVγ.trans (le_max_left _ _)) hβ.le
        have h5 : lam * Cq ≤ β * Cq := mul_le_mul_of_nonneg_right hlamβ hCq
        have h6 : lam * (envT s (x - y) - Cq) ≤ lam * V.q y x := mul_le_mul_of_nonneg_left h3 hlam0.le
        rw [hM0]
        linarith)
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    have h2 := hgm N hNR hccN1
    have h3 : 0 ≤ c₁ * Λ * (bb * B) ^ 2 * Real.exp M0 := by positivity
    calc c₁ * Λ * (bb * B) ^ 2 * Real.exp M0 * gFun d s (cc * N)
        ≤ c₁ * Λ * (bb * B) ^ 2 * Real.exp M0 * (cg * gFun d s N) := mul_le_mul_of_nonneg_left h2 h3
      _ = _ := rfl
  -- the mean of the row
  have hp := one_lt_pOf hd hs0 hsd
  set K : ℝ := N ^ (1 / pOf d s) with hKdef
  have hK1 : 1 ≤ K := Real.one_le_rpow hNR (by positivity)
  set ε : ℝ := 2 * weakKappa V β / N with hεdef
  have hκ0 : 0 ≤ weakKappa V β := weakKappa_nonneg V hβ.le
  have hε0 : 0 ≤ ε := by positivity
  have hNK : N * K ^ (1 - pOf d s) = K := rpow_identity hNpos (by linarith)
  have hcKm : ∀ x, Measurable (cK h π x) := fun x => by
    unfold cK
    exact (((measurable_h_x hm x).sub measurable_const).sub hHm).add measurable_const
  have hMx : ∀ x : Torus d, |∑ k : Fin n, ∫ y, cK h π x y ∂((pinnedLaw V lam n
      (pinsWith (fun e : Empty => e.elim) x)).map (fun Y => Y k)) - Hc h π x| ≤ C6 * B * K := by
    intro x
    have hper : ∀ k : Fin n, |∫ y, cK h π x y ∂((pinnedLaw V lam n (pinsWith (fun e : Empty => e.elim) x)).map
        (fun Y => Y k))| ≤ 2 * (bb * B) * K * ε + 2 * (c₂ * Cp * Λ * (bb * B) * K ^ (1 - pOf d s)) := by
      intro k
      haveI := isProb_pinnedLaw V hlam0.le n (pinsWith (fun e : Empty => e.elim) x)
      have := hmean hΛ hΛ0 hCp0.le (b := bb * B) (by positivity) (x := x) (ε := ε) (K := K) hε0 hK1
        (π := π) (ν := (pinnedLaw V lam n (pinsWith (fun e : Empty => e.elim) x)).map (fun Y => Y k))
        hπle (hνle x k) (fun A hA => tv_pin_le V hβ.le hκ x k hA) (hcKm x) (fun y hy => hcK x y hy)
      rwa [hzero x, sub_zero] at this
    have hsum : |∑ k : Fin n, ∫ y, cK h π x y ∂((pinnedLaw V lam n (pinsWith (fun e : Empty => e.elim) x)).map
        (fun Y => Y k))| ≤ (n : ℝ) * (2 * (bb * B) * K * ε + 2 * (c₂ * Cp * Λ * (bb * B) * K ^ (1 - pOf d s))) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ k : Fin n, |∫ y, cK h π x y ∂((pinnedLaw V lam n (pinsWith (fun e : Empty => e.elim) x)).map
            (fun Y => Y k))| ≤ ∑ _k : Fin n, (2 * (bb * B) * K * ε + 2 * (c₂ * Cp * Λ * (bb * B) * K ^ (1 - pOf d s))) :=
            Finset.sum_le_sum fun k _ => hper k
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hnN : (n : ℝ) ≤ N := by rw [hNdef]; push_cast; linarith
    have hper0 : 0 ≤ 2 * (bb * B) * K * ε + 2 * (c₂ * Cp * Λ * (bb * B) * K ^ (1 - pOf d s)) := by positivity
    have hnper : (n : ℝ) * (2 * (bb * B) * K * ε + 2 * (c₂ * Cp * Λ * (bb * B) * K ^ (1 - pOf d s)))
        ≤ (2 + 2 * c₂ * Cp * Λ) * (bb * B) * K := by
      calc (n : ℝ) * (2 * (bb * B) * K * ε + 2 * (c₂ * Cp * Λ * (bb * B) * K ^ (1 - pOf d s)))
          ≤ N * (2 * (bb * B) * K * ε + 2 * (c₂ * Cp * Λ * (bb * B) * K ^ (1 - pOf d s))) :=
            mul_le_mul_of_nonneg_right hnN hper0
        _ = 2 * (bb * B) * K * (N * ε) + 2 * (c₂ * Cp * Λ * (bb * B)) * (N * K ^ (1 - pOf d s)) := by ring
        _ = 2 * (bb * B) * K * (2 * weakKappa V β) + 2 * (c₂ * Cp * Λ * (bb * B)) * K := by
            rw [hNK, hεdef]; field_simp
        _ ≤ 2 * (bb * B) * K * 1 + 2 * (c₂ * Cp * Λ * (bb * B)) * K := by
            gcongr
            linarith
        _ = _ := by ring
    have hHx : |Hc h π x| ≤ HB * B * K := by
      calc |Hc h π x| ≤ HB * B := hHcB x
        _ ≤ HB * B * K := by
          have : 0 ≤ HB * B := by positivity
          exact le_mul_of_one_le_right this hK1
    calc |∑ k : Fin n, ∫ y, cK h π x y ∂((pinnedLaw V lam n (pinsWith (fun e : Empty => e.elim) x)).map
          (fun Y => Y k)) - Hc h π x|
        ≤ |∑ k : Fin n, ∫ y, cK h π x y ∂((pinnedLaw V lam n (pinsWith (fun e : Empty => e.elim) x)).map
          (fun Y => Y k))| + |Hc h π x| := abs_sub _ _
      _ ≤ (2 + 2 * c₂ * Cp * Λ) * (bb * B) * K + HB * B * K := add_le_add (hsum.trans hnper) hHx
      _ = C6 * B * K := by rw [hC6]; ring
  -- assembly
  have hfin := quad_reference_le V hβ.le hκ hm hsym π
    (𝒱 := ENNReal.ofReal (c₁ * Λ * (bb * B) ^ 2 * Real.exp M0 * (cg * gFun d s N))) (𝓜 := C6 * B * K) hVx hMx
  refine hfin.trans ?_
  have hg1 : 1 ≤ gFun d s N := one_le_gFun hd hs0 hsd hNR
  have hK2 : K ^ 2 ≤ N * gFun d s N := by
    have e : K ^ 2 = N ^ (2 / pOf d s) := by
      rw [hKdef, ← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
      congr 1; push_cast; ring
    rw [e]; exact rpow_two_div_le hd hs0 hsd hNR
  have hδ : deltaN d s (n + 1) = N⁻¹ * gFun d s N := deltaN_eq_gFun hd hs0 hsd hN0
  have hnN : (n : ℝ) ≤ N := by rw [hNdef]; push_cast; linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hδ]
  set g := gFun d s N with hgdef
  set D₁ : ℝ := c₁ * Λ * bb ^ 2 * Real.exp M0 * cg with hD₁
  have hD0 : 0 ≤ D₁ := by positivity
  have e1 : c₁ * Λ * (bb * B) ^ 2 * Real.exp M0 * (cg * g) = D₁ * B ^ 2 * g := by rw [hD₁]; ring
  rw [e1, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  have e2 : (16 * c₁ * Λ * bb ^ 2 * Real.exp M0 * cg + 8 * C6 ^ 2 + 1) * B ^ 2 * (N⁻¹ * g) * N ^ 2
      = (16 * D₁ + 8 * C6 ^ 2 + 1) * B ^ 2 * g * N := by
    rw [hD₁]; field_simp
  rw [e2]
  have h1 : 8 * (2 * (n : ℝ) * (D₁ * B ^ 2 * g) + (C6 * B * K) ^ 2)
      ≤ 8 * (2 * N * (D₁ * B ^ 2 * g) + C6 ^ 2 * B ^ 2 * (N * g)) := by
    have : (C6 * B * K) ^ 2 = C6 ^ 2 * B ^ 2 * K ^ 2 := by ring
    rw [this]
    gcongr
  have h2 : 0 ≤ B ^ 2 * g * N := by positivity
  linarith [h1, h2]

end QuadRef

/-! ## Part `QuadChange` -/

section QuadChange

open Function



open HRS HRS.External HRS.External.RefMarg HRS.External.PoleVar

variable {d : ℕ} {s : ℝ}

theorem evariance_add_le' {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsFiniteMeasure ν] {X Y : α → ℝ}
    (hX : AEStronglyMeasurable X ν) (hY : AEStronglyMeasurable Y ν) :
    evariance (fun z => X z + Y z) ν ≤ 2 * evariance X ν + 2 * evariance Y ν := by
  by_cases hXm : MemLp X 2 ν
  swap
  · rw [evariance_eq_top hX hXm]; simp
  by_cases hYm : MemLp Y 2 ν
  swap
  · rw [evariance_eq_top hY hYm]; simp
  have hmean : ∫ z, (X z + Y z) ∂ν = ∫ z, X z ∂ν + ∫ z, Y z ∂ν :=
    integral_add (hXm.integrable (by norm_num)) (hYm.integrable (by norm_num))
  have hXe : AEMeasurable (fun z => ‖X z - ∫ z, X z ∂ν‖ₑ ^ 2) ν :=
    ((hX.sub aestronglyMeasurable_const).aemeasurable.enorm).pow_const 2
  calc evariance (fun z => X z + Y z) ν
      = ∫⁻ z, ‖(X z + Y z) - (∫ z, X z ∂ν + ∫ z, Y z ∂ν)‖ₑ ^ 2 ∂ν := by
        rw [evariance, hmean]
    _ ≤ ∫⁻ z, 2 * (‖X z - ∫ z, X z ∂ν‖ₑ ^ 2 + ‖Y z - ∫ z, Y z ∂ν‖ₑ ^ 2) ∂ν := by
        refine lintegral_mono fun z => ?_
        have e : (X z + Y z) - (∫ z, X z ∂ν + ∫ z, Y z ∂ν)
            = (X z - ∫ z, X z ∂ν) + (Y z - ∫ z, Y z ∂ν) := by ring
        rw [e]
        exact (pow_le_pow_left' (enorm_add_le _ _) 2).trans (enorm_sq_add_le _ _)
    _ = 2 * evariance X ν + 2 * evariance Y ν := by
        rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_left' hXe, mul_add]
        rfl


section Change

variable {μ : Measure (Torus d)} [IsProbabilityMeasure μ]

/-- `D_N(h;ν) - D_N(h;π) = -(2/N) ∑_i φ(x_i) + (h₀(ν) - h₀(π))`, `φ = H_ν - H_π`. -/
theorem quadStat_sub_eq (h : Torus d → Torus d → ℝ) (π ν : Measure (Torus d)) {N : ℕ} (X : Config d N) :
    quadStat h ν X = quadStat h π X +
      ((-(2 / (N : ℝ))) * ∑ i, (Hc h ν (X i) - Hc h π (X i)) + (h0c h ν - h0c h π)) := by
  unfold quadStat Hc h0c
  simp only [Finset.sum_sub_distrib, mul_sub]
  ring

/-- **Change of the centering measure** (`A:eq:D-definition`, last paragraph of the proof):
`N Var_R D_N(h;ν) ≤ 2 N Var_R D_N(h;π) + 16 ∫ |H_ν - H_π|² dπ`, `π = R^{(1)}`. -/
theorem evariance_quad_change (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {N : ℕ} [NeZero N]
    (hκ : weakKappa V β ≤ 1 / 2) {h : Torus d → Torus d → ℝ} (hm : Measurable (Function.uncurry h))
    (ν : Measure (Torus d)) [IsProbabilityMeasure ν] :
    ((N : ℕ) : ℝ≥0∞) * evariance (fun X : Config d N => quadStat h ν X)
        (pinnedLaw V (β / N) N (fun e : Empty => e.elim))
      ≤ 2 * ((N : ℕ) : ℝ≥0∞) * evariance (fun X : Config d N => quadStat h
          ((pinnedLaw V (β / N) N (fun e : Empty => e.elim)).map (fun X => X 0)) X)
          (pinnedLaw V (β / N) N (fun e : Empty => e.elim))
        + 16 * ∫⁻ x, ‖Hc h ν x - Hc h ((pinnedLaw V (β / N) N (fun e : Empty => e.elim)).map (fun X => X 0)) x‖ₑ ^ 2
          ∂((pinnedLaw V (β / N) N (fun e : Empty => e.elim)).map (fun X => X 0)) := by
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  have hlam : 0 ≤ β / N := div_nonneg hβ hNR.le
  set R := pinnedLaw V (β / N) N (fun e : Empty => e.elim) with hR
  haveI : IsProbabilityMeasure R := isProb_pinnedLaw V hlam N _
  set π : Measure (Torus d) := R.map (fun X => X 0) with hπ
  set φ : Torus d → ℝ := fun x => Hc h ν x - Hc h π x with hφ
  have hφm : Measurable φ := (measurable_Hc hm ν).sub (measurable_Hc hm π)
  have hS : Measurable (fun X : Config d N => ∑ i, φ (X i)) :=
    Finset.measurable_sum _ fun i _ => hφm.comp (measurable_pi_apply i)
  set c0 : ℝ := h0c h ν - h0c h π with hc0
  have hFπ : Measurable (fun X : Config d N => quadStat h π X) := measurable_quadStat hm π
  have e1 : (fun X : Config d N => quadStat h ν X) = fun X => quadStat h π X +
      ((-(2 / (N : ℝ))) * ∑ i, φ (X i) + c0) := funext fun X => quadStat_sub_eq h π ν X
  have hG : Measurable (fun X : Config d N => (-(2 / (N : ℝ))) * ∑ i, φ (X i) + c0) :=
    (hS.const_mul _).add_const _
  have h1 : evariance (fun X : Config d N => quadStat h ν X) R ≤
      2 * evariance (fun X : Config d N => quadStat h π X) R +
        2 * evariance (fun X : Config d N => (-(2 / (N : ℝ))) * ∑ i, φ (X i) + c0) R := by
    rw [e1]
    exact evariance_add_le' hFπ.aestronglyMeasurable hG.aestronglyMeasurable
  have h2 : evariance (fun X : Config d N => (-(2 / (N : ℝ))) * ∑ i, φ (X i) + c0) R
      = ENNReal.ofReal ((2 / (N : ℝ)) ^ 2) * evariance (fun X : Config d N => ∑ i, φ (X i)) R := by
    rw [evariance_add_const' R (hS.const_mul _).aestronglyMeasurable c0, evariance_mul]
    congr 2; ring
  have h4 : evariance (fun X : Config d N => ∑ i, φ (X i)) R ≤ 2 * N * evariance φ π :=
    weak_linear_variance_symm (B := Empty) V hβ hN0 (by simp) (fun e : Empty => e.elim) hκ φ hφm
  have h5 : evariance φ π ≤ ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂π := by
    have := evariance_le_lintegral_sub π hφm.aestronglyMeasurable 0
    simpa using this
  have e : ENNReal.ofReal ((2 / (N : ℝ)) ^ 2) * (N : ℝ≥0∞) * (N : ℝ≥0∞) = 4 := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    have : (2 / (N : ℝ)) ^ 2 * N * N = 4 := by field_simp; norm_num
    rw [this]; simp
  calc (N : ℝ≥0∞) * evariance (fun X : Config d N => quadStat h ν X) R
      ≤ (N : ℝ≥0∞) * (2 * evariance (fun X : Config d N => quadStat h π X) R +
          2 * (ENNReal.ofReal ((2 / (N : ℝ)) ^ 2) * (2 * N * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂π))) := by
        gcongr
        refine h1.trans ?_
        gcongr
        rw [h2]
        gcongr
        exact h4.trans (by gcongr)
    _ = 2 * (N : ℝ≥0∞) * evariance (fun X : Config d N => quadStat h π X) R +
        16 * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂π := by
        have : (N : ℝ≥0∞) * (2 * (ENNReal.ofReal ((2 / (N : ℝ)) ^ 2) * (2 * N * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂π)))
            = (ENNReal.ofReal ((2 / (N : ℝ)) ^ 2) * (N : ℝ≥0∞) * (N : ℝ≥0∞)) * 4 * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂π := by ring
        rw [mul_add, this, e]
        ring


theorem lintegral_enorm_sq_eq_eLpNorm_sq {α : Type*} [MeasurableSpace α] {ν : Measure α} {f : α → ℝ}
    (hf : AEStronglyMeasurable f ν) :
    ∫⁻ x, ‖f x‖ₑ ^ 2 ∂ν = (eLpNorm f 2 ν) ^ 2 := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
  simp only [ENNReal.toReal_ofNat]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  simp

/-- **The change term** (`A:prop:marginal` + Young): `∫ |H_ν - H_π|² dπ ≤ c B² ‖dν/dμ - dπ/dμ‖²_{L²(μ)}`. -/
theorem change_term_le (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ c : ℝ, 0 < c ∧ ∀ {ρ : Torus d → ℝ} {Λ : ℝ}, (∀ y, ρ y ≤ Λ) → 0 ≤ Λ →
      ∀ {Cp : ℝ}, 0 ≤ Cp → ∀ {B : ℝ}, 0 ≤ B → ∀ {h : Torus d → Torus d → ℝ},
      Measurable (Function.uncurry h) →
      (∀ x y, x ≠ y → |h x y| ≤ B * singEnvelope s (Torus.eucDist x y)) →
      ∀ {π ν : Measure (Torus d)} [IsProbabilityMeasure π] [IsProbabilityMeasure ν],
      π ≤ ENNReal.ofReal Cp • withDensityReal ρ → ν ≤ ENNReal.ofReal Cp • withDensityReal ρ →
      π ≪ withDensityReal ρ → ν ≪ withDensityReal ρ →
      ∫⁻ x, ‖Hc h ν x - Hc h π x‖ₑ ^ 2 ∂π ≤ ENNReal.ofReal (c * Cp * Λ ^ 2 * B ^ 2) *
        (eLpNorm (fun y => (ν.rnDeriv (withDensityReal ρ) y).toReal -
          (π.rnDeriv (withDensityReal ρ) y).toReal) 2 (withDensityReal ρ)) ^ 2 := by
  obtain ⟨c₃, hc₃, hc3⟩ := lintegral_envT_le hd hs0 hsd
  refine ⟨c₃ ^ 2, by positivity, fun {ρ Λ} hΛ hΛ0 {Cp} hCp {B} hB {h} hm hh {π ν} _ _ hπ hν hπac hνac => ?_⟩
  haveI : IsFiniteMeasure (ENNReal.ofReal Λ • (volume : Measure (Torus d))) :=
    Measure.smul_finite _ ENNReal.ofReal_ne_top
  haveI : IsFiniteMeasure (withDensityReal ρ) :=
    isFiniteMeasure_of_le (ENNReal.ofReal Λ • (volume : Measure (Torus d))) (KernelAux2.withDensityReal_le ρ Λ hΛ)
  set μ := withDensityReal ρ with hμ
  set g : Torus d → ℝ := fun y => (ν.rnDeriv μ y).toReal - (π.rnDeriv μ y).toReal with hg
  have hgm : Measurable g :=
    (Measure.measurable_rnDeriv _ _).ennreal_toReal.sub (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hhint : ∀ (κ : Measure (Torus d)), κ ≤ ENNReal.ofReal Cp • μ → ∀ x, Integrable (h x) κ := fun κ hκ x =>
    integrable_of_env_bound hd hs0 hsd hΛ hΛ0 hκ hCp hB (measurable_h_x hm x) (fun y hy => by
      have := hh x y (Ne.symm hy)
      rwa [eucDist_sub] at this)
  -- pointwise bound of the difference
  have hΔ : ∀ x, ‖Hc h ν x - Hc h π x‖ₑ ≤ ENNReal.ofReal B * ∫⁻ y, ENNReal.ofReal (envT s (x - y)) * ‖g y‖ₑ ∂μ := by
    intro x
    have hiν : Integrable (fun y => (ν.rnDeriv μ y).toReal * h x y) μ :=
      (integrable_toReal_rnDeriv_mul_iff hνac).2 (hhint ν hν x)
    have hiπ : Integrable (fun y => (π.rnDeriv μ y).toReal * h x y) μ :=
      (integrable_toReal_rnDeriv_mul_iff hπac).2 (hhint π hπ x)
    have e : Hc h ν x - Hc h π x = ∫ y, g y * h x y ∂μ := by
      unfold Hc
      rw [← integral_toReal_rnDeriv_mul hνac, ← integral_toReal_rnDeriv_mul hπac,
        ← integral_sub hiν hiπ]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [hg]; ring
    rw [e]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    have hae : ∀ᵐ y ∂μ, y ≠ x := ae_ne_pt (Calib.atomless_withDensityReal (by omega) ρ) x
    calc ∫⁻ y, ‖g y * h x y‖ₑ ∂μ ≤ ∫⁻ y, ENNReal.ofReal B * (ENNReal.ofReal (envT s (x - y)) * ‖g y‖ₑ) ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [hae] with y hy
          rw [enorm_mul]
          have h1 := hh x y (Ne.symm hy)
          rw [eucDist_sub] at h1
          have h2 : ‖h x y‖ₑ ≤ ENNReal.ofReal B * ENNReal.ofReal (envT s (x - y)) := by
            rw [← ENNReal.ofReal_mul hB, Real.enorm_eq_ofReal_abs]
            exact ENNReal.ofReal_le_ofReal h1
          calc ‖g y‖ₑ * ‖h x y‖ₑ ≤ ‖g y‖ₑ * (ENNReal.ofReal B * ENNReal.ofReal (envT s (x - y))) :=
                mul_le_mul' le_rfl h2
            _ = _ := by ring
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  -- Schur
  set A : ℝ≥0∞ := ENNReal.ofReal (Λ * c₃) with hA
  have hk : Measurable fun z : Torus d => ENNReal.ofReal (envT s z) :=
    ENNReal.measurable_ofReal.comp measurable_envT
  have hs1 : ∀ x, ∫⁻ y, ENNReal.ofReal (envT s (x - y)) ∂μ ≤ A := by
    intro x
    refine (KernelAux2.lintegral_conv_le ρ Λ hΛ (fun z => ENNReal.ofReal (envT s z)) x).trans ?_
    rw [hA, ENNReal.ofReal_mul hΛ0]
    gcongr
  have hs2 : ∀ y, ∫⁻ x, ENNReal.ofReal (envT s (x - y)) ∂μ ≤ A := by
    intro y
    have : ∀ x, envT s (x - y) = envT s (y - x) := fun x => envT_sub_comm x y
    simp_rw [this]
    exact hs1 y
  have hschur := schur_sq (ν := μ) (k := fun z => ENNReal.ofReal (envT s z)) (f := fun y => ‖g y‖ₑ) hk
    hgm.enorm hs1 hs2
  calc ∫⁻ x, ‖Hc h ν x - Hc h π x‖ₑ ^ 2 ∂π
      ≤ ∫⁻ x, (ENNReal.ofReal B * ∫⁻ y, ENNReal.ofReal (envT s (x - y)) * ‖g y‖ₑ ∂μ) ^ 2 ∂π :=
        lintegral_mono fun x => pow_le_pow_left' (hΔ x) 2
    _ ≤ ∫⁻ x, (ENNReal.ofReal B * ∫⁻ y, ENNReal.ofReal (envT s (x - y)) * ‖g y‖ₑ ∂μ) ^ 2
          ∂(ENNReal.ofReal Cp • μ) := lintegral_mono' hπ le_rfl
    _ = ENNReal.ofReal Cp * (ENNReal.ofReal B ^ 2 *
          ∫⁻ x, (∫⁻ y, ENNReal.ofReal (envT s (x - y)) * ‖g y‖ₑ ∂μ) ^ 2 ∂μ) := by
        rw [lintegral_smul_measure, smul_eq_mul]
        congr 1
        simp_rw [mul_pow]
        rw [lintegral_const_mul']
        exact (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    _ ≤ ENNReal.ofReal Cp * (ENNReal.ofReal B ^ 2 * (A ^ 2 * ∫⁻ y, ‖g y‖ₑ ^ 2 ∂μ)) := by
        gcongr
    _ = ENNReal.ofReal (c₃ ^ 2 * Cp * Λ ^ 2 * B ^ 2) * (eLpNorm g 2 μ) ^ 2 := by
        rw [lintegral_enorm_sq_eq_eLpNorm_sq hgm.aestronglyMeasurable, hA]
        have e : ENNReal.ofReal (c₃ ^ 2 * Cp * Λ ^ 2 * B ^ 2) =
            ENNReal.ofReal Cp * (ENNReal.ofReal B ^ 2 * ENNReal.ofReal (Λ * c₃) ^ 2) := by
          rw [← ENNReal.ofReal_pow hB, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
            ← ENNReal.ofReal_mul hCp]
          congr 1; ring
        rw [e]; ring

end Change

end QuadChange

/-! ## Part `QuadCrude` -/

section QuadCrude

open Function



open HRS HRS.External HRS.External.RefMarg HRS.External.PoleVar

variable {d : ℕ} {s : ℝ}

theorem sq_sum_sum_erase_le {N : ℕ} (f : Fin N → Fin N → ℝ) :
    (∑ i, ∑ j ∈ Finset.univ.erase i, f i j) ^ 2
      ≤ (N : ℝ) ^ 2 * ∑ i, ∑ j ∈ Finset.univ.erase i, f i j ^ 2 := by
  have h1 : (∑ i, ∑ j ∈ Finset.univ.erase i, f i j) ^ 2
      ≤ (N : ℝ) * ∑ i, (∑ j ∈ Finset.univ.erase i, f i j) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin N => ∑ j ∈ Finset.univ.erase i, f i j)
    simpa using this
  have h2 : ∀ i : Fin N, (∑ j ∈ Finset.univ.erase i, f i j) ^ 2 ≤ (N : ℝ) * ∑ j ∈ Finset.univ.erase i, f i j ^ 2 := by
    intro i
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ.erase i) (f := fun j : Fin N => f i j)
    refine this.trans ?_
    have hc : ((Finset.univ.erase i).card : ℝ) ≤ N := by
      exact_mod_cast (Finset.card_erase_le).trans (by simp)
    exact mul_le_mul_of_nonneg_right hc (Finset.sum_nonneg fun j _ => sq_nonneg _)
  calc (∑ i, ∑ j ∈ Finset.univ.erase i, f i j) ^ 2
      ≤ (N : ℝ) * ∑ i, (∑ j ∈ Finset.univ.erase i, f i j) ^ 2 := h1
    _ ≤ (N : ℝ) * ∑ i, (N : ℝ) * ∑ j ∈ Finset.univ.erase i, f i j ^ 2 := by
        gcongr with i _
        exact h2 i
    _ = (N : ℝ) ^ 2 * ∑ i, ∑ j ∈ Finset.univ.erase i, f i j ^ 2 := by
        rw [← Finset.mul_sum]; ring

/-- Pointwise bound of the square of the statistic by the pair squares. -/
theorem quadStat_sq_le {N : ℕ} (hN : 0 < N) (h : Torus d → Torus d → ℝ) (ν : Measure (Torus d))
    [IsProbabilityMeasure ν] {H' : ℝ} (hH : ∀ x, |Hc h ν x| ≤ H') (Y : Config d N) :
    quadStat h ν Y ^ 2 ≤ 3 * (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, h (Y i) (Y j) ^ 2
      + 15 * H' ^ 2 := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hH0 : 0 ≤ H' := (abs_nonneg _).trans (hH (Y ⟨0, hN⟩))
  set a : ℝ := (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, h (Y i) (Y j) with ha
  set b : ℝ := -(2 * ((1 / (N : ℝ)) * ∑ i, Hc h ν (Y i))) with hb
  set c : ℝ := h0c h ν with hc
  have e : quadStat h ν Y = a + b + c := by
    unfold quadStat; rw [ha, hb, hc]; unfold Hc h0c; ring
  have ha2 : a ^ 2 ≤ (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, h (Y i) (Y j) ^ 2 := by
    rw [ha, mul_pow]
    have := sq_sum_sum_erase_le (fun i j => h (Y i) (Y j))
    calc (1 / (N : ℝ) ^ 2) ^ 2 * (∑ i, ∑ j ∈ Finset.univ.erase i, h (Y i) (Y j)) ^ 2
        ≤ (1 / (N : ℝ) ^ 2) ^ 2 * ((N : ℝ) ^ 2 * ∑ i, ∑ j ∈ Finset.univ.erase i, h (Y i) (Y j) ^ 2) := by gcongr
      _ = _ := by field_simp
  have hb2 : b ^ 2 ≤ 4 * H' ^ 2 := by
    have h1 : |∑ i, Hc h ν (Y i)| ≤ N * H' := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ i, |Hc h ν (Y i)| ≤ ∑ _i : Fin N, H' := Finset.sum_le_sum fun i _ => hH _
        _ = N * H' := by simp
    have h2 : |b| ≤ 2 * H' := by
      have e1 : |b| = 2 * ((1 / (N : ℝ)) * |∑ i, Hc h ν (Y i)|) := by
        rw [hb, abs_neg, abs_mul, abs_mul, abs_of_pos (one_div_pos.2 hNR)]
        norm_num
      rw [e1]
      calc 2 * ((1 / (N : ℝ)) * |∑ i, Hc h ν (Y i)|) ≤ 2 * ((1 / (N : ℝ)) * (N * H')) := by gcongr
        _ = 2 * H' := by field_simp
    nlinarith [abs_nonneg b, sq_abs b]
  have hc2 : c ^ 2 ≤ H' ^ 2 := by
    have : |c| ≤ H' := abs_h0c_le ν hH
    nlinarith [abs_nonneg c, sq_abs c]
  rw [e]
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]


set_option maxHeartbeats 800000 in
/-- **Crude bound** (fixed `n`, no smallness): `E_R |D_N(h;ν)|² ≤ C (1 + Cp²) B²`. -/
theorem quad_crude_weak (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β) (ρ : Torus d → ℝ)
    (hρ : IsProbDensity ρ) {Λ : ℝ} (hΛ : ∀ y, ρ y ≤ Λ) (hΛ0 : 0 ≤ Λ) (Mmax M'max γmax Cq : ℝ)
    (hCq : 0 ≤ Cq) {n : ℕ} (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : WeakPotential (withDensityReal ρ)), V.M ≤ Mmax → V.M' ≤ M'max → V.γ ≤ γmax →
      (∀ x y : Torus d, x ≠ y → envT s (x - y) - Cq ≤ V.q x y) →
      ∀ (B : ℝ), 0 ≤ B → ∀ (h : Torus d → Torus d → ℝ), Measurable (Function.uncurry h) →
      (∀ x y, x ≠ y → |h x y| ≤ B * singEnvelope s (Torus.eucDist x y)) →
      ∀ {Cp : ℝ}, 0 ≤ Cp → ∀ (ν : Measure (Torus d)) [IsProbabilityMeasure ν],
      ν ≤ ENNReal.ofReal Cp • withDensityReal ρ →
      ∫⁻ Y, ‖quadStat h ν Y‖ₑ ^ 2 ∂(pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim))
        ≤ ENNReal.ofReal (C * (1 + Cp ^ 2) * B ^ 2) := by
  haveI hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ
  obtain ⟨cH, hcH, hHc⟩ := Hc_bound hd hs0 hsd
  obtain ⟨c₁, hc₁, hvar⟩ := variance_integral_le hd hs0 hsd
  have hN0 : 0 < n + 1 := Nat.succ_pos n
  have hNR : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast hN0
  have hNpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by linarith
  set lam : ℝ := β / ((n + 1 : ℕ) : ℝ) with hlam
  have hlam0 : 0 < lam := by positivity
  have hlamβ : lam ≤ β := by rw [hlam, div_le_iff₀ hNpos]; nlinarith
  set K : ℝ := 1 + 2 / lam with hK
  have hK1 : 1 ≤ K := by rw [hK]; have : 0 ≤ 2 / lam := by positivity
                         linarith
  have hK2 : 2 / lam ≤ K := by rw [hK]; linarith
  set γ' : ℝ := max γmax 0 with hγ'
  set M0 : ℝ := Mmax + M'max + β * γ' + β * Cq with hM0
  set Wc : ℝ := c₁ * Λ * Real.exp M0 * gFun d s K with hWc
  have hg1 : 1 ≤ gFun d s K := one_le_gFun hd hs0 hsd hK1
  have hWc0 : 0 ≤ Wc := by rw [hWc]; positivity
  refine ⟨3 * Wc + 15 * (cH * Λ) ^ 2 + 1, by positivity, ?_⟩
  intro V hVM hVM' hVγ hq B hB h hm hh Cp hCp ν _ hν
  set P0 := pinnedLaw V lam (n + 1) (fun e : Empty => e.elim) with hP0
  haveI hRp : IsProbabilityMeasure P0 := isProb_pinnedLaw V hlam0.le (n + 1) _
  -- pair bound
  have hpair : ∀ a b : Fin (n + 1), a ≠ b → ∫⁻ Y, ‖h ((Y : Config d (n + 1)) a) (Y b)‖ₑ ^ 2 ∂P0 ≤ ENNReal.ofReal (Wc * B ^ 2) := by
    intro a b hab
    refine pair_lintegral_le V hβ.le a b hab hm (fun x => ?_)
    have h1 := hvar hΛ hΛ0 (b := B) hB (x := x) (lam := lam) (K := K) (M0 := M0) hlam0 hK1 hK2
      (f := h x) (ψ := fun y => V.M' + β * V.γ + pinField V lam (pinsWith (fun e : Empty => e.elim) x) y)
      (fun y hy => by
        have := hh x y (Ne.symm hy)
        rwa [eucDist_sub] at this) (fun y hy => by
        rw [pinField_pinsWith, pinField_empty]
        have h2 := V.φ_le y
        have h3 := hq y x hy
        rw [envT_sub_comm y x] at h3
        have h4 : β * V.γ ≤ β * γ' := mul_le_mul_of_nonneg_left (hVγ.trans (le_max_left _ _)) hβ.le
        have h5 : lam * Cq ≤ β * Cq := mul_le_mul_of_nonneg_right hlamβ hCq
        have h6 : lam * (envT s (x - y) - Cq) ≤ lam * V.q y x := mul_le_mul_of_nonneg_left h3 hlam0.le
        rw [hM0]
        nlinarith)
    refine h1.trans (le_of_eq ?_)
    rw [hWc]; congr 1; ring
  -- the one-point function
  have hH' : ∀ x, |Hc h ν x| ≤ cH * Cp * Λ * B := fun x => hHc hΛ hΛ0 hν hCp hB hh x
  set H' : ℝ := cH * Cp * Λ * B with hH'def
  have hNn : (0 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by linarith
  have hc3 : (0 : ℝ) ≤ 3 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) := by positivity
  have hmeas : ∀ i j : Fin (n + 1), Measurable fun Y : Config d (n + 1) => ‖h (Y i) (Y j)‖ₑ ^ 2 :=
    fun i j => ((measurable_h_pair hm i j).enorm).pow_const 2
  have hpt : ∀ Y : Config d (n + 1), ‖quadStat h ν Y‖ₑ ^ 2 ≤
      ∑ i, ∑ j ∈ Finset.univ.erase i, ENNReal.ofReal (3 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2)) * ‖h (Y i) (Y j)‖ₑ ^ 2
        + ENNReal.ofReal (15 * H' ^ 2) := by
    intro Y
    have h1 := quadStat_sq_le hN0 h ν hH' Y
    have e1 : ‖quadStat h ν Y‖ₑ ^ 2 = ENNReal.ofReal (quadStat h ν Y ^ 2) := by
      rw [← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]
    have e2 : ∀ i j : Fin (n + 1), ‖h (Y i) (Y j)‖ₑ ^ 2 = ENNReal.ofReal (h (Y i) (Y j) ^ 2) := fun i j => by
      rw [← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]
    rw [e1]
    simp_rw [e2]
    refine (ENNReal.ofReal_le_ofReal h1).trans ?_
    rw [ENNReal.ofReal_add (by positivity) (by positivity), Finset.mul_sum]
    refine add_le_add (le_of_eq ?_) le_rfl
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ENNReal.ofReal_mul hc3]
  have hF : Measurable fun Y : Config d (n + 1) => ‖quadStat h ν Y‖ₑ ^ 2 :=
    ((measurable_quadStat hm ν).enorm).pow_const 2
  calc ∫⁻ Y, ‖quadStat h ν Y‖ₑ ^ 2 ∂P0
      ≤ ∫⁻ Y, (∑ i, ∑ j ∈ Finset.univ.erase i, ENNReal.ofReal (3 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2)) *
          ‖h (Y i) (Y j)‖ₑ ^ 2 + ENNReal.ofReal (15 * H' ^ 2)) ∂P0 := lintegral_mono hpt
    _ = (∑ i, ∑ j ∈ Finset.univ.erase i, ENNReal.ofReal (3 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2)) *
          ∫⁻ Y, ‖h (Y i) (Y j)‖ₑ ^ 2 ∂P0) + ENNReal.ofReal (15 * H' ^ 2) := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
        congr 1
        rw [lintegral_finsetSum Finset.univ (f := fun i (Y : Config d (n + 1)) => ∑ j ∈ Finset.univ.erase i,
          ENNReal.ofReal (3 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2)) * ‖h (Y i) (Y j)‖ₑ ^ 2)
          (fun i _ => Finset.measurable_sum _ fun j _ => measurable_const.mul (hmeas i j))]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [lintegral_finsetSum (Finset.univ.erase i) (f := fun j (Y : Config d (n + 1)) =>
          ENNReal.ofReal (3 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2)) * ‖h (Y i) (Y j)‖ₑ ^ 2)
          (fun j _ => measurable_const.mul (hmeas i j))]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [lintegral_const_mul _ (hmeas i j)]
    _ ≤ (∑ i : Fin (n + 1), ∑ j ∈ Finset.univ.erase i, ENNReal.ofReal (3 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2)) *
          ENNReal.ofReal (Wc * B ^ 2)) + ENNReal.ofReal (15 * H' ^ 2) := by
        gcongr with i _ j hj
        exact hpair i j (Finset.ne_of_mem_erase hj).symm
    _ ≤ ENNReal.ofReal (3 * (Wc * B ^ 2)) + ENNReal.ofReal (15 * H' ^ 2) := by
        gcongr
        calc (∑ i : Fin (n + 1), ∑ j ∈ Finset.univ.erase i, ENNReal.ofReal (3 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2)) *
              ENNReal.ofReal (Wc * B ^ 2))
            ≤ ∑ _i : Fin (n + 1), ∑ _j : Fin (n + 1), ENNReal.ofReal (3 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2)) *
              ENNReal.ofReal (Wc * B ^ 2) := by
              refine Finset.sum_le_sum fun i _ => ?_
              exact Finset.sum_le_sum_of_subset (Finset.erase_subset _ _)
          _ = ENNReal.ofReal (((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) * (3 * (1 / ((n + 1 : ℕ) : ℝ) ^ 2) *
              (Wc * B ^ 2)))) := by
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              rw [ENNReal.ofReal_mul hNn, ENNReal.ofReal_mul hNn, ENNReal.ofReal_mul hc3,
                ENNReal.ofReal_natCast]
          _ = _ := by congr 1; field_simp
    _ = ENNReal.ofReal (3 * (Wc * B ^ 2) + 15 * H' ^ 2) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hH'def]
        have h1 : 0 ≤ Wc * B ^ 2 := by positivity
        nlinarith [sq_nonneg (cH * Λ), sq_nonneg Cp, sq_nonneg B, mul_nonneg (sq_nonneg Cp) h1,
          mul_nonneg (sq_nonneg (cH * Λ)) (sq_nonneg B), mul_nonneg (sq_nonneg Cp) (sq_nonneg B)]

end QuadCrude

/-! ## Part `QuadFinal` -/

section QuadFinal

open Function



open HRS HRS.External HRS.External.RefMarg HRS.External.PoleVar HRS.External.HeatSplit

variable {d : ℕ} {s : ℝ}

section QR

/-- `Q_{N,β}(μ)` is a probability measure, `N ≥ 1`. -/
theorem riesz_Q_isProb (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (L : ℕ)
    {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) {Λ : ℝ} (hρΛ : ∀ y, ρ y ≤ Λ) {M : ℕ}
    (Ψ : Torus d → EuclideanSpace ℝ (Fin M))
    (hΨ : ∀ x y, (weakSplit d s τ L).gL (x - y) = inner ℝ (Ψ x) (Ψ y)) {β : ℝ} (hβ : 0 < β) {N : ℕ}
    (hN : 0 < N) : IsProbabilityMeasure (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) := by
  haveI := isProb_withDensityReal hρ
  have hRH := Calib.refHyp_weakSplit hd hs0 hsd hτ hτ1 L hρ hρΛ Ψ hΨ
  haveI := hRH.isProb_RN (N := N) hβ.le
  rw [Calib.riesz_Q_eq_RN_tilted hd hs0 hsd hτ hτ1 L hρ hρΛ Ψ hΨ hβ hN]
  exact isProbabilityMeasure_tilted (hRH.integrable_exp_logW hβ (P := Calib.RN _ _ Ψ β N))

/-- `Q_N ≤ K_N R_N` for every `N ≥ 1` with a (non-uniform) constant `K_N`. -/
theorem riesz_Q_le_smul_RN_crude (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (L : ℕ) {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) {Λ : ℝ} (hρΛ : ∀ y, ρ y ≤ Λ) {M : ℕ}
    (Ψ : Torus d → EuclideanSpace ℝ (Fin M))
    (hΨ : ∀ x y, (weakSplit d s τ L).gL (x - y) = inner ℝ (Ψ x) (Ψ y)) {β : ℝ} (hβ : 0 < β) {N : ℕ}
    (hN : 0 < N) : ∃ K : ℝ, 0 < K ∧ modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ) ≤
      ENNReal.ofReal K • Calib.RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N := by
  haveI := isProb_withDensityReal hρ
  have hRH := Calib.refHyp_weakSplit hd hs0 hsd hτ hτ1 L hρ hρΛ Ψ hΨ
  haveI := hRH.isProb_RN (N := N) hβ.le
  set P := Calib.RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N with hP
  set Z : ℝ := ∫ Y, Real.exp (Calib.logW (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N Y) ∂P with hZ
  have hZpos : 0 < Z := integral_exp_pos (hRH.integrable_exp_logW hβ (P := P))
  refine ⟨1 / Z, by positivity, ?_⟩
  rw [Calib.modulatedGibbs_riesz_eq_split hd hs0 hsd hτ hτ1 L hρ,
    hRH.Q_eq_RN_withDensity hβ hN (weakSplit d s τ L).c]
  intro A
  rw [withDensity_apply' _ A, Measure.smul_apply, smul_eq_mul]
  calc ∫⁻ x in A, ENNReal.ofReal (Real.exp (Calib.logW (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N x) / Z) ∂P
      ≤ ∫⁻ _x in A, ENNReal.ofReal (1 / Z) ∂P := by
        refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
        exact div_le_div_of_nonneg_right (Real.exp_le_one_iff.2 (Calib.RefHyp.logW_nonpos hβ x)) hZpos.le
    _ = _ := by rw [setLIntegral_const]

theorem deltaN_pos (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {N : ℕ} (hN : 1 ≤ N) : 0 < deltaN d s N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [deltaN_eq_gFun hd hs0 hsd hN]
  have := one_le_gFun hd hs0 hsd (K := (N : ℝ)) (by exact_mod_cast hN)
  positivity

/-- `firstMarginal` of a probability measure is a probability measure. -/
theorem isProb_firstMarginal {N : ℕ} (hN : 0 < N) (P : Measure (Config d N)) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (firstMarginal P) := by
  unfold firstMarginal
  rw [dif_pos hN]
  infer_instance

theorem firstMarginal_mono {N : ℕ} (hN : 0 < N) {P P' : Measure (Config d N)} (h : P ≤ P') :
    firstMarginal P ≤ firstMarginal P' := by
  unfold firstMarginal
  rw [dif_pos hN, dif_pos hN]
  exact Measure.map_mono h (measurable_pi_apply _)

theorem firstMarginal_smul {N : ℕ} (hN : 0 < N) (c : ℝ≥0∞) (P : Measure (Config d N)) :
    firstMarginal (c • P) = c • firstMarginal P := by
  unfold firstMarginal
  rw [dif_pos hN, dif_pos hN]
  exact Measure.map_smul _ (measurable_pi_apply _).aemeasurable

/-- The pair kernel `q` of the weak split satisfies the lower envelope `q(z) ≥ e(z) - C_q`. -/
theorem q_lower_env (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (L : ℕ)
    {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) {Λ : ℝ} (hρΛ : ∀ y, ρ y ≤ Λ) {M : ℕ}
    (Ψ : Torus d → EuclideanSpace ℝ (Fin M))
    (hΨ : ∀ x y, (weakSplit d s τ L).gL (x - y) = inner ℝ (Ψ x) (Ψ y)) :
    ∃ Cq : ℝ, 0 ≤ Cq ∧ ∀ z : Torus d, z ≠ 0 → envT s z - Cq ≤ (weakSplit d s τ L).q z := by
  haveI := isProb_withDensityReal hρ
  have hRH := Calib.refHyp_weakSplit hd hs0 hsd hτ hτ1 L hρ hρΛ Ψ hΨ
  obtain ⟨Cg, hCg⟩ := periodicRiesz_lower_env hd hs0 hsd
  obtain ⟨-, -, hsplit, -, -, -, -, -, -, hc0, -⟩ := weakSplit_spec hd hs0 hsd hτ hτ1 L
  have hgL0 := hRH.gL_zero_nonneg
  refine ⟨max Cg 0 + (weakSplit d s τ L).gL 0, by positivity, fun z hz => ?_⟩
  have hgl : (weakSplit d s τ L).gL z ≤ (weakSplit d s τ L).gL 0 := by
    have h1 := hRH.gL_eq z 0
    rw [sub_zero] at h1
    rw [h1]
    calc inner ℝ (Ψ z) (Ψ 0) ≤ ‖Ψ z‖ * ‖Ψ 0‖ := real_inner_le_norm _ _
      _ ≤ Real.sqrt ((weakSplit d s τ L).gL 0) * Real.sqrt ((weakSplit d s τ L).gL 0) :=
          mul_le_mul (hRH.norm_Ψ_le z) (hRH.norm_Ψ_le 0) (norm_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := Real.mul_self_sqrt hgL0
  have hs := hsplit z hz
  have h2 := hCg z hz
  have := le_max_left Cg 0
  linarith

end QR

section Crude

theorem torus_nontrivial {d : ℕ} (hd : 1 ≤ d) : Nontrivial (Torus d) := by
  haveI : Inhabited (Fin d) := ⟨⟨0, hd⟩⟩
  haveI : Nontrivial UnitAddCircle := by
    refine ⟨⟨0, ((1 / 2 : ℝ) : UnitAddCircle), ?_⟩⟩
    intro h
    have h' : (((1 / 2 : ℝ)) : UnitAddCircle) = 0 := h.symm
    rw [AddCircle.coe_eq_zero_iff] at h'
    obtain ⟨n, hn⟩ := h'
    have h1 : (2 * (n : ℝ)) = 1 := by simp at hn; linarith
    have h2 : (2 * n : ℤ) = 1 := by exact_mod_cast h1
    omega
  exact Pi.nontrivial

/-- `B ≥ 0` is forced by the envelope bound. -/
theorem nonneg_of_env_bound (hd : 1 ≤ d) {B : ℝ} {h : Torus d → Torus d → ℝ}
    (hh : ∀ x y, x ≠ y → |h x y| ≤ B * singEnvelope s (Torus.eucDist x y)) : 0 ≤ B := by
  haveI := torus_nontrivial hd
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (Torus d)
  have h1 := hh x y hxy
  have h2 : 1 ≤ singEnvelope s (Torus.eucDist x y) := one_le_singEnvelope' (Real.sqrt_nonneg _)
  by_contra hB
  push Not at hB
  nlinarith [abs_nonneg (h x y)]

/-- **Crude bound for a fixed `N`** (no smallness): `N Var_Q D_N(h;ν) ≤ C_N B² δ_N`. -/
theorem quad_crude_Q (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β) (ρ : Torus d → ℝ)
    (hρ : SmoothPosDensity ρ) {N : ℕ} (hN : 2 ≤ N) :
    ∃ C : ℝ, ∀ (B : ℝ) (h : Torus d → Torus d → ℝ), Measurable (Function.uncurry h) →
      (∀ x y, x ≠ y → |h x y| ≤ B * singEnvelope s (Torus.eucDist x y)) →
      ∀ ν ∈ ({withDensityReal ρ,
          firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ))} :
            Set (Measure (Torus d))),
        (N : ℝ≥0∞) * evariance (fun X : Config d N => quadStat h ν X)
            (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≤
          ENNReal.ofReal (C * B ^ 2 * deltaN d s N) := by
  haveI hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  have hN0 : 0 < N := by omega
  obtain ⟨τ, L, Λ, M, Ψ, hτ, hτ1, hΛ1, hΛ, hΨ, hκ⟩ := PoleVar.exists_split_params hd hs0 hsd hβ hρ
  have hRH := Calib.refHyp_weakSplit hd hs0 hsd hτ hτ1 L hρ.density hΛ Ψ hΨ
  set γ : ℝ := Λ * (weakSplit d s τ L).c with hγ
  set K0 : ℝ := max 1 (4 * β * (weakSplit d s τ L).gL 0) with hK0
  have ht0 : ∀ x, |inner ℝ (Calib.tN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N)
      (Calib.Xi (withDensityReal ρ) Ψ x)| ≤ K0 :=
    fun x => (abs_tN_inner_le hRH hβ hN0 x).trans (le_max_right _ _)
  set V := weakPotK hRH hβ.le (Calib.tN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N) ht0 with hV
  have hRN : Calib.RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β N =
      pinnedLaw V (β / ((N : ℕ) : ℝ)) N (fun e : Empty => e.elim) := by
    rw [RN_eq_fieldLawK hRH hβ.le ht0, pinnedLaw_empty]
  obtain ⟨Cq, hCq0, hCq⟩ := q_lower_env hd hs0 hsd hτ hτ1 L hρ.density hΛ Ψ hΨ
  obtain ⟨K', hK'0, hQK⟩ := riesz_Q_le_smul_RN_crude hd hs0 hsd hτ hτ1 L hρ.density hΛ Ψ hΨ hβ hN0
  haveI hQp := riesz_Q_isProb hd hs0 hsd hτ hτ1 L hρ.density hΛ Ψ hΨ hβ hN0
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hΛ0 : 0 ≤ Λ := by linarith
  obtain ⟨Cc, hCc0, hCc⟩ := quad_crude_weak hd hs0 hsd hβ ρ hρ.density hΛ hΛ0 (β * γ + K0) 0 γ Cq hCq0 (n := n)
    (by omega)
  -- the marginal bound
  set Cp : ℝ := max 1 (K' * Real.exp ((β * γ + K0) + 0 + β * γ)) with hCp
  have hCp0 : 0 ≤ Cp := le_trans zero_le_one (le_max_left _ _)
  have hπR := firstMarginal_RN_leK hRH hβ (N := n + 1) hN0 ht0
  have hπQ : firstMarginal (modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ)) ≤
      ENNReal.ofReal Cp • withDensityReal ρ := by
    refine (firstMarginal_mono hN0 hQK).trans ?_
    rw [firstMarginal_smul hN0]
    refine Measure.le_iff'.2 fun A => ?_
    have h1 := hπR A
    rw [Measure.smul_apply, smul_eq_mul] at h1 ⊢
    rw [Measure.smul_apply, smul_eq_mul]
    calc ENNReal.ofReal K' * firstMarginal (Calib.RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β (n + 1)) A
        ≤ ENNReal.ofReal K' * (ENNReal.ofReal (Real.exp ((β * γ + K0) + 0 + β * γ)) * withDensityReal ρ A) :=
          mul_le_mul' le_rfl h1
      _ = ENNReal.ofReal (K' * Real.exp ((β * γ + K0) + 0 + β * γ)) * withDensityReal ρ A := by
          rw [← mul_assoc, ENNReal.ofReal_mul hK'0.le]
      _ ≤ ENNReal.ofReal Cp * withDensityReal ρ A :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_right _ _)) le_rfl
  have hδ := deltaN_pos hd hs0 hsd (N := n + 1) hN0
  refine ⟨((n + 1 : ℕ) : ℝ) * K' * Cc * (1 + Cp ^ 2) / deltaN d s (n + 1), fun B h hm hh ν hν => ?_⟩
  have hB : 0 ≤ B := nonneg_of_env_bound (by omega) hh
  have key : ∀ ν : Measure (Torus d), IsProbabilityMeasure ν → ν ≤ ENNReal.ofReal Cp • withDensityReal ρ →
      ((n + 1 : ℕ) : ℝ≥0∞) * evariance (fun X : Config d (n + 1) => quadStat h ν X)
          (modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ)) ≤
        ENNReal.ofReal (((n + 1 : ℕ) : ℝ) * K' * Cc * (1 + Cp ^ 2) / deltaN d s (n + 1) * B ^ 2 *
          deltaN d s (n + 1)) := by
    intro ν hνp hνle
    have hbd := hCc V (le_refl _) (le_refl _) (le_refl _) (fun x y hxy => hCq (x - y) (sub_ne_zero.2 hxy)) B hB h hm hh
      hCp0 ν hνle
    rw [← hRN] at hbd
    have hF : Measurable (fun X : Config d (n + 1) => quadStat h ν X) := measurable_quadStat hm ν
    have h1 : evariance (fun X : Config d (n + 1) => quadStat h ν X)
        (modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ)) ≤
        ∫⁻ X, ‖quadStat h ν X‖ₑ ^ 2 ∂(modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ)) := by
      have := evariance_le_lintegral_sub (modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ))
        hF.aestronglyMeasurable 0
      simpa using this
    have h2 : ∫⁻ X, ‖quadStat h ν X‖ₑ ^ 2 ∂(modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ))
        ≤ ENNReal.ofReal K' * ∫⁻ X, ‖quadStat h ν X‖ₑ ^ 2
          ∂(Calib.RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β (n + 1)) := by
      calc _ ≤ ∫⁻ X, ‖quadStat h ν X‖ₑ ^ 2 ∂(ENNReal.ofReal K' • Calib.RN (weakSplit d s τ L).q
              (withDensityReal ρ) Ψ β (n + 1)) := lintegral_mono' hQK le_rfl
        _ = _ := by rw [lintegral_smul_measure, smul_eq_mul]
    calc ((n + 1 : ℕ) : ℝ≥0∞) * evariance (fun X : Config d (n + 1) => quadStat h ν X)
          (modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ))
        ≤ ((n + 1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal K' * ENNReal.ofReal (Cc * (1 + Cp ^ 2) * B ^ 2)) := by
          gcongr
          exact h1.trans (h2.trans (by gcongr))
      _ = ENNReal.ofReal (((n + 1 : ℕ) : ℝ) * K' * Cc * (1 + Cp ^ 2) / deltaN d s (n + 1) * B ^ 2 *
          deltaN d s (n + 1)) := by
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hK'0.le, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp
  rcases hν with rfl | rfl
  · refine key _ inferInstance (Measure.le_iff'.2 fun A => ?_)
    rw [Measure.smul_apply, smul_eq_mul]
    exact le_mul_of_one_le_left bot_le (ENNReal.one_le_ofReal.2 (le_max_left _ _))
  · exact key _ (isProb_firstMarginal hN0 _) hπQ

end Crude

section Large

theorem deltaN_le_one (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {N : ℕ} (hN : 1 ≤ N) : deltaN d s N ≤ 1 := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  unfold deltaN
  split_ifs with h1 h2
  · exact inv_le_one_of_one_le₀ hN1
  · rw [inv_mul_le_iff₀ hN0, mul_one, Real.log_mul (Real.exp_pos 1).ne' hN0.ne', Real.log_exp]
    have := Real.log_le_sub_one_of_pos hN0
    linarith
  · have h3 : (d : ℝ) / 2 < s := lt_of_le_of_ne (not_lt.1 h1) (Ne.symm h2)
    have hs : 0 < s := by
      have : (0 : ℝ) < d / 2 := by
        have : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
        positivity
      linarith
    exact Real.rpow_le_one_of_one_le_of_nonpos hN1 (by rw [sub_nonpos, one_le_div hs]; linarith)

end Large

end QuadFinal

/-! ## Part `QuadLarge` -/

section QuadLarge

open Function



open HRS HRS.External HRS.External.RefMarg HRS.External.PoleVar HRS.External.HeatSplit

variable {d : ℕ} {s : ℝ}

theorem ofReal_comb {K a b c : ℝ} (hK : 0 ≤ K) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    ENNReal.ofReal K * (2 * ENNReal.ofReal a + 16 * (ENNReal.ofReal b * ENNReal.ofReal c))
      = ENNReal.ofReal (K * (2 * a + 16 * (b * c))) := by
  rw [ENNReal.ofReal_mul hK, ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16),
    ENNReal.ofReal_mul hb]
  simp

set_option maxHeartbeats 1600000 in
theorem quad_large (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β) (ρ : Torus d → ℝ)
    (hρ : SmoothPosDensity ρ) :
    ∃ (C : ℝ) (N₁ : ℕ), ∀ N : ℕ, N₁ ≤ N → 2 ≤ N → ∀ (B : ℝ) (h : Torus d → Torus d → ℝ),
      Measurable (Function.uncurry h) → (∀ x y, h x y = h y x) →
      (∀ x y, x ≠ y → |h x y| ≤ B * singEnvelope s (Torus.eucDist x y)) →
      ∀ ν ∈ ({withDensityReal ρ,
          firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ))} :
            Set (Measure (Torus d))),
        (N : ℝ≥0∞) * evariance (fun X : Config d N => quadStat h ν X)
            (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≤
          ENNReal.ofReal (C * B ^ 2 * deltaN d s N) := by
  haveI hμ : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  obtain ⟨τ, L, Λ, M, Ψ, hτ, hτ1, hΛ1, hΛ, hΨ, hκ⟩ := PoleVar.exists_split_params hd hs0 hsd hβ hρ
  have hΛ0 : 0 ≤ Λ := by linarith
  have hRH := Calib.refHyp_weakSplit hd hs0 hsd hτ hτ1 L hρ.density hΛ Ψ hΨ
  set γ : ℝ := Λ * (weakSplit d s τ L).c with hγ
  set gL0 : ℝ := (weakSplit d s τ L).gL 0 with hgL0
  have hgL00 : 0 ≤ gL0 := hRH.gL_zero_nonneg
  obtain ⟨N₀, hN₀⟩ := Glue.eventually_hsmall hd hs0 hsd hτ hτ1 L hρ.density hΛ Ψ hΨ hβ
  obtain ⟨N₂, hN₂⟩ := Glue.riesz_Q_le_smul_RN_eventually hd hs0 hsd hτ hτ1 L hρ.density hΛ Ψ hΨ hβ hκ
  obtain ⟨CR, N₃, hR2⟩ := reference_marginal_density_L2 hd hs0 hsd hτ hτ1 L hΛ1 hβ hκ Ψ hΨ
  obtain ⟨CF, hF2⟩ := firstMarginal_density_L2 hd hs0 hsd β hβ ρ hρ
  obtain ⟨Cq, hCq0, hCq⟩ := q_lower_env hd hs0 hsd hτ hτ1 L hρ.density hΛ Ψ hΨ
  obtain ⟨CW, hCW0, hCW⟩ := quad_weak_bound hd hs0 hsd hβ ρ hρ.density hΛ hΛ0 (β * γ + 1) 0 γ Cq hCq0
  obtain ⟨cch, hcch, hch⟩ := change_term_le hd hs0 hsd
  set KQ : ℝ := Real.exp (4 * β * gL0) with hKQ
  have hKQ1 : 1 ≤ KQ := Real.one_le_exp (by positivity)
  set E : ℝ := Real.exp ((β * γ + 1) + 0 + β * γ) with hE
  have hE0 : 0 < E := Real.exp_pos _
  set Cp : ℝ := max 1 (KQ * E) with hCp
  have hCp0 : 0 ≤ Cp := le_trans zero_le_one (le_max_left _ _)
  set Cb : ℝ := max CR 0 + max CF 0 with hCb
  have hCb0 : 0 ≤ Cb := by positivity
  refine ⟨KQ * (2 * CW + 16 * (cch * Cp * Λ ^ 2 * Cb ^ 2)) + 1, max (max N₀ N₂) (max N₃ 2), ?_⟩
  intro N hN hN2 B h hm hsym hh ν hν
  have hNN₀ : N₀ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNN₂ : N₂ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNN₃ : N₃ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN0 : 0 < N := by omega
  have hB : 0 ≤ B := nonneg_of_env_bound (by omega) hh
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  haveI : NeZero n := ⟨by omega⟩
  have hn1 : 1 ≤ n := by omega
  have hNn : 0 < n + 1 := Nat.succ_pos n
  have hδ0 : 0 < deltaN d s (n + 1) := deltaN_pos hd hs0 hsd hNn
  have hδ1 : deltaN d s (n + 1) ≤ 1 := deltaN_le_one hd hs0 hsd hNn
  have ht : ∀ x, |inner ℝ (Calib.tN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β (n + 1))
      (Calib.Xi (withDensityReal ρ) Ψ x)| ≤ 1 := fun x => by
    have := hN₀ (n + 1) hNN₀ x
    rwa [← Calib.inner_eq_sum] at this
  set V := weakPotK hRH hβ.le (Calib.tN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β (n + 1)) ht with hV
  have hRN : Calib.RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β (n + 1) =
      pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim) := by
    rw [RN_eq_fieldLawK hRH hβ.le ht, pinnedLaw_empty]
  have hκV : weakKappa V β ≤ 1 / 2 := weakKappa_weakPotK_le hRH hβ.le ht hκ
  haveI hQp := riesz_Q_isProb hd hs0 hsd hτ hτ1 L hρ.density hΛ Ψ hΨ hβ hNn
  have hQK := hN₂ (n + 1) hNN₂
  haveI hRp : IsProbabilityMeasure (Calib.RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β (n + 1)) :=
    hRH.isProb_RN hβ.le
  have hπeq : firstMarginal (Calib.RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β (n + 1)) =
      (pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim)).map (fun X => X 0) := by
    unfold firstMarginal
    rw [dif_pos hNn, hRN]
    rfl
  set R0 := pinnedLaw V (β / ((n + 1 : ℕ) : ℝ)) (n + 1) (fun e : Empty => e.elim) with hR0
  haveI hR0p : IsProbabilityMeasure R0 := by rw [← hRN]; exact hRp
  set π0 : Measure (Torus d) := R0.map (fun X => X 0) with hπ0
  haveI hπ0p : IsProbabilityMeasure π0 := inferInstance
  have hπ0le : π0 ≤ ENNReal.ofReal Cp • withDensityReal ρ := by
    have h1 := firstMarginal_RN_leK hRH hβ (N := n + 1) hNn ht
    rw [hπeq] at h1
    refine h1.trans ?_
    refine Measure.le_iff'.2 fun A => ?_
    rw [Measure.smul_apply, smul_eq_mul, Measure.smul_apply, smul_eq_mul]
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    refine le_trans ?_ (le_max_right _ _)
    nlinarith [hE0]
  have hπNle : firstMarginal (modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ)) ≤
      ENNReal.ofReal Cp • withDensityReal ρ := by
    refine (firstMarginal_mono hNn hQK).trans ?_
    rw [firstMarginal_smul hNn]
    have h1 := firstMarginal_RN_leK hRH hβ (N := n + 1) hNn ht
    refine Measure.le_iff'.2 fun A => ?_
    have h2 := h1 A
    rw [Measure.smul_apply, smul_eq_mul] at h2 ⊢
    rw [Measure.smul_apply, smul_eq_mul]
    calc ENNReal.ofReal KQ * firstMarginal (Calib.RN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β (n + 1)) A
        ≤ ENNReal.ofReal KQ * (ENNReal.ofReal E * withDensityReal ρ A) := mul_le_mul' le_rfl h2
      _ = ENNReal.ofReal (KQ * E) * withDensityReal ρ A := by rw [← mul_assoc, ENNReal.ofReal_mul (by positivity)]
      _ ≤ ENNReal.ofReal Cp * withDensityReal ρ A := mul_le_mul' (ENNReal.ofReal_le_ofReal (le_max_right _ _)) le_rfl
  -- the density estimates
  obtain ⟨hπRac, hπR2⟩ := hR2 ρ hρ.density hΛ (n + 1) hNN₃
  rw [hπeq] at hπRac hπR2
  obtain ⟨hπNac, hπN2⟩ := hF2 (n + 1) hN2
  have hνfacts : IsProbabilityMeasure ν ∧ ν ≤ ENNReal.ofReal Cp • withDensityReal ρ ∧ ν ≪ withDensityReal ρ ∧
      eLpNorm (fun y => (ν.rnDeriv (withDensityReal ρ) y).toReal -
        (π0.rnDeriv (withDensityReal ρ) y).toReal) 2 (withDensityReal ρ) ≤
          ENNReal.ofReal (Cb * deltaN d s (n + 1)) := by
    have hgm : Measurable fun y => (π0.rnDeriv (withDensityReal ρ) y).toReal :=
      (Measure.measurable_rnDeriv _ _).ennreal_toReal
    rcases hν with rfl | rfl
    · refine ⟨inferInstance, Measure.le_iff'.2 fun A => ?_, Measure.AbsolutelyContinuous.refl _, ?_⟩
      · rw [Measure.smul_apply, smul_eq_mul]
        exact le_mul_of_one_le_left bot_le (ENNReal.one_le_ofReal.2 (le_max_left _ _))
      · have e : (fun y => ((withDensityReal ρ).rnDeriv (withDensityReal ρ) y).toReal -
            (π0.rnDeriv (withDensityReal ρ) y).toReal) =ᵐ[withDensityReal ρ]
            fun y => -((π0.rnDeriv (withDensityReal ρ) y).toReal - 1) := by
          filter_upwards [Measure.rnDeriv_self (withDensityReal ρ)] with y hy
          simp [hy]
        rw [eLpNorm_congr_ae e]
        refine (le_of_eq (eLpNorm_neg _ _ _)).trans (hπR2.trans (ENNReal.ofReal_le_ofReal ?_))
        refine mul_le_mul_of_nonneg_right ?_ hδ0.le
        have := le_max_left CR 0
        have := le_max_right CF 0
        rw [hCb]; linarith
    · refine ⟨isProb_firstMarginal hNn _, hπNle, hπNac, ?_⟩
      set gN : Torus d → ℝ := fun y => ((firstMarginal (modulatedGibbs (periodicRiesz d s) (n + 1) β
        (withDensityReal ρ))).rnDeriv (withDensityReal ρ) y).toReal with hgN
      have hgNm : Measurable gN := (Measure.measurable_rnDeriv _ _).ennreal_toReal
      have e : (fun y => gN y - (π0.rnDeriv (withDensityReal ρ) y).toReal) =
          (fun y => gN y - 1) - fun y => (π0.rnDeriv (withDensityReal ρ) y).toReal - 1 := by
        funext y; simp
      rw [e]
      refine (eLpNorm_sub_le (by norm_num)).trans ?_
      refine (add_le_add hπN2 hπR2).trans ?_
      have hCF : CF * deltaN d s (n + 1) ≤ max CF 0 * deltaN d s (n + 1) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hδ0.le
      have hCR : CR * deltaN d s (n + 1) ≤ max CR 0 * deltaN d s (n + 1) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hδ0.le
      calc ENNReal.ofReal (CF * deltaN d s (n + 1)) + ENNReal.ofReal (CR * deltaN d s (n + 1))
          ≤ ENNReal.ofReal (max CF 0 * deltaN d s (n + 1)) + ENNReal.ofReal (max CR 0 * deltaN d s (n + 1)) :=
            add_le_add (ENNReal.ofReal_le_ofReal hCF) (ENNReal.ofReal_le_ofReal hCR)
        _ = ENNReal.ofReal (Cb * deltaN d s (n + 1)) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity), hCb]
            congr 1; ring
  obtain ⟨hνp, hνle, hνac, hνL2⟩ := hνfacts
  have hF : Measurable (fun X : Config d (n + 1) => quadStat h ν X) := measurable_quadStat hm ν
  rw [hRN] at hQK
  have step1 : ((n + 1 : ℕ) : ℝ≥0∞) * evariance (fun X : Config d (n + 1) => quadStat h ν X)
        (modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ)) ≤
      ENNReal.ofReal KQ * (((n + 1 : ℕ) : ℝ≥0∞) * evariance (fun X : Config d (n + 1) => quadStat h ν X) R0) := by
    have h1 := evariance_le_of_le_smul hQK hF
    calc ((n + 1 : ℕ) : ℝ≥0∞) * evariance (fun X : Config d (n + 1) => quadStat h ν X)
          (modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ))
        ≤ ((n + 1 : ℕ) : ℝ≥0∞) * (ENNReal.ofReal KQ * evariance (fun X : Config d (n + 1) => quadStat h ν X) R0) := by
          gcongr
      _ = _ := by ring
  haveI : NeZero (n + 1) := ⟨by omega⟩
  have step2 := evariance_quad_change (N := n + 1) V hβ.le hκV hm ν
  have step3 := hCW V (le_refl _) (le_refl _) (le_refl _) (fun x y hxy => hCq (x - y) (sub_ne_zero.2 hxy))
    hn1 hκV B hB h hm hsym hh
  have step4 := hch hΛ hΛ0 hCp0 hB hm hh (π := π0) (ν := ν) hπ0le hνle hπRac hνac
  have step5 : (eLpNorm (fun y => (ν.rnDeriv (withDensityReal ρ) y).toReal -
        (π0.rnDeriv (withDensityReal ρ) y).toReal) 2 (withDensityReal ρ)) ^ 2 ≤
      ENNReal.ofReal (Cb ^ 2 * deltaN d s (n + 1)) := by
    refine (pow_le_pow_left' hνL2 2).trans ?_
    rw [← ENNReal.ofReal_pow (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have : (Cb * deltaN d s (n + 1)) ^ 2 = Cb ^ 2 * (deltaN d s (n + 1) * deltaN d s (n + 1)) := by ring
    rw [this]
    have h2 : deltaN d s (n + 1) * deltaN d s (n + 1) ≤ deltaN d s (n + 1) := by nlinarith
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have hcomb := ofReal_comb (K := KQ) (a := CW * B ^ 2 * deltaN d s (n + 1)) (b := cch * Cp * Λ ^ 2 * B ^ 2)
    (c := Cb ^ 2 * deltaN d s (n + 1)) (by positivity) (by positivity) (by positivity) (by positivity)
  calc ((n + 1 : ℕ) : ℝ≥0∞) * evariance (fun X : Config d (n + 1) => quadStat h ν X)
        (modulatedGibbs (periodicRiesz d s) (n + 1) β (withDensityReal ρ))
      ≤ ENNReal.ofReal KQ * (((n + 1 : ℕ) : ℝ≥0∞) * evariance (fun X : Config d (n + 1) => quadStat h ν X) R0) := step1
    _ ≤ ENNReal.ofReal KQ * (2 * ENNReal.ofReal (CW * B ^ 2 * deltaN d s (n + 1)) +
          16 * (ENNReal.ofReal (cch * Cp * Λ ^ 2 * B ^ 2) * ENNReal.ofReal (Cb ^ 2 * deltaN d s (n + 1)))) := by
        refine mul_le_mul' le_rfl (step2.trans ?_)
        refine add_le_add ?_ ?_
        · rw [mul_assoc]
          exact mul_le_mul' le_rfl step3
        · exact mul_le_mul' le_rfl (step4.trans (mul_le_mul' le_rfl step5))
    _ = ENNReal.ofReal (KQ * (2 * (CW * B ^ 2 * deltaN d s (n + 1)) +
          16 * ((cch * Cp * Λ ^ 2 * B ^ 2) * (Cb ^ 2 * deltaN d s (n + 1))))) := hcomb
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : 0 ≤ B ^ 2 * deltaN d s (n + 1) := by positivity
        nlinarith [h1]

end QuadLarge

end HRS.Quad

namespace HRS

variable {d : ℕ} {s : ℝ}

/-- Proposition 4.3 `M:A:prop:quadratic` (source lines 3764-3778), `A:eq:quadratic`: for a
measurable symmetric kernel `h` with `|h(x,y)| ≤ B(1 + |x-y|^{-s})` (`B(1 + |log|x-y||)` if
`s = 0`) off the diagonal, both `ν = μ` and `ν = Q_{N,β}(μ)^{(1)}` satisfy
`N Var_{Q_{N,β}(μ)}[D_N(h;ν)] ≤ C B² δ_N`, with `C` independent of `h`, `B` and `N ≥ 2`. -/
theorem quadStat_variance (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) :
    ∃ C : ℝ, ∀ (B : ℝ) (h : Torus d → Torus d → ℝ), Measurable (Function.uncurry h) →
      (∀ x y, h x y = h y x) →
      (∀ x y, x ≠ y → |h x y| ≤ B * singEnvelope s (Torus.eucDist x y)) →
      ∀ N : ℕ, 2 ≤ N →
        ∀ ν ∈ ({withDensityReal ρ,
            firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ))} :
              Set (Measure (Torus d))),
          (N : ℝ≥0∞) * evariance (fun X : Config d N => quadStat h ν X)
              (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≤
            ENNReal.ofReal (C * B ^ 2 * deltaN d s N) := by
  obtain ⟨C₁, N₁, h1⟩ := Quad.quad_large hd hs0 hsd hβ ρ hρ
  have hc : ∀ N : ℕ, ∃ C : ℝ, 2 ≤ N → ∀ (B : ℝ) (h : Torus d → Torus d → ℝ), Measurable (Function.uncurry h) →
      (∀ x y, x ≠ y → |h x y| ≤ B * singEnvelope s (Torus.eucDist x y)) →
      ∀ ν ∈ ({withDensityReal ρ,
          firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ))} :
            Set (Measure (Torus d))),
        (N : ℝ≥0∞) * evariance (fun X : Config d N => quadStat h ν X)
            (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≤
          ENNReal.ofReal (C * B ^ 2 * deltaN d s N) := by
    intro N
    by_cases hN : 2 ≤ N
    · obtain ⟨C, hC⟩ := Quad.quad_crude_Q hd hs0 hsd hβ ρ hρ hN
      exact ⟨C, fun _ => hC⟩
    · exact ⟨0, fun h => absurd h hN⟩
  choose Cs hCs using hc
  refine ⟨|C₁| + ∑ N ∈ Finset.range N₁, |Cs N|, ?_⟩
  intro B h hm hsym hh N hN ν hν
  have hD : 0 ≤ B ^ 2 * deltaN d s N := by
    have := Quad.deltaN_pos hd hs0 hsd (N := N) (by omega)
    positivity
  by_cases hNN : N₁ ≤ N
  · refine (h1 N hNN hN B h hm hsym hh ν hν).trans (ENNReal.ofReal_le_ofReal ?_)
    have h2 : C₁ ≤ |C₁| + ∑ N ∈ Finset.range N₁, |Cs N| := by
      have := le_abs_self C₁
      have : 0 ≤ ∑ N ∈ Finset.range N₁, |Cs N| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      linarith
    nlinarith [mul_le_mul_of_nonneg_right h2 hD]
  · have hlt : N < N₁ := not_le.1 hNN
    refine (hCs N hN B h hm hh ν hν).trans (ENNReal.ofReal_le_ofReal ?_)
    have h2 : Cs N ≤ |C₁| + ∑ N ∈ Finset.range N₁, |Cs N| := by
      have h3 : |Cs N| ≤ ∑ N ∈ Finset.range N₁, |Cs N| :=
        Finset.single_le_sum (f := fun N => |Cs N|) (fun M _ => abs_nonneg (Cs M)) (Finset.mem_range.2 hlt)
      have := le_abs_self (Cs N)
      have := abs_nonneg C₁
      linarith
    nlinarith [mul_le_mul_of_nonneg_right h2 hD]

/-! Route for `quadStat_variance_transport` (Prop 4.3, last sentence, source lines 3779-3780):
`h_v(x,y) = (v(x) - v(y))·∇g(x-y)` is measurable (continuity of `v`, measurability of `∇g`) and
symmetric (`∇g` odd); in box coordinates `z` of `x - y`, `|v(x) - v(y)| ≤ L|z|` (mean value
theorem for the smooth lift, on a compact ball) and `|∇g(z)| ≤ C(|z|^{-s-1} + 1)`
(`periodicRiesz_grad_bound`), so `|h_v| ≤ B(1 + |x-y|^{-s})` (`B(1+|log|x-y||)` if `s = 0`).
Then `quadStat_variance` applies with this `B` (constant `C₀ B²`). -/

namespace TransportAux


theorem box_norm_le {y : Euc d} (hy : ∀ i, |y i| ≤ 1 / 2) : ‖y‖ ≤ d := by
  have h1 : ‖y‖ ≤ ∑ i, |y i| := by
    rw [EuclideanSpace.norm_eq]
    rw [Real.sqrt_le_left (Finset.sum_nonneg fun j _ => abs_nonneg _)]
    have := Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ) (f := fun j => |y j|)
      (fun j _ => abs_nonneg _)
    simpa [Real.norm_eq_abs, sq_abs] using this
  refine h1.trans ?_
  calc ∑ i, |y i| ≤ ∑ _i : Fin d, (1 : ℝ) :=
        Finset.sum_le_sum fun i _ => (hy i).trans (by norm_num)
    _ = d := by simp

theorem eucDist_eq_norm {x y : Torus d} {z : Euc d} (hz : Torus.mk z = x - y)
    (hz' : ∀ i, |z i| ≤ 1 / 2) : Torus.eucDist x y = ‖z‖ := by
  unfold Torus.eucDist
  rw [EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : x i - y i = ((z i : ℝ) : UnitAddCircle) := by
    have := congrFun hz i
    simpa [Torus.mk] using this.symm
  rw [h1, AddCircle.norm_coe_eq_abs_iff (1 : ℝ) one_ne_zero |>.2 (by simpa using hz' i),
    Real.norm_eq_abs, sq_abs]

theorem exists_lipschitz_smooth {v : Torus d → Euc d} (hv : Torus.IsSmooth v) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ y z : Euc d, (∀ i, |y i| ≤ 1 / 2) → (∀ i, |z i| ≤ 1 / 2) →
      ‖v (Torus.mk (y + z)) - v (Torus.mk y)‖ ≤ L * ‖z‖ := by
  have hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift v) := hv
  have hcont : Continuous (fderiv ℝ (Torus.lift v)) := hV.continuous_fderiv (by simp)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : Euc d) (2 * d)).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun y z hy hz => ?_⟩
  have hdiff : ∀ x ∈ Metric.closedBall (0 : Euc d) (2 * d), DifferentiableAt ℝ (Torus.lift v) x :=
    fun x _ => (hV.differentiable (by simp)) x
  have hb : ∀ x ∈ Metric.closedBall (0 : Euc d) (2 * d), ‖fderiv ℝ (Torus.lift v) x‖ ≤ max M 0 :=
    fun x hx => (hM x hx).trans (le_max_left _ _)
  have hyK : y ∈ Metric.closedBall (0 : Euc d) (2 * d) := by
    rw [mem_closedBall_zero_iff]
    have := box_norm_le hy
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    linarith
  have hyzK : y + z ∈ Metric.closedBall (0 : Euc d) (2 * d) := by
    rw [mem_closedBall_zero_iff]
    have h1 := box_norm_le hy
    have h2 := box_norm_le hz
    have := norm_add_le y z
    linarith
  have := (convex_closedBall (0 : Euc d) (2 * d)).norm_image_sub_le_of_norm_fderiv_le hdiff hb
    hyK hyzK
  rw [add_sub_cancel_left] at this
  exact this


theorem transport_envelope (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {v : Torus d → Euc d}
    (hv : Torus.IsSmooth v) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x y : Torus d, x ≠ y →
      |inner ℝ (v x - v y) (periodicRieszGrad d s (x - y))| ≤
        B * singEnvelope s (Torus.eucDist x y) := by
  obtain ⟨C, hC⟩ := periodicRiesz_grad_bound hd hs0 hsd
  obtain ⟨L, hL0, hL⟩ := exists_lipschitz_smooth hv
  refine ⟨L * max C 0 * (1 + d), by positivity, fun x y hxy => ?_⟩
  obtain ⟨z, hz, hz'⟩ := KernelGrad.exists_mk_box (x - y)
  obtain ⟨yb, hyb, hyb'⟩ := KernelGrad.exists_mk_box y
  have hr : Torus.eucDist x y = ‖z‖ := eucDist_eq_norm hz hz'
  have hz0 : z ≠ 0 := by
    rintro rfl
    apply hxy
    have : x - y = 0 := by rw [← hz]; funext i; simp [Torus.mk]
    exact sub_eq_zero.1 this
  have hrpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hxe : x = Torus.mk (yb + z) := by
    rw [Torus.mk_add, hyb, hz]; abel
  have h1 : ‖v x - v y‖ ≤ L * ‖z‖ := by
    have := hL yb z hyb' hz'
    rw [← hxe, hyb] at this
    exact this
  have h2 : ‖periodicRieszGrad d s (x - y)‖ ≤ max C 0 * (‖z‖ ^ (-s - 1) + 1) := by
    rw [← hz]
    refine (hC z hz0 hz').trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  have hzd : ‖z‖ ≤ d := box_norm_le hz'
  have hpow : 0 ≤ ‖z‖ ^ (-s) := Real.rpow_nonneg hrpos.le _
  have hmul : ‖z‖ * ‖z‖ ^ (-s - 1) = ‖z‖ ^ (-s) := by
    have := Real.rpow_add hrpos 1 (-s - 1)
    rw [Real.rpow_one] at this
    rw [← this]; congr 1; ring
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  have h3 : |inner ℝ (v x - v y) (periodicRieszGrad d s (x - y))| ≤
      L * max C 0 * (‖z‖ ^ (-s) + ‖z‖) := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    calc ‖v x - v y‖ * ‖periodicRieszGrad d s (x - y)‖
        ≤ (L * ‖z‖) * (max C 0 * (‖z‖ ^ (-s - 1) + 1)) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = L * max C 0 * (‖z‖ * ‖z‖ ^ (-s - 1) + ‖z‖) := by ring
      _ = _ := by rw [hmul]
  rw [hr]
  refine h3.trans ?_
  have hLC : 0 ≤ L * max C 0 := by positivity
  by_cases hs : s = 0
  · subst hs
    simp only [singEnvelope, ite_true, neg_zero, Real.rpow_zero]
    have hlog : 0 ≤ |Real.log ‖z‖| := abs_nonneg _
    calc L * max C 0 * (1 + ‖z‖) ≤ L * max C 0 * ((1 + d) * 1) := by gcongr; linarith
      _ ≤ L * max C 0 * ((1 + d) * (1 + |Real.log ‖z‖|)) := by gcongr; linarith
      _ = _ := by ring
  · simp only [singEnvelope, hs, ite_false]
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    calc L * max C 0 * (‖z‖ ^ (-s) + ‖z‖) ≤ L * max C 0 * ((1 + d) * (1 + ‖z‖ ^ (-s))) := by
          gcongr; nlinarith
      _ = _ := by ring

end TransportAux

/-- Proposition 4.3, last sentence (source lines 3779-3780): the transport kernel
`h_v(x,y) = (v(x) - v(y))·∇g(x-y)` of a smooth vector field `v` satisfies the same bound. -/
theorem quadStat_variance_transport (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ)
    (hβ : 0 < β) (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (v : Torus d → Euc d)
    (hv : Torus.IsSmooth v) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
      ∀ ν ∈ ({withDensityReal ρ,
          firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ))} :
            Set (Measure (Torus d))),
        (N : ℝ≥0∞) * evariance
            (fun X : Config d N =>
              quadStat (fun x y => inner ℝ (v x - v y) (periodicRieszGrad d s (x - y))) ν X)
            (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≤
          ENNReal.ofReal (C * deltaN d s N) := by
  obtain ⟨B, hB0, hB⟩ := TransportAux.transport_envelope hd hs0 hsd hv
  obtain ⟨C0, hC0⟩ := quadStat_variance hd hs0 hsd β hβ ρ hρ
  have hvc : Continuous v :=
    PoleCavityAux.continuous_of_lift' (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift v) from hv).continuous
  have hvm : Measurable v := hvc.measurable
  have hGm := KernelGrad.measurable_periodicRieszGrad (d := d) (s := s) (by exact_mod_cast hsd)
  refine ⟨C0 * B ^ 2, fun N hN ν hν => ?_⟩
  refine hC0 B (fun x y => inner ℝ (v x - v y) (periodicRieszGrad d s (x - y))) ?_ ?_ ?_ N hN ν hν
  · exact ((hvm.comp measurable_fst).sub (hvm.comp measurable_snd)).inner
      (hGm.comp (measurable_fst.sub measurable_snd))
  · intro x y
    rw [← neg_sub x y, ← neg_sub (v x) (v y), KernelGrad.periodicRieszGrad_neg_of_lt hsd, inner_neg_neg]
  · exact fun x y hxy => hB x y hxy

end HRS

end
