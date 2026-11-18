import HRS.Uniform.Q54cAux56
import HRS.Energy.Coercivity
import HRS.Stochastic.EmpiricalIto
import HRS.Duality.PairingExpansion

/-!
# KID: Proposition 3.38 (`comparison_kernel_identity`), helper file 1

PLAN (chain of sub-lemmas; sizes are rough line counts).

Part A (this file, `KIDAux1`): time regularity of the mean-field path `ρ` under
`IsMeanFieldSolution` + `IsRegularMF 3 Λ`.  (The hypothesis `weak` is only a Bochner integral
identity, so a junk value `0` is possible a priori; `HRS.Uniform.Q54c.junk_interval*` handles it.)
 A1 `kid_meas_cont` (30): `r ↦ ∫ ψ ρ_r` is measurable for continuous `ψ`.
 A2 `kid_pt_meas` (120): `r ↦ ρ_r(x)` measurable (tent functions; `K = 3` only, so no Fourier series).
 A3 `kid_weak_cont` (80): `r ↦ ∫ ψ ρ_r` continuous on `[0,T]` for continuous `ψ`
    (copy of `Q54c.weak_continuity` with `K = 3`).
 A4 `kid_unif` (150): `r ↦ ρ_r` is continuous into `(C(𝕋^d), sup)` and `r ↦ ∇ρ_r` as well
    (narrow convergence + equi-Lipschitz; interpolation).
 A5 `kid_Gconv_cont` (80): `r ↦ ∇g*ρ_r` (convGradConv) uniformly continuous (`convGradConv_cbNorm_of_one_le`), bounded.
Part B (`KIDAux2`): the background term.
 B1 `fK`: `f(r,x) = ∫ h(x-y) ρ_r(y) dy` is `C²` in `x`, derivatives = convolutions of `D^j h` (250).
 B2 `wkG` continuity in `(r, x)` for the test `ψ_x = h(x-·)`, FTC: `∂_r f = ft` (150).
 B3 `IsC12Test t f ft` (50).
 B4 `B(r) = ½∬ h(x-y) ρ_r ρ_r` is `C¹` with derivative `wkG D ρ (f_r) r` (diagonal of `A(t,s)=⟨ρ_t,f_s⟩`) (200).
Part C (`KIDAux3`): Itô + expectation.
 C1 Itô for the pair term `Fpp(Y) = (2N²)⁻¹ ∑_{i≠j} h(Y_i - Y_j)` with `ito_formula_additive_time_independent` (250).
 C2 empirical Itô for `f` (`empirical_ito_of_contact`, existing) and zero-mean martingales (`integral_itoIntegral`) (150).
 C3 expectation identity and Fubini in `(r,ω)` (200).
Part D (`KIDAux4`): pointwise algebra `ppDrift - fDrift + B' = ½ Comm + micro + β offDiag(Δh)` (300).
Part E (`KIDFinal`): assembly; `comparison_kernel_identity_proof`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open HRS HRS.PDE HRS.Uniform.Q54c

namespace HRS.KID

variable {d : ℕ}

/-- Standing mean-field context of Proposition 3.38. -/
structure MFctx (D : DynData d) (T Λ : ℝ) (ρ : ℝ → Torus d → ℝ) : Prop where
  hd : 1 ≤ d
  hT : 0 ≤ T
  hV : Torus.IsCk 2 D.V
  hmf : IsMeanFieldSolution D T ρ
  hreg : IsRegularMF 3 Λ T ρ

section Basic

variable {D : DynData d} {T Λ : ℝ} {ρ : ℝ → Torus d → ℝ}

theorem MFctx.dens (c : MFctx D T Λ ρ) {r : ℝ} (hr : r ∈ Icc 0 T) : IsProbDensity (ρ r) :=
  c.hmf.density r hr

theorem MFctx.ck3 (c : MFctx D T Λ ρ) {r : ℝ} (hr : r ∈ Icc 0 T) : Torus.IsCk 3 (ρ r) :=
  (c.hreg r hr).1

theorem MFctx.cont (c : MFctx D T Λ ρ) {r : ℝ} (hr : r ∈ Icc 0 T) : Continuous (ρ r) :=
  isCk_continuous (c.ck3 hr)

theorem MFctx.cb (c : MFctx D T Λ ρ) {r : ℝ} (hr : r ∈ Icc 0 T) : Torus.cbNorm 3 (ρ r) ≤ Λ :=
  (c.hreg r hr).2

theorem MFctx.Λ_nonneg (c : MFctx D T Λ ρ) : 0 ≤ Λ :=
  (HRS.KernelGrad.cbNorm_nonneg' (ρ 0) 3).trans (c.cb ⟨le_rfl, c.hT⟩)

theorem MFctx.abs_le (c : MFctx D T Λ ρ) {r : ℝ} (hr : r ∈ Icc 0 T) (x : Torus d) :
    |ρ r x| ≤ Λ :=
  (HRS.PDE.R2Aux.abs_le_cbNorm (c.ck3 hr) x).trans (c.cb hr)

theorem MFctx.lip (c : MFctx D T Λ ρ) {r : ℝ} (hr : r ∈ Icc 0 T) :
    Torus.IsLipschitz Λ (ρ r) := by
  have h1 := HRS.PDE.R2Aux.isLipschitz_of_cbNorm
    (show Torus.IsCk 1 (ρ r) from (c.ck3 hr).of_le (by norm_num))
  have h2 : Torus.cbNorm 1 (ρ r) ≤ Λ :=
    (HRS.KernelGrad.cbNorm_mono (by norm_num : 1 ≤ 3)).trans (c.cb hr)
  intro x y
  exact (h1 x y).trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))

theorem MFctx.rel (c : MFctx D T Λ ρ) {ψ : Torus d → ℝ} (hψ : Torus.IsCk 2 ψ) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    (∫ x, ψ x * ρ t x) - (∫ x, ψ x * ρ 0 x) = ∫ r in Icc 0 t, wkG D ρ ψ r := by
  have := weak_eq_wkG c.hmf hψ ht
  rwa [pair_wDR (c.hmf.density t ht), pair_wDR (c.hmf.density 0 ⟨le_rfl, c.hT⟩)] at this

theorem MFctx.wkG_bdd (c : MFctx D T Λ ρ) {ψ : Torus d → ℝ} (hψ : Torus.IsCk 2 ψ) :
    ∃ C : ℝ, ∀ r ∈ Icc 0 T, |wkG D ρ ψ r| ≤ C :=
  wkG_bound c.hd D T Λ 3 (by norm_num) (c.hV.of_le (by norm_num)) ρ
    (fun r hr => ⟨c.dens hr, c.ck3 hr, c.cb hr⟩) ψ hψ

/-- `A1`: measurability in time of the `C²` pairings (clamped to `[0,T]`). -/
theorem MFctx.meas_C2 (c : MFctx D T Λ ρ) {ψ : Torus d → ℝ} (hψ : Torus.IsCk 2 ψ) :
    Measurable (fun r => ∫ x, ψ x * ρ (clampT T r) x) := by
  obtain ⟨C, hC⟩ := c.wkG_bdd hψ
  obtain ⟨f', hf', hff'⟩ := junk_interval_measurable c.hT (wkG D ρ ψ) (fun t => ∫ x, ψ x * ρ t x) hC
    (fun t ht => c.rel hψ ht)
  have : (fun r => ∫ x, ψ x * ρ (clampT T r) x) = fun r => f' (clampT T r) := by
    funext r; exact (hff' _ (clampT_mem c.hT r)).symm
  rw [this]; exact hf'.comp (continuous_clampT T).measurable

theorem MFctx.pair_diff (c : MFctx D T Λ ρ) {ψ χ : Torus d → ℝ} (hψ : Continuous ψ)
    (hχ : Continuous χ) {ε : ℝ} (h : ∀ x, |ψ x - χ x| ≤ ε) {t : ℝ} (ht : t ∈ Icc 0 T) :
    |(∫ x, ψ x * ρ t x) - ∫ x, χ x * ρ t x| ≤ ε := by
  have hp := c.dens ht
  have hρi : Continuous (ρ t) := c.cont ht
  have i1 : Integrable (fun x => ψ x * ρ t x) :=
    (hψ.mul hρi).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have i2 : Integrable (fun x => χ x * ρ t x) :=
    (hχ.mul hρi).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have i3 : Integrable (ρ t) := hρi.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [← integral_sub i1 i2]
  have h1 : |∫ x, (ψ x * ρ t x - χ x * ρ t x)| ≤ ∫ x, |ψ x * ρ t x - χ x * ρ t x| := by
    simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => ψ x * ρ t x - χ x * ρ t x)
  refine h1.trans ?_
  calc ∫ x, |ψ x * ρ t x - χ x * ρ t x| ≤ ∫ x, ε * ρ t x := by
        refine integral_mono ((i1.sub i2).abs) (i3.const_mul ε) fun x => ?_
        simp only
        rw [← sub_mul, abs_mul, abs_of_nonneg (hp.nonneg x)]
        exact mul_le_mul_of_nonneg_right (h x) (hp.nonneg x)
    _ = ε := by rw [integral_const_mul, hp.integral_one, mul_one]

/-- Measurability in time of the pairings with continuous test functions. -/
theorem MFctx.meas_cont (c : MFctx D T Λ ρ) {ψ : Torus d → ℝ} (hψ : Continuous ψ) :
    Measurable (fun r => ∫ x, ψ x * ρ (clampT T r) x) := by
  choose χ hχ hχψ using fun n : ℕ => exists_isCk_approx ψ hψ (1 / ((n : ℝ) + 1)) (by positivity)
  refine measurable_of_tendsto_metrizable (f := fun (n : ℕ) (r : ℝ) =>
    ∫ x, χ n x * ρ (clampT T r) x) (fun n => c.meas_C2 (hχ n)) ?_
  refine tendsto_pi_nhds.2 fun r => ?_
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_)
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  rw [Real.dist_eq, abs_sub_comm]
  exact c.pair_diff hψ (isCk_continuous (hχ n)) (hχψ n) (clampT_mem c.hT r)

end Basic

section Tent

/-- Tent function around `x` of radius `s` (for the torus sup-norm). -/
def tent (x : Torus d) (s : ℝ) (y : Torus d) : ℝ := max 0 (1 - ‖x - y‖ / s)

theorem continuous_tent (x : Torus d) (s : ℝ) : Continuous (tent x s) := by
  unfold tent
  exact continuous_const.max (continuous_const.sub ((continuous_const.sub continuous_id).norm.div_const s))

theorem tent_nonneg (x : Torus d) (s : ℝ) (y : Torus d) : 0 ≤ tent x s y := le_max_left _ _

theorem tent_eq_zero {x y : Torus d} {s : ℝ} (hs : 0 < s) (h : s ≤ ‖x - y‖) : tent x s y = 0 := by
  unfold tent
  apply max_eq_left
  rw [sub_nonpos, le_div_iff₀ hs]
  linarith

theorem tent_self (x : Torus d) {s : ℝ} (hs : 0 < s) : tent x s x = 1 := by
  simp [tent]

/-- The mass of a tent. -/
def tentMass (d : ℕ) (s : ℝ) : ℝ := ∫ z : Torus d, max 0 (1 - ‖z‖ / s)

theorem integral_tent (x : Torus d) (s : ℝ) : ∫ y, tent x s y = tentMass d s := by
  unfold tent tentMass
  exact integral_sub_left_eq_self (fun z : Torus d => max 0 (1 - ‖z‖ / s)) volume x

theorem tentMass_pos {s : ℝ} (hs : 0 < s) : 0 < tentMass d s := by
  have h := integral_tent (d := d) 0 s
  rw [← h]
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := (0 : Torus d))
    (continuous_tent 0 s) (HasCompactSupport.of_compactSpace _) (tent_nonneg 0 s) ?_
  rw [tent_self 0 hs]; exact one_ne_zero

theorem tent_avg_err {s : ℝ} (hs : 0 < s) {g : Torus d → ℝ} {L : ℝ} (hL0 : 0 ≤ L)
    (hL : Torus.IsLipschitz L g) (hg : Continuous g) (x : Torus d) :
    |(∫ y, tent x s y * g y) - tentMass d s * g x| ≤ tentMass d s * (L * d * s) := by
  have hti : Integrable (tent x s) :=
    (continuous_tent x s).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have i1 : Integrable (fun y => tent x s y * g y) :=
    ((continuous_tent x s).mul hg).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have i2 : Integrable (fun y => tent x s y * g x) := hti.mul_const _
  have h1 : (∫ y, tent x s y * g y) - tentMass d s * g x = ∫ y, tent x s y * (g y - g x) := by
    have e : ∫ y, tent x s y * (g y - g x) = (∫ y, tent x s y * g y) - (∫ y, tent x s y) * g x := by
      simp_rw [mul_sub]
      rw [integral_sub i1 i2, integral_mul_const]
    rw [e, integral_tent]
  rw [h1]
  have hpt : ∀ y, |tent x s y * (g y - g x)| ≤ tent x s y * (L * d * s) := by
    intro y
    rw [abs_mul, abs_of_nonneg (tent_nonneg x s y)]
    by_cases hy : s ≤ ‖x - y‖
    · rw [tent_eq_zero hs hy]; simp
    · push_neg at hy
      refine mul_le_mul_of_nonneg_left ?_ (tent_nonneg x s y)
      have h2 := hL y x
      have h3 : Torus.tdist y x ≤ d * ‖x - y‖ := by
        have := HRS.Duality.tdist_le_norm_mul (d := d) y x
        rwa [norm_sub_rev] at this
      calc |g y - g x| ≤ L * Torus.tdist y x := h2
        _ ≤ L * (d * ‖x - y‖) := mul_le_mul_of_nonneg_left h3 hL0
        _ ≤ L * (d * s) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hy.le (Nat.cast_nonneg d)) hL0
        _ = L * d * s := by ring
  have i3 : Integrable (fun y => tent x s y * (g y - g x)) := i1.sub i2 |>.congr (Eventually.of_forall fun y => by simp [mul_sub])
  calc |∫ y, tent x s y * (g y - g x)| ≤ ∫ y, |tent x s y * (g y - g x)| := by
        simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun y => tent x s y * (g y - g x))
    _ ≤ ∫ y, tent x s y * (L * d * s) := integral_mono i3.abs (hti.mul_const _) hpt
    _ = tentMass d s * (L * d * s) := by rw [integral_mul_const, integral_tent]

end Tent

section Cont

variable {D : DynData d} {T Λ : ℝ} {ρ : ℝ → Torus d → ℝ}

/-- `A2`: pointwise measurability in time of the density. -/
theorem MFctx.pt_meas (c : MFctx D T Λ ρ) (x : Torus d) :
    Measurable (fun r => ρ (clampT T r) x) := by
  refine measurable_of_tendsto_metrizable (f := fun (m : ℕ) (r : ℝ) =>
    (∫ y, tent x (1 / ((m : ℝ) + 1)) y * ρ (clampT T r) y) / tentMass d (1 / ((m : ℝ) + 1)))
    (fun m => ?_) ?_
  · exact (c.meas_cont (continuous_tent x _)).div_const _
  · refine tendsto_pi_nhds.2 fun r => ?_
    rw [tendsto_iff_dist_tendsto_zero]
    have hr := clampT_mem c.hT r
    have hlim : Tendsto (fun m : ℕ => Λ * d * (1 / ((m : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (Λ * d)
    refine squeeze_zero (fun m => dist_nonneg) (fun m => ?_) hlim
    have hs : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    have hm := tentMass_pos (d := d) hs
    have h := tent_avg_err hs c.Λ_nonneg (c.lip hr) (c.cont hr) x
    have e : (∫ y, tent x (1 / ((m : ℝ) + 1)) y * ρ (clampT T r) y) / tentMass d (1 / ((m : ℝ) + 1))
        - ρ (clampT T r) x = ((∫ y, tent x (1 / ((m : ℝ) + 1)) y * ρ (clampT T r) y)
          - tentMass d (1 / ((m : ℝ) + 1)) * ρ (clampT T r) x) / tentMass d (1 / ((m : ℝ) + 1)) := by
      field_simp
    rw [Real.dist_eq, e, abs_div, abs_of_pos hm, div_le_iff₀ hm]
    nlinarith [h]

/-- `A3`: narrow continuity in time of the density path. -/
theorem MFctx.weak_cont (c : MFctx D T Λ ρ) {ψ : Torus d → ℝ} (hψ : Continuous ψ) :
    ContinuousOn (fun t => ∫ x, ψ x * ρ t x) (Icc 0 T) := by
  set ρt : ℝ → Torus d → ℝ := fun r => ρ (clampT T r) with hρt
  have hcont2 : ∀ ψ : Torus d → ℝ, Torus.IsCk 2 ψ →
      ContinuousOn (fun t => ∫ x, ψ x * ρ t x) (Icc 0 T) := by
    intro ψ hψ
    obtain ⟨C, hC⟩ := c.wkG_bdd hψ
    have hmG : Measurable (wkG D ρt ψ) := measurable_wkG D ψ hψ (c.hV.of_le (by norm_num)) ρt
      (fun r => c.dens (clampT_mem c.hT r)) (fun r => c.cont (clampT_mem c.hT r)) c.pt_meas
    have hae : AEStronglyMeasurable (wkG D ρ ψ) (volume.restrict (Icc 0 T)) := by
      refine hmG.aestronglyMeasurable.congr ?_
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Icc]
      exact Eventually.of_forall fun r hr => by simp only [wkG, ρt, clampT_of_mem hr]
    exact junk_interval_continuousOn c.hT (wkG D ρ ψ) _ hC (fun t ht => c.rel hψ ht) hae
  choose χ hχ hχψ using fun n : ℕ => exists_isCk_approx ψ hψ (1 / ((n : ℝ) + 1)) (by positivity)
  have hunif : TendstoUniformlyOn (fun (n : ℕ) (t : ℝ) => ∫ x, χ n x * ρ t x)
      (fun t => ∫ x, ψ x * ρ t x) atTop (Icc 0 T) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    filter_upwards [eventually_ge_atTop N] with n hn t ht
    rw [Real.dist_eq]
    refine lt_of_le_of_lt (c.pair_diff hψ (isCk_continuous (hχ n)) (hχψ n) ht) (lt_of_le_of_lt ?_ hN)
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  exact hunif.continuousOn (Eventually.of_forall fun n => hcont2 _ (hχ n)).frequently

theorem MFctx.weak_cont_clamp (c : MFctx D T Λ ρ) {ψ : Torus d → ℝ} (hψ : Continuous ψ) :
    Continuous (fun r => ∫ x, ψ x * ρ (clampT T r) x) :=
  (c.weak_cont hψ).comp_continuous (continuous_clampT T) (fun r => clampT_mem c.hT r)

/-- Uniform tent-approximation of the pointwise values. -/
theorem MFctx.tent_unif (c : MFctx D T Λ ρ) (x : Torus d) :
    TendstoUniformly (fun (m : ℕ) (r : ℝ) =>
      (∫ y, tent x (1 / ((m : ℝ) + 1)) y * ρ (clampT T r) y) / tentMass d (1 / ((m : ℝ) + 1)))
      (fun r => ρ (clampT T r) x) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hlim : Tendsto (fun m : ℕ => Λ * d * (1 / ((m : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (Λ * d)
  filter_upwards [hlim.eventually (gt_mem_nhds hε)] with m hm r
  have hr := clampT_mem c.hT r
  have hs : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
  have hmass := tentMass_pos (d := d) hs
  have h := tent_avg_err hs c.Λ_nonneg (c.lip hr) (c.cont hr) x
  have e : (∫ y, tent x (1 / ((m : ℝ) + 1)) y * ρ (clampT T r) y) / tentMass d (1 / ((m : ℝ) + 1))
      - ρ (clampT T r) x = ((∫ y, tent x (1 / ((m : ℝ) + 1)) y * ρ (clampT T r) y)
        - tentMass d (1 / ((m : ℝ) + 1)) * ρ (clampT T r) x) / tentMass d (1 / ((m : ℝ) + 1)) := by
    field_simp
  rw [Real.dist_eq, abs_sub_comm, e, abs_div, abs_of_pos hmass]
  refine lt_of_le_of_lt ?_ hm
  rw [div_le_iff₀ hmass]
  nlinarith [h]

theorem MFctx.pt_cont (c : MFctx D T Λ ρ) (x : Torus d) :
    Continuous (fun r => ρ (clampT T r) x) := by
  refine (c.tent_unif x).continuous (Eventually.of_forall fun m => ?_).frequently
  exact (c.weak_cont_clamp (continuous_tent x _)).div_const _

theorem MFctx.equicont (c : MFctx D T Λ ρ) :
    Equicontinuous (fun r : ℝ => ρ (clampT T r)) := by
  intro x0
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  have hct : Continuous fun x : Torus d => KernelGrad.tdist x x0 := HRS.CoercAux.continuous_tdist_left x0
  have hopen : IsOpen {x : Torus d | Λ * KernelGrad.tdist x x0 < ε} :=
    isOpen_lt (continuous_const.mul hct) continuous_const
  have hmem : x0 ∈ {x : Torus d | Λ * KernelGrad.tdist x x0 < ε} := by
    simp only [Set.mem_ofPred_eq]
    rw [HRS.CoercAux.tdist_self, mul_zero]; exact hε
  filter_upwards [hopen.mem_nhds hmem] with x hx r
  rw [Real.dist_eq, abs_sub_comm]
  refine lt_of_le_of_lt ?_ hx
  exact c.lip (clampT_mem c.hT r) x x0

/-- `A4`: the clamped density path is continuous into the sup norm. -/
theorem MFctx.unif (c : MFctx D T Λ ρ) (r0 : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r in 𝓝 r0, ∀ x, |ρ (clampT T r) x - ρ (clampT T r0) x| < ε := by
  have h := (c.equicont.tendsto_uniformFun_iff_pi (𝓝 r0) (fun x => ρ (clampT T r0) x)).2
    (tendsto_pi_nhds.2 fun x => (c.pt_cont x).continuousAt)
  have h2 := (UniformFun.tendsto_iff_tendstoUniformly).1 h
  rw [Metric.tendstoUniformly_iff] at h2
  filter_upwards [h2 ε hε] with r hr x
  have := hr x
  rw [Real.dist_eq] at this
  rwa [abs_sub_comm] at this

end Cont

section Gconv

/-- The `Λ`-coefficient of the bound for the cancellation convolution. -/
def I1 (d : ℕ) (s C β : ℝ) : ℝ := ∫ z : Torus d, C * (‖z‖ ^ (β - s - 1) + ‖z‖ ^ β)

/-- The `B`-coefficient of the bound for the cancellation convolution. -/
def I2 (s C : ℝ) : ℝ := C * ((1 / 4 : ℝ) ^ (-s - 1) + 1)

theorem I1_nonneg {s C β : ℝ} (hC : 0 ≤ C) : 0 ≤ I1 d s C β := by
  unfold I1
  refine integral_nonneg fun z => ?_
  have h1 := Real.rpow_nonneg (norm_nonneg z) (β - s - 1)
  have h2 := Real.rpow_nonneg (norm_nonneg z) β
  positivity

theorem I2_nonneg {s C : ℝ} (hC : 0 ≤ C) : 0 ≤ I2 s C := by
  unfold I2
  have := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) (-s - 1)
  positivity

theorem conv_bound_gen {s C : ℝ} {G : Torus d → Euc d} (hG : KernelGrad.GoodKernel d s C G)
    {h : Torus d → ℝ} {b Lh β : ℝ} (hb : ∀ x, |h x| ≤ b) (hb0 : 0 ≤ b) (hL0 : 0 ≤ Lh)
    (hβ0 : 0 < β) (hβ : s + 1 - d < β)
    (hH : ∀ x z, ‖z‖ ≤ 1 / 4 → |h (x - z) - h x| ≤ Lh * ‖z‖ ^ β) (x : Torus d) :
    ‖convGradConv G h x‖ ≤ Lh * I1 d s C β + b * I2 s C := by
  refine (HRS.Duality.conv_norm_le hG hb hb0 hL0 hβ0 hβ hH x).trans (le_of_eq ?_)
  have hi : Integrable (fun z : Torus d => C * (‖z‖ ^ (β - s - 1) + ‖z‖ ^ β)) := by
    have := HRS.Duality.integrable_dom_holder hG (Λ := 1) (B := 0) hβ0 hβ
    refine this.congr (Eventually.of_forall fun z => ?_)
    simp
  have e : (fun z : Torus d => Lh * C * (‖z‖ ^ (β - s - 1) + ‖z‖ ^ β)
      + b * C * ((1 / 4 : ℝ) ^ (-s - 1) + 1)) =
      fun z => Lh * (C * (‖z‖ ^ (β - s - 1) + ‖z‖ ^ β)) + b * (C * ((1 / 4 : ℝ) ^ (-s - 1) + 1)) := by
    funext z; ring
  rw [e, integral_add (hi.const_mul Lh) (integrable_const _), integral_const_mul, integral_const]
  simp [I1, I2]

theorem kern_sub (G : Torus d → Euc d) (h1 h2 : Torus d → ℝ) (x z : Torus d) :
    KernelGrad.kern G (fun y => h1 y - h2 y) x z = KernelGrad.kern G h1 x z - KernelGrad.kern G h2 x z := by
  unfold KernelGrad.kern
  split_ifs <;> simp only [sub_smul] <;> abel

theorem min_le_rpow_mul {a c β : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    min a c ≤ a ^ (1 - β) * c ^ β := by
  rcases le_total a c with h | h
  · rw [min_eq_left h]
    rcases ha.eq_or_lt with h0 | hpos
    · rw [← h0]; positivity
    · calc a = a ^ (1 - β) * a ^ β := by
            rw [← Real.rpow_add hpos]; simp
        _ ≤ a ^ (1 - β) * c ^ β := by
            gcongr
  · rw [min_eq_right h]
    rcases hc.eq_or_lt with h0 | hpos
    · rw [← h0]; positivity
    · calc c = c ^ (1 - β) * c ^ β := by
            rw [← Real.rpow_add hpos]; simp
        _ ≤ a ^ (1 - β) * c ^ β := by
            gcongr

/-- The Hölder exponent used for the cancellation convolution. -/
def betaE (d : ℕ) (s : ℝ) : ℝ := (1 + max 0 (s + 1 - d)) / 2

theorem betaE_pos (d : ℕ) (s : ℝ) : 0 < betaE d s := by
  unfold betaE; have := le_max_left 0 (s + 1 - d); linarith

theorem betaE_gt {d : ℕ} {s : ℝ} (hsd : s < d) : s + 1 - d < betaE d s := by
  unfold betaE
  have h1 := le_max_right 0 (s + 1 - d)
  have h2 : max 0 (s + 1 - d) < 1 := max_lt one_pos (by linarith)
  linarith

theorem betaE_lt_one {d : ℕ} {s : ℝ} (hsd : s < d) : betaE d s < 1 := by
  unfold betaE
  have h2 : max 0 (s + 1 - d) < 1 := max_lt one_pos (by linarith)
  linarith

section GMF

variable {D : DynData d} {T Λ : ℝ} {ρ : ℝ → Torus d → ℝ}

theorem norm_tdist_bound (z x : Torus d) : Torus.tdist (x - z) x ≤ d * ‖z‖ := by
  show KernelGrad.tdist (x - z) x ≤ _
  rw [KernelGrad.tdist_eq_sub_zero]
  have : x - z - x = -z := by abel
  rw [this, KernelGrad.tdist_neg]
  exact KernelGrad.tdist_le_mul_norm z

theorem MFctx.lipN (c : MFctx D T Λ ρ) {r : ℝ} (hr : r ∈ Icc 0 T) (x z : Torus d) :
    |ρ r (x - z) - ρ r x| ≤ Λ * d * ‖z‖ := by
  have h1 := c.lip hr (x - z) x
  calc |ρ r (x - z) - ρ r x| ≤ Λ * Torus.tdist (x - z) x := h1
    _ ≤ Λ * (d * ‖z‖) := mul_le_mul_of_nonneg_left (norm_tdist_bound z x) c.Λ_nonneg
    _ = Λ * d * ‖z‖ := by ring

theorem norm_le_rpow_of_le {z : Torus d} (hz : ‖z‖ ≤ 1 / 4) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) :
    ‖z‖ ≤ ‖z‖ ^ β := by
  have h0 : 0 ≤ ‖z‖ := norm_nonneg _
  have h1 : ‖z‖ ≤ 1 := by linarith
  calc ‖z‖ = ‖z‖ ^ (1 : ℝ) := (Real.rpow_one _).symm
    _ ≤ ‖z‖ ^ β := Real.rpow_le_rpow_of_exponent_ge' h0 h1 hβ0 hβ1

theorem MFctx.holder (c : MFctx D T Λ ρ) {r : ℝ} (hr : r ∈ Icc 0 T) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β ≤ 1) (x z : Torus d) (hz : ‖z‖ ≤ 1 / 4) :
    |ρ r (x - z) - ρ r x| ≤ (Λ * d) * ‖z‖ ^ β := by
  refine (c.lipN hr x z).trans ?_
  exact mul_le_mul_of_nonneg_left (norm_le_rpow_of_le hz hβ0 hβ1) (mul_nonneg c.Λ_nonneg (Nat.cast_nonneg d))

theorem MFctx.Gbound (c : MFctx D T Λ ρ) :
    ∃ Kg : ℝ, ∀ r ∈ Icc 0 T, ∀ x, ‖convGradConv (periodicRieszGrad d D.s) (ρ r) x‖ ≤ Kg := by
  obtain ⟨C, hG⟩ := KernelGradD1.goodKernel_periodicRieszGrad_of_one_le c.hd D.hs0 D.hsd
  have hβ1 := betaE_lt_one D.hsd
  refine ⟨Λ * d * I1 d D.s C (betaE d D.s) + Λ * I2 D.s C, fun r hr x => ?_⟩
  exact conv_bound_gen hG (b := Λ) (Lh := Λ * d) (fun y => c.abs_le hr y) c.Λ_nonneg
    (mul_nonneg c.Λ_nonneg (Nat.cast_nonneg d)) (betaE_pos d D.s) (betaE_gt D.hsd)
    (fun x z hz => c.holder hr (betaE_pos d D.s).le hβ1.le x z hz) x

theorem MFctx.Gdiff (c : MFctx D T Λ ρ) (r0 : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ r in 𝓝 r0, ∀ x, ‖convGradConv (periodicRieszGrad d D.s) (ρ (clampT T r)) x -
      convGradConv (periodicRieszGrad d D.s) (ρ (clampT T r0)) x‖ < ε := by
  obtain ⟨C, hG⟩ := KernelGradD1.goodKernel_periodicRieszGrad_of_one_le c.hd D.hs0 D.hsd
  set β := betaE d D.s with hβdef
  have hβ0 := betaE_pos d D.s
  have hβ1 := betaE_lt_one D.hsd
  have hβg := betaE_gt D.hsd
  set A : ℝ := (2 * ((Λ : ℝ) * d)) ^ β * I1 d D.s C β with hA
  set B : ℝ := I2 D.s C with hB
  -- choice of the sup-norm tolerance `b`
  have hex : ∃ b : ℝ, 0 < b ∧ (2 * b) ^ (1 - β) * A + b * B < ε := by
    have hc1 : ContinuousAt (fun b : ℝ => (2 * b) ^ (1 - β) * A + b * B) 0 := by
      have h1 : ContinuousAt (fun b : ℝ => (2 * b) ^ (1 - β)) 0 :=
        (Real.continuousAt_rpow_const (2 * 0) (1 - β) (Or.inr (by linarith))).comp
          (f := fun b : ℝ => 2 * b) (x := 0) (continuous_const.mul continuous_id).continuousAt
      exact (h1.mul continuousAt_const).add (continuousAt_id.mul continuousAt_const)
    have hval : (fun b : ℝ => (2 * b) ^ (1 - β) * A + b * B) 0 = 0 := by
      simp only [mul_zero]
      rw [Real.zero_rpow (by linarith)]; simp
    have hev := hc1.eventually (gt_mem_nhds (by rw [hval]; exact hε))
    obtain ⟨b, hb1, hb2⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))).exists
    exact ⟨b, hb2, hb1⟩
  obtain ⟨b, hb0, hbε⟩ := hex
  filter_upwards [c.unif r0 hb0] with r hr x
  have hrm := clampT_mem c.hT r
  have hr0m := clampT_mem c.hT r0
  set ρ1 := ρ (clampT T r) with hρ1
  set ρ2 := ρ (clampT T r0) with hρ2
  have hlin : convGradConv (periodicRieszGrad d D.s) ρ1 x - convGradConv (periodicRieszGrad d D.s) ρ2 x =
      convGradConv (periodicRieszGrad d D.s) (fun y => ρ1 y - ρ2 y) x := by
    rw [KernelGrad.convGradConv_eq_integral_kern, KernelGrad.convGradConv_eq_integral_kern,
      KernelGrad.convGradConv_eq_integral_kern]
    simp_rw [kern_sub]
    rw [integral_sub]
    · exact HRS.Duality.integrable_kern_holder hG (c.cont hrm).measurable (fun y => c.abs_le hrm y)
        c.Λ_nonneg (mul_nonneg c.Λ_nonneg (Nat.cast_nonneg d)) hβ0 hβg
        (fun x z hz => c.holder hrm hβ0.le hβ1.le x z hz) x
    · exact HRS.Duality.integrable_kern_holder hG (c.cont hr0m).measurable (fun y => c.abs_le hr0m y)
        c.Λ_nonneg (mul_nonneg c.Λ_nonneg (Nat.cast_nonneg d)) hβ0 hβg
        (fun x z hz => c.holder hr0m hβ0.le hβ1.le x z hz) x
  rw [hlin]
  have hb : ∀ y, |ρ1 y - ρ2 y| ≤ b := fun y => (hr y).le
  have hH : ∀ x z : Torus d, ‖z‖ ≤ 1 / 4 →
      |(ρ1 (x - z) - ρ2 (x - z)) - (ρ1 x - ρ2 x)| ≤ ((2 * b) ^ (1 - β) * (2 * ((Λ : ℝ) * d)) ^ β) * ‖z‖ ^ β := by
    intro x z hz
    have h1 : |(ρ1 (x - z) - ρ2 (x - z)) - (ρ1 x - ρ2 x)| ≤ 2 * b := by
      calc _ ≤ |ρ1 (x - z) - ρ2 (x - z)| + |ρ1 x - ρ2 x| := by
            exact abs_sub (ρ1 (x - z) - ρ2 (x - z)) (ρ1 x - ρ2 x)
        _ ≤ b + b := add_le_add (hb _) (hb _)
        _ = 2 * b := by ring
    have h2 : |(ρ1 (x - z) - ρ2 (x - z)) - (ρ1 x - ρ2 x)| ≤ 2 * ((Λ * d) * ‖z‖) := by
      calc _ = |(ρ1 (x - z) - ρ1 x) - (ρ2 (x - z) - ρ2 x)| := by ring_nf
        _ ≤ |ρ1 (x - z) - ρ1 x| + |ρ2 (x - z) - ρ2 x| := abs_sub (ρ1 (x - z) - ρ1 x) (ρ2 (x - z) - ρ2 x)
        _ ≤ Λ * d * ‖z‖ + Λ * d * ‖z‖ := add_le_add (c.lipN hrm x z) (c.lipN hr0m x z)
        _ = 2 * ((Λ * d) * ‖z‖) := by ring
    have hmin := min_le_rpow_mul (a := 2 * b) (c := 2 * ((Λ * d) * ‖z‖)) (by positivity)
      (by have := c.Λ_nonneg; positivity) hβ0.le hβ1.le
    have hle : |(ρ1 (x - z) - ρ2 (x - z)) - (ρ1 x - ρ2 x)| ≤ min (2 * b) (2 * ((Λ * d) * ‖z‖)) :=
      le_min h1 h2
    refine hle.trans (hmin.trans (le_of_eq ?_))
    rw [show 2 * ((Λ * (d : ℝ)) * ‖z‖) = (2 * (Λ * d)) * ‖z‖ by ring,
      Real.mul_rpow (by have := c.Λ_nonneg; positivity) (norm_nonneg z)]
    ring
  have key := conv_bound_gen hG (h := fun y => ρ1 y - ρ2 y) (b := b) hb hb0.le
    (by have := c.Λ_nonneg; positivity) hβ0 hβg hH x
  refine lt_of_le_of_lt key ?_
  have e : (2 * b) ^ (1 - β) * (2 * ((Λ : ℝ) * d)) ^ β * I1 d D.s C β = (2 * b) ^ (1 - β) * A := by
    rw [hA]; ring
  rw [e]
  exact hbε

end GMF

end Gconv

end HRS.KID
