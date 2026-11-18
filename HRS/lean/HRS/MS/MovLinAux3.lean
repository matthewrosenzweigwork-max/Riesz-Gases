import Mathlib

/-!
# MOV-2c, part 1: the abstract Volterra (Dyson) series with a weakly singular kernel

Infrastructure for S6.2 (`W:lem:r2mov-linear`, TeX L4278-4343), namespace `HRS.MS.MovLin`, helpers `mov2c_`.
Nothing here is specific to the oscillator: a Banach space `X`, a kernel `K(τ) ∈ B(X)`, `0 < τ ≤ T0`,
strongly continuous with `‖K(τ)‖ ≤ Kc τ^(θ-1)` (`0 < θ ≤ 1`, `θ = 1 - a/2` for the application), and a free term
`F(t) ∈ B(X)` strongly continuous on `[0,T0]`, `‖F(t)‖ ≤ M`.

## What is proved

* `mov2c_beta`, `mov2c_step`: the Beta integral `∫_0^t s^p (t-s)^(θ-1) ds = t^(p+θ) Γ(p+1)Γ(θ)/Γ(p+1+θ)` (from
  `Complex.betaIntegral`) and the Volterra step on the Mittag-Leffler profile.
* `mov2c_gamma_summable`: `∑_n x^n / Γ(1 + nθ) < ∞` for all `x ≥ 0`, `θ > 0` (via `Γ(1+(n+m)θ) ≥ (1+nθ) Γ(1+nθ)`,
  `m θ ≥ 1`, and a geometric comparison).
* `mov2c_ker_apply_cont`, `mov2c_vol_int`, `mov2c_vol_cont`: for `y` continuous on `[0,T0]` with values in `Y`,
  `s ↦ K(t-s) y(s)` is interval integrable and `t ↦ ∫_0^t K(t-s) y(s) ds` is continuous on `[0,T0]`
  (the kernel is only strongly continuous; `K : Y →L Z` between two spaces).
* `mov2c_vol_unique`: the homogeneous equation `w(t) = -∫_0^t K(t-s) w(s) ds`, `w` continuous, has only `w = 0`.
* `mov2c_Tf`, `mov2c_Tf_props`, `mov2c_Tn_exists`: the iterates `T_0 = F`, `T_{n+1}(t) x = -∫_0^t K(t-s) T_n(s) x ds`
  are linear, strongly continuous, with `‖T_n(t) x‖ ≤ M (Kc Γ(θ))^n t^{nθ} / Γ(1+nθ) ‖x‖`; they are realised as
  bounded operators.
* `mov2c_volterra` (main): `T = ∑ T_n` converges in operator norm, uniformly on `[0,T0]`
  (`‖T(t)‖ ≤ ∑_n M (Kc Γ(θ) T0^θ)^n / Γ(1+nθ)`), is strongly continuous, solves
  `T(t) x = F(t) x - ∫_0^t K(t-s) T(s) x ds`, and is the unique strongly continuous solution.

Junk values: every Bochner integral is of an integrand shown to be interval integrable on `[0,t]` (continuous on
the open interval and dominated by `Kc (t-s)^(θ-1) N`) before it is used in an identity; the iterates are
defined as plain functions and are turned into bounded operators only after linearity and the bound are proved.
-/

noncomputable section

open MeasureTheory Set Filter Topology intervalIntegral

namespace HRS.MS.MovLin

/-! ## A. Beta integral, Gamma growth -/

/-- The real Beta integral `∫_0^t x^p (t-x)^(θ-1) dx = t^(p+θ) Γ(p+1) Γ(θ) / Γ(p+1+θ)`. -/
lemma mov2c_beta {θ p t : ℝ} (hθ : 0 < θ) (hp : 0 ≤ p) (ht : 0 < t) :
    ∫ x in (0 : ℝ)..t, x ^ p * (t - x) ^ (θ - 1) =
      t ^ (p + θ) * (Real.Gamma (p + 1) * Real.Gamma θ / Real.Gamma (p + 1 + θ)) := by
  have h1 := Complex.betaIntegral_scaled ((p + 1 : ℝ) : ℂ) (θ : ℂ) ht
  have h2 : Complex.betaIntegral ((p + 1 : ℝ) : ℂ) (θ : ℂ) =
      ((Real.Gamma (p + 1) * Real.Gamma θ / Real.Gamma (p + 1 + θ) : ℝ) : ℂ) := by
    rw [Complex.betaIntegral_eq_Gamma_mul_div]
    · rw [← Complex.ofReal_add, Complex.Gamma_ofReal, Complex.Gamma_ofReal, Complex.Gamma_ofReal]
      push_cast; rfl
    · simp; linarith
    · simpa using hθ
  have h3 : ∀ x ∈ uIcc (0 : ℝ) t, ((x : ℂ) ^ (((p + 1 : ℝ) : ℂ) - 1) * ((t : ℂ) - x) ^ ((θ : ℂ) - 1)) =
      (((x ^ p * (t - x) ^ (θ - 1) : ℝ)) : ℂ) := by
    intro x hx
    rw [uIcc_of_le ht.le] at hx
    have hx0 : 0 ≤ x := hx.1
    have hx1 : 0 ≤ t - x := by linarith [hx.2]
    have e1 : ((p + 1 : ℝ) : ℂ) - 1 = ((p : ℝ) : ℂ) := by push_cast; ring
    have e2 : (θ : ℂ) - 1 = ((θ - 1 : ℝ) : ℂ) := by push_cast; ring
    have e3 : (t : ℂ) - x = ((t - x : ℝ) : ℂ) := by push_cast; ring
    rw [e1, e2, e3, Complex.ofReal_mul, Complex.ofReal_cpow hx0, Complex.ofReal_cpow hx1]
  rw [intervalIntegral.integral_congr h3, intervalIntegral.integral_ofReal, h2] at h1
  have h4 : ((t : ℂ) ^ (((p + 1 : ℝ) : ℂ) + (θ : ℂ) - 1)) = ((t ^ (p + θ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow ht.le]
    congr 1; push_cast; ring
  rw [h4, ← Complex.ofReal_mul] at h1
  exact_mod_cast h1

lemma mov2c_int_rpow_mul {θ p t : ℝ} (hθ : 0 < θ) (hp : 0 ≤ p) :
    IntervalIntegrable (fun x : ℝ => (t - x) ^ (θ - 1) * x ^ p) volume 0 t := by
  have h1 : IntervalIntegrable (fun x : ℝ => (t - x) ^ (θ - 1)) volume 0 t := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t) (r := θ - 1) (by linarith)).comp_sub_left t
    simpa using this.symm
  exact h1.mul_continuousOn (Real.continuous_rpow_const hp).continuousOn

/-- One Volterra step on the Mittag-Leffler scale. -/
lemma mov2c_step {θ A K t : ℝ} (hθ : 0 < θ) (n : ℕ) (ht : 0 < t) :
    ∫ s in (0 : ℝ)..t, K * (t - s) ^ (θ - 1) * (A * s ^ ((n : ℝ) * θ) / Real.Gamma (1 + n * θ)) =
      A * K * Real.Gamma θ * t ^ (((n : ℝ) + 1) * θ) / Real.Gamma (1 + ((n : ℝ) + 1) * θ) := by
  have hp : 0 ≤ (n : ℝ) * θ := by positivity
  have h := mov2c_beta hθ hp ht
  have e : ∀ s : ℝ, K * (t - s) ^ (θ - 1) * (A * s ^ ((n : ℝ) * θ) / Real.Gamma (1 + n * θ)) =
      (K * A / Real.Gamma (1 + n * θ)) * (s ^ ((n : ℝ) * θ) * (t - s) ^ (θ - 1)) := by
    intro s; ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul, h]
  have hG : Real.Gamma (1 + n * θ) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  have e1 : (n : ℝ) * θ + 1 = 1 + n * θ := by ring
  have e2 : (n : ℝ) * θ + θ = ((n : ℝ) + 1) * θ := by ring
  have e3 : (n : ℝ) * θ + 1 + θ = 1 + ((n : ℝ) + 1) * θ := by ring
  rw [e3, e1, e2]
  field_simp

/-- The Mittag-Leffler series `∑ x^n / Γ(1 + nθ)` converges. -/
theorem mov2c_gamma_summable {θ x : ℝ} (hθ : 0 < θ) (hx : 0 ≤ x) :
    Summable (fun n : ℕ => x ^ n / Real.Gamma (1 + n * θ)) := by
  set m : ℕ := ⌈1 / θ⌉₊ with hm
  have hmθ : 1 ≤ (m : ℝ) * θ := by
    have h1 : 1 / θ ≤ (m : ℝ) := Nat.le_ceil _
    have := mul_le_mul_of_nonneg_right h1 hθ.le
    rwa [one_div, inv_mul_cancel₀ hθ.ne'] at this
  have hm1 : 1 ≤ m := by
    by_contra h
    have : m = 0 := by omega
    have h0 : (m : ℝ) = 0 := by exact_mod_cast this
    rw [h0] at hmθ; norm_num at hmθ
  have hGpos : ∀ n : ℕ, 0 < Real.Gamma (1 + n * θ) := fun n =>
    Real.Gamma_pos_of_pos (by positivity)
  -- the term `f n`
  set f : ℕ → ℝ := fun n => x ^ n / Real.Gamma (1 + n * θ) with hf
  have hf0 : ∀ n, 0 ≤ f n := fun n => div_nonneg (pow_nonneg hx _) (hGpos n).le
  -- Gamma growth
  have hgrow : ∀ n : ℕ, (1 + n * θ) * Real.Gamma (1 + n * θ) ≤ Real.Gamma (1 + ((n + m : ℕ) : ℝ) * θ) := by
    intro n
    have h2 : Real.Gamma (1 + n * θ + 1) = (1 + n * θ) * Real.Gamma (1 + n * θ) :=
      Real.Gamma_add_one (by positivity)
    rw [← h2]
    apply Real.Gamma_strictMonoOn_Ici.monotoneOn
    · show (2 : ℝ) ≤ 1 + n * θ + 1
      have : 0 ≤ (n : ℝ) * θ := by positivity
      linarith
    · show (2 : ℝ) ≤ 1 + ((n + m : ℕ) : ℝ) * θ
      push_cast
      nlinarith [hmθ, show 0 ≤ (n : ℝ) * θ by positivity]
    · push_cast
      nlinarith [hmθ]
  have hstep : ∀ n : ℕ, f (n + m) ≤ x ^ m / (1 + n * θ) * f n := by
    intro n
    have h1 : 0 < 1 + (n : ℝ) * θ := by positivity
    simp only [hf]
    rw [pow_add]
    have hG := hGpos n
    calc x ^ n * x ^ m / Real.Gamma (1 + ((n + m : ℕ) : ℝ) * θ)
        ≤ x ^ n * x ^ m / ((1 + n * θ) * Real.Gamma (1 + n * θ)) := by
          apply div_le_div_of_nonneg_left (by positivity) (by positivity) (hgrow n)
      _ = x ^ m / (1 + n * θ) * (x ^ n / Real.Gamma (1 + n * θ)) := by
          field_simp
  -- choose N
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, x ^ m / (1 + n * θ) ≤ 1 / 2 := by
    refine ⟨⌈2 * x ^ m / θ⌉₊, fun n hn => ?_⟩
    have h1 : 2 * x ^ m / θ ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
    have h2 : 2 * x ^ m ≤ n * θ := by
      have := mul_le_mul_of_nonneg_right h1 hθ.le
      rwa [div_mul_cancel₀ _ hθ.ne'] at this
    have h3 : 0 < 1 + (n : ℝ) * θ := by positivity
    rw [div_le_iff₀ h3]
    nlinarith
  have hstep2 : ∀ n ≥ N, f (n + m) ≤ 1 / 2 * f n := fun n hn =>
    (hstep n).trans (mul_le_mul_of_nonneg_right (hN n hn) (hf0 n))
  -- geometric bound
  set ρ : ℝ := (1 / 2 : ℝ) ^ ((1 : ℝ) / m) with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρm : ρ ^ m = 1 / 2 := by
    rw [hρ, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
    have : (1 : ℝ) / m * m = 1 := by
      field_simp
    rw [this, Real.rpow_one]
  have hρ1 : ρ < 1 := by
    rw [hρ]
    apply Real.rpow_lt_one (by norm_num) (by norm_num)
    positivity
  set B : ℝ := ∑ k ∈ Finset.range m, f (N + k) / ρ ^ (N + k) with hB
  have hbound : ∀ n, N ≤ n → f n ≤ B * ρ ^ n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      by_cases hlt : n < N + m
      · have hk : n - N ∈ Finset.range m := Finset.mem_range.2 (by omega)
        have := Finset.single_le_sum (f := fun k => f (N + k) / ρ ^ (N + k))
          (fun k _ => div_nonneg (hf0 _) (by positivity)) hk
        have e : N + (n - N) = n := by omega
        simp only [e] at this
        rw [← hB] at this
        rwa [div_le_iff₀ (by positivity)] at this
      · have hn' : N ≤ n - m := by omega
        have hnm : n - m < n := by omega
        have h1 := ih (n - m) hnm hn'
        have h2 := hstep2 (n - m) hn'
        have e : n - m + m = n := by omega
        rw [e] at h2
        calc f n ≤ 1 / 2 * f (n - m) := h2
          _ ≤ 1 / 2 * (B * ρ ^ (n - m)) := by gcongr
          _ = B * ρ ^ n := by
            have : ρ ^ n = ρ ^ (n - m) * ρ ^ m := by rw [← pow_add, e]
            rw [this, hρm]; ring
  have hsum : Summable (fun n : ℕ => f (n + N)) := by
    refine Summable.of_nonneg_of_le (fun n => hf0 _) (fun n => ?_)
      ((summable_geometric_of_lt_one hρ0.le hρ1).mul_left (B * ρ ^ N))
    have := hbound (n + N) (by omega)
    calc f (n + N) ≤ B * ρ ^ (n + N) := this
      _ = B * ρ ^ N * ρ ^ n := by rw [pow_add]; ring
  exact (summable_nat_add_iff N).1 hsum

/-! ## B. Weakly singular strongly continuous kernels -/

section Kernel

variable {Y Z : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- A kernel `K(τ) : Y → Z`, `0 < τ ≤ T0`, strongly continuous with `‖K(τ)‖ ≤ Kc τ^(θ-1)`. -/
structure Mov2cKer (K : ℝ → Y →L[ℝ] Z) (T0 Kc θ : ℝ) : Prop where
  Kc_nonneg : 0 ≤ Kc
  cont : ∀ y : Y, ContinuousOn (fun τ => K τ y) (Ioc 0 T0)
  bound : ∀ τ ∈ Ioc (0 : ℝ) T0, ‖K τ‖ ≤ Kc * τ ^ (θ - 1)

lemma mov2c_ker_apply_cont {K : ℝ → Y →L[ℝ] Z} {T0 Kc θ : ℝ} (hK : Mov2cKer K T0 Kc θ)
    (hθ : θ ≤ 1) {S : Set ℝ} {τ : ℝ → ℝ} {z : ℝ → Y} (hτ : ContinuousOn τ S)
    (hτS : ∀ s ∈ S, τ s ∈ Ioc (0 : ℝ) T0) (hz : ContinuousOn z S) :
    ContinuousOn (fun s => K (τ s) (z s)) S := by
  intro s0 hs0
  have hτ0 := hτS s0 hs0
  have h2 : ContinuousWithinAt (fun s => K (τ s) (z s0)) S s0 :=
    ((hK.cont (z s0)).comp hτ hτS) s0 hs0
  have h1 : Tendsto (fun s => K (τ s) (z s - z s0)) (𝓝[S] s0) (𝓝 0) := by
    have hτc : Tendsto τ (𝓝[S] s0) (𝓝 (τ s0)) := hτ s0 hs0
    have hev : ∀ᶠ s in 𝓝[S] s0, τ s0 / 2 < τ s :=
      hτc.eventually (lt_mem_nhds (by linarith [hτ0.1]))
    have hevS : ∀ᶠ s in 𝓝[S] s0, s ∈ S := self_mem_nhdsWithin
    have hzc : Tendsto (fun s => ‖z s - z s0‖) (𝓝[S] s0) (𝓝 0) := by
      have := (hz s0 hs0).sub_const (z s0)
      have h := this.norm
      simpa using h
    have hB : Tendsto (fun s => (Kc * (τ s0 / 2) ^ (θ - 1)) * ‖z s - z s0‖) (𝓝[S] s0) (𝓝 0) := by
      simpa using hzc.const_mul (Kc * (τ s0 / 2) ^ (θ - 1))
    refine squeeze_zero_norm' ?_ hB
    filter_upwards [hev, hevS] with s hs hsS
    have hτs := hτS s hsS
    calc ‖K (τ s) (z s - z s0)‖ ≤ ‖K (τ s)‖ * ‖z s - z s0‖ := (K (τ s)).le_opNorm _
      _ ≤ (Kc * (τ s0 / 2) ^ (θ - 1)) * ‖z s - z s0‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        refine (hK.bound _ hτs).trans ?_
        apply mul_le_mul_of_nonneg_left _ hK.Kc_nonneg
        exact Real.rpow_le_rpow_of_nonpos (by linarith [hτ0.1]) hs.le (by linarith)
  have : (fun s => K (τ s) (z s)) = fun s => K (τ s) (z s - z s0) + K (τ s) (z s0) := by
    funext s; rw [← map_add]; congr 1; abel
  rw [ContinuousWithinAt, this]
  have h3 := h1.add h2
  simpa using h3

lemma mov2c_rpow_integrableOn {θ T0 : ℝ} (hθ : 0 < θ) :
    IntegrableOn (fun σ : ℝ => σ ^ (θ - 1)) (Ioc 0 T0) := by
  have := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := T0) (r := θ - 1) (by linarith)
  rcases le_total 0 T0 with h | h
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le h).1 this
  · simp [Ioc_eq_empty_of_le h]

/-- Integrability of `s ↦ K(t-s) y(s)` on `[0,t]`. -/
lemma mov2c_vol_int {K : ℝ → Y →L[ℝ] Z} {T0 Kc θ : ℝ} (hK : Mov2cKer K T0 Kc θ)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) {y : ℝ → Y} (hy : ContinuousOn y (Icc 0 T0)) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T0) :
    IntervalIntegrable (fun s => K (t - s) (y s)) volume 0 t := by
  rcases ht.1.eq_or_lt with h0 | hpos
  · subst h0; exact IntervalIntegrable.refl
  obtain ⟨N, hN⟩ := isCompact_Icc.exists_bound_of_continuousOn hy
  rw [intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1]
  have hsub : Ioo 0 t ⊆ Icc 0 T0 := fun s hs => ⟨hs.1.le, hs.2.le.trans ht.2⟩
  have hcont : ContinuousOn (fun s => K (t - s) (y s)) (Ioo 0 t) := by
    apply mov2c_ker_apply_cont hK hθ1 (τ := fun s => t - s) (continuousOn_const.sub continuousOn_id)
    · intro s hs; exact ⟨by linarith [hs.2], by linarith [hs.1, ht.2]⟩
    · exact hy.mono hsub
  have hbd : IntegrableOn (fun s : ℝ => Kc * N * (t - s) ^ (θ - 1)) (Ioo 0 t) := by
    have h1 : IntervalIntegrable (fun s : ℝ => (t - s) ^ (θ - 1)) volume 0 t := by
      have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t) (r := θ - 1)
        (by linarith)).comp_sub_left t
      simpa using this.symm
    exact ((intervalIntegrable_iff_integrableOn_Ioo_of_le ht.1).1 h1).const_mul (Kc * N)
  refine Integrable.mono' hbd (hcont.aestronglyMeasurable measurableSet_Ioo) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioo (fun s hs => ?_)
  have hτ : t - s ∈ Ioc (0 : ℝ) T0 := ⟨by linarith [hs.2], by linarith [hs.1, ht.2]⟩
  calc ‖K (t - s) (y s)‖ ≤ ‖K (t - s)‖ * ‖y s‖ := (K (t - s)).le_opNorm _
    _ ≤ (Kc * (t - s) ^ (θ - 1)) * N :=
        mul_le_mul (hK.bound _ hτ) (hN s (hsub hs)) (norm_nonneg _)
          (mul_nonneg hK.Kc_nonneg (Real.rpow_nonneg (by linarith [hs.2]) _))
    _ = Kc * N * (t - s) ^ (θ - 1) := by ring

end Kernel

section Volterra

variable {Y Z : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [CompleteSpace Z]

/-- Strong continuity of the Volterra convolution `t ↦ ∫_0^t K(t-s) y(s) ds` on `[0,T0]`. -/
lemma mov2c_vol_cont {K : ℝ → Y →L[ℝ] Z} {T0 Kc θ : ℝ} (hK : Mov2cKer K T0 Kc θ)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hT0 : 0 ≤ T0) {y : ℝ → Y} (hy : ContinuousOn y (Icc 0 T0)) :
    ContinuousOn (fun t => ∫ s in (0 : ℝ)..t, K (t - s) (y s)) (Icc 0 T0) := by
  obtain ⟨N, hN⟩ := isCompact_Icc.exists_bound_of_continuousOn hy
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hN 0 ⟨le_rfl, hT0⟩)
  set cl : ℝ → ℝ := fun u => max 0 (min u T0) with hcl
  have hclc : Continuous cl := by fun_prop
  have hclm : ∀ u, cl u ∈ Icc (0 : ℝ) T0 := fun u =>
    ⟨le_max_left _ _, max_le hT0 (min_le_right _ _)⟩
  set yh : ℝ → Y := fun u => y (cl u) with hyh
  have hyhc : Continuous yh := hy.comp_continuous hclc hclm
  have hyhb : ∀ u, ‖yh u‖ ≤ N := fun u => hN _ (hclm u)
  set Φ : ℝ → ℝ → Z := fun t σ => (Iic t).indicator (fun σ => K σ (yh (t - σ))) σ with hΦ
  set H : ℝ → Z := fun t => ∫ σ in Ioc 0 T0, Φ t σ with hH
  have hEq : ∀ t ∈ Icc (0 : ℝ) T0, ∫ s in (0 : ℝ)..t, K (t - s) (y s) = H t := by
    intro t ht
    have e1 : (fun s => K (t - s) (y s)) = fun s => (fun σ => K σ (y (t - σ))) (t - s) := by
      funext s; simp
    rw [e1, intervalIntegral.integral_comp_sub_left (fun σ => K σ (y (t - σ))) t]
    simp only [sub_self, sub_zero]
    rw [intervalIntegral.integral_of_le ht.1, hH]
    simp only [hΦ]
    rw [setIntegral_indicator measurableSet_Iic, Ioc_inter_Iic, min_eq_right ht.2]
    refine setIntegral_congr_fun measurableSet_Ioc (fun σ hσ => ?_)
    have : t - σ ∈ Icc (0 : ℝ) T0 := ⟨by linarith [hσ.2], by linarith [hσ.1, ht.2]⟩
    have e : cl (t - σ) = t - σ := by
      simp only [hcl]
      rw [min_eq_left this.2, max_eq_right this.1]
    simp [hyh, e]
  have hHc : ∀ t0, ContinuousAt H t0 := by
    intro t0
    refine continuousAt_of_dominated (bound := fun σ => Kc * N * σ ^ (θ - 1)) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall (fun t => ?_)
      refine AEStronglyMeasurable.indicator ?_ measurableSet_Iic
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
      exact mov2c_ker_apply_cont hK hθ1 (τ := id) (z := fun σ => yh (t - σ)) continuousOn_id
        (fun σ hσ => hσ) (hyhc.comp (continuous_const.sub continuous_id)).continuousOn
    · refine Eventually.of_forall (fun t => ?_)
      refine ae_restrict_of_forall_mem measurableSet_Ioc (fun σ hσ => ?_)
      simp only [hΦ, Set.indicator_apply]
      split_ifs
      · calc ‖K σ (yh (t - σ))‖ ≤ ‖K σ‖ * ‖yh (t - σ)‖ := (K σ).le_opNorm _
          _ ≤ (Kc * σ ^ (θ - 1)) * N :=
            mul_le_mul (hK.bound _ hσ) (hyhb _) (norm_nonneg _)
              (mul_nonneg hK.Kc_nonneg (Real.rpow_nonneg hσ.1.le _))
          _ = Kc * N * σ ^ (θ - 1) := by ring
      · simp only [norm_zero]
        exact mul_nonneg (mul_nonneg hK.Kc_nonneg hN0) (Real.rpow_nonneg hσ.1.le _)
    · exact (mov2c_rpow_integrableOn hθ).const_mul (Kc * N)
    · have hae : ∀ᵐ σ ∂(volume : Measure ℝ), σ ∉ ({t0} : Set ℝ) :=
        (Set.finite_singleton t0).countable.ae_notMem _
      refine ae_restrict_of_ae (hae.mono (fun σ hσ => ?_))
      have hne : σ ≠ t0 := hσ
      rcases lt_or_gt_of_ne hne with h | h
      · have : (fun t => Φ t σ) =ᶠ[𝓝 t0] fun t => K σ (yh (t - σ)) := by
          filter_upwards [eventually_gt_nhds h] with t ht
          simp [hΦ, Set.indicator_apply, ht.le]
        refine ContinuousAt.congr ?_ this.symm
        exact (K σ).continuous.continuousAt.comp
          ((hyhc.comp (continuous_id.sub continuous_const)).continuousAt)
      · have : (fun t => Φ t σ) =ᶠ[𝓝 t0] fun _ => (0 : Z) := by
          filter_upwards [eventually_lt_nhds h] with t ht
          simp [hΦ, Set.indicator_apply, not_le.2 ht]
        exact (continuousAt_const).congr this.symm
  intro t ht
  refine ((hHc t).continuousWithinAt).congr (fun u hu => hEq u hu) (hEq t ht)

/-- Norm of a Volterra integral dominated by the Mittag-Leffler profile. -/
lemma mov2c_integral_norm_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {v : ℝ → E}
    {t Kc A θ : ℝ} (hθ : 0 < θ) (hKc : 0 ≤ Kc) (hA : 0 ≤ A) (n : ℕ) (ht : 0 ≤ t)
    (hv : ∀ s ∈ Ioo 0 t, ‖v s‖ ≤ Kc * (t - s) ^ (θ - 1) * (A * s ^ ((n : ℝ) * θ) / Real.Gamma (1 + n * θ))) :
    ‖∫ s in (0 : ℝ)..t, v s‖ ≤
      A * Kc * Real.Gamma θ * t ^ (((n : ℝ) + 1) * θ) / Real.Gamma (1 + ((n : ℝ) + 1) * θ) := by
  have hpos : 0 < Real.Gamma (1 + ((n : ℝ) + 1) * θ) := Real.Gamma_pos_of_pos (by positivity)
  have hGθ : 0 < Real.Gamma θ := Real.Gamma_pos_of_pos hθ
  rcases ht.eq_or_lt with h0 | htp
  · subst h0
    simp only [intervalIntegral.integral_same, norm_zero]
    positivity
  · rw [← mov2c_step (A := A) (K := Kc) hθ n htp]
    refine intervalIntegral.norm_integral_le_of_norm_le htp.le ?_ ?_
    · have hae : ∀ᵐ s ∂(volume : Measure ℝ), s ∉ ({t} : Set ℝ) :=
        (Set.finite_singleton t).countable.ae_notMem _
      refine hae.mono (fun s hs hsI => ?_)
      exact hv s ⟨hsI.1, lt_of_le_of_ne hsI.2 hs⟩
    · have := (mov2c_int_rpow_mul (t := t) hθ (show 0 ≤ (n : ℝ) * θ by positivity))
      convert this.const_mul (Kc * A / Real.Gamma (1 + n * θ)) using 1
      funext s; ring

end Volterra

section Single

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

lemma mov2c_pow_rpow {t θ : ℝ} (ht : 0 ≤ t) (n : ℕ) : t ^ ((n : ℝ) * θ) = (t ^ θ) ^ n := by
  rw [mul_comm, Real.rpow_mul_natCast ht]

/-- The homogeneous weakly singular Volterra equation has only the zero continuous solution. -/
theorem mov2c_vol_unique {K : ℝ → X →L[ℝ] X} {T0 Kc θ : ℝ} (hK : Mov2cKer K T0 Kc θ)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hT0 : 0 ≤ T0) {w : ℝ → X} (hw : ContinuousOn w (Icc 0 T0))
    (heq : ∀ t ∈ Icc (0 : ℝ) T0, w t = -∫ s in (0 : ℝ)..t, K (t - s) (w s)) :
    ∀ t ∈ Icc (0 : ℝ) T0, w t = 0 := by
  obtain ⟨N, hN⟩ := isCompact_Icc.exists_bound_of_continuousOn hw
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hN 0 ⟨le_rfl, hT0⟩)
  set c : ℝ := Kc * Real.Gamma θ with hc
  have hc0 : 0 ≤ c := mul_nonneg hK.Kc_nonneg (Real.Gamma_pos_of_pos hθ).le
  have key : ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) T0,
      ‖w t‖ ≤ (N * c ^ n) * t ^ ((n : ℝ) * θ) / Real.Gamma (1 + n * θ) := by
    intro n
    induction n with
    | zero => intro t ht; simpa using hN t ht
    | succ n ih =>
      intro t ht
      rw [heq t ht, norm_neg]
      have := mov2c_integral_norm_le (v := fun s => K (t - s) (w s)) (t := t) (Kc := Kc)
        (A := N * c ^ n) hθ hK.Kc_nonneg (mul_nonneg hN0 (pow_nonneg hc0 _)) n ht.1 (by
          intro s hs
          have hτ : t - s ∈ Ioc (0 : ℝ) T0 := ⟨by linarith [hs.2], by linarith [hs.1, ht.2]⟩
          have hsI : s ∈ Icc (0 : ℝ) T0 := ⟨hs.1.le, hs.2.le.trans ht.2⟩
          calc ‖K (t - s) (w s)‖ ≤ ‖K (t - s)‖ * ‖w s‖ := (K (t - s)).le_opNorm _
            _ ≤ (Kc * (t - s) ^ (θ - 1)) * ((N * c ^ n) * s ^ ((n : ℝ) * θ) / Real.Gamma (1 + n * θ)) :=
              mul_le_mul (hK.bound _ hτ) (ih s hsI) (norm_nonneg _)
                (mul_nonneg hK.Kc_nonneg (Real.rpow_nonneg (by linarith [hs.2]) _))
            _ = _ := by ring)
      refine this.trans (le_of_eq ?_)
      push_cast
      rw [hc]; ring
  intro t ht
  have hsum := mov2c_gamma_summable hθ (x := c * t ^ θ) (mul_nonneg hc0 (Real.rpow_nonneg ht.1 _))
  have hlim := (hsum.tendsto_atTop_zero).const_mul N
  have hle : ∀ n : ℕ, ‖w t‖ ≤ N * ((c * t ^ θ) ^ n / Real.Gamma (1 + n * θ)) := by
    intro n
    refine (key n t ht).trans (le_of_eq ?_)
    rw [mov2c_pow_rpow ht.1, mul_pow]; ring
  have := ge_of_tendsto' hlim hle
  simp only [mul_zero] at this
  exact norm_le_zero_iff.1 this

/-- The Volterra iterates as plain functions: `T_0 = F`, `T_{n+1}(t) x = -∫_0^t K(t-s) T_n(s) x ds`. -/
def mov2c_Tf (K F : ℝ → X →L[ℝ] X) : ℕ → ℝ → X → X
  | 0, t, x => F t x
  | n + 1, t, x => -∫ s in (0 : ℝ)..t, K (t - s) (mov2c_Tf K F n s x)

lemma mov2c_Tf_zero (K F : ℝ → X →L[ℝ] X) (t : ℝ) (x : X) : mov2c_Tf K F 0 t x = F t x := rfl

lemma mov2c_Tf_succ (K F : ℝ → X →L[ℝ] X) (n : ℕ) (t : ℝ) (x : X) :
    mov2c_Tf K F (n + 1) t x = -∫ s in (0 : ℝ)..t, K (t - s) (mov2c_Tf K F n s x) := rfl

/-- Properties of the iterates: continuity, linearity and the Mittag-Leffler bound. -/
theorem mov2c_Tf_props {K F : ℝ → X →L[ℝ] X} {T0 Kc θ M : ℝ} (hK : Mov2cKer K T0 Kc θ)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hT0 : 0 ≤ T0)
    (hF : ∀ x, ContinuousOn (fun t => F t x) (Icc 0 T0)) (hM : ∀ t ∈ Icc (0 : ℝ) T0, ‖F t‖ ≤ M) :
    ∀ n : ℕ,
      (∀ x, ContinuousOn (fun t => mov2c_Tf K F n t x) (Icc 0 T0)) ∧
      (∀ t ∈ Icc (0 : ℝ) T0, ∀ x y, mov2c_Tf K F n t (x + y) = mov2c_Tf K F n t x + mov2c_Tf K F n t y) ∧
      (∀ t ∈ Icc (0 : ℝ) T0, ∀ (a : ℝ) x, mov2c_Tf K F n t (a • x) = a • mov2c_Tf K F n t x) ∧
      (∀ t ∈ Icc (0 : ℝ) T0, ∀ x, ‖mov2c_Tf K F n t x‖ ≤
        (M * (Kc * Real.Gamma θ) ^ n * ‖x‖) * t ^ ((n : ℝ) * θ) / Real.Gamma (1 + n * θ)) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, hT0⟩)
  have hc0 : 0 ≤ Kc * Real.Gamma θ := mul_nonneg hK.Kc_nonneg (Real.Gamma_pos_of_pos hθ).le
  intro n
  induction n with
  | zero =>
    refine ⟨hF, ?_, ?_, ?_⟩
    · intro t _ x y; simp [mov2c_Tf_zero]
    · intro t _ a x; simp [mov2c_Tf_zero]
    · intro t ht x
      simp only [mov2c_Tf_zero]
      simp only [pow_zero, mul_one, Nat.cast_zero, zero_mul, Real.rpow_zero, add_zero,
        Real.Gamma_one, div_one]
      calc ‖F t x‖ ≤ ‖F t‖ * ‖x‖ := (F t).le_opNorm _
        _ ≤ M * ‖x‖ := mul_le_mul_of_nonneg_right (hM t ht) (norm_nonneg _)
  | succ n ih =>
    obtain ⟨ihc, iha, ihs, ihb⟩ := ih
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x
      have := mov2c_vol_cont hK hθ hθ1 hT0 (ihc x)
      exact ContinuousOn.congr this.neg (fun t _ => by simp [mov2c_Tf_succ])
    · intro t ht x y
      simp only [mov2c_Tf_succ]
      have e : ∫ s in (0 : ℝ)..t, K (t - s) (mov2c_Tf K F n s (x + y)) =
          ∫ s in (0 : ℝ)..t, (K (t - s) (mov2c_Tf K F n s x) + K (t - s) (mov2c_Tf K F n s y)) := by
        refine intervalIntegral.integral_congr (fun s hs => ?_)
        rw [uIcc_of_le ht.1] at hs
        beta_reduce
        rw [iha s ⟨hs.1, hs.2.trans ht.2⟩, map_add]
      rw [e, intervalIntegral.integral_add (mov2c_vol_int hK hθ hθ1 (ihc x) ht)
        (mov2c_vol_int hK hθ hθ1 (ihc y) ht), neg_add]
    · intro t ht a x
      simp only [mov2c_Tf_succ]
      have e : ∫ s in (0 : ℝ)..t, K (t - s) (mov2c_Tf K F n s (a • x)) =
          ∫ s in (0 : ℝ)..t, a • K (t - s) (mov2c_Tf K F n s x) := by
        refine intervalIntegral.integral_congr (fun s hs => ?_)
        rw [uIcc_of_le ht.1] at hs
        beta_reduce
        rw [ihs s ⟨hs.1, hs.2.trans ht.2⟩, map_smul]
      rw [e, intervalIntegral.integral_smul, smul_neg]
    · intro t ht x
      rw [mov2c_Tf_succ, norm_neg]
      have := mov2c_integral_norm_le (v := fun s => K (t - s) (mov2c_Tf K F n s x)) (t := t)
        (Kc := Kc) (A := M * (Kc * Real.Gamma θ) ^ n * ‖x‖) hθ hK.Kc_nonneg
        (mul_nonneg (mul_nonneg hM0 (pow_nonneg hc0 _)) (norm_nonneg _)) n ht.1 (by
          intro s hs
          have hτ : t - s ∈ Ioc (0 : ℝ) T0 := ⟨by linarith [hs.2], by linarith [hs.1, ht.2]⟩
          have hsI : s ∈ Icc (0 : ℝ) T0 := ⟨hs.1.le, hs.2.le.trans ht.2⟩
          calc ‖K (t - s) (mov2c_Tf K F n s x)‖ ≤ ‖K (t - s)‖ * ‖mov2c_Tf K F n s x‖ :=
                (K (t - s)).le_opNorm _
            _ ≤ (Kc * (t - s) ^ (θ - 1)) *
                ((M * (Kc * Real.Gamma θ) ^ n * ‖x‖) * s ^ ((n : ℝ) * θ) / Real.Gamma (1 + n * θ)) :=
              mul_le_mul (hK.bound _ hτ) (ihb s hsI x) (norm_nonneg _)
                (mul_nonneg hK.Kc_nonneg (Real.rpow_nonneg (by linarith [hs.2]) _))
            _ = _ := by ring)
      refine this.trans (le_of_eq ?_)
      push_cast
      ring

/-- Bounded-operator versions of the iterates. -/
theorem mov2c_Tn_exists {K F : ℝ → X →L[ℝ] X} {T0 Kc θ M : ℝ} (hK : Mov2cKer K T0 Kc θ)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hT0 : 0 ≤ T0)
    (hF : ∀ x, ContinuousOn (fun t => F t x) (Icc 0 T0)) (hM : ∀ t ∈ Icc (0 : ℝ) T0, ‖F t‖ ≤ M) :
    ∃ Tn : ℕ → ℝ → X →L[ℝ] X, ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) T0,
      (∀ x, Tn n t x = mov2c_Tf K F n t x) ∧
        ‖Tn n t‖ ≤ M * (Kc * Real.Gamma θ) ^ n * t ^ ((n : ℝ) * θ) / Real.Gamma (1 + n * θ) := by
  classical
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, hT0⟩)
  have hc0 : 0 ≤ Kc * Real.Gamma θ := mul_nonneg hK.Kc_nonneg (Real.Gamma_pos_of_pos hθ).le
  have props := mov2c_Tf_props hK hθ hθ1 hT0 hF hM
  have h : ∀ (n : ℕ) (t : ℝ), ∃ A : X →L[ℝ] X, t ∈ Icc (0 : ℝ) T0 →
      (∀ x, A x = mov2c_Tf K F n t x) ∧
        ‖A‖ ≤ M * (Kc * Real.Gamma θ) ^ n * t ^ ((n : ℝ) * θ) / Real.Gamma (1 + n * θ) := by
    intro n t
    by_cases ht : t ∈ Icc (0 : ℝ) T0
    · obtain ⟨_, hadd, hsmul, hb⟩ := props n
      let lin : X →ₗ[ℝ] X :=
        { toFun := mov2c_Tf K F n t
          map_add' := hadd t ht
          map_smul' := fun a x => hsmul t ht a x }
      have hB : 0 ≤ M * (Kc * Real.Gamma θ) ^ n * t ^ ((n : ℝ) * θ) / Real.Gamma (1 + n * θ) := by
        have := Real.Gamma_pos_of_pos (show 0 < 1 + (n : ℝ) * θ by positivity)
        have := Real.rpow_nonneg ht.1 ((n : ℝ) * θ)
        positivity
      have hbd : ∀ x, ‖lin x‖ ≤
          (M * (Kc * Real.Gamma θ) ^ n * t ^ ((n : ℝ) * θ) / Real.Gamma (1 + n * θ)) * ‖x‖ := by
        intro x
        have := hb t ht x
        calc ‖lin x‖ = ‖mov2c_Tf K F n t x‖ := rfl
          _ ≤ _ := this
          _ = _ := by ring
      exact ⟨lin.mkContinuous _ hbd, fun _ => ⟨fun x => rfl, LinearMap.mkContinuous_norm_le _ hB _⟩⟩
    · exact ⟨0, fun h => absurd h ht⟩
  choose Tn hTn using h
  exact ⟨Tn, fun n t ht => hTn n t ht⟩

/-- **Abstract Volterra (Dyson) series on a Banach space.**  Kernel `K(τ) ∈ B(X)`, `0 < τ ≤ T0`,
strongly continuous with `‖K(τ)‖ ≤ Kc τ^(θ-1)`, `0 < θ ≤ 1`, free term `F` strongly continuous on `[0,T0]`
with `‖F(t)‖ ≤ M`.  Then `T_0 = F`, `T_{n+1}(t) x = -∫_0^t K(t-s) T_n(s) x ds` are bounded operators with
`‖T_n(t)‖ ≤ M (Kc Γ(θ))^n t^{nθ}/Γ(1+nθ)`, strongly continuous; `T = ∑ T_n` converges in operator norm,
uniformly on `[0,T0]`, is strongly continuous, solves `T(t) x = F(t) x - ∫_0^t K(t-s) T(s) x ds`, and is the unique
strongly continuous solution. -/
theorem mov2c_volterra {K F : ℝ → X →L[ℝ] X} {T0 Kc θ M : ℝ} (hK : Mov2cKer K T0 Kc θ)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hT0 : 0 ≤ T0)
    (hF : ∀ x, ContinuousOn (fun t => F t x) (Icc 0 T0)) (hM : ∀ t ∈ Icc (0 : ℝ) T0, ‖F t‖ ≤ M) :
    ∃ (Tn : ℕ → ℝ → X →L[ℝ] X) (T : ℝ → X →L[ℝ] X),
      (∀ t ∈ Icc (0 : ℝ) T0, Tn 0 t = F t) ∧
      (∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) T0, ∀ x, Tn (n + 1) t x = -∫ s in (0 : ℝ)..t, K (t - s) (Tn n s x)) ∧
      (∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) T0,
        ‖Tn n t‖ ≤ M * (Kc * Real.Gamma θ) ^ n * t ^ ((n : ℝ) * θ) / Real.Gamma (1 + n * θ)) ∧
      (∀ n : ℕ, ∀ x, ContinuousOn (fun t => Tn n t x) (Icc 0 T0)) ∧
      (∀ t ∈ Icc (0 : ℝ) T0, HasSum (fun n => Tn n t) (T t)) ∧
      TendstoUniformlyOn (fun (N : Finset ℕ) t => ∑ n ∈ N, Tn n t) T atTop (Icc 0 T0) ∧
      (∀ t ∈ Icc (0 : ℝ) T0,
        ‖T t‖ ≤ ∑' n : ℕ, M * (Kc * Real.Gamma θ * T0 ^ θ) ^ n / Real.Gamma (1 + n * θ)) ∧
      (∀ x, ContinuousOn (fun t => T t x) (Icc 0 T0)) ∧
      (∀ t ∈ Icc (0 : ℝ) T0, ∀ x, T t x = F t x - ∫ s in (0 : ℝ)..t, K (t - s) (T s x)) ∧
      (∀ U : ℝ → X →L[ℝ] X, (∀ x, ContinuousOn (fun t => U t x) (Icc 0 T0)) →
        (∀ t ∈ Icc (0 : ℝ) T0, ∀ x, U t x = F t x - ∫ s in (0 : ℝ)..t, K (t - s) (U s x)) →
        ∀ t ∈ Icc (0 : ℝ) T0, U t = T t) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 ⟨le_rfl, hT0⟩)
  set c : ℝ := Kc * Real.Gamma θ with hc
  have hc0 : 0 ≤ c := mul_nonneg hK.Kc_nonneg (Real.Gamma_pos_of_pos hθ).le
  have props := mov2c_Tf_props hK hθ hθ1 hT0 hF hM
  obtain ⟨Tn, hTn⟩ := mov2c_Tn_exists hK hθ hθ1 hT0 hF hM
  have hTnx : ∀ n, ∀ t ∈ Icc (0 : ℝ) T0, ∀ x, Tn n t x = mov2c_Tf K F n t x := fun n t ht => (hTn n t ht).1
  have hTnb := fun n t ht => (hTn n t ht).2
  have hTncont : ∀ n x, ContinuousOn (fun t => Tn n t x) (Icc 0 T0) := fun n x =>
    ((props n).1 x).congr (fun t ht => hTnx n t ht x)
  -- summable majorant
  set u : ℕ → ℝ := fun n => M * (c * T0 ^ θ) ^ n / Real.Gamma (1 + n * θ) with hu
  have hsumu : Summable u := by
    have := (mov2c_gamma_summable hθ (x := c * T0 ^ θ)
      (mul_nonneg hc0 (Real.rpow_nonneg hT0 _))).mul_left M
    refine this.congr (fun n => ?_)
    simp only [hu]; ring
  have hbd : ∀ n, ∀ t ∈ Icc (0 : ℝ) T0, ‖Tn n t‖ ≤ u n := by
    intro n t ht
    have hG : 0 < Real.Gamma (1 + n * θ) := Real.Gamma_pos_of_pos (by positivity)
    have h1 : t ^ ((n : ℝ) * θ) ≤ T0 ^ ((n : ℝ) * θ) :=
      Real.rpow_le_rpow ht.1 ht.2 (by positivity)
    have e : u n = M * c ^ n * T0 ^ ((n : ℝ) * θ) / Real.Gamma (1 + n * θ) := by
      simp only [hu]; rw [mul_pow, mov2c_pow_rpow hT0 n]; ring
    rw [e]
    calc ‖Tn n t‖ ≤ M * c ^ n * t ^ ((n : ℝ) * θ) / Real.Gamma (1 + n * θ) := hTnb n t ht
      _ ≤ M * c ^ n * T0 ^ ((n : ℝ) * θ) / Real.Gamma (1 + n * θ) := by
        have : 0 ≤ M * c ^ n := mul_nonneg hM0 (pow_nonneg hc0 _)
        gcongr
  have hsumT : ∀ t ∈ Icc (0 : ℝ) T0, Summable (fun n => Tn n t) := fun t ht =>
    Summable.of_norm_bounded hsumu (fun n => hbd n t ht)
  set T : ℝ → X →L[ℝ] X := fun t => ∑' n, Tn n t with hT
  have hHS : ∀ t ∈ Icc (0 : ℝ) T0, HasSum (fun n => Tn n t) (T t) := fun t ht =>
    (hsumT t ht).hasSum
  have hHSx : ∀ t ∈ Icc (0 : ℝ) T0, ∀ x, HasSum (fun n => Tn n t x) (T t x) := fun t ht x =>
    (hHS t ht).mapL (ContinuousLinearMap.apply ℝ X x)
  have hunif : TendstoUniformlyOn (fun (N : Finset ℕ) t => ∑ n ∈ N, Tn n t) T atTop (Icc 0 T0) :=
    tendstoUniformlyOn_tsum hsumu (fun n t ht => hbd n t ht)
  have hTbound : ∀ t ∈ Icc (0 : ℝ) T0, ‖T t‖ ≤ ∑' n, u n := by
    intro t ht
    have hs : Summable (fun n => ‖Tn n t‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => hbd n t ht) hsumu
    calc ‖T t‖ ≤ ∑' n, ‖Tn n t‖ := norm_tsum_le_tsum_norm hs
      _ ≤ ∑' n, u n := hs.tsum_le_tsum (fun n => hbd n t ht) hsumu
  have hTcont : ∀ x, ContinuousOn (fun t => T t x) (Icc 0 T0) := by
    intro x
    have h := continuousOn_tsum (f := fun n t => Tn n t x) (u := fun n => u n * ‖x‖)
      (fun n => hTncont n x) (hsumu.mul_right ‖x‖) (fun n t ht =>
        ((Tn n t).le_opNorm x).trans (mul_le_mul_of_nonneg_right (hbd n t ht) (norm_nonneg _)))
    exact h.congr (fun t ht => (hHSx t ht x).tsum_eq.symm)
  have hrec : ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) T0, ∀ x,
      Tn (n + 1) t x = -∫ s in (0 : ℝ)..t, K (t - s) (Tn n s x) := by
    intro n t ht x
    rw [hTnx _ t ht, mov2c_Tf_succ]
    congr 1
    refine intervalIntegral.integral_congr (fun s hs => ?_)
    rw [uIcc_of_le ht.1] at hs
    beta_reduce
    rw [hTnx n s ⟨hs.1, hs.2.trans ht.2⟩]
  have hduh : ∀ t ∈ Icc (0 : ℝ) T0, ∀ x,
      T t x = F t x - ∫ s in (0 : ℝ)..t, K (t - s) (T s x) := by
    intro t ht x
    have hsx : Summable (fun n => Tn n t x) := (hHSx t ht x).summable
    rw [← (hHSx t ht x).tsum_eq, hsx.tsum_eq_zero_add]
    have h0 : Tn 0 t x = F t x := by rw [hTnx 0 t ht]; rfl
    set μ : Measure ℝ := (volume : Measure ℝ).restrict (Ioc 0 t) with hμ
    set Fn : ℕ → ℝ → X := fun n s => K (t - s) (Tn n s x) with hFn
    have hint : ∀ n, Integrable (Fn n) μ := fun n =>
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).1
        (mov2c_vol_int hK hθ hθ1 (hTncont n x) ht)
    have hnormle : ∀ n : ℕ, ∫ s, ‖Fn n s‖ ∂μ ≤
        (M * c ^ n * ‖x‖) * Kc * Real.Gamma θ * t ^ (((n : ℝ) + 1) * θ) /
          Real.Gamma (1 + ((n : ℝ) + 1) * θ) := by
      intro n
      have h1 := mov2c_integral_norm_le (v := fun s => ‖Fn n s‖) (t := t) (Kc := Kc)
        (A := M * c ^ n * ‖x‖) hθ hK.Kc_nonneg
        (mul_nonneg (mul_nonneg hM0 (pow_nonneg hc0 _)) (norm_nonneg _)) n ht.1 (by
          intro s hs
          have hτ : t - s ∈ Ioc (0 : ℝ) T0 := ⟨by linarith [hs.2], by linarith [hs.1, ht.2]⟩
          have hsI : s ∈ Icc (0 : ℝ) T0 := ⟨hs.1.le, hs.2.le.trans ht.2⟩
          rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
          calc ‖K (t - s) (Tn n s x)‖ ≤ ‖K (t - s)‖ * ‖Tn n s x‖ := (K (t - s)).le_opNorm _
            _ ≤ (Kc * (t - s) ^ (θ - 1)) *
                ((M * c ^ n * s ^ ((n : ℝ) * θ) / Real.Gamma (1 + n * θ)) * ‖x‖) :=
              mul_le_mul (hK.bound _ hτ)
                (((Tn n s).le_opNorm x).trans (mul_le_mul_of_nonneg_right (hTnb n s hsI)
                  (norm_nonneg _))) (norm_nonneg _)
                (mul_nonneg hK.Kc_nonneg (Real.rpow_nonneg (by linarith [hs.2]) _))
            _ = _ := by ring)
      calc ∫ s, ‖Fn n s‖ ∂μ = ∫ s in (0 : ℝ)..t, ‖Fn n s‖ := by
            rw [intervalIntegral.integral_of_le ht.1]
        _ ≤ ‖∫ s in (0 : ℝ)..t, ‖Fn n s‖‖ := by rw [Real.norm_eq_abs]; exact le_abs_self _
        _ ≤ _ := h1
    have hsb : Summable (fun n : ℕ => (M * c ^ n * ‖x‖) * Kc * Real.Gamma θ *
        t ^ (((n : ℝ) + 1) * θ) / Real.Gamma (1 + ((n : ℝ) + 1) * θ)) := by
      have h := ((summable_nat_add_iff 1).2
        (mov2c_gamma_summable hθ (x := c * t ^ θ) (mul_nonneg hc0 (Real.rpow_nonneg ht.1 _)))).mul_left
          (M * ‖x‖)
      refine h.congr (fun n => ?_)
      have e1 : t ^ (((n : ℝ) + 1) * θ) = (t ^ θ) ^ (n + 1) := by
        have := mov2c_pow_rpow (θ := θ) ht.1 (n + 1)
        push_cast at this
        exact this
      rw [e1]
      push_cast
      simp only [hc]
      ring
    have hnorm : Summable (fun n => ∫ s, ‖Fn n s‖ ∂μ) :=
      Summable.of_nonneg_of_le (fun n => integral_nonneg (fun s => norm_nonneg _)) hnormle hsb
    have hHS2 := hasSum_integral_of_summable_integral_norm hint hnorm
    have hI : ∫ s, ∑' n, Fn n s ∂μ = ∫ s in (0 : ℝ)..t, K (t - s) (T s x) := by
      rw [intervalIntegral.integral_of_le ht.1]
      refine setIntegral_congr_fun measurableSet_Ioc (fun s hs => ?_)
      have hsI : s ∈ Icc (0 : ℝ) T0 := ⟨hs.1.le, hs.2.trans ht.2⟩
      simp only [hFn]
      rw [← (hHSx s hsI x).tsum_eq]
      exact ((K (t - s)).map_tsum (hHSx s hsI x).summable).symm
    rw [hI] at hHS2
    have hI2 : ∀ n, ∫ s, Fn n s ∂μ = ∫ s in (0 : ℝ)..t, K (t - s) (Tn n s x) := fun n => by
      rw [intervalIntegral.integral_of_le ht.1]
    have hfin : ∑' n, Tn (n + 1) t x = -∫ s in (0 : ℝ)..t, K (t - s) (T s x) := by
      simp_rw [hrec _ t ht x]
      rw [tsum_neg]
      simp_rw [← hI2]
      rw [hHS2.tsum_eq]
    rw [h0, hfin]; abel
  refine ⟨Tn, T, ?_, hrec, hTnb, hTncont, hHS, hunif, ?_, hTcont, hduh, ?_⟩
  · intro t ht; ext x; rw [hTnx 0 t ht]; rfl
  · intro t ht; exact hTbound t ht
  · intro U hUc hUd t ht
    ext x
    have hw := mov2c_vol_unique hK hθ hθ1 hT0 (w := fun s => U s x - T s x)
      ((hUc x).sub (hTcont x)) (by
        intro t ht
        beta_reduce
        rw [hUd t ht x, hduh t ht x]
        have e : ∫ s in (0 : ℝ)..t, K (t - s) (U s x - T s x) =
            (∫ s in (0 : ℝ)..t, K (t - s) (U s x)) - ∫ s in (0 : ℝ)..t, K (t - s) (T s x) := by
          simp_rw [map_sub]
          exact intervalIntegral.integral_sub (mov2c_vol_int hK hθ hθ1 (hUc x) ht)
            (mov2c_vol_int hK hθ hθ1 (hTcont x) ht)
        rw [e]; abel) t ht
    exact sub_eq_zero.1 hw

end Single

end HRS.MS.MovLin
