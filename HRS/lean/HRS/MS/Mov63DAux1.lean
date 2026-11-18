import HRS.MS.MovLinAux3

/-!
# S6.3, packet N5 (part 1): the abstract weakly singular Duhamel operator

Namespace `HRS.MS.Mov63`, helper prefix `mnd_`.  Infrastructure for S6.3 (`W:thm:r2mov-nonlinear`); not a manuscript row.

## PER-PACKET PLAN (packet N5 of `docs/SC63_REPORT.md` 2.4: the contraction, existence of the mild solution)

Statement check against the real definitions (done before any proof; nothing false, no hypothesis insufficient):

* `mov_linear_proof` gives `T = mov2d_T` on `L²_0 = MovL2Zero ρ` and a rate `c > 0` with `MovSmoothingBounds d s ρ m c C T`
  for every `m ≥ a` (the rate `c` is chosen before `m`); `a = movA d s ∈ [1, 2)` (`mov2d_a_bounds`), so the weak
  singularity `t^{-a/2}` has exponent `θ - 1 = -a/2` with `θ = 1 - a/2 ∈ (0, 1/2]`: integrable.
* `mov_B_ext H hm : OscSpace d m →L OscSpace d m →L OscSpace d (m - a)` (`d/2 + 3 < m`) with `‖B(v,w)‖ ≤ K‖v‖‖w‖`
  (`mov_B_ext_bound`) and mass conservation `⟨B(v,w), √ρ₀⟩ = 0` (`mov_B_ext_mass`): so `B` takes `Σ^m × Σ^m` into `Σ^{m-a} ∩ L²_0`.
* The decay/smoothing bounds are stated for functions in `L²_0` (`MovSmoothingBounds`); the scale-level flow `mov2d_G H r t`
  on `OscSpace d r` agrees with `T` through `movlin_T_seq` (`ofFun 0 (T t v) = G 0 t (ofFun 0 v)`), `mov2d_G_compat`
  (commutation with the embeddings `mov2d_j`), `movlin_memOsc_of_lev` and the injectivity `movlin_j_inj`.  The mass functional
  `x ↦ ⟨√ρ₀, j₀ x⟩` is invariant under `G` (`mov2d_ell_inv`).
* Hence the mild equation is stated WITHOUT the singular `T(t-u)`-integral in `Σ^m`: it is stated at the level `Σ^{m-a}`, where
  `u ↦ G(m-a)(t-u) B(v_u,v_u)` is a continuous integrand (strong continuity `mov2d_G_cont`), and the smoothing `Σ^{m-a} → Σ^m`
  is used only for the bound and for the membership `v_t ∈ Σ^m`.  (Equivalent to the Bochner integral in `Σ^m`: the
  embedding `j` is injective and commutes with the integral.)

Plan (files, all new, no existing file touched):

* `Mov63DAux1` (this file): abstract Banach-space theory, independent of the oscillator scale.  Data: a strongly continuous
  `U : ℝ → X →L X` with `‖U t‖ ≤ C_U e^{-ct}`, a strongly continuous (on `t > 0`) smoothing kernel `S : ℝ → Y →L X` with
  `‖S τ‖ ≤ C_S (1 + τ^{θ-1}) e^{-cτ}`, a bounded bilinear `B : X → X → Y`.  Beta integral `∫_0^∞ (1+u^{θ-1}) e^{-κu} du`;
  convolution bound; contraction on the closed ball of radius `R = 2C_U‖x₀‖` of `ℝ≥0 →ᵇ X` for `w_t = e^{c₀t} v_t`
  (`c₀ = c/2`); `mnd_abstract_exists`: for `‖x₀‖ ≤ ε` there is a continuous `v` with `‖v_t‖ ≤ 2C_U‖x₀‖ e^{-ct/2}` and
  `v_t = U(t)x₀ + ∫_0^t S(t-u) B(v_u,v_u) du`.
* `Mov63DAux2`: the concrete spaces `Z_r = {x ∈ Σ^r : ⟨√ρ₀, x⟩ = 0}` (closed subspaces), the restricted `U`, `S`, `B`
  (`mnd_Uop`, `mnd_Sop`, `mnd_Bop`), the bridge from `MovSmoothingBounds` to scale-level bounds (`mnd_G_decay`, `mnd_smooth`).
* `Mov63DAux3`: the tie: `mov63_mild_existence` (statement below) and the consumer API.

Final statement (consumed by N6 mild ⇒ weak, N7 positivity, N8 decay, N9 assembly), see `Mov63DAux3`:
for `H : Mov2dTh d s β q ρ` there is `c > 0` such that for every real `m > d/2 + 3` there are `ε, C > 0` such that for every
`x₀ ∈ Σ^m`, `⟨√ρ₀, x₀⟩ = 0`, `‖x₀‖ ≤ ε` there is a continuous `v : ℝ → Σ^m` (continuous on `[0,∞)`) with `v 0 = x₀`,
`⟨√ρ₀, v_t⟩ = 0`, `‖v_t‖ ≤ C ‖x₀‖ e^{-ct/2}` (LINEAR amplitude) and, for all `t ≥ 0`,
`j v_t = G_{m-a}(t) j x₀ + ∫_0^t G_{m-a}(t-u) B_ext(v_u, v_u) du` in `Σ^{m-a}` (integrand integrable).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators BoundedContinuousFunction

namespace HRS.MS.Mov63

open HRS.MS.MovLin

section Beta

/-- The Beta-type integral `∫_0^∞ (1 + τ^{θ-1}) e^{-κτ} dτ` (finite for `θ, κ > 0`). -/
def mndBeta (θ κ : ℝ) : ℝ := ∫ τ in Ioi (0 : ℝ), (1 + τ ^ (θ - 1)) * Real.exp (-(κ * τ))

lemma mnd_rpow_exp_int {θ κ : ℝ} (hθ : 0 < θ) (hκ : 0 < κ) :
    IntegrableOn (fun τ : ℝ => τ ^ (θ - 1) * Real.exp (-(κ * τ))) (Ioi 0) := by
  have key := Real.integral_rpow_mul_exp_neg_mul_Ioi hθ hκ
  refine MeasureTheory.Integrable.of_integral_ne_zero ?_
  rw [key]
  have := Real.Gamma_pos_of_pos hθ
  positivity

lemma mnd_beta_int {θ κ : ℝ} (hθ : 0 < θ) (hκ : 0 < κ) :
    IntegrableOn (fun τ : ℝ => (1 + τ ^ (θ - 1)) * Real.exp (-(κ * τ))) (Ioi 0) := by
  have h1 : IntegrableOn (fun τ : ℝ => Real.exp (-κ * τ)) (Ioi 0) := exp_neg_integrableOn_Ioi 0 hκ
  have h2 := mnd_rpow_exp_int hθ hκ
  refine (h1.add h2).congr_fun (fun τ _ => ?_) measurableSet_Ioi
  simp only [Pi.add_apply]
  rw [add_mul, one_mul, neg_mul]

lemma mnd_beta_nonneg (θ κ : ℝ) : 0 ≤ mndBeta θ κ := by
  unfold mndBeta
  refine setIntegral_nonneg measurableSet_Ioi (fun τ hτ => ?_)
  have := Real.rpow_nonneg (le_of_lt (show (0 : ℝ) < τ from hτ)) (θ - 1)
  positivity

/-- `∫_0^t (1 + τ^{θ-1}) e^{-κτ} dτ ≤ mndBeta θ κ`. -/
lemma mnd_beta_le {θ κ : ℝ} (hθ : 0 < θ) (hκ : 0 < κ) {t : ℝ} (ht : 0 ≤ t) :
    ∫ τ in (0 : ℝ)..t, (1 + τ ^ (θ - 1)) * Real.exp (-(κ * τ)) ≤ mndBeta θ κ := by
  rw [intervalIntegral.integral_of_le ht]
  unfold mndBeta
  refine setIntegral_mono_set (mnd_beta_int hθ hκ) ?_ Ioc_subset_Ioi_self.eventuallySubset
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with τ hτ
  have := Real.rpow_nonneg (le_of_lt (show (0 : ℝ) < τ from hτ)) (θ - 1)
  positivity

lemma mnd_beta_intervalIntegrable {θ κ : ℝ} (hθ : 0 < θ) (hκ : 0 < κ) {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable (fun τ : ℝ => (1 + τ ^ (θ - 1)) * Real.exp (-(κ * τ))) volume 0 t := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht]
  exact (mnd_beta_int hθ hκ).mono_set Ioc_subset_Ioi_self

end Beta

section Abstract

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Hypotheses on the linear data: a strongly continuous exponentially decaying family `U` on `X`, and a weakly singular
strongly continuous smoothing family `S : Y → X` (`τ > 0`). -/
structure MndKer (U : ℝ → X →L[ℝ] X) (S : ℝ → Y →L[ℝ] X) (c CU CS θ : ℝ) : Prop where
  CU_nonneg : 0 ≤ CU
  CS_nonneg : 0 ≤ CS
  c_pos : 0 < c
  θ_pos : 0 < θ
  θ_le : θ ≤ 1
  U_zero : ∀ x, U 0 x = x
  U_cont : ∀ x, ContinuousOn (fun t => U t x) (Ici 0)
  U_bound : ∀ t, 0 ≤ t → ‖U t‖ ≤ CU * Real.exp (-c * t)
  S_cont : ∀ y, ContinuousOn (fun τ => S τ y) (Ioi 0)
  S_bound : ∀ τ, 0 < τ → ‖S τ‖ ≤ CS * (1 + τ ^ (θ - 1)) * Real.exp (-c * τ)

/-- The weighted kernel `e^{c₀τ} S(τ)`. -/
def mndK (c₀ : ℝ) (S : ℝ → Y →L[ℝ] X) (τ : ℝ) : Y →L[ℝ] X := Real.exp (c₀ * τ) • S τ

variable {U : ℝ → X →L[ℝ] X} {S : ℝ → Y →L[ℝ] X} {c CU CS θ : ℝ}

lemma mnd_K_bound (hK : MndKer U S c CU CS θ) {c₀ : ℝ} (hc₀ : c₀ ≤ c) {τ : ℝ} (hτ : 0 < τ) :
    ‖mndK c₀ S τ‖ ≤ CS * (1 + τ ^ (θ - 1)) * Real.exp (-((c - c₀) * τ)) := by
  unfold mndK
  rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  calc Real.exp (c₀ * τ) * ‖S τ‖ ≤ Real.exp (c₀ * τ) * (CS * (1 + τ ^ (θ - 1)) * Real.exp (-c * τ)) :=
        mul_le_mul_of_nonneg_left (hK.S_bound τ hτ) (Real.exp_pos _).le
    _ = CS * (1 + τ ^ (θ - 1)) * (Real.exp (c₀ * τ) * Real.exp (-c * τ)) := by ring
    _ = CS * (1 + τ ^ (θ - 1)) * Real.exp (-((c - c₀) * τ)) := by
        rw [← Real.exp_add]; congr 2; ring

lemma mnd_K_ker (hK : MndKer U S c CU CS θ) {c₀ : ℝ} (hc₀ : c₀ ≤ c) {T0 : ℝ} (hT0 : 0 < T0) :
    Mov2cKer (mndK c₀ S) T0 (CS * (T0 ^ (1 - θ) + 1)) θ := by
  refine ⟨mul_nonneg hK.CS_nonneg (by positivity), fun y => ?_, fun τ hτ => ?_⟩
  · have h1 : ContinuousOn (fun τ => Real.exp (c₀ * τ)) (Ioc 0 T0) := by fun_prop
    have h2 : ContinuousOn (fun τ => S τ y) (Ioc 0 T0) := (hK.S_cont y).mono (fun τ hτ => hτ.1)
    exact h1.smul h2
  · have hτ0 : 0 < τ := hτ.1
    refine (mnd_K_bound hK hc₀ hτ0).trans ?_
    have hexp : Real.exp (-((c - c₀) * τ)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ (c - c₀) * τ := mul_nonneg (by linarith) hτ0.le
      linarith
    have hp : 1 + τ ^ (θ - 1) ≤ (T0 ^ (1 - θ) + 1) * τ ^ (θ - 1) := by
      have h3 : 1 ≤ T0 ^ (1 - θ) * τ ^ (θ - 1) := by
        have hle : τ ^ (θ - 1) ≥ T0 ^ (θ - 1) :=
          Real.rpow_le_rpow_of_nonpos hτ0 hτ.2 (by linarith [hK.θ_le])
        have : T0 ^ (1 - θ) * T0 ^ (θ - 1) = 1 := by
          rw [← Real.rpow_add hT0]; simp
        calc (1 : ℝ) = T0 ^ (1 - θ) * T0 ^ (θ - 1) := this.symm
          _ ≤ T0 ^ (1 - θ) * τ ^ (θ - 1) :=
            mul_le_mul_of_nonneg_left hle (Real.rpow_nonneg hT0.le _)
      nlinarith
    have hCS := hK.CS_nonneg
    calc CS * (1 + τ ^ (θ - 1)) * Real.exp (-((c - c₀) * τ)) ≤ CS * (1 + τ ^ (θ - 1)) * 1 :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
      _ ≤ CS * ((T0 ^ (1 - θ) + 1) * τ ^ (θ - 1)) := by
          rw [mul_one]; exact mul_le_mul_of_nonneg_left hp hCS
      _ = CS * (T0 ^ (1 - θ) + 1) * τ ^ (θ - 1) := by ring

end Abstract

section Conv

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {U : ℝ → X →L[ℝ] X} {S : ℝ → Y →L[ℝ] X} {c CU CS θ : ℝ}

/-- The weakly singular Duhamel integral `∫_0^t e^{c₀(t-u)} S(t-u) y(u) du`. -/
def mndConv (c₀ : ℝ) (S : ℝ → Y →L[ℝ] X) (y : ℝ → Y) (t : ℝ) : X :=
  ∫ u in (0 : ℝ)..t, mndK c₀ S (t - u) (y u)

lemma mnd_conv_int (hK : MndKer U S c CU CS θ) {c₀ : ℝ} (hc₀ : c₀ ≤ c) {y : ℝ → Y} (hy : Continuous y)
    {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable (fun u => mndK c₀ S (t - u) (y u)) volume 0 t :=
  mov2c_vol_int (mnd_K_ker hK hc₀ (T0 := t + 1) (by linarith)) hK.θ_pos hK.θ_le hy.continuousOn
    ⟨ht, by linarith⟩

lemma mnd_conv_cont (hK : MndKer U S c CU CS θ) {c₀ : ℝ} (hc₀ : c₀ ≤ c) {y : ℝ → Y} (hy : Continuous y) :
    ContinuousOn (mndConv c₀ S y) (Ici 0) := by
  intro t0 ht0
  have ht0' : (0 : ℝ) ≤ t0 := ht0
  have hc := mov2c_vol_cont (mnd_K_ker hK hc₀ (T0 := t0 + 1) (by linarith)) hK.θ_pos hK.θ_le (by linarith)
    hy.continuousOn
  have hI : Icc (0 : ℝ) (t0 + 1) ∈ 𝓝[Ici (0 : ℝ)] t0 :=
    mem_nhdsWithin.2 ⟨Iio (t0 + 1), isOpen_Iio, lt_add_one t0, fun u hu => ⟨hu.2, hu.1.le⟩⟩
  exact (hc t0 ⟨ht0', by linarith⟩).mono_of_mem_nhdsWithin hI

lemma mnd_conv_norm_le (hK : MndKer U S c CU CS θ) {c₀ : ℝ} (hc₀ : c₀ < c) {y : ℝ → Y} (hy : Continuous y)
    {N : ℝ} (hN : ∀ u, 0 ≤ u → ‖y u‖ ≤ N) {t : ℝ} (ht : 0 ≤ t) :
    ‖mndConv c₀ S y t‖ ≤ CS * N * mndBeta θ (c - c₀) := by
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hN 0 le_rfl)
  have hκ : 0 < c - c₀ := by linarith
  set F : ℝ → ℝ := fun τ => (1 + τ ^ (θ - 1)) * Real.exp (-((c - c₀) * τ)) with hF
  have hFi : IntervalIntegrable F volume 0 t := mnd_beta_intervalIntegrable hK.θ_pos hκ ht
  have hint : IntervalIntegrable (fun u => CS * N * F (t - u)) volume 0 t := by
    have := (hFi.comp_sub_left t)
    simp only [sub_zero, sub_self] at this
    exact (this.symm).const_mul (CS * N)
  unfold mndConv
  calc ‖∫ u in (0 : ℝ)..t, mndK c₀ S (t - u) (y u)‖ ≤ ∫ u in (0 : ℝ)..t, CS * N * F (t - u) := by
        refine intervalIntegral.norm_integral_le_of_norm_le ht ?_ hint
        have hae : ∀ᵐ u ∂(volume : Measure ℝ), u ∉ ({t} : Set ℝ) :=
          (Set.finite_singleton t).countable.ae_notMem _
        refine hae.mono (fun u hu hu' => ?_)
        have hne : u ≠ t := hu
        have hut : u < t := lt_of_le_of_ne hu'.2 hne
        have hτ : 0 < t - u := by linarith
        calc ‖mndK c₀ S (t - u) (y u)‖ ≤ ‖mndK c₀ S (t - u)‖ * ‖y u‖ := (mndK c₀ S (t - u)).le_opNorm _
          _ ≤ (CS * F (t - u)) * N := by
              refine mul_le_mul ?_ (hN u hu'.1.le) (norm_nonneg _) (by
                have := hK.CS_nonneg
                have h2 := Real.rpow_nonneg hτ.le (θ - 1)
                simp only [hF]
                positivity)
              have := mnd_K_bound hK hc₀.le hτ
              simp only [hF]
              rw [← mul_assoc]
              exact this
          _ = CS * N * F (t - u) := by ring
    _ = CS * N * ∫ τ in (0 : ℝ)..t, F τ := by
        rw [intervalIntegral.integral_const_mul]
        congr 1
        have := intervalIntegral.integral_comp_sub_left (a := 0) (b := t) F t
        simpa using this
    _ ≤ CS * N * mndBeta θ (c - c₀) := by
        refine mul_le_mul_of_nonneg_left (mnd_beta_le hK.θ_pos hκ ht) (mul_nonneg hK.CS_nonneg hN0)

end Conv

section Fixed

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The standing hypotheses of the fixed-point scheme: linear data and a bounded bilinear `B`. -/
structure MndSetup (U : ℝ → X →L[ℝ] X) (S : ℝ → Y →L[ℝ] X) (B : X →L[ℝ] X →L[ℝ] Y) (c CU CS θ Kb : ℝ) : Prop where
  ker : MndKer U S c CU CS θ
  Kb_nonneg : 0 ≤ Kb
  Bbound : ∀ x x' : X, ‖B x x'‖ ≤ Kb * ‖x‖ * ‖x'‖

variable {U : ℝ → X →L[ℝ] X} {S : ℝ → Y →L[ℝ] X} {B : X →L[ℝ] X →L[ℝ] Y} {c CU CS θ Kb : ℝ}

/-- Extension of `w : ℝ≥0 →ᵇ X` to `ℝ` (constant for negative times). -/
def mndW (w : ℝ≥0 →ᵇ X) (u : ℝ) : X := w u.toNNReal

lemma mndW_cont (w : ℝ≥0 →ᵇ X) : Continuous (mndW w) := w.continuous.comp continuous_real_toNNReal

lemma mndW_norm_le (w : ℝ≥0 →ᵇ X) (u : ℝ) : ‖mndW w u‖ ≤ ‖w‖ := w.norm_coe_le_norm _

lemma mndW_sub (w w' : ℝ≥0 →ᵇ X) (u : ℝ) : mndW w u - mndW w' u = mndW (w - w') u := rfl

/-- The nonlinearity, in the weighted variable `w_t = e^{c₀t} v_t`: `y(u) = e^{-c₀u} B(w_u, w_u)`. -/
def mndN (B : X →L[ℝ] X →L[ℝ] Y) (c₀ : ℝ) (w : ℝ≥0 →ᵇ X) (u : ℝ) : Y :=
  Real.exp (-c₀ * u) • B (mndW w u) (mndW w u)

lemma mndN_cont (B : X →L[ℝ] X →L[ℝ] Y) (c₀ : ℝ) (w : ℝ≥0 →ᵇ X) : Continuous (mndN B c₀ w) := by
  unfold mndN
  have h1 : Continuous fun u : ℝ => Real.exp (-c₀ * u) := by fun_prop
  have h2 : Continuous fun u => B (mndW w u) (mndW w u) :=
    (B.continuous.comp (mndW_cont w)).clm_apply (mndW_cont w)
  exact h1.smul h2

lemma mndN_bound (hS : MndSetup U S B c CU CS θ Kb) {c₀ : ℝ} (hc₀ : 0 ≤ c₀) (w : ℝ≥0 →ᵇ X) {u : ℝ} (hu : 0 ≤ u) :
    ‖mndN B c₀ w u‖ ≤ Kb * ‖w‖ ^ 2 := by
  unfold mndN
  rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  have h1 : Real.exp (-c₀ * u) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  have h2 : ‖B (mndW w u) (mndW w u)‖ ≤ Kb * ‖w‖ ^ 2 := by
    refine (hS.Bbound _ _).trans ?_
    have hw := mndW_norm_le w u
    have h0 := norm_nonneg (mndW w u)
    have hK0 := hS.Kb_nonneg
    calc Kb * ‖mndW w u‖ * ‖mndW w u‖ ≤ Kb * ‖w‖ * ‖w‖ :=
          mul_le_mul (mul_le_mul_of_nonneg_left hw hK0) hw h0 (by positivity)
      _ = Kb * ‖w‖ ^ 2 := by ring
  calc Real.exp (-c₀ * u) * ‖B (mndW w u) (mndW w u)‖ ≤ 1 * (Kb * ‖w‖ ^ 2) :=
        mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = Kb * ‖w‖ ^ 2 := one_mul _

lemma mndN_sub_bound (hS : MndSetup U S B c CU CS θ Kb) {c₀ : ℝ} (hc₀ : 0 ≤ c₀) (w w' : ℝ≥0 →ᵇ X) {u : ℝ}
    (hu : 0 ≤ u) : ‖mndN B c₀ w u - mndN B c₀ w' u‖ ≤ Kb * (‖w‖ + ‖w'‖) * ‖w - w'‖ := by
  unfold mndN
  rw [← smul_sub, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  have h1 : Real.exp (-c₀ * u) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith
  set a := mndW w u
  set b := mndW w' u
  have hab : B a a - B b b = B (a - b) a + B b (a - b) := by
    rw [map_sub, sub_apply, map_sub]; abel
  have hd : ‖a - b‖ ≤ ‖w - w'‖ := by
    rw [mndW_sub]; exact mndW_norm_le _ _
  have ha : ‖a‖ ≤ ‖w‖ := mndW_norm_le w u
  have hb : ‖b‖ ≤ ‖w'‖ := mndW_norm_le w' u
  have h2 : ‖B a a - B b b‖ ≤ Kb * (‖w‖ + ‖w'‖) * ‖w - w'‖ := by
    rw [hab]
    refine (norm_add_le _ _).trans ?_
    have e1 := hS.Bbound (a - b) a
    have e2 := hS.Bbound b (a - b)
    have hK0 := hS.Kb_nonneg
    have n1 := norm_nonneg a
    have n2 := norm_nonneg b
    have n3 := norm_nonneg (a - b)
    have p1 : Kb * ‖a - b‖ * ‖a‖ ≤ Kb * ‖w - w'‖ * ‖w‖ :=
      mul_le_mul (mul_le_mul_of_nonneg_left hd hK0) ha n1 (by positivity)
    have p2 : Kb * ‖b‖ * ‖a - b‖ ≤ Kb * ‖w'‖ * ‖w - w'‖ :=
      mul_le_mul (mul_le_mul_of_nonneg_left hb hK0) hd n3 (by positivity)
    nlinarith
  calc Real.exp (-c₀ * u) * ‖B a a - B b b‖ ≤ 1 * (Kb * (‖w‖ + ‖w'‖) * ‖w - w'‖) :=
        mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = _ := one_mul _

lemma mnd_conv_sub (hK : MndKer U S c CU CS θ) {c₀ : ℝ} (hc₀ : c₀ ≤ c) {y y' : ℝ → Y} (hy : Continuous y)
    (hy' : Continuous y') {t : ℝ} (ht : 0 ≤ t) :
    mndConv c₀ S y t - mndConv c₀ S y' t = mndConv c₀ S (fun u => y u - y' u) t := by
  unfold mndConv
  rw [← intervalIntegral.integral_sub (mnd_conv_int hK hc₀ hy ht) (mnd_conv_int hK hc₀ hy' ht)]
  simp only [map_sub]

/-- The Duhamel map on `ℝ≥0 →ᵇ X`: `w ↦ e^{c₀t} U(t) x₀ + ∫_0^t e^{c₀(t-u)} S(t-u) e^{-c₀u} B(w_u, w_u) du`, `c₀ = c/2`. -/
def mndPsiFun (U : ℝ → X →L[ℝ] X) (S : ℝ → Y →L[ℝ] X) (B : X →L[ℝ] X →L[ℝ] Y) (c : ℝ) (x0 : X)
    (w : ℝ≥0 →ᵇ X) (t : ℝ≥0) : X :=
  Real.exp (c / 2 * (t : ℝ)) • U (t : ℝ) x0 + mndConv (c / 2) S (mndN B (c / 2) w) (t : ℝ)

lemma mndPsiFun_cont (hS : MndSetup U S B c CU CS θ Kb) (x0 : X) (w : ℝ≥0 →ᵇ X) :
    Continuous (mndPsiFun U S B c x0 w) := by
  have hc := hS.ker.c_pos
  have h1 : ContinuousOn (fun t : ℝ => Real.exp (c / 2 * t) • U t x0) (Ici 0) :=
    (by fun_prop : Continuous fun t : ℝ => Real.exp (c / 2 * t)).continuousOn.smul (hS.ker.U_cont x0)
  have h2 := mnd_conv_cont hS.ker (c₀ := c / 2) (by linarith) (mndN_cont B (c / 2) w)
  have h3 := h1.add h2
  exact h3.comp_continuous NNReal.continuous_coe (fun t => t.2)

lemma mndPsiFun_bound (hS : MndSetup U S B c CU CS θ Kb) (x0 : X) (w : ℝ≥0 →ᵇ X) (t : ℝ≥0) :
    ‖mndPsiFun U S B c x0 w t‖ ≤ CU * ‖x0‖ + CS * (Kb * ‖w‖ ^ 2) * mndBeta θ (c - c / 2) := by
  have hc := hS.ker.c_pos
  have ht : (0 : ℝ) ≤ t := t.2
  unfold mndPsiFun
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
    have h1 := (U (t : ℝ)).le_opNorm x0
    have h2 := hS.ker.U_bound t ht
    have h3 : Real.exp (c / 2 * t) * Real.exp (-c * t) ≤ 1 := by
      rw [← Real.exp_add, Real.exp_le_one_iff]; nlinarith
    calc Real.exp (c / 2 * t) * ‖U t x0‖ ≤ Real.exp (c / 2 * t) * (CU * Real.exp (-c * t) * ‖x0‖) :=
          mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))) (Real.exp_pos _).le
      _ = CU * ‖x0‖ * (Real.exp (c / 2 * t) * Real.exp (-c * t)) := by ring
      _ ≤ CU * ‖x0‖ * 1 := mul_le_mul_of_nonneg_left h3 (mul_nonneg hS.ker.CU_nonneg (norm_nonneg _))
      _ = CU * ‖x0‖ := mul_one _
  · exact mnd_conv_norm_le hS.ker (c₀ := c / 2) (by linarith) (mndN_cont B (c / 2) w)
      (fun u hu => mndN_bound hS (by linarith) w hu) ht

/-- The Duhamel map as a self-map of `ℝ≥0 →ᵇ X`. -/
def mndPsi (hS : MndSetup U S B c CU CS θ Kb) (x0 : X) (w : ℝ≥0 →ᵇ X) : ℝ≥0 →ᵇ X :=
  BoundedContinuousFunction.ofNormedAddCommGroup (mndPsiFun U S B c x0 w) (mndPsiFun_cont hS x0 w)
    _ (mndPsiFun_bound hS x0 w)

lemma mndPsi_apply (hS : MndSetup U S B c CU CS θ Kb) (x0 : X) (w : ℝ≥0 →ᵇ X) (t : ℝ≥0) :
    mndPsi hS x0 w t = mndPsiFun U S B c x0 w t := rfl

lemma mndPsi_norm_le (hS : MndSetup U S B c CU CS θ Kb) (x0 : X) (w : ℝ≥0 →ᵇ X) :
    ‖mndPsi hS x0 w‖ ≤ CU * ‖x0‖ + CS * (Kb * ‖w‖ ^ 2) * mndBeta θ (c - c / 2) := by
  have hc := hS.ker.c_pos
  have h0 : 0 ≤ CU * ‖x0‖ + CS * (Kb * ‖w‖ ^ 2) * mndBeta θ (c - c / 2) := by
    have := mnd_beta_nonneg θ (c - c / 2)
    have := hS.ker.CU_nonneg
    have := hS.ker.CS_nonneg
    have := hS.Kb_nonneg
    positivity
  exact (BoundedContinuousFunction.norm_le h0).2 (fun t => mndPsiFun_bound hS x0 w t)

lemma mndPsi_dist_le (hS : MndSetup U S B c CU CS θ Kb) (x0 : X) (w w' : ℝ≥0 →ᵇ X) :
    dist (mndPsi hS x0 w) (mndPsi hS x0 w') ≤
      CS * Kb * mndBeta θ (c - c / 2) * (‖w‖ + ‖w'‖) * dist w w' := by
  have hc := hS.ker.c_pos
  have h0 : 0 ≤ CS * Kb * mndBeta θ (c - c / 2) * (‖w‖ + ‖w'‖) * dist w w' := by
    have := mnd_beta_nonneg θ (c - c / 2)
    have := hS.ker.CS_nonneg
    have := hS.Kb_nonneg
    positivity
  refine (BoundedContinuousFunction.dist_le h0).2 (fun t => ?_)
  have ht : (0 : ℝ) ≤ t := t.2
  rw [dist_eq_norm, mndPsi_apply, mndPsi_apply]
  unfold mndPsiFun
  rw [add_sub_add_left_eq_sub, mnd_conv_sub hS.ker (c₀ := c / 2) (by linarith) (mndN_cont B (c / 2) w)
    (mndN_cont B (c / 2) w') ht]
  have hcont : Continuous fun u => mndN B (c / 2) w u - mndN B (c / 2) w' u :=
    (mndN_cont B (c / 2) w).sub (mndN_cont B (c / 2) w')
  have := mnd_conv_norm_le hS.ker (c₀ := c / 2) (by linarith) hcont
    (N := Kb * (‖w‖ + ‖w'‖) * ‖w - w'‖)
    (fun u hu => mndN_sub_bound hS (by linarith) w w' hu) ht
  rw [dist_eq_norm]
  calc _ ≤ CS * (Kb * (‖w‖ + ‖w'‖) * ‖w - w'‖) * mndBeta θ (c - c / 2) := this
    _ = _ := by ring

end Fixed

section Exist

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {U : ℝ → X →L[ℝ] X} {S : ℝ → Y →L[ℝ] X} {B : X →L[ℝ] X →L[ℝ] Y} {c CU CS θ Kb : ℝ}

/-- Banach fixed point of the Duhamel map in the closed ball of radius `R`, unique in that ball. -/
lemma mnd_exists_fixed (hS : MndSetup U S B c CU CS θ Kb) (x0 : X) {R : ℝ} (hR : R = 2 * CU * ‖x0‖)
    (hsmall : CS * Kb * mndBeta θ (c - c / 2) * R ≤ 1 / 4) :
    ∃ w : ℝ≥0 →ᵇ X, ‖w‖ ≤ R ∧ mndPsi hS x0 w = w ∧
      ∀ w' : ℝ≥0 →ᵇ X, ‖w'‖ ≤ R → mndPsi hS x0 w' = w' → w' = w := by
  set KI : ℝ := CS * Kb * mndBeta θ (c - c / 2) with hKI
  have hKI0 : 0 ≤ KI := by
    have := mnd_beta_nonneg θ (c - c / 2)
    have := hS.ker.CS_nonneg
    have := hS.Kb_nonneg
    positivity
  have hCU := hS.ker.CU_nonneg
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  have hmaps : ∀ w : ℝ≥0 →ᵇ X, ‖w‖ ≤ R → ‖mndPsi hS x0 w‖ ≤ R := by
    intro w hw
    refine (mndPsi_norm_le hS x0 w).trans ?_
    have h1 : CS * (Kb * ‖w‖ ^ 2) * mndBeta θ (c - c / 2) = KI * ‖w‖ ^ 2 := by rw [hKI]; ring
    have h2 : ‖w‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hw 2
    have h3 : KI * ‖w‖ ^ 2 ≤ KI * R ^ 2 := mul_le_mul_of_nonneg_left h2 hKI0
    have h4 : KI * R ^ 2 = (KI * R) * R := by ring
    have h5 : (KI * R) * R ≤ 1 / 4 * R := mul_le_mul_of_nonneg_right hsmall hR0
    have h6 : CU * ‖x0‖ = R / 2 := by rw [hR]; ring
    rw [h1, h6]
    nlinarith
  let Bl : Set (ℝ≥0 →ᵇ X) := Metric.closedBall 0 R
  haveI : CompleteSpace Bl := (Metric.isClosed_closedBall).completeSpace_coe
  haveI : Nonempty Bl := ⟨⟨0, by simpa [Bl] using hR0⟩⟩
  let f : Bl → Bl := fun w => ⟨mndPsi hS x0 w.1, mem_closedBall_zero_iff.2
    (hmaps w.1 (mem_closedBall_zero_iff.1 w.2))⟩
  have hf : ContractingWith (1 / 2 : ℝ≥0) f := by
    refine ⟨by norm_num, LipschitzWith.of_dist_le_mul (fun w w' => ?_)⟩
    have hw : ‖w.1‖ ≤ R := mem_closedBall_zero_iff.1 w.2
    have hw' : ‖w'.1‖ ≤ R := mem_closedBall_zero_iff.1 w'.2
    have hd := mndPsi_dist_le hS x0 w.1 w'.1
    have hd0 := dist_nonneg (x := w.1) (y := w'.1)
    have : KI * (‖w.1‖ + ‖w'.1‖) ≤ 1 / 2 := by nlinarith
    show dist (mndPsi hS x0 w.1) (mndPsi hS x0 w'.1) ≤ ((1 / 2 : ℝ≥0) : ℝ) * dist w.1 w'.1
    have e : ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 := by norm_num
    rw [e]
    calc _ ≤ KI * (‖w.1‖ + ‖w'.1‖) * dist w.1 w'.1 := by
          exact hd.trans (le_of_eq (by rw [hKI]))
      _ ≤ 1 / 2 * dist w.1 w'.1 := mul_le_mul_of_nonneg_right this hd0
  refine ⟨(ContractingWith.fixedPoint f hf).1, mem_closedBall_zero_iff.1 (ContractingWith.fixedPoint f hf).2, ?_, ?_⟩
  · have := ContractingWith.fixedPoint_isFixedPt (f := f) hf
    exact congrArg Subtype.val this
  · intro w' hw' hfix
    have hmem : w' ∈ Bl := mem_closedBall_zero_iff.2 hw'
    have := ContractingWith.fixedPoint_unique (f := f) hf (x := ⟨w', hmem⟩) (Subtype.ext hfix)
    exact congrArg Subtype.val this

/-- The unweighted perturbation `v_t = e^{-c t / 2} w_t`. -/
def mndV (c : ℝ) (w : ℝ≥0 →ᵇ X) (t : ℝ) : X := Real.exp (-(c / 2) * t) • mndW w t

lemma mndV_cont (c : ℝ) (w : ℝ≥0 →ᵇ X) : Continuous (mndV c w) := by
  unfold mndV
  exact (by fun_prop : Continuous fun t : ℝ => Real.exp (-(c / 2) * t)).smul (mndW_cont w)

lemma mndV_norm_le (c : ℝ) (w : ℝ≥0 →ᵇ X) (t : ℝ) : ‖mndV c w t‖ ≤ ‖w‖ * Real.exp (-(c / 2) * t) := by
  unfold mndV
  rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le, mul_comm]
  exact mul_le_mul_of_nonneg_right (mndW_norm_le w t) (Real.exp_pos _).le

/-- The mild equation for a fixed point of the Duhamel map. -/
lemma mnd_mild_of_fixed (hS : MndSetup U S B c CU CS θ Kb) (x0 : X) (w : ℝ≥0 →ᵇ X)
    (hw : mndPsi hS x0 w = w) {t : ℝ} (ht : 0 ≤ t) :
    IntervalIntegrable (fun u => S (t - u) (B (mndV c w u) (mndV c w u))) volume 0 t ∧
      mndV c w t = U t x0 + ∫ u in (0 : ℝ)..t, S (t - u) (B (mndV c w u) (mndV c w u)) := by
  have hc := hS.ker.c_pos
  have hwt : mndW w t = Real.exp (c / 2 * t) • U t x0 + mndConv (c / 2) S (mndN B (c / 2) w) t := by
    have := congrArg (fun f : ℝ≥0 →ᵇ X => f t.toNNReal) hw
    simp only [mndPsi_apply, mndPsiFun] at this
    rw [Real.coe_toNNReal t ht] at this
    exact this.symm
  have hpt : ∀ u : ℝ, Real.exp (-(c / 2) * t) • (mndK (c / 2) S (t - u)) (mndN B (c / 2) w u) =
      S (t - u) (B (mndV c w u) (mndV c w u)) := by
    intro u
    simp only [mndK, mndN, mndV, smul_apply, map_smul, smul_smul]
    congr 1
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hint : IntervalIntegrable (fun u => S (t - u) (B (mndV c w u) (mndV c w u))) volume 0 t := by
    have h0 := (mnd_conv_int hS.ker (c₀ := c / 2) (by linarith) (mndN_cont B (c / 2) w) ht).smul
      (Real.exp (-(c / 2) * t))
    have e : (fun u => S (t - u) (B (mndV c w u) (mndV c w u))) =
        fun u => Real.exp (-(c / 2) * t) • (mndK (c / 2) S (t - u)) (mndN B (c / 2) w u) :=
      funext fun u => (hpt u).symm
    rw [e]; exact h0
  refine ⟨hint, ?_⟩
  have hI : ∫ u in (0 : ℝ)..t, S (t - u) (B (mndV c w u) (mndV c w u)) =
      Real.exp (-(c / 2) * t) • mndConv (c / 2) S (mndN B (c / 2) w) t := by
    unfold mndConv
    rw [← intervalIntegral.integral_smul]
    exact intervalIntegral.integral_congr (fun u _ => (hpt u).symm)
  rw [hI]
  unfold mndV
  rw [hwt, smul_add, smul_smul, ← Real.exp_add]
  have : -(c / 2) * t + c / 2 * t = 0 := by ring
  rw [this, Real.exp_zero, one_smul]

/-- **Abstract existence of the mild solution** (contraction): for `‖x₀‖ ≤ ε` there is a continuous `v` with the LINEAR bound
`‖v_t‖ ≤ 2 C_U ‖x₀‖ e^{-ct/2}`, `v_0 = x₀` and `v_t = U(t) x₀ + ∫_0^t S(t-u) B(v_u,v_u) du` (integrand integrable). -/
theorem mnd_abstract_exists (hS : MndSetup U S B c CU CS θ Kb) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x0 : X, ‖x0‖ ≤ ε →
      ∃ v : ℝ → X, ContinuousOn v (Ici 0) ∧ v 0 = x0 ∧
        (∀ t : ℝ, 0 ≤ t → ‖v t‖ ≤ 2 * CU * ‖x0‖ * Real.exp (-(c / 2) * t)) ∧
        ∀ t : ℝ, 0 ≤ t →
          IntervalIntegrable (fun u => S (t - u) (B (v u) (v u))) volume 0 t ∧
            v t = U t x0 + ∫ u in (0 : ℝ)..t, S (t - u) (B (v u) (v u)) := by
  set P : ℝ := CS * Kb * mndBeta θ (c - c / 2) * CU with hP
  have hP0 : 0 ≤ P := by
    have := mnd_beta_nonneg θ (c - c / 2)
    have := hS.ker.CS_nonneg
    have := hS.Kb_nonneg
    have := hS.ker.CU_nonneg
    positivity
  have hpos : 0 < 8 * (P + 1) := by positivity
  refine ⟨1 / (8 * (P + 1)), by positivity, fun x0 hx0 => ?_⟩
  have hε : (1 / (8 * (P + 1))) * (8 * (P + 1)) = 1 := by field_simp
  have hε0 : 0 ≤ 1 / (8 * (P + 1)) := by positivity
  have hsmall : CS * Kb * mndBeta θ (c - c / 2) * (2 * CU * ‖x0‖) ≤ 1 / 4 := by
    have e : CS * Kb * mndBeta θ (c - c / 2) * (2 * CU * ‖x0‖) = 2 * P * ‖x0‖ := by rw [hP]; ring
    rw [e]
    have h1 : P * ‖x0‖ ≤ P * (1 / (8 * (P + 1))) := mul_le_mul_of_nonneg_left hx0 hP0
    nlinarith
  obtain ⟨w, hwR, hfix, -⟩ := mnd_exists_fixed hS x0 (R := 2 * CU * ‖x0‖) rfl hsmall
  have hmild := fun t (ht : 0 ≤ t) => mnd_mild_of_fixed hS x0 w hfix ht
  refine ⟨mndV c w, (mndV_cont c w).continuousOn, ?_, fun t ht => ?_, hmild⟩
  · have := (hmild 0 le_rfl).2
    rw [this]
    simp [hS.ker.U_zero]
  · refine (mndV_norm_le c w t).trans ?_
    exact mul_le_mul_of_nonneg_right hwR (Real.exp_pos _).le

end Exist

end HRS.MS.Mov63

end
