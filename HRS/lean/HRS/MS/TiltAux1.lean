import HRS.MS.QprepAux14
import HRS.MS.DerCorAux2
import HRS.MS.UniqFAux4

/-!
# S4.7 `tilt_static`, `tilt_static_osc`, `tilt_static_mean_field`: packet P1 (plan and reference data)

Worker S47.  Namespace `S47` (top level, as `S45`, `S46`; the ties re-export it as `HRS.MS.Tilt.*`), helper prefix `s47_`.  Frozen rows: `HRS/Whole/Thermal.lean`
(`tilt_static` :435, `tilt_static_osc` :453, `tilt_static_mean_field` :470).  TeX: supplement L2705-2745 (corollary)
and its proof L2746-2840.  Full plan: `S47_PLAN.md` (scratch directory), summarised here.

## Verdict on the statements
All three are TRUE and non-vacuous as stated; no statement change and no new hypothesis are needed.
`μ₀ = tiltedMeasure d s a β ε ψ = withDensityReal ρ₀`, `ρ₀ = (1 + εψ) ρ_*` is a smooth positive probability density with
`ρ₀ ≤ (3/2) ρ_*` and uniform Gaussian bounds (`s48_ref_data`).  Junk values: `Kop`/`responseInverse` honest as in S4.5/S4.6
(the response exists by the corrector below), `featureVec`/`law` honest by conjuncts 1, 2 of `StaticFieldConclusion`,
`smoothDist` used through `Real.iSup_le` only, `Real.log 0`/`0^(-s)` only on the collision null set, `firstMarginal` a probability
measure (`d ≥ 2`, `N ≥ 2`); empty parameter intervals make the statements vacuous.  Mean field clause:
`Y_N = X_N + b`, `b = (√N (m⁰_N - μ₀)(φ_j))_j`, `‖b‖ ≤ √N ‖dm⁰_N/dμ₀ - 1‖_{L²(μ₀)} Σ_j ‖φ_j‖_∞ ≤ C S √N δ_N`.

## "The corrector at the perturbed reference"
The frozen statements contain no corrector; the proof needs, for `φ ∈ C_b^J` (`J > d/2 + 2`), a `χ ∈ C²` with
`‖∇χ‖, ‖D²χ‖ ≤ C‖φ‖_{C_b^J}`, `L₀χ ∈ L²(μ₀)` and `(γ₀⁻¹ + K_{μ₀}) L₀χ = P_{μ₀}φ` (`μ₀`-a.e.), `L₀ = -Δ - ∇log ρ₀ · ∇`.
This follows from the merged generic pieces (`s48_ref_data`, `tc5_resolvent_rep` (generic in `TcRef`), `s48_poisson_deriv`
(generic in the drift `-q x + B`), `Gap.gap_invariant`, `Gap.gap_gradient_log`) as in `derivative_corrector_proof` (packet P2).

## Packets (as built; all complete)
* `TiltAux1` (this file): reference class `TRef` (generic `ρ`, `∇ρ = ρ (-q x + Bd)`), regularity of `U₀ = g * μ₀`
  (`U₀ = locK + farK` of the constant `1`: `C^∞` with bounded gradient, uniform), `TRef` for `ρ₀` with uniform constants (`s47_tref`).
* `TiltAux2`: corrector at `ρ₀` (`S47Feat`, `s47_corrector`).  `TiltAux3`: canonical form `Q = canonicalGibbs g V₀ N γ`, static bundle.
  `TiltAux4`: Gibbs integration by parts for `V₀`.  `TiltAux5`-`6`: corrector/covariance/generator identities.
  `TiltAux7`: `R`, `T` bounds.  `TiltAux8`-`10`: Stein identity, vector Stein identity, `hfin` data.  `TiltAux11`: uniform setup, bias.
  `TiltAux12`: feature-form conclusion.  `TiltAux13`: `tilt_static_osc`.  `TiltAux14`: `tilt_static`, `tilt_static_mean_field`.
  `TiltTie`: `type_of%` ties and the re-export `HRS.MS.Tilt.*_proof`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S47

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

/-- The reference data of the S4.7 chain: `ρ` smooth positive probability density with Gaussian bounds, the potential
`U = g * ρ` smooth with bounded gradient, and `∇ρ = ρ (-q x + Bd)` with `Bd` continuous and bounded. -/
structure TRef (d : ℕ) (s : ℝ) (ρ : Euc d → ℝ) (q C c BU BB : ℝ) (Bd : Euc d → Euc d) : Prop where
  prob : IsProbDensity ρ
  smooth : ContDiff ℝ ∞ ρ
  pos : ∀ y : Euc d, 0 < ρ y
  C0 : 0 ≤ C
  hc : 0 < c
  h0 : ∀ y : Euc d, |ρ y| ≤ C * Real.exp (-c * ‖y‖ ^ 2)
  h1 : ∀ y : Euc d, ‖fderiv ℝ ρ y‖ ≤ C * Real.exp (-c * ‖y‖ ^ 2)
  Usmooth : ContDiff ℝ ∞ (convMeasure (rieszKernel d s) (withDensityReal ρ))
  BU0 : 0 ≤ BU
  gradU_le : ∀ y : Euc d, ‖gradient (convMeasure (rieszKernel d s) (withDensityReal ρ)) y‖ ≤ BU
  Bd_cont : Continuous Bd
  BB0 : 0 ≤ BB
  Bd_le : ∀ y : Euc d, ‖Bd y‖ ≤ BB
  grad_rho : ∀ y : Euc d, gradient ρ y = ρ y • (-q • y + Bd y)

/-! ### The potential `g * μ` through the splitting `g = θ g + (1 - θ) g` -/

theorem s47_kernel_bound {s : ℝ} (hs0 : 0 ≤ s) {z : Euc d} (hz : z ≠ 0) :
    |rieszKernel d s z| ≤ 1 * (2 * ‖z‖ ^ (-movtr_sp s) + ‖z‖ + 1) := by
  rw [one_mul, ← movtr_gEps_zero d s]
  exact movtr_gEps_abs_le hs0 le_rfl zero_le_one hz

theorem s47_kernel_measurable (s : ℝ) : Measurable (rieszKernel d s : Euc d → ℝ) := by
  rw [← movtr_gEps_zero d s]; exact movtr_gEps_measurable s 0

/-- `y ↦ g(x - y)` is integrable against a density with a Gaussian bound. -/
theorem s47_hint (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Euc d → ℝ}
    (hρ : IsProbDensity ρ) (hρc : Continuous ρ) {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (h0 : ∀ y, |ρ y| ≤ C * Real.exp (-c * ‖y‖ ^ 2)) (x : Euc d) :
    Integrable (fun y => rieszKernel d s (x - y)) (withDensityReal ρ) := by
  rw [HRS.MS.TcF.tc4_integrable_iff hρ]
  have := S45.s45_LI hd hs0 hsd hc (k := fun z => rieszKernel d s z) (h := ρ)
    (s47_kernel_measurable (d := d) s).aestronglyMeasurable hρc zero_le_one
    (fun z hz => s47_kernel_bound hs0 hz) hC h0 x
  exact this.congr (Filter.Eventually.of_forall fun y => by simp only; ring)

/-- `g * μ = locK + farK` (the constant `1`). -/
theorem s47_U_eq (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Euc d → ℝ}
    (hρ : IsProbDensity ρ) (hρc : Continuous ρ) {c C : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (h0 : ∀ y, |ρ y| ≤ C * Real.exp (-c * ‖y‖ ^ 2)) {θ : Euc d → ℝ} (hθ : HRS.MS.TcF.TcCutoff θ) :
    convMeasure (rieszKernel d s) (withDensityReal ρ) = fun x =>
      HRS.MS.TcF.locK d s θ ρ (fun _ => 1) x +
        HRS.MS.TcF.farK d s θ (withDensityReal ρ) (fun _ => 1) x := by
  funext x
  have h := HRS.MS.TcF.tc4_split_pt hρ hθ (s := s) (f := fun _ => (1 : ℝ)) (x := x)
    (by simpa using s47_hint hd hs0 hsd hρ hρc hc hC h0 x)
  simp only [mul_one] at h
  exact h

/-- The far part `farK μ 1` is `C^∞` with a bounded gradient, the bound depending only on `(d, s, θ)`. -/
theorem s47_far {s : ℝ} (hs0 : 0 ≤ s) {θ : Euc d → ℝ} (hθ : HRS.MS.TcF.TcCutoff θ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (μ : Measure (Euc d)) [IsProbabilityMeasure μ],
      Integrable (fun y : Euc d => ‖y‖ ^ 2) μ →
        ContDiff ℝ ∞ (HRS.MS.TcF.farK d s θ μ (fun _ => 1)) ∧
        ∀ x, ‖fderiv ℝ (HRS.MS.TcF.farK d s θ μ (fun _ => 1)) x‖ ≤ A := by
  obtain ⟨A, hA0, hA⟩ := HRS.MS.TcF.tc4_G_fderiv_bound hθ (s := s) hs0
  refine ⟨A, hA0, fun μ _ hm2 => ?_⟩
  have hf : Integrable (fun _ : Euc d => (1 : ℝ)) μ := integrable_const _
  have hint : ∀ x, Integrable (fun y => (fun _ : Euc d => (1 : ℝ)) y • HRS.MS.TcF.tc4_G d s θ (x - y)) μ :=
    fun x => HRS.MS.TcF.tc4_far_integrable hθ hA hm2 (memLp_const (1 : ℝ)) x
  have hG : ∀ n : ℕ, ContDiff ℝ (n + 1 : ℕ) (HRS.MS.TcF.tc4_G d s θ) := fun n =>
    (HRS.MS.TcF.tc4_G_contDiff hθ s).of_le (by exact_mod_cast le_top)
  have hb : ∀ n : ℕ, ∀ j, 1 ≤ j → j ≤ n + 1 →
      ∃ A, ∀ z, ‖iteratedFDeriv ℝ j (HRS.MS.TcF.tc4_G d s θ) z‖ ≤ A :=
    fun n j hj _ => HRS.MS.TcF.tc4_G_bound hθ hs0 hj
  rw [HRS.MS.TcF.farK_eq_conv]
  refine ⟨contDiff_infty.2 fun n => ?_, fun x => ?_⟩
  · exact (HRS.MS.TcF.tc4_contDiff_conv_succ hf n (hG n) (hb n) hint).of_le
      (by exact_mod_cast Nat.le_succ n)
  · have h := HRS.MS.TcF.tc4_norm_iteratedFDeriv_conv_le hf 0 ℝ (HRS.MS.TcF.tc4_G d s θ)
      (by simpa using hG 0) (by simpa using hb 0) hint A
      (fun z => by rw [zero_add, norm_iteratedFDeriv_one]; exact hA z) x
    rw [zero_add, norm_iteratedFDeriv_one] at h
    simpa using h

theorem s47_M0_nonneg {ρ : Euc d → ℝ} {M₀ c S : ℝ} {N : ℕ} (hρ : HRS.MS.TcDefs.TcRef d ρ M₀ c S N) :
    0 ≤ M₀ := by
  have h := hρ.gauss 0
  have h0 := hρ.pos 0
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    Real.exp_zero, mul_one] at h
  linarith

/-- The decomposition `U = locK + farK` for a reference density. -/
theorem s47_U_eq' (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Euc d → ℝ} {M₀ c S : ℝ} {N : ℕ}
    (hρ : HRS.MS.TcDefs.TcRef d ρ M₀ c S N) (hc : 0 < c) {θ : Euc d → ℝ}
    (hθ : HRS.MS.TcF.TcCutoff θ) :
    convMeasure (rieszKernel d s) (withDensityReal ρ) = fun x =>
      HRS.MS.TcF.locK d s θ ρ (fun _ => 1) x +
        HRS.MS.TcF.farK d s θ (withDensityReal ρ) (fun _ => 1) x :=
  s47_U_eq hd hs0 hsd hρ.prob hρ.smooth.continuous hc (s47_M0_nonneg hρ)
    (fun y => by rw [abs_of_pos (hρ.pos y)]; exact hρ.gauss y) hθ

/-- Smoothness (`C¹`) and a bound for the gradient of `U = g * μ`, uniform over the references. -/
theorem s47_U_grad (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (M₀ c : ℝ) (hc : 0 < c) :
    ∃ K A : ℝ, 0 ≤ K ∧ 0 ≤ A ∧ ∀ (ρ : Euc d → ℝ) (S : ℝ), HRS.MS.TcDefs.TcRef d ρ M₀ c S 1 →
      ContDiff ℝ 1 (convMeasure (rieszKernel d s) (withDensityReal ρ)) ∧
      ∀ y, ‖gradient (convMeasure (rieszKernel d s) (withDensityReal ρ)) y‖ ≤ K * S + A := by
  obtain ⟨θ, hθ⟩ := HRS.MS.Tc5.tc5_cutoff (d := d)
  obtain ⟨A, hA0, hA⟩ := s47_far hs0 hθ
  obtain ⟨C, hC0, hC⟩ := HRS.MS.TcF.tc4_loc_cb_rho 1 hθ hs0 hsd c hc
  refine ⟨C * (∫ z, ‖θ z * rieszKernel d s z‖), A, by positivity, hA0, fun ρ S hρ => ?_⟩
  have := HRS.MS.TcF.tc4_isProb hρ.prob
  obtain ⟨hloc, hlocn⟩ := hC ρ M₀ S hρ (fun _ => 1) (HRS.MS.Tc5.tc5_cb_const 1 1).1
  obtain ⟨hfar, hfarn⟩ := hA (withDensityReal ρ) (HRS.MS.TcF.tc4_sq_integrable hρ hc)
  have hU := s47_U_eq' hd hs0 hsd hρ hc hθ
  have hlocd : ContDiff ℝ 1 (HRS.MS.TcF.locK d s θ ρ (fun _ => 1)) := by
    simpa using hloc.1
  have hfard : ContDiff ℝ 1 (HRS.MS.TcF.farK d s θ (withDensityReal ρ) (fun _ => 1)) :=
    hfar.of_le (by exact_mod_cast le_top)
  have hsum : convMeasure (rieszKernel d s) (withDensityReal ρ) =
      HRS.MS.TcF.locK d s θ ρ (fun _ => 1) + HRS.MS.TcF.farK d s θ (withDensityReal ρ) (fun _ => 1) := by
    rw [hU]; rfl
  rw [hsum]
  refine ⟨hlocd.add hfard, fun y => ?_⟩
  rw [S45.s45_norm_gradient, fderiv_add (hlocd.differentiable (by simp) y) (hfard.differentiable (by simp) y)]
  have h1 : ‖fderiv ℝ (HRS.MS.TcF.locK d s θ ρ (fun _ => 1)) y‖ ≤
      C * (∫ z, ‖θ z * rieszKernel d s z‖) * S := by
    have h := HRS.MS.UniqF.uniqf_norm_le_cbNorm hloc (j := 1) le_rfl y
    rw [norm_iteratedFDeriv_one] at h
    refine h.trans (hlocn.trans ?_)
    have hcb : HRS.cbNorm 1 (fun _ : Euc d => (1 : ℝ)) ≤ 1 := by
      have := (HRS.MS.Tc5.tc5_cb_const (d := d) 1 1).2
      simpa using this
    have hI : 0 ≤ ∫ z, ‖θ z * rieszKernel d s z‖ := integral_nonneg fun _ => norm_nonneg _
    have hCS : 0 ≤ C * S * (∫ z, ‖θ z * rieszKernel d s z‖) := by
      have hS0 : 0 ≤ S := by
        have h3 := hρ.deriv 0 (Nat.zero_le _) 0
        rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_of_pos (hρ.pos 0)] at h3
        norm_num at h3
        linarith [hρ.pos 0]
      positivity
    calc C * S * (∫ z, ‖θ z * rieszKernel d s z‖) * HRS.cbNorm 1 (fun _ : Euc d => (1 : ℝ))
        ≤ C * S * (∫ z, ‖θ z * rieszKernel d s z‖) * 1 := mul_le_mul_of_nonneg_left hcb hCS
      _ = C * (∫ z, ‖θ z * rieszKernel d s z‖) * S := by ring
  calc ‖fderiv ℝ (HRS.MS.TcF.locK d s θ ρ fun _ => 1) y +
        fderiv ℝ (HRS.MS.TcF.farK d s θ (withDensityReal ρ) fun _ => 1) y‖
      ≤ ‖fderiv ℝ (HRS.MS.TcF.locK d s θ ρ fun _ => 1) y‖ +
        ‖fderiv ℝ (HRS.MS.TcF.farK d s θ (withDensityReal ρ) fun _ => 1) y‖ := norm_add_le _ _
    _ ≤ _ := add_le_add h1 (hfarn y)

/-- `U = g * μ` is `C^∞` for a reference density with Gaussian-weighted derivative bounds of every order. -/
theorem s47_U_smooth (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Euc d → ℝ} {M₀ c : ℝ}
    (hc : 0 < c) (hρ : ∀ N : ℕ, ∃ S : ℝ, HRS.MS.TcDefs.TcRef d ρ M₀ c S N) :
    ContDiff ℝ ∞ (convMeasure (rieszKernel d s) (withDensityReal ρ)) := by
  obtain ⟨θ, hθ⟩ := HRS.MS.Tc5.tc5_cutoff (d := d)
  obtain ⟨A, hA0, hA⟩ := s47_far hs0 hθ
  obtain ⟨S0, hS0⟩ := hρ 0
  have := HRS.MS.TcF.tc4_isProb hS0.prob
  obtain ⟨hfar, -⟩ := hA (withDensityReal ρ) (HRS.MS.TcF.tc4_sq_integrable hS0 hc)
  refine contDiff_infty.2 fun n => ?_
  obtain ⟨S, hS⟩ := hρ n
  obtain ⟨C, hC0, hC⟩ := HRS.MS.TcF.tc4_loc_cb_rho n hθ hs0 hsd c hc
  obtain ⟨hloc, -⟩ := hC ρ M₀ S hS (fun _ => 1) (HRS.MS.Tc5.tc5_cb_const n 1).1
  have hU := s47_U_eq' hd hs0 hsd hS hc hθ
  rw [hU]
  exact hloc.1.add (hfar.of_le (by exact_mod_cast le_top))

/-- qualitative: every member of the uniform class has `TcRef` of every order (constants depending on `ρ`), used only for
the `C^∞` regularity of `g * ρ`. -/
theorem s47_hall (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β εstar : ℝ} (ha : 0 < a) (hβ : 0 < β)
    {ρ : Euc d → ℝ} (hρ : HRS.MS.S48.UnifRef d s a β εstar ρ) :
    ∃ c M₀ : ℝ, 0 < c ∧ ∀ N : ℕ, ∃ S : ℝ, HRS.MS.TcDefs.TcRef d ρ M₀ c S N := by
  rcases hρ with rfl | ⟨ε, ψ, hε, -, rfl⟩
  · obtain ⟨c, M₀, m₂, hc, hM₀, hpk⟩ := HRS.MS.S48.s48_ref_data hd hs0 hsd ha hβ le_rfl le_rfl (0 : Euc d → ℝ)
    refine ⟨c, M₀, hc, fun N => ?_⟩
    obtain ⟨S, Mb, h⟩ := hpk N 0
    exact ⟨S, (h a β le_rfl le_rfl le_rfl le_rfl _ IsStaticReference.thermal).ref⟩
  · obtain ⟨c, M₀, m₂, hc, hM₀, hpk⟩ := HRS.MS.S48.s48_ref_data hd hs0 hsd ha hβ le_rfl le_rfl ψ
    refine ⟨c, M₀, hc, fun N => ?_⟩
    obtain ⟨S, Mb, h⟩ := hpk N 0
    exact ⟨S, (h a β le_rfl le_rfl le_rfl le_rfl _ (IsStaticReference.perturbed ε hε)).ref⟩

/-- **Uniform reference data, uniform over the tilt class** (ED15R).  For `a, β` in compact positive intervals and `ρ` the
thermal density or a compact relative perturbation `(1+εψ)ρ_*` with `‖εψ‖_{C_b^{100d+1001}} ≤ ε_*` (`UnifRef`), `ρ` satisfies
`TRef` with `q = a β` and constants depending only on `ε_*` (not on `ε, ψ`). -/
theorem s47_tref_unif (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {am ap βm βp : ℝ} (ham : 0 < am)
    (hβm : 0 < βm) (hap : am ≤ ap) (hβp : βm ≤ βp) (εstar : ℝ) :
    ∃ C c BU BB : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ a β : ℝ, am ≤ a → a ≤ ap → βm ≤ β → β ≤ βp →
      ∀ ρ : Euc d → ℝ, HRS.MS.S48.UnifRef d s a β εstar ρ →
        ∃ Bd : Euc d → Euc d, TRef d s ρ (a * β) C c BU BB Bd := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨c₀, M₀, m₂, hc₀, hM₀, hpk⟩ := HRS.MS.S48.s48_ref_data_unif hd hs0 hsd ham hβm hap hβp εstar
  obtain ⟨S, Mb, hS⟩ := hpk 1 0 (by omega)
  obtain ⟨Cp, hCp0, hCp⟩ := S45.s45_poly_le (half_pos hc₀)
  obtain ⟨K, A, hK0, hA0, hKA⟩ := s47_U_grad hd1 hs0 hsd M₀ c₀ hc₀
  refine ⟨max M₀ (|S| * Cp), c₀ / 2, K * |S| + A, |Mb|, le_max_of_le_left hM₀.le, half_pos hc₀,
    fun a β h1 h2 h3 h4 ρ hρ => ?_⟩
  have hp := hS a β h1 h2 h3 h4 ρ hρ
  have href := hp.ref
  obtain ⟨Bd, hR, hcb⟩ := hp.drift
  obtain ⟨c', M₀', hc', hall⟩ := s47_hall hd hs0 hsd (ham.trans_le h1) (hβm.trans_le h3) hρ
  refine ⟨Bd, ?_⟩
  obtain ⟨hUc, hUb⟩ := hKA ρ S href
  have hS0 : 0 ≤ S := by
    have h3 := href.deriv 0 (Nat.zero_le _) 0
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_of_pos (href.pos 0)] at h3
    norm_num at h3
    linarith [href.pos 0]
  refine ⟨href.prob, href.smooth, href.pos, le_max_of_le_left hM₀.le, half_pos hc₀, fun y => ?_,
    fun y => ?_, s47_U_smooth hd1 hs0 hsd hc' hall, by positivity, fun y => ?_,
    hcb.1.continuous, abs_nonneg _, fun y => ?_, hR.grad⟩
  · rw [abs_of_nonneg (href.prob.nonneg y)]
    refine (href.gauss y).trans ?_
    have : Real.exp (-c₀ * ‖y‖ ^ 2) ≤ Real.exp (-(c₀ / 2) * ‖y‖ ^ 2) :=
      Real.exp_le_exp.2 (by nlinarith [sq_nonneg ‖y‖])
    calc M₀ * Real.exp (-c₀ * ‖y‖ ^ 2) ≤ M₀ * Real.exp (-(c₀ / 2) * ‖y‖ ^ 2) :=
          mul_le_mul_of_nonneg_left this hM₀.le
      _ ≤ max M₀ (|S| * Cp) * Real.exp (-(c₀ / 2) * ‖y‖ ^ 2) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
  · have h := href.deriv 1 le_rfl y
    rw [norm_iteratedFDeriv_one] at h
    have hp := hCp ‖y‖ (norm_nonneg _)
    have e : Real.exp (c₀ / 2 * ‖y‖ ^ 2) * Real.exp (-c₀ * ‖y‖ ^ 2) =
        Real.exp (-(c₀ / 2) * ‖y‖ ^ 2) := by rw [← Real.exp_add]; congr 1; ring
    calc ‖fderiv ℝ ρ y‖ ≤ S * (1 + ‖y‖) ^ 1 * Real.exp (-c₀ * ‖y‖ ^ 2) := h
      _ = S * (1 + ‖y‖) * Real.exp (-c₀ * ‖y‖ ^ 2) := by rw [pow_one]
      _ ≤ S * (Cp * Real.exp (c₀ / 2 * ‖y‖ ^ 2)) * Real.exp (-c₀ * ‖y‖ ^ 2) := by gcongr
      _ = (S * Cp) * (Real.exp (c₀ / 2 * ‖y‖ ^ 2) * Real.exp (-c₀ * ‖y‖ ^ 2)) := by ring
      _ = (S * Cp) * Real.exp (-(c₀ / 2) * ‖y‖ ^ 2) := by rw [e]
      _ ≤ max M₀ (|S| * Cp) * Real.exp (-(c₀ / 2) * ‖y‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          exact (mul_le_mul_of_nonneg_right (le_abs_self S) hCp0).trans (le_max_right _ _)
  · refine (hUb y).trans ?_
    rw [abs_of_nonneg hS0]
  · have h := hcb.2 0 le_rfl y
    rw [norm_iteratedFDeriv_zero] at h
    exact h.trans (le_abs_self _)

/-- **Uniform reference data** (fixed `ψ`; a corollary of `s47_tref_unif`).  For `a, β` in compact positive intervals and `ρ` the
thermal density or a compact relative perturbation `(1+εψ)ρ_*` (`IsStaticReference`), `ρ` satisfies `TRef` with `q = a β`. -/
theorem s47_tref (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {am ap βm βp : ℝ} (ham : 0 < am)
    (hβm : 0 < βm) (hap : am ≤ ap) (hβp : βm ≤ βp) (ψ : Euc d → ℝ) :
    ∃ C c BU BB : ℝ, 0 ≤ C ∧ 0 < c ∧ ∀ a β : ℝ, am ≤ a → a ≤ ap → βm ≤ β → β ≤ βp →
      ∀ ρ : Euc d → ℝ, IsStaticReference d s a β ψ ρ →
        ∃ Bd : Euc d → Euc d, TRef d s ρ (a * β) C c BU BB Bd := by
  obtain ⟨εstar, hε⟩ := HRS.MS.S48.s48_static_to_unif (d := d) ψ
  obtain ⟨C, c, BU, BB, hC0, hc, h⟩ := s47_tref_unif hd hs0 hsd ham hβm hap hβp εstar
  exact ⟨C, c, BU, BB, hC0, hc, fun a β h1 h2 h3 h4 ρ hρ => h a β h1 h2 h3 h4 ρ (hε s a β ρ hρ)⟩

end S47

end
