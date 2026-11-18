import HRS.MS.MovAdjAux26

/-!
# S6.7 nonlinear row, package A (Sigma-level adjoint theory), packet N1: the weak Volterra identity

Namespace `HRS.MS.MovAdjNl`, helpers `s67a_`.  Infrastructure for the supplement row `S:W:lem:r2mov-global-adjoint`
(`HRS.Whole.mov_global_adjoint_nonlinear`); not a manuscript row.  The plan is
summarized in the docstring of `MovAdjNlAux1` below.

## Verdict on the frozen statement
TRUE and NON-VACUOUS (junk-value analysis as in `HRS.MS.MovAdj` / `docs/S67_PLAN.md`, section 0).  Only `rho in MovInSmallClass` is used
through `||v_u||_{Sigma^m} <= r` (u >= 0) and continuity of `rho^u`; constants of the statement are existential (use `s67_shrink`).

## Plan (packets, each `<= 2k` lines)
* N1 (this file): `s67aR` = (generator along `rho^u`) - (stationary generator); **`s67a_volterra`**: for a classical adjoint solution `f` of the
  coefficient `coeff rho^u`, `0 <= r <= t` and `v0` in the Schwartz core of `L^2_0`:
  `int f_r sqrt(rho0) v0 = int phi sqrt(rho0) T(t-r) v0 + int_0^{t-r} int s67aR_{r+sig}(f_{r+sig}) sqrt(rho0) T(sig) v0 dsig`.
* N2: structure of `s67aR`: `sqrt(rho0) R_u f = E_u(psi_u)`, `E(psi) = -F.q + sqrt(rho0) sum_k d_k g * (v q_k)`, `q = grad psi - psi l/2`.
* N3: `||E(psi)||_{Sigma^{p-a}} <= K_p ||v||_{Sigma^m} ||psi||_{Sigma^p}`, every real `p in [2,M]` (movc2_alg, movc1_loc_term, mo_mult_cb, movc2_Phi).
* N4: a priori `psi_u in Sigma^2` (converse ladder).   N5: abstract Volterra lemma, bootstrap `Sigma^p -> Sigma^{p+delta}`, `delta < 2-a`, absorption.
* N6: `||J_u f_u||_{C_b^{j+1}} <= K ||psi_u||_{Sigma^M}`.   N7: packaged statement `s67a_sigma_decay`.
Not in package A: the `C_b^j` Duhamel/Volterra (uses `gradient_smoothing_cb`, S67B) and the tie.

## This file
* `s67a_L0_growth`: `|generatorW (stationary) r u x| <= B (1+|x|)` for `u in C_b^2`.
* `s67a_int_lin`: a measurable function of linear growth times `sqrt(rho0) phi'` is integrable (`phi'` Schwartz).
* `s67a_hdv`: right derivative of `tau -> f_{clamp(r+tau)} sqrt(rho0)` in `L^2` for an ARBITRARY coefficient `C` (generalises `s67a_hasDeriv`).
* `s67a_gdv`: right derivative of the pairing `g(sig) = <f_{r+sig} sqrt(rho0), T(sig) v0>` is `-k(sig)`, `k(sig) = int s67aR(..) sqrt(rho0) T(sig) v0`.
* `s67a_volterra`: the identity above (FTC for right derivatives with integrable derivative).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovAdjNl

open HRS HRS.Whole HRS.MH.DualityRd HRS.MS.MovLin HRS.MS.Mov63 HRS.MS.MovAdj

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

/-- The part of the generator along `ρ^u` beyond the stationary generator: `R_u g = 𝓛^{ρ^u}_u g - 𝓛^{ρ₀}_u g`. -/
def s67aR (d : ℕ) (s q β : ℝ) (ρ : Euc d → ℝ) (ρt : ℝ → Euc d → ℝ) (u : ℝ) (g : Euc d → ℝ) (x : Euc d) : ℝ :=
  generatorW ((quadraticGradientDyn d s q β).coeff ρt) u g x -
    generatorW ((quadraticGradientDyn d s q β).coeff (fun _ => ρ)) u g x

/-! ### Growth and measurability of the stationary generator -/

theorem s67a_L0_growth (H : Mov2dTh d s β q ρ) {u : Euc d → ℝ} (hu : MemCb 2 u) (r : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, |generatorW ((quadraticGradientDyn d s q β).coeff (fun _ => ρ)) r u x| ≤
      B * (1 + ‖x‖) := by
  obtain ⟨B, hB0, hBu, hB1, hB2⟩ := s67_memCb_bounds hu
  obtain ⟨⟨BJ, hBJ⟩, -⟩ := s67_J_bdd H hu
  obtain ⟨hEq, -, hC⟩ := HRS.MS.MovC1.mov_force_tail_thermal H.hd H.hs0 H.hsd β q H.hβ H.hq ρ H.hρ
  obtain ⟨Cf, hCf⟩ := hC 0
  have hF : ∀ x, ‖movForce d s ρ x‖ ≤ Cf := fun x => by
    have := (hCf x).1
    rwa [norm_iteratedFDeriv_zero, ← hEq x] at this
  have hCf0 : 0 ≤ Cf := (norm_nonneg _).trans (hF 0)
  have hβ0 := H.hβ
  have hq0 := H.hq
  refine ⟨β⁻¹ * (d * B) + (q + Cf) * B + |BJ|, by positivity, fun x => ?_⟩
  rw [s67_gen_eq]
  have h1 : |β⁻¹ * Laplacian.laplacian u x| ≤ β⁻¹ * (d * B) := by
    rw [abs_mul, abs_of_pos (inv_pos.2 hβ0)]
    exact mul_le_mul_of_nonneg_left (s67_lap_bound hB2 x) (inv_pos.2 hβ0).le
  have h2 : |inner ℝ (-(q • x) - movForce d s ρ x) (gradient u x)| ≤ (q * ‖x‖ + Cf) * B := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    have e1 : ‖gradient u x‖ ≤ B := by rw [s67_grad_norm]; exact hB1 x
    have e2 : ‖-(q • x) - movForce d s ρ x‖ ≤ q * ‖x‖ + Cf := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_neg, norm_smul, Real.norm_of_nonneg hq0.le]
      exact add_le_add le_rfl (hF x)
    exact mul_le_mul e2 e1 (norm_nonneg _) (by positivity)
  have h3 : |s67J d s ρ u x| ≤ |BJ| := (hBJ x).trans (le_abs_self _)
  have hx : 0 ≤ ‖x‖ := norm_nonneg x
  calc |β⁻¹ * Laplacian.laplacian u x + inner ℝ (-(q • x) - movForce d s ρ x) (gradient u x) +
        s67J d s ρ u x|
      ≤ |β⁻¹ * Laplacian.laplacian u x| + |inner ℝ (-(q • x) - movForce d s ρ x) (gradient u x)| +
        |s67J d s ρ u x| := by
        refine (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ β⁻¹ * (d * B) + (q * ‖x‖ + Cf) * B + |BJ| := add_le_add (add_le_add h1 h2) h3
    _ ≤ (β⁻¹ * (d * B) + (q + Cf) * B + |BJ|) * (1 + ‖x‖) := by
        have hB0' : 0 ≤ B := hB0
        have habs : 0 ≤ |BJ| := abs_nonneg _
        have hp : 0 ≤ β⁻¹ * (d * B) := by positivity
        nlinarith [mul_nonneg hx hp, mul_nonneg hx habs, mul_nonneg hx (mul_nonneg (add_nonneg hq0.le hCf0) hB0'),
          mul_nonneg hx (mul_nonneg hCf0 hB0'), mul_nonneg hx (mul_nonneg hq0.le hB0')]

theorem s67a_L0_meas (H : Mov2dTh d s β q ρ) {u : Euc d → ℝ} (hu : MemCb 2 u) (r : ℝ) :
    AEStronglyMeasurable (generatorW ((quadraticGradientDyn d s q β).coeff (fun _ => ρ)) r u)
      (volume : Measure (Euc d)) := by
  obtain ⟨⟨BJ, hBJ⟩, hJm⟩ := s67_J_bdd H hu
  obtain ⟨hEq, hCD, -⟩ := HRS.MS.MovC1.mov_force_tail_thermal H.hd H.hs0 H.hsd β q H.hβ H.hq ρ H.hρ
  have hFc : Continuous (movForce d s ρ) := by
    have : movForce d s ρ = fun x => gradient (HRS.Whole.convFun (rieszKernel d s) ρ) x := funext hEq
    rw [this]; exact hCD.continuous
  have hg : Continuous (fun y => gradient u y) := s67_grad_cont (hu.1.of_le (by norm_num))
  have hL : Continuous (Laplacian.laplacian u) := s67_lap_cont hu.1
  have e : generatorW ((quadraticGradientDyn d s q β).coeff (fun _ => ρ)) r u = fun x =>
      β⁻¹ * Laplacian.laplacian u x + inner ℝ (-(q • x) - movForce d s ρ x) (gradient u x) + s67J d s ρ u x := by
    funext x; exact s67_gen_eq s q β ρ r u x
  rw [e]
  refine AEStronglyMeasurable.add (AEStronglyMeasurable.add ?_ ?_) hJm.aestronglyMeasurable
  · exact (continuous_const.mul hL).aestronglyMeasurable
  · have h1 : Continuous (fun x : Euc d => -(q • x) - movForce d s ρ x) :=
      by fun_prop
    have hc : Continuous (fun x : Euc d => inner ℝ (-(q • x) - movForce d s ρ x) (gradient u x)) :=
      Continuous.inner h1 hg
    exact hc.aestronglyMeasurable

/-- A measurable function of linear growth times `√ρ φ'` (`φ'` Schwartz) is integrable. -/
theorem s67a_int_lin (H : Mov2dTh d s β q ρ) {F : Euc d → ℝ}
    (hF : AEStronglyMeasurable F (volume : Measure (Euc d))) {B : ℝ} (hB : ∀ x, |F x| ≤ B * (1 + ‖x‖))
    (φ' : 𝓢R) : Integrable (fun x => F x * (Real.sqrt (ρ x) * φ' x)) := by
  have hG := s67_memLp_G H
  have hφ : MemLp (⇑φ' : Euc d → ℝ) 2 (volume : Measure (Euc d)) := φ'.memLp 2
  have hI : Integrable (fun x => ((1 + ‖x‖) * Real.sqrt (ρ x)) * φ' x) := hG.integrable_mul hφ
  have hρ := mnb_rhoData H
  have hm : AEStronglyMeasurable (fun x => Real.sqrt (ρ x) * φ' x) (volume : Measure (Euc d)) :=
    (hρ.smooth.continuous.sqrt.mul φ'.continuous).aestronglyMeasurable
  refine (hI.norm.const_mul |B|).mono' (hF.mul hm) (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  calc |F x| * (Real.sqrt (ρ x) * |φ' x|) ≤ (B * (1 + ‖x‖)) * (Real.sqrt (ρ x) * |φ' x|) :=
        mul_le_mul_of_nonneg_right (hB x) (by positivity)
    _ ≤ |B| * ((1 + ‖x‖) * Real.sqrt (ρ x) * |φ' x|) := by
        have : B * (1 + ‖x‖) * (Real.sqrt (ρ x) * |φ' x|) = B * ((1 + ‖x‖) * Real.sqrt (ρ x) * |φ' x|) := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_right (le_abs_self B) (by positivity)
    _ = |B| * ‖((1 + ‖x‖) * Real.sqrt (ρ x)) * φ' x‖ := by
        have h1 : (0 : ℝ) ≤ 1 + ‖x‖ := by positivity
        simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg h1, abs_of_nonneg (Real.sqrt_nonneg (ρ x))]

/-! ### The `L²` derivative of `f_r √ρ` for an arbitrary coefficient -/

theorem s67a_hdv (H : Mov2dTh d s β q ρ) {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW C t φ f) (ht : 0 ≤ t)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) t)
    (hgL : MemLp (fun x => Real.sqrt (ρ x)) 2 (volume : Measure (Euc d))) {σ : ℝ}
    (hσ : σ ∈ Set.Ioo (0 : ℝ) (t - r)) :
    ∃ (a' : Euc d → ℝ) (ha' : MemLp a' 2 (volume : Measure (Euc d))),
      (∀ x, a' x = (-(generatorW C (r + σ) (f (r + σ)) x)) * Real.sqrt (ρ x)) ∧
      HasDerivWithinAt (fun τ => (s67a_memLp hf ht r hgL τ).toLp (s67a f ρ r t τ))
        (ha'.toLp a') (Set.Ici σ) σ := by
  have hρ := mnb_rhoData H
  obtain ⟨Bf, hBf0, hBgen, hlip⟩ := s67_time_lip hf
  have hr1 : 0 < r + σ := by linarith [hr.1, hσ.1]
  have hr2 : r + σ < t := by linarith [hσ.2]
  set r' := r + σ with hr'
  have hr'mem : r' ∈ Set.Icc (0 : ℝ) t := ⟨hr1.le, hr2.le⟩
  have hclσ : s67clamp r t σ = r' := s67clamp_eq hr1.le hr2.le
  set a' : Euc d → ℝ := fun x => (-(generatorW C r' (f r') x)) * Real.sqrt (ρ x) with ha'def
  set G : Euc d → ℝ := fun x => Bf * ((1 + ‖x‖) * Real.sqrt (ρ x)) with hGdef
  have hGL : MemLp G 2 (volume : Measure (Euc d)) := (s67_memLp_G H).const_mul Bf
  have ha'meas : AEStronglyMeasurable a' (volume : Measure (Euc d)) := by
    have h1 : Continuous fun x => generatorW C r' (f r') x := s67_gen_cont hf hr'mem
    exact ((h1.neg).mul hρ.smooth.continuous.sqrt).aestronglyMeasurable
  have hbG : ∀ x, |a' x| ≤ G x := by
    intro x
    rw [ha'def]
    dsimp only
    rw [abs_mul, abs_neg, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc |generatorW C r' (f r') x| * Real.sqrt (ρ x) ≤ (Bf * (1 + ‖x‖)) * Real.sqrt (ρ x) :=
          mul_le_mul_of_nonneg_right (hBgen r' hr'mem x) (Real.sqrt_nonneg _)
      _ = G x := by rw [hGdef]; ring
  have ha'L : MemLp a' 2 (volume : Measure (Euc d)) :=
    MemLp.of_le_mul (c := 1) hGL ha'meas (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul, abs_of_nonneg
        (mul_nonneg hBf0 (mul_nonneg (by positivity) (Real.sqrt_nonneg _)))]
      exact hbG x)
  have hdom : ∀ τ ∈ Set.Ioo σ (σ + (t - r - σ)), ∀ x,
      |s67a f ρ r t τ x - s67a f ρ r t σ x| ≤ (τ - σ) * G x := by
    intro τ hτ x
    have hτ1 : r + τ < t := by linarith [hτ.2]
    have hτ0 : 0 ≤ r + τ := by linarith [hτ.1]
    have e1 : s67clamp r t τ = r + τ := s67clamp_eq hτ0 hτ1.le
    unfold s67a
    rw [e1, hclσ, ← sub_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    have := hlip r' (r + τ) hr1 (by linarith [hτ.1]) hτ1.le x
    calc |f (r + τ) x - f r' x| * Real.sqrt (ρ x) ≤ (Bf * (1 + ‖x‖) * (r + τ - r')) * Real.sqrt (ρ x) :=
          mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg _)
      _ = (τ - σ) * G x := by rw [hGdef, hr']; ring
  have hpt : ∀ x, Tendsto (fun τ => (τ - σ)⁻¹ * (s67a f ρ r t τ x - s67a f ρ r t σ x)) (𝓝[>] σ)
      (𝓝 (a' x)) := by
    intro x
    have hd1 : HasDerivAt (fun τ => f (r + τ) x) (-(generatorW C r' (f r') x)) σ := by
      have := hf.time_deriv x r' ⟨hr1, hr2⟩
      exact this.comp_const_add r σ
    have hsl := (hasDerivAt_iff_tendsto_slope.1 hd1).mono_left (nhdsGT_le_nhdsNE σ)
    have hsl' := hsl.mul_const (Real.sqrt (ρ x))
    refine hsl'.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (show σ < σ + (t - r - σ) by linarith)] with τ hτ
    have hτ1 : r + τ < t := by linarith [hτ.2]
    have hτ0 : 0 ≤ r + τ := by linarith [hτ.1]
    have e1 : s67clamp r t τ = r + τ := s67clamp_eq hτ0 hτ1.le
    unfold s67a
    rw [e1, hclσ, slope_def_field, ← sub_mul]
    simp only [← hr']
    field_simp
  refine ⟨a', ha'L, fun x => rfl, ?_⟩
  exact s67_hasDeriv_toLp (a := s67a f ρ r t) (a' := a') (G := G) (σ := σ) (δ := t - r - σ)
    (by linarith [hσ.2]) (s67a_memLp hf ht r hgL) hGL ha'L hdom hpt hbG

end HRS.MS.MovAdjNl
