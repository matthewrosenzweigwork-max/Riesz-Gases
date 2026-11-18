import HRS.MS.GapRefAux1
import HRS.MS.ThCorrAux1
import HRS.MS.ThCorrDriftAux1
import HRS.MS.ThmSpecAux2
import Mathlib.Analysis.Distribution.TemperateGrowth

/-!
# MOV-0 (part 1): thermal data for S6.1, abstract Gaussian calculus

Namespace `HRS.MS.Mov0`; helper prefix `mov0_`, output prefix `mv0_`.  Infrastructure for the supplement packet
S6.1 (`docs/MOV_PLAN.md`, step 1, brief MOV-0); no frozen statement is touched.

Contents of this file.
* `mv0_rho_eq`: an `IsThermalEquilibrium d s q β ρ` equals `thermalDensity d s q β` at every point (`0 ≤ s < d`),
  from the a.e. uniqueness (`thermalDensity_spec_proof` / `logThermalDensity_spec_proof`) and the pointwise
  rigidity of the thermal equation (`thermalDensity_eq_pointwise`).
* `mv0_gapref`: `GapRef d ρ (β * q) B` for `B = -β ∇(g * μ)` (and `C_b^m` bounds for every `m`); the data comes from
  `Tc6.tc6_unif` (box `a = q`, `β = β`) and `Tc1.tc1_B_eq`.
* Abstract calculus (generic in a positive function `u` with `∇u = u (-a x + B')`, `B'` bounded of temperate growth):
  `mov0_tensor` (`D^k u = u · P_k` with `P_k` of temperate growth, by induction on tensors), `mov0_ray_bound`
  (`u(x) ≤ u(0) exp(-a‖x‖²/2 + M‖x‖)`, integration along rays), `mov0_gauss_deriv`
  (`‖D^k u x‖ ≤ C_k exp(-(a/4)‖x‖²)`).

Statement adjustment relative to the plan sketch: in `mv0_gapref` the explicit formula for `B` is part of the
conclusion; the generic Gaussian lemmas carry the hypothesis `0 < a` (`q' > 0`), which `GapRef` alone does not give.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff
open HRS HRS.Whole

noncomputable section

namespace HRS.MS.Mov0

variable {d : ℕ}

/-! ### Pointwise identification and `GapRef` -/

/-- **MOV-0, step 1a.**  A thermal equilibrium (free-energy minimiser satisfying the thermal equation) equals
`thermalDensity d s q β` at every point. -/
theorem mv0_rho_eq (hd : 2 ≤ d) {s q β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hq : 0 < q) (hb : 0 < β)
    {ρ : Euc d → ℝ} (h : IsThermalEquilibrium d s q β ρ) : ρ = thermalDensity d s q β := by
  have hae : ρ =ᵐ[volume] thermalDensity d s q β := by
    rcases hs0.eq_or_lt with h0 | h0
    · subst h0
      exact (HRS.MS.Thm.logThermalDensity_spec_proof (d := d) hd q β hq hb).2.2 ρ h.1
    · exact (HRS.MS.Thm.thermalDensity_spec_proof (d := d) (s := s) hd h0 hsd q β hq hb).2.2 ρ h.1
  have hth := HRS.MS.Tc1.tc1_thermal_eq hd hs0 hsd hq hb
  funext x
  exact HRS.MS.Thm.thermalDensity_eq_pointwise h.2 hth hae x

/-- **MOV-0, step 1b.**  `GapRef d ρ (β q) B` with `B = -β ∇(g * μ)`, `μ = ρ dx`; in particular `ρ > 0`,
`ρ ∈ C^∞`, `∇ρ = ρ(-(βq)x + B)` and `B ∈ C_b^m` for every `m`. -/
theorem mv0_gapref (hd : 2 ≤ d) {s q β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hq : 0 < q) (hb : 0 < β)
    {ρ : Euc d → ℝ} (h : IsThermalEquilibrium d s q β ρ) :
    ∃ B : Euc d → Euc d,
      B = (fun x => (-β) • gradient (HRS.Whole.convMeasure (rieszKernel d s) (thermalMeasure d s q β)) x) ∧
      HRS.MS.Gap.GapRef d ρ (β * q) B ∧ ∀ m : ℕ, ∃ Mb : ℝ, HasCbBound m Mb B := by
  have hρ := mv0_rho_eq hd hs0 hsd hq hb h
  subst hρ
  obtain ⟨c, M₀, m₂, hc, hM₀, -, hdr⟩ :=
    HRS.MS.Tc6.tc6_unif hd hs0 hsd (am := q) (ap := q) (βm := β) (βp := β) hq hb le_rfl le_rfl
  obtain ⟨Mb, -, hMb⟩ := hdr 0
  obtain ⟨B, hR, -⟩ := (hMb q β le_rfl le_rfl le_rfl le_rfl).gap
  have hR' : HRS.MS.Gap.GapRef d (thermalDensity d s q β) (q * β) B := by rwa [mul_comm q β]
  have hBeq := HRS.MS.Tc1.tc1_B_eq hd hs0 hsd hq hb hR'
  exact ⟨B, hBeq, hR, hR.cb⟩

/-! ### Abstract calculus: tensors, ray bound, Gaussian bounds -/

/-- The derivative of a function of temperate growth has temperate growth. -/
lemma mov0_tg_fderiv {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → F} (hf : f.HasTemperateGrowth) : (fderiv ℝ f).HasTemperateGrowth := by
  refine ⟨hf.1.fderiv_right (m := ∞) (by simp), fun n => ?_⟩
  obtain ⟨k, C, h⟩ := hf.2 (n + 1)
  exact ⟨k, C, fun x => by rw [norm_iteratedFDeriv_fderiv]; exact h x⟩

/-- The covector `⟪v, ·⟫` as a continuous linear map in `v`. -/
def mov0_dualL (d : ℕ) : Euc d →L[ℝ] (Euc d →L[ℝ] ℝ) := (innerSL ℝ : Euc d →L[ℝ] Euc d →L[ℝ] ℝ)

lemma mov0_dualL_apply (v w : Euc d) : mov0_dualL d v w = inner ℝ v w := by
  rfl

lemma mov0_fderiv_eq_dual (u : Euc d → ℝ) (x : Euc d) : fderiv ℝ u x = mov0_dualL d (gradient u x) := by
  ext v
  rw [mov0_dualL_apply, real_inner_comm, HRS.MS.PoisKolm.kl_inner_gradient]

/-- `k`-linear forms on `ℝ^d`. -/
abbrev mov0_M (d k : ℕ) : Type := ContinuousMultilinearMap ℝ (fun _ : Fin k => Euc d) ℝ

/-- **Tensor induction.**  If `∇u = u L` with `L` of temperate growth, then `D^k u = u · P_k` with `P_k` of temperate
growth (valued in `k`-linear forms). -/
lemma mov0_tensor {u : Euc d → ℝ} (hu : ContDiff ℝ ∞ u) {L : Euc d → Euc d} (hL : L.HasTemperateGrowth)
    (hgrad : ∀ x, gradient u x = u x • L x) (k : ℕ) :
    ∃ P : Euc d → mov0_M d k, P.HasTemperateGrowth ∧ ∀ x, iteratedFDeriv ℝ k u x = u x • P x := by
  induction k with
  | zero =>
    refine ⟨fun _ => (continuousMultilinearCurryFin0 ℝ (Euc d) ℝ).symm 1, Function.HasTemperateGrowth.const _,
      fun x => ?_⟩
    ext m
    simp
  | succ k ih =>
    obtain ⟨P, hP, hPe⟩ := ih
    have hΛ : (fun x => mov0_dualL d (L x)).HasTemperateGrowth :=
      (mov0_dualL d).hasTemperateGrowth.comp hL
    have hbil : (fun x => (ContinuousLinearMap.smulRightL ℝ (Euc d) (mov0_M d k))
        (mov0_dualL d (L x)) (P x)).HasTemperateGrowth :=
      ContinuousLinearMap.bilinear_hasTemperateGrowth (𝕜 := ℝ) _ hΛ hP
    obtain ⟨Q, hQdef⟩ : ∃ Q : Euc d → (Euc d →L[ℝ] mov0_M d k), Q = fun x => fderiv ℝ P x +
        (ContinuousLinearMap.smulRightL ℝ (Euc d) (mov0_M d k)) (mov0_dualL d (L x)) (P x) := ⟨_, rfl⟩
    have hQ : Q.HasTemperateGrowth := by
      rw [hQdef]
      exact (mov0_tg_fderiv hP).add hbil
    set Φ := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => Euc d) ℝ).symm with hΦ
    have hΦtg : Function.HasTemperateGrowth (fun y : Euc d →L[ℝ] mov0_M d k => Φ y) :=
      ContinuousLinearEquiv.hasTemperateGrowth (E := Euc d →L[ℝ] mov0_M d k) (F := mov0_M d (k + 1))
        Φ.toContinuousLinearEquiv
    refine ⟨fun x => Φ (Q x), by exact hΦtg.comp hQ, fun x => ?_⟩
    have hPd : DifferentiableAt ℝ P x := (hP.1.differentiable (by simp)) x
    have hud : DifferentiableAt ℝ u x := (hu.differentiable (by simp)) x
    have e1 : iteratedFDeriv ℝ k u = fun y => u y • P y := funext hPe
    have e2 : iteratedFDeriv ℝ (k + 1) u x = Φ (fderiv ℝ (iteratedFDeriv ℝ k u) x) := by
      rw [iteratedFDeriv_succ_eq_comp_left]; rfl
    rw [e2, e1]
    have e3 : fderiv ℝ (fun y => u y • P y) x = u x • fderiv ℝ P x + (fderiv ℝ u x).smulRight (P x) :=
      fderiv_smul hud hPd
    have e4 : fderiv ℝ u x = u x • mov0_dualL d (L x) := by
      rw [mov0_fderiv_eq_dual, hgrad x, map_smul]
    rw [e3, e4]
    have e5 : (u x • mov0_dualL d (L x)).smulRight (P x) =
        u x • ((ContinuousLinearMap.smulRightL ℝ (Euc d) (mov0_M d k)) (mov0_dualL d (L x)) (P x)) := by
      ext v
      simp [mul_assoc]
    rw [e5]
    simp only [hQdef, map_add, map_smul, smul_add]

/-- **Ray bound.**  If `∇u = u(-a x + B')` with `‖B'‖ ≤ M` and `u ≥ 0`, then
`u(x) ≤ u(0) exp(-a‖x‖²/2 + M‖x‖)`. -/
lemma mov0_ray_bound {a M : ℝ} {B' : Euc d → Euc d} (hM : ∀ x, ‖B' x‖ ≤ M) {u : Euc d → ℝ}
    (hu : Differentiable ℝ u) (hu0 : ∀ x, 0 ≤ u x)
    (hgrad : ∀ x, gradient u x = u x • (-a • x + B' x)) (x : Euc d) :
    u x ≤ u 0 * Real.exp (-(a * ‖x‖ ^ 2 / 2) + M * ‖x‖) := by
  set h : ℝ → ℝ := fun t => u (t • x) * Real.exp (a * t ^ 2 * ‖x‖ ^ 2 / 2 - M * ‖x‖ * t) with hh
  have hderiv : ∀ t : ℝ, HasDerivAt h (Real.exp (a * t ^ 2 * ‖x‖ ^ 2 / 2 - M * ‖x‖ * t) * u (t • x) *
      (inner ℝ x (B' (t • x)) - M * ‖x‖)) t := by
    intro t
    have hl : HasDerivAt (fun t : ℝ => t • x) x t := by
      simpa using (hasDerivAt_id t).smul_const x
    have h1 : HasDerivAt (fun t : ℝ => u (t • x)) (fderiv ℝ u (t • x) x) t :=
      (hu (t • x)).hasFDerivAt.comp_hasDerivAt t hl
    have h2 : HasDerivAt (fun t : ℝ => a * t ^ 2 * ‖x‖ ^ 2 / 2 - M * ‖x‖ * t)
        (a * t * ‖x‖ ^ 2 - M * ‖x‖) t := by
      have := (((hasDerivAt_pow 2 t).const_mul a).mul_const (‖x‖ ^ 2)).div_const 2 |>.sub
        ((hasDerivAt_id t).const_mul (M * ‖x‖))
      refine this.congr_deriv ?_
      simp
      ring
    have h3 := h1.mul h2.exp
    have e : fderiv ℝ u (t • x) x = u (t • x) * (-(a * t * ‖x‖ ^ 2) + inner ℝ x (B' (t • x))) := by
      rw [mov0_fderiv_eq_dual, hgrad, map_smul, smul_apply, mov0_dualL_apply]
      rw [real_inner_comm, inner_add_right, inner_smul_right, inner_smul_right, real_inner_self_eq_norm_sq]
      simp only [smul_eq_mul]
      ring
    refine h3.congr_deriv ?_
    rw [e]
    ring
  have hanti : Antitone h := by
    refine antitone_of_deriv_nonpos (fun t => (hderiv t).differentiableAt) (fun t => ?_)
    rw [(hderiv t).deriv]
    have hin : inner ℝ x (B' (t • x)) ≤ M * ‖x‖ :=
      (real_inner_le_norm _ _).trans (by rw [mul_comm]; exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _))
    have : 0 ≤ Real.exp (a * t ^ 2 * ‖x‖ ^ 2 / 2 - M * ‖x‖ * t) * u (t • x) :=
      mul_nonneg (Real.exp_pos _).le (hu0 _)
    nlinarith
  have h10 : h 1 ≤ h 0 := hanti (by norm_num)
  have h11 : u x * Real.exp (a * 1 ^ 2 * ‖x‖ ^ 2 / 2 - M * ‖x‖ * 1) ≤ u 0 := by
    have e0 : h 0 = u 0 := by simp [hh]
    have e1 : h 1 = u x * Real.exp (a * 1 ^ 2 * ‖x‖ ^ 2 / 2 - M * ‖x‖ * 1) := by simp [hh]
    rw [← e1, ← e0]; exact h10
  have e6 : Real.exp (-(a * ‖x‖ ^ 2 / 2) + M * ‖x‖) = (Real.exp (a * 1 ^ 2 * ‖x‖ ^ 2 / 2 - M * ‖x‖ * 1))⁻¹ := by
    rw [← Real.exp_neg]; congr 1; ring
  rw [e6]
  rw [← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
  exact h11

/-- Polynomial times Gaussian-with-linear-term is Gaussian: `(1+r)^N e^{-a r²/2 + M r} ≤ N! e^{1+(M+1)²/a} e^{-a r²/4}`. -/
lemma mov0_pow_exp_bound {a M : ℝ} (ha : 0 < a) (N : ℕ) (r : ℝ) (hr : 0 ≤ r) :
    (1 + r) ^ N * Real.exp (-(a * r ^ 2 / 2) + M * r) ≤
      (N.factorial : ℝ) * Real.exp (1 + (M + 1) ^ 2 / a) * Real.exp (-(a / 4) * r ^ 2) := by
  have hfac : (0 : ℝ) < N.factorial := by exact_mod_cast Nat.factorial_pos N
  have h1 : (1 + r) ^ N ≤ N.factorial * Real.exp (1 + r) := by
    have := Real.pow_div_factorial_le_exp (1 + r) (by linarith) N
    rwa [div_le_iff₀ hfac, mul_comm] at this
  have h2 : (M + 1) * r ≤ (M + 1) ^ 2 / a + a * r ^ 2 / 4 := by
    have e : (M + 1) ^ 2 / a + a * r ^ 2 / 4 - (M + 1) * r = (a * r / 2 - (M + 1)) ^ 2 / a := by
      field_simp
      ring
    have : 0 ≤ (a * r / 2 - (M + 1)) ^ 2 / a := by positivity
    linarith
  calc (1 + r) ^ N * Real.exp (-(a * r ^ 2 / 2) + M * r)
      ≤ (N.factorial * Real.exp (1 + r)) * Real.exp (-(a * r ^ 2 / 2) + M * r) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = N.factorial * Real.exp (1 + r + (-(a * r ^ 2 / 2) + M * r)) := by rw [mul_assoc, ← Real.exp_add]
    _ ≤ N.factorial * Real.exp ((1 + (M + 1) ^ 2 / a) + (-(a / 4) * r ^ 2)) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hfac.le
        nlinarith
    _ = _ := by rw [Real.exp_add]; ring

/-- **Gaussian bound for the derivatives of `u`** with `∇u = u(-a x + B')`, `B'` bounded of temperate growth,
`u ≥ 0` smooth: `‖D^k u(x)‖ ≤ C_k exp(-(a/4)‖x‖²)`. -/
theorem mov0_gauss_deriv {a M : ℝ} (ha : 0 < a) {B' : Euc d → Euc d} (hB' : B'.HasTemperateGrowth)
    (hM : ∀ x, ‖B' x‖ ≤ M) {u : Euc d → ℝ} (hu : ContDiff ℝ ∞ u) (hu0 : ∀ x, 0 ≤ u x)
    (hgrad : ∀ x, gradient u x = u x • (-a • x + B' x)) (k : ℕ) :
    ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ k u x‖ ≤ C * Real.exp (-(a / 4) * ‖x‖ ^ 2) := by
  have hL : Function.HasTemperateGrowth (fun x : Euc d => -a • x + B' x) := by
    have h1 := ContinuousLinearMap.hasTemperateGrowth ((-a) • ContinuousLinearMap.id ℝ (Euc d))
    exact h1.add hB'
  obtain ⟨P, hP, hPe⟩ := mov0_tensor hu hL hgrad k
  obtain ⟨N, C0, hC0⟩ := hP.2 0
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  refine ⟨u 0 * |C0| * (N.factorial : ℝ) * Real.exp (1 + (M + 1) ^ 2 / a), fun x => ?_⟩
  have hP0 : ‖P x‖ ≤ |C0| * (1 + ‖x‖) ^ N := by
    have := hC0 x
    rw [norm_iteratedFDeriv_zero] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
  have hux := mov0_ray_bound hM (hu.differentiable (by simp)) hu0 hgrad x
  rw [hPe x, norm_smul, Real.norm_of_nonneg (hu0 x)]
  have hb := mov0_pow_exp_bound (M := M) ha N ‖x‖ (norm_nonneg _)
  calc u x * ‖P x‖ ≤ (u 0 * Real.exp (-(a * ‖x‖ ^ 2 / 2) + M * ‖x‖)) * (|C0| * (1 + ‖x‖) ^ N) :=
        mul_le_mul hux hP0 (norm_nonneg _) (mul_nonneg (hu0 0) (Real.exp_pos _).le)
    _ = u 0 * |C0| * ((1 + ‖x‖) ^ N * Real.exp (-(a * ‖x‖ ^ 2 / 2) + M * ‖x‖)) := by ring
    _ ≤ u 0 * |C0| * ((N.factorial : ℝ) * Real.exp (1 + (M + 1) ^ 2 / a) * Real.exp (-(a / 4) * ‖x‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hb (mul_nonneg (hu0 0) (abs_nonneg _))
    _ = _ := by ring

end HRS.MS.Mov0

end
