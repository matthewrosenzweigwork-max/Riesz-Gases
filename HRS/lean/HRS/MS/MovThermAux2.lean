import HRS.MS.MovThermAux1
import HRS.Whole.MovtrAux5

/-!
# MOV-0 (part 2): Gaussian derivative bounds for `ρ` and `√ρ`, bounds on `∇ log ρ`

Namespace `HRS.MS.Mov0`; helper prefix `mov0_`, output prefix `mv0_`.  Packet MOV-0 of `docs/MOV_PLAN.md`.

Generic in `(ρ, q', B)` with `GapRef d ρ q' B` and `q' > 0` (for the thermal data `q' = β q`, `B = -β ∇(g * μ)`, see
`mv0_gapref`):
* `mv0_sqrt_gauss`: `√ρ ∈ C^∞`, `∇ log ρ = -q' x + B`, and `‖D^k √ρ x‖ ≤ C_k exp(-c‖x‖²)` with `c = q'/8`.
* `mv0_hgauss_gapref`: `ρ ∈ C^∞` and `‖D^k ρ x‖ ≤ C_k exp(-c‖x‖²)` with `c = q'/4`.
* `mv0_dlog_bounds`: `‖D^k (∇ log ρ)‖ ≤ C_k` for `k ≥ 1` and `‖∇ log ρ x‖ ≤ q'‖x‖ + M`.

Thermal instances: `mv0_hgauss` gives `hsmooth` and `hgauss` in exactly the form required by
`HRS.Whole.movtr_thermal_force` (`MovtrAux5.lean`), and `mv0_thermal_force` discharges that theorem.  The route is
the one of the plan: `u(x) ≤ u(0) exp(-a‖x‖²/2 + M‖x‖)` by integration along rays, and `D^k u = u · P_k` with `P_k` of
temperate growth by induction on tensors (no Faà di Bruno).

Statement adjustments relative to the plan sketch: the Gaussian rate `c` is explicit (`q'/8` for `√ρ`, `q'/4` for
`ρ`, uniform in `k`); `q' > 0` is a hypothesis of the generic lemmas.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff
open HRS HRS.Whole

noncomputable section

namespace HRS.MS.Mov0

variable {d : ℕ}

/-! ### Elementary consequences of `GapRef` -/

lemma mov0_B_smooth {ρ : Euc d → ℝ} {q : ℝ} {B : Euc d → Euc d} (hR : HRS.MS.Gap.GapRef d ρ q B) :
    ContDiff ℝ ∞ B := by
  rw [contDiff_infty]
  intro n
  obtain ⟨Mb, hMb⟩ := hR.cb n
  exact hMb.1

lemma mov0_B_tg {ρ : Euc d → ℝ} {q : ℝ} {B : Euc d → Euc d} (hR : HRS.MS.Gap.GapRef d ρ q B) :
    B.HasTemperateGrowth := by
  refine ⟨mov0_B_smooth hR, fun n => ?_⟩
  obtain ⟨Mb, hMb⟩ := hR.cb n
  exact ⟨0, Mb, fun x => by simpa using hMb.2 n le_rfl x⟩

lemma mov0_B_bdd {ρ : Euc d → ℝ} {q : ℝ} {B : Euc d → Euc d} (hR : HRS.MS.Gap.GapRef d ρ q B) :
    ∃ M : ℝ, ∀ x, ‖B x‖ ≤ M := by
  obtain ⟨Mb, hMb⟩ := hR.cb 0
  exact ⟨Mb, fun x => by simpa using hMb.2 0 le_rfl x⟩

lemma mov0_rho_differentiable {ρ : Euc d → ℝ} {q : ℝ} {B : Euc d → Euc d}
    (hR : HRS.MS.Gap.GapRef d ρ q B) : Differentiable ℝ ρ :=
  hR.smooth.differentiable (by simp)

/-- `∇ log ρ = -q' x + B`. -/
theorem mov0_grad_log {ρ : Euc d → ℝ} {q : ℝ} {B : Euc d → Euc d} (hR : HRS.MS.Gap.GapRef d ρ q B)
    (x : Euc d) : gradient (fun y => Real.log (ρ y)) x = -q • x + B x := by
  have hρx : ρ x ≠ 0 := (hR.pos x).ne'
  have hf : HasFDerivAt (fun y => Real.log (ρ y)) ((ρ x)⁻¹ • fderiv ℝ ρ x) x :=
    ((mov0_rho_differentiable hR) x).hasFDerivAt.log hρx
  refine ext_inner_left ℝ fun v => ?_
  rw [HRS.MS.PoisKolm.kl_inner_gradient, hf.fderiv, ContinuousLinearMap.smul_apply,
    ← HRS.MS.PoisKolm.kl_inner_gradient ρ x v, hR.grad x, inner_smul_right, smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ hρx, one_mul]

/-- `∇ √ρ = √ρ (-(q'/2) x + B/2)`. -/
theorem mov0_grad_sqrt {ρ : Euc d → ℝ} {q : ℝ} {B : Euc d → Euc d} (hR : HRS.MS.Gap.GapRef d ρ q B)
    (x : Euc d) :
    gradient (fun y => Real.sqrt (ρ y)) x = Real.sqrt (ρ x) • (-(q / 2) • x + (1 / 2 : ℝ) • B x) := by
  have hρx : ρ x ≠ 0 := (hR.pos x).ne'
  have hf : HasFDerivAt (fun y => Real.sqrt (ρ y)) ((1 / (2 * Real.sqrt (ρ x))) • fderiv ℝ ρ x) x :=
    ((mov0_rho_differentiable hR) x).hasFDerivAt.sqrt hρx
  have hs : 0 < Real.sqrt (ρ x) := Real.sqrt_pos.2 (hR.pos x)
  have hss : Real.sqrt (ρ x) * Real.sqrt (ρ x) = ρ x := Real.mul_self_sqrt (hR.pos x).le
  refine ext_inner_left ℝ fun v => ?_
  rw [HRS.MS.PoisKolm.kl_inner_gradient, hf.fderiv, ContinuousLinearMap.smul_apply,
    ← HRS.MS.PoisKolm.kl_inner_gradient ρ x v, hR.grad x]
  simp only [inner_add_right, inner_smul_right, smul_eq_mul]
  generalize Real.sqrt (ρ x) = r at hs hss ⊢
  rw [← hss]
  field_simp

/-! ### Smoothness and Gaussian bounds -/

/-- `√ρ ∈ C^∞`. -/
lemma mov0_sqrt_smooth {ρ : Euc d → ℝ} {q : ℝ} {B : Euc d → Euc d} (hR : HRS.MS.Gap.GapRef d ρ q B) :
    ContDiff ℝ ∞ (fun x => Real.sqrt (ρ x)) :=
  hR.smooth.sqrt (fun x => (hR.pos x).ne')

/-- **MOV-0, step 1c.**  Generic in `GapRef d ρ q' B`, `q' > 0`: `√ρ` is `C^∞`, `∇ log ρ = -q' x + B`, and all
derivatives of `√ρ` have a Gaussian bound (rate `c = q'/8`). -/
theorem mv0_sqrt_gauss {ρ : Euc d → ℝ} {q' : ℝ} {B : Euc d → Euc d} (hq : 0 < q')
    (hR : HRS.MS.Gap.GapRef d ρ q' B) :
    ContDiff ℝ ∞ (fun x => Real.sqrt (ρ x)) ∧
      (∀ x, gradient (fun y => Real.log (ρ y)) x = -q' • x + B x) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, ∃ C : ℝ, ∀ x,
        ‖iteratedFDeriv ℝ k (fun y => Real.sqrt (ρ y)) x‖ ≤ C * Real.exp (-c * ‖x‖ ^ 2) := by
  refine ⟨mov0_sqrt_smooth hR, mov0_grad_log hR, q' / 8, by positivity, fun k => ?_⟩
  obtain ⟨M, hM⟩ := mov0_B_bdd hR
  have hB' : (fun x => (1 / 2 : ℝ) • B x).HasTemperateGrowth :=
    (Function.HasTemperateGrowth.const (1 / 2 : ℝ)).smul (mov0_B_tg hR)
  obtain ⟨C, hC⟩ := mov0_gauss_deriv (a := q' / 2) (M := |1 / 2| * M) (by positivity) hB'
    (fun x => by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hM x) (abs_nonneg _))
    (mov0_sqrt_smooth hR) (fun x => Real.sqrt_nonneg _) (mov0_grad_sqrt hR) k
  refine ⟨C, fun x => ?_⟩
  have : -(q' / 2 / 4) = -(q' / 8) := by ring
  simpa [this] using hC x

/-- **MOV-0, step 1d (generic).**  `ρ ∈ C^∞` and all derivatives of `ρ` have a Gaussian bound (rate `c = q'/4`). -/
theorem mv0_hgauss_gapref {ρ : Euc d → ℝ} {q' : ℝ} {B : Euc d → Euc d} (hq : 0 < q')
    (hR : HRS.MS.Gap.GapRef d ρ q' B) :
    ContDiff ℝ ∞ ρ ∧ ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, ∃ C : ℝ, ∀ x,
      ‖iteratedFDeriv ℝ k ρ x‖ ≤ C * Real.exp (-c * ‖x‖ ^ 2) := by
  refine ⟨hR.smooth, q' / 4, by positivity, fun k => ?_⟩
  obtain ⟨M, hM⟩ := mov0_B_bdd hR
  obtain ⟨C, hC⟩ := mov0_gauss_deriv (a := q') (M := M) hq (mov0_B_tg hR) hM hR.smooth
    (fun x => (hR.pos x).le) hR.grad k
  exact ⟨C, hC⟩

/-- **MOV-0, step 1d (thermal).**  For a thermal equilibrium: `hsmooth` and `hgauss` of `movtr_thermal_force`
(`MovtrAux5.lean`), exactly in that form. -/
theorem mv0_hgauss (hd : 2 ≤ d) {s q β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hq : 0 < q) (hb : 0 < β)
    {ρ : Euc d → ℝ} (h : IsThermalEquilibrium d s q β ρ) :
    ContDiff ℝ ∞ ρ ∧ ∀ k : ℕ, ∃ C c : ℝ, 0 < c ∧ ∀ x,
      ‖iteratedFDeriv ℝ k ρ x‖ ≤ C * Real.exp (-c * ‖x‖ ^ 2) := by
  obtain ⟨B, -, hR, -⟩ := mv0_gapref hd hs0 hsd hq hb h
  obtain ⟨hsm, c, hc, hk⟩ := mv0_hgauss_gapref (mul_pos hb hq) hR
  exact ⟨hsm, fun k => by obtain ⟨C, hC⟩ := hk k; exact ⟨C, c, hc, hC⟩⟩

/-- Thermal instance of `mv0_sqrt_gauss`: `√ρ ∈ C^∞`, `∇ log ρ = -(βq) x + B` with `B = -β ∇(g * μ)` and the
Gaussian bounds of `D^k √ρ`. -/
theorem mv0_sqrt_gauss_thermal (hd : 2 ≤ d) {s q β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hq : 0 < q) (hb : 0 < β)
    {ρ : Euc d → ℝ} (h : IsThermalEquilibrium d s q β ρ) :
    ContDiff ℝ ∞ (fun x => Real.sqrt (ρ x)) ∧
      (∀ x, gradient (fun y => Real.log (ρ y)) x = -(β * q) • x +
        (-β) • gradient (HRS.Whole.convMeasure (rieszKernel d s) (thermalMeasure d s q β)) x) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, ∃ C : ℝ, ∀ x,
        ‖iteratedFDeriv ℝ k (fun y => Real.sqrt (ρ y)) x‖ ≤ C * Real.exp (-c * ‖x‖ ^ 2) := by
  obtain ⟨B, hB, hR, -⟩ := mv0_gapref hd hs0 hsd hq hb h
  obtain ⟨h1, h2, h3⟩ := mv0_sqrt_gauss (mul_pos hb hq) hR
  refine ⟨h1, fun x => ?_, h3⟩
  rw [h2 x, hB]

/-- Tie to `movtr_thermal_force`: the Euler equation `β⁻¹ ∇ log ρ + q x + ∇g*ρ = 0` for a thermal equilibrium, with
the smoothness and Gaussian hypotheses discharged by `mv0_hgauss`. -/
theorem mv0_thermal_force (hd : 2 ≤ d) {s q β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hq : 0 < q) (hb : 0 < β)
    {ρ : Euc d → ℝ} (h : IsThermalEquilibrium d s q β ρ) (x : Euc d) :
    β⁻¹ • gradient (fun y => Real.log (ρ y)) x + q • x + convGradConvW (rieszKernelGrad d s) ρ x = 0 := by
  obtain ⟨hsm, hg⟩ := mv0_hgauss hd hs0 hsd hq hb h
  exact movtr_thermal_force hd hs0 hsd hb h hsm hg x

/-! ### Bounds on `∇ log ρ` -/

/-- `‖D^{j+1} l‖ ≤ ‖l‖` for a continuous linear map `l` (all higher derivatives vanish). -/
lemma mov0_clm_iter {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (l : E →L[ℝ] F) (j : ℕ) (x : E) : ‖iteratedFDeriv ℝ (j + 1) l x‖ ≤ ‖l‖ := by
  rw [← norm_iteratedFDeriv_fderiv]
  have hl : fderiv ℝ (fun y => l y) = fun _ => l := by
    ext1 v
    simp only [ContinuousLinearMap.fderiv]
  rw [hl]
  rcases j with _ | j
  · simp
  · rw [iteratedFDeriv_const_of_ne (by omega)]
    simp

/-- **MOV-0, step 1e.**  Generic in `GapRef d ρ q' B`, `q' ≥ 0`: all derivatives of order `k ≥ 1` of `∇ log ρ` are
bounded, and `∇ log ρ` has linear growth `q'‖x‖ + M`. -/
theorem mv0_dlog_bounds {ρ : Euc d → ℝ} {q' : ℝ} {B : Euc d → Euc d} (hq : 0 ≤ q')
    (hR : HRS.MS.Gap.GapRef d ρ q' B) :
    (∀ k : ℕ, 1 ≤ k → ∃ C : ℝ, ∀ x,
      ‖iteratedFDeriv ℝ k (fun y => gradient (fun z => Real.log (ρ z)) y) x‖ ≤ C) ∧
    ∃ M : ℝ, ∀ x, ‖gradient (fun y => Real.log (ρ y)) x‖ ≤ q' * ‖x‖ + M := by
  have hfun : (fun y => gradient (fun z => Real.log (ρ z)) y) =
      (fun y => ((-q') • ContinuousLinearMap.id ℝ (Euc d)) y) + B := by
    funext y
    rw [mov0_grad_log hR y]
    simp
  constructor
  · intro k hk
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    obtain ⟨Mb, hMb⟩ := hR.cb (j + 1)
    refine ⟨‖(-q') • ContinuousLinearMap.id ℝ (Euc d)‖ + Mb, fun x => ?_⟩
    rw [hfun, iteratedFDeriv_add_apply
      (((-q') • ContinuousLinearMap.id ℝ (Euc d)).contDiff.contDiffAt) hMb.1.contDiffAt]
    refine (norm_add_le _ _).trans (add_le_add (mov0_clm_iter _ j x) (hMb.2 (j + 1) le_rfl x))
  · obtain ⟨M, hM⟩ := mov0_B_bdd hR
    refine ⟨M, fun x => ?_⟩
    rw [mov0_grad_log hR x]
    refine (norm_add_le _ _).trans (add_le_add ?_ (hM x))
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hq]

end HRS.MS.Mov0

end
