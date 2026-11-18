import HRS.Whole.MovingDyn
import HRS.MS.Canon
import HRS.MS.MovThermAux2
import HRS.MS.MovLinAux5
import HRS.MS.MovForceAux3

/-!
# S64 (row S6.9 `mov_moving_reference`), part 1: PLAN and clause (1) (velocity and time derivative of the translated equilibrium)

Namespace `HRS.MS.MovSch`, prefix `s64_`.

## PLAN S6.9 `HRS.Whole.mov_moving_reference` (MovingDyn.lean ~:322, TeX S L4902-4921)

Statement check.  The frozen statement carries the M1/M1b hypotheses `GibbsInvariant d s q β N` (clause (2), dynamic part) and
`GibbsEntropyContraction d s q β N` (clause (4)); it does not use the S6.3 solution and does not need `IsRegularMFRd` (clause (2)
of S6.8, not used here: only S6.8 clauses (1), (3), (4), all proved: `movtr_strong_translate`, `movtr_modulatedGibbs_translate`,
`movtr_modulatedEnergy_translate`, `movtr_gibbsNormalizer_translate`).  TRUE and non-vacuous with these hypotheses, with one trap
handled: the density identity of clause (2) is FALSE if the Bochner normaliser `K = gibbsNormalizer` is `0` (non-integrable weight:
`(ofReal 0)⁻¹ = ⊤` on the left, `0⁻¹ = 0` on the right), so it needs `0 < K`, i.e. `0 < canonicalPartition` (`K = k Z_can`, `k > 0`,
`HRS.MS.Canon.cn_pointwise`); this holds for every `N ≥ 1`, `0 ≤ s < d` (`exp(-βH_N) ≤ ∏ (1+|x_i|)^{βN} e^{-βq|x_i|²/2}`).
`movPartial` is a `deriv` (junk off differentiability): clause (3) is only claimed off collisions, where the density is `C^∞`.

Proof plan.
(1) `u = q a_t` by `movtr_movU_translate` and the Euler equation `mv0_thermal_force`; `∂_tρ^t(x) = fderiv ρ₀ (x - a_t) (q a_t)` (chain rule)
`= movDiv (ρ^t • q a_t)(x)`.   [this file]
(2a) `0 < Z_can`; `movQDensity ρ₀ X = Z_can⁻¹ exp(-βH_N X)`; `movQDensity ρ^t X = movQDensity ρ₀ (X - a_t)`; `modulatedGibbs ρ^t =
(modulatedGibbs ρ₀).map(+a_t)`; density identity.
(2b), (4): `Y = X - a_t` solves the SDE from `X₀ - a₀` (S6.8(1) with `-a₀`), translate the laws, apply the hypotheses, translate back.
(3) `q^t(X) = Q(X - a_t)`, `Q = Z⁻¹ e^{-βH_N}`; stationarity `β⁻¹ ∂_{ik}Q + Q(q x_{ik} + N⁻¹∑_{j≠i}∂_k g(x_i-x_j)) = 0`;
for the translate the flux is `q a_k Q`, hence `movFP q^t = q a·∇Q = ∂_t q^t`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovSch

open HRS HRS.Whole

variable {d : ℕ}

/-- `div (f • c) = fderiv f c` for a constant vector `c`. -/
lemma s64_movDiv_smul_const {f : Euc d → ℝ} {x : Euc d} (hf : DifferentiableAt ℝ f x) (c : Euc d) :
    movDiv (fun y => f y • c) x = fderiv ℝ f x c := by
  have hconst : movDiv (fun _ : Euc d => c) x = 0 := by
    unfold movDiv
    simp
  rw [HRS.MS.MovForce.mv1_movDiv_smul hf (differentiableAt_const c), hconst, mul_zero, zero_add,
    HRS.MS.MovLin.mov2a_sum_fderiv_mul]
  rw [real_inner_comm]
  exact HRS.MS.PoisKolm.kl_inner_gradient f x c

/-- Clause (1) of `mov_moving_reference`. -/
theorem s64_ref1 {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β q : ℝ) (hβ : 0 < β)
    (hq : 0 < q) (ρ₀ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ₀) (a₀ : Euc d) :
    ∀ t : ℝ, 0 ≤ t → ∀ x : Euc d,
      movU d s q β (movTranslatedDensity q a₀ ρ₀ t) x = q • movShift q a₀ t ∧
      HasDerivAt (fun τ => movTranslatedDensity q a₀ ρ₀ τ x)
        (movDiv (fun y => movTranslatedDensity q a₀ ρ₀ t y •
          movU d s q β (movTranslatedDensity q a₀ ρ₀ t) y) x) t := by
  intro t _ x
  have hforce := HRS.MS.Mov0.mv0_thermal_force hd hs0 hsd hq hβ hρ
  have hsm := (HRS.MS.Mov0.mv0_hgauss hd hs0 hsd hq hβ hρ).1
  have hU : ∀ y, movU d s q β (movTranslatedDensity q a₀ ρ₀ t) y = q • movShift q a₀ t :=
    fun y => movtr_movU_translate s q β ρ₀ hforce (movShift q a₀ t) y
  refine ⟨hU x, ?_⟩
  have hfun : (fun y => movTranslatedDensity q a₀ ρ₀ t y • movU d s q β (movTranslatedDensity q a₀ ρ₀ t) y) =
      fun y => ρ₀ (y - movShift q a₀ t) • (q • movShift q a₀ t) := by
    funext y
    rw [hU y]
    rfl
  rw [hfun]
  have hdiff : DifferentiableAt ℝ (fun y => ρ₀ (y - movShift q a₀ t)) x :=
    ((hsm.differentiable (by simp)) _).comp x (differentiableAt_id.sub_const _)
  rw [s64_movDiv_smul_const hdiff]
  have hfd : fderiv ℝ (fun y => ρ₀ (y - movShift q a₀ t)) x = fderiv ℝ ρ₀ (x - movShift q a₀ t) := by
    have h1 : HasFDerivAt (fun y => ρ₀ (y - movShift q a₀ t)) (fderiv ℝ ρ₀ (x - movShift q a₀ t)) x := by
      have := ((hsm.differentiable (by simp)) (x - movShift q a₀ t)).hasFDerivAt.comp x
        ((hasFDerivAt_id x).sub_const (movShift q a₀ t))
      simpa [Function.comp_def] using this
    exact h1.fderiv
  rw [hfd]
  -- the time derivative
  have hs : HasDerivAt (fun τ : ℝ => x - movShift q a₀ τ) (q • movShift q a₀ t) t := by
    have h1 : HasDerivAt (fun τ : ℝ => Real.exp (-q * τ)) (Real.exp (-q * t) * (-q)) t := by
      have := (hasDerivAt_id t).const_mul (-q)
      simpa using this.exp
    have h2 := h1.smul_const a₀
    have h3 : HasDerivAt (fun τ : ℝ => x - movShift q a₀ τ) (-((Real.exp (-q * t) * -q) • a₀)) t := h2.const_sub x
    have e : -((Real.exp (-q * t) * -q) • a₀) = q • movShift q a₀ t := by
      unfold movShift
      rw [smul_smul, ← neg_smul]
      congr 1
      ring
    exact h3.congr_deriv e
  have hρd : HasFDerivAt ρ₀ (fderiv ℝ ρ₀ (x - movShift q a₀ t)) (x - movShift q a₀ t) :=
    ((hsm.differentiable (by simp)) _).hasFDerivAt
  exact hρd.comp_hasDerivAt t hs

end HRS.MS.MovSch

end
