import HRS.Sections.Sec7Fields
import HRS.PDE.MeanFieldLinearResponse
import HRS.PDE.MeanFieldPairSeries

/-!
# Packet L2C-1, helper 1: the quadratic form of `A⁻¹`, and a Grönwall lemma

Abstract facts used for the `A_β⁻¹`-Lyapunov functional `F(v) = ⟨y, R y⟩_{L²(μ_β)}` (`R = A⁻¹`,
`A = I + βKP` on `L²(μ_β)`, `HRS.PDE.MFLinear.exists_inverse`):

* `l2c1_form_bounds`: `‖y‖² ≤ κ₁ ⟨y, R y⟩` and `⟨y, R y⟩ ≤ κ₂ ‖y‖²` (the form is equivalent to the
  `L²(μ_β)` norm, because `A` is bounded and coercive);
* `l2c1_gronwall`: a differential inequality `F' ≤ -a F` on `(0,∞)` with `F` continuous on `[0,∞)`
  gives `F(τ) ≤ e^{-aτ} F(0)`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.L2C1

open HRS HRS.PDE HRS.PDE.MFAdjoint HRS.PDE.MFLinear

variable {d : ℕ}

/-- The quadratic form of `R = A⁻¹` is equivalent to the squared `L²(μ)` norm. -/
theorem l2c1_form_bounds (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    {ρ : Torus d → ℝ} {Λ : ℝ} (H : KS (periodicRiesz d s) ρ Λ) (hρc : Continuous ρ)
    (β : ℝ) (hβ : 0 ≤ β)
    (R : Lp ℝ 2 (withDensityReal ρ) →L[ℝ] Lp ℝ 2 (withDensityReal ρ))
    (hAR : ∀ y, ALp H β (R y) = y) :
    ∃ κ₁ κ₂ : ℝ, 0 < κ₁ ∧ 0 < κ₂ ∧ ∀ y : Lp ℝ 2 (withDensityReal ρ),
      ‖y‖ ^ 2 ≤ κ₁ * inner ℝ y (R y) ∧ inner ℝ y (R y) ≤ κ₂ * ‖y‖ ^ 2 := by
  refine ⟨‖(ALp H β)‖ ^ 2 + 1, ‖R‖ + 1, by positivity, by positivity, fun y => ?_⟩
  have hco := ALp_coercive hd s hs0 hsd H hρc β hβ (R y)
  rw [hAR y] at hco
  have hu2 : ‖R y‖ * ‖R y‖ ≤ inner ℝ y (R y) := hco
  have hy : ‖y‖ ≤ ‖(ALp H β)‖ * ‖R y‖ := by
    have := (ALp H β).le_opNorm (R y)
    rwa [hAR y] at this
  have hnn : 0 ≤ inner ℝ y (R y) := (mul_self_nonneg _).trans hu2
  constructor
  · calc ‖y‖ ^ 2 ≤ (‖(ALp H β)‖ * ‖R y‖) ^ 2 := by gcongr
      _ = ‖(ALp H β)‖ ^ 2 * (‖R y‖ * ‖R y‖) := by ring
      _ ≤ ‖(ALp H β)‖ ^ 2 * inner ℝ y (R y) :=
          mul_le_mul_of_nonneg_left hu2 (sq_nonneg _)
      _ ≤ (‖(ALp H β)‖ ^ 2 + 1) * inner ℝ y (R y) := by nlinarith
  · calc inner ℝ y (R y) ≤ ‖y‖ * ‖R y‖ := real_inner_le_norm _ _
      _ ≤ ‖y‖ * (‖R‖ * ‖y‖) := mul_le_mul_of_nonneg_left (R.le_opNorm y) (norm_nonneg _)
      _ = ‖R‖ * ‖y‖ ^ 2 := by ring
      _ ≤ (‖R‖ + 1) * ‖y‖ ^ 2 := by nlinarith [sq_nonneg ‖y‖]

/-- Grönwall: `F` continuous on `[0,∞)`, `F' ≤ -a F` on `(0,∞)` gives `F τ ≤ e^{-aτ} F 0`. -/
theorem l2c1_gronwall {F f : ℝ → ℝ} {a : ℝ} (hFc : ContinuousOn F (Set.Ici 0))
    (hder : ∀ v, 0 < v → HasDerivAt F (f v) v) (hle : ∀ v, 0 < v → f v ≤ -a * F v)
    {τ : ℝ} (hτ : 0 ≤ τ) : F τ ≤ Real.exp (-a * τ) * F 0 := by
  set G : ℝ → ℝ := fun v => Real.exp (a * v) * F v with hG
  have hGder : ∀ v, 0 < v → HasDerivAt G (Real.exp (a * v) * (a * F v + f v)) v := by
    intro v hv
    have h1 : HasDerivAt (fun v => Real.exp (a * v)) (Real.exp (a * v) * a) v := by
      simpa using ((hasDerivAt_id v).const_mul a).exp
    have := h1.mul (hder v hv)
    refine this.congr_deriv ?_
    ring
  have hGc : ContinuousOn G (Set.Ici 0) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul hFc
  have hanti : AntitoneOn G (Set.Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0) hGc ?_ ?_
    · intro v hv
      rw [interior_Ici] at hv
      exact (hGder v hv).differentiableAt.differentiableWithinAt
    · intro v hv
      rw [interior_Ici] at hv
      rw [(hGder v hv).deriv]
      refine mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le ?_
      have := hle v hv
      linarith
  have h1 : G τ ≤ G 0 := hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hτ) hτ
  simp only [hG, mul_zero, Real.exp_zero, one_mul] at h1
  have h5 : F τ = Real.exp (-a * τ) * (Real.exp (a * τ) * F τ) := by
    rw [← mul_assoc, ← Real.exp_add]; simp
  rw [h5]
  exact mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le

end HRS.MC.L2C1
