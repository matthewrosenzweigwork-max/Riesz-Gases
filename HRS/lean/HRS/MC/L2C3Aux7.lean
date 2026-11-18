import HRS.MC.L2C3Aux6

/-!
# Packet L2C-3, helper 7: scalar lemmas and the weighted energy `∫ρ_β|∇F|²`

* `l2c3_pw1`, `l2c3_pw3`: the pointwise absorption (AM-GM) in the Lyapunov differential inequality;
* `l2c3_int_exp_le`, `l2c3_amgm`, `l2c3_eqGen_zero`: small facts;
* `l2c3_E1`: the weighted gradient energy `∫ρ_β|∇F(t-τ)|²` and its continuity.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Sec7 HRS.PDE HRS.PDE.MFAdjoint HRS.PDE.MFLinear

namespace HRS.MC.L2C3

variable {d : ℕ}

theorem l2c3_eqGen_zero (s : ℝ) (ρ : Torus d → ℝ) (ν : ℝ) :
    equilibriumGen d s ρ ν (fun _ => 0) = fun _ => 0 := by
  funext x
  have h : ∀ y, Torus.grad (fun _ : Torus d => (0 : ℝ)) y = 0 := by
    intro y
    simp [Torus.grad, Torus.lift, Function.comp_def, gradient]
  have hl : Lop ρ (fun _ : Torus d => (0 : ℝ)) = fun _ => 0 := by
    funext y
    simp [Lop, h, Torus.div, Torus.lift, Function.comp_def]
  simp [equilibriumGen, hl, Kop, projMean, pair]

theorem l2c3_int_exp_le {τ b : ℝ} (hτ : 0 ≤ τ) (hb : 0 < b) :
    ∫ σ in (0 : ℝ)..τ, Real.exp (-b * σ) ≤ 1 / b := by
  have h : ∀ σ ∈ Set.uIcc (0 : ℝ) τ,
      HasDerivAt (fun σ => -(1 / b) * Real.exp (-b * σ)) (Real.exp (-b * σ)) σ := by
    intro σ _
    have h1 : HasDerivAt (fun σ : ℝ => Real.exp (-b * σ)) (Real.exp (-b * σ) * (-b)) σ := by
      simpa using ((hasDerivAt_id σ).const_mul (-b)).exp
    refine (h1.const_mul (-(1 / b))).congr_deriv ?_
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _)]
  simp only [mul_zero, Real.exp_zero]
  have : 0 ≤ Real.exp (-b * τ) := (Real.exp_pos _).le
  have : 0 ≤ 1 / b := by positivity
  nlinarith [mul_nonneg this (Real.exp_pos (-b * τ)).le]

theorem l2c3_amgm {ε : ℝ} (hε : 0 < ε) (u v : ℝ) : 2 * (u * v) ≤ ε * u ^ 2 + v ^ 2 / ε := by
  rw [← sub_nonneg]
  have : ε * u ^ 2 + v ^ 2 / ε - 2 * (u * v) = (ε * u - v) ^ 2 / ε := by
    field_simp
    ring
  rw [this]
  positivity

/-- Pointwise absorption for the decay of `Fv` (`S = 0`). -/
theorem l2c3_pw1 {ν c0 κ1 Cm e N v E Fv f' : ℝ} (hν : 0 < ν) (hc0 : 0 < c0) (hκ1 : 0 < κ1)
    (hCm : 0 ≤ Cm) (he : 0 ≤ e)
    (hf : f' ≤ -2 * ν * E + 2 * Cm * e * Real.sqrt N * v) (hNE : c0 * N ≤ E)
    (hvF : v ^ 2 ≤ κ1 * Fv) (hN : 0 ≤ N) :
    f' ≤ -ν * E + Cm ^ 2 * κ1 / (ν * c0) * e ^ 2 * Fv := by
  have hε : 0 < ν * c0 := mul_pos hν hc0
  have h1 := l2c3_amgm hε (Real.sqrt N) (Cm * e * v)
  rw [Real.sq_sqrt hN] at h1
  have h2 : (Cm * e * v) ^ 2 / (ν * c0) ≤ Cm ^ 2 * κ1 / (ν * c0) * e ^ 2 * Fv := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hε]
    have : (Cm * e * v) ^ 2 = Cm ^ 2 * e ^ 2 * v ^ 2 := by ring
    rw [this]
    have h0 : 0 ≤ Cm ^ 2 * e ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hvF h0]
  have h3 : ν * c0 * N ≤ ν * E := by nlinarith
  have h4 : 2 * Cm * e * Real.sqrt N * v = 2 * (Real.sqrt N * (Cm * e * v)) := by ring
  rw [h4] at hf
  nlinarith

/-- Pointwise absorption for the difference path (the perturbation is absorbed by the Poincaré inequality). -/
theorem l2c3_pw3 {ν cP Cm e N v E f' : ℝ} (hν : 0 < ν) (hcP : 0 < cP) (hCm : 0 ≤ Cm)
    (hf : f' ≤ -2 * ν * E + 2 * Cm * e * Real.sqrt N * v) (hvE : cP * v ^ 2 ≤ E) (hN : 0 ≤ N) :
    f' ≤ -ν * E + Cm ^ 2 / (ν * cP) * e ^ 2 * N := by
  have hε : 0 < ν * cP := mul_pos hν hcP
  have h1 := l2c3_amgm hε v (Cm * e * Real.sqrt N)
  have h2 : (Cm * e * Real.sqrt N) ^ 2 / (ν * cP) = Cm ^ 2 / (ν * cP) * e ^ 2 * N := by
    have : (Cm * e * Real.sqrt N) ^ 2 = Cm ^ 2 * e ^ 2 * N := by
      rw [mul_pow, Real.sq_sqrt hN]; ring
    rw [this]; ring
  have h3 : ν * cP * v ^ 2 ≤ ν * E := by nlinarith
  have h4 : 2 * Cm * e * Real.sqrt N * v = 2 * (v * (Cm * e * Real.sqrt N)) := by ring
  rw [h4] at hf
  nlinarith

/-- The weighted gradient energy `∫ρ_β |∇F(t-τ)|²`. -/
def l2c3_E1 (R : Regime d) (t : ℝ) (F : ℝ → Torus d → ℝ) (τ : ℝ) : ℝ :=
  ∫ x, R.ρβ x * ‖Torus.grad (F (t - τ)) x‖ ^ 2

/-- Continuity of `r ↦ ∫ w |∇F r|²` on `[0,t]` for a classical solution and a continuous weight. -/
theorem l2c3_energy_cont {D : DynData d} {μ : ℝ → Torus d → ℝ} {t : ℝ} {φ : Torus d → ℝ}
    {F : ℝ → Torus d → ℝ} (hF : IsClassicalAdjointSolution D μ t φ F) {w : Torus d → ℝ}
    (hw : Continuous w) :
    ContinuousOn (fun r => ∫ x, w x * ‖Torus.grad (F r) x‖ ^ 2) (Set.Icc 0 t) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have key := continuous_parametric_integral_of_continuous (μ := (volume : Measure (Torus d)))
    (f := fun (r : Set.Icc (0 : ℝ) t) (x : Torus d) => w x * ‖Torus.grad (F r.1) x‖ ^ 2) (by
      have hg : Continuous fun p : Set.Icc (0 : ℝ) t × Torus d => ‖Torus.grad (F p.1) p.2‖ ^ 2 := by
        simp_rw [MFApriori.norm_grad_sq]
        exact continuous_finsetSum _ fun i _ => (continuous_partialDeriv_prod hF i).pow 2
      exact (hw.comp continuous_snd).mul hg) isCompact_univ
  simp only [MeasureTheory.Measure.restrict_univ] at key
  exact key

end HRS.MC.L2C3
