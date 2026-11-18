/-
# HRS.Equilibrium.Q84dAuxV — packet Q84d: Gibbs-weighted bounds for `∇g`, integrability of `w`
-/
import HRS.Equilibrium.Q84dAuxU

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.Q84d

variable {d : ℕ} {s : ℝ} {N : ℕ}

theorem q84d_measurable_eucDist_prod (d : ℕ) :
    Measurable (fun p : Torus d × Torus d => Torus.eucDist p.1 p.2) := by
  unfold Torus.eucDist
  refine Real.continuous_sqrt.measurable.comp (Finset.measurable_sum _ fun i _ => ?_)
  refine Measurable.pow_const ?_ 2
  exact (((measurable_pi_apply i).comp measurable_fst).sub
    ((measurable_pi_apply i).comp measurable_snd)).norm

theorem q84d_exists_grad_bound {V : Torus d → ℝ} (hV : Torus.IsSmooth V) :
    ∃ G : ℝ, ∀ x k, |(Torus.grad V x) k| ≤ G := by
  have h1 : ContDiff ℝ 1 (Torus.lift V) :=
    (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift V) from hV).of_le (by norm_cast)
  obtain ⟨G, hG⟩ := Torus.bddAbove_norm_iteratedFDeriv_lift 1 V h1
  refine ⟨G, fun x k => ?_⟩
  have h2 : ‖Torus.grad V x‖ = ‖iteratedFDeriv ℝ 1 (Torus.lift V) (Torus.rep x)‖ := by
    rw [norm_iteratedFDeriv_one]
    unfold Torus.grad gradient
    exact LinearIsometryEquiv.norm_map _ _
  exact (q84d_comp_le_norm _ k).trans (by rw [h2]; exact hG ⟨Torus.rep x, rfl⟩)

theorem q84d_rTrunc_pow_le_w_sq (hs1 : 1 ≤ s) {x y : Torus d} (hxy : x ≠ y) :
    rTrunc x y ^ (-s - 1) ≤ wEnv s x y ^ 2 := by
  have hr := PairCorrAux.rTrunc_pos hxy
  have hr1 := PairCorrAux.rTrunc_le_one x y
  have h1 : rTrunc x y ^ (-s - 1) ≤ rTrunc x y ^ (-s + -s) :=
    Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)
  rw [Real.rpow_add hr] at h1
  have h2 : 0 ≤ rTrunc x y ^ (-s) := Real.rpow_nonneg hr.le _
  unfold wEnv
  nlinarith

theorem q84d_gradg_le_w_sq (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ x y : Torus d, x ≠ y →
      ‖periodicRieszGrad d s (x - y)‖ ≤ Cg * wEnv s x y ^ 2 := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs1 : 1 ≤ s := by rw [hcrit]; linarith
  have hs0 : 0 ≤ s := by linarith
  have hsd : s < d := by rw [hcrit]; linarith
  obtain ⟨Cg, hCg0, hCg⟩ := Q84a.q84a_gg_bound hd hs0 hsd
  refine ⟨2 * Cg, by positivity, fun x y hxy => ?_⟩
  have h1 := Q84a.q84a_Gb_bound hCg0 (by linarith) hCg hxy
  have h2 := q84d_rTrunc_pow_le_w_sq hs1 hxy
  calc ‖periodicRieszGrad d s (x - y)‖ ≤ 2 * Cg * rTrunc x y ^ (-s - 1) := h1
    _ ≤ 2 * Cg * wEnv s x y ^ 2 := mul_le_mul_of_nonneg_left h2 (by positivity)

section Weighted

variable (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2)
include hd hcrit

theorem q84d_q_mul_gradg_le {V : Torus d → ℝ} (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β)
    (hN : 1 ≤ N) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (X : Config d N) (i j : Fin N), i ≠ j → X i ≠ X j →
      qd d s V β X * ‖periodicRieszGrad d s (X i - X j)‖ ≤ M := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨Q, hQ0, hQ⟩ := q84d_q_one_pair hd hcrit hV hβ hN
  obtain ⟨C, hC0, hC⟩ := q84d_w_exp_bound hd hcrit (κ := β / N) (div_pos hβ hNp)
  obtain ⟨Cg, hCg0, hCg⟩ := q84d_gradg_le_w_sq hd hcrit
  refine ⟨Q * (Cg * C), by positivity, fun X i j hij hXij => ?_⟩
  have h1 := hQ X i j hij
  have h2 := (hC (X i) (X j)).2
  have h3 := hCg (X i) (X j) hXij
  have h0 : 0 ≤ ‖periodicRieszGrad d s (X i - X j)‖ := norm_nonneg _
  unfold qd
  calc Real.exp (-β * canonicalHamiltonian (periodicRiesz d s) V X) *
        ‖periodicRieszGrad d s (X i - X j)‖
      ≤ (Q * Real.exp (-(β / N) * periodicRiesz d s (X i - X j))) *
          (Cg * wEnv s (X i) (X j) ^ 2) :=
        mul_le_mul h1 h3 h0 (by positivity)
    _ = Q * Cg * (wEnv s (X i) (X j) ^ 2 * Real.exp (-(β / N) * periodicRiesz d s (X i - X j))) := by ring
    _ ≤ Q * Cg * C := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = Q * (Cg * C) := by ring

theorem q84d_integrable_wEnv_prod :
    Integrable (fun p : Torus d × Torus d => wEnv s p.1 p.2) volume := by
  obtain ⟨c, hc0, hc⟩ := q84d_integral_wEnv_le hd hcrit (s := s)
  have hm : Measurable (fun p : Torus d × Torus d => wEnv s p.1 p.2) := by
    unfold wEnv rTrunc
    exact measurable_const.add ((measurable_const.min (q84d_measurable_eucDist_prod d)).pow_const _)
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  have h0 : 0 ≤ᵐ[(volume : Measure (Torus d × Torus d))] (fun p : Torus d × Torus d => wEnv s p.1 p.2) :=
    Filter.Eventually.of_forall (fun p => zero_le_one.trans (PairCorrAux.one_le_wEnv s p.1 p.2))
  rw [hasFiniteIntegral_iff_ofReal h0]
  have hm' : Measurable (fun p : Torus d × Torus d => ENNReal.ofReal (wEnv s p.1 p.2)) :=
    ENNReal.measurable_ofReal.comp hm
  rw [Measure.volume_eq_prod, lintegral_prod _ hm'.aemeasurable]
  calc ∫⁻ x, ∫⁻ y, ENNReal.ofReal (wEnv s x y) ≤ ∫⁻ _x : Torus d, ENNReal.ofReal
          (PairCorrAux.cdR d * ((1 / d + 1 / s) * 1 ^ s) + 2) :=
        lintegral_mono fun x => PairCorrAux.radial_B0 hd hcrit x
    _ = ENNReal.ofReal (PairCorrAux.cdR d * ((1 / d + 1 / s) * 1 ^ s) + 2) := by simp
    _ < ⊤ := ENNReal.ofReal_lt_top

theorem q84d_integrable_w_pair {i j : Fin N} (hij : i ≠ j) :
    Integrable (fun X : Config d N => wEnv s (X i) (X j)) volume := by
  have := integrable_pair_comp (volume : Measure (Torus d)) hij
    (H := fun p : Torus d × Torus d => wEnv s p.1 p.2) (by
      rw [← Measure.volume_eq_prod]; exact q84d_integrable_wEnv_prod hd hcrit)
  exact this

end Weighted

end HRS.Q84d

end
