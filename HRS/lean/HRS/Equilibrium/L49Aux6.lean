/-
# HRS.Equilibrium.L49Aux6 — Proposition 4.9, part 6: the compensated integral on the torus

`l49_compensated` (`R:eq:compensated-integral`): for `0 < λ ≤ λ₀`, uniformly in `x`,
`|∫ H(λ g₊(x-y)) dμ(y) - (|S^{d-1}|/d) ρ(x) λ² log(1/λ)| ≤ C λ²`,
via the shift to the cube, the local normalisation `g = |w|^{-s} + r(w)` and `l49_local_abstract`.
-/
import HRS.Equilibrium.L49Aux5
import HRS.Equilibrium.LocalDivSub

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS

namespace L49

open HRS.LocalDivAux HRS.PoleCavityAux HRS.KernelAux HRS.KernelAux2

variable {d : ℕ} {s : ℝ}

set_option maxHeartbeats 1600000 in
theorem l49_compensated (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) :
    ∃ C lam0 : ℝ, 0 < lam0 ∧ lam0 ≤ 1 ∧ ∀ lam : ℝ, 0 < lam → lam ≤ lam0 → ∀ x : Torus d,
      Integrable (fun y => taylorH (lam * gPlus d s c (x - y))) (withDensityReal ρ) ∧
      |∫ y, taylorH (lam * gPlus d s c (x - y)) ∂(withDensityReal ρ) -
          sphereArea d / d * ρ x * lam ^ 2 * Real.log (1 / lam)| ≤ C * lam ^ 2 := by
  obtain ⟨hs0', hsd⟩ := hs_aux hd hcrit
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by rw [hcrit]; linarith
  have hs1 : 1 ≤ s := by rw [hcrit]; linarith
  have hds : (d : ℝ) = 2 * s := by rw [hcrit]; ring
  have hd1 : 1 ≤ d := by omega
  have hd0 : 0 < d := by omega
  have hgm := measurable_gPlus hd hs0' hsd c
  obtain ⟨r, δ₁, hδ₁, hr, hloc⟩ := periodicRiesz_local_singularity (d := d) hd hs0 hsd
  have hrc : Continuous r :=
    continuous_of_lift' (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift r) from hr).continuous
  obtain ⟨R₀, hR₀⟩ := isCompact_univ.exists_bound_of_continuousOn (f := r) hrc.continuousOn
  set R : ℝ := |R₀| + |c| with hR
  have hR0 : 0 ≤ R := by positivity
  obtain ⟨L, hL0, hLip⟩ := lip_shift (d := d) hρ.smooth
  obtain ⟨Lam, hLam0, hLam⟩ := exists_density_bound hρ
  obtain ⟨A, hA1, hA⟩ := gPlus_envelope hd hs0 hsd c
  set δ : ℝ := min (δ₁ / 2) (1 / 4) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ4 : δ ≤ 1 / 4 := min_le_right _ _
  have hδδ₁ : δ < δ₁ := by have := min_le_left (δ₁ / 2) (1 / 4); linarith
  set Γ₀ : ℝ := A * (δ / d) ^ (-s) with hΓ₀
  have hΓ0 : 0 ≤ Γ₀ := by positivity
  set lam0 : ℝ := min 1 (δ ^ s) with hlam0def
  have hlam0pos : 0 < lam0 := lt_min one_pos (Real.rpow_pos_of_pos hδ0 _)
  set Bc : ℝ := ballConst d with hBc
  set K2 : ℝ := L * (1 + R ^ 2) + Lam * (4 * R ^ 3 + R + R ^ 2 / 2) with hK2
  refine ⟨Lam * (1 + R) * Bc / s + K2 * Bc * δ + 4 * Lam * Bc / s + Lam * Γ₀ ^ 2 / 2 +
      Lam * Bc * |Real.log δ| / 2, lam0, hlam0pos, min_le_left _ _, ?_⟩
  intro lam hlam hlamle x
  have hlam1 : lam ≤ 1 := hlamle.trans (min_le_left _ _)
  have hlamδ : lam ≤ δ ^ s := hlamle.trans (min_le_right _ _)
  set rl : ℝ := lam ^ (1 / s) with hrl
  have hrl0 : 0 < rl := Real.rpow_pos_of_pos hlam _
  have hrls : rl ^ s = lam := by
    rw [hrl, ← Real.rpow_mul hlam.le, one_div, inv_mul_cancel₀ hs0.ne', Real.rpow_one]
  have hrlδ : rl ≤ δ := by
    have : rl ^ s ≤ δ ^ s := by rw [hrls]; exact hlamδ
    by_contra h
    push Not at h
    have := Real.rpow_lt_rpow hδ0.le h hs0
    linarith
  -- the data
  have hγm : Measurable fun w : Euc d => gPlus d s c (Torus.mk w) := hgm.comp Torus.continuous_mk.measurable
  have hρm := measurable_ρx hρ x
  have hγ0 : ∀ w : Euc d, 0 ≤ gPlus d s c (Torus.mk w) := fun w => hc _
  have hγu : ∀ w : Euc d, 0 < ‖w‖ → ‖w‖ ≤ δ →
      |gPlus d s c (Torus.mk w) - ‖w‖ ^ (-s)| ≤ R := by
    intro w hw0 hwδ
    have hw1 : ‖w‖ < δ₁ := lt_of_le_of_lt hwδ hδδ₁
    have := hloc w hw1 (norm_pos_iff.1 hw0)
    unfold gPlus
    rw [this]
    have e : ‖w‖ ^ (-s) + r (Torus.mk w) + c - ‖w‖ ^ (-s) = r (Torus.mk w) + c := by ring
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add ?_ le_rfl)
    have := hR₀ (Torus.mk w) trivial
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_abs_self _)
  have hρb : ∀ w : Euc d, 0 ≤ ρ (x + Torus.mk w) ∧ ρ (x + Torus.mk w) ≤ Lam :=
    fun w => ⟨hρ.density.nonneg _, hLam _⟩
  have hρ0 : 0 ≤ ρ x ∧ ρ x ≤ Lam := ⟨hρ.density.nonneg _, hLam _⟩
  have hρL : ∀ w : Euc d, ‖w‖ ≤ δ → |ρ (x + Torus.mk w) - ρ x| ≤ L * ‖w‖ :=
    fun w _ => hLip x w
  have hfar : ∀ w ∈ cube d, δ < ‖w‖ → gPlus d s c (Torus.mk w) ≤ Γ₀ := by
    intro w hw hwδ
    have hy : (w.ofLp : Fin d → ℝ) ∈ Box d := fun i => hw i
    have hw0 : w ≠ 0 := by
      intro h; rw [h, norm_zero] at hwδ; linarith
    have hy0 : (w.ofLp : Fin d → ℝ) ≠ 0 := by
      intro h; apply hw0; ext i; exact congrFun h i
    have h1 := hA _ hy hy0
    have h2 : ‖w‖ ≤ d * ‖(w.ofLp : Fin d → ℝ)‖ := by
      have := norm_toLp_le_card_mul hd0 (w.ofLp : Fin d → ℝ)
      simpa using this
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd0
    have h3 : δ / d ≤ ‖(w.ofLp : Fin d → ℝ)‖ := by
      rw [div_le_iff₀ hdpos]
      nlinarith
    have h4 : ‖(w.ofLp : Fin d → ℝ)‖ ^ (-s) ≤ (δ / d) ^ (-s) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) h3 (by linarith)
    have e : boxPt (w.ofLp : Fin d → ℝ) = Torus.mk w := rfl
    rw [e] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left h4 (by linarith))
  obtain ⟨hI, hB⟩ := l49_local_abstract hd hs1 hds hγm hρm hγ0 hγu hR0 hρb hρ0 hρL hL0 hfar hΓ0
    hδ0 hδ4 hrl0 hrlδ hlam hlam1 hrls
  -- conversion to the torus integral
  have hGm : Measurable fun y : Torus d => ρ y * taylorH (lam * gPlus d s c (x - y)) :=
    hρ.density.measurable.mul (l49_measurable_taylorH.comp
      (measurable_const.mul (hgm.comp (measurable_const.sub measurable_id))))
  have hcube : ∀ w : Euc d, ρ (x + Torus.mk w) * taylorH (lam * gPlus d s c (x - (x + Torus.mk w))) =
      ρ (x + Torus.mk w) * taylorH (lam * gPlus d s c (Torus.mk w)) := by
    intro w
    rw [sub_add_cancel_left, gPlus_neg]
  have hIc : IntegrableOn (fun w : Euc d => ρ (x + Torus.mk w) *
      taylorH (lam * gPlus d s c (x - (x + Torus.mk w)))) (cube d) :=
    hI.congr_fun (fun w _ => (hcube w).symm) measurableSet_cube
  refine ⟨?_, ?_⟩
  · refine (integrable_mu_iff hρ).2 ?_
    exact integrable_torus_of_cube hGm x hIc
  · rw [integral_withDensityReal_eq ρ hρ.density.measurable hρ.density.nonneg,
      integral_shift_cube x _ hGm]
    have e : ∫ w in cube d, ρ (x + Torus.mk w) * taylorH (lam * gPlus d s c (x - (x + Torus.mk w))) =
        ∫ w in cube d, ρ (x + Torus.mk w) * taylorH (lam * gPlus d s c (Torus.mk w)) :=
      setIntegral_congr_fun measurableSet_cube fun w _ => hcube w
    show |(∫ w in cube d, ρ (x + Torus.mk w) * taylorH (lam * gPlus d s c (x - (x + Torus.mk w)))) -
        sphereArea d / d * ρ x * lam ^ 2 * Real.log (1 / lam)| ≤ _
    rw [e]
    have hbc : ballConst d / (2 * s) = sphereArea d / d := by
      rw [l49_ballConst_eq hd1, hds]
    rw [← hbc]
    exact hB

end L49

end HRS

end
