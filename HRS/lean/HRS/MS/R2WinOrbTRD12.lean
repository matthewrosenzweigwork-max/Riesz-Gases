import HRS.MS.R2WinOrbTRD11

/-!
# S10.3 packet [C], part 12: time calculus for the density and the nonlocal term

Prefix `s103c_`, namespace `HRS.MS.R2WinOrbNL`.

* `s103c_rho_ftc`: if `τ ↦ ρ'_τ(y)` is continuous on `[0,∞)` and `ρ'` is the right derivative of `ρ`, then `ρ_l(y) - ρ_e(y) = ∫_e^l ρ'_σ(y) dσ`.
* `s103c_avg_u2dec`: the weighted average of a family with weighted jets has weighted jets (iterated differences, the weight `(1+‖y‖)⁻ᴸ`).
* `s103c_Q_smul`, `s103c_nQ_eq`: homogeneity of `s103bQ` in the density, and `s103nQ = s103bQ`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.R2WinOrbNL

open HRS HRS.Whole HRS.MS.Wad HRS.MS.Ul HRS.MS.Who HRS.MS.BreakdownS67 HRS.MS.MovLin HRS.MS.R2WinOrb

variable {d : ℕ}

theorem s103c_rho_ftc {ρ ρ' : ℝ → Euc d → ℝ}
    (hder : ∀ t, 0 ≤ t → ∀ x, HasDerivWithinAt (fun τ => ρ τ x) (ρ' t x) (Set.Ici t) t)
    (hcont : ∀ x, ContinuousOn (fun τ => ρ τ x) (Set.Ici 0))
    (hρ'c : ∀ x, ContinuousOn (fun τ => ρ' τ x) (Set.Ici 0)) {e l : ℝ} (he : 0 ≤ e) (hel : e ≤ l) (y : Euc d) :
    ρ l y - ρ e y = ∫ σ in e..l, ρ' σ y := by
  have hsub : ∀ b, e ≤ b → Set.Icc e b ⊆ Set.Ici (0 : ℝ) := fun b _ σ hσ => he.trans hσ.1
  have hint : ∀ b, e ≤ b → IntervalIntegrable (fun σ => ρ' σ y) volume e b := fun b hb =>
    ((hρ'c y).mono (hsub b hb)).intervalIntegrable_of_Icc hb
  have hintl := hint l hel
  set g : ℝ → ℝ := fun s => ρ s y - ∫ σ in e..s, ρ' σ y with hg
  have hgc : ContinuousOn g (Set.Icc e l) := by
    refine ContinuousOn.sub ((hcont y).mono (hsub l hel)) ?_
    have hIntOn : MeasureTheory.IntegrableOn (fun σ => ρ' σ y) (Set.uIcc e l) := by
      rw [Set.uIcc_of_le hel]; exact ((hρ'c y).mono (hsub l hel)).integrableOn_Icc
    have := intervalIntegral.continuousOn_primitive_interval hIntOn
    rwa [Set.uIcc_of_le hel] at this
  have hgd : ∀ s ∈ Set.Ico e l, HasDerivWithinAt g 0 (Set.Ici s) s := by
    intro s hs
    have hs0 : 0 ≤ s := he.trans hs.1
    have h1 := hder s hs0 y
    have hcs : ContinuousOn (fun σ => ρ' σ y) (Set.Ici s) := (hρ'c y).mono (Set.Ici_subset_Ici.2 hs0)
    have h2 := intervalIntegral.integral_hasDerivWithinAt_right (a := e) (b := s) (s := Set.Ici s) (t := Set.Ioi s)
      (f := fun σ => ρ' σ y) (hint s hs.1)
      ((hcs.mono Set.Ioi_subset_Ici_self).stronglyMeasurableAtFilter_nhdsWithin measurableSet_Ioi s)
      ((hcs s Set.self_mem_Ici).mono Set.Ioi_subset_Ici_self)
    have h3 := h1.sub h2
    rw [sub_self] at h3
    exact h3
  have := constant_of_has_deriv_right_zero hgc hgd l ⟨hel, le_rfl⟩
  simp only [hg, intervalIntegral.integral_same, sub_zero] at this
  linarith

theorem s103c_avg_u2dec {K L : ℕ} {B e l : ℝ} (hel : e ≤ l) (hB : 0 ≤ B) {g : ℝ → Euc d → ℝ}
    (hint : ∀ y, IntervalIntegrable (fun σ => g σ y) volume e l)
    (hg : ∀ σ ∈ Set.Icc e l, U2Dec K (L : ℝ) B (g σ))
    {G : Euc d → ℝ} (hG : ContDiff ℝ (K : WithTop ℕ∞) G) (hGeq : ∀ y, G y = ∫ σ in e..l, g σ y) :
    U2Dec K (L : ℝ) (((max 1 (d : ℝ)) ^ K * ((5 / 4 : ℝ) ^ L) ^ K) * B * (l - e)) G := by
  refine ⟨hG, fun j hj x => ?_⟩
  have hc1 : (1 : ℝ) ≤ (5 / 4 : ℝ) ^ L := one_le_pow₀ (by norm_num)
  have hwL' : ∀ y : Euc d, u2Wt (L : ℝ) y = ((1 + ‖y‖)⁻¹) ^ L := by
    intro y
    unfold u2Wt
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, inv_pow]
  rw [hwL' x]
  have hGe : G = fun y => ∫ σ in e..l, g σ y := funext hGeq
  have hw0 : 0 ≤ ((1 + ‖x‖)⁻¹) ^ L := by positivity
  have hba := sub_nonneg.2 hel
  have hBnn : 0 ≤ B * ((5 / 4 : ℝ) ^ L) ^ j * ((1 + ‖x‖)⁻¹) ^ L * (l - e) := by positivity
  have hGj : ContDiff ℝ (j : WithTop ℕ∞) G := hG.of_le (by exact_mod_cast hj)
  have hmain : ‖iteratedFDeriv ℝ j G x‖ ≤
      (d : ℝ) ^ j * (B * ((5 / 4 : ℝ) ^ L) ^ j * ((1 + ‖x‖)⁻¹) ^ L * (l - e)) := by
    refine s103c_iter_le_of_dpF hGj hBnn x fun h hh hh0 idx => ?_
    obtain ⟨hn, hsum, hprod⟩ := s103c_steps_small hh hh0 idx
    set m : Fin j → Euc d := fun l => h • (EuclideanSpace.single (idx l) (1 : ℝ) : Euc d) with hm
    obtain ⟨-, hi2⟩ := s103b_dpF_integral (r := e) (t := l) hint j m
    rw [hGe, hi2 x]
    have hb : ∀ σ ∈ Set.uIoc e l, ‖s8f_dpF j m (g σ) x‖ ≤
        B * ((5 / 4 : ℝ) ^ L) ^ j * h ^ j * ((1 + ‖x‖)⁻¹) ^ L := by
      intro σ hσ
      have hσ' : σ ∈ Set.Icc e l := by
        rw [Set.uIoc_of_le hel] at hσ; exact ⟨hσ.1.le, hσ.2⟩
      have h0 := hg σ hσ'
      have := s103c_dpF_bound L hB (h0.1.of_le (by exact_mod_cast hj)) (fun i hi y => by
        have := h0.2 i (hi.trans hj) y
        rwa [hwL' y] at this) m hsum x
      rw [Real.norm_eq_abs]
      rw [hprod] at this
      exact this.trans (le_of_eq (by ring))
    have := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [Real.norm_eq_abs] at this
    refine this.trans (le_of_eq ?_)
    rw [abs_of_nonneg hba]; ring
  refine hmain.trans ?_
  have hdi : (d : ℝ) ^ j ≤ (max 1 (d : ℝ)) ^ K :=
    (pow_le_pow_left₀ (Nat.cast_nonneg d) (le_max_right _ _) j).trans
      (pow_le_pow_right₀ (le_max_left _ _) hj)
  have hcj : ((5 / 4 : ℝ) ^ L) ^ j ≤ ((5 / 4 : ℝ) ^ L) ^ K := pow_le_pow_right₀ hc1 hj
  calc (d : ℝ) ^ j * (B * ((5 / 4 : ℝ) ^ L) ^ j * ((1 + ‖x‖)⁻¹) ^ L * (l - e))
      ≤ (max 1 (d : ℝ)) ^ K * (B * ((5 / 4 : ℝ) ^ L) ^ K * ((1 + ‖x‖)⁻¹) ^ L * (l - e)) := by
        gcongr
    _ = _ := by ring

theorem s103c_Q_smul {s : ℝ} (c : ℝ) (h g : Euc d → ℝ) (x : Euc d) :
    s103bQ d s (fun y => c * h y) g x = c * s103bQ d s h g x := by
  unfold s103bQ
  simp only [s103c_force_smul, PiLp.smul_apply, smul_eq_mul]
  have e : ∀ j : Fin d, (fun y => c * h y * fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ))) =
      fun y => c * (h y * fderiv ℝ g y (EuclideanSpace.single j (1 : ℝ))) := fun j => by funext y; ring
  simp only [e, s103c_force_smul, PiLp.smul_apply, smul_eq_mul]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem s103c_nQ_eq {s : ℝ} (h g : Euc d → ℝ) (x : Euc d) : s103nQ d s h g x = s103bQ d s h g x := by
  unfold s103nQ s103bQ
  ring

end HRS.MS.R2WinOrbNL

end
