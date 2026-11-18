import HRS.ME.UnifP4A
import HRS.ME.UnifP3B
import HRS.ME.UnifP2A
import HRS.ME.UnifP2B
import HRS.PDE.EnergyR2Fn
import HRS.Equilibrium.L49Aux15

/-!
# Uniform Lemma 4.7, Proposition 4.8, Proposition 4.9 inputs (packet P6), part A

Basics.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.ME.Unif

open HRS HRS.External HRS.PoleCavityAux HRS.MarginalAux HRS.ProdTransfer

variable {d : ℕ} {s : ℝ}

/-- The family of densities over which the constants of Lemma 4.7, Propositions 4.8 and 4.9 are uniform:
smooth probability densities with `c₀ ≤ ρ ≤ Λ` and `cbNorm 1 ρ ≤ Λ` (Lipschitz bound). -/
structure UFam (d : ℕ) (c₀ Λ : ℝ) (ρ : Torus d → ℝ) : Prop where
  smooth : SmoothPosDensity ρ
  low : ∀ x, c₀ ≤ ρ x
  up : ∀ x, ρ x ≤ Λ
  lip : Torus.cbNorm 1 ρ ≤ Λ

/-- `lip_shift` with the explicit constant `cbNorm 1 f`. -/
theorem lip_shift_cb {f : Torus d → ℝ} (hf : Torus.IsSmooth f) :
    ∀ (x : Torus d) (w : Euc d), |f (x + Torus.mk w) - f x| ≤ Torus.cbNorm 1 f * ‖w‖ := by
  have hCk := HRS.LocalDivAux.isCk_one_of_smooth hf
  have hL := HRS.PDE.R2Aux.lipschitzWith_lift_of_bound
    (HRS.PDE.R2Aux.differentiable_lift_of_isCk hCk) _ (HRS.PDE.R2Aux.norm_fderiv_le_cbNorm hCk)
  intro x w
  have := hL.dist_le_mul (Torus.rep x + w) (Torus.rep x)
  rw [Real.dist_eq, dist_eq_norm, add_sub_cancel_left,
    Real.coe_toNNReal _ (HRS.PDE.R2Aux.cbNorm_nonneg' 1 f)] at this
  have e : Torus.lift f (Torus.rep x + w) = f (x + Torus.mk w) := by
    simp [Torus.lift, HRS.LocalDivAux.mk_add', Torus.mk_rep]
  have e2 : Torus.lift f (Torus.rep x) = f x := by simp [Torus.lift, Torus.mk_rep]
  rw [e, e2] at this
  exact this

open HRS.L49 HRS.LocalDivAux HRS.KernelAux HRS.KernelAux2 in
set_option maxHeartbeats 1600000 in
/-- Uniform `l49_compensated` (`∫ H(λ g₊(x - ·)) dμ = (|S|/d) ρ(x) λ² log(1/λ) + O(λ²)`): `C`, `lam0` depend on
`d, s, c, Λ` only; the Lipschitz constant of `ρ` is `cbNorm 1 ρ ≤ Λ`. -/
theorem l49_compensated_unif (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (c₀ Λ : ℝ) (hΛ0 : 0 ≤ Λ) :
    ∃ C lam0 : ℝ, 0 < lam0 ∧ lam0 ≤ 1 ∧ ∀ ρ : Torus d → ℝ, UFam d c₀ Λ ρ →
      ∀ lam : ℝ, 0 < lam → lam ≤ lam0 → ∀ x : Torus d,
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
  set L : ℝ := Λ with hLdef
  set Lam : ℝ := Λ with hLamdef
  have hL0 : 0 ≤ L := hΛ0
  have hLam0 : 0 ≤ Lam := hΛ0
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
  intro ρ hF lam hlam hlamle x
  have hρ := hF.smooth
  have hLip : ∀ (x : Torus d) (w : Euc d), |ρ (x + Torus.mk w) - ρ x| ≤ L * ‖w‖ := fun x w =>
    (lip_shift_cb hρ.smooth x w).trans (mul_le_mul_of_nonneg_right hF.lip (norm_nonneg _))
  have hLam : ∀ y, ρ y ≤ Lam := hF.up
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

open HRS.L49 in
/-- Uniform `l49_sqlog`: `C` depends on `d, s, c, Λ` only (from `critical_integrals_unif`). -/
theorem l49_sqlog_unif (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (c₀ Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Torus d → ℝ, UFam d c₀ Λ ρ → ∀ u : ℝ, 0 < u → u ≤ 1 → ∀ x : Torus d,
      Integrable (fun y => gPlus d s c (x - y) ^ 2 * Real.exp (-u * gPlus d s c (x - y)))
        (withDensityReal ρ) ∧ 0 ≤ l49_J d s c ρ x u ∧
      l49_J d s c ρ x u ≤ C * (1 + |Real.log u|) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  obtain ⟨C, hmain, -⟩ := critical_integrals_unif hd hcrit c hc Λ hΛ
  have hgm := measurable_gPlus hd hs0 hsd c
  refine ⟨|C|, abs_nonneg _, fun ρ hF u hu hu1 x => ?_⟩
  have h5 := (hmain ρ hF.smooth hF.up).2.2.1
  have hfm : Measurable fun y : Torus d => gPlus d s c (x - y) ^ 2 * Real.exp (-u * gPlus d s c (x - y)) :=
    ((hgm.comp (measurable_const.sub measurable_id)).pow_const 2).mul
      (Real.measurable_exp.comp (measurable_const.mul (hgm.comp (measurable_const.sub measurable_id))))
  have hf0 : ∀ y : Torus d, 0 ≤ gPlus d s c (x - y) ^ 2 * Real.exp (-u * gPlus d s c (x - y)) :=
    fun y => by positivity
  have hb := h5 u hu hu1 x
  have hfin : ∫⁻ y, ENNReal.ofReal (gPlus d s c (x - y) ^ 2 * Real.exp (-u * gPlus d s c (x - y)))
      ∂(withDensityReal ρ) < ∞ := lt_of_le_of_lt hb ENNReal.ofReal_lt_top
  have hint : Integrable (fun y => gPlus d s c (x - y) ^ 2 * Real.exp (-u * gPlus d s c (x - y)))
      (withDensityReal ρ) := by
    refine ⟨hfm.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    refine lt_of_le_of_lt (le_of_eq ?_) hfin
    refine lintegral_congr fun y => ?_
    rw [Real.enorm_eq_ofReal (hf0 y)]
  refine ⟨hint, integral_nonneg hf0, ?_⟩
  unfold l49_J
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hf0) hfm.aestronglyMeasurable]
  have hCl : C * (1 + |Real.log u|) ≤ |C| * (1 + |Real.log u|) :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
  refine (ENNReal.toReal_le_of_le_ofReal (by positivity) (hb.trans ?_))
  exact ENNReal.ofReal_le_ofReal hCl

open HRS.L49 HRS.External HRS.CavResp in
set_option maxHeartbeats 1600000 in
/-- Uniform `l49_var_bound`. -/
theorem l49_var_bound_unif (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (βm βp : ℝ) (hβm : 0 < βm) (c₀ Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, UFam d c₀ Λ ρ →
      ∀ N : ℕ, 2 ≤ N → β / N ≤ 1 → ∀ x : Torus d, ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      evariance (fun Y : Config d (N - 1) => ∑ i, gPlus d s c (x - Y i)) (critPole d s c β ρ N x t) ≤
        ENNReal.ofReal (C * ((N - 1 : ℕ) : ℝ) * (1 + |Real.log (t * (β / N))|)) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  obtain ⟨C₁, hC₁, hvar_all⟩ := pole_variance_clause_unif hd hs0 hsd βm βp hβm Λ
  obtain ⟨Csl, hCsl0, hsl_all⟩ := l49_sqlog_unif hd hcrit c hc c₀ Λ hΛ
  have hgm := measurable_gPlus hd hs0 hsd c
  refine ⟨C₁ * Real.exp (βp * |c|) * Csl, by positivity, fun β hβI ρ hF N hN hlamle x t ht => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβI.1
  have hρ := hF.smooth
  have hvar := hvar_all β hβI ρ hρ hF.up
  have hsl := hsl_all ρ hF
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlam : 0 ≤ β / N := by positivity
  have ht' : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
  set u : ℝ := t * (β / N) with hu
  have hu0 : 0 < u := mul_pos ht.1 (by positivity)
  have hu1 : u ≤ 1 := by
    have : t * (β / N) ≤ 1 * (β / N) := mul_le_mul_of_nonneg_right ht.2 hlam
    linarith
  have huβ : u ≤ β := by
    have : β / N ≤ β := by
      rw [div_le_iff₀ hN0]
      have : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
      nlinarith
    have : t * (β / N) ≤ 1 * (β / N) := mul_le_mul_of_nonneg_right ht.2 hlam
    linarith
  rw [critPole_eq_poleLaw (c := c) hd hs0 hsd β hβ hρ hN x t]
  have hfm : Measurable fun y : Torus d => gPlus d s c (x - y) :=
    hgm.comp (measurable_const.sub measurable_id)
  have h1 := hvar N hN x t ht' (fun y => gPlus d s c (x - y)) hfm
  have hint := (hsl u hu0 hu1 x).2.2
  have hlint : ∫⁻ y, ENNReal.ofReal (gPlus d s c (x - y) ^ 2 * Real.exp (-u * gPlus d s c (x - y)))
      ∂(withDensityReal ρ) ≤ ENNReal.ofReal (Csl * (1 + |Real.log u|)) := by
    obtain ⟨hI, -, hJ⟩ := hsl u hu0 hu1 x
    rw [← ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall fun y => by positivity)]
    exact ENNReal.ofReal_le_ofReal hJ
  have hE : ∫⁻ y, ‖gPlus d s c (x - y)‖ₑ ^ 2 *
      ENNReal.ofReal (Real.exp (-(t * (β / N)) * periodicRiesz d s (x - y))) ∂(withDensityReal ρ) ≤
      ENNReal.ofReal (Real.exp (βp * |c|)) * ENNReal.ofReal (Csl * (1 + |Real.log u|)) := by
    calc _ ≤ ∫⁻ y, ENNReal.ofReal (Real.exp (βp * |c|)) * ENNReal.ofReal
          (gPlus d s c (x - y) ^ 2 * Real.exp (-u * gPlus d s c (x - y))) ∂(withDensityReal ρ) := by
          refine lintegral_mono fun y => ?_
          have e3 : ‖gPlus d s c (x - y)‖ₑ ^ 2 = ENNReal.ofReal (gPlus d s c (x - y) ^ 2) := by
            rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
          rw [e3, ← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (Real.exp_pos _).le]
          refine ENNReal.ofReal_le_ofReal ?_
          have hpr : periodicRiesz d s (x - y) = gPlus d s c (x - y) - c := by unfold gPlus; ring
          have hexp : Real.exp (-u * periodicRiesz d s (x - y)) =
              Real.exp (-u * gPlus d s c (x - y)) * Real.exp (u * c) := by
            rw [← Real.exp_add, hpr]; congr 1; ring
          have hec : Real.exp (u * c) ≤ Real.exp (βp * |c|) := by
            refine Real.exp_le_exp.2 ?_
            calc u * c ≤ u * |c| := mul_le_mul_of_nonneg_left (le_abs_self c) hu0.le
              _ ≤ βp * |c| := mul_le_mul_of_nonneg_right (huβ.trans hβI.2) (abs_nonneg _)
          show gPlus d s c (x - y) ^ 2 * Real.exp (-u * periodicRiesz d s (x - y)) ≤ _
          rw [hexp]
          have := Real.exp_pos (-u * gPlus d s c (x - y))
          nlinarith [mul_le_mul_of_nonneg_left hec (mul_nonneg (sq_nonneg (gPlus d s c (x - y))) this.le)]
      _ = ENNReal.ofReal (Real.exp (βp * |c|)) * ∫⁻ y, ENNReal.ofReal
          (gPlus d s c (x - y) ^ 2 * Real.exp (-u * gPlus d s c (x - y))) ∂(withDensityReal ρ) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ _ := mul_le_mul' le_rfl hlint
  refine (h1.trans (mul_le_mul' le_rfl hE)).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

end HRS.ME.Unif

end
