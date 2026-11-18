import HRS.Main.EqBiasAux6

/-!
# EQ-BIAS, S8c/S7: the local profile of `g_+` on the torus

* `eqbias_local_data`: `δ, R, G₀` with `|g_+(w) - |w|^{-s}| ≤ R` for `0 < |w| ≤ δ` and `g_+ ≤ G₀` on the
  cube away from `0` (copied from `l49_compensated`, without `hcrit`).
* `eqbias_J_torus`: `sup_x |u^{2-p} J_x(u) - ρ(x) κ₂| → 0`, `J_x(u) = ∫ g_+(x-y)² e^{-u g_+(x-y)} dμ(y)`,
  `κ₂ = |𝕊^{d-1}|Γ(2-p)/s`.
* `eqbias_J_le`: `J_x(u) ≤ C_J u^{p-2}` for `0 < u ≤ 1`.
* `eqbias_core_mass`: `∫ g_+(x-y) 1{g_+(x-y) > H} dμ(y) ≤ C_m H^{1-p}` for `H ≥ H₀`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS

namespace Main

variable {d : ℕ} {s : ℝ}

open HRS.LocalDivAux HRS.PoleCavityAux HRS.KernelAux HRS.KernelAux2 HRS.CavResp

set_option maxHeartbeats 1600000 in
theorem eqbias_local_data (hd : 2 ≤ d) (hs0 : 0 < s) (hsd : s < d) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) :
    ∃ δ R G₀ : ℝ, 0 < δ ∧ δ ≤ 1 / 4 ∧ 0 ≤ R ∧ 0 ≤ G₀ ∧
      (∀ w : Euc d, 0 < ‖w‖ → ‖w‖ ≤ δ →
        |gPlus d s c (Torus.mk w) - ‖w‖ ^ (-s)| ≤ R) ∧
      (∀ w ∈ cube d, δ < ‖w‖ → gPlus d s c (Torus.mk w) ≤ G₀) := by
  have hd1 : 1 ≤ d := by omega
  have hd0 : 0 < d := by omega
  have hs0' : 0 ≤ s := hs0.le
  obtain ⟨r, δ₁, hδ₁, hr, hloc⟩ := periodicRiesz_local_singularity (d := d) hd hs0 hsd
  have hrc : Continuous r :=
    continuous_of_lift' (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift r) from hr).continuous
  obtain ⟨R₀, hR₀⟩ := isCompact_univ.exists_bound_of_continuousOn (f := r) hrc.continuousOn
  set R : ℝ := |R₀| + |c| with hR
  have hR0 : 0 ≤ R := by positivity
  obtain ⟨A, hA1, hA⟩ := gPlus_envelope hd hs0 hsd c
  set δ : ℝ := min (δ₁ / 2) (1 / 4) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδ4 : δ ≤ 1 / 4 := min_le_right _ _
  have hδδ₁ : δ < δ₁ := by have := min_le_left (δ₁ / 2) (1 / 4); linarith
  set Γ₀ : ℝ := A * (δ / d) ^ (-s) with hΓ₀
  have hΓ0 : 0 ≤ Γ₀ := by
    have : 0 ≤ A := by linarith
    positivity
  refine ⟨δ, R, Γ₀, hδ0, hδ4, hR0, hΓ0, ?_, ?_⟩
  · intro w hw0 hwδ
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
  · intro w hw hwδ
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

theorem eqbias_mk_zero : Torus.mk (0 : Euc d) = 0 := by
  funext i; simp [Torus.mk]

theorem eqbias_gPlus_neg (c : ℝ) (z : Torus d) : gPlus d s c (-z) = gPlus d s c z := by
  unfold gPlus; rw [periodicRiesz_neg]

set_option maxHeartbeats 1600000 in
/-- `sup_x |u^{2-p} J_x(u) - ρ(x) κ₂| → 0` as `u → 0`. -/
theorem eqbias_J_torus (hd : 2 ≤ d) (hs1 : (d : ℝ) / 2 < s) (hsd : s < d) {ρ : Torus d → ℝ}
    (hρ : SmoothPosDensity ρ) (c : ℝ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) :
    ∀ ε : ℝ, 0 < ε → ∃ u₀ : ℝ, 0 < u₀ ∧ ∀ u : ℝ, 0 < u → u ≤ u₀ → ∀ x : Torus d,
      |u ^ (2 - (d : ℝ) / s) *
          (∫ y, gPlus d s c (x - y) ^ 2 * Real.exp (-(u * gPlus d s c (x - y)))
            ∂(withDensityReal ρ)) -
        ρ x * (sphereArea d * Real.Gamma (2 - (d : ℝ) / s) / s)| ≤ ε := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨hs0, hp1, hp2⟩ := eqbias_p_range hs1 hsd hd
  obtain ⟨Λ, hΛ0, hΛ⟩ := PoleCavityAux.exists_density_bound hρ
  obtain ⟨L, hL0, hL⟩ := lip_shift hρ.smooth
  obtain ⟨δ, R, G₀, hδ, hδ4, hR, hG₀, hloc, hfar⟩ := eqbias_local_data hd hs0 hsd c hc
  intro ε hε
  obtain ⟨u₀, hu₀, hJ⟩ := eqbias_J_abstract hd1 hs0 hsd hp2 hδ hδ4 hR hG₀ hΛ0.le hL0 ε hε
  refine ⟨u₀, hu₀, fun u hu hu₀' x => ?_⟩
  have hgm := PoleCavityAux.measurable_gPlus hd hs0.le hsd c
  have hγm : Measurable fun w : Euc d => gPlus d s c (Torus.mk w) :=
    hgm.comp Torus.continuous_mk.measurable
  have hρm := measurable_ρx hρ x
  have hFm : Measurable fun y : Torus d => gPlus d s c (x - y) ^ 2 *
      Real.exp (-(u * gPlus d s c (x - y))) :=
    ((hgm.comp (measurable_const.sub measurable_id)).pow_const 2).mul
      (Real.measurable_exp.comp (((hgm.comp (measurable_const.sub measurable_id)).const_mul u).neg))
  have e1 : ∫ y, gPlus d s c (x - y) ^ 2 * Real.exp (-(u * gPlus d s c (x - y))) ∂(withDensityReal ρ) =
      ∫ y, ρ y * (gPlus d s c (x - y) ^ 2 * Real.exp (-(u * gPlus d s c (x - y)))) :=
    integral_withDensityReal_eq ρ hρ.density.measurable hρ.density.nonneg _
  have e2 : ∫ y, ρ y * (gPlus d s c (x - y) ^ 2 * Real.exp (-(u * gPlus d s c (x - y)))) =
      ∫ w in cube d, ρ (x + Torus.mk w) * (gPlus d s c (x - (x + Torus.mk w)) ^ 2 *
        Real.exp (-(u * gPlus d s c (x - (x + Torus.mk w))))) :=
    integral_shift_cube x (fun y => ρ y * (gPlus d s c (x - y) ^ 2 *
      Real.exp (-(u * gPlus d s c (x - y))))) (hρ.density.measurable.mul hFm)
  have e3 : ∫ w in cube d, ρ (x + Torus.mk w) * (gPlus d s c (x - (x + Torus.mk w)) ^ 2 *
        Real.exp (-(u * gPlus d s c (x - (x + Torus.mk w))))) =
      ∫ w in cube d, gPlus d s c (Torus.mk w) ^ 2 * Real.exp (-(u * gPlus d s c (Torus.mk w))) *
        ρ (x + Torus.mk w) := by
    refine setIntegral_congr_fun measurableSet_cube fun w _ => ?_
    rw [sub_add_cancel_left, eqbias_gPlus_neg]
    ring
  rw [e1, e2, e3]
  have h := hJ (fun w => gPlus d s c (Torus.mk w)) (fun w => ρ (x + Torus.mk w)) hγm hρm
    (fun w => hc _) hloc hfar (fun w => ⟨hρ.density.nonneg _, hΛ _⟩)
    (fun w hw => by
      have := hL x w
      simp only [eqbias_mk_zero, add_zero]
      exact this) u hu hu₀'
  have e4 : ρ (x + Torus.mk (0 : Euc d)) = ρ x := by
    rw [eqbias_mk_zero, add_zero]
  have hbc : ballConst d = sphereArea d := HRS.L49.l49_ballConst_eq hd1
  rw [e4, hbc] at h
  exact h

/-- `J_x(u) ≤ C_J u^{p-2}` for `0 < u ≤ 1`. -/
theorem eqbias_J_le (hd : 2 ≤ d) (hs1 : (d : ℝ) / 2 < s) (hsd : s < d) {ρ : Torus d → ℝ}
    (hρ : SmoothPosDensity ρ) (c : ℝ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) :
    ∃ CJ : ℝ, 0 ≤ CJ ∧ ∀ u : ℝ, 0 < u → u ≤ 1 → ∀ x : Torus d,
      ∫ y, gPlus d s c (x - y) ^ 2 * Real.exp (-(u * gPlus d s c (x - y))) ∂(withDensityReal ρ) ≤
        CJ * u ^ ((d : ℝ) / s - 2) := by
  obtain ⟨hs0, hp1, hp2⟩ := eqbias_p_range hs1 hsd hd
  have hP := PoleCavityAux.isProbabilityMeasure_mu hρ
  obtain ⟨Λ, hΛ0, hΛ⟩ := PoleCavityAux.exists_density_bound hρ
  obtain ⟨u₁, hu₁, hJ⟩ := eqbias_J_torus hd hs1 hsd hρ c hc 1 one_pos
  set u₀ : ℝ := min u₁ 1 with hu₀
  have hu₀0 : 0 < u₀ := lt_min hu₁ one_pos
  set κ₂ : ℝ := sphereArea d * Real.Gamma (2 - (d : ℝ) / s) / s with hκ₂
  have hκ₂0 : 0 ≤ κ₂ := by
    have hA : 0 < sphereArea d := HRS.StaticLimitsAux.sphereArea_pos hd
    have hG : 0 < Real.Gamma (2 - (d : ℝ) / s) := Real.Gamma_pos_of_pos (by linarith)
    positivity
  refine ⟨max (Λ * κ₂ + 1) (2 / u₀ ^ 2), by positivity, fun u hu hu1 x => ?_⟩
  have hgm := PoleCavityAux.measurable_gPlus hd hs0.le hsd c
  have hFm : Measurable fun y : Torus d => gPlus d s c (x - y) ^ 2 *
      Real.exp (-(u * gPlus d s c (x - y))) :=
    ((hgm.comp (measurable_const.sub measurable_id)).pow_const 2).mul
      (Real.measurable_exp.comp (((hgm.comp (measurable_const.sub measurable_id)).const_mul u).neg))
  have hneg : u ^ ((d : ℝ) / s - 2) = (u ^ (2 - (d : ℝ) / s))⁻¹ := by
    rw [← Real.rpow_neg hu.le]; congr 1; ring
  have hge1 : 1 ≤ u ^ ((d : ℝ) / s - 2) := by
    have := Real.rpow_le_rpow_of_exponent_ge hu hu1 (show (d : ℝ) / s - 2 ≤ 0 by linarith)
    simpa using this
  by_cases hsmall : u ≤ u₀
  · have h1 := hJ u hu (hsmall.trans (min_le_left _ _)) x
    set J := ∫ y, gPlus d s c (x - y) ^ 2 * Real.exp (-(u * gPlus d s c (x - y))) ∂(withDensityReal ρ)
      with hJdef
    have hpos : 0 < u ^ (2 - (d : ℝ) / s) := Real.rpow_pos_of_pos hu _
    have h2 : u ^ (2 - (d : ℝ) / s) * J ≤ Λ * κ₂ + 1 := by
      have h3 := (abs_le.1 h1).2
      have h4 : ρ x * κ₂ ≤ Λ * κ₂ := mul_le_mul_of_nonneg_right (hΛ x) hκ₂0
      linarith
    have h5 : J ≤ (Λ * κ₂ + 1) * u ^ ((d : ℝ) / s - 2) := by
      rw [hneg, ← div_eq_mul_inv, le_div_iff₀ hpos, mul_comm]
      exact h2
    exact h5.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · push Not at hsmall
    have hJb : ∫ y, gPlus d s c (x - y) ^ 2 * Real.exp (-(u * gPlus d s c (x - y)))
        ∂(withDensityReal ρ) ≤ 2 / u ^ 2 := by
      have := integral_mono_of_nonneg (μ := withDensityReal ρ)
        (f := fun y : Torus d => gPlus d s c (x - y) ^ 2 * Real.exp (-(u * gPlus d s c (x - y))))
        (g := fun _ => 2 / u ^ 2)
        (Eventually.of_forall fun y => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
        (integrable_const _) (Eventually.of_forall fun y => eqbias_gam_exp_le (hc _) hu)
      simpa using this
    have h6 : 2 / u ^ 2 ≤ 2 / u₀ ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hu₀0.le hsmall.le 2)
    have h7 : 2 / u₀ ^ 2 ≤ max (Λ * κ₂ + 1) (2 / u₀ ^ 2) * u ^ ((d : ℝ) / s - 2) := by
      have : max (Λ * κ₂ + 1) (2 / u₀ ^ 2) * 1 ≤ max (Λ * κ₂ + 1) (2 / u₀ ^ 2) * u ^ ((d : ℝ) / s - 2) :=
        mul_le_mul_of_nonneg_left hge1 (by positivity)
      linarith [le_max_right (Λ * κ₂ + 1) (2 / u₀ ^ 2)]
    linarith

set_option maxHeartbeats 3200000 in
/-- Mass of the core `{g_+ > H}`: `∫ g_+ 1{g_+ > H} dμ ≤ C_m H^{1-p}` for `H ≥ H₀`. -/
theorem eqbias_core_mass (hd : 2 ≤ d) (hs1 : (d : ℝ) / 2 < s) (hsd : s < d) {ρ : Torus d → ℝ}
    (hρ : SmoothPosDensity ρ) (c : ℝ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) :
    ∃ Cm H₀ : ℝ, 0 ≤ Cm ∧ 0 < H₀ ∧ ∀ H : ℝ, H₀ ≤ H → ∀ x : Torus d,
      ∫ y, (if H < gPlus d s c (x - y) then gPlus d s c (x - y) else 0) ∂(withDensityReal ρ) ≤
        Cm * H ^ (1 - (d : ℝ) / s) := by
  have hd1 : 1 ≤ d := by omega
  haveI : Nonempty (Fin d) := ⟨⟨0, hd1⟩⟩
  obtain ⟨hs0, hp1, hp2⟩ := eqbias_p_range hs1 hsd hd
  obtain ⟨Λ, hΛ0, hΛ⟩ := PoleCavityAux.exists_density_bound hρ
  obtain ⟨δ, R, G₀, hδ, hδ4, hR, hG₀, hloc, hfar⟩ := eqbias_local_data hd hs0 hsd c hc
  have hds : (0 : ℝ) < d - s := by linarith
  set Cm : ℝ := 2 * Λ * (ballConst d / ((d : ℝ) - s)) * 2 ^ ((d : ℝ) / s - 1) with hCm
  have hbc : 0 ≤ ballConst d := ballConst_nonneg
  refine ⟨Cm, max (G₀ + 1) (2 * R + 1), by positivity, lt_max_of_lt_left (by linarith), ?_⟩
  intro H hH x
  have hH1 : G₀ + 1 ≤ H := (le_max_left _ _).trans hH
  have hH2 : 2 * R + 1 ≤ H := (le_max_right _ _).trans hH
  have hHpos : 0 < H := by linarith
  have hgm := PoleCavityAux.measurable_gPlus hd hs0.le hsd c
  have hγm : Measurable fun w : Euc d => gPlus d s c (Torus.mk w) :=
    hgm.comp Torus.continuous_mk.measurable
  have hρm := measurable_ρx hρ x
  have hfm : Measurable fun y : Torus d => gPlus d s c (x - y) :=
    hgm.comp (measurable_const.sub measurable_id)
  have hFm : Measurable fun y : Torus d => (if H < gPlus d s c (x - y) then gPlus d s c (x - y) else 0) :=
    Measurable.ite (measurableSet_lt measurable_const hfm) hfm measurable_const
  have e1 : ∫ y, (if H < gPlus d s c (x - y) then gPlus d s c (x - y) else 0) ∂(withDensityReal ρ) =
      ∫ y, ρ y * (if H < gPlus d s c (x - y) then gPlus d s c (x - y) else 0) :=
    integral_withDensityReal_eq ρ hρ.density.measurable hρ.density.nonneg _
  have e2 : ∫ y, ρ y * (if H < gPlus d s c (x - y) then gPlus d s c (x - y) else 0) =
      ∫ w in cube d, ρ (x + Torus.mk w) * (if H < gPlus d s c (x - (x + Torus.mk w)) then
        gPlus d s c (x - (x + Torus.mk w)) else 0) :=
    integral_shift_cube x (fun y => ρ y * (if H < gPlus d s c (x - y) then gPlus d s c (x - y) else 0))
      (hρ.density.measurable.mul hFm)
  have e3 : ∫ w in cube d, ρ (x + Torus.mk w) * (if H < gPlus d s c (x - (x + Torus.mk w)) then
        gPlus d s c (x - (x + Torus.mk w)) else 0) =
      ∫ w in cube d, ρ (x + Torus.mk w) * (if H < gPlus d s c (Torus.mk w) then
        gPlus d s c (Torus.mk w) else 0) := by
    refine setIntegral_congr_fun measurableSet_cube fun w _ => ?_
    rw [sub_add_cancel_left, eqbias_gPlus_neg]
  rw [e1, e2, e3]
  -- the dominating radial function
  set ϱ : ℝ := (H / 2) ^ (-(1 / s)) with hϱ
  have hϱ0 : 0 < ϱ := Real.rpow_pos_of_pos (by positivity) _
  set G : Euc d → ℝ := fun w => 2 * Λ * (Ioc (0 : ℝ) ϱ).indicator (fun r : ℝ => r ^ (-s)) ‖w‖ with hG
  have hGint : Integrable G := by
    have := (HRS.L49.l49_radial_ind hd1 (ε := 0) (δ := ϱ) le_rfl hϱ0.le s (Or.inl (by linarith))).1
    exact this.const_mul (2 * Λ)
  have hG0 : ∀ w, 0 ≤ G w := by
    intro w
    simp only [hG]
    refine mul_nonneg (by positivity) ?_
    by_cases hw : ‖w‖ ∈ Ioc (0 : ℝ) ϱ
    · rw [indicator_of_mem hw]; exact Real.rpow_nonneg (norm_nonneg w) _
    · rw [indicator_of_notMem hw]
  have hpt : ∀ w : Euc d, w ≠ 0 → w ∈ cube d →
      ρ (x + Torus.mk w) * (if H < gPlus d s c (Torus.mk w) then gPlus d s c (Torus.mk w) else 0) ≤ G w := by
    intro w hw0 hwc
    have hρw := hρ.density.nonneg (x + Torus.mk w)
    have hρΛ := hΛ (x + Torus.mk w)
    by_cases hγ : H < gPlus d s c (Torus.mk w)
    · rw [if_pos hγ]
      have hwδ : ‖w‖ ≤ δ := by
        by_contra hcon
        push Not at hcon
        have := hfar w hwc hcon
        linarith
      have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw0
      have hl := hloc w hwpos hwδ
      have hup : gPlus d s c (Torus.mk w) ≤ ‖w‖ ^ (-s) + R := by
        have := (abs_le.1 hl).2; linarith
      have hA : H / 2 < ‖w‖ ^ (-s) := by linarith
      have hwϱ : ‖w‖ ≤ ϱ := by
        by_contra hcon
        push Not at hcon
        have h1 : ‖w‖ ^ (-s) ≤ ϱ ^ (-s) := Real.rpow_le_rpow_of_nonpos hϱ0 hcon.le (by linarith)
        have h2 : ϱ ^ (-s) = H / 2 := by
          rw [hϱ, ← Real.rpow_mul (by positivity)]
          have : -(1 / s) * -s = 1 := by field_simp
          rw [this, Real.rpow_one]
        linarith
      have hγ2 : gPlus d s c (Torus.mk w) ≤ 2 * ‖w‖ ^ (-s) := by linarith
      simp only [hG]
      rw [indicator_of_mem (show ‖w‖ ∈ Ioc (0 : ℝ) ϱ from ⟨hwpos, hwϱ⟩)]
      calc ρ (x + Torus.mk w) * gPlus d s c (Torus.mk w) ≤ Λ * (2 * ‖w‖ ^ (-s)) :=
            mul_le_mul hρΛ hγ2 (show 0 ≤ gPlus d s c (Torus.mk w) from hc _) hΛ0.le
        _ = 2 * Λ * ‖w‖ ^ (-s) := by ring
    · rw [if_neg hγ, mul_zero]; exact hG0 w
  have hne : ∀ᵐ w ∂(volume : Measure (Euc d)), w ≠ 0 := by
    rw [ae_iff]
    simpa using measure_singleton (μ := (volume : Measure (Euc d))) (0 : Euc d)
  have hle1 : ∫ w in cube d, ρ (x + Torus.mk w) * (if H < gPlus d s c (Torus.mk w) then
      gPlus d s c (Torus.mk w) else 0) ≤ ∫ w in cube d, G w := by
    refine integral_mono_of_nonneg (μ := (volume : Measure (Euc d)).restrict (cube d)) ?_
      hGint.integrableOn ?_
    · exact Eventually.of_forall fun w => mul_nonneg (hρ.density.nonneg _)
        (by
          split_ifs with h
          · exact hc _
          · exact le_rfl)
    · filter_upwards [ae_restrict_of_ae hne, ae_restrict_mem measurableSet_cube] with w hw0 hwc
      exact hpt w hw0 hwc
  have hle2 : ∫ w in cube d, G w ≤ ∫ w, G w :=
    setIntegral_le_integral hGint (Eventually.of_forall hG0)
  have hGval : ∫ w, G w = 2 * Λ * (ballConst d * ((ϱ ^ ((d : ℝ) - s)) / ((d : ℝ) - s))) := by
    simp only [hG]
    rw [integral_const_mul]
    have := (HRS.L49.l49_radial_ind hd1 (ε := 0) (δ := ϱ) le_rfl hϱ0.le s (Or.inl (by linarith))).2
    rw [this, integral_rpow (Or.inl (by linarith))]
    rw [show (d : ℝ) - 1 - s + 1 = (d : ℝ) - s by ring, Real.zero_rpow (by linarith)]
    ring
  have hϱpow : ϱ ^ ((d : ℝ) - s) = 2 ^ ((d : ℝ) / s - 1) * H ^ (1 - (d : ℝ) / s) := by
    rw [hϱ, ← Real.rpow_mul (by positivity), Real.div_rpow hHpos.le (by norm_num)]
    have h1 : -(1 / s) * ((d : ℝ) - s) = 1 - (d : ℝ) / s := by field_simp; ring
    rw [h1]
    have h2 : (2 : ℝ) ^ (1 - (d : ℝ) / s) = ((2 : ℝ) ^ ((d : ℝ) / s - 1))⁻¹ := by
      rw [← Real.rpow_neg (by norm_num)]; congr 1; ring
    rw [h2]
    field_simp
  refine hle1.trans (hle2.trans (le_of_eq ?_))
  rw [hGval, hϱpow, hCm]
  ring

end Main

end HRS

end
