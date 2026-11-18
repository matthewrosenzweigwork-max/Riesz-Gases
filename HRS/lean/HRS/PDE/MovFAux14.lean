import HRS.PDE.MovFAux13

/-!
# MOVF Aux14: bridge B (relaxation `⇒` `∫₀^∞ L < ∞`), for a `C²` thermal density
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

/-- The thermal density is positive, and `u_eq = 0` for a `C²` thermal density and `C²` potential. -/
theorem movf_thermal_facts {D : DynData d} (hβ : 0 < D.invβ) (hV : Torus.IsCk 2 D.V) {ρβ : Torus d → ℝ}
    (hth : IsThermalDensity (periodicRiesz d D.s) D.V D.invβ⁻¹ ρβ) (hρβ2 : Torus.IsCk 2 ρβ) :
    (∀ x, 0 < ρβ x) ∧ ∀ x, mfeTransport D ρβ x = 0 := by
  have hd1 : 1 ≤ d := b15_one_le_d D
  have hgi := mova_integrable_periodicRiesz hd1 D.hs0 D.hsd
  obtain ⟨hdens, hform⟩ := hth
  set Z : ℝ := ∫ y, Real.exp (-D.invβ⁻¹ * (D.V y + convFun (periodicRiesz d D.s) ρβ y)) with hZ
  have hZpos : 0 < Z := by
    by_contra hneg
    push Not at hneg
    rcases hneg.lt_or_eq with hlt | heq
    · have h0 := hdens.nonneg 0
      rw [hform 0] at h0
      have : Real.exp (-D.invβ⁻¹ * (D.V 0 + convFun (periodicRiesz d D.s) ρβ 0)) / Z < 0 :=
        div_neg_of_pos_of_neg (Real.exp_pos _) hlt
      linarith
    · have : ∀ x, ρβ x = 0 := fun x => by rw [hform x, heq, div_zero]
      have h1 := hdens.integral_one
      simp only [this, integral_zero] at h1
      norm_num at h1
  have hposβ : ∀ x, 0 < ρβ x := fun x => by
    rw [hform x]; exact div_pos (Real.exp_pos _) hZpos
  refine ⟨hposβ, fun x => ?_⟩
  have hρβ1 := mova_isCk_one_of_two hρβ2
  have hρβc := mova_continuous_of_isCk hρβ2
  ext j
  rw [mova_mfeTransport_apply D hρβ2 hposβ]
  have hV1 := mova_isCk_one_of_two hV
  have hC1 : Torus.IsCk 1 (convFun (periodicRiesz d D.s) ρβ) := mova_isCk_one_convFun hgi hρβ1
  have hlog : (fun y => Real.log (ρβ y)) =
      fun y => (-D.invβ⁻¹) * (D.V y + convFun (periodicRiesz d D.s) ρβ y) + (-Real.log Z) := by
    funext y
    rw [hform y, Real.log_div (Real.exp_pos _).ne' hZpos.ne', Real.log_exp]
    ring
  have hd := congrArg (fun f => Torus.partialDeriv j f x) hlog
  rw [mova_partialDeriv_log j hρβ1 hposβ x] at hd
  have hsum1 : Torus.IsCk 1 (fun y => D.V y + convFun (periodicRiesz d D.s) ρβ y) := mova_isCk_add hV1 hC1
  rw [mova_partialDeriv_add j (mova_isCk_const_mul _ hsum1) (mova_isCk_const _ _),
    mova_partialDeriv_const_mul j hsum1, mova_partialDeriv_add j hV1 hC1,
    mova_partialDeriv_const, mova_partialDeriv_convFun hgi hρβ1 j x] at hd
  have hκ : D.invβ * D.invβ⁻¹ = 1 := mul_inv_cancel₀ hβ.ne'
  have : D.invβ * (Torus.partialDeriv j ρβ x / ρβ x) =
      -(Torus.partialDeriv j D.V x + convFun (periodicRiesz d D.s) (Torus.partialDeriv j ρβ) x) := by
    rw [hd]
    calc D.invβ * (-D.invβ⁻¹ * (Torus.partialDeriv j D.V x +
          convFun (periodicRiesz d D.s) (Torus.partialDeriv j ρβ) x) + 0) =
        -(D.invβ * D.invβ⁻¹) * (Torus.partialDeriv j D.V x +
          convFun (periodicRiesz d D.s) (Torus.partialDeriv j ρβ) x) := by ring
      _ = _ := by rw [hκ]; ring
  rw [this]
  show _ = (0 : ℝ)
  ring

theorem movf_relaxation_L_of_reg {D : DynData d} {ρ : ℝ → Torus d → ℝ} {ρβ : Torus d → ℝ}
    (hM : D.M = -1) (hβ : 0 < D.invβ) (hth : IsThermalDensity (periodicRiesz d D.s) D.V D.invβ⁻¹ ρβ)
    (hρβ2 : Torus.IsCk 2 ρβ) (htr : ∀ T : ℝ, MovTraj D T ρ) {C₀ lam : ℝ} (hlam : 0 < lam)
    (hrelax : ∀ t : ℝ, 0 ≤ t → Torus.cbNorm 2 (fun x => ρ t x - ρβ x) ≤ C₀ * Real.exp (-lam * t)) :
    ∃ L : ℝ → ℝ, (∀ t, 0 ≤ t → 0 ≤ L t) ∧ IntegrableOn L (Set.Ici 0) ∧
      ∀ t : ℝ, 0 ≤ t → IsLipschitzVF (L t) (mfeTransport D (ρ t)) := by
  have hV2 : Torus.IsCk 2 D.V := (htr 0).V_reg
  obtain ⟨hposβ, heq⟩ := movf_thermal_facts hβ hV2 hth hρβ2
  have hρβc := mova_continuous_of_isCk hρβ2
  have hck : ∀ t : ℝ, 0 ≤ t → Torus.IsCk 2 (ρ t) := fun t ht => (htr t).ck t ⟨ht, le_rfl⟩
  -- the lower bound of `ρβ`
  obtain ⟨x0, -, hx0⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hρβc.continuousOn
  set m : ℝ := ρβ x0 with hm
  have hm0 : 0 < m := hposβ x0
  have hmlow : ∀ x, m ≤ ρβ x := fun x => isMinOn_iff.1 hx0 x (Set.mem_univ x)
  set C₀' : ℝ := max C₀ 0 with hC₀'
  have hC₀'0 : 0 ≤ C₀' := le_max_right _ _
  have hrel' : ∀ t : ℝ, 0 ≤ t → Torus.cbNorm 2 (fun x => ρ t x - ρβ x) ≤ C₀' * Real.exp (-lam * t) :=
    fun t ht => (hrelax t ht).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  -- the time after which `ρ` stays above `m/2`
  have hlim : Tendsto (fun t : ℝ => C₀' * Real.exp (-lam * t)) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_neg_iff_pos.2 hlam)))
    simpa using this.const_mul C₀'
  obtain ⟨t₁, ht₁⟩ := (eventually_atTop.1 (hlim.eventually (gt_mem_nhds (half_pos hm0))))
  set t₂ : ℝ := max t₁ 0 with ht₂
  have ht₂0 : 0 ≤ t₂ := le_max_right _ _
  have hbig : ∀ t, t₂ ≤ t → C₀' * Real.exp (-lam * t) < m / 2 := fun t ht =>
    ht₁ t ((le_max_left _ _).trans ht)
  -- constants
  set Λ : ℝ := Torus.cbNorm 2 ρβ + C₀' with hΛ
  obtain ⟨K, hK0, hK⟩ := movf_lip_diff D hβ (m / 2) Λ (half_pos hm0)
  obtain ⟨c₁, Lu, hc₁, hLu, -, hLuL⟩ := mova_traj_bounds (htr t₂)
  have hΛβ : Torus.cbNorm 2 ρβ ≤ Λ := by
    have : 0 ≤ C₀' := hC₀'0
    linarith
  set A : ℝ := Lu * Real.exp (lam * t₂) + K * C₀' with hA
  refine ⟨fun t => A * Real.exp (-lam * t), fun t _ => by positivity, ?_, fun t ht => ?_⟩
  · have h1 : IntegrableOn (fun t : ℝ => A * Real.exp (-lam * t)) (Set.Ioi 0) :=
      (exp_neg_integrableOn_Ioi 0 hlam).const_mul A
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact h1
  · by_cases hts : t ≤ t₂
    · have h1 := hLuL t ⟨ht, hts⟩
      refine mova_isLipschitzVF_mono ?_ h1
      have e1 : 1 ≤ Real.exp (lam * (t₂ - t)) := Real.one_le_exp (by nlinarith)
      have e2 : Real.exp (lam * t₂) * Real.exp (-lam * t) = Real.exp (lam * (t₂ - t)) := by
        rw [← Real.exp_add]; congr 1; ring
      have : 0 ≤ K * C₀' * Real.exp (-lam * t) := by positivity
      calc Lu ≤ Lu * Real.exp (lam * (t₂ - t)) := le_mul_of_one_le_right hLu.le e1
        _ = Lu * Real.exp (lam * t₂) * Real.exp (-lam * t) := by rw [mul_assoc, e2]
        _ ≤ A * Real.exp (-lam * t) := by rw [hA]; nlinarith
    · push Not at hts
      have hts' : t₂ ≤ t := hts.le
      have hρt := hck t ht
      have hh2 : Torus.IsCk 2 (fun x => ρ t x - ρβ x) := mova_isCk_sub hρt hρβ2
      have hδ := hrel' t ht
      have hlow : ∀ x, m / 2 ≤ ρ t x := by
        intro x
        have h1 := mova_abs_le_cbNorm_two hh2 x
        have h2 := hbig t hts'
        have := (abs_le.1 (h1.trans hδ)).1
        have h3 := hmlow x
        linarith
      have hΛt : Torus.cbNorm 2 (ρ t) ≤ Λ := by
        have hsplit : ρ t = ρβ + fun x => ρ t x - ρβ x := by funext x; simp
        have := Torus.cbNorm_add_le 2 ρβ (fun x => ρ t x - ρβ x) hρβ2 hh2
        rw [← hsplit] at this
        have h3 : Real.exp (-lam * t) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
        have h4 : C₀' * Real.exp (-lam * t) ≤ C₀' := by nlinarith
        rw [hΛ]
        linarith
      have hlowβ : ∀ x, m / 2 ≤ ρβ x := fun x => by linarith [hmlow x]
      have hLt := hK hρt hρβ2 hlow hlowβ hΛt hΛβ heq
      refine mova_isLipschitzVF_mono ?_ hLt
      have h5 : K * Torus.cbNorm 2 (fun x => ρ t x - ρβ x) ≤ K * (C₀' * Real.exp (-lam * t)) :=
        mul_le_mul_of_nonneg_left hδ hK0
      have : 0 ≤ Lu * Real.exp (lam * t₂) * Real.exp (-lam * t) := by positivity
      calc K * Torus.cbNorm 2 (fun x => ρ t x - ρβ x) ≤ K * (C₀' * Real.exp (-lam * t)) := h5
        _ ≤ A * Real.exp (-lam * t) := by rw [hA]; nlinarith

end HRS

end
