/-
# HRS.Equilibrium.Q84aAuxC — packet Q84a helpers (the force field is bounded)

`F_μ = ∇(g*μ)`; the thermal equation gives `g*ρ = -β⁻¹ log(Zρ) - V`, so
`F_μ = -β⁻¹ ∇ρ/ρ - ∇V` is bounded (`ρ` smooth and positive on the compact torus).
-/
import HRS.Equilibrium.Q84aAuxA

open MeasureTheory Filter Topology

noncomputable section

namespace HRS.Q84a

variable {d : ℕ} {s : ℝ}

theorem q84a_contDiff_one {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) (Torus.lift φ) :=
  ContDiff.of_le (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift φ) from hφ)
    (by exact_mod_cast (le_top : ((1 : ℕ) : ℕ∞) ≤ ⊤))

theorem q84a_conv_eq {ρ : Torus d → ℝ} (hρs : SmoothPosDensity ρ) :
    convMeasure (periodicRiesz d s) (withDensityReal ρ) = convFun (periodicRiesz d s) ρ := by
  have hρc : Continuous ρ := Torus.continuous_of_continuous_lift (q84a_contDiff_one hρs.smooth).continuous
  funext z
  unfold convMeasure convFun
  rw [integral_withDensityReal_eq ρ hρc.measurable (fun y => (hρs.pos y).le)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  ring

theorem q84a_fderiv_bdd {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ y, ‖fderiv ℝ (Torus.lift φ) y‖ ≤ B := by
  obtain ⟨B, hB⟩ := Torus.bddAbove_norm_iteratedFDeriv_lift 1 φ (q84a_contDiff_one hφ)
  refine ⟨max B 0, le_max_right _ _, fun y => ?_⟩
  have := hB (Set.mem_range_self y)
  simp only [norm_iteratedFDeriv_one] at this
  exact this.trans (le_max_left _ _)

theorem q84a_force_bound {V ρ : Torus d → ℝ} {β : ℝ} (hβ : 0 < β) (hV : Torus.IsSmooth V)
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρ) (hρs : SmoothPosDensity ρ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖forceField d s ρ x‖ ≤ M := by
  obtain ⟨Bρ, hBρ0, hBρ⟩ := q84a_fderiv_bdd hρs.smooth
  obtain ⟨BV, hBV0, hBV⟩ := q84a_fderiv_bdd hV
  have hρ1 := q84a_contDiff_one hρs.smooth
  have hV1 := q84a_contDiff_one hV
  have hρc : Continuous ρ := Torus.continuous_of_continuous_lift hρ1.continuous
  obtain ⟨x0, -, hx0⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hρc.continuousOn
  have hm : 0 < ρ x0 := hρs.pos x0
  set φ : Torus d → ℝ := convFun (periodicRiesz d s) ρ with hφ
  set Z : ℝ := ∫ y, Real.exp (-β * (V y + φ y)) with hZdef
  have ht : ∀ x, ρ x = Real.exp (-β * (V x + φ x)) / Z := hρ.2
  have hZ : 0 < Z := by
    have h1 := ht 0
    have h2 := hρs.pos 0
    have h3 := Real.exp_pos (-β * (V 0 + φ 0))
    rcases lt_trichotomy Z 0 with h | h | h
    · exfalso
      have : Real.exp (-β * (V 0 + φ 0)) / Z < 0 := div_neg_of_pos_of_neg h3 h
      linarith
    · rw [h, div_zero] at h1; linarith
    · exact h
  have hform : φ = fun x => -β⁻¹ * Real.log (Z * ρ x) - V x := by
    funext x
    have h1 : Z * ρ x = Real.exp (-β * (V x + φ x)) := by
      rw [ht x]; field_simp
    rw [h1, Real.log_exp]
    field_simp
    ring
  have hlift : Torus.lift φ = fun y => -β⁻¹ * Real.log (Z * Torus.lift ρ y) - Torus.lift V y := by
    funext y
    simp only [Torus.lift, Function.comp]
    rw [hform]
  have hne : ∀ y, Z * Torus.lift ρ y ≠ 0 := fun y => (mul_pos hZ (hρs.pos _)).ne'
  refine ⟨β⁻¹ * (ρ x0)⁻¹ * Bρ + BV, by positivity, fun x => ?_⟩
  have hFx : forceField d s ρ x = (InnerProductSpace.toDual ℝ (Euc d)).symm
      (fderiv ℝ (Torus.lift φ) (Torus.rep x)) := by
    unfold forceField Torus.grad gradient
    rw [q84a_conv_eq hρs]
  rw [hFx, LinearIsometryEquiv.norm_map]
  have hρd : HasFDerivAt (Torus.lift ρ) (fderiv ℝ (Torus.lift ρ) (Torus.rep x)) (Torus.rep x) :=
    ((hρ1.differentiable (by simp)) _).hasFDerivAt
  have hVd : HasFDerivAt (Torus.lift V) (fderiv ℝ (Torus.lift V) (Torus.rep x)) (Torus.rep x) :=
    ((hV1.differentiable (by simp)) _).hasFDerivAt
  have hd := ((((hρd.const_mul Z).log (hne _)).const_mul (-β⁻¹)).sub hVd)
  have h1 : fderiv ℝ (Torus.lift φ) (Torus.rep x) =
      -β⁻¹ • (Z * Torus.lift ρ (Torus.rep x))⁻¹ • Z • fderiv ℝ (Torus.lift ρ) (Torus.rep x)
        - fderiv ℝ (Torus.lift V) (Torus.rep x) := by
    rw [hlift]; exact hd.fderiv
  have hρx : Torus.lift ρ (Torus.rep x) = ρ x := by simp [Torus.lift, Torus.mk_rep]
  rw [h1, hρx]
  refine (norm_sub_le _ _).trans ?_
  have hρxm : ρ x0 ≤ ρ x := isMinOn_univ_iff.1 hx0 x
  have hρx0 : 0 < ρ x := hρs.pos x
  have hc : ‖(-β⁻¹ : ℝ)‖ * (‖(Z * ρ x)⁻¹‖ * ‖Z‖) ≤ β⁻¹ * (ρ x0)⁻¹ := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg,
      abs_of_pos (inv_pos.2 hβ), abs_of_pos hZ, abs_of_pos (inv_pos.2 (mul_pos hZ hρx0))]
    have : (Z * ρ x)⁻¹ * Z = (ρ x)⁻¹ := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ hm hρxm) (inv_pos.2 hβ).le
  rw [norm_smul, norm_smul, norm_smul]
  have h2 := mul_le_mul hc (hBρ (Torus.rep x)) (norm_nonneg _) (by positivity)
  have h3 := hBV (Torus.rep x)
  calc _ ≤ ‖(-β⁻¹ : ℝ)‖ * (‖(Z * ρ x)⁻¹‖ * (‖Z‖ * ‖fderiv ℝ (Torus.lift ρ) (Torus.rep x)‖)) +
        ‖fderiv ℝ (Torus.lift V) (Torus.rep x)‖ := le_refl _
    _ = ‖(-β⁻¹ : ℝ)‖ * (‖(Z * ρ x)⁻¹‖ * ‖Z‖) * ‖fderiv ℝ (Torus.lift ρ) (Torus.rep x)‖ +
        ‖fderiv ℝ (Torus.lift V) (Torus.rep x)‖ := by ring
    _ ≤ β⁻¹ * (ρ x0)⁻¹ * Bρ + BV := add_le_add h2 h3

end HRS.Q84a
