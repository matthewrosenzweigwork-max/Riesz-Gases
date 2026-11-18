import HRS.MS.S21F_D00
import HRS.MS.R2WinOrbTRE3
import HRS.MS.S103dLip2
import HRS.MS.S104eFinal
import HRS.MS.S21H2_W13
import HRS.MS.GapExt
import HRS.MS.S111X2Aux5

/-!
# HRS S2.1(iii), SOL13 packets 1–2: common radius and uniform thermal data

The common radius is selected below the all-time orbit threshold and both terminal-regularity
thresholds.  The thermal package exposes a Poincaré constant and the uniform response form before
any trajectory, together with the actual-law density-ratio interface.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole
open HRS.MS.R26T3
open HRS.MS.R2WinOrbNL
open HRS.MS.R2WinErr

private theorem fp81s21_canonical_thermal (p : Parameters) :
    IsThermalEquilibrium p.d p.s p.a p.β (thermalDensity p.d p.s p.a p.β) := by
  have hdp : 2 ≤ p.d := p.hd
  have hdnat : 0 < p.d := by omega
  have hdpos : (0 : ℝ) < p.d := by exact_mod_cast hdnat
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  by_cases hs0 : p.s = 0
  · obtain ⟨⟨ρ, hρ, -⟩, -, -⟩ :=
      HRS.MS.Thm.logThermalDensity_spec_proof p.hd p.a p.β p.ha p.hβ
    have hρeq := HRS.MS.Mov0.mv0_rho_eq p.hd (by norm_num) hdpos p.ha p.hβ hρ
    rw [hρeq] at hρ
    simpa [hs0] using hρ
  · have hspos : 0 < p.s := lt_of_le_of_ne p.hs0 (Ne.symm hs0)
    obtain ⟨⟨ρ, hρ, -⟩, -, -⟩ :=
      HRS.MS.Thm.thermalDensity_spec_proof p.hd hspos hsd p.a p.β p.ha p.hβ
    have hρeq := HRS.MS.Mov0.mv0_rho_eq p.hd p.hs0 hsd p.ha p.hβ hρ
    rw [hρeq] at hρ
    exact hρ

/-- One radius works for the all-time nonlinear orbits, the Hermite adjoint interface,
general-initial-time terminal regularity, and every positive window horizon. -/
theorem fp81s21_common_radius (p : Parameters) :
    ∃ δ0 Co co : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧ 0 < co ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 →
        ∀ ρβ : Euc p.d → ℝ, IsThermalEquilibrium p.d p.s p.a p.β ρβ →
          S103nOrbitClaims p.d p.s p.a p.β ρβ δ p.c₁ p.C₁ Co co ∧
          HRS.MS.S104j.S104jHex p.d p.s p.a p.β ρβ δ p.c₁ p.C₁ ∧
          S104bTermRegGen p.d p.s p.a p.β ρβ δ p.c₁ p.C₁ ∧
          ∀ H : ℝ, 0 < H → S103nWindowClause p.d p.s p.a p.β H ρβ δ p.c₁ p.C₁ := by
  have hρ0 : IsThermalEquilibrium p.d p.s p.a p.β
      (thermalDensity p.d p.s p.a p.β) := fp81s21_canonical_thermal p
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  let H0 : HRS.MS.MovLin.Mov2dTh p.d p.s p.β p.a (thermalDensity p.d p.s p.a p.β) :=
    ⟨p.hd, p.hs0, hsd, p.hβ, p.ha, hρ0⟩
  obtain ⟨εo, hεo, Co, co, hco, hOrb⟩ :=
    s103n_orbits_nonlinear' H0 p.c₁ p.C₁
  obtain ⟨εwin, hεwin, hWinReg⟩ := s103d_termReg_small H0 p.c₁ p.C₁
  have hUCsmall := s103d_rhoPrimeUCsmall p.hd p.hs0 hsd p.ha p.hβ
  obtain ⟨εUC, hεUC, hUC⟩ := hUCsmall
    (thermalDensity p.d p.s p.a p.β) hρ0 p.c₁ p.C₁
  obtain ⟨εreg, hεreg, hReg⟩ :=
    HRS.MS.R2WinOrbNL.s104g_termRegGen_of_ex p.hd p.hs0 hsd p.ha p.hβ hρ0 p.c₁ p.C₁
  let δ0 : ℝ := min (1 / 2) (min εo (min εwin (min εUC εreg)))
  have hδ0 : 0 < δ0 := by
    dsimp [δ0]
    exact lt_min (by norm_num) (lt_min hεo (lt_min hεwin (lt_min hεUC hεreg)))
  have hδhalf : δ0 ≤ 1 / 2 := by dsimp [δ0]; exact min_le_left _ _
  have hδorb : δ0 ≤ εo := by
    dsimp [δ0]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hδwin : δ0 ≤ εwin := by
    dsimp [δ0]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδUC : δ0 ≤ εUC := by
    dsimp [δ0]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδreg : δ0 ≤ εreg := by
    dsimp [δ0]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨δ0, Co, co, hδ0, hδhalf, hco, fun δ hδ hδle ρβ hρβ => ?_⟩
  have hδεo : δ ≤ εo := hδle.trans hδorb
  have hδwin' : δ ≤ εwin := hδle.trans hδwin
  have hδUC' : δ ≤ εUC := hδle.trans hδUC
  have hδreg' : δ ≤ εreg := hδle.trans hδreg
  have horb0' : S103nOrbitClaims p.d p.s p.a p.β
      (thermalDensity p.d p.s p.a p.β) δ p.c₁ p.C₁ Co co := by
    exact s103d_orbits_mono hδ hδεo hOrb
  have hhexReg : HRS.MS.S104j.S104jHex p.d p.s p.a p.β
      (thermalDensity p.d p.s p.a p.β) εreg p.c₁ p.C₁ :=
    HRS.MS.S104e.s104e_hex p.hd p.hs0 hsd p.ha p.hβ εreg p.c₁ p.C₁ hρ0
  have htermReg : S104bTermRegGen p.d p.s p.a p.β
      (thermalDensity p.d p.s p.a p.β) δ p.c₁ p.C₁ := by
    have hlarge := hReg εreg hεreg le_rfl hhexReg
    exact HRS.MS.S104j.s104j_termRegGen_mono hρ0 hδreg' hlarge
  have hwindowReg : S103nTermReg p.d p.s p.a p.β
      (thermalDensity p.d p.s p.a p.β) δ p.c₁ p.C₁ :=
    hWinReg δ hδ hδwin' (hUC δ hδ hδUC')
  have hhex : HRS.MS.S104j.S104jHex p.d p.s p.a p.β ρβ δ p.c₁ p.C₁ :=
    HRS.MS.S104e.s104e_hex p.hd p.hs0 hsd p.ha p.hβ δ p.c₁ p.C₁ hρβ
  have heq : ρβ = thermalDensity p.d p.s p.a p.β := by
    rw [HRS.MS.Mov0.mv0_rho_eq p.hd p.hs0 hsd p.ha p.hβ hρβ,
      HRS.MS.Mov0.mv0_rho_eq p.hd p.hs0 hsd p.ha p.hβ hρ0]
  have horb : S103nOrbitClaims p.d p.s p.a p.β ρβ δ p.c₁ p.C₁ Co co := by
    simpa [heq] using horb0'
  have hterm : S104bTermRegGen p.d p.s p.a p.β ρβ δ p.c₁ p.C₁ := by
    simpa [heq] using htermReg
  have hwindowReg' : S103nTermReg p.d p.s p.a p.β ρβ δ p.c₁ p.C₁ := by
    simpa [heq] using hwindowReg
  refine ⟨horb, hhex, hterm, fun H hH => ?_⟩
  exact s103n_windowClause_of_termReg hH horb hwindowReg'

/-- Uniform thermal Poincaré and response constants, together with the fixed-parameter
actual-law density-ratio threshold.  The response bounds use the explicit energy constants
`β η` and `β`; the trajectory's two moving-density comparisons retain the class constant `C₁`. -/
theorem fp81s21_uniform_thermal_package (p : Parameters) :
    ∃ δdens pinf K η gapConst : ℝ,
      0 < δdens ∧ δdens ≤ 1 / 2 ∧ 1 < pinf ∧ 0 < η ∧ η ≤ 1 ∧ 0 < gapConst ∧
      (∀ ρβ : Euc p.d → ℝ, IsThermalEquilibrium p.d p.s p.a p.β ρβ →
        (∀ f : Euc p.d → ℝ,
          ContDiff ℝ 1 f → (∃ Cf, ∀ x, ‖gradient f x‖ ≤ Cf) →
          MemLp f 2 (HRS.Whole.withDensityReal ρβ) →
          gapConst * ProbabilityTheory.variance f (HRS.Whole.withDensityReal ρβ) ≤
            ∫ x, ‖gradient f x‖ ^ 2 ∂(HRS.Whole.withDensityReal ρβ)) ∧
        HRS.MS.S111X2.ResponseForm (HRS.Whole.rieszKernel p.d p.s)
          (HRS.Whole.withDensityReal ρβ) p.β η) ∧
      (∀ {δ : ℝ} (R : Trajectory p δ) (f : Euc p.d → ℝ),
        MemLp f 2 (HRS.Whole.withDensityReal R.ρβ) →
        (p.β * η) * ∫ x, (HRS.Whole.projMean (HRS.Whole.withDensityReal R.ρβ) f x) ^ 2
            ∂(HRS.Whole.withDensityReal R.ρβ) ≤
          p.β * HRS.Whole.susceptibilityCov (rieszKernel p.d p.s)
            (HRS.Whole.withDensityReal R.ρβ) p.β f f ∧
        p.β * HRS.Whole.susceptibilityCov (rieszKernel p.d p.s)
          (HRS.Whole.withDensityReal R.ρβ) p.β f f ≤ p.β * ∫ x,
          (HRS.Whole.projMean (HRS.Whole.withDensityReal R.ρβ) f x) ^ 2
            ∂(HRS.Whole.withDensityReal R.ρβ)) ∧
      (∀ R : Trajectory p δdens, ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N,
        ∀ t : ℝ, 0 ≤ t →
          HasR2ActualDensity p.s p.β pinf K (r26t3_mu R t) (law A.P (A.X t.toNNReal))) ∧
      (∀ {δ : ℝ} (R : Trajectory p δ), ∀ t : ℝ, 0 ≤ t → ∀ x,
        p.C₁⁻¹ * R.ρβ x ≤ R.ρ t x ∧ R.ρ t x ≤ p.C₁ * R.ρβ x) := by
  have hρ0 : IsThermalEquilibrium p.d p.s p.a p.β
      (thermalDensity p.d p.s p.a p.β) := fp81s21_canonical_thermal p
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  obtain ⟨B, hBdef, hGap, hCb⟩ :=
    HRS.MS.Mov0.mv0_gapref p.hd p.hs0 hsd p.ha p.hβ hρ0
  obtain ⟨Mb, hB2⟩ := hCb 2
  obtain ⟨gapConst, hgapPos, hPoincare0⟩ := HRS.MS.Gap.gap_ext hGap (mul_pos p.hβ p.ha) hB2
  obtain ⟨η, hη, hη1, hResponse⟩ :=
    HRS.MS.S111X2.s111x2_thermal_response_forms p.hd p.s p.a p.β p.β
      p.hs0 p.hs p.ha p.hβ p.hβ.le
  obtain ⟨δdens, hδdens, hδdensHalf, pinf, K, hpinf, hActual⟩ :=
    HRS.MS.R26T3.r26t3_actual_density p
  have hThermal : ∀ ρβ : Euc p.d → ℝ,
      IsThermalEquilibrium p.d p.s p.a p.β ρβ →
      (∀ f : Euc p.d → ℝ, ContDiff ℝ 1 f → (∃ Cf, ∀ x, ‖gradient f x‖ ≤ Cf) →
        MemLp f 2 (HRS.Whole.withDensityReal ρβ) →
        gapConst * ProbabilityTheory.variance f (HRS.Whole.withDensityReal ρβ) ≤
          ∫ x, ‖gradient f x‖ ^ 2 ∂(HRS.Whole.withDensityReal ρβ)) ∧
      HRS.MS.S111X2.ResponseForm (HRS.Whole.rieszKernel p.d p.s)
        (HRS.Whole.withDensityReal ρβ) p.β η := by
    intro ρβ hρβ
    have hEq : ρβ = thermalDensity p.d p.s p.a p.β :=
      HRS.MS.Mov0.mv0_rho_eq p.hd p.hs0 hsd p.ha p.hβ hρβ
    have hPoincare : ∀ f : Euc p.d → ℝ, ContDiff ℝ 1 f →
        (∃ Cf, ∀ x, ‖gradient f x‖ ≤ Cf) →
        MemLp f 2 (HRS.Whole.withDensityReal ρβ) →
        gapConst * ProbabilityTheory.variance f (HRS.Whole.withDensityReal ρβ) ≤
          ∫ x, ‖gradient f x‖ ^ 2 ∂(HRS.Whole.withDensityReal ρβ) := by
      intro f hf hgrad hmem
      have hmem0 : MemLp f 2
          (HRS.Whole.withDensityReal (thermalDensity p.d p.s p.a p.β)) := by
        simpa [hEq] using hmem
      have hp0 := hPoincare0 f hf hgrad hmem0
      simpa [hEq] using hp0
    exact ⟨hPoincare, hResponse ρβ hρβ p.β ⟨p.hβ.le, le_rfl⟩⟩
  have hEnergy : ∀ {δ : ℝ} (R : Trajectory p δ) (f : Euc p.d → ℝ),
      MemLp f 2 (HRS.Whole.withDensityReal R.ρβ) →
      (p.β * η) * ∫ x, (HRS.Whole.projMean (HRS.Whole.withDensityReal R.ρβ) f x) ^ 2
          ∂(HRS.Whole.withDensityReal R.ρβ) ≤
        p.β * HRS.Whole.susceptibilityCov (rieszKernel p.d p.s)
          (HRS.Whole.withDensityReal R.ρβ) p.β f f ∧
      p.β * HRS.Whole.susceptibilityCov (rieszKernel p.d p.s)
        (HRS.Whole.withDensityReal R.ρβ) p.β f f ≤ p.β * ∫ x,
        (HRS.Whole.projMean (HRS.Whole.withDensityReal R.ρβ) f x) ^ 2
          ∂(HRS.Whole.withDensityReal R.ρβ) := by
    intro δ R f hf
    have hform := (hResponse R.ρβ R.thermal p.β ⟨p.hβ.le, le_rfl⟩)
    obtain ⟨hlo, hhi⟩ := hform.coercive f hf
    refine ⟨?_, ?_⟩
    · calc
        (p.β * η) * ∫ x, (HRS.Whole.projMean (HRS.Whole.withDensityReal R.ρβ) f x) ^ 2
            ∂(HRS.Whole.withDensityReal R.ρβ) =
          p.β * (η * HRS.MS.S111X2.s111x2_centeredSquare
            (HRS.Whole.withDensityReal R.ρβ) f) := by
              unfold HRS.MS.S111X2.s111x2_centeredSquare
              ring
        _ ≤ p.β * HRS.Whole.susceptibilityCov (rieszKernel p.d p.s)
            (HRS.Whole.withDensityReal R.ρβ) p.β f f :=
          mul_le_mul_of_nonneg_left hlo p.hβ.le
    · calc
        p.β * HRS.Whole.susceptibilityCov (rieszKernel p.d p.s)
            (HRS.Whole.withDensityReal R.ρβ) p.β f f ≤
          p.β * HRS.MS.S111X2.s111x2_centeredSquare
            (HRS.Whole.withDensityReal R.ρβ) f := mul_le_mul_of_nonneg_left hhi p.hβ.le
        _ = p.β * ∫ x,
            (HRS.Whole.projMean (HRS.Whole.withDensityReal R.ρβ) f x) ^ 2
              ∂(HRS.Whole.withDensityReal R.ρβ) := by
                unfold HRS.MS.S111X2.s111x2_centeredSquare
                rfl
  have hRatio : ∀ {δ : ℝ} (R : Trajectory p δ), ∀ t : ℝ, 0 ≤ t → ∀ x,
      p.C₁⁻¹ * R.ρβ x ≤ R.ρ t x ∧ R.ρ t x ≤ p.C₁ * R.ρβ x :=
    fun R t ht x => R.resulting.ratio t ht x
  exact ⟨δdens, pinf, K, η, gapConst, hδdens, hδdensHalf, hpinf, hη, hη1, hgapPos,
    hThermal, hEnergy, hActual, hRatio⟩

#print axioms fp81s21_common_radius
#print axioms fp81s21_uniform_thermal_package

end HRS.Fp81.S21

end
