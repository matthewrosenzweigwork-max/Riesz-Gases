import HRS.MC.E214H4

/-!
# E214H5: `covariance_relaxation`
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.MC.E214H

open HRS HRS.Main HRS.Sec7 HRS.MC.E213Plan

variable {d : ℕ}

theorem covariance_relaxation (S : PreparedData d) (β₀ m T : ℝ) (hE : EdgeworthHyp S β₀ m)
    (hT : 0 < T) (ρβ : Torus d → ℝ) (hρβ : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ)
    (hpair : PairHyp (HRS.MC.E213A.regimeOfPrepared S β₀ hE) T) (hbridge : BridgeHyp S β₀ hE) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ a : ℝ, 0 ≤ a →
      ∀ (ν : Measure (NegSobolev d m)),
        IsCenteredGaussianWithCov m ν (preparedCov d S.s β₀ S.μ0) →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Z₀ : Ω' → NegSobolev d m) (Z : ℝ → Ω' → NegSobolev d m),
        IsPreparedLinear S m (a + T) ν P' Z₀ Z →
      ∀ {Ω'' : Type} [MeasurableSpace Ω''] (P'' : Measure Ω'') [IsProbabilityMeasure P'']
        (Zs : ℝ → Ω'' → NegSobolev d m),
        IsStationaryGaussianField P'' S.s S.β S.hs0 S.hsd S.hβ S.V ρβ m Zs →
        covDist P' P'' (windowPath m T a Z) (windowPath m T 0 Zs) ≤ C * Real.exp (-c * a) := by
  classical
  obtain ⟨Ω, mΩ, P, hP, Y₀, Ys₀, η, ηs, hpd, C₁, κ, hC₁, hκ, hsup⟩ := hpair
  obtain ⟨gd⟩ := HRS.MC.E213U4.exists_gaussData_proof (S := S) (β₀ := β₀) hE
  obtain ⟨CZ, hCZ0, hCZ⟩ := HRS.MC.E213U11.u11_Z_moment gd T hT 2 (by norm_num)
  set A : ℝ := 2 * CZ + 2 * C₁ ^ 2 with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨2 * Real.sqrt A * C₁ + 1, κ, by positivity, hκ, ?_⟩
  intro a ha ν hν Ω' _ P' _ Z₀ Z hZ Ω'' _ P'' _ Zs hZs
  have hrm : rLvl d ≤ m := rLvl_le hE
  have hd : 2 ≤ d := S.hd
  have hlinη : ∀ T' : ℝ, IsLinearFluctuationSolution P S.dyn S.ρ (rLvl d) S.β⁻¹ T' Y₀ η := hpd.2.2.1
  have hlinηs : ∀ T' : ℝ, IsLinearFluctuationSolution P S.dyn
      (fun _ => (HRS.MC.E213A.regimeOfPrepared S β₀ hE).ρβ) (rLvl d) S.β⁻¹ T' Ys₀ ηs := hpd.2.2.2
  have hηG : IsGaussianLimitField S.dyn S.ρ (withDensityReal S.ρ0) β₀ (rLvl d) P η :=
    ⟨Y₀, hpd.1, hlinη⟩
  set X : Ω → PathSpace d m T := fun ω => HRS.MD.EQInterp.epath hrm T (procWin (rLvl d) T a η ω) with hX
  set Y : Ω → PathSpace d m T := fun ω => HRS.MD.EQInterp.epath hrm T (procWin (rLvl d) T a ηs ω) with hY
  have hηm : AEMeasurable (procWin (rLvl d) T a η) P :=
    HRS.MC.Sec7.S7UCU.S7UCU_procWin_aemeasurable P (rLvl d) T hT η a ha
      (fun t => (hlinη (a + T)).meas t) (hlinη (a + T)).cont
  have hηsm : AEMeasurable (procWin (rLvl d) T a ηs) P :=
    HRS.MC.Sec7.S7UCU.S7UCU_procWin_aemeasurable P (rLvl d) T hT ηs a ha
      (fun t => (hlinηs (a + T)).meas t) (hlinηs (a + T)).cont
  have hep := (HRS.MD.EQInterp.epath hrm T : PathSpace d (rLvl d) T →L[ℝ] PathSpace d m T).continuous
  have hXm : AEMeasurable X P := hep.aemeasurable.comp_aemeasurable hηm
  have hYm : AEMeasurable Y P := hep.aemeasurable.comp_aemeasurable hηsm
  -- the prepared window
  have hlawX : law P' (windowPath m T a Z) = law P X := by
    rw [HRS.MC.E213P.e213p_window_law S β₀ m hE (rLvl d) rfl T a hT ha P η hηG ν hν P' Z₀ Z hZ]
    exact (AEMeasurable.map_map_of_aemeasurable hep.aemeasurable hηm)
  obtain ⟨hWm, hZwm, hlawZ, -⟩ := HRS.MC.E213U5.Z_universal_proof gd T hT a ha ν hν P' Z₀ Z hZ
  -- the stationary window
  have hρeq := thermal_eq S β₀ hE ρβ hρβ
  have hst : IsStationaryGaussianField P S.s S.β S.hs0 S.hsd S.hβ S.V ρβ (rLvl d) ηs := by
    rw [hρeq]; exact hbridge P Y₀ Ys₀ η ηs hpd
  have hrpos : (d : ℝ) / 2 < rLvl d := by
    unfold rLvl; have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith
  have hlift := HRS.MD.EQGaussLift.eq_gauss_lift_proof hd S.hs0 S.hsd S.V S.hβ ρβ (rLvl d) m hrpos hrm
    P ηs hst
  have hlaw2 : law P'' (windowPath m T 0 Zs) = law P Y := by
    rw [HRS.MD.EQGaussWindow.eq_gauss_window_law_proof hd S.hs0 S.hsd S.V S.hβ ρβ m T hT.le P'' P Zs
      (fun t ω => NegSobolev.embed m (ηs t ω)) hZs hlift 0 a le_rfl ha]
    refine Measure.map_congr ?_
    filter_upwards [(hlinηs (a + T)).cont] with ω hω
    exact HRS.MC.E213P.e213p_windowPath_embed hrm T a ha ηs ω hω
  -- reduction to a statement about `X, Y` on `P`
  have hWs := (HRS.MD.EQGaussWindow.eqgw_fidi hd S.hs0 S.hsd S.V S.hβ ρβ m T P'' Zs hZs 0 le_rfl).1
  rw [← covDist_of_law_eq hXm hWm hlawX.symm hYm hWs hlaw2.symm]
  -- the estimates
  set ε : ℝ := C₁ * Real.exp (-κ * a) with hε
  have hε0 : 0 ≤ ε := by positivity
  have hexp : Real.exp (-κ * a) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have hεC : ε ≤ C₁ := by
    calc ε ≤ C₁ * 1 := mul_le_mul_of_nonneg_left hexp hC₁.le
      _ = C₁ := mul_one _
  have hε2 : ε ^ 2 ≤ C₁ ^ 2 := pow_le_pow_left₀ hε0 hεC 2
  have hlawXgd : law P X = law gd.P₀ (gd.Zwin T a) := hlawX.symm.trans hlawZ
  obtain ⟨-, hZi, hZb⟩ := hCZ a ha
  have hsq : Continuous fun w : PathSpace d m T => ‖w‖ ^ 2 := by fun_prop
  have hZi' : Integrable (fun ω => ‖gd.Zwin T a ω‖ ^ (2 : ℕ)) gd.P₀ := by
    simpa [Real.rpow_two] using hZi
  have hZb' : ∫ ω, ‖gd.Zwin T a ω‖ ^ (2 : ℕ) ∂gd.P₀ ≤ CZ := by
    simpa [Real.rpow_two] using hZb
  have hXi : Integrable (fun ω => ‖X ω‖ ^ 2) P :=
    integrable_comp_of_law_eq (g := fun w : PathSpace d m T => ‖w‖ ^ 2) hXm hZwm hlawXgd hsq hZi'
  have hXb : ∫ ω, ‖X ω‖ ^ 2 ∂P ≤ CZ := by
    rw [integral_comp_of_law_eq (g := fun w : PathSpace d m T => ‖w‖ ^ 2) hXm hZwm hlawXgd hsq]
    exact hZb'
  -- the difference
  have hD : AEStronglyMeasurable (fun ω => X ω - Y ω) P :=
    hXm.aestronglyMeasurable.sub hYm.aestronglyMeasurable
  have hDsm : AEStronglyMeasurable (fun ω => ‖X ω - Y ω‖ ^ 2) P :=
    (continuous_pow 2).comp_aestronglyMeasurable hD.norm
  have hae : ∀ᵐ ω ∂P, ‖X ω - Y ω‖ₑ ≤ ⨆ t ∈ Icc (0 : ℝ) T, ‖η (a + t) ω - ηs (a + t) ω‖ₑ := by
    filter_upwards [(hlinη (a + T)).cont, (hlinηs (a + T)).cont] with ω h1 h2
    exact enorm_epath_sub_le hrm ha η ηs ω h1 h2
  have hlint : ∫⁻ ω, ‖X ω - Y ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal (ε ^ 2) := by
    calc ∫⁻ ω, ‖X ω - Y ω‖ₑ ^ 2 ∂P
        ≤ ∫⁻ ω, (⨆ t ∈ Icc (0 : ℝ) T, ‖η (a + t) ω - ηs (a + t) ω‖ₑ) ^ (2 : ℝ) ∂P :=
          lintegral_mono_ae (hae.mono fun ω h => by
            rw [ENNReal.rpow_two]; exact pow_le_pow_left' h 2)
      _ ≤ ENNReal.ofReal ((C₁ * Real.exp (-κ * a)) ^ (2 : ℝ)) := hsup a ha
      _ = ENNReal.ofReal (ε ^ 2) := by rw [Real.rpow_two]
  have hDi : Integrable (fun ω => ‖X ω - Y ω‖ ^ 2) P := by
    refine ⟨hDsm, ?_⟩
    have : ∫⁻ ω, ‖‖X ω - Y ω‖ ^ 2‖ₑ ∂P = ∫⁻ ω, ‖X ω - Y ω‖ₑ ^ 2 ∂P := by
      simp only [enorm_pow, enorm_norm]
    unfold HasFiniteIntegral
    rw [this]
    exact lt_of_le_of_lt hlint ENNReal.ofReal_lt_top
  have hDb : ∫ ω, ‖X ω - Y ω‖ ^ 2 ∂P ≤ ε ^ 2 := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω => sq_nonneg _) hDsm]
    refine ENNReal.toReal_le_of_le_ofReal (sq_nonneg ε) ?_
    have : ∫⁻ ω, ENNReal.ofReal (‖X ω - Y ω‖ ^ 2) ∂P = ∫⁻ ω, ‖X ω - Y ω‖ₑ ^ 2 ∂P := by
      refine lintegral_congr fun ω => ?_
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    rw [this]; exact hlint
  -- the second moment of `Y`
  have hYpt : ∀ ω, ‖Y ω‖ ^ 2 ≤ 2 * ‖X ω‖ ^ 2 + 2 * ‖X ω - Y ω‖ ^ 2 := by
    intro ω
    have h1 : ‖Y ω‖ ≤ ‖X ω‖ + ‖X ω - Y ω‖ := by
      calc ‖Y ω‖ = ‖X ω - (X ω - Y ω)‖ := by rw [sub_sub_cancel]
        _ ≤ ‖X ω‖ + ‖X ω - Y ω‖ := norm_sub_le _ _
    have h2 : ‖Y ω‖ ^ 2 ≤ (‖X ω‖ + ‖X ω - Y ω‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg (‖X ω‖ - ‖X ω - Y ω‖)]
  have hYsm : AEStronglyMeasurable (fun ω => ‖Y ω‖ ^ 2) P :=
    (continuous_pow 2).comp_aestronglyMeasurable hYm.aestronglyMeasurable.norm
  have hYi : Integrable (fun ω => ‖Y ω‖ ^ 2) P := by
    refine Integrable.mono' ((hXi.const_mul 2).add (hDi.const_mul 2)) hYsm
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hYpt ω
  have hYb : ∫ ω, ‖Y ω‖ ^ 2 ∂P ≤ A := by
    calc ∫ ω, ‖Y ω‖ ^ 2 ∂P ≤ ∫ ω, (2 * ‖X ω‖ ^ 2 + 2 * ‖X ω - Y ω‖ ^ 2) ∂P :=
          integral_mono hYi ((hXi.const_mul 2).add (hDi.const_mul 2)) hYpt
      _ = 2 * ∫ ω, ‖X ω‖ ^ 2 ∂P + 2 * ∫ ω, ‖X ω - Y ω‖ ^ 2 ∂P := by
          rw [integral_add (hXi.const_mul 2) (hDi.const_mul 2), integral_const_mul,
            integral_const_mul]
      _ ≤ A := by rw [hA]; linarith
  have hXA : ∫ ω, ‖X ω‖ ^ 2 ∂P ≤ A := by rw [hA]; nlinarith [sq_nonneg C₁]
  have key := covDist_le_L2 P X Y hXm.aestronglyMeasurable hYm.aestronglyMeasurable hε0 hXi hYi hDi
    hXA hYb hDb
  refine key.trans ?_
  rw [hε]
  have := Real.exp_pos (-κ * a)
  nlinarith [Real.sqrt_nonneg A]

end HRS.MC.E214H

end
