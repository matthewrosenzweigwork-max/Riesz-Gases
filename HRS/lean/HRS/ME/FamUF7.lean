import HRS.ME.CritDefs
import HRS.ME.CritBures
import HRS.ME.FamUF2
import HRS.ME.EVUD

/-!
# Chunk E, packet F7 (namespace `HRS.ME.FamU`): family forms of the critical defs and the V-uniform Bures bound

Originals and new declarations:
* `Uniform417Fam`, `CritForcingFam`, `CritBurnConclFam`: families of `HRS.ME.Crit.Uniform417`, `HRS.ME.Crit.CritForcing`,
  `HRS.ME.Crit.CritBurnConcl` (HRS/ME/CritDefs.lean). Parameters are those of the originals minus `V`, plus `Bf` last.
  The constant(s) come before `∀ V, Torus.IsSmooth V → (∀ j, Torus.cbNorm j V ≤ Bf j) → …`; the body is copied verbatim.
* `Uniform417Fam.specialize`, `CritForcingFam.specialize`, `CritBurnConclFam.specialize`: a family and one smooth `V` with
  `cbNorm j V ≤ Bf j` give the fixed-`V` original.
* `crit_bures2_uniform_unifV`: V-uniform copy of `HRS.ME.Crit.crit_bures2_uniform` (statement HRS/ME/CritSpec.lean:93;
  proof `crit_bures2_uniform_proof`, HRS/ME/CritBures.lean:112). The constants `C₁, C₂, lam, C` (from `eq_static_linear_unifV`,
  `equilibrium_marginal_L2_unifV`, `exists_thermal_bounds_unifV` with `Bv := Bf 0`, and `crit_lintegral_majorant`, which is V-free)
  are chosen before `V`; `eqstat_thermal_setup_unifV` gives the per-`V` identity `canonicalGibbs = modulatedGibbs`.
  `eqtrace_setup` and `q41_thermal_regular` need only `Torus.IsSmooth V` and are used per `V`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.ME.FamU

section Defs

open HRS HRS.LZ HRS.Uniform HRS.Main HRS.MD.EQ29

variable {d : ℕ}

/-- Family form of `HRS.ME.Crit.Uniform417`: the constant `C` is chosen before the potential `V`, which ranges over the smooth
potentials with `cbNorm j V ≤ Bf j`. -/
def Uniform417Fam (d : ℕ) (hs0 : 0 ≤ (d : ℝ) / 2) (hsd : (d : ℝ) / 2 < d) (βm βp : ℝ) (hβm : 0 < βm)
    (m T : ℝ) (Bf : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : Torus d → ℝ), Torus.IsSmooth V → (∀ j : ℕ, Torus.cbNorm j V ≤ Bf j) →
    ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ : Torus d → ℝ),
    IsThermalDensity (periodicRiesz d ((d : ℝ) / 2)) V β ρβ → Torus.IsSmooth ρβ → (∀ x, 0 < ρβ x) →
    ∀ N : ℕ, 2 ≤ N → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N) (a : ℝ), 0 ≤ a →
      IsStationaryGibbsFlow P ((d : ℝ) / 2) hs0 hsd V β (hβm.trans_le hβ.1) (a + T) X₀ W X →
      ∫⁻ ω, ⨆ t ∈ ratTimes 0 T, ∑' k : NonzeroLattice d,
          ENNReal.ofReal (integratedCenteredForcing (PDE.mfData d ((d : ℝ) / 2) hs0 hsd V β (hβm.trans_le hβ.1)) ρβ P X m k
            (a + t) ω ^ 2) ∂P ≤
        ENNReal.ofReal (C ^ 2 / N)

/-- Family form of `HRS.ME.Crit.CritForcing`: the constant `C` is chosen before the potential `V`. -/
def CritForcingFam (d : ℕ) (hs0 : 0 ≤ (d : ℝ) / 2) (hsd : (d : ℝ) / 2 < d) (βm βp : ℝ) (hβm : 0 < βm)
    (m T : ℝ) (Bf : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : Torus d → ℝ), Torus.IsSmooth V → (∀ j : ℕ, Torus.cbNorm j V ≤ Bf j) →
    ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ : Torus d → ℝ),
    IsThermalDensity (periodicRiesz d ((d : ℝ) / 2)) V β ρβ →
    ∀ N : ℕ, 2 ≤ N → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N) (a : ℝ), 0 ≤ a →
      (∃ q : ℚ, (q : ℝ) = a) →
      IsStationaryGibbsFlow P ((d : ℝ) / 2) hs0 hsd V β (hβm.trans_le hβ.1) (a + T) X₀ W X →
      ∫⁻ ω, (⨆ t ∈ ratTimes a T,
          (coordEnergy m (fun k => statForcingCoord d hs0 hsd V (hβm.trans_le hβ.1) ρβ X k t ω)) ^ (1 / 2 : ℝ)) ^ 2 ∂P ≤
        ENNReal.ofReal (C ^ 2 / N)

/-- Family form of `HRS.ME.Crit.CritBurnConcl`: the constants `C, c` are chosen before the potential `V`. -/
def CritBurnConclFam (d : ℕ) (hs0 : 0 ≤ (d : ℝ) / 2) (hsd : (d : ℝ) / 2 < d) (βm βp : ℝ) (hβm : 0 < βm)
    (m T : ℝ) (Bf : ℕ → ℝ) : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (V : Torus d → ℝ), Torus.IsSmooth V → (∀ j : ℕ, Torus.cbNorm j V ≤ Bf j) →
    ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ : Torus d → ℝ),
    IsThermalDensity (periodicRiesz d ((d : ℝ) / 2)) V β ρβ →
    ∀ a : ℝ, 0 ≤ a → (∃ q : ℚ, (q : ℝ) = a) → ∀ N : ℕ, 2 ≤ N →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
      IsStationaryGibbsFlow P ((d : ℝ) / 2) hs0 hsd V β (hβm.trans_le hβ.1) (a + T) X₀ W X →
    ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      (Z : ℝ → Ω' → NegSobolev d m),
      IsStationaryGaussianField P' ((d : ℝ) / 2) β hs0 hsd (hβm.trans_le hβ.1) V ρβ m Z →
      wassersteinE 2 (law P (Main.windowZeta m T a P X)) (law P' (Main.windowPath m T 0 Z)) ≤
        ENNReal.ofReal (C * (Real.exp (-c * a) + (N : ℝ) ^ (-(1 : ℝ) / 2)))

/-- A family and one smooth potential bounded by `Bf` give `Uniform417` for that potential. -/
theorem Uniform417Fam.specialize {d : ℕ} (hs0 : 0 ≤ (d : ℝ) / 2) (hsd : (d : ℝ) / 2 < d) (βm βp : ℝ) (hβm : 0 < βm)
    (m T : ℝ) (Bf : ℕ → ℝ) (hu : Uniform417Fam d hs0 hsd βm βp hβm m T Bf) (V : Torus d → ℝ)
    (hV : Torus.IsSmooth V) (hVB : ∀ j : ℕ, Torus.cbNorm j V ≤ Bf j) :
    HRS.ME.Crit.Uniform417 d hs0 hsd V βm βp hβm m T := by
  obtain ⟨C, hC, h⟩ := hu
  refine ⟨C, hC, ?_⟩
  intro β hβ ρβ hρ hsm hpos N hN Ω _ P _ X₀ W X a ha hflow
  exact h V hV hVB β hβ ρβ hρ hsm hpos N hN P X₀ W X a ha hflow

/-- A family and one smooth potential bounded by `Bf` give `CritForcing` for that potential. -/
theorem CritForcingFam.specialize {d : ℕ} (hs0 : 0 ≤ (d : ℝ) / 2) (hsd : (d : ℝ) / 2 < d) (βm βp : ℝ) (hβm : 0 < βm)
    (m T : ℝ) (Bf : ℕ → ℝ) (hu : CritForcingFam d hs0 hsd βm βp hβm m T Bf) (V : Torus d → ℝ)
    (hV : Torus.IsSmooth V) (hVB : ∀ j : ℕ, Torus.cbNorm j V ≤ Bf j) :
    HRS.ME.Crit.CritForcing d hs0 hsd V βm βp hβm m T := by
  obtain ⟨C, hC, h⟩ := hu
  refine ⟨C, hC, ?_⟩
  intro β hβ ρβ hρ N hN Ω _ P _ X₀ W X a ha hq hflow
  exact h V hV hVB β hβ ρβ hρ N hN P X₀ W X a ha hq hflow

/-- A family and one smooth potential bounded by `Bf` give `CritBurnConcl` for that potential. -/
theorem CritBurnConclFam.specialize {d : ℕ} (hs0 : 0 ≤ (d : ℝ) / 2) (hsd : (d : ℝ) / 2 < d) (βm βp : ℝ)
    (hβm : 0 < βm) (m T : ℝ) (Bf : ℕ → ℝ) (hu : CritBurnConclFam d hs0 hsd βm βp hβm m T Bf) (V : Torus d → ℝ)
    (hV : Torus.IsSmooth V) (hVB : ∀ j : ℕ, Torus.cbNorm j V ≤ Bf j) :
    HRS.ME.Crit.CritBurnConcl d hs0 hsd V βm βp hβm m T := by
  obtain ⟨C, c, hC, hc, h⟩ := hu
  refine ⟨C, c, hC, hc, ?_⟩
  intro β hβ ρβ hρ a ha hq N hN Ω _ P _ X₀ W X hflow Ω' _ P' _ Z hZ
  exact h V hV hVB β hβ ρβ hρ a ha hq N hN P X₀ W X hflow P' Z hZ

end Defs

section Bures

open HRS HRS.Uniform HRS.Uniform.Q14 HRS.Uniform.Q48c

variable {d : ℕ}

/-- (A2, V-uniform) `E_{ℙ_{N,β}} 𝔟(Σ_N, C̄_β)² ≤ C (N⁻¹ + δ_N²)` with `C` chosen before the potential `V` (bounded by `Bf` in
`cbNorm`), before `β ∈ [βm,βp]` and the thermal density. Copy of `HRS.ME.Crit.crit_bures2_uniform` (proof of
`HRS.ME.CritBures.crit_bures2_uniform_proof`) with `eq_static_linear_unifV`, `equilibrium_marginal_L2_unifV`,
`eqstat_thermal_setup_unifV`, `exists_thermal_bounds_unifV` in place of their fixed-`V` originals. -/
theorem crit_bures2_uniform_unifV (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp) (m : ℝ) (hm : (d : ℝ) + 3 ≤ m) (Bf : ℕ → ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ V : Torus d → ℝ, Torus.IsSmooth V → (∀ j : ℕ, Torus.cbNorm j V ≤ Bf j) →
      ∀ β : ℝ, β ∈ Set.Icc βm βp → ∀ ρβ : Torus d → ℝ,
      IsThermalDensity (periodicRiesz d s) V β ρβ → ∀ N : ℕ, 2 ≤ N →
      ∫⁻ X, ENNReal.ofReal (bures2 (covForm m β⁻¹ (empirical X)) (covForm m β⁻¹ (withDensityReal ρβ)))
          ∂(canonicalGibbs (periodicRiesz d s) V N β) ≤
        ENNReal.ofReal (C * ((N : ℝ)⁻¹ + deltaN d s N ^ 2)) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C₁, hC₁, hlin⟩ := eq_static_linear_unifV hd hs0 hsd βm βp hβm hββ Bf
  obtain ⟨C₂, hC₂, hmargU⟩ := equilibrium_marginal_L2_unifV hd hs0 hsd βm βp hβm hββ Bf
  obtain ⟨Lam, hLam⟩ := eqstat_thermal_setup_unifV hd hs0 hsd βm βp hβm hββ Bf
  obtain ⟨lam, Lam', hlam, hb⟩ :=
    HRS.ME.EVU.exists_thermal_bounds_unifV hd1 s hs0 hsd βm βp hβm hββ (Bf 0)
  obtain ⟨C, hC0, hCU⟩ := HRS.ME.CritBures.crit_lintegral_majorant hm (inv_pos.2 hβm) lam hlam (max C₁ C₂)
  have hm1 : (d : ℝ) / 2 + 2 < m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  refine ⟨C + 1, by linarith, fun V hV hVB β hβ ρβ hρ N hN => ?_⟩
  have hVc : Continuous V :=
    HRS.PDE.MFAux.continuous_of_isCk (ContDiff.of_le
      (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift V) from hV) (by exact_mod_cast le_top))
  have hVb : ∀ x, |V x| ≤ Bf 0 := fun x => (HRS.ME.FamU.abs_le_cbNorm_zero hV x).trans (hVB 0)
  have hβ0 : 0 < β := lt_of_lt_of_le hβm hβ.1
  have hq : 0 < β⁻¹ := inv_pos.2 hβ0
  have hqle : β⁻¹ ≤ βm⁻¹ := inv_anti₀ hβm hβ.1
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  obtain ⟨hρc, hρp, hPr⟩ := HRS.MD.EQTrace.eqtrace_setup hd hs0 hsd V hV βm βp hβm hββ β hβ ρβ hρ N hN
  haveI := hPr
  obtain ⟨hpos, -⟩ := HRS.Q41.q41_thermal_regular hd hs0 hsd hβ0 hV hρ
  have hcρ : ∀ x, lam ≤ ρβ x := fun x => (hb V hVc hVb β hβ ρβ hρ hρc hpos x).1
  obtain ⟨-, -, hP⟩ := hLam V hV hVB β hβ ρβ hρ
  have hPm : canonicalGibbs (periodicRiesz d s) V N β =
      modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρβ) := hP N
  have hex : IsExchangeable (canonicalGibbs (periodicRiesz d s) V N β) := by
    rw [hPm]; exact modulatedGibbs_isExchangeable _ _ _ (fun x => periodicRiesz_neg x)
  obtain ⟨hac, hL2⟩ := hmargU V hV hVB β hβ ρβ hρ N hN
  have hδ0 : 0 ≤ deltaN d s N :=
    (inv_nonneg.2 hN0.le).trans (HRS.MarginalAux.inv_le_deltaN (d := d) hs0 N hN1)
  haveI hP1 : IsProbabilityMeasure (withDensityReal ρβ) := isProb_withDensityReal hρp
  set P := canonicalGibbs (periodicRiesz d s) V N β with hPdef
  -- variance hypothesis with the V-uniform constant `max C₁ C₂`
  have hvar : ∀ f : Torus d → ℝ, Measurable f → MemLp f 2 (withDensityReal ρβ) →
      evariance (fun x : Config d N => pair (empirical x) f) P ≤
        ENNReal.ofReal (max C₁ C₂ * (N : ℝ)⁻¹ * ∫ x, f x ^ 2 ∂(withDensityReal ρβ)) := by
    intro f hf hmem
    refine (hlin V hV hVB β hβ ρβ hρ N hN f hf hmem).trans (ENNReal.ofReal_le_ofReal ?_)
    have hI : 0 ≤ ∫ x, f x ^ 2 ∂(withDensityReal ρβ) := integral_nonneg fun x => sq_nonneg _
    have h1 : C₁ * (N : ℝ)⁻¹ ≤ max C₁ C₂ * (N : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (inv_nonneg.2 hN0.le)
    exact mul_le_mul_of_nonneg_right h1 hI
  -- the marginal: `(1/N) ∑ law(X_i) = firstMarginal = (dm/dμ) μ`
  have hmeanEq : meanEmpirical P = firstMarginal P := meanEmpirical_eq_firstMarginal P hex hN1
  haveI hFMp : IsProbabilityMeasure (firstMarginal P) := by
    rw [← hmeanEq]; exact isProbabilityMeasure_meanEmpirical P hN1
  have hsum : (N : ℝ≥0∞)⁻¹ • ∑ i : Fin N, P.map (fun x : Config d N => x i) = firstMarginal P :=
    (meanEmpirical_eq_sum P).symm.trans hmeanEq
  haveI hSF : SigmaFinite (withDensityReal ρβ) := inferInstance
  haveI hSF' : SFinite (firstMarginal P) := inferInstance
  have hwd : (withDensityReal ρβ).withDensity (fun x => ENNReal.ofReal
      ((firstMarginal P).rnDeriv (withDensityReal ρβ) x).toReal) = firstMarginal P := by
    calc (withDensityReal ρβ).withDensity (fun x => ENNReal.ofReal
          ((firstMarginal P).rnDeriv (withDensityReal ρβ) x).toReal)
        = (withDensityReal ρβ).withDensity ((firstMarginal P).rnDeriv (withDensityReal ρβ)) := by
          refine withDensity_congr_ae ?_
          filter_upwards [Measure.rnDeriv_lt_top (firstMarginal P) (withDensityReal ρβ)] with x hx
          rw [ENNReal.ofReal_toReal hx.ne]
      _ = firstMarginal P := Measure.withDensity_rnDeriv_eq _ _ hac
  have hmeas : Measurable (fun y => ((firstMarginal P).rnDeriv (withDensityReal ρβ) y).toReal) :=
    (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hmarg' : (N : ℝ≥0∞)⁻¹ • ∑ i : Fin N, P.map (fun x : Config d N => x i) =
      (withDensityReal ρβ).withDensity fun x =>
        ENNReal.ofReal ((fun y => ((firstMarginal P).rnDeriv (withDensityReal ρβ) y).toReal) x) :=
    hsum.trans hwd.symm
  have hgL2 : ∫⁻ x, ‖(fun y => ((firstMarginal P).rnDeriv (withDensityReal ρβ) y).toReal) x - 1‖ₑ ^ 2
      ∂(withDensityReal ρβ) ≤ ENNReal.ofReal ((max C₁ C₂ * deltaN d s N) ^ 2) := by
    set F : Torus d → ℝ := fun y => ((firstMarginal P).rnDeriv (withDensityReal ρβ) y).toReal - 1 with hF
    have hmeasF : AEStronglyMeasurable F (withDensityReal ρβ) :=
      (hmeas.sub measurable_const).aestronglyMeasurable
    have h2 := eLpNorm_nnreal_pow_eq_lintegral (μ := withDensityReal ρβ) (f := F) (p := 2)
      (by norm_num) hmeasF
    norm_num [ENNReal.rpow_two] at h2
    have hL2' : eLpNorm F 2 (withDensityReal ρβ) ≤ ENNReal.ofReal (C₂ * deltaN d s N) := hL2
    calc ∫⁻ x, ‖(fun y => ((firstMarginal P).rnDeriv (withDensityReal ρβ) y).toReal) x - 1‖ₑ ^ 2
          ∂(withDensityReal ρβ)
        = ∫⁻ x, ‖F x‖ₑ ^ 2 ∂(withDensityReal ρβ) := rfl
      _ = eLpNorm F 2 (withDensityReal ρβ) ^ 2 := h2.symm
      _ ≤ (ENNReal.ofReal (C₂ * deltaN d s N)) ^ 2 := pow_le_pow_left₀ zero_le hL2' 2
      _ = ENNReal.ofReal ((C₂ * deltaN d s N) ^ 2) := by
          rw [ENNReal.ofReal_pow (mul_nonneg hC₂.le hδ0)]
      _ ≤ ENNReal.ofReal ((max C₁ C₂ * deltaN d s N) ^ 2) :=
          ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (mul_nonneg hC₂.le hδ0)
            (mul_le_mul_of_nonneg_right (le_max_right _ _) hδ0) 2)
  have hmajor := hCU β⁻¹ hq hqle hρc hP1 N hN1 (deltaN d s N) P
    (fun y => ((firstMarginal P).rnDeriv (withDensityReal ρβ) y).toReal) hmeas hmarg' hgL2 hvar
  have hX : (0 : ℝ) ≤ (N : ℝ)⁻¹ + deltaN d s N ^ 2 := by positivity
  calc ∫⁻ X, ENNReal.ofReal (bures2 (covForm m β⁻¹ (empirical X)) (covForm m β⁻¹ (withDensityReal ρβ))) ∂P
      ≤ ∫⁻ X, majorant d m β⁻¹ lam ρβ X ∂P :=
        lintegral_mono fun X => bures2_pointwise hm1 hq hρc hlam hcρ hN1 X
    _ ≤ ENNReal.ofReal (C * ((N : ℝ)⁻¹ + deltaN d s N ^ 2)) := hmajor
    _ ≤ ENNReal.ofReal ((C + 1) * ((N : ℝ)⁻¹ + deltaN d s N ^ 2)) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (by linarith) hX)

end Bures

end HRS.ME.FamU

end
