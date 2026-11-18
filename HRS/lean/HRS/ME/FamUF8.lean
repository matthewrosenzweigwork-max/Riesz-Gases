import HRS.ME.FamUF6
import HRS.ME.CritUnifDefs

/-!
# Chunk E, packet F8 (namespace `HRS.ME.FamU`): uniform mode package, family definitions

Originals and new declarations:
* `HRS.ME.unifModePackage_gen` (`HRS/ME/NfUPU13b.lean:26`) becomes `unifModePackage_genV` in family form: the constant
  `C` is chosen before the potential `V` (bounded by `Bf` in `cbNorm`), before `β ∈ [βm, βp]` and the thermal density.
  The two constants `Cpp` (`pair_poisson_unif_thermal_unifV`, FamUF5) and `Cnf` (`normal_form_unif_thermalV`, FamUF6) are
  chosen first; the proof is the body of `mode_package_proof` (`HRS/ME/Mode417.lean:238`) with `V` introduced afterwards.
* `unifModePackageFam`: the family at `s = d/2`, from `unifModePackage_genV`.
* `UnifModePackageFam` (family of `HRS.ME.Crit.UnifModePackage`, HRS/ME/CritUnifDefs.lean:53) and
  `UnifModePackageFam.specialize` (fixed smooth `V` with `cbNorm j V ≤ Bf j` gives `HRS.ME.Crit.UnifModePackage`).
* `UnifModeForcingFam` (family of `HRS.ME.Crit.UnifModeForcing`, HRS/ME/CritUnifDefs.lean:76) and
  `UnifModeForcingFam.specialize`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ME.FamU

open HRS HRS.LZ HRS.Uniform HRS.Main

variable {d : ℕ}

/-- Family form of `HRS.ME.Crit.UnifModePackage` (`mode_package_proof` at `s = d/2`): the constant `C` is chosen before
the smooth potential `V` (with `cbNorm j V ≤ Bf j`), before `β ∈ [βm, βp]` and the thermal density. -/
def UnifModePackageFam (d : ℕ) (hd : 2 ≤ d) (βm βp : ℝ) (hβm : 0 < βm) (Bf : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : Torus d → ℝ), Torus.IsSmooth V → (∀ j : ℕ, Torus.cbNorm j V ≤ Bf j) →
    ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ : Torus d → ℝ),
    IsThermalDensity (periodicRiesz d ((d : ℝ) / 2)) V β ρβ → Torus.IsSmooth ρβ → (∀ x, 0 < ρβ x) →
    ∀ (N : ℕ), 2 ≤ N → ∀ f : Torus d → ℝ, Torus.IsSmooth f →
      ∃ F G E : Config d N → ℝ,
        Measurable F ∧ Measurable G ∧ Measurable E ∧
        IsLZTest (canonicalGibbs (periodicRiesz d ((d : ℝ) / 2)) V N β) F ∧
        ContDiffOn ℝ 1 (configLift (fun _ => F) 0) (coverFree d N) ∧
        MD.DOM.IsInClosedGenerator d ((d : ℝ) / 2) V β (canonicalGibbs (periodicRiesz d ((d : ℝ) / 2)) V N β) F G ∧
        ∫ Y, F Y ∂(canonicalGibbs (periodicRiesz d ((d : ℝ) / 2)) V N β) = 0 ∧
        (∀ X : Config d N, X ∉ collisionSet d N →
          Real.sqrt N / 2 * centeredUnder (canonicalGibbs (periodicRiesz d ((d : ℝ) / 2)) V N β)
              (quadStat (hTransport d ((d : ℝ) / 2) f) (withDensityReal ρβ)) X = -G X + E X) ∧
        ∫⁻ Y, ENNReal.ofReal (F Y ^ 2) ∂(canonicalGibbs (periodicRiesz d ((d : ℝ) / 2)) V N β) ≤
          ENNReal.ofReal ((C * posSeminorm (8 * d + 80) f) ^ 2 / N) ∧
        ∫⁻ Y, ENNReal.ofReal (E Y ^ 2) ∂(canonicalGibbs (periodicRiesz d ((d : ℝ) / 2)) V N β) ≤
          ENNReal.ofReal ((C * posSeminorm (8 * d + 80) f) ^ 2 / N) ∧
        ∫⁻ Y, ∑ i, ‖configGrad F Y i‖ₑ ^ 2 ∂(canonicalGibbs (periodicRiesz d ((d : ℝ) / 2)) V N β) ≤
          ENNReal.ofReal ((C * posSeminorm (8 * d + 80) f) ^ 2 / N) ∧
        ∫⁻ Y, ENNReal.ofReal (configGradSq F Y) ∂(canonicalGibbs (periodicRiesz d ((d : ℝ) / 2)) V N β) ≤
          ENNReal.ofReal ((C * posSeminorm (8 * d + 80) f) ^ 2 / N)

/-- Family form of `HRS.ME.Crit.UnifModeForcing` (`mode_forcing_bound_proof` at `s = d/2`): the constant `C` is chosen
before the smooth potential `V` (with `cbNorm j V ≤ Bf j`), before `β ∈ [βm, βp]` and the thermal density. -/
def UnifModeForcingFam (d : ℕ) (hs0 : 0 ≤ (d : ℝ) / 2) (hsd : (d : ℝ) / 2 < d) (βm βp : ℝ) (hβm : 0 < βm)
    (c T : ℝ) (Bf : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : Torus d → ℝ), Torus.IsSmooth V → (∀ j : ℕ, Torus.cbNorm j V ≤ Bf j) →
    ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ : Torus d → ℝ),
    IsThermalDensity (periodicRiesz d ((d : ℝ) / 2)) V β ρβ → Torus.IsSmooth ρβ → (∀ x, 0 < ρβ x) →
    ∀ {N : ℕ} (hN : 2 ≤ N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d))
      (X : ℝ≥0 → Ω → Config d N) (a : ℝ) (ha : 0 ≤ a)
      (hflow : IsStationaryGibbsFlow P ((d : ℝ) / 2) hs0 hsd V β (hβm.trans_le hβ.1) (a + T) X₀ W X)
      (l : NonzeroLattice d) (Γ : ℝ) (hΓ : 0 ≤ Γ) (γ γ' : ℝ → ℝ)
      (hγ : ∀ x, 0 ≤ x → HasDerivWithinAt γ (γ' x) (Set.Ici 0) x) (hγ' : ContinuousOn γ' (Set.Ici 0))
      (hbd : ∀ v, 0 ≤ v → |γ v| ≤ Γ * Real.exp (-c * v) ∧ |γ' v| ≤ Γ * Real.exp (-c * v)),
      ∫⁻ ω, ⨆ t ∈ ratTimes 0 T, ENNReal.ofReal
          ((∫ r in (0 : ℝ)..(a + t), γ (a + t - r) *
              forcingStat ((d : ℝ) / 2) V β ρβ (Torus.realMode l) (X r.toNNReal ω)) ^ 2) ∂P ≤
        ENNReal.ofReal (C * Γ ^ 2 * Lattice.jp l.1 ^ (2 * (8 * d + 80)) / N)

/-- **F8.1 (V-uniform copy of `unifModePackage_gen`, family form).** The fixed data are `d hd s hcrit βm βp hβm hββ` and
the bound `Bf` of the `C^j` norms of `V`. The constant `C` is chosen before `V`, `β`, `ρβ`; the constants `Cpp` (pair
Poisson, `pair_poisson_unif_thermal_unifV`) and `Cnf` (normal form, `normal_form_unif_thermalV`) are chosen before `V`. -/
theorem unifModePackage_genV (hd : 2 ≤ d) {s : ℝ} (hcrit : s = d / 2) (βm βp : ℝ) (hβm : 0 < βm)
    (hββ : βm ≤ βp) (Bf : ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : Torus d → ℝ), Torus.IsSmooth V → (∀ j : ℕ, Torus.cbNorm j V ≤ Bf j) →
    ∀ β ∈ Set.Icc βm βp, ∀ (ρβ : Torus d → ℝ),
      IsThermalDensity (periodicRiesz d s) V β ρβ → Torus.IsSmooth ρβ → (∀ x, 0 < ρβ x) →
      ∀ (N : ℕ), 2 ≤ N → ∀ f : Torus d → ℝ, Torus.IsSmooth f →
      ∃ F G E : Config d N → ℝ,
        Measurable F ∧ Measurable G ∧ Measurable E ∧
        IsLZTest (canonicalGibbs (periodicRiesz d s) V N β) F ∧
        ContDiffOn ℝ 1 (configLift (fun _ => F) 0) (coverFree d N) ∧
        MD.DOM.IsInClosedGenerator d s V β (canonicalGibbs (periodicRiesz d s) V N β) F G ∧
        ∫ Y, F Y ∂(canonicalGibbs (periodicRiesz d s) V N β) = 0 ∧
        (∀ X : Config d N, X ∉ collisionSet d N →
          Real.sqrt N / 2 * centeredUnder (canonicalGibbs (periodicRiesz d s) V N β)
              (quadStat (hTransport d s f) (withDensityReal ρβ)) X = -G X + E X) ∧
        ∫⁻ Y, ENNReal.ofReal (F Y ^ 2) ∂(canonicalGibbs (periodicRiesz d s) V N β) ≤
          ENNReal.ofReal ((C * posSeminorm (8 * d + 80) f) ^ 2 / N) ∧
        ∫⁻ Y, ENNReal.ofReal (E Y ^ 2) ∂(canonicalGibbs (periodicRiesz d s) V N β) ≤
          ENNReal.ofReal ((C * posSeminorm (8 * d + 80) f) ^ 2 / N) ∧
        ∫⁻ Y, ∑ i, ‖configGrad F Y i‖ₑ ^ 2 ∂(canonicalGibbs (periodicRiesz d s) V N β) ≤
          ENNReal.ofReal ((C * posSeminorm (8 * d + 80) f) ^ 2 / N) ∧
        ∫⁻ Y, ENNReal.ofReal (configGradSq F Y) ∂(canonicalGibbs (periodicRiesz d s) V N β) ≤
          ENNReal.ofReal ((C * posSeminorm (8 * d + 80) f) ^ 2 / N) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by rw [hcrit]; linarith
  have hsd : s < d := by rw [hcrit]; linarith
  obtain ⟨Cpp, hCpp0, hPPu⟩ :=
    HRS.ME.FamU.pair_poisson_unif_thermal_unifV hd hcrit hs0 hsd βm βp hβm hββ Bf
  obtain ⟨Cnf, hNF⟩ := HRS.ME.FamU.normal_form_unif_thermalV hd hcrit βm βp hβm hββ Bf
  obtain ⟨c0, hc0def⟩ : ∃ c0 : ℝ, c0 = max Cnf 0 := ⟨_, rfl⟩
  have hc0 : 0 ≤ c0 := hc0def ▸ le_max_right _ _
  have hCnf : Cnf ≤ c0 := hc0def ▸ le_max_left _ _
  refine ⟨3 * c0 * (|Cpp| + 1), mul_nonneg (mul_nonneg (by norm_num) hc0) (by positivity),
    fun V hV hVB β hβI ρβ hρβ hρS hρpos N hN f hf => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβI.1
  have hρs : SmoothPosDensity ρβ := ⟨hρβ.1, hρS, hρpos⟩
  obtain ⟨Ψ, -, hPP⟩ := hPPu V hV hVB β hβI ρβ hρβ hρS hρpos
  have hdom := HRS.MD.DOMProof.normal_form_domain_proof hd hcrit β hβ V hV ρβ hρβ hρs
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  haveI : IsProbabilityMeasure (canonicalGibbs (periodicRiesz d s) V N β) :=
    Q84d.q84d_isProb hd hcrit hV hβ hN1 (N := N)
  obtain ⟨hψ, -, -⟩ := hPP f hf
  obtain ⟨hQint, hFint, herrint, hid, hbound⟩ := hNF V hV hVB β hβI ρβ hρβ hρS hρpos f _ (Ψ f) hf hψ N hN
  have hdomN := hdom f _ (Ψ f) hf hψ N hN
  have hK0 : 0 ≤ Cpp * posSeminorm (8 * d + 80) f := Q84d.q84d_K_nonneg hd hcrit hψ
  have hP0 : 0 ≤ posSeminorm (8 * d + 80) f := Q84d.q84d_posSeminorm_nonneg _ f
  generalize hP : posSeminorm (8 * d + 80) f = P at hP0 hbound hψ hdomN hK0 ⊢
  generalize hK : Cpp * P = K₁ at hK0 hbound hψ hdomN
  set μ := canonicalGibbs (periodicRiesz d s) V N β with hμ
  have hac : μ ≪ (volume : Measure (Config d N)) := Q84d.q84d_gibbs_ac
  have hae : ∀ᵐ X ∂μ, X ∉ collisionSet d N :=
    hac.ae_le (Q84d.q84d_ae_not_collision (d := d) (N := N) (by omega))
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (N : ℝ) ^ (-(1 / 2 : ℝ)) := ⟨_, rfl⟩
  rw [← hr] at hbound
  have hr0 : 0 ≤ r := hr ▸ Real.rpow_nonneg hNpos.le _
  have hKP0 : 0 ≤ K₁ + P := by linarith
  have hKP : K₁ + P ≤ (|Cpp| + 1) * P := by
    rw [← hK]; nlinarith [mul_le_mul_of_nonneg_right (le_abs_self Cpp) hP0]
  obtain ⟨B0, hB0⟩ : ∃ B : ℝ, B = c0 * (K₁ + P) * r := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = 3 * c0 * (|Cpp| + 1) * P * r := ⟨_, rfl⟩
  have hB0nn : 0 ≤ B0 := by rw [hB0]; exact mul_nonneg (mul_nonneg hc0 hKP0) hr0
  have hMB : 3 * B0 ≤ M := by
    rw [hB0, hM]
    have h1 : (K₁ + P) * r ≤ ((|Cpp| + 1) * P) * r := mul_le_mul_of_nonneg_right hKP hr0
    have h2 := mul_le_mul_of_nonneg_left h1 hc0
    nlinarith [h2]
  have hB0le : B0 ≤ M := by linarith
  have hM0 : 0 ≤ M := by linarith
  have hbB : ENNReal.ofReal (Cnf * (K₁ + P) * r) ≤ ENNReal.ofReal B0 := by
    apply ENNReal.ofReal_le_ofReal
    rw [hB0]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCnf hKP0) hr0
  have hsum := hbound.trans hbB
  -- the four terms of the normal-form bound
  have tA : eLpNorm (centeredUnder μ (Fstat (N := N) (Ψ f))) 2 μ ≤ ENNReal.ofReal B0 :=
    ((le_self_add.trans le_self_add).trans le_self_add).trans hsum
  have tB : (∫⁻ X, ∑ i, ‖configGrad (Fstat (N := N) (Ψ f)) X i‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal B0 :=
    ((le_add_self.trans le_self_add).trans le_self_add).trans hsum
  have tC : eLpNorm (centeredUnder μ (errStat d s ρβ (N := N) (Ψ f))) 2 μ ≤ ENNReal.ofReal B0 :=
    (le_add_self.trans le_self_add).trans hsum
  have tD : ENNReal.ofReal (1 / (N : ℝ)) * eLpNorm (fun X : Config d N => Real.sqrt N *
      centeredUnder μ (fun Y : Config d N => (1 / (N : ℝ)) * ∑ i, aCoef d s ρβ f (Y i)) X) 2 μ ≤
      ENNReal.ofReal B0 :=
    le_add_self.trans hsum
  -- the constant
  have hMsq : M ^ 2 = (3 * c0 * (|Cpp| + 1) * P) ^ 2 / N := by
    rw [hM, mul_pow, hr, m417_rpow_sq N hNpos]
    ring
  rw [← hMsq]
  have tB' : ∫⁻ X, ∑ i, ‖configGrad (Fstat (N := N) (Ψ f)) X i‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (M ^ 2) :=
    (m417_sq_of_half hB0nn tB).trans (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hB0nn hB0le 2))
  -- the witnesses
  obtain ⟨F, hF⟩ : ∃ F : Config d N → ℝ, F = centeredUnder μ (Fstat (N := N) (Ψ f)) := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : Config d N → ℝ,
      G = (collisionSet d N)ᶜ.indicator (particleGen d s V β (Fstat (N := N) (Ψ f))) := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : Config d N → ℝ, E = fun X => Real.sqrt N / 2 *
      centeredUnder μ (quadStat (hTransport d s f) (withDensityReal ρβ)) X + G X := ⟨_, rfl⟩
  -- measurability
  have hFm : Measurable F := by
    rw [hF]; exact (Q84e.q84e_measurable_Fstat hψ.measurable).sub measurable_const
  have hGm : Measurable G := by
    rw [hG]; exact m417_measurable_G hsd V β (Ψ f) hψ.measurable hψ.size.smooth
  have hcqm : Measurable (fun X : Config d N =>
      centeredUnder μ (quadStat (hTransport d s f) (withDensityReal ρβ)) X) :=
    (HRS.Quad.measurable_quadStat (h := hTransport d s f)
      (HRS.LocalDivAux.measurable_hTransport hsd hf) (withDensityReal ρβ)).sub measurable_const
  have hEm : Measurable E := by
    rw [hE]; exact (hcqm.const_mul _).add hGm
  -- regularity of F
  have hFcd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (configLift (fun _ => F) 0) (coverFree d N) := by
    rw [hF]; exact (m417_contDiffOn_Fstat (N := N) (Ψ f) hψ.size.smooth).sub contDiffOn_const
  have hcd1 : ContDiffOn ℝ 1 (configLift (fun _ => F) 0) (coverFree d N) :=
    hFcd.of_le (by exact_mod_cast le_top)
  have hdiff : ∀ X : Config d N, X ∉ collisionSet d N →
      DifferentiableAt ℝ (configLift (fun _ => F) 0) (fun k => Torus.rep (X k)) := fun X hX =>
    (hFcd.contDiffAt ((m417_isOpen_coverFree N).mem_nhds (m417_rep_mem X hX))).differentiableAt
      (by simp)
  -- energy
  have hconf : ∀ X : Config d N, ∀ i : Fin N,
      configGrad F X i = configGrad (Fstat (N := N) (Ψ f)) X i := by
    intro X i; rw [hF]; exact m417_configGrad_sub_const _ _ X i
  have hsumF : ∀ᵐ X ∂μ, ENNReal.ofReal (configGradSq F X) = ∑ i, ‖configGrad F X i‖ₑ ^ 2 := by
    filter_upwards [hae] with X hX
    exact m417_ofReal_configGradSq F X hX (hdiff X hX)
  have hLint : ∫⁻ X, ENNReal.ofReal (configGradSq F X) ∂μ ≤ ENNReal.ofReal (M ^ 2) := by
    rw [lintegral_congr_ae hsumF]
    simp_rw [hconf]
    exact tB'
  have hnn : ∀ X, ‖configGradSq F X‖ₑ = ENNReal.ofReal (configGradSq F X) :=
    fun X => Real.enorm_eq_ofReal (m417_configGradSq_nonneg F X)
  have hen : Integrable (configGradSq F) μ := by
    refine ⟨(m417_measurable_configGradSq F).aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    simp_rw [hnn]
    exact lt_of_le_of_lt hLint ENNReal.ofReal_lt_top
  -- the `L²` bounds
  have tF : eLpNorm F 2 μ ≤ ENNReal.ofReal M := by
    rw [hF]; exact tA.trans (ENNReal.ofReal_le_ofReal hB0le)
  have bF : ∫⁻ Y, ENNReal.ofReal (F Y ^ 2) ∂μ ≤ ENNReal.ofReal (M ^ 2) :=
    m417_sq_bound F hM0 hFm.aestronglyMeasurable tF
  -- the error statistic
  have hA1 : Measurable (aCoef d s ρβ f) := HRS.Q84d.q84d_measurable_aCoef hsd hρs.density hf
  have hζ0 : Measurable (fun Y : Config d N => (1 / (N : ℝ)) * ∑ i, aCoef d s ρβ f (Y i)) :=
    measurable_const.mul (Finset.measurable_sum _ fun i _ => hA1.comp (measurable_pi_apply i))
  have hgζm : Measurable (fun X : Config d N => Real.sqrt N *
      centeredUnder μ (fun Y : Config d N => (1 / (N : ℝ)) * ∑ i, aCoef d s ρβ f (Y i)) X) :=
    measurable_const.mul (hζ0.sub measurable_const)
  have hcen : AEStronglyMeasurable (fun X : Config d N =>
      centeredUnder μ (errStat d s ρβ (N := N) (Ψ f)) X) μ :=
    herrint.aestronglyMeasurable.sub aestronglyMeasurable_const
  have hz2 : AEStronglyMeasurable (fun X : Config d N =>
      (2 / (N : ℝ)) * (Real.sqrt N * centeredUnder μ
        (fun Y : Config d N => (1 / (N : ℝ)) * ∑ i, aCoef d s ρβ f (Y i)) X)) μ :=
    ((measurable_const.mul hgζm)).aestronglyMeasurable
  have hEeq : E =ᵐ[μ] fun X : Config d N => centeredUnder μ (errStat d s ρβ (N := N) (Ψ f)) X -
      (2 / (N : ℝ)) * (Real.sqrt N * centeredUnder μ
        (fun Y : Config d N => (1 / (N : ℝ)) * ∑ i, aCoef d s ρβ f (Y i)) X) := by
    filter_upwards [hae] with X hX
    have h1 := hid X hX
    simp only [hE, hG]
    rw [Set.indicator_of_mem (show X ∈ (collisionSet d N)ᶜ from hX)]
    linarith [h1]
  have hsub : eLpNorm (fun X : Config d N => centeredUnder μ (errStat d s ρβ (N := N) (Ψ f)) X -
      (2 / (N : ℝ)) * (Real.sqrt N * centeredUnder μ
        (fun Y : Config d N => (1 / (N : ℝ)) * ∑ i, aCoef d s ρβ f (Y i)) X)) 2 μ ≤
      eLpNorm (fun X : Config d N => centeredUnder μ (errStat d s ρβ (N := N) (Ψ f)) X) 2 μ +
      eLpNorm (fun X : Config d N => (2 / (N : ℝ)) * (Real.sqrt N * centeredUnder μ
        (fun Y : Config d N => (1 / (N : ℝ)) * ∑ i, aCoef d s ρβ f (Y i)) X)) 2 μ :=
    eLpNorm_sub_le (by norm_num)
  have hc2 : eLpNorm (fun X : Config d N => (2 / (N : ℝ)) * (Real.sqrt N * centeredUnder μ
        (fun Y : Config d N => (1 / (N : ℝ)) * ∑ i, aCoef d s ρβ f (Y i)) X)) 2 μ =
      2 * (ENNReal.ofReal (1 / (N : ℝ)) * eLpNorm (fun X : Config d N => Real.sqrt N *
        centeredUnder μ (fun Y : Config d N => (1 / (N : ℝ)) * ∑ i, aCoef d s ρβ f (Y i)) X) 2 μ) := by
    rw [show (fun X : Config d N => (2 / (N : ℝ)) * (Real.sqrt N * centeredUnder μ
        (fun Y : Config d N => (1 / (N : ℝ)) * ∑ i, aCoef d s ρβ f (Y i)) X)) =
        (2 / (N : ℝ)) • (fun X : Config d N => Real.sqrt N * centeredUnder μ
        (fun Y : Config d N => (1 / (N : ℝ)) * ∑ i, aCoef d s ρβ f (Y i)) X) from rfl,
      eLpNorm_const_smul, Real.enorm_of_nonneg (by positivity)]
    rw [show (2 / (N : ℝ)) = 2 * (1 / (N : ℝ)) by ring, ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_ofNat]
    ring
  have hE3 : eLpNorm E 2 μ ≤ ENNReal.ofReal (3 * B0) := by
    rw [eLpNorm_congr_ae hEeq]
    have h3 : ENNReal.ofReal (3 * B0) =
        ENNReal.ofReal B0 + (ENNReal.ofReal B0 + ENNReal.ofReal B0) := by
      rw [show 3 * B0 = B0 + (B0 + B0) by ring, ENNReal.ofReal_add hB0nn (by linarith),
        ENNReal.ofReal_add hB0nn hB0nn]
    rw [h3]
    refine hsub.trans (add_le_add tC ?_)
    rw [hc2]
    exact (mul_le_mul_of_nonneg_left tD (by norm_num : (0 : ℝ≥0∞) ≤ 2)).trans (two_mul _).le
  have bE : ∫⁻ Y, ENNReal.ofReal (E Y ^ 2) ∂μ ≤ ENNReal.ofReal (M ^ 2) :=
    (m417_sq_bound E (by linarith) hEm.aestronglyMeasurable hE3).trans
      (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by linarith) (by linarith) 2))
  -- conjuncts
  have hint0 : ∫ Y, F Y ∂μ = 0 := by
    rw [hF]
    simp only [centeredUnder]
    rw [integral_sub hFint (integrable_const _)]
    simp
  have hGae : particleGen d s V β (Fstat (N := N) (Ψ f)) =ᵐ[μ] G := by
    filter_upwards [hae] with X hX
    rw [hG, Set.indicator_of_mem (show X ∈ (collisionSet d N)ᶜ from hX)]
  have hclos : MD.DOM.IsInClosedGenerator d s V β μ F G := by
    rw [hF]; exact hdomN.congr_ae hGae
  have hident : ∀ X : Config d N, X ∉ collisionSet d N →
      Real.sqrt N / 2 * centeredUnder μ (quadStat (hTransport d s f) (withDensityReal ρβ)) X =
        -G X + E X := by
    intro X _
    simp only [hE]
    ring
  have tF' : ∫⁻ Y, ENNReal.ofReal (F Y ^ 2) ∂μ ≤ ENNReal.ofReal (M ^ 2) := bF
  have hgrad : ∫⁻ Y, ∑ i, ‖configGrad F Y i‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (M ^ 2) := by
    simp_rw [hconf]
    exact tB'
  refine ⟨F, G, E, hFm, hGm, hEm, ⟨hFm, lt_of_le_of_lt tF ENNReal.ofReal_lt_top,
    hcd1, hen⟩, hcd1, hclos, hint0, hident, bF, bE, hgrad, hLint⟩

/-- The uniform mode package at `s = d/2`, family form (`unifModePackage_genV` with `s = d/2`). -/
theorem unifModePackageFam (hd : 2 ≤ d) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp) (Bf : ℕ → ℝ) :
    UnifModePackageFam d hd βm βp hβm Bf :=
  unifModePackage_genV hd rfl βm βp hβm hββ Bf

/-- A family and one smooth potential bounded by `Bf` give `HRS.ME.Crit.UnifModePackage` for that potential. -/
theorem UnifModePackageFam.specialize {d : ℕ} (hd : 2 ≤ d) (βm βp : ℝ) (hβm : 0 < βm) (Bf : ℕ → ℝ)
    (hu : UnifModePackageFam d hd βm βp hβm Bf) (V : Torus d → ℝ) (hV : Torus.IsSmooth V)
    (hVB : ∀ j : ℕ, Torus.cbNorm j V ≤ Bf j) :
    HRS.ME.Crit.UnifModePackage d hd V hV βm βp hβm := by
  obtain ⟨C, hC, h⟩ := hu
  exact ⟨C, hC, fun β hβ ρβ hρ hsm hpos N hN f hf => h V hV hVB β hβ ρβ hρ hsm hpos N hN f hf⟩

/-- A family and one smooth potential bounded by `Bf` give `HRS.ME.Crit.UnifModeForcing` for that potential. -/
theorem UnifModeForcingFam.specialize {d : ℕ} (hs0 : 0 ≤ (d : ℝ) / 2) (hsd : (d : ℝ) / 2 < d) (βm βp : ℝ)
    (hβm : 0 < βm) (c T : ℝ) (Bf : ℕ → ℝ) (hu : UnifModeForcingFam d hs0 hsd βm βp hβm c T Bf)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (hVB : ∀ j : ℕ, Torus.cbNorm j V ≤ Bf j) :
    HRS.ME.Crit.UnifModeForcing d hs0 hsd V βm βp hβm c T := by
  obtain ⟨C, hC, h⟩ := hu
  refine ⟨C, hC, ?_⟩
  intro β hβ ρβ hρ hsm hpos
  exact h V hV hVB β hβ ρβ hρ hsm hpos

end HRS.ME.FamU

end
