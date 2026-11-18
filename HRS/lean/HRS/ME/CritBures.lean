import HRS.ME.CritSpec
import HRS.MD.EQTraceLin
import HRS.Uniform.Q48cCov

/-!
# Task A2: `crit_bures2_uniform` (uniform Bures estimate of the empirical covariance)

`HRS.ME.Crit.crit_bures2_uniform` is proved by the route of `HRS.Uniform.Q48c.bures2_cov_estimate`, with the
constants made uniform in `β ∈ [βm, βp]` and in the thermal density `ρβ`:

* `crit_lintegral_majorant`: copy of `HRS.Uniform.Q48c.lintegral_majorant_le` with the constant written out:
  `q ∈ (0, q0]` and a density of total mass one (instead of an existential constant depending on `ρ`).
* the uniform inputs are `HRS.MD.EQStat.eq_static_linear_proof` (variance), `HRS.Main.equilibrium_marginal_L2_proof`
  (one-body marginal) and `HRS.PDE.MFDecay.exists_thermal_bounds` (lower bound `lam ≤ ρβ`, used pointwise in
  `bures2_pointwise`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ME.CritBures

open HRS HRS.Uniform HRS.Uniform.Q14 HRS.Uniform.Q48c

variable {d : ℕ}

/-- Copy of `HRS.Uniform.Q48c.lintegral_majorant_le` (proof text unchanged except for the final constant): the
constant is explicit, depends on `q0`, `c`, `Cv`, `d`, `m` only, and is uniform over `q ∈ (0, q0]` and over the
densities `ρ` of total mass one. -/
theorem crit_lintegral_majorant {m : ℝ} (hm : (d : ℝ) + 3 ≤ m) {q0 : ℝ} (hq0 : 0 < q0)
    (c : ℝ) (hc : 0 < c) (Cv : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℝ) (hq : 0 < q), q ≤ q0 → ∀ {ρ : Torus d → ℝ}, Continuous ρ →
      IsProbabilityMeasure (withDensityReal ρ) → ∀ (N : ℕ) (hN : 1 ≤ N) (δ : ℝ)
      (Q : Measure (Config d N)) [IsProbabilityMeasure Q] (g : Torus d → ℝ) (hg : Measurable g)
      (hmarg : (N : ℝ≥0∞)⁻¹ • ∑ i, Q.map (fun x : Config d N => x i) =
        (withDensityReal ρ).withDensity fun x => ENNReal.ofReal (g x))
      (hgL2 : ∫⁻ x, ‖g x - 1‖ₑ ^ 2 ∂(withDensityReal ρ) ≤ ENNReal.ofReal ((Cv * δ) ^ 2))
      (hvar : ∀ f : Torus d → ℝ, Measurable f → MemLp f 2 (withDensityReal ρ) →
        evariance (fun x : Config d N => pair (empirical x) f) Q ≤
          ENNReal.ofReal (Cv * (N : ℝ)⁻¹ * ∫ x, f x ^ 2 ∂(withDensityReal ρ))),
      ∫⁻ x, majorant d m q c ρ x ∂Q ≤ ENNReal.ofReal (C * ((N : ℝ)⁻¹ + δ ^ 2)) := by
  have hm1 : (d : ℝ) / 2 + 2 < m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hm2 : (d : ℝ) + 1 < m := by linarith
  set S : ℝ := ∑' k : NonzeroLattice d, wt m k * Lattice.jp k.1 with hS
  set Kmax : ℝ := max |Cv| (Cv ^ 2) with hKmax
  set C : ℝ := 2 * c⁻¹ * (16 * q0 * (d : ℝ) ^ 2 * Kmax * S ^ 2) with hCdef
  have hS0 : 0 ≤ S := tsum_nonneg fun k => mul_nonneg (wt_pos k).le (Torus.jp_pos k.1).le
  have hK0 : 0 ≤ Kmax := (abs_nonneg Cv).trans (le_max_left _ _)
  have hC0 : 0 ≤ C := by positivity
  refine ⟨C, hC0, ?_⟩
  intro q hq hqq ρ hρ hP1 N hN δ Q _ g hg hmarg hgL2 hvar
  haveI hfin : IsFiniteMeasure (withDensityReal ρ) := inferInstance
  set M : ℝ := ((withDensityReal ρ) Set.univ).toReal with hMdef
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  have hM1 : M = 1 := by rw [hMdef]; simp [measure_univ]
  have hN0 : (0 : ℝ) ≤ (N : ℝ)⁻¹ := by positivity
  set Kn : ℝ := |Cv| * (N : ℝ)⁻¹ + (Cv * δ) ^ 2 with hKn
  have hKnle : Kn ≤ Kmax * ((N : ℝ)⁻¹ + δ ^ 2) := by
    simp only [hKn, hKmax]
    rw [mul_pow]
    nlinarith [mul_nonneg hN0 (sub_nonneg.2 (le_max_left |Cv| (Cv ^ 2))),
      mul_nonneg (sq_nonneg δ) (sub_nonneg.2 (le_max_right |Cv| (Cv ^ 2)))]
  have hKn0 : 0 ≤ Kn := by positivity
  set K1 : ℝ := 16 * q * (d : ℝ) ^ 2 * M * Kn with hK1
  have hK10 : 0 ≤ K1 := by positivity
  have hK1le : K1 ≤ 16 * q0 * (d : ℝ) ^ 2 * (Kmax * ((N : ℝ)⁻¹ + δ ^ 2)) := by
    rw [hK1, hM1]
    calc 16 * q * (d : ℝ) ^ 2 * 1 * Kn ≤ 16 * q0 * (d : ℝ) ^ 2 * 1 * Kn := by gcongr
      _ ≤ 16 * q0 * (d : ℝ) ^ 2 * 1 * (Kmax * ((N : ℝ)⁻¹ + δ ^ 2)) := by gcongr
      _ = _ := by ring
  have hrq : ∫⁻ x, Uniform.relQuad (basis d m) (dd0 m q)
      (covForm m q (empirical x) - covForm m q (withDensityReal ρ)) ∂Q ≤
      ENNReal.ofReal (K1 * S ^ 2) := by
    set f : NonzeroLattice d × NonzeroLattice d → Config d N → ℝ≥0∞ := fun p x => ENNReal.ofReal
          (((covForm m q (empirical x) - covForm m q (withDensityReal ρ))
            (basis d m p.1) (basis d m p.2)) ^ 2 / (dd0 m q p.1 + dd0 m q p.2)) with hf
    have hfm : ∀ p, AEMeasurable (f p) Q := fun p =>
      (measurable_entry hm1 hq.le hρ hN p.1 p.2).aemeasurable
    have e1 : ∫⁻ x, Uniform.relQuad (basis d m) (dd0 m q)
        (covForm m q (empirical x) - covForm m q (withDensityReal ρ)) ∂Q =
        ∑' p, ∫⁻ x, f p x ∂Q := lintegral_tsum hfm
    rw [e1]
    calc ∑' p, ∫⁻ x, f p x ∂Q
        ≤ ∑' p : NonzeroLattice d × NonzeroLattice d, ENNReal.ofReal
          (K1 * ((wt m p.1 * Lattice.jp p.1.1) * (wt m p.2 * Lattice.jp p.2.1))) :=
          ENNReal.tsum_le_tsum fun p =>
            entry_bound hm1 hq hρ hN Q g hg hmarg Cv δ hgL2 hvar p.1 p.2
      _ = ENNReal.ofReal (K1 * S ^ 2) := sum_s_le hm2 K1 hK10
  unfold majorant
  calc ∫⁻ x, 2 * ENNReal.ofReal c⁻¹ * Uniform.relQuad (basis d m) (dd0 m q)
        (covForm m q (empirical x) - covForm m q (withDensityReal ρ)) ∂Q
      = 2 * ENNReal.ofReal c⁻¹ * ∫⁻ x, Uniform.relQuad (basis d m) (dd0 m q)
        (covForm m q (empirical x) - covForm m q (withDensityReal ρ)) ∂Q :=
        lintegral_const_mul' _ _ (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
    _ ≤ 2 * ENNReal.ofReal c⁻¹ * ENNReal.ofReal (K1 * S ^ 2) := by gcongr
    _ = ENNReal.ofReal (2 * c⁻¹ * (K1 * S ^ 2)) := by
        have h2c : (0 : ℝ) ≤ 2 * c⁻¹ := by positivity
        rw [ENNReal.ofReal_mul h2c, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        simp
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc 2 * c⁻¹ * (K1 * S ^ 2)
            ≤ 2 * c⁻¹ * ((16 * q0 * (d : ℝ) ^ 2 * (Kmax * ((N : ℝ)⁻¹ + δ ^ 2))) * S ^ 2) := by
              gcongr
          _ = C * ((N : ℝ)⁻¹ + δ ^ 2) := by simp only [hCdef]; ring

/-- (A2.) `HRS.ME.Crit.crit_bures2_uniform`: the uniform Bures estimate of the empirical covariance. -/
theorem crit_bures2_uniform_proof {d : ℕ} : type_of% (@HRS.ME.Crit.crit_bures2_uniform d) := by
  intro hd s hs0 hsd V hV βm βp hβm hββ m hm
  have hd1 : 1 ≤ d := by omega
  have hVc : Continuous V :=
    HRS.PDE.MFAux.continuous_of_isCk (ContDiff.of_le
      (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift V) from hV) (by exact_mod_cast le_top))
  obtain ⟨C₁, hC₁, hlin⟩ := HRS.MD.EQStat.eq_static_linear_proof hd hs0 hsd V hV βm βp hβm hββ
  obtain ⟨C₂, hC₂, hmargU⟩ := HRS.Main.equilibrium_marginal_L2_proof hd hs0 hsd V hV βm βp hβm hββ
  obtain ⟨Lam, hLam⟩ := HRS.MD.EQStat.eqstat_thermal_setup hd hs0 hsd V hV βm βp hβm hββ
  obtain ⟨lam, Lam', hlam, hb⟩ := HRS.PDE.MFDecay.exists_thermal_bounds hd1 s hs0 hsd βm βp hβm hββ V hVc
  obtain ⟨C, hC0, hCU⟩ := crit_lintegral_majorant hm (inv_pos.2 hβm) lam hlam (max C₁ C₂)
  have hm1 : (d : ℝ) / 2 + 2 < m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  refine ⟨C + 1, by linarith, ?_⟩
  intro β hβ ρβ hρ N hN
  have hβ0 : 0 < β := lt_of_lt_of_le hβm hβ.1
  have hq : 0 < β⁻¹ := inv_pos.2 hβ0
  have hqle : β⁻¹ ≤ βm⁻¹ := inv_anti₀ hβm hβ.1
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  obtain ⟨hρc, hρp, hPr⟩ := HRS.MD.EQTrace.eqtrace_setup hd hs0 hsd V hV βm βp hβm hββ β hβ ρβ hρ N hN
  haveI := hPr
  obtain ⟨hpos, -⟩ := HRS.Q41.q41_thermal_regular hd hs0 hsd hβ0 hV hρ
  have hcρ : ∀ x, lam ≤ ρβ x := fun x => (hb β hβ ρβ hρ hρc hpos x).1
  obtain ⟨-, -, hP⟩ := hLam β hβ ρβ hρ
  have hPm : canonicalGibbs (periodicRiesz d s) V N β =
      modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρβ) := hP N
  have hex : IsExchangeable (canonicalGibbs (periodicRiesz d s) V N β) := by
    rw [hPm]; exact modulatedGibbs_isExchangeable _ _ _ (fun x => periodicRiesz_neg x)
  obtain ⟨hac, hL2⟩ := hmargU β hβ ρβ hρ N hN
  have hδ0 : 0 ≤ deltaN d s N :=
    (inv_nonneg.2 hN0.le).trans (HRS.MarginalAux.inv_le_deltaN (d := d) hs0 N hN1)
  haveI hP1 : IsProbabilityMeasure (withDensityReal ρβ) := isProb_withDensityReal hρp
  set P := canonicalGibbs (periodicRiesz d s) V N β with hPdef
  -- variance hypothesis with the uniform constant `max C₁ C₂`
  have hvar : ∀ f : Torus d → ℝ, Measurable f → MemLp f 2 (withDensityReal ρβ) →
      evariance (fun x : Config d N => pair (empirical x) f) P ≤
        ENNReal.ofReal (max C₁ C₂ * (N : ℝ)⁻¹ * ∫ x, f x ^ 2 ∂(withDensityReal ρβ)) := by
    intro f hf hmem
    refine (hlin β hβ ρβ hρ N hN f hf hmem).trans (ENNReal.ofReal_le_ofReal ?_)
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

end HRS.ME.CritBures
