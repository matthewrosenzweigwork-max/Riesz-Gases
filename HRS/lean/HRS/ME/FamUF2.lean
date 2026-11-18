import HRS.MD.EQStatLinear
import HRS.Main.EqMargFinal
import HRS.ME.EVUD
import HRS.MD.EQEvoUnif

/-!
# Chunk E, packet F2 (namespace `HRS.ME.FamU`): V-uniform copies of three static bounds

Each copy has the fixed data first (everything the original takes except `V, hV`), plus `Bf : ℕ → ℝ`;
then the constant(s); then `∀ V, Torus.IsSmooth V → (∀ j, Torus.cbNorm j V ≤ Bf j) → …`.

* `eqstat_thermal_setup_unifV` (original `HRS.MD.EQStat.eqstat_thermal_setup`, HRS/MD/EQStatQuadratic.lean:80):
  only `Lam` (from `exists_thermal_bounds`) is chosen before `V`, through
  `HRS.ME.EVU.exists_thermal_bounds_unifV` with `Bv := Bf 0` (`|V x| ≤ cbNorm 0 V ≤ Bf 0`, lemma
  `abs_le_cbNorm_zero`). The density facts `hρs`, `hP` stay per `V`.
* `eq_static_linear_unifV` (original `HRS.MD.EQStat.eq_static_linear_proof`, HRS/MD/EQStatLinear.lean:236).
* `equilibrium_marginal_L2_unifV` (original `HRS.Main.equilibrium_marginal_L2_proof`, HRS/Main/EqMargFinal.lean:99),
  with `Lam` from `exists_thermal_bounds_unifV` and the marginal constant `HRS.EqMarg.eqmarg_marginal_unif`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace HRS.ME.FamU

open HRS HRS.Quad HRS.External HRS.External.RefMarg HRS.External.PoleVar HRS.External.HeatSplit HRS.External.Calib

variable {d : ℕ} {s : ℝ}

/-- The sup norm of a smooth `V` is bounded by its `cbNorm 0` (the `C^0` part of `cbNorm`). -/
theorem abs_le_cbNorm_zero {V : Torus d → ℝ} (hV : Torus.IsSmooth V) (x : Torus d) :
    |V x| ≤ Torus.cbNorm 0 V := by
  have hVL : Torus.IsCk ((0 : ℕ) : WithTop ENat) V := HRS.MD.EQEvoUnif.eqevo_isCk_nat hV 0
  have h := HRS.PDE.MFPair.norm_iter_le_cb_ps (L := 0) hVL (i := 0) (Nat.zero_le _) (Torus.rep x)
  rw [norm_iteratedFDeriv_zero] at h
  have hx : Torus.lift V (Torus.rep x) = V x := by
    simp [Torus.lift, Torus.mk_rep]
  rw [hx, Real.norm_eq_abs] at h
  exact h

/-- **F2.1** `eqstat_thermal_setup`, V-uniform: the common density bound `Lam` is chosen before `V`. -/
theorem eqstat_thermal_setup_unifV (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (βm βp : ℝ)
    (hβm : 0 < βm) (hββ : βm ≤ βp) (Bf : ℕ → ℝ) :
    ∃ Lam : ℝ, ∀ V : Torus d → ℝ, Torus.IsSmooth V → (∀ j : ℕ, Torus.cbNorm j V ≤ Bf j) →
      ∀ β : ℝ, β ∈ Set.Icc βm βp → ∀ ρβ : Torus d → ℝ,
      IsThermalDensity (periodicRiesz d s) V β ρβ →
      ∃ hρs : SmoothPosDensity ρβ, (∀ x, ρβ x ≤ Lam) ∧
        ∀ N : ℕ, canonicalGibbs (periodicRiesz d s) V N β =
          modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρβ) := by
  obtain ⟨lam, Lam, hlam, hb⟩ :=
    HRS.ME.EVU.exists_thermal_bounds_unifV (by omega : 1 ≤ d) s hs0 hsd βm βp hβm hββ (Bf 0)
  refine ⟨Lam, fun V hV hVB β hβ ρβ hρ => ?_⟩
  have hVc : Continuous V :=
    HRS.PDE.MFAux.continuous_of_isCk (ContDiff.of_le
      (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift V) from hV) (by exact_mod_cast le_top))
  have hVb : ∀ x, |V x| ≤ Bf 0 := fun x => (abs_le_cbNorm_zero hV x).trans (hVB 0)
  have hβ0 : 0 < β := lt_of_lt_of_le hβm hβ.1
  obtain ⟨hpos, hsm⟩ := Q41.q41_thermal_regular hd hs0 hsd hβ0 hV hρ
  have hρs : SmoothPosDensity ρβ := ⟨hρ.1, hsm, hpos⟩
  refine ⟨hρs, fun x => (hb V hVc hVb β hβ ρβ hρ (PoleCavityAux.continuous_of_smoothPos hρs) hpos x).2,
    fun N => ?_⟩
  obtain ⟨Λ, hΛ0, hΛ'⟩ := PoleCavityAux.exists_density_bound hρs
  refine canonicalGibbs_eq_modulatedGibbs (periodicRiesz d s) V β ρβ hρ
    (fun x => periodicRiesz_neg x) ?_
  intro x
  exact (CoercAux.J_bounds (by omega : 1 ≤ d) hs0 hsd one_pos hρs.density hΛ0.le hΛ' x).1

/-- **F2.2** `eq_static_linear`, V-uniform: the constant `C` is chosen before `V`, through the V-uniform
`Lam` of `eqstat_thermal_setup_unifV`. -/
theorem eq_static_linear_unifV (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (βm βp : ℝ)
    (hβm : 0 < βm) (hββ : βm ≤ βp) (Bf : ℕ → ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ V : Torus d → ℝ, Torus.IsSmooth V → (∀ j : ℕ, Torus.cbNorm j V ≤ Bf j) →
    ∀ β : ℝ, β ∈ Set.Icc βm βp → ∀ ρβ : Torus d → ℝ,
      IsThermalDensity (periodicRiesz d s) V β ρβ → ∀ N : ℕ, 2 ≤ N →
      ∀ f : Torus d → ℝ, Measurable f → MemLp f 2 (withDensityReal ρβ) →
        evariance (fun X : Config d N => pair (empirical X) f)
            (canonicalGibbs (periodicRiesz d s) V N β) ≤
          ENNReal.ofReal (C * (N : ℝ)⁻¹ * ∫ x, f x ^ 2 ∂(withDensityReal ρβ)) := by
  obtain ⟨Lam, hLam⟩ := eqstat_thermal_setup_unifV hd hs0 hsd βm βp hβm hββ Bf
  obtain ⟨C, hCU⟩ := HRS.MD.EQStat.eqstat_lin_main hd hs0 hsd hβm hββ Lam
  refine ⟨|C| + 1, by positivity, fun V hV hVB β hβ ρβ hρ N hN f hf hf2 => ?_⟩
  obtain ⟨hρs, hΛ, hP⟩ := hLam V hV hVB β hβ ρβ hρ
  have hN0 : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  have hF : (fun X : Config d N => pair (empirical X) f) = fun X => (1 / (N : ℝ)) * ∑ i, f (X i) := by
    funext X
    rw [pair_empirical hN0, one_div]
  rw [hF, hP N]
  have hmain := hCU hβ.1 hβ.2 ρβ hρs.density hΛ N hN f hf hf2
  have hI : 0 ≤ ∫ x, f x ^ 2 ∂(withDensityReal ρβ) := integral_nonneg fun _ => sq_nonneg _
  have hev : evariance (fun X : Config d N => (1 / (N : ℝ)) * ∑ i, f (X i))
      (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρβ)) =
      ENNReal.ofReal ((N : ℝ)⁻¹) * ((N : ℝ≥0∞) * evariance (fun X : Config d N => (1 / (N : ℝ)) * ∑ i, f (X i))
        (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρβ))) := by
    rw [← mul_assoc, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
      inv_mul_cancel₀ hNR.ne', ENNReal.ofReal_one, one_mul]
  rw [hev]
  calc ENNReal.ofReal ((N : ℝ)⁻¹) * ((N : ℝ≥0∞) * evariance (fun X : Config d N => (1 / (N : ℝ)) * ∑ i, f (X i))
        (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρβ)))
      ≤ ENNReal.ofReal ((N : ℝ)⁻¹) * ENNReal.ofReal (C * ∫ x, f x ^ 2 ∂(withDensityReal ρβ)) := by
        gcongr
    _ = ENNReal.ofReal ((N : ℝ)⁻¹ * (C * ∫ x, f x ^ 2 ∂(withDensityReal ρβ))) := by
        exact (ENNReal.ofReal_mul (inv_nonneg.2 hNR.le)).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hNi : 0 ≤ (N : ℝ)⁻¹ := by positivity
        have h1 : C ≤ |C| + 1 := by linarith [le_abs_self C]
        nlinarith [mul_le_mul_of_nonneg_right h1 (mul_nonneg hNi hI)]

/-- **F2.3** `equilibrium_marginal_L2`, V-uniform: the constant `C + 1` is chosen before `V`; the density
bound `Lam` comes from `exists_thermal_bounds_unifV` with `Bv := Bf 0`. -/
theorem equilibrium_marginal_L2_unifV (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (βm βp : ℝ)
    (hβm : 0 < βm) (hββ : βm ≤ βp) (Bf : ℕ → ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ V : Torus d → ℝ, Torus.IsSmooth V → (∀ j : ℕ, Torus.cbNorm j V ≤ Bf j) →
    ∀ β : ℝ, β ∈ Set.Icc βm βp → ∀ ρβ : Torus d → ℝ,
      IsThermalDensity (periodicRiesz d s) V β ρβ → ∀ N : ℕ, 2 ≤ N →
      firstMarginal (canonicalGibbs (periodicRiesz d s) V N β) ≪ withDensityReal ρβ ∧
        eLpNorm (fun y => ((firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)).rnDeriv
            (withDensityReal ρβ) y).toReal - 1) 2 (withDensityReal ρβ) ≤
          ENNReal.ofReal (C * deltaN d s N) := by
  obtain ⟨lam, Lam, hlam, hb⟩ :=
    HRS.ME.EVU.exists_thermal_bounds_unifV (by omega : 1 ≤ d) s hs0 hsd βm βp hβm hββ (Bf 0)
  obtain ⟨C, hC0, hCU⟩ := HRS.EqMarg.eqmarg_marginal_unif hd hs0 hsd βm βp hβm hββ Lam
  refine ⟨C + 1, by linarith, fun V hV hVB β hβ ρβ hρ N hN => ?_⟩
  have hVc : Continuous V :=
    HRS.PDE.MFAux.continuous_of_isCk (ContDiff.of_le
      (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift V) from hV) (by exact_mod_cast le_top))
  have hVb : ∀ x, |V x| ≤ Bf 0 := fun x => (abs_le_cbNorm_zero hV x).trans (hVB 0)
  have hβ0 : 0 < β := lt_of_lt_of_le hβm hβ.1
  obtain ⟨hpos, hsm⟩ := Q41.q41_thermal_regular hd hs0 hsd hβ0 hV hρ
  have hρs : SmoothPosDensity ρβ := ⟨hρ.1, hsm, hpos⟩
  have hΛ : ∀ x, ρβ x ≤ Lam :=
    fun x => (hb V hVc hVb β hβ ρβ hρ (PoleCavityAux.continuous_of_smoothPos hρs) hpos x).2
  have hP : canonicalGibbs (periodicRiesz d s) V N β =
      modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρβ) := by
    obtain ⟨Λ, hΛ0, hΛ'⟩ := PoleCavityAux.exists_density_bound hρs
    refine canonicalGibbs_eq_modulatedGibbs (periodicRiesz d s) V β ρβ hρ
      (fun x => periodicRiesz_neg x) ?_
    intro x
    exact (CoercAux.J_bounds (by omega : 1 ≤ d) hs0 hsd one_pos hρs.density hΛ0.le hΛ' x).1
  rw [hP]
  obtain ⟨h1, h2⟩ := hCU β hβ.1 hβ.2 ρβ hρs hΛ N hN
  refine ⟨h1, h2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have hδ0 : 0 ≤ deltaN d s N := by
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    exact (inv_nonneg.2 hN0.le).trans (MarginalAux.inv_le_deltaN (d := d) hs0 N (by omega))
  nlinarith

end HRS.ME.FamU

end
