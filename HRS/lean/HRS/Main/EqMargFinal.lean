import HRS.Main.EqMargU4
import HRS.Main.Equilibrium29Spec
import HRS.PDE.MeanFieldDecayGap
import HRS.Sections.Q41Aux14

/-!
# EQ-MARG-U: `equilibrium_marginal_L2` (Theorem 2.9, TeX M L972-973), uniform in `β ∈ [β₋,β₊]`

Relocated proof of `HRS.Main.equilibrium_marginal_L2` (HRS/Main/Equilibrium29Spec.lean).

The constant of Proposition 4.2 depends on `ρ` only through the upper bound `Λ ≥ ρ`
(`EqMargU1`-`EqMargU4`: the proofs of `pole_variance_clause`, `insDefect_le`, `cavity_tv`,
`pDens_bounds`, `L2_all`, ... re-run with `∃ C` before `∀ ρ ≤ Λ` and before `∀ β ∈ [β₋,β₊]`).
The thermal densities `ρ_β`, `β ∈ [β₋,β₊]`, satisfy `ρ_β ≤ Λ` uniformly
(`HRS.PDE.MFDecay.exists_thermal_bounds`, from the thermal equation).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS

namespace EqMarg

open HRS.External HRS.PoleCavityAux HRS.MarginalAux

variable {d : ℕ} {s : ℝ}

/-- Uniform version of `firstMarginal_density_L2` (Proposition 4.2, full-law part). -/
theorem eqmarg_marginal_unif (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (βm βp : ℝ) (hβm : 0 < βm)
    (hββ : βm ≤ βp) (Λ0 : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β : ℝ, βm ≤ β → β ≤ βp → ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ →
      (∀ x, ρ x ≤ Λ0) → ∀ N : ℕ, 2 ≤ N →
      firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≪
          withDensityReal ρ ∧
        eLpNorm (fun y => ((firstMarginal (modulatedGibbs (periodicRiesz d s) N β
            (withDensityReal ρ))).rnDeriv (withDensityReal ρ) y).toReal - 1) 2
            (withDensityReal ρ) ≤ ENNReal.ofReal (C * deltaN d s N) := by
  have hβp : 0 < βp := lt_of_lt_of_le hβm hββ
  obtain ⟨C, hC0, hCU⟩ := eqmarg_L2_all hd hs0 hsd βm βp hβm hββ Λ0
  obtain ⟨Mp, hMp1, hMpU⟩ := eqmarg_pDens_bounds hd hs0 hsd βm βp hβm hββ Λ0
  refine ⟨C, hC0, fun β hβ1 hβ2 ρ hρ hΛ N hN => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβ1
  have hμ := isProbabilityMeasure_mu hρ
  have hC := hCU β hβ1 hβ2 ρ hρ hΛ
  have hMp := hMpU β hβ1 hβ2 ρ hρ hΛ
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 0 < n := by omega
  obtain ⟨hlam, hln, -⟩ := lam_facts hd hs0 hsd hβ hρ hn (lam := β / ((n + 1 : ℕ) : ℝ)) rfl
  have hae := rnDeriv_pi_eq hd hs0 hsd hρ hlam hln
  rw [modulatedGibbs_eq_cavity hd hs0 hsd hβ hρ (n + 1) (Nat.succ_pos n)]
  refine ⟨?_, ?_⟩
  · rw [firstMarginal_eq_withDensity hd hs0 hsd hρ hlam hln]
    exact withDensity_absolutelyContinuous _ _
  · have hN' : 2 ≤ n + 1 := hN
    have hpm := measurable_pDens hd hs0 hsd hρ hlam hln
    have hp0 := pDens_pos hd hs0 hsd hρ hlam hln
    have hz : ∀ y, |pDens (periodicRiesz d s) (withDensityReal ρ) n (β / ((n + 1 : ℕ) : ℝ)) β y - 1| ≤ Mp := by
      intro y
      have h1 := hp0 y
      have h2 := (hMp (n + 1) hN' y).2
      simp only [Nat.add_sub_cancel] at h2
      rw [abs_le]; constructor <;> linarith
    have hmem : MemLp (fun y => pDens (periodicRiesz d s) (withDensityReal ρ) n (β / ((n + 1 : ℕ) : ℝ)) β y - 1)
        2 (withDensityReal ρ) :=
      MemLp.of_bound (hpm.sub measurable_const).aestronglyMeasurable Mp (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]; exact hz y)
    rw [eLpNorm_congr_ae (g := fun y => pDens (periodicRiesz d s) (withDensityReal ρ) n
      (β / ((n + 1 : ℕ) : ℝ)) β y - 1) (hae.mono fun y hy => by simp only [hy])]
    rw [hmem.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hA := hC n hn (β / ((n + 1 : ℕ) : ℝ)) rfl
    have hδ0 : 0 ≤ deltaN d s (n + 1) := by
      have hN0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      have := inv_le_deltaN (d := d) hs0 (n + 1) (by omega)
      exact (inv_nonneg.2 hN0.le).trans this
    have e : ∫ y, ‖pDens (periodicRiesz d s) (withDensityReal ρ) n (β / ((n + 1 : ℕ) : ℝ)) β y - 1‖ ^
        (2 : ENNReal).toReal ∂(withDensityReal ρ) =
        ∫ y, (pDens (periodicRiesz d s) (withDensityReal ρ) n (β / ((n + 1 : ℕ) : ℝ)) β y - 1) ^ 2
          ∂(withDensityReal ρ) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp [Real.norm_eq_abs, Real.rpow_two, sq_abs]
    rw [e]
    have h3 : (2 : ENNReal).toReal⁻¹ = 1 / 2 := by simp
    rw [h3, ← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_iff.2 ⟨mul_nonneg hC0 hδ0, hA⟩

end EqMarg

namespace Main

variable {d : ℕ}

theorem equilibrium_marginal_L2_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp) :
    ∃ C : ℝ, 0 < C ∧ ∀ β : ℝ, β ∈ Set.Icc βm βp → ∀ ρβ : Torus d → ℝ,
      IsThermalDensity (periodicRiesz d s) V β ρβ → ∀ N : ℕ, 2 ≤ N →
      firstMarginal (canonicalGibbs (periodicRiesz d s) V N β) ≪ withDensityReal ρβ ∧
        eLpNorm (fun y => ((firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)).rnDeriv
            (withDensityReal ρβ) y).toReal - 1) 2 (withDensityReal ρβ) ≤
          ENNReal.ofReal (C * deltaN d s N) := by
  have hVc : Continuous V :=
    HRS.PDE.MFAux.continuous_of_isCk (ContDiff.of_le
      (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift V) from hV) (by exact_mod_cast le_top))
  obtain ⟨lam, Lam, hlam, hb⟩ :=
    PDE.MFDecay.exists_thermal_bounds (by omega : 1 ≤ d) s hs0 hsd βm βp hβm hββ V hVc
  obtain ⟨C, hC0, hCU⟩ := EqMarg.eqmarg_marginal_unif hd hs0 hsd βm βp hβm hββ Lam
  refine ⟨C + 1, by linarith, fun β hβ ρβ hρ N hN => ?_⟩
  have hβ0 : 0 < β := lt_of_lt_of_le hβm hβ.1
  obtain ⟨hpos, hsm⟩ := Q41.q41_thermal_regular hd hs0 hsd hβ0 hV hρ
  have hρs : SmoothPosDensity ρβ := ⟨hρ.1, hsm, hpos⟩
  have hΛ : ∀ x, ρβ x ≤ Lam :=
    fun x => (hb β hβ ρβ hρ (PoleCavityAux.continuous_of_smoothPos hρs) hpos x).2
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

end Main

end HRS

example := (@HRS.Main.equilibrium_marginal_L2_proof : type_of% @HRS.Main.equilibrium_marginal_L2)
