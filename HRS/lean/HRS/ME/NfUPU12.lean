import HRS.ME.ParxU
import HRS.ME.PmU
import HRS.Equilibrium.Q84dAuxI
import HRS.Equilibrium.Q84dAuxX
import HRS.Equilibrium.Q84dStationary

/-!
# Packet PU12 (uniform envelope integral, `a_f` bound and zeta bound)

Uniform forms of three lemmas of the Q84d chain, for densities `ρ` on `β ∈ Icc βm βp`. The data
`d, s, βm, βp, c₀, Λ₀` (with `0 < βm`, `βm ≤ βp`) and, for the zeta bound, the smooth potential `V`
are fixed before `β` and `ρ`.

* `q84d_integral_wEnv_mu_le_unif` is `HRS.Q84d.q84d_integral_wEnv_mu_le` (`HRS/Equilibrium/Q84dAuxI.lean:98`).
  The original uses no potential and no thermal equation, so the hypothesis is `RhoU`. The density
  bound `ρ ≤ Λ` is `hup` (with `|Λ₀|` in place of `Λ`), and the constant is `|Λ₀| * c` with `c` from
  `q84d_integral_wEnv_le`, which does not depend on `ρ`.
* `q84d_aCoef_bound_unif` is `HRS.Q84d.q84d_aCoef_bound` (`HRS/Equilibrium/Q84dAuxX.lean:126`).
  The hypothesis is `RhoU` (no potential, no thermal equation). The constant is `C₀ * M₀ / 2` with
  `C₀` from `q84d_hTransport_quant` and `M₀` from `q84d_integral_wEnv_mu_le_unif`.
* `q84d_zeta_bound_unif` is `HRS.Q84d.q84d_zeta_bound` (`HRS/Equilibrium/Q84dStationary.lean:189`).
  The original uses `V` (in `canonicalGibbs`) but not the thermal equation (`_hρ` is unused), so the
  hypothesis is the bundle `ParxU d s 1 βp⁻¹ βm⁻¹ c₀ Λ₀ β V ρ`, from which `RhoU` is extracted by
  `rhoU_of_parxU`. The constant is `2 * Ca` with `Ca` from `q84d_aCoef_bound_unif`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HRS.ME.NfU

open HRS.Q84d

variable {d : ℕ}

/-- The `RhoU` hypotheses are extracted from the Parametrix bundle (`ρ ≥ c₀`, `ρ ≤ Λ₀`,
smoothness and positivity), with `β ∈ Icc βm βp` and `0 < βm` given. -/
theorem rhoU_of_parxU {s : ℝ} {N : ℕ} {νm νp c₀ Λ₀ β βm βp : ℝ} {V ρ : Torus d → ℝ}
    (hβm : 0 < βm) (hβ : β ∈ Icc βm βp)
    (U : HRS.ME.ParxU.ParxU d s N νm νp c₀ Λ₀ β V ρ) :
    HRS.ME.PmU.RhoU d βm βp c₀ Λ₀ β ρ :=
  ⟨hβm, hβ, U.F.hc₀, U.H.rho_smooth, fun x => U.rho_ge x, fun x => U.rho_le x⟩

/-- **Uniform `q84d_integral_wEnv_mu_le`.** One constant `M` for all `β ∈ [βm, βp]`, all `RhoU`
densities and all `x`. -/
theorem q84d_integral_wEnv_mu_le_unif {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2)
    (βm βp c₀ Λ₀ : ℝ) (_hβm : 0 < βm) (_hββ : βm ≤ βp) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ β ∈ Icc βm βp, ∀ ρ : Torus d → ℝ,
      HRS.ME.PmU.RhoU d βm βp c₀ Λ₀ β ρ → ∀ x : Torus d,
        Integrable (fun y => wEnv s x y) (withDensityReal ρ) ∧
          ∫ y, wEnv s x y ∂(withDensityReal ρ) ≤ M := by
  obtain ⟨c, hc0, hc⟩ := q84d_integral_wEnv_le hd hcrit
  refine ⟨|Λ₀| * c, mul_nonneg (abs_nonneg _) hc0, fun β _ ρ U x => ?_⟩
  have hle := q84d_withDensity_le (fun y => (U.hup y).trans (le_abs_self _))
  refine ⟨?_, ?_⟩
  · exact ((q84d_integrable_wEnv hd hcrit x).smul_measure ENNReal.ofReal_ne_top).mono_measure hle
  · calc ∫ y, wEnv s x y ∂(withDensityReal ρ)
        ≤ ∫ y, wEnv s x y ∂(ENNReal.ofReal |Λ₀| • (volume : Measure (Torus d))) :=
          integral_mono_measure hle (Filter.Eventually.of_forall fun z =>
            (zero_le_one.trans (PairCorrAux.one_le_wEnv s x z)))
            ((q84d_integrable_wEnv hd hcrit x).smul_measure ENNReal.ofReal_ne_top)
      _ = |Λ₀| * ∫ y, wEnv s x y := by
          rw [integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), smul_eq_mul]
      _ ≤ |Λ₀| * c := mul_le_mul_of_nonneg_left (hc x) (abs_nonneg _)

/-- **Uniform `q84d_aCoef_bound`.** One constant `Ca` for all `β ∈ [βm, βp]` and all `RhoU` densities. -/
theorem q84d_aCoef_bound_unif {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2)
    (βm βp c₀ Λ₀ : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp) :
    ∃ Ca : ℝ, 0 ≤ Ca ∧ ∀ β ∈ Icc βm βp, ∀ ρ : Torus d → ℝ,
      HRS.ME.PmU.RhoU d βm βp c₀ Λ₀ β ρ →
      ∀ {f : Torus d → ℝ}, Torus.IsSmooth f → ∀ x : Torus d,
        |aCoef d s ρ f x| ≤ Ca * posSeminorm (8 * d + 80) f := by
  obtain ⟨C₀, hC₀, hC⟩ := q84d_hTransport_quant hd hcrit (s := s)
  obtain ⟨M₀, hM₀, hM⟩ := q84d_integral_wEnv_mu_le_unif hd hcrit βm βp c₀ Λ₀ hβm hββ
  refine ⟨C₀ * M₀ / 2, by positivity, fun β hβI ρ U {f} hf x => ?_⟩
  set D := posSeminorm (8 * d + 80) f with hDdef
  have hD0 : 0 ≤ D := q84d_posSeminorm_nonneg _ f
  have hb := hC hf (q84d_hess_le_posSeminorm hf)
  obtain ⟨hint, hle⟩ := hM β hβI ρ U x
  have hae : ∀ᵐ y ∂(withDensityReal ρ), ‖hTransport d s f x y‖ ≤ C₀ * D * wEnv s x y := by
    have h0 : ∀ᵐ y ∂(volume : Measure (Torus d)), y ≠ x := by
      rw [ae_iff]; simpa using volume_singleton_torus (by omega) x
    filter_upwards [(withDensity_absolutelyContinuous _ _).ae_le h0] with y hy
    rw [Real.norm_eq_abs]; exact hb x y hy.symm
  have h1 := norm_integral_le_of_norm_le (hint.const_mul (C₀ * D)) hae
  rw [integral_const_mul, Real.norm_eq_abs] at h1
  unfold aCoef
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have h2 : C₀ * D * ∫ y, wEnv s x y ∂(withDensityReal ρ) ≤ C₀ * D * M₀ :=
    mul_le_mul_of_nonneg_left hle (by positivity)
  calc 1 / 2 * |∫ y, hTransport d s f x y ∂(withDensityReal ρ)| ≤ 1 / 2 * (C₀ * D * M₀) := by
        gcongr; exact h1.trans h2
    _ = C₀ * M₀ / 2 * D := by ring

/-- **Uniform `q84d_zeta_bound`.** One constant `C` for all `β ∈ [βm, βp]`, all bundle densities `ρ`,
all smooth `f` and all `N ≥ 2`. The thermal equation of the bundle is not used by the original. -/
theorem q84d_zeta_bound_unif {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2)
    (βm βp c₀ Λ₀ : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp) (V : Torus d → ℝ) (hV : Torus.IsSmooth V) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β ∈ Icc βm βp, ∀ ρ : Torus d → ℝ,
      HRS.ME.ParxU.ParxU d s 1 βp⁻¹ βm⁻¹ c₀ Λ₀ β V ρ →
      ∀ (f : Torus d → ℝ), Torus.IsSmooth f → ∀ N : ℕ, 2 ≤ N →
      ENNReal.ofReal (1 / (N : ℝ)) *
        eLpNorm (fun X : Config d N => Real.sqrt N *
          centeredUnder (canonicalGibbs (periodicRiesz d s) V N β)
            (fun Y : Config d N => (1 / (N : ℝ)) * ∑ i, aCoef d s ρ f (Y i)) X) 2
          (canonicalGibbs (periodicRiesz d s) V N β) ≤
        ENNReal.ofReal (C * posSeminorm (8 * d + 80) f * (N : ℝ) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨Ca, hCa0, hCa⟩ := q84d_aCoef_bound_unif hd hcrit βm βp c₀ Λ₀ hβm hββ
  refine ⟨2 * Ca, by positivity, fun β hβI ρ Uρ f hf N hN => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβI.1
  have hU := rhoU_of_parxU hβm hβI Uρ
  have hρs := hU.rho
  have hN1 : 1 ≤ N := by omega
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < d := by rw [hcrit]; linarith
  have := q84d_isProb hd hcrit hV hβ hN1 (N := N)
  have hD0 := q84d_posSeminorm_nonneg (8 * d + 80) f
  have h1 := q84d_zeta_trivial hN1 (P := canonicalGibbs (periodicRiesz d s) V N β)
    (aCoef d s ρ f) (q84d_measurable_aCoef hsd hρs.density hf)
    (M := Ca * posSeminorm (8 * d + 80) f) (fun x => hCa β hβI ρ hU hf x)
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN1
  have e : (1 / (N : ℝ)) * (2 * (Ca * posSeminorm (8 * d + 80) f) * Real.sqrt N) =
      2 * Ca * posSeminorm (8 * d + 80) f * (N : ℝ) ^ (-(1 / 2 : ℝ)) := by
    rw [Real.rpow_neg hNp.le, ← Real.sqrt_eq_rpow]
    have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hNp
    have hss : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hNp.le
    have h3 : (1 / (N : ℝ)) * Real.sqrt N = (Real.sqrt N)⁻¹ := by
      have h4 : 1 / (N : ℝ) * Real.sqrt N * Real.sqrt N = (1 / (N : ℝ)) * (Real.sqrt N * Real.sqrt N) := by ring
      have h5 : 1 / (N : ℝ) * Real.sqrt N * Real.sqrt N = 1 := by rw [h4, hss]; field_simp
      exact eq_inv_of_mul_eq_one_left h5
    calc (1 / (N : ℝ)) * (2 * (Ca * posSeminorm (8 * d + 80) f) * Real.sqrt N)
        = 2 * (Ca * posSeminorm (8 * d + 80) f) * ((1 / (N : ℝ)) * Real.sqrt N) := by ring
      _ = _ := by rw [h3]; ring
  calc ENNReal.ofReal (1 / (N : ℝ)) * eLpNorm _ 2 (canonicalGibbs (periodicRiesz d s) V N β)
      ≤ ENNReal.ofReal (1 / (N : ℝ)) * ENNReal.ofReal (2 * (Ca * posSeminorm (8 * d + 80) f) * Real.sqrt N) :=
        by gcongr
    _ = ENNReal.ofReal ((1 / (N : ℝ)) * (2 * (Ca * posSeminorm (8 * d + 80) f) * Real.sqrt N)) := by
        exact (ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ))).symm
    _ = _ := by rw [e]

end HRS.ME.NfU
