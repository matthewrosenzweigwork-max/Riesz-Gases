import HRS.ME.FamUF5
import HRS.ME.FamUF5B
import HRS.ME.NfUPU13a

/-!
# Chunk E, packet F6 (namespace `HRS.ME.FamU`): V-uniform zeta bound, pair moments, normal form

Originals (copied with the convention of `docs/MAIN_E_FAMU_PLAN.md`):
* `HRS.ME.NfU.q84d_zeta_bound_unif` (`HRS/ME/NfUPU12.lean:99`) becomes `q84d_zeta_bound_unifV`. The
  constant `C` is chosen after `d s βm βp c₀ Λ₀`; `V` is bound after it and the hypothesis on `V` is the
  bundle `ParxU d s 1 βp⁻¹ βm⁻¹ c₀ Λ₀ β V ρ` (the `cbNorm` information enters through the bundle, so no
  separate `Bf` hypothesis is added). The proof is the original one with `V` introduced after `C`.
* `HRS.ME.NfU.pair_moments_unif` (`HRS/ME/NfUPU13a.lean:43`) becomes `pair_moments_unifV`. `V` occurs only in
  `IsThermalDensity`; the original `_hV` is unused and is dropped to a bare hypothesis `IsSmooth V` under the
  bound `V`. The constant `C₀` is chosen before `V`; its proof uses only the `RhoU`-based `_unif` lemmas.
* `HRS.ME.NfU.normal_form_unif_thermal` (`HRS/ME/NfUPU13a.lean:135`) becomes `normal_form_unif_thermalV`.
  Fixed data `d s hd hcrit βm βp hβm hββ Bf`; `c₀ Λ₀` from `parxU_of_eqevoV` at `n = 1`, `K = 6d+32`;
  `Cu` from `q84e_modified_kernels_uniform_unifV`, `Cz` from `q84d_zeta_bound_unifV`, `C₀` from
  `pair_moments_unifV` (with `max Λ₀ 1`); all four are chosen before `V`. The constant is
  `4 * c0 + 3 * c0 * Cu + Cz` with `c0 = sqrt (max C₀ 0)`, as in the original.
  `triple_canonical_proof` is applied at the introduced `V` (only its `IsCanonicalTriple` part is used,
  its constant is not part of the result).
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory Function
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace HRS.ME.FamU

open HRS HRS.PairMom HRS.Q84d

variable {d : ℕ}

/-- **F6.1 (V-uniform copy of `q84d_zeta_bound_unif`).** One constant `C` for all `V`, all
`β ∈ [βm, βp]`, all bundle densities `ρ`, all smooth `f` and all `N ≥ 2`. The constant depends on
`d s βm βp c₀ Λ₀` only. -/
theorem q84d_zeta_bound_unifV {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2)
    (βm βp c₀ Λ₀ : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : Torus d → ℝ), Torus.IsSmooth V → ∀ β ∈ Icc βm βp, ∀ ρ : Torus d → ℝ,
      HRS.ME.ParxU.ParxU d s 1 βp⁻¹ βm⁻¹ c₀ Λ₀ β V ρ →
      ∀ (f : Torus d → ℝ), Torus.IsSmooth f → ∀ N : ℕ, 2 ≤ N →
      ENNReal.ofReal (1 / (N : ℝ)) *
        eLpNorm (fun X : Config d N => Real.sqrt N *
          centeredUnder (canonicalGibbs (periodicRiesz d s) V N β)
            (fun Y : Config d N => (1 / (N : ℝ)) * ∑ i, aCoef d s ρ f (Y i)) X) 2
          (canonicalGibbs (periodicRiesz d s) V N β) ≤
        ENNReal.ofReal (C * posSeminorm (8 * d + 80) f * (N : ℝ) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨Ca, hCa0, hCa⟩ := HRS.ME.NfU.q84d_aCoef_bound_unif hd hcrit βm βp c₀ Λ₀ hβm hββ
  refine ⟨2 * Ca, by positivity, fun V hV β hβI ρ Uρ f hf N hN => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβI.1
  have hU := HRS.ME.NfU.rhoU_of_parxU hβm hβI Uρ
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

/-- **F6.2 (V-uniform copy of `pair_moments_unif`).** The constant `C₀` is chosen after
`d s βm βp c₀ Λ₀` and before `V`, `β`, `ρ`. The hypothesis on `(β, ρ)` is the thermal equation with
`V` together with `RhoU`; the original `_hV` is kept as `Torus.IsSmooth V` under the bound `V`. -/
theorem pair_moments_unifV {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2)
    (βm βp c₀ Λ₀ : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp) (hc₀ : 0 < c₀) (hΛ : 1 ≤ Λ₀) :
    ∃ C₀ : ℝ, ∀ (V : Torus d → ℝ), Torus.IsSmooth V → ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ,
      HRS.IsThermalDensity (HRS.periodicRiesz d s) V β ρ →
      HRS.ME.PmU.RhoU d βm βp c₀ Λ₀ β ρ →
      (∀ (K : ℝ) (ψ : Torus d → Torus d → ℝ), Measurable (Function.uncurry ψ) → IsSymmPair ψ →
        IsCanonicalPair (withDensityReal ρ) ψ → PsiSize s K ψ → ∀ N : ℕ, 2 ≤ N →
          evariance (Fstat ψ) (canonicalGibbs (periodicRiesz d s) V N β) +
              ∫⁻ X, ∑ i, ‖configGrad (Fstat ψ) X i‖ₑ ^ 2
                ∂(canonicalGibbs (periodicRiesz d s) V N β) ≤
            ENNReal.ofReal (C₀ * K ^ 2 / N)) ∧
      (∀ (K : ℝ) (j : Torus d → Torus d → ℝ), Measurable (Function.uncurry j) → IsSymmPair j →
        IsCanonicalPair (withDensityReal ρ) j → (∀ x y, x ≠ y → |j x y| ≤ K * wEnv s x y) →
        ∀ N : ℕ, 2 ≤ N →
          evariance (Fstat j) (canonicalGibbs (periodicRiesz d s) V N β) ≤
            ENNReal.ofReal (C₀ * K ^ 2 * logEN N / N)) ∧
      (∀ (K : ℝ) (b : Torus d → Torus d → ℝ), Measurable (Function.uncurry b) → IsSymmPair b →
        (∀ x y, x ≠ y → |b x y| ≤ K * wEnv s x y ^ 2) → ∀ N : ℕ, 2 ≤ N →
          evariance (fun X : Config d N => (N : ℝ) ^ (-(5 / 2 : ℝ)) * pairSumOrdered b X)
              (canonicalGibbs (periodicRiesz d s) V N β) ≤
            ENNReal.ofReal (C₀ * K ^ 2 / N)) ∧
      (∀ (K : ℝ) (g3 : Torus d → Torus d → Torus d → ℝ),
        Measurable (fun p : Torus d × Torus d × Torus d => g3 p.1 p.2.1 p.2.2) →
        IsSymmTriple g3 → IsCanonicalTriple (withDensityReal ρ) g3 →
        (∀ x y z, x ≠ y → x ≠ z → y ≠ z → |g3 x y z| ≤
          K * (wEnv s x y * wEnv s x z + wEnv s x y * wEnv s y z + wEnv s x z * wEnv s y z)) →
        ∀ N : ℕ, 2 ≤ N →
          evariance (fun X : Config d N => (N : ℝ) ^ (-(5 / 2 : ℝ)) * tripleSum g3 X)
              (canonicalGibbs (periodicRiesz d s) V N β) ≤
            ENNReal.ofReal (C₀ * K ^ 2 * logEN N ^ 2 / (N : ℝ) ^ 2)) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 ≤ s := by rw [hcrit]; linarith
  have hsd : s < d := by rw [hcrit]; linarith
  have hΛ0 : (0 : ℝ) ≤ Λ₀ := by linarith
  obtain ⟨Cψ, hCψ0, hCψ⟩ := HRS.ME.NfU.partpsi_all_unif hd hcrit βm βp c₀ Λ₀ hβm hββ hΛ hc₀
  obtain ⟨Ce, hCe0, hCe⟩ := HRS.ME.NfU.energy_all_unif hd hcrit βm βp c₀ Λ₀ hβm hββ hc₀ hΛ
  obtain ⟨Cj, hCj0, hCj⟩ := HRS.ME.NfU.partj_all_unif hd hcrit βm βp c₀ Λ₀ hβm hββ hΛ hc₀
  obtain ⟨Cb, hCb0, hCb⟩ := HRS.ME.NfU.partb_all_unif hd hcrit βm βp c₀ Λ₀ hβm hββ hΛ hc₀
  obtain ⟨Ct, hCt0, hCt⟩ := HRS.ME.NfU.partt_all_unif hd hcrit βm βp c₀ Λ₀ hβm hββ hc₀ hΛ
  refine ⟨Cψ + Ce + Cj + Cb + Ct, fun V _hV β hβ ρ hρ U => ?_⟩
  have hP : ∀ N : ℕ, canonicalGibbs (periodicRiesz d s) V N β =
      modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ) := by
    intro N
    refine canonicalGibbs_eq_modulatedGibbs (periodicRiesz d s) V β ρ hρ
      (fun x => periodicRiesz_neg x) ?_
    intro x
    exact (CoercAux.J_bounds (by omega : 1 ≤ d) hs0 hsd one_pos hρ.1 hΛ0 U.hup x).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro K ψ hm hsymm hcan hsz N hN
    rw [hP N]
    have hNp : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have h1 := hCψ β hβ ρ U K ψ hm hsymm hcan (fun x y hxy => hsz.size x y hxy) N hN
    have h2 := hCe β hβ ρ U K ψ hsymm hcan hsz.smooth hsz.grad N hN
    calc evariance (Fstat ψ) (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) +
          ∫⁻ X, ∑ i, ‖configGrad (Fstat ψ) X i‖ₑ ^ 2
            ∂(modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ))
        ≤ ENNReal.ofReal (Cψ * K ^ 2 / N) + ENNReal.ofReal (Ce * K ^ 2 / N) := add_le_add h1 h2
      _ = ENNReal.ofReal ((Cψ + Ce) * K ^ 2 / N) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1; ring
      _ ≤ _ := by
          refine ENNReal.ofReal_le_ofReal ?_
          refine div_le_div_of_nonneg_right ?_ hNp.le
          exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg K)
  · intro K j hm hsymm hcan hj N hN
    rw [hP N]
    have hNp : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hL := logEN_pos' (N := N) (by omega)
    refine (hCj β hβ ρ U K j hm hsymm hcan hj N hN).trans (ENNReal.ofReal_le_ofReal ?_)
    refine div_le_div_of_nonneg_right ?_ hNp.le
    have : 0 ≤ K ^ 2 * logEN N := by positivity
    nlinarith [mul_le_mul_of_nonneg_right (show Cj ≤ Cψ + Ce + Cj + Cb + Ct by linarith) this]
  · intro K b hm hsymm hb N hN
    rw [hP N]
    have hNp : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    refine (hCb β hβ ρ U K b hm hsymm hb N hN).trans (ENNReal.ofReal_le_ofReal ?_)
    refine div_le_div_of_nonneg_right ?_ hNp.le
    exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg K)
  · intro K g3 hm hsymm hcan hg3 N hN
    rw [hP N]
    have hNp : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hL := logEN_pos' (N := N) (by omega)
    refine (hCt β hβ ρ U K g3 hm hsymm hcan hg3 N hN).trans (ENNReal.ofReal_le_ofReal ?_)
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have : 0 ≤ K ^ 2 * logEN N ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right (show Ct ≤ Cψ + Ce + Cj + Cb + Ct by linarith) this]

/-- **F6.3 (V-uniform copy of `normal_form_unif_thermal`).** The fixed data are `d s hd hcrit βm βp hβm hββ`
and the bound `Bf` of the `C^j` norms of `V`. The constants `c₀, Λ₀` (bundle), `Cu`, `Cz` and `C₀` (pair
moments) are chosen before `V`; the constant `C` is their combination. -/
theorem normal_form_unif_thermalV {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2)
    (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp) (Bf : ℕ → ℝ) :
    ∃ C : ℝ, ∀ (V : Torus d → ℝ), Torus.IsSmooth V → (∀ j : ℕ, Torus.cbNorm j V ≤ Bf j) →
    ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ,
      IsThermalDensity (periodicRiesz d s) V β ρ → Torus.IsSmooth ρ → (∀ x, 0 < ρ x) →
      ∀ (f : Torus d → ℝ) (K₁ : ℝ) (ψ : Torus d → Torus d → ℝ), Torus.IsSmooth f →
        IsPairCorrector d s V β ρ f K₁ ψ → ∀ N : ℕ, 2 ≤ N →
          Integrable (quadStat (hTransport d s f) (withDensityReal ρ))
              (canonicalGibbs (periodicRiesz d s) V N β) ∧
          Integrable (Fstat (N := N) ψ) (canonicalGibbs (periodicRiesz d s) V N β) ∧
          Integrable (errStat d s ρ (N := N) ψ) (canonicalGibbs (periodicRiesz d s) V N β) ∧
          (∀ X : Config d N, X ∉ collisionSet d N →
            Real.sqrt N / 2 * centeredUnder (canonicalGibbs (periodicRiesz d s) V N β)
                (quadStat (hTransport d s f) (withDensityReal ρ)) X =
              -particleGen d s V β (Fstat ψ) X +
                centeredUnder (canonicalGibbs (periodicRiesz d s) V N β) (errStat d s ρ ψ) X -
                (2 / (N : ℝ)) * (Real.sqrt N * centeredUnder (canonicalGibbs (periodicRiesz d s) V N β)
                  (fun Y : Config d N => (1 / (N : ℝ)) * ∑ i, aCoef d s ρ f (Y i)) X)) ∧
          eLpNorm (centeredUnder (canonicalGibbs (periodicRiesz d s) V N β) (Fstat ψ)) 2
                (canonicalGibbs (periodicRiesz d s) V N β) +
              (∫⁻ X, ∑ i, ‖configGrad (Fstat ψ) X i‖ₑ ^ 2
                ∂(canonicalGibbs (periodicRiesz d s) V N β)) ^ (1 / 2 : ℝ) +
              eLpNorm (centeredUnder (canonicalGibbs (periodicRiesz d s) V N β) (errStat d s ρ ψ)) 2
                (canonicalGibbs (periodicRiesz d s) V N β) +
              ENNReal.ofReal (1 / (N : ℝ)) *
                eLpNorm (fun X : Config d N => Real.sqrt N *
                    centeredUnder (canonicalGibbs (periodicRiesz d s) V N β)
                      (fun Y : Config d N => (1 / (N : ℝ)) * ∑ i, aCoef d s ρ f (Y i)) X) 2
                  (canonicalGibbs (periodicRiesz d s) V N β) ≤
            ENNReal.ofReal (C * (K₁ + posSeminorm (8 * d + 80) f) * (N : ℝ) ^ (-(1 / 2 : ℝ))) := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 ≤ s := by rw [hcrit]; linarith
  have hsd : s < d := by rw [hcrit]; linarith
  obtain ⟨c₀, Λ₀, hc₀, hB⟩ := parxU_of_eqevoV hd s βm βp hcrit hs0 hsd hβm hββ Bf 1 (6 * d + 32)
    (by omega)
  obtain ⟨Cu, hCu0, hCu⟩ := q84e_modified_kernels_uniform_unifV hd hcrit βm βp c₀ Λ₀ hβm
  obtain ⟨Cz, hCz0, hCz⟩ := q84d_zeta_bound_unifV hd hcrit βm βp c₀ Λ₀ hβm hββ
  obtain ⟨C₀, hPM⟩ := pair_moments_unifV hd hcrit βm βp c₀ (max Λ₀ 1) hβm hββ hc₀
    (le_max_right _ _)
  obtain ⟨c0, hc0def⟩ : ∃ c0 : ℝ, c0 = Real.sqrt (max C₀ 0) := ⟨_, rfl⟩
  have hc0 : 0 ≤ c0 := by rw [hc0def]; exact Real.sqrt_nonneg _
  have hc0sq : c0 ^ 2 = max C₀ 0 := by rw [hc0def]; exact Real.sq_sqrt (le_max_right _ _)
  refine ⟨4 * c0 + 3 * c0 * Cu + Cz, fun V hV hVB β hβI ρ hρ hsm hpos => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβI.1
  have hρs : SmoothPosDensity ρ := ⟨hρ.1, hsm, hpos⟩
  have U := hB V hV hVB β hβI ρ hρ hsm hpos
  have hRU : HRS.ME.PmU.RhoU d βm βp c₀ (max Λ₀ 1) β ρ :=
    ⟨hβm, hβI, hc₀, hρs, fun x => U.rho_ge x, fun x => (U.rho_le x).trans (le_max_left _ _)⟩
  obtain ⟨hPM1, hPM2, hPM3, hPM4⟩ := hPM V hV β hβI ρ hρ hRU
  obtain ⟨C3, hC3⟩ := triple_canonical_proof hd hcrit β hβ V hV ρ hρ hρs
  intro f K₁ ψ hf hψ N hN
  have hN1 : 1 ≤ N := by omega
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN1
  have := Q84d.q84d_isProb hd hcrit hV hβ hN1 (N := N)
  set P := canonicalGibbs (periodicRiesz d s) V N β with hP
  have hK₁ := Q84d.q84d_K_nonneg hd hcrit hψ
  have hD := Q84d.q84d_posSeminorm_nonneg (8 * d + 80) f
  refine ⟨Q84d.q84d_quadStat_integrable hd hcrit β hβ V hV ρ hρ hρs f hf N hN,
    Q84d.q84d_Fstat_integrable hd hcrit β hβ V hV ρ hρ hρs f K₁ ψ hf hψ N hN,
    Q84d.q84d_errStat_integrable hd hcrit β hβ V hV ρ hρ hρs f K₁ ψ hf hψ N hN,
    Q84e.q84e_identity_centered hd hcrit hβ hV hρ hρs hf hψ hN, ?_⟩
  -- the kernels
  obtain ⟨-, hGcan, -, -, -⟩ := hC3 f K₁ ψ hf hψ
  obtain ⟨Jt, Bt, Gt, ⟨hJm, hJs, hJc, hJb⟩, ⟨hBm, hBs, hBb⟩, ⟨hGm, hGs, hGc, hGb⟩, hae⟩ :=
    hCu V hV β hβI ρ U f K₁ ψ hf hψ hGcan
  -- variance bounds
  have hlog := Q84e.q84e_logEN_pos hN1
  have v1 := hPM1 K₁ ψ hψ.measurable hψ.symm hψ.canonical hψ.size N hN
  have v2 := hPM2 K₁ Jt hJm hJs hJc hJb N hN
  have v3 := hPM3 (Cu * K₁) Bt hBm hBs hBb N hN
  have v4 := hPM4 (Cu * K₁) Gt hGm hGs hGc hGb N hN
  have hmax : ∀ x : ℝ, 0 ≤ x → C₀ * x ≤ c0 ^ 2 * x := fun x hx =>
    mul_le_mul_of_nonneg_right (by rw [hc0sq]; exact le_max_left _ _) hx
  set a₁ : ℝ := c0 ^ 2 * K₁ ^ 2 / N with ha₁
  have ha₁0 : 0 ≤ a₁ := by positivity
  have w1 : evariance (Fstat ψ) P + ∫⁻ X, ∑ i, ‖configGrad (Fstat ψ) X i‖ₑ ^ 2 ∂P ≤
      ENNReal.ofReal a₁ := by
    refine v1.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [ha₁]
    refine div_le_div_of_nonneg_right ?_ hNp.le
    have := hmax (K₁ ^ 2) (sq_nonneg _)
    linarith
  have hFψm : AEStronglyMeasurable (Fstat (N := N) ψ) P :=
    (Q84e.q84e_measurable_Fstat hψ.measurable).aestronglyMeasurable
  have T1 : eLpNorm (centeredUnder P (Fstat ψ)) 2 P ≤ ENNReal.ofReal (Real.sqrt a₁) :=
    Q84e.q84e_eLp_center_le P hFψm a₁ ha₁0 (le_trans le_self_add w1)
  have T2 : (∫⁻ X, ∑ i, ‖configGrad (Fstat ψ) X i‖ₑ ^ 2 ∂P) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Real.sqrt a₁) := by
    rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg ha₁0 (by norm_num)]
    exact ENNReal.rpow_le_rpow (le_trans le_add_self w1) (by norm_num)
  -- the error statistic
  set aJ : ℝ := c0 ^ 2 * K₁ ^ 2 * logEN N / N with haJ
  set aT : ℝ := c0 ^ 2 * (Cu * K₁) ^ 2 * logEN N ^ 2 / (N : ℝ) ^ 2 with haT
  set aB : ℝ := c0 ^ 2 * (Cu * K₁) ^ 2 / N with haB
  have haJ0 : 0 ≤ aJ := by positivity
  have haT0 : 0 ≤ aT := by positivity
  have haB0 : 0 ≤ aB := by positivity
  have wJ : evariance (Fstat Jt) P ≤ ENNReal.ofReal aJ := by
    refine v2.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [haJ]
    refine div_le_div_of_nonneg_right ?_ hNp.le
    have := hmax (K₁ ^ 2 * logEN N) (by positivity)
    linarith
  have wT : evariance (fun X : Config d N => (N : ℝ) ^ (-(5 / 2 : ℝ)) * tripleSum Gt X) P ≤
      ENNReal.ofReal aT := by
    refine v4.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [haT]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    have := hmax ((Cu * K₁) ^ 2 * logEN N ^ 2) (by positivity)
    linarith
  have wB : evariance (fun X : Config d N => (N : ℝ) ^ (-(5 / 2 : ℝ)) * pairSumOrdered Bt X) P ≤
      ENNReal.ofReal aB := by
    refine v3.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [haB]
    refine div_le_div_of_nonneg_right ?_ hNp.le
    have := hmax ((Cu * K₁) ^ 2) (sq_nonneg _)
    linarith
  have T3 : eLpNorm (centeredUnder P (errStat d s ρ ψ)) 2 P ≤
      ENNReal.ofReal (|2 / (N : ℝ)| * Real.sqrt aJ + Real.sqrt aT + Real.sqrt aB) :=
    Q84e.q84e_err_L2 P (E := errStat d s ρ (N := N) ψ) (FJ := Fstat Jt)
      (T := fun X : Config d N => (N : ℝ) ^ (-(5 / 2 : ℝ)) * tripleSum Gt X)
      (B := fun X : Config d N => (N : ℝ) ^ (-(5 / 2 : ℝ)) * pairSumOrdered Bt X)
      (c1 := 2 / (N : ℝ)) haJ0 haT0 haB0 (hae N hN)
      (Q84e.q84e_measurable_Fstat hJm).aestronglyMeasurable
      (Q84e.q84e_measurable_scaledTriple hGm _).aestronglyMeasurable
      (Q84e.q84e_measurable_scaledPair hBm _).aestronglyMeasurable wJ wT wB
  have T4 := hCz V hV β hβI ρ U f hf N hN
  -- arithmetic
  have harith := Q84e.q84e_arith hN1 hc0 hK₁ hCu0 hD hCz0
  calc _ ≤ ENNReal.ofReal (Real.sqrt a₁) + ENNReal.ofReal (Real.sqrt a₁) +
        ENNReal.ofReal (|2 / (N : ℝ)| * Real.sqrt aJ + Real.sqrt aT + Real.sqrt aB) +
        ENNReal.ofReal (Cz * posSeminorm (8 * d + 80) f * (N : ℝ) ^ (-(1 / 2 : ℝ))) := by
        gcongr
    _ = ENNReal.ofReal (Real.sqrt a₁ + Real.sqrt a₁ +
          (|2 / (N : ℝ)| * Real.sqrt aJ + Real.sqrt aT + Real.sqrt aB) +
          Cz * posSeminorm (8 * d + 80) f * (N : ℝ) ^ (-(1 / 2 : ℝ))) := by
        have hz : 0 ≤ Cz * posSeminorm (8 * d + 80) f * (N : ℝ) ^ (-(1 / 2 : ℝ)) :=
          mul_nonneg (mul_nonneg hCz0 hD) (Real.rpow_nonneg hNp.le _)
        have hsum : 0 ≤ |2 / (N : ℝ)| * Real.sqrt aJ + Real.sqrt aT + Real.sqrt aB := by positivity
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) hsum, ← ENNReal.ofReal_add (by positivity) hz]
    _ ≤ _ := ENNReal.ofReal_le_ofReal harith

end HRS.ME.FamU

end
