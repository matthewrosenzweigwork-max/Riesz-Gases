import HRS.ME.UnifP5F

/-!
# Uniform Lemma 4.6 (cavity response), part G (packet P5)

The five clauses of `HRS.cavity_response_proof` (`HRS/Equilibrium/CavityMain.lean`) with a constant `C` chosen
after `d, s, βm, βp, Λ, c` and before `β ∈ [βm, βp]` and the smooth density `ρ ≤ Λ`:

`HRS.ME.Unif.cavity_response_unif` (this is exactly the statement consumed by `me_marg_glue`:
`hPac`, `hFc`, `hzc`, `hDc0` of `HRS/ME/Marginal.lean`, with `Cc = C`, hold for every such `(β, ρ)` and `N ≥ 2`).
The lower bound `c₀ ≤ ρ` is not needed.  The proof is that of `cavity_response_proof` with every
`∃ C` input replaced by its uniform form (`UnifP2`, `UnifP4A`, `UnifP5A`-`F`).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.ME.Unif

open HRS HRS.External HRS.PoleCavityAux HRS.MarginalAux HRS.ProdTransfer HRS.CavResp

variable {d : ℕ} {s c : ℝ}

/-- Uniform `item2`: closeness of the first marginal to the cavity marginal. -/
theorem item2_unif (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (βm βp : ℝ) (hβm : 0 < βm)
    (hββ : βm ≤ βp) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (Λ : ℝ) (hΛ1 : 1 ≤ Λ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ →
      (∀ x, ρ x ≤ Λ) → ∀ N : ℕ, 2 ≤ N →
      (firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≪
          withDensityReal ρ ∧
        firstMarginal (critCavity d s c β ρ N) ≪ withDensityReal ρ ∧
        eLpNorm (fun y =>
            ((firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ))).rnDeriv
                (withDensityReal ρ) y).toReal -
              ((firstMarginal (critCavity d s c β ρ N)).rnDeriv (withDensityReal ρ) y).toReal)
            2 (withDensityReal ρ) ≤
          ENNReal.ofReal (C * Real.sqrt (Real.log N) / N)) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  obtain ⟨CL, hCL0, hCLU⟩ := cavity_L2_unif hd hs0 hsd βm βp hβm hββ Λ
  obtain ⟨Mp, hMp1, hMpU⟩ := pDens_bounds_unif hd hs0 hsd βm βp hβm hββ Λ
  obtain ⟨Mq, hMq0, hMqU⟩ := qDens_bound_unif hd hs0 hsd βm βp hβm hββ Λ
  refine ⟨2 * CL, by positivity, fun β hβI ρ hρ hΛ N hN => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβI.1
  have hμ := isProbabilityMeasure_mu hρ
  have hCL := hCLU β hβI ρ hρ hΛ
  have hMp := hMpU β hβI ρ hρ hΛ
  have hMq := hMqU β hβI ρ hρ hΛ
  obtain ⟨h1, h2, h3⟩ := gibbs_dens hd hcrit hβ hρ (c := c) hN
  refine ⟨h1, h3, ?_⟩
  have hcav := critCavity_eq hd hs0 hsd c β hρ N
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 0 < n := by omega
  have hlamdef : β / ((n + 1 : ℕ) : ℝ) = β / ((n + 1 : ℕ) : ℝ) := rfl
  obtain ⟨hlam, hln, -⟩ := lam_facts hd hs0 hsd hβ hρ hn hlamdef
  have hpm := measurable_pDens hd hs0 hsd hρ hlam hln
  have hqm := qDens_measurable hd hs0 hsd hβ hρ hn hlamdef
  have hqb : ∀ᵐ y ∂(withDensityReal ρ), qDens (periodicRiesz d s) (withDensityReal ρ) n
      (β / ((n + 1 : ℕ) : ℝ)) β y ≤ Mq := (hMq (n + 1) hN).2
  have hpb : ∀ y, pDens (periodicRiesz d s) (withDensityReal ρ) n (β / ((n + 1 : ℕ) : ℝ)) β y ≤ Mp :=
    fun y => (hMp (n + 1) hN y).2
  have hp0 : ∀ y, 0 ≤ pDens (periodicRiesz d s) (withDensityReal ρ) n (β / ((n + 1 : ℕ) : ℝ)) β y :=
    fun y => (pDens_pos hd hs0 hsd hρ hlam hln y).le
  have hq0 : ∀ y, 0 ≤ qDens (periodicRiesz d s) (withDensityReal ρ) n (β / ((n + 1 : ℕ) : ℝ)) β y :=
    fun y => ENNReal.toReal_nonneg
  have hmem : MemLp (fun y => pDens (periodicRiesz d s) (withDensityReal ρ) n (β / ((n + 1 : ℕ) : ℝ)) β y -
      qDens (periodicRiesz d s) (withDensityReal ρ) n (β / ((n + 1 : ℕ) : ℝ)) β y) 2 (withDensityReal ρ) :=
    MemLp.of_bound (hpm.sub hqm).aestronglyMeasurable (Mp + Mq) (by
      filter_upwards [hqb] with y hy
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hpb y, hp0 y, hq0 y])
  have hL2 := hCL n hn _ rfl
  obtain ⟨r1, -, -⟩ := rate_facts (d := d) hcrit hN
  have hbound : Real.sqrt (∫ y, (pDens (periodicRiesz d s) (withDensityReal ρ) n (β / ((n + 1 : ℕ) : ℝ)) β y -
      qDens (periodicRiesz d s) (withDensityReal ρ) n (β / ((n + 1 : ℕ) : ℝ)) β y) ^ 2
        ∂(withDensityReal ρ)) ≤ 2 * CL * Real.sqrt (Real.log ((n + 1 : ℕ) : ℝ)) / ((n + 1 : ℕ) : ℝ) := by
    refine hL2.trans ?_
    calc _ ≤ CL * (2 * Real.sqrt (Real.log ((n + 1 : ℕ) : ℝ)) / ((n + 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left r1 hCL0
      _ = _ := by ring
  refine le_trans (le_of_eq ?_) (eLpNorm_two_le hmem hbound)
  refine eLpNorm_congr_ae ?_
  filter_upwards [h2] with y hy
  rw [hy, hcav]
  rfl

/-- Uniform `item3`: the response equation up to `√(log N)/N`. -/
theorem item3_unif (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (βm βp : ℝ) (hβm : 0 < βm)
    (hββ : βm ≤ βp) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (Λ : ℝ) (hΛ1 : 1 ≤ Λ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ →
      (∀ x, ρ x ≤ Λ) → ∀ N : ℕ, 2 ≤ N →
      eLpNorm (fun y =>
          (((firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ))).rnDeriv
              (withDensityReal ρ) y).toReal - 1) +
            β * Kop (periodicRiesz d s) (withDensityReal ρ)
              (fun y' => ((firstMarginal (modulatedGibbs (periodicRiesz d s) N β
                (withDensityReal ρ))).rnDeriv (withDensityReal ρ) y').toReal - 1) y -
            projMean (withDensityReal ρ) (insertionDefect d s c β ρ N) y)
          2 (withDensityReal ρ) ≤
        ENNReal.ofReal (C * Real.sqrt (Real.log N) / N) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  obtain ⟨Cr, hCr0, hCrU⟩ := response_bound_unif hd hcrit βm βp hβm hββ c hc Λ hΛ1
  refine ⟨15 * Cr, by positivity, fun β hβI ρ hρ hΛ N hN => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβI.1
  have hμ := isProbabilityMeasure_mu hρ
  have hCr := hCrU β hβI ρ hρ hΛ
  obtain ⟨h1, h2, h3⟩ := gibbs_dens hd hcrit hβ hρ (c := c) hN
  have hDef : insertionDefect d s c β ρ N =
      insDefect (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β :=
    funext fun x => insertionDefect_eq_insDefect hd hs0 hsd c β hβ hρ hN x
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 0 < n := by omega
  obtain ⟨hmem, hsq⟩ := hCr n hn _ rfl
  obtain ⟨r1, r2, r3⟩ := rate_facts (d := d) hcrit hN
  have hbound : Real.sqrt (∫ x, ((pDens (periodicRiesz d s) (withDensityReal ρ) n (β / ((n + 1 : ℕ) : ℝ)) β x - 1) +
          β * Kop (periodicRiesz d s) (withDensityReal ρ)
            (fun y => pDens (periodicRiesz d s) (withDensityReal ρ) n (β / ((n + 1 : ℕ) : ℝ)) β y - 1) x -
          projMean (withDensityReal ρ)
            (insDefect (periodicRiesz d s) (withDensityReal ρ) n (β / ((n + 1 : ℕ) : ℝ)) β) x) ^ 2
          ∂(withDensityReal ρ)) ≤
      15 * Cr * Real.sqrt (Real.log ((n + 1 : ℕ) : ℝ)) / ((n + 1 : ℕ) : ℝ) := by
    refine hsq.trans ?_
    calc _ ≤ Cr * (11 * Real.sqrt (Real.log ((n + 1 : ℕ) : ℝ)) / ((n + 1 : ℕ) : ℝ) +
            2 * Real.sqrt (Real.log ((n + 1 : ℕ) : ℝ)) / ((n + 1 : ℕ) : ℝ) +
            2 * Real.sqrt (Real.log ((n + 1 : ℕ) : ℝ)) / ((n + 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left (by linarith) hCr0
      _ = _ := by ring
  refine le_trans (le_of_eq ?_) (eLpNorm_two_le hmem hbound)
  refine eLpNorm_congr_ae ?_
  have hKop : ∀ y, Kop (periodicRiesz d s) (withDensityReal ρ)
      (fun y' => ((firstMarginal (modulatedGibbs (periodicRiesz d s) (n + 1) β
        (withDensityReal ρ))).rnDeriv (withDensityReal ρ) y').toReal - 1) y =
      Kop (periodicRiesz d s) (withDensityReal ρ)
        (fun y' => pDens (periodicRiesz d s) (withDensityReal ρ) n (β / ((n + 1 : ℕ) : ℝ)) β y' - 1) y := by
    intro y
    unfold Kop
    have : (fun x => ∫ y', periodicRiesz d s (x - y') * (((firstMarginal (modulatedGibbs (periodicRiesz d s)
        (n + 1) β (withDensityReal ρ))).rnDeriv (withDensityReal ρ) y').toReal - 1) ∂(withDensityReal ρ)) =
        fun x => ∫ y', periodicRiesz d s (x - y') * (pDens (periodicRiesz d s) (withDensityReal ρ) n
          (β / ((n + 1 : ℕ) : ℝ)) β y' - 1) ∂(withDensityReal ρ) := by
      funext x
      refine integral_congr_ae ?_
      filter_upwards [h2] with y' hy'
      rw [hy']
      rfl
    rw [this]
  filter_upwards [h2] with y hy
  rw [hy, hKop y, hDef]
  rfl

/-- Uniform `item5`: the sup-norm bound of the first-marginal density. -/
theorem item5_unif (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (βm βp : ℝ) (hβm : 0 < βm)
    (hββ : βm ≤ βp) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (Λ : ℝ) (hΛ1 : 1 ≤ Λ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ →
      (∀ x, ρ x ≤ Λ) → ∀ N : ℕ, 2 ≤ N →
      ∀ᵐ y ∂(withDensityReal ρ),
        |((firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ))).rnDeriv
            (withDensityReal ρ) y).toReal - 1| ≤ C * Real.sqrt (deltaN d s N) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  obtain ⟨Cs, hCs0, hCsU⟩ := sup_dev_rate_unif hd hcrit βm βp hβm hββ c hc Λ hΛ1
  refine ⟨Cs, hCs0, fun β hβI ρ hρ hΛ N hN => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβI.1
  have hCs := hCsU β hβI ρ hρ hΛ
  obtain ⟨h1, h2, h3⟩ := gibbs_dens hd hcrit hβ hρ (c := c) hN
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 0 < n := by omega
  filter_upwards [h2] with y hy
  rw [hy]
  exact hCs n hn _ rfl y

/-- Uniform `partA`: the derivative statement and the defect bound `D_N ≤ C δ_N`. -/
theorem partA_unif (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (βm βp : ℝ) (hβm : 0 < βm)
    (hββ : βm ≤ βp) (c : ℝ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (Λ : ℝ) :
    ∃ C : ℝ, ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ →
      (∀ x, ρ x ≤ Λ) → ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d,
      Integrable (fun Y : Config d (N - 1) => ∑ i, gPlus d s c (x - Y i))
          (critCavity d s c β ρ N) ∧
        HasDerivWithinAt (insertionPressure d s c β ρ N x)
          (-((β / N) * ∫ Y, ∑ i, gPlus d s c (x - Y i) ∂(critCavity d s c β ρ N)))
          (Set.Ici 0) 0 ∧
        0 ≤ insertionDefect d s c β ρ N x ∧
        ENNReal.ofReal (insertionDefect d s c β ρ N x) =
          ∫⁻ t in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal ((1 - t) * (β / N) ^ 2) *
            evariance (fun Y : Config d (N - 1) => ∑ i, gPlus d s c (x - Y i))
              (critPole d s c β ρ N x t) ∧
        insertionDefect d s c β ρ N x ≤ C * deltaN d s N := by
  obtain ⟨C, hCU⟩ := insDefect_le_unif hd hs0 hsd βm βp hβm hββ Λ
  refine ⟨C, fun β hβI ρ hρ hΛ N hN x => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβI.1
  obtain ⟨CA, hA⟩ := CavResp.partA hd hs0 hsd β hβ hρ c hc
  obtain ⟨a1, a2, a3, a4, -⟩ := hA N hN x
  refine ⟨a1, a2, a3, a4, ?_⟩
  rw [insertionDefect_eq_insDefect hd hs0 hsd c β hβ hρ hN x]
  exact (hCU β hβI ρ hρ hΛ N hN x).2.1

/-- **Lemma 4.6 (`M:R:lem:cavity`, cavity response), uniform form.**  The constant `C` is chosen after
`d, s, βm, βp, Λ, c` and before `β ∈ [βm, βp]`, the smooth density `ρ ≤ Λ` and `N ≥ 2`. -/
theorem cavity_response_unif_aux (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (βm βp : ℝ) (hβm : 0 < βm)
    (hββ : βm ≤ βp) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (Λ : ℝ) (hΛ1 : 1 ≤ Λ) :
    ∃ C : ℝ, ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ N : ℕ, 2 ≤ N →
      (∀ x : Torus d,
        Integrable (fun Y : Config d (N - 1) => ∑ i, gPlus d s c (x - Y i))
            (critCavity d s c β ρ N) ∧
          HasDerivWithinAt (insertionPressure d s c β ρ N x)
            (-((β / N) * ∫ Y, ∑ i, gPlus d s c (x - Y i) ∂(critCavity d s c β ρ N)))
            (Set.Ici 0) 0 ∧
          0 ≤ insertionDefect d s c β ρ N x ∧
          ENNReal.ofReal (insertionDefect d s c β ρ N x) =
            ∫⁻ t in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal ((1 - t) * (β / N) ^ 2) *
              evariance (fun Y : Config d (N - 1) => ∑ i, gPlus d s c (x - Y i))
                (critPole d s c β ρ N x t) ∧
          insertionDefect d s c β ρ N x ≤ C * deltaN d s N) ∧
      (firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≪
          withDensityReal ρ ∧
        firstMarginal (critCavity d s c β ρ N) ≪ withDensityReal ρ ∧
        eLpNorm (fun y =>
            ((firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ))).rnDeriv
                (withDensityReal ρ) y).toReal -
              ((firstMarginal (critCavity d s c β ρ N)).rnDeriv (withDensityReal ρ) y).toReal)
            2 (withDensityReal ρ) ≤
          ENNReal.ofReal (C * Real.sqrt (Real.log N) / N)) ∧
      eLpNorm (fun y =>
          (((firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ))).rnDeriv
              (withDensityReal ρ) y).toReal - 1) +
            β * Kop (periodicRiesz d s) (withDensityReal ρ)
              (fun y' => ((firstMarginal (modulatedGibbs (periodicRiesz d s) N β
                (withDensityReal ρ))).rnDeriv (withDensityReal ρ) y').toReal - 1) y -
            projMean (withDensityReal ρ) (insertionDefect d s c β ρ N) y)
          2 (withDensityReal ρ) ≤
        ENNReal.ofReal (C * Real.sqrt (Real.log N) / N) ∧
      (∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        firstMarginal (critPole d s c β ρ N x t) ≪ withDensityReal ρ ∧
          ∀ᵐ y ∂(withDensityReal ρ),
            |((firstMarginal (critPole d s c β ρ N x t)).rnDeriv (withDensityReal ρ) y).toReal -
                Real.exp (-(t * (β / N)) * gPlus d s c (x - y))| ≤
              C * Real.sqrt (deltaN d s N) * Real.exp (-(t * (β / N)) * gPlus d s c (x - y))) ∧
      (∀ᵐ y ∂(withDensityReal ρ),
        |((firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ))).rnDeriv
            (withDensityReal ρ) y).toReal - 1| ≤ C * Real.sqrt (deltaN d s N)) := by
  obtain ⟨hs0, hsd⟩ := PoleCavityAux.hs_aux hd hcrit
  obtain ⟨CA, hAU⟩ := partA_unif hd hs0 hsd βm βp hβm hββ c hc Λ
  obtain ⟨C2, hC20, h2U⟩ := item2_unif hd hcrit βm βp hβm hββ hc Λ hΛ1
  obtain ⟨C3, hC30, h3U⟩ := item3_unif hd hcrit βm βp hβm hββ hc Λ hΛ1
  obtain ⟨C4, hC40, h4U⟩ := pole_prefactor_unif hd hcrit βm βp hβm hββ hc Λ hΛ1
  obtain ⟨C5, hC50, h5U⟩ := item5_unif hd hcrit βm βp hβm hββ hc Λ hΛ1
  obtain ⟨Cm, hCm⟩ : ∃ Cm : ℝ, Cm = max (max (max CA C2) (max C3 C4)) C5 := ⟨_, rfl⟩
  have hCA : CA ≤ Cm := hCm ▸ ((le_max_left CA C2).trans ((le_max_left _ _).trans (le_max_left _ _)))
  have hC2 : C2 ≤ Cm := hCm ▸ ((le_max_right CA C2).trans ((le_max_left _ _).trans (le_max_left _ _)))
  have hC3 : C3 ≤ Cm := hCm ▸ ((le_max_left C3 C4).trans ((le_max_right _ _).trans (le_max_left _ _)))
  have hC4 : C4 ≤ Cm := hCm ▸ ((le_max_right C3 C4).trans ((le_max_right _ _).trans (le_max_left _ _)))
  have hC5 : C5 ≤ Cm := hCm ▸ (le_max_right _ _)
  refine ⟨Cm, fun β hβI ρ hρ hΛ N hN => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβI.1
  have hA := hAU β hβI ρ hρ hΛ
  have h2 := h2U β hβI ρ hρ hΛ
  have h3 := h3U β hβI ρ hρ hΛ
  have h4 := h4U β hβI ρ hρ hΛ
  have h5 := h5U β hβI ρ hρ hΛ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨a1, a2, a3, a4, a5⟩ := hA N hN x
    refine ⟨a1, a2, a3, a4, a5.trans ?_⟩
    have hδ : 0 ≤ deltaN d s N := (inv_nonneg.2 (by positivity : (0 : ℝ) ≤ N)).trans
      (MarginalAux.inv_le_deltaN (d := d) hs0 N (by omega))
    exact mul_le_mul_of_nonneg_right hCA hδ
  · obtain ⟨b1, b2, b3⟩ := h2 N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    refine ⟨b1, b2, b3.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC2 (Real.sqrt_nonneg _)) hN0.le
  · have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    refine (h3 N hN).trans (ENNReal.ofReal_le_ofReal ?_)
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC3 (Real.sqrt_nonneg _)) hN0.le
  · intro x t ht
    obtain ⟨b1, b2⟩ := h4 N hN x t ht
    refine ⟨b1, b2.mono fun y hy => hy.trans ?_⟩
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC4 (Real.sqrt_nonneg _))
      (Real.exp_pos _).le
  · exact (h5 N hN).mono fun y hy =>
      hy.trans (mul_le_mul_of_nonneg_right hC5 (Real.sqrt_nonneg _))

/-- **Lemma 4.6 (`M:R:lem:cavity`, cavity response), uniform form** (any upper bound `Λ` on the density). -/
theorem cavity_response_unif {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (βm βp : ℝ)
    (hβm : 0 < βm) (hββ : βm ≤ βp) (Λ : ℝ) (c : ℝ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) :
    ∃ C : ℝ, ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ N : ℕ, 2 ≤ N →
      (∀ x : Torus d,
        Integrable (fun Y : Config d (N - 1) => ∑ i, gPlus d s c (x - Y i))
            (critCavity d s c β ρ N) ∧
          HasDerivWithinAt (insertionPressure d s c β ρ N x)
            (-((β / N) * ∫ Y, ∑ i, gPlus d s c (x - Y i) ∂(critCavity d s c β ρ N)))
            (Set.Ici 0) 0 ∧
          0 ≤ insertionDefect d s c β ρ N x ∧
          ENNReal.ofReal (insertionDefect d s c β ρ N x) =
            ∫⁻ t in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal ((1 - t) * (β / N) ^ 2) *
              evariance (fun Y : Config d (N - 1) => ∑ i, gPlus d s c (x - Y i))
                (critPole d s c β ρ N x t) ∧
          insertionDefect d s c β ρ N x ≤ C * deltaN d s N) ∧
      (firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≪
          withDensityReal ρ ∧
        firstMarginal (critCavity d s c β ρ N) ≪ withDensityReal ρ ∧
        eLpNorm (fun y =>
            ((firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ))).rnDeriv
                (withDensityReal ρ) y).toReal -
              ((firstMarginal (critCavity d s c β ρ N)).rnDeriv (withDensityReal ρ) y).toReal)
            2 (withDensityReal ρ) ≤
          ENNReal.ofReal (C * Real.sqrt (Real.log N) / N)) ∧
      eLpNorm (fun y =>
          (((firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ))).rnDeriv
              (withDensityReal ρ) y).toReal - 1) +
            β * Kop (periodicRiesz d s) (withDensityReal ρ)
              (fun y' => ((firstMarginal (modulatedGibbs (periodicRiesz d s) N β
                (withDensityReal ρ))).rnDeriv (withDensityReal ρ) y').toReal - 1) y -
            projMean (withDensityReal ρ) (insertionDefect d s c β ρ N) y)
          2 (withDensityReal ρ) ≤
        ENNReal.ofReal (C * Real.sqrt (Real.log N) / N) ∧
      (∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        firstMarginal (critPole d s c β ρ N x t) ≪ withDensityReal ρ ∧
          ∀ᵐ y ∂(withDensityReal ρ),
            |((firstMarginal (critPole d s c β ρ N x t)).rnDeriv (withDensityReal ρ) y).toReal -
                Real.exp (-(t * (β / N)) * gPlus d s c (x - y))| ≤
              C * Real.sqrt (deltaN d s N) * Real.exp (-(t * (β / N)) * gPlus d s c (x - y))) ∧
      (∀ᵐ y ∂(withDensityReal ρ),
        |((firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ))).rnDeriv
            (withDensityReal ρ) y).toReal - 1| ≤ C * Real.sqrt (deltaN d s N)) := by
  obtain ⟨C, hC⟩ := cavity_response_unif_aux hd hcrit βm βp hβm hββ hc (max Λ 1) (le_max_right _ _)
  exact ⟨C, fun β hβ ρ hρ hΛ N hN => hC β hβ ρ hρ (fun x => (hΛ x).trans (le_max_left _ _)) N hN⟩

end HRS.ME.Unif

end
