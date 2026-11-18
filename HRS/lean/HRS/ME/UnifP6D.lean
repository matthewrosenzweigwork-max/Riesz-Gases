import HRS.ME.UnifP6C

/-!
# Uniform Proposition 4.8, part D (packet P6): pole/cavity marginal estimates

Uniform forms of `conv_gPlus`, `pole_marg_le`, `pole_dual` (Lemma 4.6 inputs of Proposition 4.8).
The `CavRespUnif` predicate packages the only input from the
(uniform) Lemma 4.6 (`cavity_response`, packet P5) is `CavRespUnif`: the clauses 2 and 4 of its conclusion.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.ME.Unif

open HRS HRS.External HRS.PoleCavityAux HRS.MarginalAux HRS.ProdTransfer HRS.CavResp HRS.L48

variable {d : ℕ} {s : ℝ}

/-- Clauses 2 and 4 of the conclusion of Lemma 4.6 (`cavity_response`), in uniform form: this is the
only input from the uniform cavity response used by Proposition 4.8 and 4.9.  It follows from the uniform
`cavity_response` (conjuncts 2 and 4) with one common constant. -/
def CavRespUnif (d : ℕ) (s c βm βp c₀ Λ : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, UFam d c₀ Λ ρ → ∀ N : ℕ, 2 ≤ N →
    (firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ)) ≪ withDensityReal ρ ∧
      firstMarginal (critCavity d s c β ρ N) ≪ withDensityReal ρ ∧
      eLpNorm (fun y =>
          ((firstMarginal (modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρ))).rnDeriv
              (withDensityReal ρ) y).toReal -
            ((firstMarginal (critCavity d s c β ρ N)).rnDeriv (withDensityReal ρ) y).toReal)
          2 (withDensityReal ρ) ≤
        ENNReal.ofReal (C * Real.sqrt (Real.log N) / N)) ∧
    (∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      firstMarginal (critPole d s c β ρ N x t) ≪ withDensityReal ρ ∧
        ∀ᵐ y ∂(withDensityReal ρ),
          |((firstMarginal (critPole d s c β ρ N x t)).rnDeriv (withDensityReal ρ) y).toReal -
              Real.exp (-(t * (β / N)) * gPlus d s c (x - y))| ≤
            C * Real.sqrt (deltaN d s N) * Real.exp (-(t * (β / N)) * gPlus d s c (x - y)))

/-- Uniform `conv_gPlus`. -/
theorem conv_gPlus_unif_fam (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (c : ℝ)
    (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (c₀ Λ : ℝ) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ ρ : Torus d → ℝ, UFam d c₀ Λ ρ → ∀ y,
      0 ≤ convMeasure (gPlus d s c) (withDensityReal ρ) y ∧
      convMeasure (gPlus d s c) (withDensityReal ρ) y ≤ Cg := by
  obtain ⟨B, Cc, hB0, hK⟩ := NfU.kerData_periodicRiesz_unif hd hs0 hsd Λ
  refine ⟨|Cc| + |c|, by positivity, fun ρ hF y => ?_⟩
  have hρ := hF.smooth
  have hμ := isProbabilityMeasure_mu hρ
  have hKρ := hK ρ hρ hF.up
  refine ⟨?_, ?_⟩
  · exact integral_nonneg fun z => hc _
  · have hconv : convMeasure (gPlus d s c) (withDensityReal ρ) y =
        convMeasure (periodicRiesz d s) (withDensityReal ρ) y + c := by
      unfold convMeasure gPlus
      rw [integral_add (hKρ.int y) (integrable_const _)]
      simp
    rw [hconv]
    have := (abs_le.1 (hKρ.conv y)).2
    linarith [le_abs_self c, le_abs_self Cc]

/-- Uniform `pole_marg_le`. -/
theorem pole_marg_le_unif_fam (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (βm βp : ℝ) (hβm : 0 < βm)
    (c₀ Λ : ℝ) :
    ∃ M1 : ℝ, 0 < M1 ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, UFam d c₀ Λ ρ →
      ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) ≪
          withDensityReal ρ ∧
        ∀ j : Fin (N - 1),
          (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t).map
              (fun Y : Config d (N - 1) => Y j) ≤ ENNReal.ofReal M1 • withDensityReal ρ := by
  obtain ⟨C1, hC1, h1_all⟩ := pole_density_clauses_unif hd hs0 hsd βm βp hβm Λ
  obtain ⟨B, hB⟩ := periodicRiesz_ge (d := d) hd hs0 hsd
  have hB0 : 0 ≤ max B 0 := le_max_right _ _
  refine ⟨C1 * Real.exp (βp * max B 0), by positivity, fun β hβI ρ hF N hN x t ht => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβI.1
  have hρ := hF.smooth
  have hμ := isProbabilityMeasure_mu hρ
  have h1 := h1_all β hβI ρ hρ hF.up

  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlam : 0 ≤ β / N := by positivity
  have hn1 : 0 < N - 1 := by omega
  obtain ⟨⟨hac, hle⟩, -⟩ := h1 N hN x t ht
  haveI := pole_isProb hd hs0 hsd β hρ (N - 1) (β / N) hlam x t ht.1
  haveI hνp := isProb_firstMarginal hn1 (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t)
  refine ⟨hac, fun j => ?_⟩
  have hexch := MarginalAux.poleLaw_exchangeable hd hs0 hsd β hρ (N - 1) (β / N) hlam x t
  have hfm : firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) =
      (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t).map
        (fun Y : Config d (N - 1) => Y ⟨0, hn1⟩) := by
    unfold firstMarginal; rw [dif_pos hn1]
  rw [hexch.marginal_eq j ⟨0, hn1⟩, ← hfm]
  refine Measure.le_iff'.2 fun A => ?_
  have hlam1 : β / N ≤ β := by
    rw [div_le_iff₀ hN0]
    have : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    nlinarith
  have hbd : ∀ᵐ y ∂(withDensityReal ρ),
      (firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t)).rnDeriv
        (withDensityReal ρ) y ≤ ENNReal.ofReal (C1 * Real.exp (βp * max B 0)) := by
    filter_upwards [hle] with y hy
    refine hy.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC1.le))
    have h4 := hB (x - y)
    have h5 : 0 ≤ t * (β / N) := mul_nonneg ht.1 hlam
    have h6 : t * (β / N) ≤ β := by nlinarith [ht.2]
    have h7 : -B ≤ periodicRiesz d s (x - y) := by linarith
    have h8 : β * max B 0 ≤ βp * max B 0 := mul_le_mul_of_nonneg_right hβI.2 hB0
    nlinarith [le_max_left B 0, h8]
  have hA : (firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t)) A =
      ∫⁻ y in A, (firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t)).rnDeriv
        (withDensityReal ρ) y ∂(withDensityReal ρ) := by
    rw [Measure.setLIntegral_rnDeriv hac]
  rw [hA]
  calc _ ≤ ∫⁻ y in A, ENNReal.ofReal (C1 * Real.exp (βp * max B 0)) ∂(withDensityReal ρ) :=
        lintegral_mono_ae (ae_restrict_of_ae hbd)
    _ = _ := by simp [Measure.smul_apply]


/-- Uniform `pole_dual`. -/
theorem pole_dual_unif_fam (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (βm βp : ℝ) (hβm : 0 < βm)
    (hββ : βm ≤ βp) (c₀ Λ : ℝ) :
    ∃ Cd : ℝ, 0 ≤ Cd ∧ ∀ β ∈ Set.Icc βm βp, ∀ ρ : Torus d → ℝ, UFam d c₀ Λ ρ →
      ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ f : Torus d → ℝ, Measurable f → ∀ K : ℝ, (∀ y, |f y| ≤ K) →
        |∫ y, f y ∂(firstMarginal
              (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t)) -
            ∫ y, f y ∂(firstMarginal
              (cavityLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β))| ≤
          Cd * Real.sqrt (∫ y, f y ^ 2 ∂(withDensityReal ρ)) * Real.sqrt (deltaN d s N / N) := by
  obtain ⟨C₁, hC₁, hvar_all⟩ := pole_variance_clause_unif hd hs0 hsd βm βp hβm Λ
  obtain ⟨Cd, hCd_all⟩ := insDefect_le_unif hd hs0 hsd βm βp hβm hββ Λ
  obtain ⟨B, hB0, hB⟩ := MarginalAux.rieszB hd hs0 hsd
  have hgm := measurable_periodicRiesz hd hs0 hsd
  have hβp : 0 < βp := lt_of_lt_of_le hβm hββ
  set K1 : ℝ := C₁ * Real.exp (βp * B) with hK1
  set K2 : ℝ := |Cd| * Real.exp |Cd| with hK2
  have hK1p : 0 ≤ K1 := by positivity
  have hK2p : 0 ≤ K2 := by positivity
  refine ⟨2 * Real.sqrt (2 * (K1 * K2)), by positivity, fun β hβI ρ hF N hN x t ht f hfm K hf => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβI.1
  have hβle : β ≤ βp := hβI.2
  have hρ := hF.smooth
  have hμ := isProbabilityMeasure_mu hρ
  have hvar := hvar_all β hβI ρ hρ hF.up
  have hCd := hCd_all β hβI ρ hρ hF.up
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlam : 0 ≤ β / N := by positivity
  have hn1 : 0 < N - 1 := by omega
  have hn0 : (0 : ℝ) < ((N - 1 : ℕ) : ℝ) := by exact_mod_cast hn1
  have hnN : (N : ℝ) ≤ 2 * ((N - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hln : β / N * ((N - 1 : ℕ) : ℝ) ≤ β := by
    rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
    have : β / N * ((N : ℝ) - 1) = β - β / N := by field_simp
    rw [this]; linarith
  set n : ℕ := N - 1 with hn
  set lam : ℝ := β / N with hlamdef
  set L : ℝ := ∫ y, f y ^ 2 ∂(withDensityReal ρ) with hL
  have hL0 : 0 ≤ L := integral_nonneg fun y => sq_nonneg _
  haveI hP0 := cavity_isProb hd hs0 hsd β hρ n lam hlam
  set P0 := cavityLaw (periodicRiesz d s) (withDensityReal ρ) n lam β with hP0def
  have hδ0 : 0 ≤ deltaN d s N := by
    have := inv_le_deltaN (d := d) hs0 N (by omega)
    exact (inv_nonneg.2 hN0.le).trans this
  have hδ1 : deltaN d s N ≤ 1 := deltaN_le_one hs0 hsd (by omega) N (by omega)
  have hRHS : 0 ≤ 2 * Real.sqrt (2 * (K1 * K2)) * Real.sqrt L * Real.sqrt (deltaN d s N / N) := by
    positivity
  rcases eq_or_lt_of_le ht.1 with h0 | htpos
  · rw [← h0, poleLaw_zero_eq hd hs0 hsd β hρ n lam hlam x, ← hP0def, sub_self, abs_zero]
    exact hRHS
  have hXm' : Measurable fun Y : Config d n => t * Xx (periodicRiesz d s) lam x Y :=
    (measurable_Xx hgm lam x).const_mul t
  have hbX := Xx_le hd hs0 hsd hlam hln hB0 hB x
  have hb' : ∀ Y : Config d n, t * Xx (periodicRiesz d s) lam x Y ≤ β * B := by
    intro Y
    have h1 := hbX Y
    have h2 : 0 ≤ β * B := by positivity
    nlinarith [ht.2]
  have hφm := measurable_fracF (n := n) hfm
  have htv := EF.ef_tv (P := P0) hXm' hb' hφm (abs_fracF_le hn1 hf)
  have e1 : P0.tilted (fun Y => t * Xx (periodicRiesz d s) lam x Y) =
      poleLaw (periodicRiesz d s) (withDensityReal ρ) n lam β x t :=
    (poleLaw_eq_tilted_cavity hd hs0 hsd β hρ n lam hlam x t).symm
  have e0 : P0 = poleLaw (periodicRiesz d s) (withDensityReal ρ) n lam β x 0 :=
    (poleLaw_zero_eq hd hs0 hsd β hρ n lam hlam x).symm
  haveI hPt := pole_isProb hd hs0 hsd β hρ n lam hlam x t ht.1
  have hint1 : ∫ Y, fracF f Y ∂(P0.tilted (fun Y => t * Xx (periodicRiesz d s) lam x Y)) =
      ∫ y, f y ∂(firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) n lam β x t)) := by
    rw [e1]
    exact integral_fracF hn1 hfm hf _ (poleLaw_exchangeable hd hs0 hsd β hρ n lam hlam x t)
  have hint0 : ∫ Y, fracF f Y ∂P0 = ∫ y, f y ∂(firstMarginal P0) :=
    integral_fracF hn1 hfm hf P0 (cavityLaw_exchangeable hd hs0 hsd β hρ n lam)
  have hKm : ∀ {v : ℝ}, v ≤ C₁ * Real.exp (β * B) * (∫ y, f y ^ 2 ∂(withDensityReal ρ)) / ((N - 1 : ℕ) : ℝ) →
      v ≤ (K1 * L) / (n : ℝ) := fun h => h.trans (by
    rw [hK1, hL]
    have hn0' : (0 : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have hLn : 0 ≤ ∫ y, f y ^ 2 ∂(withDensityReal ρ) := integral_nonneg fun y => sq_nonneg _
    have hexp : Real.exp (β * B) ≤ Real.exp (βp * B) := Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hβle hB0)
    have := mul_le_mul_of_nonneg_left hexp hC₁.le
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right this hLn) hn0')
  have hV0 : Var[fracF (n := n) f; P0] ≤ (K1 * L) / (n : ℝ) := by
    rw [e0]
    have := var_fracF_le hd hs0 hsd hβ hρ hC₁ hvar hB0 hB (N := N) hN x (t := 0) ⟨le_rfl, zero_le_one⟩
      hfm hf
    exact hKm (by simpa [mul_assoc] using this)
  have hV1 : Var[fracF (n := n) f; P0.tilted (fun Y => t * Xx (periodicRiesz d s) lam x Y)] ≤
      (K1 * L) / (n : ℝ) := by
    rw [e1]
    have := var_fracF_le hd hs0 hsd hβ hρ hC₁ hvar hB0 hB (N := N) hN x ht hfm hf
    exact hKm (by simpa [mul_assoc] using this)
  -- the second difference of the cumulant generating function
  obtain ⟨-, -, hΔ1⟩ := hCd N hN x
  have hXmx := measurable_Xx hgm lam x (n := n)
  have hmono := cgf_diff_mono (P := P0) hXmx hbX htpos ht.2
  have hc1 : cgf (fun Y => t * Xx (periodicRiesz d s) lam x Y) P0 1 =
      cgf (Xx (periodicRiesz d s) lam x) P0 t := by
    unfold cgf mgf; congr 2; funext Y; congr 1; ring
  have hc2 : cgf (fun Y => t * Xx (periodicRiesz d s) lam x Y) P0 (1 / 2) =
      cgf (Xx (periodicRiesz d s) lam x) P0 (t / 2) := by
    unfold cgf mgf; congr 2; funext Y; congr 1; ring
  have hΔ' : cgf (fun Y => t * Xx (periodicRiesz d s) lam x Y) P0 1 -
      2 * cgf (fun Y => t * Xx (periodicRiesz d s) lam x Y) P0 (1 / 2) ≤
      |Cd| * deltaN d s N := by
    rw [hc1, hc2]
    exact (hmono.trans hΔ1).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hδ0)
  have hee := exp_sub_one_le _ |Cd| (deltaN d s N) hδ0 hδ1 (abs_nonneg _) hΔ'
  rw [hint1, hint0] at htv
  refine htv.trans ?_
  have hch := sqrt_chain (n := (n : ℝ)) (N := (N : ℝ)) hn0 hN0 hnN (mul_nonneg hK1p hL0) hK2p hδ0
    hV0 hV1 hee
  refine hch.trans (le_of_eq ?_)
  rw [show 2 * (K1 * L * K2) = (2 * (K1 * K2)) * L by ring, Real.sqrt_mul (by positivity)]
  ring

/-! ### Duality for densities and the mixture step -/

end HRS.ME.Unif

end
