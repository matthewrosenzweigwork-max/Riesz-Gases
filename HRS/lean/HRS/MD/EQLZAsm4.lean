import HRS.MD.EQLZAsm3

/-!
# EQ-LZ packet ASM, part 4: `eqlz_assembly_proof`

The statement of `HRS.MD.EQLZ.eqlz_assembly` (`HRS/MD/EQLZSpec.lean`): the frozen `lyonsZheng_maximal_family`
(`HRS/Stochastic/LyonsZhengSpec.lean`, copied verbatim) from `SmoothMaximal`, `eqlz_cap` and `eqlz_marg`.  Tie in
`EQLZAsmTie.lean`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal
open HRS.LZ

namespace HRS.MD.EQLZ.Asm

theorem asm_smoothCfg_facts {d N : ℕ} {G : Config d N → ℝ} (hG : IsSmoothCfg G) :
    Measurable G ∧ ∃ B : ℝ, ∀ x, |G x| ≤ B := by
  have hc : Continuous (fun x : Torus (N * d) => G ((d1_configEquiv d N).symm x)) :=
    Cap.continuous_of_cdiff (Cap.isSmooth_cdiff hG)
  have hGe : ∀ x, G x = (fun y : Torus (N * d) => G ((d1_configEquiv d N).symm y)) (d1_configEquiv d N x) := by
    intro x; simp
  refine ⟨?_, ?_⟩
  · have : G = (fun y => G ((d1_configEquiv d N).symm y)) ∘ d1_configEquiv d N := funext hGe
    rw [this]; exact hc.measurable.comp (d1_configEquiv d N).measurable
  · obtain ⟨B, hB⟩ := b15_bounded_of_continuous hc
    exact ⟨B, fun x => by rw [hGe x]; exact hB _⟩

/-- (ASM, `eqlz_assembly`.)  Statement copied verbatim from `HRS.MD.EQLZ.eqlz_assembly`, with the frozen statement
`HRS.LZ.lyonsZheng_maximal_family` as conclusion. -/
theorem eqlz_assembly_proof (hsmooth : SmoothMaximal) (hcap : type_of% @HRS.MD.EQLZ.Cap.eqlz_cap_proof)
    (hmarg : type_of% @HRS.MD.EQLZMarg.eqlz_marg_proof) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d N : ℕ), 2 ≤ d → 2 ≤ N → ∀ (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
      (V : Torus d → ℝ), Torus.IsSmooth V → ∀ (β : ℝ) (hβ : 0 < β) (T a : ℝ), 0 ≤ T → 0 ≤ a →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsStationaryGibbsFlow P s hs0 hsd V β hβ (a + T) X₀ W X →
        ∀ F : ℕ → Config d N → ℝ,
          (∀ j, IsLZTest (canonicalGibbs (periodicRiesz d s) V N β) (F j)) →
          ∫⁻ ω, ⨆ t ∈ ratTimes a T,
              ∑' j, ENNReal.ofReal
                ((F j (X t.toNNReal ω) - ∫ Y, F j Y ∂(canonicalGibbs (periodicRiesz d s) V N β)) ^ 2) ∂P ≤
            ENNReal.ofReal C *
              (∑' j, ENNReal.ofReal (∫ Y, (F j Y -
                  ∫ Y', F j Y' ∂(canonicalGibbs (periodicRiesz d s) V N β)) ^ 2
                    ∂(canonicalGibbs (periodicRiesz d s) V N β)) +
                ENNReal.ofReal (β⁻¹ * T) *
                  ∑' j, ENNReal.ofReal (∫ Y, configGradSq (F j) Y
                    ∂(canonicalGibbs (periodicRiesz d s) V N β))) := by
  obtain ⟨C, hC, hsm⟩ := hsmooth
  refine ⟨C, hC, ?_⟩
  intro d N hd hN s hs0 hsd V hV β hβ T a hT ha Ω _ P _ X₀ W X hflow F hF
  have hprob : IsProbabilityMeasure (canonicalGibbs (periodicRiesz d s) V N β) :=
    (Cap.gibbs_facts (N := N) hd s hs0 hsd hV hβ).1
  set μ := canonicalGibbs (periodicRiesz d s) V N β with hμ
  have hmeasX : ∀ t, Measurable (X t) := by
    intro t
    obtain ⟨ℱ, W', hfil⟩ := hflow.filtered
    exact (hfil.adapted t).mono (ℱ.le (t : ℝ)) le_rfl
  have hlaw : ∀ t ∈ ratTimes a T, P.map (X t.toNNReal) = μ := fun t ht =>
    hmarg d N hd hN s hs0 hsd V hV β hβ (a + T) P X₀ W X hflow t (ha.trans ht.1.1)
      (by have := ht.1.2; linarith)
  have hR : (ratTimes a T).Countable :=
    (Set.countable_range ((↑) : ℚ → ℝ)).mono fun t ht => by
      obtain ⟨q, hq⟩ := ht.2; exact ⟨q, hq⟩
  have scalar : ∀ j, ∫⁻ ω, ⨆ t ∈ ratTimes a T,
      ENNReal.ofReal ((F j (X t.toNNReal ω) - ∫ Y, F j Y ∂μ) ^ 2) ∂P ≤
        ENNReal.ofReal C * (ENNReal.ofReal (∫ Y, (F j Y - ∫ Y', F j Y' ∂μ) ^ 2 ∂μ) +
          ENNReal.ofReal (β⁻¹ * T) * ENNReal.ofReal (∫ Y, configGradSq (F j) Y ∂μ)) := by
    intro j
    obtain ⟨G, hGs, hG1, hG2⟩ := hcap d N hd hN s hs0 hsd V hV β hβ (F j) (hF j)
    refine asm_countable P (fun t ω => ENNReal.ofReal ((F j (X t.toNNReal ω) - ∫ Y, F j Y ∂μ) ^ 2))
      _ hR (fun t _ => ?_) _ (fun S hS => ?_)
    · exact ENNReal.measurable_ofReal.comp ((((hF j).measurable.comp (hmeasX _)).sub_const _).pow_const 2)
    · refine asm_finite P μ (fun t => X t.toNNReal) S (fun t _ => hmeasX _)
        (fun t ht => hlaw t (hS ht)) C (β⁻¹ * T) (∫ Y, configGradSq (F j) Y ∂μ) (F j) (hF j).measurable
        (hF j).memLp G (fun k => (asm_smoothCfg_facts (hGs k)).1)
        (fun k => (asm_smoothCfg_facts (hGs k)).2) (fun k => ∫ x, configGradSq (G k) x ∂μ) hG1 hG2
        (fun k => ?_)
      refine le_trans (lintegral_mono fun ω => ?_)
        (hsm d N hd hN s hs0 hsd V hV β hβ T a hT ha P X₀ W X hflow (G k) (hGs k))
      exact iSup₂_le fun t ht => le_iSup₂ (f := fun t (_ : t ∈ ratTimes a T) =>
        ENNReal.ofReal ((G k (X t.toNNReal ω) - ∫ x, G k x ∂μ) ^ 2)) t (hS ht)
  calc ∫⁻ ω, ⨆ t ∈ ratTimes a T, ∑' j, ENNReal.ofReal ((F j (X t.toNNReal ω) - ∫ Y, F j Y ∂μ) ^ 2) ∂P
      ≤ ∫⁻ ω, ∑' j, ⨆ t ∈ ratTimes a T, ENNReal.ofReal ((F j (X t.toNNReal ω) - ∫ Y, F j Y ∂μ) ^ 2) ∂P :=
        lintegral_mono fun ω => iSup₂_le fun t ht => ENNReal.tsum_le_tsum fun j =>
          le_iSup₂ (f := fun t (_ : t ∈ ratTimes a T) =>
            ENNReal.ofReal ((F j (X t.toNNReal ω) - ∫ Y, F j Y ∂μ) ^ 2)) t ht
    _ = ∑' j, ∫⁻ ω, ⨆ t ∈ ratTimes a T, ENNReal.ofReal ((F j (X t.toNNReal ω) - ∫ Y, F j Y ∂μ) ^ 2) ∂P :=
        lintegral_tsum fun j => (Measurable.biSup _ hR fun t _ =>
          ENNReal.measurable_ofReal.comp
            ((((hF j).measurable.comp (hmeasX _)).sub_const _).pow_const 2)).aemeasurable
    _ ≤ ∑' j, ENNReal.ofReal C * (ENNReal.ofReal (∫ Y, (F j Y - ∫ Y', F j Y' ∂μ) ^ 2 ∂μ) +
          ENNReal.ofReal (β⁻¹ * T) * ENNReal.ofReal (∫ Y, configGradSq (F j) Y ∂μ)) :=
        ENNReal.tsum_le_tsum scalar
    _ = _ := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_add]
        simp only [ENNReal.tsum_mul_left]

end HRS.MD.EQLZ.Asm

end
