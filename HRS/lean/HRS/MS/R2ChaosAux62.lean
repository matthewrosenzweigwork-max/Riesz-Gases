import HRS.MS.R2ChaosAux61

/-!
# HRS.MS.R2ChaosAux62 -- S9.6 (P4): conclusion (ii) for polynomial kernels

Packet S94 (S9.6), namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.

`s94_part_ii_poly`: as `s94_part_ii`, but only `N ≥ 2` is identified with the continuous image (the statement is asymptotic in `N`);
measurability of the `N`-th integrated process for every `N` is an input (`hint`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.deprecated false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2Chaos

open HRS.Whole

variable {d : ℕ}

section PartIIPoly

variable {T : ℝ} {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)]
  {P : ∀ N, Measure (Ω N)} [∀ N, IsProbabilityMeasure (P N)]
  {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {ξ : (Euc d → ℝ) → Ω' → C(Set.Icc (0 : ℝ) T, ℝ)}

theorem s94_part_ii_poly (hT : 0 < T) {μ : Measure (Euc d)} {h : ℝ → Euc d → Euc d → ℝ} {F : ℝ → Ω' → ℝ}
    {X : ∀ N, ℝ≥0 → Ω N → EucConfig d N}
    (hF2 : ∀ ζ, MemLp (fun t => F t ζ) 2 (volume.restrict (Set.Icc (0 : ℝ) T)))
    (hae : ∀ N, 2 ≤ N → ∀ᵐ ζ ∂(P N), MemLp (fun t => r2QuadFluct μ h (P N) (X N) t ζ) 2
      (volume.restrict (Set.Icc (0 : ℝ) T)))
    {k : ℕ} {aa : Fin k → Euc d → ℝ}
    (hL2 : ∀ N, Measurable fun ζ => r2L2Path T (fun t => r2QuadFluct μ h (P N) (X N) t ζ))
    (hint : ∀ N, Measurable fun ζ => r2IntPath T (fun t => r2QuadFluct μ h (P N) (X N) t ζ))
    (hc : ∀ N, AEMeasurable (fun ζ i => r2ContPath T (r2EmpFluct μ (aa i) (X N) ζ)) (P N))
    (hi : TendstoInDistribution
      (fun N ζ => (r2L2Path T (fun t => r2QuadFluct μ h (P N) (X N) t ζ),
        fun i => r2ContPath T (r2EmpFluct μ (aa i) (X N) ζ))) atTop
      (fun ζ' => (r2L2Path T (fun t => F t ζ'), fun i => ξ (aa i) ζ')) P P') :
    TendstoInDistribution
      (fun N ζ => (r2L2Path T (fun t => r2QuadFluct μ h (P N) (X N) t ζ),
        r2IntPath T (fun t => r2QuadFluct μ h (P N) (X N) t ζ),
        fun i => r2ContPath T (r2EmpFluct μ (aa i) (X N) ζ))) atTop
      (fun ζ' => (r2L2Path T (fun t => F t ζ'), r2IntPath T (fun t => F t ζ'),
        fun i => ξ (aa i) ζ')) P P' := by
  let g : R2L2 T × (Fin k → C(Set.Icc (0 : ℝ) T, ℝ)) →
      R2L2 T × C(Set.Icc (0 : ℝ) T, ℝ) × (Fin k → C(Set.Icc (0 : ℝ) T, ℝ)) :=
    fun x => (x.1, s94_J hT.le x.1, x.2)
  have hg : Continuous g :=
    continuous_fst.prodMk (((s94_J hT.le).continuous.comp continuous_fst).prodMk continuous_snd)
  have hic := hi.continuous_comp hg
  have hZeq : ∀ ζ', (g ∘ fun ζ' => (r2L2Path T (fun t => F t ζ'), fun i => ξ (aa i) ζ')) ζ' =
      (r2L2Path T (fun t => F t ζ'), r2IntPath T (fun t => F t ζ'), fun i => ξ (aa i) ζ') := by
    intro ζ'
    show (_, s94_J hT.le _, _) = _
    rw [← s94_r2IntPath_eq hT.le (hF2 ζ')]
  have hYeq : ∀ N, 2 ≤ N → (g ∘ fun ζ => (r2L2Path T (fun t => r2QuadFluct μ h (P N) (X N) t ζ),
      fun i => r2ContPath T (r2EmpFluct μ (aa i) (X N) ζ))) =ᵐ[P N]
      fun ζ => (r2L2Path T (fun t => r2QuadFluct μ h (P N) (X N) t ζ),
        r2IntPath T (fun t => r2QuadFluct μ h (P N) (X N) t ζ),
        fun i => r2ContPath T (r2EmpFluct μ (aa i) (X N) ζ)) := by
    intro N hN
    filter_upwards [hae N hN] with ζ hζ
    show (_, s94_J hT.le _, _) = _
    rw [← s94_r2IntPath_eq hT.le hζ]
  refine ⟨fun N => (hL2 N).aemeasurable.prodMk ((hint N).aemeasurable.prodMk (hc N)),
    hic.aemeasurable_limit.congr (ae_of_all _ hZeq), ?_⟩
  have h1 := hic.tendsto
  have e : ∀ᶠ N in atTop, (⟨(P N).map (g ∘ fun ζ => (r2L2Path T (fun t => r2QuadFluct μ h (P N) (X N) t ζ),
      fun i => r2ContPath T (r2EmpFluct μ (aa i) (X N) ζ))), inferInstance⟩ :
        ProbabilityMeasure (R2L2 T × C(Set.Icc (0 : ℝ) T, ℝ) × (Fin k → C(Set.Icc (0 : ℝ) T, ℝ)))) =
      ⟨(P N).map (fun ζ => (r2L2Path T (fun t => r2QuadFluct μ h (P N) (X N) t ζ),
        r2IntPath T (fun t => r2QuadFluct μ h (P N) (X N) t ζ),
        fun i => r2ContPath T (r2EmpFluct μ (aa i) (X N) ζ))), inferInstance⟩ := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    exact Subtype.ext (Measure.map_congr (hYeq N hN))
  have e2 : (⟨P'.map (g ∘ fun ζ' => (r2L2Path T (fun t => F t ζ'), fun i => ξ (aa i) ζ')), inferInstance⟩ :
        ProbabilityMeasure (R2L2 T × C(Set.Icc (0 : ℝ) T, ℝ) × (Fin k → C(Set.Icc (0 : ℝ) T, ℝ)))) =
      ⟨P'.map (fun ζ' => (r2L2Path T (fun t => F t ζ'), r2IntPath T (fun t => F t ζ'),
        fun i => ξ (aa i) ζ')), inferInstance⟩ :=
    Subtype.ext (Measure.map_congr (ae_of_all _ hZeq))
  rw [e2] at h1
  exact h1.congr' e

end PartIIPoly

end HRS.MS.R2Chaos
