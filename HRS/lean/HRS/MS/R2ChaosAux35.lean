import HRS.MS.R2ChaosAux34

/-!
# HRS.MS.R2ChaosAux35 -- conclusion (ii): the integrated process (continuous image of (i))

Packet S94, namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.

`s94_part_ii`: from (i) by the continuous map `(w, v) ↦ (w, J w, v)` (`J : L²(dt) → C([0,T])` the integration operator,
`‖J‖ ≤ √T`), `r2IntPath T f = J (r2L2Path T f)` for `f ∈ L²(dt)` (a.s. in `ζ`, for every `N`, by hypothesis `hae`).
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

section PartII

variable {s T b p K M L : ℝ} {ρ : Euc d → ℝ} {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)]
  {P : ∀ N, Measure (Ω N)} [∀ N, IsProbabilityMeasure (P N)] {X : ∀ N, ℝ≥0 → Ω N → EucConfig d N}
  {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {ξ : (Euc d → ℝ) → Ω' → C(Set.Icc (0 : ℝ) T, ℝ)}

theorem s94_part_ii (hT : 0 < T) {h : ℝ → Euc d → Euc d → ℝ} {F : ℝ → Ω' → ℝ} {μ : Measure (Euc d)}
    (hF2 : ∀ ζ, MemLp (fun t => F t ζ) 2 (volume.restrict (Set.Icc (0 : ℝ) T)))
    (hae : ∀ N, ∀ᵐ ζ ∂(P N), MemLp (fun t => r2QuadFluct μ h (P N) (X N) t ζ) 2
      (volume.restrict (Set.Icc (0 : ℝ) T)))
    {k : ℕ} {aa : Fin k → Euc d → ℝ}
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
  refine (hi.continuous_comp hg).congr (fun N => ?_) (ae_of_all _ fun ζ' => ?_)
  · filter_upwards [hae N] with ζ hζ
    show (_, s94_J hT.le _, _) = _
    rw [← s94_r2IntPath_eq hT.le hζ]
  · show (_, s94_J hT.le _, _) = _
    rw [← s94_r2IntPath_eq hT.le (hF2 ζ')]

end PartII

end HRS.MS.R2Chaos
