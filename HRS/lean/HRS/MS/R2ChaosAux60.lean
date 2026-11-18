import HRS.MS.R2ChaosAux59

/-!
# HRS.MS.R2ChaosAux60 -- S9.6 (P4): conclusion (i) for polynomial kernels by truncation

Packet S94 (S9.6), namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.

`s94_part_i_poly`: (i) for `h` follows from (i) for the bounded truncations `h^j` (`s94_tid_of_approx`), the `L²(dt⊗P')` convergence
`F^j → F` and the S9.5 tail `s94_R3poly`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.deprecated false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2Chaos

open HRS.Whole HRS.MS.R2Poly

variable {d : ℕ}

section PartIPoly

variable {s T b p K M L C₀ c₀ Pw : ℝ} {ρ : Euc d → ℝ} {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)]
  {P : ∀ N, Measure (Ω N)} [∀ N, IsProbabilityMeasure (P N)] {X : ∀ N, ℝ≥0 → Ω N → EucConfig d N}
  {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {ξ : (Euc d → ℝ) → Ω' → C(Set.Icc (0 : ℝ) T, ℝ)}

theorem s94_part_i_poly (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hb : 0 < b) (hp : 1 < p)
    (hρ : IsRound2Density d s M L ρ) (hG : HasR2GaussianUpper C₀ c₀ ρ) (hPw : 0 ≤ Pw)
    (hset : IsRound2PathSetting d s T b p K (Whole.withDensityReal ρ) P X P' ξ) (hT : 0 < T) {B : ℝ}
    {h : ℝ → Euc d → Euc d → ℝ} (hmeas : Measurable fun q : ℝ × Euc d × Euc d => h q.1 q.2.1 q.2.2)
    (hker : ∀ t ∈ Set.Icc (0 : ℝ) T, IsR2PolyPairKernel s Pw B (h t))
    {Fj : ℕ → ℝ → Ω' → ℝ} (hFjm : ∀ j, Measurable fun q : ℝ × Ω' => Fj j q.1 q.2)
    (hFj2 : ∀ j ζ, MemLp (fun t => Fj j t ζ) 2 (volume.restrict (Set.Icc (0 : ℝ) T)))
    (hFji : ∀ (j k : ℕ) (aa : Fin k → Euc d → ℝ), (∀ i, IsR2Test (aa i)) →
      TendstoInDistribution
        (fun N ζ => (r2L2Path T (fun t => r2QuadFluct (Whole.withDensityReal ρ) (fun t => s95_part (h t) j) (P N) (X N) t ζ),
          fun i => r2ContPath T (r2EmpFluct (Whole.withDensityReal ρ) (aa i) (X N) ζ))) atTop
        (fun ζ' => (r2L2Path T (fun t => Fj j t ζ'), fun i => ξ (aa i) ζ')) P P')
    {F : ℝ → Ω' → ℝ} (hFm : Measurable fun q : ℝ × Ω' => F q.1 q.2)
    (hF2 : ∀ ζ, MemLp (fun t => F t ζ) 2 (volume.restrict (Set.Icc (0 : ℝ) T)))
    {η : ℕ → ℝ} (hη0 : ∀ j, 0 ≤ η j) (hη : Tendsto η atTop (𝓝 0))
    (hFη : ∀ j, ∫⁻ ζ', ∫⁻ t in Set.Icc (0 : ℝ) T, ‖Fj j t ζ' - F t ζ'‖ₑ ^ 2 ∂volume ∂P' ≤ ENNReal.ofReal (η j))
    {k : ℕ} {aa : Fin k → Euc d → ℝ} (haa : ∀ i, IsR2Test (aa i)) :
    TendstoInDistribution
      (fun N ζ => (r2L2Path T (fun t => r2QuadFluct (Whole.withDensityReal ρ) h (P N) (X N) t ζ),
        fun i => r2ContPath T (r2EmpFluct (Whole.withDensityReal ρ) (aa i) (X N) ζ))) atTop
      (fun ζ' => (r2L2Path T (fun t => F t ζ'), fun i => ξ (aa i) ζ')) P P' := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ.prob
  have hB : 0 ≤ B := s94_polyB_nonneg hd (hker 0 ⟨le_rfl, hT.le⟩)
  have hhm : ∀ j, ∀ t ∈ Set.Icc (0 : ℝ) T, IsR2PolyPairKernel s Pw B (s95_part (h t) j) :=
    fun j t ht => s94_trunc_poly (hker t ht) j
  have hmeasm : ∀ j, Measurable fun q : ℝ × Euc d × Euc d => (fun j t => s95_part (h t) j) j q.1 q.2.1 q.2.2 :=
    fun j => s94_trunc_family_meas hmeas j
  have hconv : ∀ t ∈ Set.Icc (0 : ℝ) T, ∃ ε : ℝ, 0 < ε ∧ (2 + ε) * s < d ∧
      Tendsto (fun j => eLpNorm (fun q : Euc d × Euc d => (fun j t => s95_part (h t) j) j t q.1 q.2 - h t q.1 q.2)
        (ENNReal.ofReal (2 + ε)) ((Whole.withDensityReal ρ).prod (Whole.withDensityReal ρ))) atTop (𝓝 0) := by
    intro t ht
    obtain ⟨ε, hε, hεs⟩ := s94_exists_eps hd hs0 hs
    exact ⟨ε, hε, hεs, s94_trunc_lq hd hs0 hs hρ hG hPw (hker t ht) (q := 2 + ε) (by linarith)
      (by linarith)⟩
  obtain ⟨ηY, hηY0, hηY, hY⟩ := s94_R3poly hd hs0 hs hb hp hρ hG hPw hset hB (hm := fun j t => s95_part (h t) j)
    hmeas hmeasm hker hhm hconv
  have hcaa := hset.conv k aa haa
  have hYm : ∀ N, Measurable fun ζ => r2L2Path T (fun t => r2QuadFluct (Whole.withDensityReal ρ) h (P N) (X N) t ζ) :=
    fun N => s94_measurable_r2L2Path T _ (s94_quad_measurable (N := N) hmeas (X N) (hset.measX N))
  have hYjm : ∀ j N, Measurable fun ζ => r2L2Path T (fun t => r2QuadFluct (Whole.withDensityReal ρ)
      (fun t => s95_part (h t) j) (P N) (X N) t ζ) := fun j N =>
    s94_measurable_r2L2Path T _ (s94_quad_measurable (N := N) (hmeasm j) (X N) (hset.measX N))
  have hZm : Measurable fun ζ => r2L2Path T (fun t => F t ζ) :=
    s94_measurable_r2L2Path T (fun q : ℝ × Ω' => F q.1 q.2) hFm
  have hZjm : ∀ j, Measurable fun ζ => r2L2Path T (fun t => Fj j t ζ) := fun j =>
    s94_measurable_r2L2Path T (fun q : ℝ × Ω' => Fj j q.1 q.2) (hFjm j)
  have hξm : AEMeasurable (fun ζ i => ξ (aa i) ζ) P' := (measurable_pi_iff.2 fun i => hset.measξ _).aemeasurable
  refine s94_tid_of_approx (E := R2L2 T × (Fin k → C(Set.Icc (0 : ℝ) T, ℝ)))
    (fun N ζ => (r2L2Path T (fun t => r2QuadFluct (Whole.withDensityReal ρ) h (P N) (X N) t ζ),
      fun i => r2ContPath T (r2EmpFluct (Whole.withDensityReal ρ) (aa i) (X N) ζ)))
    (fun ζ => (r2L2Path T (fun t => F t ζ), fun i => ξ (aa i) ζ))
    (fun j N ζ => (r2L2Path T (fun t => r2QuadFluct (Whole.withDensityReal ρ)
      (fun t => s95_part (h t) j) (P N) (X N) t ζ),
      fun i => r2ContPath T (r2EmpFluct (Whole.withDensityReal ρ) (aa i) (X N) ζ)))
    (fun j ζ => (r2L2Path T (fun t => Fj j t ζ), fun i => ξ (aa i) ζ))
    (fun N => (hYm N).aemeasurable.prodMk (hcaa.forall_aemeasurable N))
    (hZm.aemeasurable.prodMk hξm)
    (fun j N => (hYjm j N).aemeasurable.prodMk (hcaa.forall_aemeasurable N))
    (fun j => (hZjm j).aemeasurable.prodMk hξm)
    (fun j => hFji j k aa haa)
    (fun j => η j + ηY j) (fun j => add_nonneg (hη0 j) (hηY0 j)) (by simpa using hη.add hηY)
    (fun j => ?_) (fun j => ?_)
  · refine le_trans (le_of_eq ?_) ((hFη j).trans (ENNReal.ofReal_le_ofReal (by linarith [hηY0 j])))
    refine lintegral_congr fun ζ' => ?_
    exact s94_pair_enorm_sq (hFj2 j ζ') (hF2 ζ') (fun i => ξ (aa i) ζ')
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have a1 := s94_quad_ae_memLp hd hs0 hs hb hp hρ hset (B' := B * 2 ^ Pw * (1 + (j : ℝ)) ^ Pw)
      (kf := fun t => s95_part (h t) j) (hmeasm j)
      (fun t ht => s94_trunc_bdd hd hPw (hker t ht) j) hN
    have a2 := s94_pquad_ae_memLp hd hs0 hs hb hp hρ hG hPw hset hB hmeas hker hN
    refine le_trans (le_of_eq ?_) ((hY j N hN).trans (ENNReal.ofReal_le_ofReal (by linarith [hη0 j])))
    refine lintegral_congr_ae ?_
    filter_upwards [a1, a2] with ζ h1 h2
    exact s94_pair_enorm_sq h1 h2 (fun i => r2ContPath T (r2EmpFluct (Whole.withDensityReal ρ) (aa i) (X N) ζ))

end PartIPoly

end HRS.MS.R2Chaos
