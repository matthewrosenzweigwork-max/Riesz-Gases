import HRS.MS.R2ChaosAux33

/-!
# HRS.MS.R2ChaosAux34 -- assembly of (i): convergence in law in `R2L2 T × C([0,T])^k`

Packet S94, namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.

`s94_part_i`: given the time-dependent finite-rank approximants of R1 and a jointly measurable `F` with `F(·,ζ') ∈ L²(dt)`
that is the `L²(dt ⊗ P')` limit of the finite-rank Gaussian integrands `s94Flim`, conclusion (i) of
`IntegratedChaosConclusion` holds (finite-rank convergence `s94_flat_tid` + the S9.2 tail `s94_R3` +
convergence together `s94_tid_of_approx`).
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

section PartI

variable {s T b p K M L : ℝ} {ρ : Euc d → ℝ} {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)]
  {P : ∀ N, Measure (Ω N)} [∀ N, IsProbabilityMeasure (P N)] {X : ∀ N, ℝ≥0 → Ω N → EucConfig d N}
  {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {ξ : (Euc d → ℝ) → Ω' → C(Set.Icc (0 : ℝ) T, ℝ)}

theorem s94_part_i (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hb : 0 < b) (hp : 1 < p)
    (hρ : IsRound2Density d s M L ρ)
    (hset : IsRound2PathSetting d s T b p K (Whole.withDensityReal ρ) P X P' ξ) (hT : 0 < T) {B C₁ : ℝ}
    {h : ℝ → Euc d → Euc d → ℝ} (hmeas : Measurable fun q : ℝ × Euc d × Euc d => h q.1 q.2.1 q.2.2)
    (hker : ∀ t ∈ Set.Icc (0 : ℝ) T, IsBoundedPairKernel s B (h t))
    {n : ℕ → ℕ} {u : ∀ m, Fin (n m) → Euc d → ℝ} {Cm : ∀ m, ℝ → Fin (n m) → Fin (n m) → ℝ}
    (hu : ∀ m a, IsR2Test (u m a)) (hCm : ∀ m a b, Measurable fun t => Cm m t a b)
    (hCb : ∀ m, ∃ K0 : ℝ, 0 ≤ K0 ∧ ∀ t a b, |Cm m t a b| ≤ K0) (hCs : ∀ m t a b, Cm m t a b = Cm m t b a)
    (hA : ∀ t ∈ Set.Icc (0 : ℝ) T, IsRound2Approx s C₁ B (Whole.withDensityReal ρ) (h t)
      (fun m => r2FiniteRankKernel (Cm m t) (u m)))
    {F : ℝ → Ω' → ℝ} (hFm : Measurable fun q : ℝ × Ω' => F q.1 q.2)
    (hF2 : ∀ ζ, MemLp (fun t => F t ζ) 2 (volume.restrict (Set.Icc (0 : ℝ) T)))
    {ηF : ℕ → ℝ} (hηF0 : ∀ m, 0 ≤ ηF m) (hηF : Tendsto ηF atTop (𝓝 0))
    (hFη : ∀ m, ∫⁻ ζ', ∫⁻ t in Set.Icc (0 : ℝ) T, ‖s94Flim ξ P' (Cm m) (u m) t ζ' - F t ζ'‖ₑ ^ 2 ∂volume ∂P'
      ≤ ENNReal.ofReal (ηF m))
    {k : ℕ} {aa : Fin k → Euc d → ℝ} (haa : ∀ i, IsR2Test (aa i)) :
    TendstoInDistribution
      (fun N ζ => (r2L2Path T (fun t => r2QuadFluct (Whole.withDensityReal ρ) h (P N) (X N) t ζ),
        fun i => r2ContPath T (r2EmpFluct (Whole.withDensityReal ρ) (aa i) (X N) ζ))) atTop
      (fun ζ' => (r2L2Path T (fun t => F t ζ'), fun i => ξ (aa i) ζ')) P P' := by
  haveI : IsProbabilityMeasure (Whole.withDensityReal ρ) := HRS.Whole.U1.u1_isProb hρ.prob
  choose K0 hK0 hbd using hCb
  have hmeasm : ∀ m, Measurable fun q : ℝ × Euc d × Euc d =>
      (fun m t => r2FiniteRankKernel (Cm m t) (u m)) m q.1 q.2.1 q.2.2 := fun m =>
    s94_measurable_FRfamily (hCm m) (hu m)
  obtain ⟨ηY, hηY0, hηY, hY⟩ := s94_R3 hd hs0 hs hb hp hρ hset (hm := fun m t => r2FiniteRankKernel (Cm m t) (u m))
    hmeas hmeasm hker hA
  have hcaa := hset.conv k aa haa
  have hYm : ∀ N, Measurable fun ζ => r2L2Path T (fun t => r2QuadFluct (Whole.withDensityReal ρ) h (P N) (X N) t ζ) :=
    fun N => s94_measurable_r2L2Path T _ (s94_quad_measurable (N := N) hmeas (X N) (hset.measX N))
  have hYjm : ∀ j N, Measurable fun ζ => r2L2Path T (fun t => r2QuadFluct (Whole.withDensityReal ρ)
      (fun t => r2FiniteRankKernel (Cm j t) (u j)) (P N) (X N) t ζ) := fun j N =>
    s94_measurable_r2L2Path T _ (s94_quad_measurable (N := N) (hmeasm j) (X N) (hset.measX N))
  have hZm : Measurable fun ζ => r2L2Path T (fun t => F t ζ) :=
    s94_measurable_r2L2Path T (fun q : ℝ × Ω' => F q.1 q.2) hFm
  have hZjm : ∀ j, Measurable fun ζ => r2L2Path T (fun t => s94Flim ξ P' (Cm j) (u j) t ζ) := fun j =>
    s94_measurable_r2L2Path T (fun q : ℝ × Ω' => s94Flim ξ P' (Cm j) (u j) q.1 q.2)
      (s94Flim_measurable hset.measξ P' (hCm j) (u j))
  have hξm : AEMeasurable (fun ζ i => ξ (aa i) ζ) P' := (measurable_pi_iff.2 fun i => hset.measξ _).aemeasurable
  refine s94_tid_of_approx (E := R2L2 T × (Fin k → C(Set.Icc (0 : ℝ) T, ℝ)))
    (fun N ζ => (r2L2Path T (fun t => r2QuadFluct (Whole.withDensityReal ρ) h (P N) (X N) t ζ),
      fun i => r2ContPath T (r2EmpFluct (Whole.withDensityReal ρ) (aa i) (X N) ζ)))
    (fun ζ => (r2L2Path T (fun t => F t ζ), fun i => ξ (aa i) ζ))
    (fun j N ζ => (r2L2Path T (fun t => r2QuadFluct (Whole.withDensityReal ρ)
      (fun t => r2FiniteRankKernel (Cm j t) (u j)) (P N) (X N) t ζ),
      fun i => r2ContPath T (r2EmpFluct (Whole.withDensityReal ρ) (aa i) (X N) ζ)))
    (fun j ζ => (r2L2Path T (fun t => s94Flim ξ P' (Cm j) (u j) t ζ), fun i => ξ (aa i) ζ))
    (fun N => (hYm N).aemeasurable.prodMk (hcaa.forall_aemeasurable N))
    (hZm.aemeasurable.prodMk hξm)
    (fun j N => (hYjm j N).aemeasurable.prodMk (hcaa.forall_aemeasurable N))
    (fun j => (hZjm j).aemeasurable.prodMk hξm)
    (fun j => s94_flat_tid hd hs0 hs hb hp hρ hset hT.le (hu j) (hCm j) (hK0 j) (hbd j) (hCs j) haa)
    (fun j => ηF j + ηY j) (fun j => add_nonneg (hηF0 j) (hηY0 j)) (by simpa using hηF.add hηY)
    (fun j => ?_) (fun j => ?_)
  · refine le_trans (le_of_eq ?_) ((hFη j).trans (ENNReal.ofReal_le_ofReal (by linarith [hηY0 j])))
    refine lintegral_congr fun ζ' => ?_
    exact s94_pair_enorm_sq (s94_Flim_memLp hd hs0 hs hb hp hρ hset hT.le (hu j) (hCm j) (hK0 j) (hbd j) ζ')
      (hF2 ζ') (fun i => ξ (aa i) ζ')
  · filter_upwards [eventually_ge_atTop 2] with N hN
    have a1 := s94_quad_ae_memLp hd hs0 hs hb hp hρ hset (B' := C₁ * B)
      (kf := fun t => r2FiniteRankKernel (Cm j t) (u j)) (hmeasm j)
      (fun t ht => s94_approx_bounded (hA t ht) j) hN
    have a2 := s94_quad_ae_memLp hd hs0 hs hb hp hρ hset (B' := B) (kf := h) hmeas hker hN
    refine le_trans (le_of_eq ?_) ((hY j N hN).trans (ENNReal.ofReal_le_ofReal (by linarith [hηF0 j])))
    refine lintegral_congr_ae ?_
    filter_upwards [a1, a2] with ζ h1 h2
    exact s94_pair_enorm_sq h1 h2 (fun i => r2ContPath T (r2EmpFluct (Whole.withDensityReal ρ) (aa i) (X N) ζ))

end PartI

end HRS.MS.R2Chaos
