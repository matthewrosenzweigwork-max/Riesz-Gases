import HRS.Sections.AdjKEAux7
import HRS.Main.GFB2Aux6
import HRS.Sections.DynCmpAux5

/-!
# ADJKE part 8: the mild identity for a fixed time and mode

For `t ∈ [0,T]` and a mode `k`, almost surely
`η_N^t(e_k) = (V^{t,0}η_N^0)(e_k) + Z_t(e_k) + evolvingForcingCoord k t`
(`dyncmp_ae_identity`, `adjke_pair_identification`, `dyncmp_fluc_eq`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.AdjK

open HRS HRS.Uniform HRS.GF HRS.Uniform.Q54c

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

theorem adjke_eval_etaE {m : ℝ} (hm : (d : ℝ) < 2 * m) {N : ℕ} (hN : 0 < N) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] (X : Config d N) (ψ : Torus d → ℝ) (hc : Continuous ψ)
    (hs : Summable fun k : Lattice d => ‖Torus.fcoef ψ k‖) :
    NegSobolev.eval (etaE m X μ) ψ = linCoord μ ψ X := by
  haveI : IsProbabilityMeasure (empirical X) := empirical_isProbabilityMeasure hN _
  unfold etaE flucE
  rw [gfb2_eval_flucPair hm _ _ _ ψ hc hs, pair_empirical hN]
  unfold linCoord
  rw [one_div]

theorem adjke_identity_fixed (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ)
    {m : ℝ} (hm : (d : ℝ) / 2 + 2 < m) (T : ℝ) (hT : 0 < T) {N : ℕ} (hN : 2 ≤ N)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hX : IsParticleSystem P htr.dyn T X₀ W X) {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} (hF : IsFilteredSolution P ℱ W' W X)
    (M : ℝ → Ω → NegSobolev d m)
    (hMid : ∀ φ : Torus d → ℝ, Torus.IsSmooth φ → ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
      NegSobolev.eval (M t ω) φ =
        Real.sqrt N * empiricalMartingale P ℱ W' htr.dyn T (fun _ => φ) X t ω)
    (Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m) (hV : IsDualEvolution htr.dyn ρ m Vev)
    (Z : ℝ → Ω → NegSobolev d m) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T)
    (hZ : IsStochConv P Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) M 0 t (Z t))
    (hZm : AEMeasurable (Z t) P) (k : NonzeroLattice d) :
    ∀ᵐ ω ∂P,
      NegSobolev.fourierCoeff (etaE m (X t.toNNReal ω) (withDensityReal (ρ t))) k =
        NegSobolev.fourierCoeff (Vev t 0 (etaE m (X 0 ω) (withDensityReal (ρ 0)))) k +
          NegSobolev.fourierCoeff (Z t ω) k + evolvingForcingCoord htr.dyn ρ X k t ω := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hN0 : 0 < N := by omega
  haveI : NeZero N := ⟨by omega⟩
  have hm2 : (d : ℝ) < 2 * m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  set φ : Torus d → ℝ := Torus.realMode k with hφdef
  have hφ : Torus.IsSmooth φ := HRS.FieldSingAux.isSmooth_realMode k
  obtain ⟨hφ2, hφm⟩ := gf_smooth_mem_proof hφ m
  -- trajectory data
  obtain ⟨Λ₂, hreg, hjc, hpack⟩ := dyncmp_adjoint_package hd htr T
  obtain ⟨Cφ, hCφ⟩ := hpack φ hφ
  have hfC : IsClassicalAdjointSolution htr.dyn ρ t φ (fun r => propagator htr.dyn ρ r t φ) :=
    (hCφ t ht).1
  have hρ := Q40b.q40b_meanField hd1 htr hT
  have hV2 : Torus.IsCk 2 htr.dyn.V := mova_isCk_two_of_smooth htr.V_smooth
  have hid := dyncmp_ae_identity hd1 (rfl : htr.dyn.M = -1) hV2 hρ hreg hN hX.sol hF ht hφ2 hfC
    (fun r _ => rfl)
  -- density bound
  obtain ⟨Λ, hΛ⟩ := (isCompact_Icc.prod isCompact_univ).exists_bound_of_continuousOn hjc
  have hB : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ x, ρ r x ≤ Λ := fun r hr x =>
    (le_abs_self _).trans (by simpa using hΛ (r, x) ⟨⟨hr.1, hr.2.trans ht.2⟩, Set.mem_univ _⟩)
  -- regularity of `U^{0,t}φ` and `U^{r,t}φ`
  set j : ℕ := ⌈m⌉₊ + d + 2 with hjdef
  have hj : (d : ℝ) + 2 ≤ j := by
    rw [hjdef]; push_cast
    have : (0 : ℝ) ≤ ⌈m⌉₊ := Nat.cast_nonneg _
    linarith
  have hmj : m ≤ (j : ℝ) + 5 := by
    rw [hjdef]; push_cast
    have := Nat.le_ceil m
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨hψ0c, hψ0m'⟩ := adjke_prop_dom hd htr j hj hφ (le_refl (0 : ℝ)) ht.1
  have hψ0m : MemSobolev m (propagator htr.dyn ρ 0 t φ) :=
    HRS.PDE.MFAdjoint.memSobolev_mono_idx hψ0m' hmj
  have hψ0s := gfb2_summable_of_memSobolev hm2 hψ0m
  have hφc : Continuous φ := Q54c.isCk_continuous hφ2
  have hφs := gfb2_summable_of_memSobolev hm2 hφm
  -- the three terms
  have hpairId := adjke_pair_identification hd htr hm T hT hN P hF M hMid Vev hV ht (Z t) hZ k
    (by
      have hc : Continuous fun F : NegSobolev d m => NegSobolev.eval F (Torus.realMode k) := by
        have : (fun F : NegSobolev d m => NegSobolev.eval F (Torus.realMode k)) =
            fun F => Lattice.jp k.1 ^ m * NegSobolev.coord F k := by
          funext F; rw [adjke_eval_realMode]; rfl
        rw [this]
        exact continuous_const.mul (adjk_continuous_coord m k)
      exact hc.measurable.comp_aemeasurable hZm)
  filter_upwards [hid, hpairId] with ω h1 h2
  haveI : IsProbabilityMeasure (withDensityReal (ρ t)) :=
    isProb_withDensityReal (hρ.density t ⟨ht.1, ht.2⟩)
  haveI : IsProbabilityMeasure (withDensityReal (ρ 0)) :=
    isProb_withDensityReal (hρ.density 0 ⟨le_rfl, ht.1.trans ht.2⟩)
  rw [← adjke_eval_realMode, ← adjke_eval_realMode, ← adjke_eval_realMode]
  show NegSobolev.eval (etaE m (X t.toNNReal ω) (withDensityReal (ρ t))) φ = _
  rw [adjke_eval_etaE hm2 hN0 _ _ φ hφc hφs, hV 0 t le_rfl ht.1 _ φ hφ,
    adjke_eval_etaE hm2 hN0 _ _ _ hψ0c hψ0s, h2, h1]
  -- the forcing term
  have hforce : Real.sqrt N * ∫ r in (0 : ℝ)..t, flucInteraction htr.dyn
        (propagator htr.dyn ρ r t φ) (X r.toNNReal ω) (ρ r) =
      evolvingForcingCoord htr.dyn ρ X k t ω := by
    unfold evolvingForcingCoord
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [Set.uIcc_of_le ht.1] at hr
    have hfr : Torus.IsCk 2 (propagator htr.dyn ρ r t φ) := hfC.c2 r hr
    have := dyncmp_fluc_eq hd1 (rfl : htr.dyn.M = -1) hfr (hB r hr) hN0 (X r.toNNReal ω)
    simp only [this]
    ring
  rw [hforce]

end HRS.AdjK
