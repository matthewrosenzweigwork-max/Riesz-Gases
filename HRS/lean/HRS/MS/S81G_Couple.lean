import HRS.MS.MfeConfAux115

/-!
# S81G, packet G5: coupling of the frozen strong solution with the regularised flows on the ORIGINAL probability space

Hypotheses are exactly those of `GibbsEntropyContraction` (`IsVectorBrownian`, independent initial datum, `IsWholeStrongSolution`):
no filtered realization.  The bridge `exists_isBrownianFiltration_of_isVectorBrownian` supplies a Brownian filtration
`σ(X 0) ∨ σ(W') ∨ null sets` for which `X 0` is `ℱ 0`-measurable; `Y^M` (global strong solutions of the truncated-kernel SDE) are built
on it, and `s81g_ident` is `sb1_ident` with the `IsWholeFilteredSolution` hypothesis replaced by what it really uses.
`s81g_couple`: laws `law (Y^M_t) = sb1Flow ...`, eventual equality `Y^M = X` on `[0,T]` a.s., setwise convergence of the laws.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS HRS.MD.EQLawPath HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Impl HRS.MS.MfeConf
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S81G

variable {d N : ℕ}

/-- `sb1_ident` with the hypothesis `IsWholeFilteredSolution` replaced by `IsBrownianFiltration` and the coordinate identification -/
theorem s81g_ident (D : Whole.WholeDyn d) (hM : D.M = -1) {B : ℝ} (P : Sb1Pot D.V B) {S : ℝ} (hS : 0 < S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X₀ : Ω → Whole.EucConfig d N} {X : ℝ≥0 → Ω → Whole.EucConfig d N}
    (hX : Whole.IsWholeStrongSolution Pm D S X₀ W X) (hB : IsBrownianFiltration Pm ℱ W')
    (hcoords : ∀ᵐ ζ ∂Pm, ∀ t i j, W' t ζ (i, j) = W t ζ i j)
    {gM : ℕ → Euc d → ℝ} (hgM : ∀ M : ℕ, IsP4Kernel d D.s (1 / ((M : ℝ) + 1)) (gM M))
    {Ys : ℕ → ℝ → Ω → Whole.EucConfig d N}
    (hYs : ∀ M, IsAdditiveSDESolution Pm (p4r_shiftFil ℱ) W' (fun _ => sb1DriftM D (gM M) N)
      (p4r_sigma d N D.invβ) (X 0) (fun _ => ⊤) (Ys M)) :
    ∀ᵐ ζ ∂Pm, ∀ᶠ M : ℕ in atTop, ∀ t : ℝ≥0, (t : ℝ) ≤ S → Ys M (t : ℝ) ζ = X t ζ := by
  have hpaths : ∀ᵐ ζ ∂Pm, ∀ M, IsPathSolution (fun _ => sb1DriftM D (gM M) N) (p4r_sigma d N D.invβ)
      (fun t => W' t ζ) (X 0 ζ) ⊤ (fun t => Ys M t ζ) :=
    ae_all_iff.2 fun M => (hYs M).isPathSolution
  filter_upwards [hX.eqn, hX.cont, hX.no_collision, hcoords, hpaths] with ζ heqn hcont hnoc hcoord hpath
  have hcontX : Continuous fun t : ℝ≥0 => X t ζ := continuous_pi hcont
  have hsep := p4r_sep hS hcontX (fun t ht i j hij hEq => hnoc t ht ⟨i, j, hij, hEq⟩)
  filter_upwards [hsep] with M hMsep
  have hagree : ∀ r ∈ Set.Icc (0 : ℝ) S, (fun _ : ℝ => sb1DriftM D (gM M) N) r (X (Real.toNNReal r) ζ) =
      (fun _ : ℝ => Whole.particleDriftW D) r (X (Real.toNNReal r) ζ) := fun r hr => by
    show sb1DriftM D (gM M) N _ = Whole.particleDriftW D _
    rw [sb1_particleDrift_eq D hM N]
    exact sb1_driftM_eq D (hgM M) N _ (fun i j hij => hMsep i j hij (Real.toNNReal r)
      (by rw [Real.coe_toNNReal _ hr.1]; exact hr.2))
  have hyM := p4r_isPathSolution D.invβ S (fun _ => sb1DriftM D (gM M) N) (fun t => X t ζ) hcontX
    (fun t => W' t ζ) (fun t => W t ζ) (fun t i j => hcoord t i j) (funext fun k => by
      simpa using congrFun (hB.zero ζ) k)
    (p4r_eqn_congr (b := fun _ => Whole.particleDriftW D) (y := fun t => X t ζ) (w := fun t => W t ζ)
      hagree heqn)
  have hu := ode_additive_unique Set.univ isOpen_univ (fun _ => sb1DriftM D (gM M) N)
    (sb1_driftM_isLip D (hgM M) P N).toLoc (p4r_sigma d N D.invβ) (fun t => W' t ζ)
    (hB.cont ζ) (X 0 ζ) hyM (hpath M) (fun _ _ _ => trivial) (fun _ _ _ => trivial)
  have hEq : Set.EqOn (fun u : ℝ => Ys M u ζ) (fun u : ℝ => X (Real.toNNReal u) ζ) (Set.Ico 0 S) :=
    fun u hu0 => (hu u hu0.1 (by simpa using hu0.2)).symm
  have hc1 : ContinuousOn (fun u : ℝ => Ys M u ζ) (Set.Icc 0 S) :=
    (hYs M).cont ζ S hS.le (WithTop.coe_lt_top S)
  have hc2 : ContinuousOn (fun u : ℝ => X (Real.toNNReal u) ζ) (Set.Icc 0 S) :=
    (hcontX.comp continuous_real_toNNReal).continuousOn
  have hEq' := Set.EqOn.of_subset_closure hEq hc1 hc2 Set.Ico_subset_Icc_self
    (by rw [closure_Ico hS.ne])
  intro t ht
  have := hEq' ⟨NNReal.coe_nonneg t, ht⟩
  simpa using this

theorem s81g_couple (D : Whole.WholeDyn d) (hM : D.M = -1) (hs0 : 0 ≤ D.s) {B : ℝ} (P : Sb1Pot D.V B)
    {T : ℝ} (hT : 0 < T)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} (hW : IsVectorBrownian Pm W)
    {X₀ : Ω → Whole.EucConfig d N} {X : ℝ≥0 → Ω → Whole.EucConfig d N}
    (hX : Whole.IsWholeStrongSolution Pm D T X₀ W X)
    (hind : IndepFun X₀ (fun ζ t => W t ζ) Pm) :
    ∃ (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ)
      (hB : IsBrownianFiltration Pm (p4r_shiftFil ℱ) W') (Ys : ℕ → ℝ → Ω → Whole.EucConfig d N),
      (∀ (M : ℕ) (τ : ℝ), Measurable (Ys M τ)) ∧
      (∀ (M : ℕ) (t : ℝ), 0 ≤ t → Pm.map (Ys M t) =
        sb1Flow D (sb1kM d D.s M) N (Pm.map (X 0)) (Pm.map (bfPath hB)) t) ∧
      (∀ᵐ ζ ∂Pm, ∀ᶠ M : ℕ in atTop, ∀ t : ℝ≥0, (t : ℝ) ≤ T → Ys M (t : ℝ) ζ = X t ζ) ∧
      (∀ τ : ℝ, 0 ≤ τ → τ ≤ T → ∀ A : Set (Whole.EucConfig d N), MeasurableSet A →
        Tendsto (fun M : ℕ => Pm.map (Ys M τ) A) atTop (𝓝 (Pm.map (X (Real.toNNReal τ)) A))) := by
  have hind' : IndepFun (X 0) (fun ζ t => W t ζ) Pm :=
    hind.congr (hX.init.mono fun ζ h => h.symm) Filter.EventuallyEq.rfl
  obtain ⟨W', hW'm, hcoords, hBF, hX0⟩ :=
    exists_isBrownianFiltration_of_isVectorBrownian Pm W hW (X 0) (hX.adapted 0) hind'
  set ℱ := generatedFiltration Pm (X 0) (hX.adapted 0) W' hW'm with hℱ
  have hW' : IsBrownianFiltration Pm (p4r_shiftFil ℱ) W' := p4r_shiftFil_brownian hBF
  have hY0 : ∀ t : ℝ, Measurable[p4r_shiftFil ℱ t] (X 0) := fun t => hX0 (max t 0)
  have hex : ∀ M : ℕ, ∃ Ys : ℝ → Ω → Whole.EucConfig d N,
      IsAdditiveSDESolution Pm (p4r_shiftFil ℱ) W' (fun _ => sb1DriftM D (sb1kM d D.s M) N)
        (p4r_sigma d N D.invβ) (X 0) (fun _ => ⊤) Ys := fun M =>
    exists_sde_solution_global_exists hW' _ (sb1_driftM_isLip D (sb1kM_isKernel D.s hs0 M) P N) _ hY0
  choose Ys hYs using hex
  have hae := s81g_ident D hM P hT hX hBF hcoords (fun M => sb1kM_isKernel D.s hs0 M) hYs
  have hmeas : ∀ (M : ℕ) (τ : ℝ), Measurable (Ys M τ) := fun M τ =>
    ((hYs M).adapted τ).mono ((p4r_shiftFil ℱ).le _) le_rfl
  refine ⟨ℱ, W', hW', Ys, hmeas, fun M t ht => ?_, hae, ?_⟩
  · exact sb1_law_repr hW' (sb1_driftM_isLip D (sb1kM_isKernel D.s hs0 M) P N) (hY0 0) (hYs M) ht
  · intro τ hτ hτT A hA
    have hτS : ((Real.toNNReal τ : ℝ≥0) : ℝ) ≤ T := by rw [Real.coe_toNNReal _ hτ]; exact hτT
    have hmY : Measurable (X (Real.toNNReal τ)) := hX.adapted _
    simp only [Measure.map_apply (hmeas _ τ) hA, Measure.map_apply hmY hA]
    refine tendsto_measure_of_ae_tendsto_indicator_of_isFiniteMeasure atTop (hmY hA)
      (fun M => hmeas M τ hA) ?_
    filter_upwards [hae] with ζ h
    filter_upwards [h] with M hM'
    have := hM' _ hτS
    rw [Real.coe_toNNReal _ hτ] at this
    simp only [Set.mem_preimage, this]

end HRS.MS.S81G
