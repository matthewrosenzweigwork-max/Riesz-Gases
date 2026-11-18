import HRS.Main.HeadlineEquilibrium
import HRS.MD.EQInterpWin
import HRS.MD.EQBurnClt

/-!
# Chunk E, row 2.10 (fixed-`β` closure), packet A: the mean-field-centered window is the exactly centered
window plus a constant path

For a stationary Gibbs flow (`d ≥ 2`, `N ≥ 2`, `d < 2m`) the first marginal at every time in `[0, u+T]` is the
first marginal `m_N` of the canonical Gibbs law, hence almost surely
`η_N^{u+·} = ζ_N^{u+·} + h_N` as paths, with the constant path `h_N = √N (m_N - μ_β)`
(`windowFluc_ae_eq`).  Also: the norm of `ζ_N^{u+·}` is bounded (`windowZeta_norm_le`) and the norm and the
algebra of constant paths (`norm_constPath`, `constPath_sub`, `constPath_smul`, `constPath_add`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.ME.Bias

variable {d : ℕ}

open HRS HRS.Main

/-- The constant path `t ↦ b` has the norm of `b` (for `T ≥ 0`, the interval `[0,T]` is nonempty). -/
theorem norm_constPath {m T : ℝ} (hT : 0 ≤ T) (b : NegSobolev d m) :
    ‖(constPath m T b : PathSpace d m T)‖ = ‖b‖ := by
  show ‖(ContinuousMap.const (Set.Icc (0 : ℝ) T) b :
    ContinuousMap (Set.Icc (0 : ℝ) T) (NegSobolev d m))‖ = ‖b‖
  apply le_antisymm
  · exact (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun τ => le_rfl
  · exact ContinuousMap.norm_coe_le_norm (ContinuousMap.const (Set.Icc (0 : ℝ) T) b)
      ⟨0, ⟨le_rfl, hT⟩⟩

theorem constPath_sub {m T : ℝ} (a b : NegSobolev d m) :
    (constPath m T (a - b) : PathSpace d m T) = constPath m T a - constPath m T b := by
  unfold constPath
  exact ContinuousMap.ext fun τ => rfl

theorem constPath_add {m T : ℝ} (a b : NegSobolev d m) :
    (constPath m T (a + b) : PathSpace d m T) = constPath m T a + constPath m T b := by
  unfold constPath
  exact ContinuousMap.ext fun τ => rfl

theorem constPath_smul {m T : ℝ} (r : ℝ) (b : NegSobolev d m) :
    (constPath m T (r • b) : PathSpace d m T) = r • constPath m T b := by
  unfold constPath
  exact ContinuousMap.ext fun τ => rfl

/-- `h_N = √N (m_N - μ_β)` with `m_N` the first marginal of the canonical Gibbs law. -/
def shiftE (d : ℕ) (s : ℝ) (V : Torus d → ℝ) (N : ℕ) (β m : ℝ) (ρβ : Torus d → ℝ) :
    NegSobolev d m :=
  Real.sqrt N • NegSobolev.ofMeasureDiff m
    (firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)) (withDensityReal ρβ)

/-- Almost surely `η_N^{u+·} = ζ_N^{u+·} + h_N` as elements of `𝒳_{m,T}`. -/
theorem windowFluc_ae_eq (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ)
    (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) {ρβ : Torus d → ℝ}
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρβ) {N : ℕ} (hN : 2 ≤ N) {u T : ℝ}
    (hu : 0 ≤ u) (hT : 0 ≤ T) {m : ℝ} (hm : (d : ℝ) < 2 * m)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hX : HRS.LZ.IsStationaryGibbsFlow P s hs0 hsd V β hβ (u + T) X₀ W X) :
    ∀ᵐ ω ∂P, windowFluc m T u (Real.sqrt N) X (fun _ => ρβ) ω =
      windowZeta m T u P X ω + constPath m T (shiftE d s V N β m ρβ) := by
  obtain ⟨hstat, -, -⟩ := HRS.MD.EQInterp.flow_facts hd hs0 hsd V hV hβ hN P hX
  obtain ⟨hGprob, hGexch⟩ := HRS.MD.EQBurnClt.eqclt_gibbs hd hs0 hsd V hV hβ ρβ hρ hN
  haveI := hGprob
  have hN1 : 1 ≤ N := by omega
  haveI : IsProbabilityMeasure (withDensityReal ρβ) := HRS.isProb_withDensityReal hρ.1
  have hcont := HRS.MD.EQInterp.windowZeta_cont_ae hd hs0 hsd V hV hβ hN hu hT P hX hm
  have htime : ∀ τ : Set.Icc (0 : ℝ) T,
      Real.toNNReal (u + (τ : ℝ)) = Real.toNNReal u + Real.toNNReal (τ : ℝ) :=
    fun τ => Real.toNNReal_add hu τ.2.1
  have hlaw : ∀ τ : Set.Icc (0 : ℝ) T,
      P.map (X (Real.toNNReal (u + (τ : ℝ)))) = canonicalGibbs (periodicRiesz d s) V N β := by
    intro τ
    refine hstat _ ?_
    rw [Real.coe_toNNReal _ (add_nonneg hu τ.2.1)]
    linarith [τ.2.2]
  have hpt : ∀ (ω : Ω) (τ : Set.Icc (0 : ℝ) T),
      Real.sqrt N • NegSobolev.ofMeasureDiff m
          (empirical (X (Real.toNNReal u + Real.toNNReal (τ : ℝ)) ω)) (withDensityReal ρβ) =
        zetaE m (P.map (X (Real.toNNReal (u + (τ : ℝ))))) (X (Real.toNNReal (u + (τ : ℝ))) ω) +
          shiftE d s V N β m ρβ := by
    intro ω τ
    rw [← htime τ, hlaw τ]
    haveI : IsProbabilityMeasure (empirical (X (Real.toNNReal (u + (τ : ℝ))) ω)) :=
      empirical_isProbabilityMeasure (by omega : 1 ≤ N) _
    haveI : IsProbabilityMeasure (firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)) := by
      rw [← meanEmpirical_eq_firstMarginal (canonicalGibbs (periodicRiesz d s) V N β) hGexch hN1]
      exact isProbabilityMeasure_meanEmpirical (canonicalGibbs (periodicRiesz d s) V N β) hN1
    unfold zetaE shiftE
    rw [meanEmpirical_eq_firstMarginal (canonicalGibbs (periodicRiesz d s) V N β) hGexch hN1,
      NegSobolev.ofMeasureDiff_add hm (empirical (X (Real.toNNReal (u + (τ : ℝ))) ω))
        (firstMarginal (canonicalGibbs (periodicRiesz d s) V N β)) (withDensityReal ρβ), smul_add]
  filter_upwards [hcont] with ω hω
  have hF : (fun τ : Set.Icc (0 : ℝ) T =>
      Real.sqrt N • NegSobolev.ofMeasureDiff m
        (empirical (X (Real.toNNReal u + Real.toNNReal (τ : ℝ)) ω)) (withDensityReal ρβ)) =
      fun τ : Set.Icc (0 : ℝ) T =>
        zetaE m (P.map (X (Real.toNNReal (u + (τ : ℝ))))) (X (Real.toNNReal (u + (τ : ℝ))) ω) +
          shiftE d s V N β m ρβ := by
    funext τ
    exact hpt ω τ
  have hcontF : Continuous fun τ : Set.Icc (0 : ℝ) T =>
      Real.sqrt N • NegSobolev.ofMeasureDiff m
        (empirical (X (Real.toNNReal u + Real.toNNReal (τ : ℝ)) ω)) (withDensityReal ρβ) := by
    rw [hF]
    exact hω.add continuous_const
  have e1 : windowFluc m T u (Real.sqrt N) X (fun _ => ρβ) ω =
      (⟨_, hcontF⟩ : PathSpace d m T) := by
    unfold windowFluc flucPath
    exact dif_pos hcontF
  have e2 : windowZeta m T u P X ω = (⟨_, hω⟩ : PathSpace d m T) := by
    unfold windowZeta
    exact dif_pos hω
  have key : (⟨_, hcontF⟩ : ContinuousMap (Set.Icc (0 : ℝ) T) (NegSobolev d m)) =
      (⟨_, hω⟩ : ContinuousMap (Set.Icc (0 : ℝ) T) (NegSobolev d m)) +
        ContinuousMap.const (Set.Icc (0 : ℝ) T) (shiftE d s V N β m ρβ) := by
    refine ContinuousMap.ext fun τ => ?_
    exact hpt ω τ
  rw [e1, e2]
  exact key

/-- `η_N^{u+·}` is a.e. measurable (it is a.e. `ζ_N^{u+·} + h_N`). -/
theorem windowFluc_aemeasurable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ)
    (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) {ρβ : Torus d → ℝ}
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρβ) {N : ℕ} (hN : 2 ≤ N) {u T : ℝ}
    (hu : 0 ≤ u) (hT : 0 ≤ T) {m : ℝ} (hm : (d : ℝ) < 2 * m)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hX : HRS.LZ.IsStationaryGibbsFlow P s hs0 hsd V β hβ (u + T) X₀ W X) :
    AEMeasurable (windowFluc m T u (Real.sqrt N) X (fun _ => ρβ)) P := by
  have hae := windowFluc_ae_eq hd hs0 hsd V hV hβ hρ hN hu hT hm P hX
  have hz := HRS.MD.EQInterp.windowZeta_aemeasurable hd hs0 hsd V hV hβ hN hu hT P hX hm
  have hc : Measurable fun w : PathSpace d m T =>
      w + constPath m T (shiftE d s V N β m ρβ) :=
    (continuous_id.add continuous_const).measurable
  exact (hc.comp_aemeasurable hz).congr (hae.mono fun ω h => h.symm)

/-- The path `ζ_N^{u+·}` has bounded norm (`‖ζ_N^{t}‖ ≤ √N · sqrt (8 ∑' k, jp(k)^{-2m})`, both
empirical and mean empirical measure being probability measures); hence `‖ζ_N^{u+·}‖` is integrable. -/
theorem windowZeta_integrable_norm (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) {N : ℕ} (hN : 2 ≤ N)
    {u T : ℝ} (hu : 0 ≤ u) (hT : 0 ≤ T) {m : ℝ} (hm : (d : ℝ) < 2 * m)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hX : HRS.LZ.IsStationaryGibbsFlow P s hs0 hsd V β hβ (u + T) X₀ W X) :
    Integrable (fun ω => ‖windowZeta m T u P X ω‖) P := by
  obtain ⟨-, hmeas, -⟩ := HRS.MD.EQInterp.flow_facts hd hs0 hsd V hV hβ hN P hX
  have hz := HRS.MD.EQInterp.windowZeta_aemeasurable hd hs0 hsd V hV hβ hN hu hT P hX hm
  have hK : 0 ≤ Real.sqrt N * Real.sqrt (8 * ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m))) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hbound : ∀ ω, ‖windowZeta m T u P X ω‖ ≤
      Real.sqrt N * Real.sqrt (8 * ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m))) := by
    intro ω
    by_cases hc : Continuous fun t : Set.Icc (0 : ℝ) T =>
        zetaE m (P.map (X (Real.toNNReal (u + (t : ℝ))))) (X (Real.toNNReal (u + (t : ℝ))) ω)
    · have e : windowZeta m T u P X ω = (⟨_, hc⟩ : PathSpace d m T) := by
        unfold windowZeta
        exact dif_pos hc
      rw [e]
      refine (ContinuousMap.norm_le _ hK).2 fun τ => ?_
      change ‖zetaE m (P.map (X (Real.toNNReal (u + (τ : ℝ))))) (X (Real.toNNReal (u + (τ : ℝ))) ω)‖ ≤ _
      haveI : IsProbabilityMeasure (P.map (X (Real.toNNReal (u + (τ : ℝ))))) :=
        (Measure.isProbabilityMeasure_map_iff
          (hmeas (Real.toNNReal (u + (τ : ℝ)))).aemeasurable).2 inferInstance
      haveI := empirical_isProbabilityMeasure (by omega : 1 ≤ N)
        (X (Real.toNNReal (u + (τ : ℝ))) ω)
      haveI := isProbabilityMeasure_meanEmpirical (P.map (X (Real.toNNReal (u + (τ : ℝ)))))
        (by omega : 1 ≤ N)
      unfold zetaE
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_mul_of_nonneg_left
        (norm_ofMeasureDiff_le hm (empirical (X (Real.toNNReal (u + (τ : ℝ))) ω))
          (meanEmpirical (P.map (X (Real.toNNReal (u + (τ : ℝ))))))) (Real.sqrt_nonneg _)
    · have e : windowZeta m T u P X ω = 0 := by
        unfold windowZeta
        exact dif_neg hc
      rw [e]
      simpa using hK
  have hmeasN : AEStronglyMeasurable (fun ω => ‖windowZeta m T u P X ω‖) P :=
    hz.norm.aestronglyMeasurable
  exact Integrable.of_bound hmeasN
    (Real.sqrt N * Real.sqrt (8 * ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m))))
    (Filter.Eventually.of_forall fun ω => by
      simp only [norm_norm]
      exact hbound ω)

end HRS.ME.Bias
