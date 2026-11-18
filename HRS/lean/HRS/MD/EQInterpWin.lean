import HRS.MD.EQInterpHolder
import HRS.MD.Stat
import HRS.MD.EQLawZeta
import HRS.MD.EQGaussWindow

/-!
# EQ-INTERP packet, part 7: the windows `ζ_N^{u+·}` and `Z^{·}` in `𝒳_{m,T}` against `𝒳_{m₁,T}`

For a stationary Gibbs flow (`d ≥ 2`, `N ≥ 2`):
* `windowZeta_cont_ae`: a.s. `τ ↦ ζ_N^{u+τ}` is continuous in `E_m` (`m > d/2`; the centre is the constant Gibbs marginal);
* `windowZeta_aemeasurable`, `windowZeta_embed_ae`: `windowZeta` is a.e. measurable and `windowZeta m₁ = epath ∘ windowZeta m` a.e.
  (`zetaE_embed`: the coordinates of `ζ_N` do not depend on `m`);
* the same for the window of a stationary Gaussian field (`windowPath_embed_ae`) and the law identities
  `law (windowZeta m₁) = (law (windowZeta m)).map epath`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MD.EQInterp

variable {d : ℕ} {N : ℕ}

theorem coord_eq_jp_fourierCoeff {m : ℝ} (F : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.coord F k = Lattice.jp k.1 ^ (-m) * NegSobolev.fourierCoeff F k := by
  have hj := Torus.jp_pos k.1
  simp only [NegSobolev.fourierCoeff]
  rw [← mul_assoc, ← Real.rpow_add hj]; simp

theorem fourierCoeff_zetaE {m : ℝ} (hm : (d : ℝ) < 2 * m) (hN : 1 ≤ N) (μ : Measure (Config d N))
    [IsProbabilityMeasure μ] (x : Config d N) (k : NonzeroLattice d) :
    NegSobolev.fourierCoeff (zetaE m μ x) k =
      Real.sqrt N * (Torus.measureRealCoeff (empirical x) k -
        Torus.measureRealCoeff (meanEmpirical μ) k) := by
  haveI := empirical_isProbabilityMeasure (by omega : 0 < N) x
  haveI := isProbabilityMeasure_meanEmpirical μ hN
  have h := NegSobolev.fourierCoeff_ofMeasureDiff hm (empirical x) (meanEmpirical μ) k
  have hs : ∀ (c : ℝ) (F : NegSobolev d m), NegSobolev.fourierCoeff (c • F) k =
      c * NegSobolev.fourierCoeff F k := by
    intro c F
    simp only [NegSobolev.fourierCoeff]
    have : NegSobolev.coord (c • F) k = c * NegSobolev.coord F k := rfl
    rw [this]; ring
  unfold zetaE
  rw [hs, h]

theorem zetaE_embed {m m₁ : ℝ} (hm : (d : ℝ) < 2 * m) (hmm : m ≤ m₁) (hN : 1 ≤ N)
    (μ : Measure (Config d N)) [IsProbabilityMeasure μ] (x : Config d N) :
    NegSobolev.embed m₁ (zetaE m μ x) = zetaE m₁ μ x := by
  refine EQGaussLift.eqgl_ext fun k => ?_
  rw [EQGaussLift.eqgl_coord_embed hmm, coord_eq_jp_fourierCoeff (zetaE m₁ μ x) k,
    fourierCoeff_zetaE hm hN, fourierCoeff_zetaE (by linarith) hN]

/-- Stationarity, measurability and a.s. continuity of a stationary Gibbs flow. -/
theorem flow_facts (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ)
    (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) (hN : 2 ≤ N) {H : ℝ}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hX : HRS.LZ.IsStationaryGibbsFlow P s hs0 hsd V β hβ H X₀ W X) :
    (∀ t : ℝ≥0, (t : ℝ) ≤ H → P.map (X t) = canonicalGibbs (periodicRiesz d s) V N β) ∧
    (∀ t, Measurable (X t)) ∧ (∀ᵐ ω ∂P, ∀ i, Continuous fun t : ℝ≥0 => X t ω i) := by
  have hS : IsStrongSolution P (PDE.mfData d s hs0 hsd V β hβ) H X₀ W X ∧
      PathwiseUnique P (PDE.mfData d s hs0 hsd V β hβ) H X₀ W := by
    rcases hX.flow.flow with hh | ⟨hd1, -⟩
    · exact hh
    · omega
  exact ⟨HRS.MD.Stat.md_stat_gibbs_flow_stationary_proof hd hs0 hsd V hV β hβ H hN P X₀ W X hX,
    hS.1.adapted, hS.1.cont⟩

theorem windowZeta_cont_ae (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ)
    (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) (hN : 2 ≤ N) {u T : ℝ} (hu : 0 ≤ u) (hT : 0 ≤ T)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hX : HRS.LZ.IsStationaryGibbsFlow P s hs0 hsd V β hβ (u + T) X₀ W X) {m : ℝ}
    (hm : (d : ℝ) < 2 * m) :
    ∀ᵐ ω ∂P, Continuous fun τ : Set.Icc (0 : ℝ) T =>
      zetaE m (P.map (X (Real.toNNReal (u + τ)))) (X (Real.toNNReal (u + τ)) ω) := by
  obtain ⟨hstat, hmeas, hcont⟩ := flow_facts hd hs0 hsd V hV hβ hN P hX
  have hG : IsProbabilityMeasure (canonicalGibbs (periodicRiesz d s) V N β) := by
    rw [← hstat 0 (by simp; positivity)]
    exact (Measure.isProbabilityMeasure_map_iff (hmeas 0).aemeasurable).2 inferInstance
  filter_upwards [hcont] with ω hω
  have hfun : (fun τ : Set.Icc (0 : ℝ) T =>
      zetaE m (P.map (X (Real.toNNReal (u + τ)))) (X (Real.toNNReal (u + τ)) ω)) =
      fun τ : Set.Icc (0 : ℝ) T =>
        zetaE m (canonicalGibbs (periodicRiesz d s) V N β) (X (Real.toNNReal (u + τ)) ω) := by
    funext τ
    rw [hstat _ (by rw [Real.coe_toNNReal _ (by linarith [τ.2.1])]; linarith [τ.2.2])]
  rw [hfun]
  refine (EQLawPath.eqlaw_continuous_zetaE hm (by omega) _).comp ?_
  refine continuous_pi fun i => ?_
  exact (hω i).comp (continuous_real_toNNReal.comp (continuous_const.add continuous_subtype_val))


theorem windowZeta_at' {m T u : ℝ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → Config d N) (ω : Ω)
    (hc : Continuous fun τ : Set.Icc (0 : ℝ) T =>
      zetaE m (P.map (X (Real.toNNReal (u + τ)))) (X (Real.toNNReal (u + τ)) ω))
    (τ : Set.Icc (0 : ℝ) T) :
    (Main.windowZeta m T u P X ω).at' τ =
      zetaE m (P.map (X (Real.toNNReal (u + τ)))) (X (Real.toNNReal (u + τ)) ω) := by
  have h : Main.windowZeta m T u P X ω = (⟨_, hc⟩ : C(Set.Icc (0 : ℝ) T, NegSobolev d m)) := by
    unfold Main.windowZeta
    exact dif_pos hc
  rw [h]
  rfl

theorem windowZeta_aemeasurable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ)
    (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) (hN : 2 ≤ N) {u T : ℝ} (hu : 0 ≤ u) (hT : 0 ≤ T)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hX : HRS.LZ.IsStationaryGibbsFlow P s hs0 hsd V β hβ (u + T) X₀ W X) {m : ℝ}
    (hm : (d : ℝ) < 2 * m) : AEMeasurable (Main.windowZeta m T u P X) P := by
  obtain ⟨hstat, hmeas, -⟩ := flow_facts hd hs0 hsd V hV hβ hN P hX
  have hG : IsProbabilityMeasure (canonicalGibbs (periodicRiesz d s) V N β) := by
    rw [← hstat 0 (by simp; positivity)]
    exact (Measure.isProbabilityMeasure_map_iff (hmeas 0).aemeasurable).2 inferInstance
  have heq : Main.windowZeta m T u P X = fun ω => EQLawPath.eqlaw_pathOf d m T (fun τ =>
      zetaE m (P.map (X (Real.toNNReal (u + τ)))) (X (Real.toNNReal (u + τ)) ω)) := by
    funext ω; rfl
  rw [heq]
  refine EQLawPath.eqlaw_aemeasurable_pathOf P T _ (fun τ => ?_)
    (windowZeta_cont_ae hd hs0 hsd V hV hβ hN hu hT P hX hm)
  have : (fun ω => zetaE m (P.map (X (Real.toNNReal (u + τ)))) (X (Real.toNNReal (u + τ)) ω)) =
      fun ω => zetaE m (canonicalGibbs (periodicRiesz d s) V N β) (X (Real.toNNReal (u + τ)) ω) := by
    funext ω
    rw [hstat _ (by rw [Real.coe_toNNReal _ (by linarith [τ.2.1])]; linarith [τ.2.2])]
  rw [this]
  exact (EQLawPath.eqlaw_continuous_zetaE hm (by omega) _).measurable.comp (hmeas _)

theorem windowZeta_embed_ae (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ)
    (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) (hN : 2 ≤ N) {u T : ℝ} (hu : 0 ≤ u) (hT : 0 ≤ T)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hX : HRS.LZ.IsStationaryGibbsFlow P s hs0 hsd V β hβ (u + T) X₀ W X) {m m₁ : ℝ}
    (hm : (d : ℝ) < 2 * m) (hmm : m ≤ m₁) :
    ∀ᵐ ω ∂P, Main.windowZeta m₁ T u P X ω = epath hmm T (Main.windowZeta m T u P X ω) := by
  obtain ⟨hstat, hmeas, -⟩ := flow_facts hd hs0 hsd V hV hβ hN P hX
  filter_upwards [windowZeta_cont_ae hd hs0 hsd V hV hβ hN hu hT P hX hm,
    windowZeta_cont_ae hd hs0 hsd V hV hβ hN hu hT P hX (show (d : ℝ) < 2 * m₁ by linarith)]
    with ω h1 h2
  refine ContinuousMap.ext fun τ => ?_
  show (Main.windowZeta m₁ T u P X ω).at' τ = NegSobolev.embed m₁ ((Main.windowZeta m T u P X ω).at' τ)
  rw [windowZeta_at' P X ω h1, windowZeta_at' P X ω h2]
  haveI : IsProbabilityMeasure (P.map (X (Real.toNNReal (u + τ)))) :=
    (Measure.isProbabilityMeasure_map_iff (hmeas _).aemeasurable).2 inferInstance
  exact (zetaE_embed hm hmm (by omega) _ _).symm

theorem windowPath_at' {m T : ℝ} {Ω : Type*} (Z : ℝ → Ω → NegSobolev d m) (ω : Ω)
    (hc : ContinuousOn (fun t => Z t ω) (Set.Ici 0)) (τ : Set.Icc (0 : ℝ) T) :
    (Main.windowPath m T 0 Z ω).at' τ = Z (0 + τ) ω :=
  EQGaussWindow.eqgw_windowPath_at T 0 le_rfl Z ω hc τ

theorem windowPath_embed_ae {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    (V ρβ : Torus d → ℝ) {m m₁ : ℝ} (hmm : m ≤ m₁) (T : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (Z : ℝ → Ω → NegSobolev d m)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Ici 0)) :
    ∀ᵐ ω ∂P, Main.windowPath m₁ T 0 (fun t ω => NegSobolev.embed m₁ (Z t ω)) ω =
      epath hmm T (Main.windowPath m T 0 Z ω) := by
  filter_upwards [hcont] with ω hω
  have hlip := EQGaussLift.eqgl_embed_lip (d := d) hmm
  have hω1 : ContinuousOn (fun t => NegSobolev.embed m₁ (Z t ω)) (Set.Ici 0) :=
    hlip.continuous.comp_continuousOn hω
  refine ContinuousMap.ext fun τ => ?_
  show (Main.windowPath m₁ T 0 (fun t ω => NegSobolev.embed m₁ (Z t ω)) ω).at' τ =
    NegSobolev.embed m₁ ((Main.windowPath m T 0 Z ω).at' τ)
  rw [windowPath_at' _ ω hω1, windowPath_at' _ ω hω]

end HRS.MD.EQInterp
