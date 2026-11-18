import HRS.MD.EQLawPath3
import HRS.MD.EQLawFlow
import HRS.MD.EQLawZeta
import HRS.MD.EQ29Vocab
import HRS.MD.Stat
import HRS.Stochastic.Particle

/-!
# EQ-LAW (packet `eq_path_stationary`), part 4: one flow against the canonical solution

For a stationary Gibbs flow `(X, W)` on the horizon `H` and a time `u ≤ H`:

* `eqlaw_flow_canon`: the map `J ω = (X_u ω, path of W_{u+·} - W_u)` into the canonical space has the image measure
  `ℙ_{N,β} ⊗ law(path)` (`P.map (X u) = ℙ_{N,β}` by STAT, independence by `eqlawJ_map`), the shifted Brownian
  filtration being a Brownian filtration.
* `eqlaw_flow_compare`: if `Xσ` is a strong solution on the canonical space then `X_{u+s} = Xσ_s ∘ J` a.s. for `s ≤ T`
  (pathwise uniqueness on `(Ω, P)`).
* `eqlaw_window_eq`: hence the window `windowZeta` equals the functional `Γ ∘ J` a.s.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MD.EQLawPath

open HRS.LZ

variable {d N : ℕ}

theorem eqlaw_flow_canon (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ)
    (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) (hN : 2 ≤ N) {H : ℝ}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hX : IsStationaryGibbsFlow P s hs0 hsd V β hβ H X₀ W X) (u : ℝ≥0) (hu : (u : ℝ) ≤ H) :
    ∃ (ℱ1 : Filtration ℝ mΩ) (W1 : ℝ≥0 → Ω → Fin N × Fin d → ℝ) (hBF : IsBrownianFiltration P ℱ1 W1),
      Measurable (fun ω => ((X u ω, bfPath hBF ω) : Sig d N)) ∧
      P.map (fun ω => ((X u ω, bfPath hBF ω) : Sig d N)) =
        (canonicalGibbs (periodicRiesz d s) V N β).prod (P.map (bfPath hBF)) ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (fun i => W (u + t) ω i - W u ω i) = ofCoords W1 t ω := by
  classical
  obtain ⟨ℱ, W', hF⟩ := hX.filtered
  have hBF := hF.brownian
  have hXm : Measurable[ℱ (u : ℝ)] (X u) := hF.adapted u
  have hstat := Stat.md_stat_gibbs_flow_stationary_proof hd hs0 hsd V hV β hβ H hN P X₀ W X hX u hu
  refine ⟨shiftFil ℱ u, shiftProc W' u, isBrownianFiltration_shift hBF u, ?_, ?_, ?_⟩
  · exact measurable_eqlawJ hBF u (hXm.mono (ℱ.le _) le_rfl)
  · have := eqlawJ_map hBF u hXm
    rw [hstat] at this
    exact this
  · filter_upwards [hF.coords] with ω hω t
    funext i
    ext j
    simp [ofCoords, shiftProc, hω]

theorem eqlaw_flow_compare {D : DynData d}
    (hb : IsLocLipschitzDrift (liftedFree d N) (fun _ Z => liftedDrift D Z)) {T : ℝ}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N} (u : ℝ≥0)
    (hstr : IsStrongSolution P D ((u : ℝ) + T) X₀ W X)
    {ℱ1 : Filtration ℝ mΩ} {W1 : ℝ≥0 → Ω → Fin N × Fin d → ℝ} (hBF : IsBrownianFiltration P ℱ1 W1)
    (hdrv : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (fun i => W (u + t) ω i - W u ω i) = ofCoords W1 t ω)
    (hJ : Measurable (fun ω => ((X u ω, bfPath hBF ω) : Sig d N))) {Q : Measure (Sig d N)}
    (hmap : P.map (fun ω => ((X u ω, bfPath hBF ω) : Sig d N)) = Q)
    {Xσ : ℝ≥0 → Sig d N → Config d N} (hσ : IsStrongSolution Q D T Prod.fst (sigW d N) Xσ) :
    ∀ᵐ ω ∂P, ∀ s : ℝ≥0, (s : ℝ) ≤ T → X (u + s) ω = Xσ s ((X u ω, bfPath hBF ω) : Sig d N) := by
  have S1 := eqlaw_isStrongSolution_shift hstr
  have S1' : IsStrongSolution P D T (X u) (ofCoords W1) (fun s => X (u + s)) :=
    eqlaw_isStrongSolution_congr S1 (Filter.Eventually.of_forall fun ω => rfl)
      (hdrv.mono fun ω h t => h t)
  have S2 := eqlaw_isStrongSolution_comp _ hJ hmap hσ
  have S2' : IsStrongSolution P D T (X u) (ofCoords W1)
      (fun t ω => Xσ t ((X u ω, bfPath hBF ω) : Sig d N)) := S2
  have hPU := pathwiseUnique_of_locLipschitz P D hb T (X u) (ofCoords W1)
    (isVectorBrownian_of_isBrownianFiltration P ℱ1 W1 hBF)
  filter_upwards [hPU _ _ S1' S2'] with ω hω s hs using hω s hs


theorem eqlaw_window_eq {s : ℝ} {V : Torus d → ℝ} {β : ℝ} (m T : ℝ) {u : ℝ} (hu : 0 ≤ u)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) {X : ℝ≥0 → Ω → Config d N}
    (G : Measure (Config d N))
    (hstat : ∀ t : ℝ≥0, (t : ℝ) ≤ u + T → P.map (X t) = G)
    {J : Ω → Sig d N} {Xσ : ℝ≥0 → Sig d N → Config d N}
    (hcmp : ∀ᵐ ω ∂P, ∀ r : ℝ≥0, (r : ℝ) ≤ T → X (Real.toNNReal u + r) ω = Xσ r (J ω)) :
    ∀ᵐ ω ∂P, Main.windowZeta m T u P X ω =
      eqlaw_pathOf d m T (fun t : Set.Icc (0 : ℝ) T => zetaE m G (Xσ (Real.toNNReal t) (J ω))) := by
  filter_upwards [hcmp] with ω hω
  have hf : (fun t : Set.Icc (0 : ℝ) T => zetaE m (P.map (X (Real.toNNReal (u + t))))
        (X (Real.toNNReal (u + t)) ω)) =
      fun t : Set.Icc (0 : ℝ) T => zetaE m G (Xσ (Real.toNNReal t) (J ω)) := by
    funext t
    have ht0 : 0 ≤ (t : ℝ) := t.2.1
    have ht1 : (t : ℝ) ≤ T := t.2.2
    have hn : Real.toNNReal (u + t) = Real.toNNReal u + Real.toNNReal t :=
      Real.toNNReal_add hu ht0
    have h1 : P.map (X (Real.toNNReal (u + t))) = G :=
      hstat _ (by rw [Real.coe_toNNReal _ (by linarith)]; linarith)
    rw [h1, hn, hω (Real.toNNReal t) (by rw [Real.coe_toNNReal _ ht0]; exact ht1)]
  show eqlaw_pathOf d m T _ = _
  rw [hf]

end HRS.MD.EQLawPath
