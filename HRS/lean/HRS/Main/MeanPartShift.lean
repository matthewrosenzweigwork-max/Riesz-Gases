import HRS.Main.MeanPartFlow
import HRS.Main.MeanPartMetric
import HRS.Main.T25Aux6
import HRS.Main.ThermAux13
import HRS.Sections.AdjKDFinal
import HRS.Uniform.Comp28W10

/-!
# MEANPART (shift): L6 `mp_window_eq_map`, L7 `mp_window_aemeasurable`, L9 `mp_toPath_add_const`

(packet `mpshift`, plan `docs/MAIN_A_PLAN_mean_particles.md`, section 4.)
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Main

variable {d : ℕ}

theorem mp_isProbDensity_one : IsProbDensity (fun _ : Torus d => (1 : ℝ)) :=
  (mp_thermalDensity_one (fun _ : Torus d => (0 : ℝ)) 1).1

/-- **L7** (measurability of the windowed fluctuation field, any constant centre). -/
theorem mp_window_aemeasurable {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (hN : 1 ≤ N)
    (P : Measure Ω) (X : ℝ≥0 → Ω → Config d N) (hXm : ∀ t, Measurable (X t))
    (hXc : ∀ᵐ ω ∂P, ∀ i, Continuous fun t : ℝ≥0 => X t ω i) {m : ℝ} (hm2 : (d : ℝ) < 2 * m)
    {a : ℝ} (ha : 0 ≤ a) {T : ℝ} (hT : 0 ≤ T) (σ : ℝ) {ρβ : Torus d → ℝ} (hρβ : IsProbDensity ρβ) :
    AEMeasurable (windowFluc m T a σ X (fun _ => ρβ)) P := by
  haveI : IsProbabilityMeasure (withDensityReal ρβ) := HRS.isProb_withDensityReal hρβ
  have hm0 : (d : ℝ) / 2 < m := by linarith
  have hflm : ∀ t, Measurable (fun ω => GF.flucProc m σ X (fun _ => ρβ) t ω) := fun t =>
    ((GF.gf_measurable_ofMeasureDiff_proof m hm0 (withDensityReal ρβ)).const_smul σ).comp (hXm _)
  have hc : ∀ᵐ ω ∂P, ContinuousOn (fun t => GF.flucProc m σ X (fun _ => ρβ) t ω)
      (Set.Icc 0 (a + T)) := by
    filter_upwards [hXc] with ω hω
    have hXp : Continuous fun t : Set.Icc (0 : ℝ) (a + T) => X (Real.toNNReal t) ω :=
      continuous_pi fun i => (hω i).comp (continuous_real_toNNReal.comp continuous_subtype_val)
    have := therm_cont_emp (a + T) hm2 hN σ (fun t => X (Real.toNNReal t) ω) hXp
      (fun _ => withDensityReal ρβ) (fun k => continuous_const)
    exact continuousOn_iff_continuous_restrict.mpr this
  have h1 := HRS.Uniform.Comp28.aem_wp_a P ha hT _ (fun t _ => hflm t) hc
  have e : windowFluc m T a σ X (fun _ => ρβ) = fun ω =>
      (Uniform.windowPath a T (GF.flucProc m σ X (fun _ => ρβ)) ω : PathSpace d m T) :=
    funext fun ω => T25.t25_windowFluc_eq m T a σ ha X (fun _ => ρβ) ω
  rw [e]
  exact h1

/-- The deterministic shift path `t ↦ √N (μ^{a+t} - dx)` (`Dp_n` of the plan). -/
def mp_Dp (S : PreparedData d) {m : ℝ} (hm2 : (d : ℝ) < 2 * m) (T a : ℝ) (ha : 0 ≤ a) (σ : ℝ) :
    PathSpace d m T :=
  (⟨therm_Dfun S T a m σ (fun _ => 1), therm_Dfun_cont S T a hm2 ha σ mp_isProbDensity_one⟩ :
    C(Set.Icc (0 : ℝ) T, NegSobolev d m))

/-- **L6**: the law of the window centred at `1` (Haar measure) is the law of the window centred at
the mean-field solution, translated by the deterministic path `Dp`. -/
theorem mp_window_eq_map (S : PreparedData d) {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (hN : 1 ≤ N) (P : Measure Ω) (X : ℝ≥0 → Ω → Config d N) (hXm : ∀ t, Measurable (X t))
    (hXc : ∀ᵐ ω ∂P, ∀ i, Continuous fun t : ℝ≥0 => X t ω i) {m : ℝ} (hm2 : (d : ℝ) < 2 * m)
    {a : ℝ} (ha : 0 ≤ a) {T : ℝ} (hT : 0 ≤ T) :
    law P (windowFluc m T a (Real.sqrt N) X (fun _ _ => (1 : ℝ))) =
      (S.etaLaw m T a P X).map (fun w => w + mp_Dp S hm2 T a ha (Real.sqrt N)) := by
  have hW : AEMeasurable (windowFluc m T a (Real.sqrt N) X (fun _ _ => (1 : ℝ))) P :=
    mp_window_aemeasurable hN P X hXm hXc hm2 ha hT (Real.sqrt N) mp_isProbDensity_one
  have hae : ∀ᵐ ω ∂P, windowFluc m T a (Real.sqrt N) X (fun _ _ => (1 : ℝ)) ω =
      windowFluc m T a (Real.sqrt N) X S.ρ ω + mp_Dp S hm2 T a ha (Real.sqrt N) := by
    filter_upwards [hXc] with ω hω
    exact therm_window_eq S T a hm2 hN ha (Real.sqrt N) mp_isProbDensity_one X ω hω
  have hη : AEMeasurable (windowFluc m T a (Real.sqrt N) X S.ρ) P := by
    refine (hW.sub_const (mp_Dp S hm2 T a ha (Real.sqrt N))).congr ?_
    filter_upwards [hae] with ω hω
    simp [hω]
  have hadd : Measurable (fun w : PathSpace d m T => w + mp_Dp S hm2 T a ha (Real.sqrt N)) :=
    (continuous_id.add continuous_const).measurable
  unfold PreparedData.etaLaw law
  rw [AEMeasurable.map_map_of_aemeasurable hadd.aemeasurable hη]
  exact Measure.map_congr hae

/-! ### L9: adding a deterministic continuous path to a process -/

/-- The path `t ↦ s t` on `[0,T]`. -/
def mp_shiftPath (m T : ℝ) (s : ℝ → NegSobolev d m) (hs : ContinuousOn s (Set.Icc 0 T)) :
    PathSpace d m T :=
  (⟨fun t : Set.Icc (0 : ℝ) T => s t, continuousOn_iff_continuous_restrict.mp hs⟩ :
    C(Set.Icc (0 : ℝ) T, NegSobolev d m))

/-- **L9**: `toPath (Z + s) = toPath Z + s` almost surely. -/
theorem mp_toPath_add_const {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') (m T : ℝ)
    (Z : ℝ → Ω' → NegSobolev d m) (hZ : ∀ᵐ ω ∂P', ContinuousOn (fun t => Z t ω) (Set.Icc 0 T))
    (s : ℝ → NegSobolev d m) (hs : ContinuousOn s (Set.Icc 0 T)) :
    ∀ᵐ ω ∂P', toPath m T (fun t ω' => Z t ω' + s t) ω =
      toPath m T Z ω + mp_shiftPath m T s hs := by
  filter_upwards [hZ] with ω hω
  have h1 : Continuous fun t : Set.Icc (0 : ℝ) T => Z t ω :=
    continuousOn_iff_continuous_restrict.mp hω
  have h2 : Continuous fun t : Set.Icc (0 : ℝ) T => Z t ω + s t :=
    continuousOn_iff_continuous_restrict.mp (hω.add hs)
  have e1 : toPath m T (fun t ω' => Z t ω' + s t) ω =
      (⟨fun t : Set.Icc (0 : ℝ) T => Z t ω + s t, h2⟩ : C(Set.Icc (0 : ℝ) T, NegSobolev d m)) :=
    dif_pos h2
  have e2 : toPath m T Z ω =
      (⟨fun t : Set.Icc (0 : ℝ) T => Z t ω, h1⟩ : C(Set.Icc (0 : ℝ) T, NegSobolev d m)) :=
    dif_pos h1
  rw [e1, e2]
  rfl

/-- Measurability of `toPath (Z + s)`. -/
theorem mp_toPath_add_const_aemeasurable {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω')
    (m T : ℝ) (Z : ℝ → Ω' → NegSobolev d m) (hmeas : ∀ t, Measurable (Z t))
    (hZ : ∀ᵐ ω ∂P', ContinuousOn (fun t => Z t ω) (Set.Icc 0 T))
    (s : ℝ → NegSobolev d m) (hs : ContinuousOn s (Set.Icc 0 T)) :
    AEMeasurable (toPath m T (fun t ω' => Z t ω' + s t)) P' := by
  refine AdjK.adjk_toPath_aemeasurable_proof P' m T _ (fun t => (hmeas t).add_const _) ?_
  filter_upwards [hZ] with ω hω
  exact hω.add hs

/-- The law of `toPath (Z + s)` is the translate of the law of `toPath Z`. -/
theorem mp_law_toPath_add_const {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') (m T : ℝ)
    (Z : ℝ → Ω' → NegSobolev d m) (hmeas : ∀ t, Measurable (Z t))
    (hZ : ∀ᵐ ω ∂P', ContinuousOn (fun t => Z t ω) (Set.Icc 0 T))
    (s : ℝ → NegSobolev d m) (hs : ContinuousOn s (Set.Icc 0 T)) :
    law P' (toPath m T (fun t ω' => Z t ω' + s t)) =
      (law P' (toPath m T Z)).map (fun w => w + mp_shiftPath m T s hs) := by
  have hZm : AEMeasurable (toPath m T Z) P' := by
    simpa using mp_toPath_add_const_aemeasurable P' m T Z hmeas hZ (fun _ => 0)
      continuousOn_const
  have hadd : Measurable (fun w : PathSpace d m T => w + mp_shiftPath m T s hs) :=
    (continuous_id.add continuous_const).measurable
  unfold law
  rw [AEMeasurable.map_map_of_aemeasurable hadd.aemeasurable hZm]
  exact Measure.map_congr (mp_toPath_add_const P' m T Z hZ s hs)

end Main

end HRS
