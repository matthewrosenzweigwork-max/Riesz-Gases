import HRS.ME.FamVC
import HRS.ME.RetPathLaw
import HRS.Main.HeadlineEquilibrium
import HRS.Sections.Q38bAux4
import HRS.MH.CondOuDefs
import HRS.MH.CondOuA
import HRS.MH.CondOuP1
import HRS.MH.CondOuP2
import HRS.MH.CondOuP3
import HRS.MH.CondOuP4
import HRS.MH.CondOuP5
import HRS.MH.CondOuP6
import HRS.MH.CondOuP7

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators BoundedContinuousFunction

namespace HRS.MH.CondOuPackets

open HRS HRS.Main HRS.LZ

variable {d : ℕ}

/-- Measurability of the linear coordinate. -/
theorem p_cp8_linCoord_meas {N : ℕ} (k : Lattice d) :
    Measurable (fun X : Config d N => linCoord (volume : Measure (Torus d)) (PDE.cosTest k) X) := by
  have hψ : Measurable (PDE.cosTest k : Torus d → ℝ) := (continuous_const.mul (Torus.continuous_cosMode k)).measurable
  unfold linCoord
  refine measurable_const.mul ((measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_)).sub
    measurable_const)
  exact hψ.comp (measurable_pi_apply i)

/-- Time-marginals of a selected flow are measurable (`d ≥ 2`). -/
theorem p_cp8_adapted (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {N : ℕ} {T : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hsel : SelectedFlow P (PDE.mfData d s hs0 hsd (fun _ => (0 : ℝ)) β hβ) T X₀ W X) (τ : ℝ≥0) :
    Measurable (X τ) := by
  rcases hsel.flow with ⟨hs, -⟩ | ⟨hd1, -⟩
  · exact hs.adapted τ
  · exact absurd hd1 (by omega)

/-- A selected flow starts at `X₀` (`d ≥ 2`). -/
theorem p_cp8_init (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {N : ℕ} {T : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hsel : SelectedFlow P (PDE.mfData d s hs0 hsd (fun _ => (0 : ℝ)) β hβ) T X₀ W X) :
    ∀ᵐ ω ∂P, X 0 ω = X₀ ω := by
  rcases hsel.flow with ⟨hs, -⟩ | ⟨hd1, -⟩
  · exact hs.init
  · exact absurd hd1 (by omega)

/-- P8 -/
theorem p8_assembly (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (k : Lattice d) (hk : k ≠ 0) :
    (∀ (t : ℝ), 0 ≤ t →
      ∀ (Ω : ℕ → Type) [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
        [∀ N, IsProbabilityMeasure (P N)]
        (X₀ : ∀ N, Ω N → Config d N) (W : ∀ N, ℝ≥0 → Ω N → (Fin N → Euc d))
        (X : ∀ N, ℝ≥0 → Ω N → Config d N),
        (∀ N : ℕ, 2 ≤ N → SelectedFlow (P N) (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ) t
          (X₀ N) (W N) (X N)) →
        (∀ N : ℕ, 2 ≤ N → ∃ (ℱ : MeasureTheory.Filtration ℝ (inferInstance : MeasurableSpace (Ω N)))
          (W' : ℝ≥0 → Ω N → (Fin N × Fin d) → ℝ), IsFilteredSolution (P N) ℱ W' (W N) (X N)) →
        (∀ N : ℕ, 2 ≤ N → law (P N) (X₀ N) =
          ProbabilityTheory.cond (canonicalGibbs (periodicRiesz d s) (fun _ => (0 : ℝ)) N β)
            {Y | 0 < linCoord (volume : Measure (Torus d)) (PDE.cosTest k) Y}) →
        ConvergesInLaw
          (fun N : ℕ => law (P N) (fun ω =>
            linCoord (volume : Measure (Torus d)) (PDE.cosTest k) (X N (Real.toNNReal t) ω)))
          (halfNormalMixtureLaw d s β k t)) := by
  classical
  intro t ht Ω _ P _ X₀ W X hsel hfil hν f
  have hV : Torus.IsSmooth (fun _ : Torus d => (0 : ℝ)) := HRS.d1_isSmooth_const 0
  have hex : ∀ n : ℕ, ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (X₀ : Ω → Config d (n + 2)) (W : ℝ≥0 → Ω → (Fin (n + 2) → Euc d)) (X : ℝ≥0 → Ω → Config d (n + 2)),
      IsStationaryGibbsFlow P s hs0 hsd (fun _ => (0 : ℝ)) β hβ t X₀ W X :=
    fun n => HRS.MD.EQLawFlow.eq_flow_exists_proof hd hs0 hsd _ hV hβ (by omega) t ht
  choose Ω₂ inst₂ P₂ hP₂ X₀₂ W₂ X₂ h₂ using hex
  have hmeas : ∀ n τ, Measurable (X₂ n τ) := fun n τ => p_cp8_adapted hd hs0 hsd hβ (h₂ n).flow τ
  have hjoint := condou_stationary_joint hd hs0 hsd hβ k hk t ht Ω₂ P₂ X₀₂ W₂ X₂ h₂
  have hpm : ∀ n, Measurable (fun ω => (WithLp.toLp 2 ![
        linCoord (volume : Measure (Torus d)) (PDE.cosTest k) (X₂ n 0 ω),
        linCoord (volume : Measure (Torus d)) (PDE.cosTest k) (X₂ n (Real.toNNReal t) ω)] :
        EuclideanSpace ℝ (Fin 2))) := fun n =>
    (WithLp.measurable_toLp 2 (Fin 2 → ℝ)).comp (measurable_pi_iff.2 (Fin.forall_fin_two.2
      ⟨(p_cp8_linCoord_meas k).comp (hmeas n 0), (p_cp8_linCoord_meas k).comp (hmeas n _)⟩))
  have hνp : ∀ n, IsProbabilityMeasure (law (P₂ n) (fun ω => (WithLp.toLp 2 ![
        linCoord (volume : Measure (Torus d)) (PDE.cosTest k) (X₂ n 0 ω),
        linCoord (volume : Measure (Torus d)) (PDE.cosTest k) (X₂ n (Real.toNNReal t) ω)] :
        EuclideanSpace ℝ (Fin 2)))) := fun n => inferInstance
  -- P6 with `a = x ↦ x 0`, `g = 2 f (x 1)`
  have hxm : Continuous (fun x : EuclideanSpace ℝ (Fin 2) => x 1) := by fun_prop
  have hx0 : Continuous (fun x : EuclideanSpace ℝ (Fin 2) => x 0) := by fun_prop
  let g : EuclideanSpace ℝ (Fin 2) →ᵇ ℝ := (2 : ℝ) • f.compContinuous ⟨fun x => x 1, hxm⟩
  have hg : ∀ x, g x = 2 * f (x 1) := fun x => by simp [g]
  have hlim := condou_tendsto_indicator2 _ (multivariateGaussian 0 (condouCov d s β k t))
    (fun x : EuclideanSpace ℝ (Fin 2) => x 0) hx0 (condou_gauss_pair_nullset hd hs0 hsd hβ k t ht) hjoint g
  have hg' : (fun x : EuclideanSpace ℝ (Fin 2) => Set.indicator {x : EuclideanSpace ℝ (Fin 2) | 0 < x 0} (fun x => g x) x) =
      fun x => Set.indicator {x : EuclideanSpace ℝ (Fin 2) | 0 < x 0} (fun x => 2 * f (x 1)) x := by
    funext x; simp only [hg]
  simp only [hg'] at hlim
  rw [condou_gauss_pair_integral hd hs0 hsd hβ k t ht f] at hlim
  -- the sequence in question
  have hseq : ∀ n : ℕ, ∫ x, f x ∂(law (P (n + 2)) (fun ω =>
      linCoord (volume : Measure (Torus d)) (PDE.cosTest k) (X (n + 2) (Real.toNNReal t) ω))) =
      ∫ x, Set.indicator {x : EuclideanSpace ℝ (Fin 2) | 0 < x 0} (fun x => 2 * f (x 1)) x
        ∂(law (P₂ n) (fun ω => (WithLp.toLp 2 ![
        linCoord (volume : Measure (Torus d)) (PDE.cosTest k) (X₂ n 0 ω),
        linCoord (volume : Measure (Torus d)) (PDE.cosTest k) (X₂ n (Real.toNNReal t) ω)] :
        EuclideanSpace ℝ (Fin 2)))) := by
    intro n
    have hN : 2 ≤ n + 2 := by omega
    have hXm : Measurable (fun ω => linCoord (volume : Measure (Torus d)) (PDE.cosTest k)
        (X (n + 2) (Real.toNNReal t) ω)) :=
      (p_cp8_linCoord_meas k).comp (p_cp8_adapted hd hs0 hsd hβ (hsel (n + 2) hN) _)
    have hprob := HRS.MH.CondOuP.conditioned_ou_prob_proof hd hs0 hsd β hβ k hk (n + 2) (by omega)
    have hA : MeasurableSet {Y : Config d (n + 2) |
        0 < linCoord (volume : Measure (Torus d)) (PDE.cosTest k) Y} :=
      measurableSet_lt measurable_const (p_cp8_linCoord_meas k)
    have hP1 := condou_weighted_integral hd hs0 hsd hβ hN t ht (P (n + 2)) (X₀ (n + 2)) (W (n + 2))
      (X (n + 2)) (hsel _ hN) (hfil _ hN) (P₂ n) (X₀₂ n) (W₂ n) (X₂ n) (h₂ n)
      {Y | 0 < linCoord (volume : Measure (Torus d)) (PDE.cosTest k) Y} hA hprob (hν _ hN)
      (fun Y => linCoord (volume : Measure (Torus d)) (PDE.cosTest k) Y) (p_cp8_linCoord_meas k)
      (Real.toNNReal t) (by rw [Real.coe_toNNReal _ ht]) f
    have hind : Measurable (fun x : EuclideanSpace ℝ (Fin 2) =>
        Set.indicator {x : EuclideanSpace ℝ (Fin 2) | 0 < x 0} (fun x => 2 * f (x 1)) x) :=
      (measurable_const.mul (f.continuous.measurable.comp hxm.measurable)).indicator
        (measurableSet_lt measurable_const hx0.measurable)
    rw [law, integral_map hXm.aemeasurable f.continuous.aestronglyMeasurable, hP1, law,
      integral_map (hpm n).aemeasurable hind.aestronglyMeasurable]
    refine integral_congr_ae ?_
    filter_upwards [p_cp8_init hd hs0 hsd hβ (h₂ n).flow] with ω hω
    rw [← hω]
    by_cases h : 0 < linCoord (volume : Measure (Torus d)) (PDE.cosTest k) (X₂ n 0 ω)
    · simp [Set.indicator, h]
    · simp [Set.indicator, h]
  have hfin : Tendsto (fun N : ℕ => ∫ x, f x ∂(law (P N) (fun ω =>
      linCoord (volume : Measure (Torus d)) (PDE.cosTest k) (X N (Real.toNNReal t) ω)))) atTop
      (𝓝 (∫ y, f y ∂(halfNormalMixtureLaw d s β k t))) := by
    rw [← tendsto_add_atTop_iff_nat 2]
    simp only [hseq]
    exact hlim
  exact hfin

end HRS.MH.CondOuPackets

end
