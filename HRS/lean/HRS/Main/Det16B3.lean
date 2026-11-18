import HRS.Main.GFB2Aux2
import HRS.Main.Assumptions

/-!
# det16b L9: continuity of the fluctuation path for `MainData` (Example A.16)

`MainData` version of `gfb2_fluc_cont_path` (GFB2Aux2), plus the law of `flucPath` when the particle path is a.s. constant.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Main.Det16

open HRS HRS.GF HRS.Uniform

variable {d : ℕ}

/-- Weak time continuity of `t ↦ ∫ ψ ρ_N(t)` on `[0,T]` from `MeanFieldRegularity`. -/
theorem det16b_weak (S : MainData d) {r : ℕ} {Λ : ℝ} (hr : d + 1 ≤ r) (hmf : MeanFieldRegularity S r Λ)
    (hV : Torus.IsCk 1 S.V) {N : ℕ} (hN : 1 ≤ N) :
    ∀ ψ : Torus d → ℝ, Continuous ψ →
      ContinuousOn (fun t => ∫ x, ψ x * S.ρ N t x) (Set.Icc 0 S.T) :=
  Q54c.weak_continuity (S.dyn N) S.hd S.T Λ S.hT.le r hr (S.ρ N) (hmf.solution N hN)
    (hmf.regular N hN).1 hV

/-- **L9** (`MainData` version of `gfb2_fluc_cont_path`).  For a continuous particle path the rescaled
fluctuation path `t ↦ σ ofMeasureDiff_m(emp X^t, ρ_N^t)` is continuous on `[0,T]` in `E_m`, `d < 2m`. -/
theorem det16b_fluc_cont (S : MainData d) {r : ℕ} {Λ : ℝ} (hr : d + 1 ≤ r)
    (hmf : MeanFieldRegularity S r Λ) (hV : Torus.IsCk 1 S.V) {N : ℕ} (hN : 1 ≤ N)
    {m : ℝ} (hm2 : (d : ℝ) < 2 * m) {Ω : Type*} (X : ℝ≥0 → Ω → Config d N) (σ : ℝ) (ω : Ω)
    (hc : ∀ i, Continuous fun t : ℝ≥0 => X t ω i) :
    Continuous fun t : Set.Icc (0 : ℝ) S.T => flucProc m σ X (S.ρ N) t ω := by
  have hMFN := hmf.solution N hN
  have hweak := det16b_weak S hr hmf hV hN
  have hprob : ∀ t : Set.Icc (0 : ℝ) S.T, IsProbabilityMeasure (withDensityReal (S.ρ N t)) :=
    fun t => isProb_withDensityReal (hMFN.density t.1 t.2)
  have hb : Summable fun k : NonzeroLattice d => σ ^ 2 * (8 * Lattice.jp k.1 ^ (-(2 * m))) :=
    ((summable_jp_rpow (d := d) m hm2).mul_left 8).mul_left (σ ^ 2)
  have hcoord : ∀ (t : Set.Icc (0 : ℝ) S.T) (k : NonzeroLattice d),
      NegSobolev.coord (flucProc m σ X (S.ρ N) t ω) k =
        σ * (Lattice.jp k.1 ^ (-m) * ((N : ℝ)⁻¹ * ∑ i, Torus.realMode k (X (Real.toNNReal t) ω i) -
          ∫ x, Torus.realMode k x * S.ρ N t x)) := by
    intro t k
    haveI := hprob t
    unfold flucProc
    have h1 : NegSobolev.coord (σ • NegSobolev.ofMeasureDiff m (empirical (X (Real.toNNReal t) ω))
        (withDensityReal (S.ρ N t))) k =
        σ * NegSobolev.coord (NegSobolev.ofMeasureDiff m (empirical (X (Real.toNNReal t) ω))
        (withDensityReal (S.ρ N t))) k := rfl
    rw [h1, coord_ofMeasureDiff hm2]
    congr 2
    congr 1
    · unfold Torus.measureRealCoeff
      exact integral_empirical _ (continuous_realMode' k)
    · unfold Torus.measureRealCoeff
      rw [integral_withDensityReal_eq _ (hMFN.density t.1 t.2).measurable (hMFN.density t.1 t.2).nonneg]
      exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  refine gfb2_continuous_of_coords _ _ hb (fun t k => ?_) (fun k => ?_)
  · haveI := hprob t
    haveI : IsFiniteMeasure (empirical (X (Real.toNNReal t) ω)) := inferInstance
    have := gfb2_coord_sq_le (m := m) hm2 (empirical (X (Real.toNNReal t) ω)) (withDensityReal (S.ρ N t))
      (by
        have := gfb2_empirical_mass (X (Real.toNNReal t) ω)
        have h2 := ENNReal.toReal_mono ENNReal.one_ne_top this
        simpa using h2)
      (by simp) k
    have e : NegSobolev.coord (flucProc m σ X (S.ρ N) t ω) k =
        σ * NegSobolev.coord (NegSobolev.ofMeasureDiff m (empirical (X (Real.toNNReal t) ω))
          (withDensityReal (S.ρ N t))) k := rfl
    rw [e, mul_pow]
    exact mul_le_mul_of_nonneg_left this (sq_nonneg σ)
  · simp only [hcoord]
    refine continuous_const.mul (continuous_const.mul (Continuous.sub ?_ ?_))
    · refine continuous_const.mul (continuous_finsetSum _ fun i _ => ?_)
      exact (continuous_realMode' k).comp ((hc i).comp (continuous_real_toNNReal.comp continuous_subtype_val))
    · exact (hweak (Torus.realMode k) (continuous_realMode' k)).comp_continuous continuous_subtype_val
        (fun t => t.2)

/-- Continuity of the deterministic fluctuation path of a fixed configuration `y` (the constant particle
path), the hypothesis `hcont` of `det16b_law_flucPath_dirac`. -/
theorem det16b_const_cont (S : MainData d) {r : ℕ} {Λ : ℝ} (hr : d + 1 ≤ r)
    (hmf : MeanFieldRegularity S r Λ) (hV : Torus.IsCk 1 S.V) {N : ℕ} (hN : 1 ≤ N)
    {m : ℝ} (hm2 : (d : ℝ) < 2 * m) (σ : ℝ) (y : Config d N) :
    Continuous fun t : Set.Icc (0 : ℝ) S.T =>
      σ • NegSobolev.ofMeasureDiff m (empirical y) (withDensityReal (S.ρ N t)) :=
  det16b_fluc_cont S hr hmf hV hN hm2 (fun (_ : ℝ≥0) (_ : Unit) => y) σ ()
    (fun _ => continuous_const)

/-- The deterministic fluctuation path of a configuration `y`, as an element of the path space (given its
continuity, e.g. from `det16b_fluc_cont` applied to the constant path). -/
def det16b_constPath {N : ℕ} (m T σ : ℝ) (ρ : ℝ → Torus d → ℝ) (y : Config d N)
    (hcont : Continuous fun t : Set.Icc (0 : ℝ) T =>
      σ • NegSobolev.ofMeasureDiff m (empirical y) (withDensityReal (ρ t))) : PathSpace d m T :=
  ⟨_, hcont⟩

/-- If the particle path equals a fixed configuration `y` a.s. on `[0,T]`, the law of `flucPath` is the
Dirac mass at the deterministic fluctuation path (no measurability of the particle process is needed). -/
theorem det16b_law_flucPath_dirac {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {N : ℕ} (m T σ : ℝ) (X : ℝ≥0 → Ω → Config d N) (ρ : ℝ → Torus d → ℝ) (y : Config d N)
    (hX : ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, X (Real.toNNReal t) ω = y)
    (hcont : Continuous fun t : Set.Icc (0 : ℝ) T =>
      σ • NegSobolev.ofMeasureDiff m (empirical y) (withDensityReal (ρ t))) :
    law P (flucPath m T σ X ρ) = Measure.dirac (det16b_constPath m T σ ρ y hcont) := by
  have hae : flucPath m T σ X ρ =ᵐ[P] fun _ => det16b_constPath m T σ ρ y hcont := by
    filter_upwards [hX] with ω hω
    have e : (fun t : Set.Icc (0 : ℝ) T => σ • NegSobolev.ofMeasureDiff m
        (empirical (X (Real.toNNReal t) ω)) (withDensityReal (ρ t))) =
        fun t : Set.Icc (0 : ℝ) T => σ • NegSobolev.ofMeasureDiff m (empirical y)
          (withDensityReal (ρ t)) := by
      funext t; rw [hω t t.2]
    have hc : Continuous fun t : Set.Icc (0 : ℝ) T => σ • NegSobolev.ofMeasureDiff m
        (empirical (X (Real.toNNReal t) ω)) (withDensityReal (ρ t)) := by rw [e]; exact hcont
    have key : flucPath m T σ X ρ ω = (⟨_, hc⟩ : PathSpace d m T) := by
      unfold flucPath
      exact dif_pos hc
    rw [key]
    refine ContinuousMap.ext fun t => ?_
    exact congrFun e t
  have hmeas : AEMeasurable (flucPath m T σ X ρ) P :=
    aemeasurable_const.congr hae.symm
  refine (Measure.map_congr hae).trans ?_
  rw [Measure.map_const, measure_univ, one_smul]

end HRS.Main.Det16
