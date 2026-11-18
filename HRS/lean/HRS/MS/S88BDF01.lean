import HRS.MS.S88BDA05
import HRS.MS.S88BDP02
import HRS.MS.S88BDM03
import HRS.MS.S88BDM04

/-!
# S8.8.F01: particle window and full-time supremum assembly

`s88_particle_decay`: P01 gives the a.e. measurability, exchangeability and the probability first marginal, P02 the
second moments of the centered particle observables of the orbit tests, the envelope of A05 the common base/increment
inputs of M03 (with `K = max Cin 1`), and M04 identifies the supremum over `[0,T]` with the rational-time supremum
pathwise (every coordinate `t ↦ √N(μ_N(f_t) - ∫ f_t dm_N)` is continuous: the empirical term is a finite sum of
continuous functions of `t`, and the first-marginal integral is continuous by dominated convergence with the compact-time
uniform bound of `S88OrbitRegular`).
-/

set_option autoImplicit false
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal BigOperators

namespace HRS.MS.S88Breakdown

open HRS HRS.Whole

theorem s88_particle_decay {d : ℕ} (hd : 2 ≤ d) (a β : ℝ)
    (ha : 0 < a) (hβ : 0 < β) (m : ℝ) (ρ : Euc d → ℝ)
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρ)
    (c : ℝ) (b : MultiIndex d → ℝ) (hb : ∀ α, 0 ≤ b α) (hsum : Summable b)
    (hreg : S88OrbitRegular (critCoeff d a β ρ) m)
    (henv : S88OrbitEnvelope (critCoeff d a β ρ) (HRS.Whole.withDensityReal ρ) m c b)
    (T Cin u : ℝ) (hT : 0 < T) (hu : 1 ≤ u) (N : ℕ) (hN : 2 ≤ N)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → EucConfig d N)
    (hlaw : law P X = HRS.Whole.canonicalGibbs (rieszKernel d ((d : ℝ) / 2)) (confinement a) N β)
    (hvar : ∀ f : Euc d → ℝ, MemLp f 2 (HRS.Whole.withDensityReal ρ) →
      evariance (fun z => HRS.Whole.linStat f (X z)) P ≤
        ENNReal.ofReal (Cin / N * ∫ x, f x ^ 2 ∂(HRS.Whole.withDensityReal ρ))) :
    ((∫⁻ z, (⨆ t : Set.Icc (0 : ℝ) T, HRS.Whole.l2NormE (fun α : MultiIndex d =>
      s88Particle P X (s88Orbit (critCoeff d a β ρ) m (u + t.1) α) z)) ^ 2 ∂P) ^
        (1 / 2 : ℝ)) ≤ ENNReal.ofReal (s88Constant T Cin b * Real.exp (-c * u)) := by
  have hN1 : 1 ≤ N := by omega
  have hprob : HRS.Whole.IsProbDensity ρ := hρ.1.1
  haveI := Q34.isProbabilityMeasure_nu hprob
  obtain ⟨hX, hex, hfm⟩ := s88_canonical_map_facts hd hN a β ha hβ P X hlaw
  haveI := hfm
  haveI : Countable (S88RatTime T) := s88_ratTime_countable T
  have hK0 : (0 : ℝ) ≤ max Cin 1 := le_trans zero_le_one (le_max_right _ _)
  have hE0 : 0 < Real.exp (-2 * c * u) := Real.exp_pos _
  have hu0 : 0 ≤ u := by linarith
  have hIcc : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ u + t := fun t ht => by linarith [ht.1]
  -- the particle observables of the orbit tests
  have hmem : ∀ (α : MultiIndex d) (t : ℝ), t ∈ Set.Icc (0 : ℝ) T →
      MemLp (fun z => s88Particle P X (s88Orbit (critCoeff d a β ρ) m (u + t) α) z) 2 P := by
    intro α t ht
    have h := hreg.memCb α _ (hIcc t ht)
    exact (s88_particle_second_moments hN1 (HRS.Whole.withDensityReal ρ) Cin P X hX hex hvar _ _
      h h).1
  have hbase : ∀ α : MultiIndex d,
      (∫⁻ z, ENNReal.ofReal ((s88Particle P X (s88Orbit (critCoeff d a β ρ) m (u + 0) α) z) ^ 2) ∂P) ≤
        ENNReal.ofReal (max Cin 1 * b α * Real.exp (-2 * c * u)) := by
    intro α
    have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
    have hmc := hreg.memCb α _ (hIcc 0 h0)
    refine (s88_particle_second_moments hN1 (HRS.Whole.withDensityReal ρ) Cin P X hX hex hvar _ _
      hmc hmc).2.2.1.trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have := (henv.base α u hu).2
    rw [add_zero]
    have hb0 := mul_nonneg (hb α) hE0.le
    have hI : 0 ≤ ∫ x, HRS.Whole.projMean (HRS.Whole.withDensityReal ρ)
        (s88Orbit (critCoeff d a β ρ) m u α) x ^ 2 ∂(HRS.Whole.withDensityReal ρ) :=
      integral_nonneg fun x => sq_nonneg _
    calc _ ≤ max Cin 1 * ∫ x, HRS.Whole.projMean (HRS.Whole.withDensityReal ρ)
          (s88Orbit (critCoeff d a β ρ) m u α) x ^ 2 ∂(HRS.Whole.withDensityReal ρ) :=
          mul_le_mul_of_nonneg_right (max_le_max le_rfl zero_le_one) hI
      _ ≤ max Cin 1 * (b α * Real.exp (-2 * c * u)) := mul_le_mul_of_nonneg_left this hK0
      _ = _ := by ring
  have hinc : ∀ (α : MultiIndex d) (s : ℝ), s ∈ Set.Icc (0 : ℝ) T →
      ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) T →
        (∫⁻ z, ENNReal.ofReal ((s88Particle P X (s88Orbit (critCoeff d a β ρ) m (u + s) α) z -
            s88Particle P X (s88Orbit (critCoeff d a β ρ) m (u + t) α) z) ^ 2) ∂P) ≤
          ENNReal.ofReal (max Cin 1 * b α * Real.exp (-2 * c * u) * (s - t) ^ 2) := by
    intro α s hs t ht
    refine (s88_particle_second_moments hN1 (HRS.Whole.withDensityReal ρ) Cin P X hX hex hvar _ _
      (hreg.memCb α _ (hIcc s hs)) (hreg.memCb α _ (hIcc t ht))).2.2.2.trans ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have := (henv.increment α u s t hu hs.1 ht.1).2
    have hb0 := mul_nonneg (mul_nonneg (hb α) hE0.le) (sq_nonneg (s - t))
    have hI : 0 ≤ ∫ x, HRS.Whole.projMean (HRS.Whole.withDensityReal ρ)
        (fun y => s88Orbit (critCoeff d a β ρ) m (u + s) α y -
          s88Orbit (critCoeff d a β ρ) m (u + t) α y) x ^ 2 ∂(HRS.Whole.withDensityReal ρ) :=
      integral_nonneg fun x => sq_nonneg _
    calc _ ≤ max Cin 1 * ∫ x, HRS.Whole.projMean (HRS.Whole.withDensityReal ρ)
          (fun y => s88Orbit (critCoeff d a β ρ) m (u + s) α y -
            s88Orbit (critCoeff d a β ρ) m (u + t) α y) x ^ 2 ∂(HRS.Whole.withDensityReal ρ) :=
          mul_le_mul_of_nonneg_right (max_le_max le_rfl zero_le_one) hI
      _ ≤ max Cin 1 * (b α * Real.exp (-2 * c * u) * (s - t) ^ 2) :=
          mul_le_mul_of_nonneg_left this hK0
      _ = _ := by ring
  have hM3 := s88_l2_maximal_decay P T (max Cin 1) c u hT hK0 b hb hsum
    (fun t z α => s88Particle P X (s88Orbit (critCoeff d a β ρ) m (u + t) α) z) hmem hbase hinc
    (fun t : S88RatTime T => t.1) (fun t => t.2.1)
  -- pathwise continuity in time
  have hcont : ∀ (z : Ω) (α : MultiIndex d),
      ContinuousOn (fun t : ℝ => s88Particle P X (s88Orbit (critCoeff d a β ρ) m (u + t) α) z)
        (Set.Icc (0 : ℝ) T) := by
    intro z α
    have hshift : ∀ x : Euc d, ContinuousOn
        (fun t : ℝ => s88Orbit (critCoeff d a β ρ) m (u + t) α x) (Set.Icc (0 : ℝ) T) := by
      intro x
      refine (hreg.time_cont α x (u + T) (by linarith)).comp (continuousOn_const.add continuousOn_id)
        (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    unfold s88Particle
    refine continuousOn_const.mul (ContinuousOn.sub ?_ ?_)
    · have : ∀ t ∈ Set.Icc (0 : ℝ) T, HRS.Whole.pair (HRS.Whole.empirical (X z))
          (s88Orbit (critCoeff d a β ρ) m (u + t) α) =
          (1 / (N : ℝ)) * ∑ i, s88Orbit (critCoeff d a β ρ) m (u + t) α (X z i) := fun t ht =>
        s88_pair_empirical hN1 (hreg.memCb α _ (hIcc t ht)).1.continuous _
      refine ContinuousOn.congr ?_ this
      exact continuousOn_const.mul (continuousOn_finsetSum _ fun i _ => hshift (X z i))
    · obtain ⟨B, -, hB⟩ := hreg.local_bdd α (u + T) (by linarith)
      refine continuousOn_of_dominated (bound := fun _ => B) ?_ ?_ (integrable_const B) ?_
      · intro t ht
        exact (hreg.memCb α _ (hIcc t ht)).1.continuous.aestronglyMeasurable
      · intro t ht
        refine Filter.Eventually.of_forall fun x => ?_
        rw [Real.norm_eq_abs]
        exact hB (u + t) ⟨hIcc t ht, by linarith [ht.2]⟩ x
      · exact Filter.Eventually.of_forall hshift
  have hsup : ∀ z : Ω, (⨆ t : Set.Icc (0 : ℝ) T, HRS.Whole.l2NormE (fun α : MultiIndex d =>
      s88Particle P X (s88Orbit (critCoeff d a β ρ) m (u + t.1) α) z)) =
      ⨆ t : S88RatTime T, HRS.Whole.l2NormE (fun α : MultiIndex d =>
        s88Particle P X (s88Orbit (critCoeff d a β ρ) m (u + t.1) α) z) := fun z =>
    s88_sup_eq_rational T hT (fun t α =>
      s88Particle P X (s88Orbit (critCoeff d a β ρ) m (u + t) α) z) (hcont z)
  simp_rw [hsup]
  exact hM3

end HRS.MS.S88Breakdown
