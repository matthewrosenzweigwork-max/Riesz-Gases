import HRS.MS.R2GenInitAux16

/-!
# S10.5 window comparison, packet B3: the initial `𝒦_T`-state `k₀` for a feature family at `r = 0`

Generic version of `GenPathAux24-26` (`s56k0`): for a family `G0 : Fin d → Euc d → 𝒦_T` (the features at time `r = 0`),
`s105k0 G0 σ ν μρ = σ ∫∫∫_0^1 ∑_a (x-y)_a G0_a(y + θ(x-y)) dθ dμρ(y) dν(x)`.  Its pairing with a vector `E` whose pairings with the features
are `∂_a h` is `σ(ν(h) - μρ(h))` (`s105_k0_inner`); measurability of `x ↦ s105k0 G0 σ (empirical x) μρ` (`s105_k0_meas`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2GenInit

open HRS HRS.Whole HRS.MP.RdRem HRS.MS.GenPath

variable {d : ℕ}

/-- The integrand of `k₀`. -/
def s105F {m T : ℝ} (G0 : Fin d → Euc d → KSpace d m T) (p : Euc d × (Euc d × ℝ)) : KSpace d m T :=
  ∑ a : Fin d, (p.1 - p.2.1) a • G0 a (p.2.1 + p.2.2 • (p.1 - p.2.1))

def s105k0 {m T : ℝ} (G0 : Fin d → Euc d → KSpace d m T) (σ : ℝ) (ν μρ : Measure (Euc d)) : KSpace d m T :=
  σ • ∫ p, s105F G0 p ∂(ν.prod (μρ.prod (volume.restrict (Set.Icc (0 : ℝ) 1))))

theorem s105F_meas {m T : ℝ} (G0 : Fin d → Euc d → KSpace d m T) (hmeas : ∀ a : Fin d, Measurable (G0 a)) :
    Measurable (s105F G0) := by
  unfold s105F
  refine Finset.measurable_sum _ fun a _ => ?_
  have h1 : Measurable fun p : Euc d × (Euc d × ℝ) => (p.1 - p.2.1) a :=
    ((EuclideanSpace.proj a : Euc d →L[ℝ] ℝ).continuous.measurable.comp
      (measurable_fst.sub (measurable_fst.comp measurable_snd)))
  have h2 : Measurable fun p : Euc d × (Euc d × ℝ) => G0 a (p.2.1 + p.2.2 • (p.1 - p.2.1)) :=
    (hmeas a).comp ((measurable_fst.comp measurable_snd).add
      ((measurable_snd.comp measurable_snd).smul (measurable_fst.sub (measurable_fst.comp measurable_snd))))
  exact h1.smul h2

theorem s105F_norm_le {m T : ℝ} (G0 : Fin d → Euc d → KSpace d m T) (Bf : ℝ) (hBf : 0 ≤ Bf)
    (hbd : ∀ (a : Fin d) (z : Euc d), ‖G0 a z‖ ≤ Bf) (p : Euc d × (Euc d × ℝ)) :
    ‖s105F G0 p‖ ≤ d * Bf * (‖p.1‖ + ‖p.2.1‖) := by
  unfold s105F
  refine (norm_sum_le _ _).trans ?_
  have : ∀ a : Fin d, ‖(p.1 - p.2.1) a • G0 a (p.2.1 + p.2.2 • (p.1 - p.2.1))‖ ≤
      Bf * (‖p.1‖ + ‖p.2.1‖) := by
    intro a
    rw [norm_smul, mul_comm]
    refine mul_le_mul (hbd _ _) ?_ (norm_nonneg _) hBf
    calc ‖(p.1 - p.2.1) a‖ ≤ ‖p.1 - p.2.1‖ := PiLp.norm_apply_le _ a
      _ ≤ ‖p.1‖ + ‖p.2.1‖ := norm_sub_le _ _
  calc ∑ a : Fin d, ‖(p.1 - p.2.1) a • G0 a (p.2.1 + p.2.2 • (p.1 - p.2.1))‖
      ≤ ∑ _a : Fin d, Bf * (‖p.1‖ + ‖p.2.1‖) := Finset.sum_le_sum fun a _ => this a
    _ = _ := by simp [Finset.sum_const]; ring

theorem s105F_integrable {m T : ℝ} (G0 : Fin d → Euc d → KSpace d m T) (Bf : ℝ) (hBf : 0 ≤ Bf)
    (hmeas : ∀ a : Fin d, Measurable (G0 a)) (hbd : ∀ (a : Fin d) (z : Euc d), ‖G0 a z‖ ≤ Bf)
    (ν μρ : Measure (Euc d)) [IsProbabilityMeasure ν] [IsProbabilityMeasure μρ]
    (hν : Integrable (fun x : Euc d => ‖x‖) ν) (hμ : Integrable (fun x : Euc d => ‖x‖) μρ) :
    Integrable (s105F G0) (ν.prod (μρ.prod (volume.restrict (Set.Icc (0 : ℝ) 1)))) := by
  have : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := ⟨by simp⟩
  refine Integrable.mono' (g := fun p => d * Bf * (‖p.1‖ + ‖p.2.1‖)) ?_
    (s105F_meas G0 hmeas).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => s105F_norm_le G0 Bf hBf hbd p)
  refine Integrable.const_mul ?_ _
  exact (hν.comp_fst _).add ((hμ.comp_fst _).comp_snd ν)

theorem s105_k0_inner {m T : ℝ} (G0 : Fin d → Euc d → KSpace d m T) (σ Bf : ℝ) (hBf : 0 ≤ Bf)
    (hmeas : ∀ a : Fin d, Measurable (G0 a)) (hbd : ∀ (a : Fin d) (z : Euc d), ‖G0 a z‖ ≤ Bf)
    (ν μρ : Measure (Euc d)) [IsProbabilityMeasure ν] [IsProbabilityMeasure μρ]
    (hν : Integrable (fun x : Euc d => ‖x‖) ν) (hμ : Integrable (fun x : Euc d => ‖x‖) μρ)
    (E : KSpace d m T) (h : Euc d → ℝ) (hh : ContDiff ℝ 1 h) (B : ℝ) (hB : ∀ z, |h z| ≤ B)
    (hE : ∀ (a : Fin d) (z : Euc d), inner ℝ (G0 a z) E = gradComp a h z) :
    inner ℝ (s105k0 G0 σ ν μρ) E = σ * (∫ x, h x ∂ν - ∫ x, h x ∂μρ) := by
  haveI : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := ⟨by simp⟩
  have hFm := s105F_meas G0 hmeas
  have hFint := s105F_integrable G0 Bf hBf hmeas hbd ν μρ hν hμ
  have hhm : Continuous h := hh.continuous
  have hhint : ∀ μ : Measure (Euc d), IsProbabilityMeasure μ → Integrable h μ := fun μ _ =>
    Integrable.of_bound hhm.aestronglyMeasurable B (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]; exact hB z)
  unfold s105k0
  rw [inner_smul_left, real_inner_comm, ← integral_inner hFint, conj_trivial]
  congr 1
  have hinner : ∀ p : Euc d × (Euc d × ℝ), inner ℝ E (s105F G0 p) =
      ∑ a, (p.1 - p.2.1) a * gradComp a h (p.2.1 + p.2.2 • (p.1 - p.2.1)) := by
    intro p
    unfold s105F
    rw [inner_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [real_inner_smul_right, real_inner_comm, hE]
  simp_rw [hinner]
  have hGint : Integrable (fun p : Euc d × (Euc d × ℝ) => inner ℝ E (s105F G0 p))
      (ν.prod (μρ.prod (volume.restrict (Set.Icc (0 : ℝ) 1)))) := hFint.const_inner E
  simp_rw [hinner] at hGint
  rw [integral_prod _ hGint]
  have hGx : ∀ x : Euc d, Integrable (fun q : Euc d × ℝ => ∑ a, (x - q.1) a *
      gradComp a h (q.1 + q.2 • (x - q.1))) (μρ.prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
    intro x
    have hm : Measurable fun q : Euc d × ℝ => s105F G0 (x, q) :=
      hFm.comp (measurable_const.prodMk measurable_id)
    have hI : Integrable (fun q : Euc d × ℝ => inner ℝ E (s105F G0 (x, q)))
        (μρ.prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
      refine Integrable.mono' (g := fun q : Euc d × ℝ => ‖E‖ * (d * Bf * (‖x‖ + ‖q.1‖))) ?_
        (measurable_const.inner hm).aestronglyMeasurable
        (Filter.Eventually.of_forall fun q => ?_)
      · exact (((integrable_const (‖x‖)).add (hμ.comp_fst (volume.restrict (Set.Icc (0 : ℝ) 1)))).const_mul
          (d * Bf)).const_mul ‖E‖
      · rw [Real.norm_eq_abs]
        refine (abs_real_inner_le_norm _ _).trans ?_
        exact mul_le_mul_of_nonneg_left (s105F_norm_le G0 Bf hBf hbd (x, q)) (norm_nonneg _)
    simpa only [hinner] using hI
  have step : ∀ x : Euc d, ∫ q : Euc d × ℝ, ∑ a, (x - q.1) a * gradComp a h (q.1 + q.2 • (x - q.1))
      ∂(μρ.prod (volume.restrict (Set.Icc (0 : ℝ) 1))) = h x - ∫ y, h y ∂μρ := by
    intro x
    rw [integral_prod _ (hGx x)]
    have : ∀ y : Euc d, ∫ θ, ∑ a, (x - y) a * gradComp a h (y + θ • (x - y))
        ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) = h x - h y := fun y => s56_line_ftc hh x y
    simp_rw [this]
    rw [integral_sub (integrable_const _) (hhint μρ inferInstance), integral_const]
    simp
  simp_rw [step]
  rw [integral_sub (hhint ν inferInstance) (integrable_const _), integral_const]
  simp

theorem s105_k0_emp {m T : ℝ} (G0 : Fin d → Euc d → KSpace d m T) (σ Bf : ℝ) (hBf : 0 ≤ Bf)
    (hmeas : ∀ a : Fin d, Measurable (G0 a)) (hbd : ∀ (a : Fin d) (z : Euc d), ‖G0 a z‖ ≤ Bf)
    {N : ℕ} (hN : 0 < N) (μρ : Measure (Euc d)) [IsProbabilityMeasure μρ]
    (hμ : Integrable (fun x : Euc d => ‖x‖) μρ) (x : EucConfig d N) :
    s105k0 G0 σ (HRS.Whole.empirical x) μρ = σ • ((N : ℝ)⁻¹ • ∑ i : Fin N,
      ∫ q : Euc d × ℝ, s105F G0 (x i, q) ∂(μρ.prod (volume.restrict (Set.Icc (0 : ℝ) 1)))) := by
  have : IsProbabilityMeasure (HRS.Whole.empirical x) := HRS.Whole.empirical_isProbabilityMeasure hN x
  have hν : Integrable (fun z : Euc d => ‖z‖) (HRS.Whole.empirical x) :=
    HRS.Whole.Q09A.integrable_empirical hN x _
  have hint := s105F_integrable G0 Bf hBf hmeas hbd (HRS.Whole.empirical x) μρ hν hμ
  unfold s105k0
  rw [integral_prod _ hint]
  congr 1
  unfold HRS.Whole.empirical
  rw [integral_smul_measure, integral_finsetSum_measure]
  · simp only [integral_dirac, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  · intro i _
    exact integrable_dirac (by simp)

theorem s105_k0_meas {m T : ℝ} (G0 : Fin d → Euc d → KSpace d m T) (σ Bf : ℝ) (hBf : 0 ≤ Bf)
    (hmeas : ∀ a : Fin d, Measurable (G0 a)) (hbd : ∀ (a : Fin d) (z : Euc d), ‖G0 a z‖ ≤ Bf)
    {N : ℕ} (hN : 0 < N) (μρ : Measure (Euc d)) [IsProbabilityMeasure μρ]
    (hμ : Integrable (fun x : Euc d => ‖x‖) μρ) :
    Measurable fun x : EucConfig d N => s105k0 G0 σ (HRS.Whole.empirical x) μρ := by
  have : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := ⟨by simp⟩
  simp_rw [s105_k0_emp G0 σ Bf hBf hmeas hbd hN μρ hμ]
  have hg : StronglyMeasurable fun z : Euc d => ∫ q : Euc d × ℝ, s105F G0 (z, q)
      ∂(μρ.prod (volume.restrict (Set.Icc (0 : ℝ) 1))) :=
    (s105F_meas G0 hmeas).stronglyMeasurable.integral_prod_right'
  have hsum : Measurable fun x : EucConfig d N => ∑ i : Fin N, ∫ q : Euc d × ℝ, s105F G0 (x i, q)
      ∂(μρ.prod (volume.restrict (Set.Icc (0 : ℝ) 1))) :=
    Finset.measurable_sum (Finset.univ : Finset (Fin N)) fun i _ => hg.measurable.comp (measurable_pi_apply i)
  exact (hsum.const_smul ((N : ℝ)⁻¹)).const_smul σ

end HRS.MS.R2GenInit
