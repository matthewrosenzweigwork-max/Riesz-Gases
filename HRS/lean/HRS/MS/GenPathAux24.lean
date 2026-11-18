import HRS.MS.GenPathAux23

/-!
# S5.6 packet P7b: the initial `𝒦`-state `k₀` of the particle path

`s56k0 C m T σ ν μρ = σ ∫∫∫_0^1 ∑_a (x-y)_a Γ_{0,a}(y + θ(x-y)) dθ dμρ(y) dν(x)`: its pairing with a vector `E`
whose pairings with the gradient features are `∂_a h` is `σ(ν(h) - μρ(h))` (line integral; no value-Duhamel identity needed).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.GenPath

open HRS HRS.Whole HRS.MP.RdRem

variable {d : ℕ}

/-- The integrand of `k₀`. -/
def s56F (C : WholeCoeff d) (m T : ℝ) (p : Euc d × (Euc d × ℝ)) : KSpace d m T :=
  ∑ a : Fin d, (p.1 - p.2.1) a • gradFeature C m T a 0 (p.2.1 + p.2.2 • (p.1 - p.2.1))

def s56k0 (C : WholeCoeff d) (m T σ : ℝ) (ν μρ : Measure (Euc d)) : KSpace d m T :=
  σ • ∫ p, s56F C m T p ∂(ν.prod (μρ.prod (volume.restrict (Set.Icc (0 : ℝ) 1))))

theorem s56F_meas (C : WholeCoeff d) (m T : ℝ)
    (hmeas : ∀ a : Fin d, Measurable fun z : Euc d => gradFeature C m T a 0 z) :
    Measurable (s56F C m T) := by
  unfold s56F
  refine Finset.measurable_sum _ fun a _ => ?_
  have h1 : Measurable fun p : Euc d × (Euc d × ℝ) => (p.1 - p.2.1) a :=
    ((EuclideanSpace.proj a : Euc d →L[ℝ] ℝ).continuous.measurable.comp (measurable_fst.sub (measurable_fst.comp measurable_snd)))
  have h2 : Measurable fun p : Euc d × (Euc d × ℝ) => gradFeature C m T a 0 (p.2.1 + p.2.2 • (p.1 - p.2.1)) :=
    (hmeas a).comp ((measurable_fst.comp measurable_snd).add
      ((measurable_snd.comp measurable_snd).smul (measurable_fst.sub (measurable_fst.comp measurable_snd))))
  exact h1.smul h2

theorem s56F_norm_le (C : WholeCoeff d) (m T Bf : ℝ) (hBf : 0 ≤ Bf)
    (hbd : ∀ (a : Fin d) (z : Euc d), ‖gradFeature C m T a 0 z‖ ≤ Bf) (p : Euc d × (Euc d × ℝ)) :
    ‖s56F C m T p‖ ≤ d * Bf * (‖p.1‖ + ‖p.2.1‖) := by
  unfold s56F
  refine (norm_sum_le _ _).trans ?_
  have : ∀ a : Fin d, ‖(p.1 - p.2.1) a • gradFeature C m T a 0 (p.2.1 + p.2.2 • (p.1 - p.2.1))‖ ≤
      Bf * (‖p.1‖ + ‖p.2.1‖) := by
    intro a
    rw [norm_smul, mul_comm]
    refine mul_le_mul (hbd _ _) ?_ (norm_nonneg _) hBf
    calc ‖(p.1 - p.2.1) a‖ ≤ ‖p.1 - p.2.1‖ := PiLp.norm_apply_le _ a
      _ ≤ ‖p.1‖ + ‖p.2.1‖ := norm_sub_le _ _
  calc ∑ a : Fin d, ‖(p.1 - p.2.1) a • gradFeature C m T a 0 (p.2.1 + p.2.2 • (p.1 - p.2.1))‖
      ≤ ∑ _a : Fin d, Bf * (‖p.1‖ + ‖p.2.1‖) := Finset.sum_le_sum fun a _ => this a
    _ = _ := by simp [Finset.sum_const]; ring

theorem s56_k0_inner (C : WholeCoeff d) (m T σ Bf : ℝ) (hBf : 0 ≤ Bf)
    (hmeas : ∀ a : Fin d, Measurable fun z : Euc d => gradFeature C m T a 0 z)
    (hbd : ∀ (a : Fin d) (z : Euc d), ‖gradFeature C m T a 0 z‖ ≤ Bf)
    (ν μρ : Measure (Euc d)) [IsProbabilityMeasure ν] [IsProbabilityMeasure μρ]
    (hν : Integrable (fun x : Euc d => ‖x‖) ν) (hμ : Integrable (fun x : Euc d => ‖x‖) μρ)
    (E : KSpace d m T) (h : Euc d → ℝ) (hh : ContDiff ℝ 1 h) (B : ℝ) (hB : ∀ z, |h z| ≤ B)
    (hE : ∀ (a : Fin d) (z : Euc d), inner ℝ (gradFeature C m T a 0 z) E = gradComp a h z) :
    inner ℝ (s56k0 C m T σ ν μρ) E = σ * (∫ x, h x ∂ν - ∫ x, h x ∂μρ) := by
  haveI : IsProbabilityMeasure (volume.restrict (Set.Icc (0 : ℝ) 1)) := ⟨by simp⟩
  have hFm := s56F_meas C m T hmeas
  have hFint : Integrable (s56F C m T) (ν.prod (μρ.prod (volume.restrict (Set.Icc (0 : ℝ) 1)))) := by
    refine Integrable.mono' (g := fun p => d * Bf * (‖p.1‖ + ‖p.2.1‖)) ?_ hFm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => s56F_norm_le C m T Bf hBf hbd p)
    refine Integrable.const_mul ?_ _
    refine Integrable.add ?_ ?_
    · exact (hν.comp_fst (μρ.prod (volume.restrict (Set.Icc (0 : ℝ) 1)))) 
    · exact ((hμ.comp_fst (volume.restrict (Set.Icc (0 : ℝ) 1))).comp_snd ν)
  have hhm : Continuous h := hh.continuous
  have hhint : ∀ μ : Measure (Euc d), IsProbabilityMeasure μ → Integrable h μ := fun μ _ =>
    Integrable.of_bound hhm.aestronglyMeasurable B (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]; exact hB z)
  unfold s56k0
  rw [inner_smul_left, real_inner_comm, ← integral_inner hFint, conj_trivial]
  congr 1
  have hinner : ∀ p : Euc d × (Euc d × ℝ), inner ℝ E (s56F C m T p) =
      ∑ a, (p.1 - p.2.1) a * gradComp a h (p.2.1 + p.2.2 • (p.1 - p.2.1)) := by
    intro p
    unfold s56F
    rw [inner_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [real_inner_smul_right, real_inner_comm, hE]
  simp_rw [hinner]
  have hGint : Integrable (fun p : Euc d × (Euc d × ℝ) => inner ℝ E (s56F C m T p)) (ν.prod (μρ.prod (volume.restrict (Set.Icc (0 : ℝ) 1)))) :=
    hFint.const_inner E
  simp_rw [hinner] at hGint
  rw [integral_prod _ hGint]
  have hGx : ∀ x : Euc d, Integrable (fun q : Euc d × ℝ => ∑ a, (x - q.1) a *
      gradComp a h (q.1 + q.2 • (x - q.1))) (μρ.prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
    intro x
    have hm : Measurable fun q : Euc d × ℝ => s56F C m T (x, q) :=
      hFm.comp (measurable_const.prodMk measurable_id)
    have hI : Integrable (fun q : Euc d × ℝ => inner ℝ E (s56F C m T (x, q)))
        (μρ.prod (volume.restrict (Set.Icc (0 : ℝ) 1))) := by
      refine Integrable.mono' (g := fun q : Euc d × ℝ => ‖E‖ * (d * Bf * (‖x‖ + ‖q.1‖))) ?_
        (measurable_const.inner hm).aestronglyMeasurable
        (Filter.Eventually.of_forall fun q => ?_)
      · exact (((integrable_const (‖x‖)).add (hμ.comp_fst (volume.restrict (Set.Icc (0 : ℝ) 1)))).const_mul
          (d * Bf)).const_mul ‖E‖
      · rw [Real.norm_eq_abs]
        refine (abs_real_inner_le_norm _ _).trans ?_
        exact mul_le_mul_of_nonneg_left (s56F_norm_le C m T Bf hBf hbd (x, q)) (norm_nonneg _)
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

end HRS.MS.GenPath
