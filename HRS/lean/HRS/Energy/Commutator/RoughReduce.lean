import Mathlib

/-!
# Reduction of a pair of finite measures to one measure with a bounded density (packet CM-S3 helper)

For finite measures `ν, μ` on `α` put `m = ν + μ`.  There is a measurable `a : α → [0,1]` with
`ν = a m`, `μ = (1-a) m`; with `s = 2a - 1` one has, for every symmetric kernel `K` integrable
against `m ⊗ m`,
`∬ K dν dν - 2 ∬ K dμ dν + ∬ K dμ dμ = ∬ s(x) s(y) K(x,y) dm dm`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator.RoughReduce

variable {α : Type*} [MeasurableSpace α]

theorem exists_density (ν μ : Measure α) [IsFiniteMeasure ν] [IsFiniteMeasure μ] :
    ∃ a : α → ℝ, Measurable a ∧ (∀ y, 0 ≤ a y ∧ a y ≤ 1) ∧
      (∀ g : α → ℝ, ∫ y, g y ∂ν = ∫ y, a y * g y ∂(ν + μ)) ∧
      (∀ g : α → ℝ, ∫ y, g y ∂μ = ∫ y, (1 - a y) * g y ∂(ν + μ)) := by
  set m : Measure α := ν + μ with hm
  have hνm : ν ≪ m := Measure.absolutelyContinuous_of_le (Measure.le_add_right le_rfl)
  have hμm : μ ≪ m := Measure.absolutelyContinuous_of_le (Measure.le_add_left le_rfl)
  set f := ν.rnDeriv m with hf
  set h := μ.rnDeriv m with hh
  have hfm : Measurable f := Measure.measurable_rnDeriv _ _
  have hhm : Measurable h := Measure.measurable_rnDeriv _ _
  have hflt : ∀ᵐ y ∂m, f y < ∞ := Measure.rnDeriv_lt_top _ _
  have hhlt : ∀ᵐ y ∂m, h y < ∞ := Measure.rnDeriv_lt_top _ _
  have hsum : ∀ᵐ y ∂m, f y + h y = 1 := by
    filter_upwards [Measure.rnDeriv_add ν μ m, Measure.rnDeriv_self m] with y h1 h2
    simp only [Pi.add_apply] at h1
    rw [← h1]
    exact h2
  set a : α → ℝ := fun y => max 0 (min 1 (f y).toReal) with ha
  have ha_ae : ∀ᵐ y ∂m, a y = (f y).toReal := by
    filter_upwards [hflt, hhlt, hsum] with y h1 h2 h3
    have h4 : (f y).toReal + (h y).toReal = 1 := by
      rw [← ENNReal.toReal_add h1.ne h2.ne, h3]; simp
    have h5 : 0 ≤ (h y).toReal := ENNReal.toReal_nonneg
    have h6 : 0 ≤ (f y).toReal := ENNReal.toReal_nonneg
    simp only [ha]
    rw [min_eq_right (by linarith), max_eq_right h6]
  have hb_ae : ∀ᵐ y ∂m, 1 - a y = (h y).toReal := by
    filter_upwards [hflt, hhlt, hsum, ha_ae] with y h1 h2 h3 h4
    have h5 : (f y).toReal + (h y).toReal = 1 := by
      rw [← ENNReal.toReal_add h1.ne h2.ne, h3]; simp
    rw [h4]; linarith
  refine ⟨a, ?_, fun y => ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩, ?_, ?_⟩
  · exact (measurable_const.max ((measurable_const.min hfm.ennreal_toReal)))
  · intro g
    conv_lhs => rw [← Measure.withDensity_rnDeriv_eq ν m hνm]
    rw [integral_withDensity_eq_integral_toReal_smul hfm hflt]
    refine integral_congr_ae ?_
    filter_upwards [ha_ae] with y hy
    simp [hy]
  · intro g
    conv_lhs => rw [← Measure.withDensity_rnDeriv_eq μ m hμm]
    rw [integral_withDensity_eq_integral_toReal_smul hhm hhlt]
    refine integral_congr_ae ?_
    filter_upwards [hb_ae] with y hy
    simp [← hy]

/-- Bilinear pairing of bounded densities against a kernel. -/
theorem integrable_phi {m : Measure α} [IsFiniteMeasure m] {K : α → α → ℝ}
    (hKm : Measurable (Function.uncurry K)) (hKi : Integrable (Function.uncurry K) (m.prod m))
    {f g : α → ℝ} (hfm : Measurable f) (hgm : Measurable g) (hf : ∀ y, |f y| ≤ 1) (hg : ∀ y, |g y| ≤ 1) :
    Integrable (fun p : α × α => f p.1 * g p.2 * K p.1 p.2) (m.prod m) := by
  have hmeas : Measurable fun p : α × α => f p.1 * g p.2 * K p.1 p.2 :=
    ((hfm.comp measurable_fst).mul (hgm.comp measurable_snd)).mul hKm
  refine Integrable.mono' hKi.norm hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
  simp only [Real.norm_eq_abs, abs_mul, Function.uncurry]
  have h1 := hf p.1
  have h2 := hg p.2
  calc |f p.1| * |g p.2| * |K p.1 p.2| ≤ 1 * 1 * |K p.1 p.2| := by gcongr
    _ = _ := by ring

theorem reduce {ν μ : Measure α} [IsFiniteMeasure ν] [IsFiniteMeasure μ] :
    ∃ s : α → ℝ, Measurable s ∧ (∀ y, |s y| ≤ 1) ∧
      ∫ y, s y ∂(ν + μ) = ν.real Set.univ - μ.real Set.univ ∧
      ∀ K : α → α → ℝ, Measurable (Function.uncurry K) → (∀ x y, K x y = K y x) →
        Integrable (Function.uncurry K) ((ν + μ).prod (ν + μ)) →
        (∫ x, ∫ y, K x y ∂ν ∂ν) - 2 * (∫ x, ∫ y, K x y ∂μ ∂ν) + (∫ x, ∫ y, K x y ∂μ ∂μ) =
          ∫ p : α × α, s p.1 * s p.2 * K p.1 p.2 ∂((ν + μ).prod (ν + μ)) := by
  obtain ⟨a, ham, ha01, hνa, hμa⟩ := exists_density ν μ
  set m : Measure α := ν + μ with hm
  refine ⟨fun y => a y - (1 - a y), ham.sub (measurable_const.sub ham), fun y => ?_, ?_, ?_⟩
  · have := ha01 y
    rw [abs_le]; constructor <;> linarith [this.1, this.2]
  · have h1 : ν.real Set.univ = ∫ y, a y ∂m := by
      have := hνa (fun _ => (1 : ℝ))
      simpa [Measure.real] using this
    have h2 : μ.real Set.univ = ∫ y, (1 - a y) ∂m := by
      have := hμa (fun _ => (1 : ℝ))
      simpa [Measure.real] using this
    have hai : Integrable a m := by
      refine Integrable.mono' (integrable_const (1 : ℝ)) ham.aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (ha01 y).1]; exact (ha01 y).2
    rw [h1, h2, integral_sub hai (by exact (integrable_const (1 : ℝ)).sub hai), integral_sub (integrable_const _) hai]
  · intro K hKm hKs hKi
    set b : α → ℝ := fun y => 1 - a y with hb
    have hbm : Measurable b := measurable_const.sub ham
    have ha1 : ∀ y, |a y| ≤ 1 := fun y => by rw [abs_of_nonneg (ha01 y).1]; exact (ha01 y).2
    have hb1 : ∀ y, |b y| ≤ 1 := fun y => by
      simp only [hb]; rw [abs_of_nonneg (by linarith [(ha01 y).2])]; linarith [(ha01 y).1]
    have hI := fun (f g : α → ℝ) (hf : Measurable f) (hg : Measurable g) (h1 : ∀ y, |f y| ≤ 1)
      (h2 : ∀ y, |g y| ≤ 1) => integrable_phi hKm hKi hf hg h1 h2
    -- iterated form of the pairing
    have hiter : ∀ (f g : α → ℝ), Measurable f → Measurable g → (∀ y, |f y| ≤ 1) → (∀ y, |g y| ≤ 1) →
        ∫ x, f x * (∫ y, g y * K x y ∂m) ∂m = ∫ p : α × α, f p.1 * g p.2 * K p.1 p.2 ∂(m.prod m) := by
      intro f g hf hg h1 h2
      rw [integral_prod _ (hI f g hf hg h1 h2)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only []
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)
    have T11 : ∫ x, ∫ y, K x y ∂ν ∂ν = ∫ x, a x * (∫ y, a y * K x y ∂m) ∂m := by
      have e : ∀ x, ∫ y, K x y ∂ν = ∫ y, a y * K x y ∂m := fun x => hνa _
      simp_rw [e]
      exact hνa (fun x => ∫ y, a y * K x y ∂m)
    have T12 : ∫ x, ∫ y, K x y ∂μ ∂ν = ∫ x, a x * (∫ y, b y * K x y ∂m) ∂m := by
      have e : ∀ x, ∫ y, K x y ∂μ = ∫ y, b y * K x y ∂m := fun x => hμa _
      simp_rw [e]
      exact hνa (fun x => ∫ y, b y * K x y ∂m)
    have T22 : ∫ x, ∫ y, K x y ∂μ ∂μ = ∫ x, b x * (∫ y, b y * K x y ∂m) ∂m := by
      have e : ∀ x, ∫ y, K x y ∂μ = ∫ y, b y * K x y ∂m := fun x => hμa _
      simp_rw [e]
      exact hμa (fun x => ∫ y, b y * K x y ∂m)
    rw [T11, T12, T22, hiter a a ham ham ha1 ha1, hiter a b ham hbm ha1 hb1, hiter b b hbm hbm hb1 hb1]
    -- symmetry of the pairing
    have hsym : ∫ p : α × α, b p.1 * a p.2 * K p.1 p.2 ∂(m.prod m) =
        ∫ p : α × α, a p.1 * b p.2 * K p.1 p.2 ∂(m.prod m) := by
      rw [← integral_prod_swap (fun p : α × α => a p.1 * b p.2 * K p.1 p.2)]
      exact integral_congr_ae (Filter.Eventually.of_forall fun p => by
        simp only [Prod.fst_swap, Prod.snd_swap]
        rw [hKs p.2 p.1]; ring)
    have hex : ∀ p : α × α, (a p.1 - b p.1) * (a p.2 - b p.2) * K p.1 p.2 =
        a p.1 * a p.2 * K p.1 p.2 - a p.1 * b p.2 * K p.1 p.2 - b p.1 * a p.2 * K p.1 p.2 +
          b p.1 * b p.2 * K p.1 p.2 := fun p => by ring
    have hI1 := hI a a ham ham ha1 ha1
    have hI2 := hI a b ham hbm ha1 hb1
    have hI3 := hI b a hbm ham hb1 ha1
    have hI4 := hI b b hbm hbm hb1 hb1
    set F1 : α × α → ℝ := fun p => a p.1 * a p.2 * K p.1 p.2 with hF1
    set F2 : α × α → ℝ := fun p => a p.1 * b p.2 * K p.1 p.2 with hF2
    set F3 : α × α → ℝ := fun p => b p.1 * a p.2 * K p.1 p.2 with hF3
    set F4 : α × α → ℝ := fun p => b p.1 * b p.2 * K p.1 p.2 with hF4
    have hs : ∫ p : α × α, (a p.1 - (1 - a p.1)) * (a p.2 - (1 - a p.2)) * K p.1 p.2 ∂(m.prod m) =
        ∫ p, F1 p ∂(m.prod m) - ∫ p, F2 p ∂(m.prod m) - ∫ p, F3 p ∂(m.prod m) + ∫ p, F4 p ∂(m.prod m) := by
      have e : (fun p : α × α => (a p.1 - (1 - a p.1)) * (a p.2 - (1 - a p.2)) * K p.1 p.2) =
          F1 - F2 - F3 + F4 := by
        funext p; simp only [hF1, hF2, hF3, hF4, hb, Pi.add_apply, Pi.sub_apply]; ring
      rw [e, integral_add' ((hI1.sub hI2).sub hI3) hI4, integral_sub' (hI1.sub hI2) hI3, integral_sub' hI1 hI2]
    rw [hs, hsym]
    ring

end HRS.Commutator.RoughReduce
