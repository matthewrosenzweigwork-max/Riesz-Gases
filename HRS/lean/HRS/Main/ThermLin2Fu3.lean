import HRS.Main.ThermLin2Fu2

/-!
# THERMLIN2 Fu3: generic `L²` lemmas for the time integral `B(ω) = ∫_0^t F(r,ω) dr` (helpers for B4)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ThermLin.Plan2

/-- Cauchy-Schwarz in the form `(∫ f)² ≤ μ(univ) ∫ f²`. -/
theorem tl2fu_sq_integral_le {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, f x ∂μ) ^ 2 ≤ μ.real Set.univ * ∫ x, f x ^ 2 ∂μ := by
  have hf1 : Integrable f μ := hf.integrable one_le_two
  have hf2 : Integrable (fun x => f x ^ 2) μ := hf.integrable_sq
  by_cases h0 : μ = 0
  · subst h0; simp
  have hM : 0 < μ.real Set.univ := by
    have : μ Set.univ ≠ 0 := fun h => h0 (Measure.measure_univ_eq_zero.1 h)
    exact ENNReal.toReal_pos this (measure_ne_top _ _)
  set M := μ.real Set.univ with hMdef
  set I := ∫ x, f x ∂μ with hI
  set c : ℝ := I / M with hc
  have h1 : 0 ≤ ∫ x, (f x - c) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have e : ∫ x, (f x - c) ^ 2 ∂μ = (∫ x, f x ^ 2 ∂μ) - 2 * c * I + c ^ 2 * M := by
    have : (fun x => (f x - c) ^ 2) = fun x => (f x ^ 2 - 2 * c * f x) + c ^ 2 := by
      funext x; ring
    have hA : Integrable (fun x => f x ^ 2 - 2 * c * f x) μ := hf2.sub (hf1.const_mul _)
    rw [this, integral_add hA (integrable_const _),
      integral_sub (f := fun x => f x ^ 2) (g := fun x => 2 * c * f x) hf2 (hf1.const_mul _),
      integral_const_mul, integral_const]
    simp [hMdef, mul_comm]
    exact Or.inl rfl
  rw [e] at h1
  have : c * M = I := by rw [hc]; field_simp
  have h2 : c ^ 2 * M = c * I := by rw [← this]; ring
  nlinarith [this, h2]

section Bp

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- `Fp²` is integrable on `[0,t] × Ω` when its slices are in `L²` with a uniform bound. -/
theorem tl2fu_Fp_sq_integrable {t : ℝ} (Fp : ℝ → Ω → ℝ) (hFp : Measurable fun q : ℝ × Ω => Fp q.1 q.2)
    (M : ℝ) (hL2 : ∀ r ∈ Set.Icc (0 : ℝ) t, MemLp (Fp r) 2 P)
    (hM : ∀ r ∈ Set.Icc (0 : ℝ) t, ∫ ω, Fp r ω ^ 2 ∂P ≤ M) :
    Integrable (fun q : ℝ × Ω => Fp q.1 q.2 ^ 2) ((volume.restrict (Set.Icc 0 t)).prod P) := by
  have h1f : AEStronglyMeasurable (fun q : ℝ × Ω => Fp q.1 q.2 ^ 2)
      ((volume.restrict (Set.Icc 0 t)).prod P) := (hFp.pow_const 2).aestronglyMeasurable
  refine (integrable_prod_iff h1f).2 ⟨?_, ?_⟩
  · exact (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun r hr => (hL2 r hr).integrable_sq)
  · refine Integrable.mono' (integrable_const M) (h1f.norm.integral_prod_right') ?_
    refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun r hr => ?_)
    have : ∫ ω, ‖Fp r ω ^ 2‖ ∂P = ∫ ω, Fp r ω ^ 2 ∂P := by
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only [Real.norm_eq_abs]; exact abs_of_nonneg (sq_nonneg _)
    rw [Real.norm_eq_abs, this, abs_of_nonneg (integral_nonneg fun ω => sq_nonneg _)]
    exact hM r hr

theorem tl2fu_Bp_pair {t : ℝ} (Fp : ℝ → Ω → ℝ) (hFp : Measurable fun q : ℝ × Ω => Fp q.1 q.2)
    (hsq : Integrable (fun q : ℝ × Ω => Fp q.1 q.2 ^ 2) ((volume.restrict (Set.Icc 0 t)).prod P))
    (u : Ω → ℝ) (hu : MemLp u 2 P) (hum : Measurable u) :
    ∫ ω, (∫ r in Set.Icc 0 t, Fp r ω) * u ω ∂P = ∫ r in Set.Icc 0 t, ∫ ω, Fp r ω * u ω ∂P := by
  have hint : Integrable (Function.uncurry fun r ω => Fp r ω * u ω)
      ((volume.restrict (Set.Icc 0 t)).prod P) := by
    have hb : Integrable (fun q : ℝ × Ω => Fp q.1 q.2 ^ 2 + (1 : ℝ) * u q.2 ^ 2)
        ((volume.restrict (Set.Icc 0 t)).prod P) :=
      hsq.add ((integrable_const (1 : ℝ)).mul_prod hu.integrable_sq)
    refine hb.mono' ((hFp.mul (hum.comp measurable_snd)).aestronglyMeasurable) ?_
    refine Eventually.of_forall fun q => ?_
    simp only [Function.uncurry, Real.norm_eq_abs, one_mul, abs_mul]
    nlinarith [sq_nonneg (|Fp q.1 q.2| - |u q.2|), sq_abs (Fp q.1 q.2), sq_abs (u q.2), abs_nonneg (Fp q.1 q.2),
      abs_nonneg (u q.2)]
  have := integral_integral_swap hint
  rw [this]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  simp only []
  rw [integral_mul_const]

theorem tl2fu_Bp_memLp {t : ℝ} (Fp : ℝ → Ω → ℝ) (hFp : Measurable fun q : ℝ × Ω => Fp q.1 q.2)
    (hsq : Integrable (fun q : ℝ × Ω => Fp q.1 q.2 ^ 2) ((volume.restrict (Set.Icc 0 t)).prod P)) :
    MemLp (fun ω => ∫ r in Set.Icc 0 t, Fp r ω) 2 P := by
  have hmeas : Measurable (fun ω => ∫ r in Set.Icc 0 t, Fp r ω) :=
    (hFp.stronglyMeasurable.integral_prod_left' (μ := volume.restrict (Set.Icc 0 t))).measurable
  refine (memLp_two_iff_integrable_sq hmeas.aestronglyMeasurable).2 ?_
  have hg : Integrable (fun ω => (volume.restrict (Set.Icc (0 : ℝ) t)).real Set.univ *
      ∫ r, Fp r ω ^ 2 ∂(volume.restrict (Set.Icc 0 t))) P :=
    (hsq.integral_prod_right).const_mul _
  refine hg.mono' (hmeas.pow_const 2).aestronglyMeasurable ?_
  filter_upwards [hsq.prod_left_ae] with ω hω
  have hm : AEStronglyMeasurable (fun r => Fp r ω) (volume.restrict (Set.Icc 0 t)) :=
    (hFp.comp measurable_prodMk_right).aestronglyMeasurable
  have hL : MemLp (fun r => Fp r ω) 2 (volume.restrict (Set.Icc (0 : ℝ) t)) :=
    (memLp_two_iff_integrable_sq hm).2 hω
  have := tl2fu_sq_integral_le hL
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact this

end Bp

end HRS.ThermLin.Plan2
