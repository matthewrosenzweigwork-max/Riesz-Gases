import HRS.Main.A34Aux22

/-!
# Packet A34, helper 23: convergence in law from couplings / of convolutions
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory
open scoped ENNReal NNReal BigOperators ComplexConjugate RealInnerProductSpace BoundedContinuousFunction

namespace HRS.A34

open HRS HRS.Main

section Conv

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- If `μ N` can be coupled with the fixed law `μ₀` at `L¹`-distance `ε N → 0`, then `μ N → μ₀`. -/
theorem a34_converges_of_coupling (μ : ℕ → Measure E) (μ₀ : Measure E) [IsProbabilityMeasure μ₀]
    (hμ : ∀ N, 1 ≤ N → IsProbabilityMeasure (μ N)) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hcoup : ∀ N, 1 ≤ N → ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (_ : IsProbabilityMeasure P) (X Y : Ω → E), Measurable X ∧ Measurable Y ∧
        P.map X = μ N ∧ P.map Y = μ₀ ∧ Integrable (fun ω => ‖X ω - Y ω‖) P ∧
        ∫ ω, ‖X ω - Y ω‖ ∂P ≤ ε N) :
    ConvergesInLaw μ μ₀ := by
  let ν : ℕ → ProbabilityMeasure E := fun n => ⟨μ (n + 1), hμ (n + 1) (by omega)⟩
  let ν₀ : ProbabilityMeasure E := ⟨μ₀, inferInstance⟩
  have hlim : Tendsto ν atTop (𝓝 ν₀) := by
    rw [tendsto_iff_forall_lipschitz_integral_tendsto]
    intro f ⟨C, hC⟩ ⟨L, hL⟩
    have hfc : Continuous f := hL.continuous
    have hfm : Measurable f := hfc.measurable
    have hbd : ∀ x, |f x| ≤ |f 0| + C := fun x => by
      have := hC x 0
      rw [Real.dist_eq] at this
      have h2 : |f x| ≤ |f x - f 0| + |f 0| := by
        have := abs_sub_abs_le_abs_sub (f x) (f 0)
        linarith
      linarith
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      (g := fun n => L * ε (n + 1)) ?_
    · obtain ⟨Ω, mΩ, P, hP, X, Y, hX, hY, hmX, hmY, hint, hε'⟩ := hcoup (n + 1) (by omega)
      haveI := hP
      have e1 : ∫ x, f x ∂(ν n : Measure E) = ∫ ω, f (X ω) ∂P := by
        show ∫ x, f x ∂(μ (n + 1)) = _
        rw [← hmX]; exact integral_map hX.aemeasurable hfc.aestronglyMeasurable
      have e2 : ∫ x, f x ∂(ν₀ : Measure E) = ∫ ω, f (Y ω) ∂P := by
        show ∫ x, f x ∂μ₀ = _
        rw [← hmY]; exact integral_map hY.aemeasurable hfc.aestronglyMeasurable
      have hi : ∀ Z : Ω → E, Measurable Z → Integrable (fun ω => f (Z ω)) P := fun Z hZ =>
        Integrable.of_bound (hfm.comp hZ).aestronglyMeasurable (|f 0| + C)
          (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hbd (Z ω))
      rw [e1, e2, ← integral_sub (hi X hX) (hi Y hY), Real.norm_eq_abs]
      calc |∫ ω, (f (X ω) - f (Y ω)) ∂P| ≤ ∫ ω, |f (X ω) - f (Y ω)| ∂P := by
            simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := P)
              (fun ω => f (X ω) - f (Y ω))
        _ ≤ ∫ ω, L * ‖X ω - Y ω‖ ∂P := by
            refine integral_mono ((hi X hX).sub (hi Y hY)).abs (hint.const_mul _) fun ω => ?_
            have := hL.dist_le_mul (X ω) (Y ω)
            rw [Real.dist_eq, dist_eq_norm] at this
            exact this
        _ = L * ∫ ω, ‖X ω - Y ω‖ ∂P := integral_const_mul _ _
        _ ≤ L * ε (n + 1) := mul_le_mul_of_nonneg_left hε' L.coe_nonneg
    · have := ((tendsto_add_atTop_iff_nat 1).2 hε).const_mul (L : ℝ)
      simpa using this
  intro f
  have := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hlim f
  have h2 : Tendsto (fun n : ℕ => ∫ x, f x ∂(μ (n + 1))) atTop (𝓝 (∫ x, f x ∂μ₀)) := this
  exact (tendsto_add_atTop_iff_nat (f := fun n => ∫ x, f x ∂(μ n)) 1).1 h2

variable [SecondCountableTopology E]

theorem a34_int_conv_bdd (μ ν : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : E → ℝ} (hfc : Continuous f) {M : ℝ} (hM : ∀ x, |f x| ≤ M) :
    ∫ z, f z ∂(μ ∗ ν) = ∫ x, ∫ y, f (x + y) ∂ν ∂μ := by
  have hconv : μ ∗ ν = (μ.prod ν).map (fun p => p.1 + p.2) := rfl
  have hm : Measurable (fun p : E × E => p.1 + p.2) := measurable_fst.add measurable_snd
  rw [hconv, integral_map hm.aemeasurable hfc.aestronglyMeasurable]
  have hint : Integrable (fun p : E × E => f (p.1 + p.2)) (μ.prod ν) :=
    Integrable.of_bound (hfc.measurable.comp hm).aestronglyMeasurable M
      (ae_of_all _ fun p => by simpa using hM (p.1 + p.2))
  rw [integral_prod _ hint]

theorem a34_g_lip (ν : Measure E) [IsProbabilityMeasure ν] {f : E → ℝ} {C : ℝ} {L : ℝ≥0}
    (hC : ∀ x y, dist (f x) (f y) ≤ C) (hL : LipschitzWith L f) :
    LipschitzWith L (fun x => ∫ y, f (x + y) ∂ν) ∧ ∀ x, |∫ y, f (x + y) ∂ν| ≤ |f 0| + C := by
  have hfc : Continuous f := hL.continuous
  have hbd : ∀ x, |f x| ≤ |f 0| + C := fun x => by
    have := hC x 0
    rw [Real.dist_eq] at this
    have h2 : |f x| ≤ |f x - f 0| + |f 0| := by
      have := abs_sub_abs_le_abs_sub (f x) (f 0)
      linarith
    linarith
  have hi : ∀ z : E, Integrable (fun y => f (z + y)) ν := fun z =>
    Integrable.of_bound (hfc.measurable.comp (measurable_const.add measurable_id)).aestronglyMeasurable
      (|f 0| + C) (ae_of_all _ fun y => by simpa [Real.norm_eq_abs] using hbd (z + y))
  refine ⟨LipschitzWith.of_dist_le_mul fun x x' => ?_, fun x => ?_⟩
  · simp only [Real.dist_eq, dist_eq_norm]
    rw [← integral_sub (hi x) (hi x')]
    calc |∫ y, (f (x + y) - f (x' + y)) ∂ν| ≤ ∫ y, |f (x + y) - f (x' + y)| ∂ν := by
          simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := ν)
            (fun y => f (x + y) - f (x' + y))
      _ ≤ ∫ y, (L : ℝ) * ‖x - x'‖ ∂ν := by
          refine integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _) (integrable_const _)
            (ae_of_all _ fun y => ?_)
          have := hL.dist_le_mul (x + y) (x' + y)
          rw [Real.dist_eq, dist_eq_norm] at this
          simpa [add_sub_add_right_eq_sub] using this
      _ = (L : ℝ) * ‖x - x'‖ := by simp
  · calc |∫ y, f (x + y) ∂ν| ≤ ∫ y, |f (x + y)| ∂ν := by
          simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := ν) (fun y => f (x + y))
      _ ≤ ∫ y, (|f 0| + C) ∂ν := integral_mono_of_nonneg (ae_of_all _ fun _ => abs_nonneg _)
          (integrable_const _) (ae_of_all _ fun y => hbd _)
      _ = |f 0| + C := by simp

theorem a34_converges_conv (μ : ℕ → Measure E) (μ₀ : Measure E) (ν : ℕ → Measure E) (ν₀ : Measure E)
    [IsProbabilityMeasure μ₀] [IsProbabilityMeasure ν₀]
    (hμ : ∀ N, 1 ≤ N → IsProbabilityMeasure (μ N)) (hν : ∀ N, 1 ≤ N → IsProbabilityMeasure (ν N))
    (hμc : ConvergesInLaw μ μ₀) (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hcoup : ∀ N, 1 ≤ N → ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (_ : IsProbabilityMeasure P) (X Y : Ω → E), Measurable X ∧ Measurable Y ∧
        P.map X = ν N ∧ P.map Y = ν₀ ∧ Integrable (fun ω => ‖X ω - Y ω‖) P ∧
        ∫ ω, ‖X ω - Y ω‖ ∂P ≤ ε N) :
    ConvergesInLaw (fun N => μ N ∗ ν N) (μ₀ ∗ ν₀) := by
  have hκ : ∀ N, 1 ≤ N → IsProbabilityMeasure (μ N ∗ ν N) := fun N hN => by
    haveI := hμ N hN; haveI := hν N hN; infer_instance
  let κ : ℕ → ProbabilityMeasure E := fun n => ⟨μ (n + 1) ∗ ν (n + 1), hκ (n + 1) (by omega)⟩
  let κ₀ : ProbabilityMeasure E := ⟨μ₀ ∗ ν₀, inferInstance⟩
  have hlim : Tendsto κ atTop (𝓝 κ₀) := by
    rw [tendsto_iff_forall_lipschitz_integral_tendsto]
    intro f ⟨C, hC⟩ ⟨L, hL⟩
    have hfc : Continuous f := hL.continuous
    have hbd : ∀ x, |f x| ≤ |f 0| + C := fun x => by
      have := hC x 0
      rw [Real.dist_eq] at this
      have h2 : |f x| ≤ |f x - f 0| + |f 0| := by
        have := abs_sub_abs_le_abs_sub (f x) (f 0)
        linarith
      linarith
    obtain ⟨hgl, hgb⟩ := a34_g_lip ν₀ hC hL
    set g : E → ℝ := fun x => ∫ y, f (x + y) ∂ν₀ with hg
    let gb : E →ᵇ ℝ := BoundedContinuousFunction.mkOfBound ⟨g, hgl.continuous⟩ (2 * (|f 0| + C))
      (fun x y => by
        rw [Real.dist_eq]
        have h1 := hgb x
        have h2 := hgb y
        show |g x - g y| ≤ _
        calc |g x - g y| ≤ |g x| + |g y| := abs_sub _ _
          _ ≤ _ := by linarith)
    have hμg := hμc gb
    have hgm : Measurable g := hgl.continuous.measurable
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
      (g := fun n => L * ε (n + 1) + |∫ x, g x ∂(μ (n + 1)) - ∫ x, g x ∂μ₀|) ?_
    · haveI := hμ (n + 1) (by omega)
      haveI := hν (n + 1) (by omega)
      obtain ⟨Ω, mΩ, P, hP, X, Y, hX, hY, hmX, hmY, hint, hε'⟩ := hcoup (n + 1) (by omega)
      haveI := hP
      set A : E → ℝ := fun x => ∫ y, f (x + y) ∂(ν (n + 1)) with hA
      obtain ⟨hAl, hAb⟩ := a34_g_lip (ν (n + 1)) hC hL
      have e1 : ∫ z, f z ∂(κ n : Measure E) = ∫ x, A x ∂(μ (n + 1)) :=
        a34_int_conv_bdd (μ (n + 1)) (ν (n + 1)) hfc hbd
      have e2 : ∫ z, f z ∂(κ₀ : Measure E) = ∫ x, g x ∂μ₀ :=
        a34_int_conv_bdd μ₀ ν₀ hfc hbd
      have hxA : ∀ x, |A x - g x| ≤ L * ε (n + 1) := by
        intro x
        have hi : ∀ Z : Ω → E, Measurable Z → Integrable (fun ω => f (x + Z ω)) P := fun Z hZ =>
          Integrable.of_bound (hfc.measurable.comp (measurable_const.add hZ)).aestronglyMeasurable
            (|f 0| + C) (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hbd (x + Z ω))
        have a1 : A x = ∫ ω, f (x + X ω) ∂P := by
          simp only [hA]; rw [← hmX]
          exact integral_map hX.aemeasurable (hfc.comp (continuous_const.add continuous_id)).aestronglyMeasurable
        have a2 : g x = ∫ ω, f (x + Y ω) ∂P := by
          simp only [hg]; rw [← hmY]
          exact integral_map hY.aemeasurable (hfc.comp (continuous_const.add continuous_id)).aestronglyMeasurable
        rw [a1, a2, ← integral_sub (hi X hX) (hi Y hY)]
        calc |∫ ω, (f (x + X ω) - f (x + Y ω)) ∂P| ≤ ∫ ω, |f (x + X ω) - f (x + Y ω)| ∂P := by
              simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := P)
                (fun ω => f (x + X ω) - f (x + Y ω))
          _ ≤ ∫ ω, (L : ℝ) * ‖X ω - Y ω‖ ∂P := by
              refine integral_mono ((hi X hX).sub (hi Y hY)).abs (hint.const_mul _) fun ω => ?_
              have := hL.dist_le_mul (x + X ω) (x + Y ω)
              rw [Real.dist_eq, dist_eq_norm] at this
              simpa [add_sub_add_left_eq_sub] using this
          _ = L * ∫ ω, ‖X ω - Y ω‖ ∂P := integral_const_mul _ _
          _ ≤ L * ε (n + 1) := mul_le_mul_of_nonneg_left hε' L.coe_nonneg
      have hAi : Integrable A (μ (n + 1)) :=
        Integrable.of_bound hAl.continuous.measurable.aestronglyMeasurable (|f 0| + C)
          (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hAb x)
      have hgi : Integrable g (μ (n + 1)) :=
        Integrable.of_bound hgm.aestronglyMeasurable (|f 0| + C)
          (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hgb x)
      have hdiff : |∫ x, A x ∂(μ (n + 1)) - ∫ x, g x ∂(μ (n + 1))| ≤ L * ε (n + 1) := by
        rw [← integral_sub hAi hgi]
        calc |∫ x, (A x - g x) ∂(μ (n + 1))| ≤ ∫ x, |A x - g x| ∂(μ (n + 1)) := by
              simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := μ (n + 1))
                (fun x => A x - g x)
          _ ≤ ∫ x, (L * ε (n + 1)) ∂(μ (n + 1)) := integral_mono_of_nonneg
              (ae_of_all _ fun _ => abs_nonneg _) (integrable_const _) (ae_of_all _ hxA)
          _ = L * ε (n + 1) := by simp
      show ‖∫ z, f z ∂(κ n : Measure E) - ∫ z, f z ∂(κ₀ : Measure E)‖ ≤ _
      rw [e1, e2, Real.norm_eq_abs]
      have : ∫ x, A x ∂(μ (n + 1)) - ∫ x, g x ∂μ₀ =
          (∫ x, A x ∂(μ (n + 1)) - ∫ x, g x ∂(μ (n + 1))) +
            (∫ x, g x ∂(μ (n + 1)) - ∫ x, g x ∂μ₀) := by ring
      rw [this]
      exact (abs_add_le _ _).trans (add_le_add hdiff le_rfl)
    · have h1 := ((tendsto_add_atTop_iff_nat 1).2 hε).const_mul (L : ℝ)
      have h2 : Tendsto (fun n : ℕ => ∫ x, g x ∂(μ (n + 1))) atTop (𝓝 (∫ x, g x ∂μ₀)) :=
        (tendsto_add_atTop_iff_nat (f := fun n => ∫ x, gb x ∂(μ n)) 1).2 hμg
      have h3 := (h2.sub_const (∫ x, g x ∂μ₀)).abs
      simpa using h1.add h3
  intro f
  have := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hlim f
  have h2 : Tendsto (fun n : ℕ => ∫ x, f x ∂(μ (n + 1) ∗ ν (n + 1))) atTop
      (𝓝 (∫ x, f x ∂(μ₀ ∗ ν₀))) := this
  exact (tendsto_add_atTop_iff_nat (f := fun n => ∫ x, f x ∂(μ n ∗ ν n)) 1).1 h2

end Conv

end HRS.A34
