import HRS.MS.S111K2T02a
import HRS.MS.S111K2T02b

/-!
# S11.1 continuation, T02: `summed_commutator_kernel`

The vector commutator kernel estimate: `Σ_j ∫∫ h_{∇f_j}(x,y)² dμ dμ ≤ C B`, with explicit summability and `L²`
membership of each kernel.  Assembled from the pointwise Taylor bound (`T02a`) and the weighted double integral (`T02b`).
-/

noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.S111K2
open HRS HRS.Whole

theorem s111k2_summed_commutator_kernel (d : ℕ) (hd : 2 ≤ d)
    (s Pw M c : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (hPw : 0 ≤ Pw) (hM : 0 < M) (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ rho : Euc d → ℝ,
      HRS.Whole.IsProbDensity rho → HRS.Whole.HasR2GaussianUpper M c rho →
      ∀ f : ℕ → Euc d → ℝ, (∀ j, ContDiff ℝ 2 (f j)) →
      ∀ B : ℝ, 0 ≤ B →
      (∀ x, Summable (fun j => ‖fderiv ℝ (gradient (f j)) x‖ ^ 2) ∧
        (∑' j, ‖fderiv ℝ (gradient (f j)) x‖ ^ 2) ≤
          B * (1 + ‖x‖) ^ (2 * Pw)) →
      let mu := HRS.Whole.withDensityReal rho
      let v := fun j => ∫ xy,
        commutatorKernel d s (gradient (f j)) xy.1 xy.2 ^ 2 ∂(mu.prod mu)
      (∀ j, MemLp (Function.uncurry (commutatorKernel d s (gradient (f j)))) 2 (mu.prod mu)) ∧
        Summable v ∧ (∑' j, v j) ≤ C * B := by
  obtain ⟨K, hK0, hK⟩ := s111k2_double hd hs0 hs M c hc hPw
  refine ⟨(s + 1) ^ 2 * K, by positivity, fun ρ hρ hG f hf B hB hsum => ?_⟩
  intro mu v
  haveI : IsProbabilityMeasure mu := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  have hDbl := hK ρ hρ hG.2
  set a : Euc d → ℝ := fun y => (1 + ‖y‖) ^ (2 * Pw) with ha
  set k : ℕ → Euc d × Euc d → ℝ := fun j p => commutatorKernel d s (gradient (f j)) p.1 p.2 with hk
  have hkm : ∀ j, Measurable (k j) := by
    intro j
    have hg : Measurable (gradient (f j)) := by
      have h1 : Continuous (fderiv ℝ (f j)) := ((hf j).continuous_fderiv (by norm_num))
      exact ((InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp h1).measurable
    have h2 : Measurable fun p : Euc d × Euc d => gradient (f j) p.1 - gradient (f j) p.2 :=
      (hg.comp measurable_fst).sub (hg.comp measurable_snd)
    have h3 : Measurable fun p : Euc d × Euc d => rieszKernelGrad d s (p.1 - p.2) :=
      (movtr_rieszKernelGrad_measurable (d := d) s).comp (measurable_fst.sub measurable_snd)
    exact h2.inner h3
  set W : Euc d × Euc d → ℝ := fun p => HRS.Whole.rieszWeight s (p.1 - p.2) with hW
  set E : ℝ≥0∞ := ENNReal.ofReal ((s + 1) ^ 2 * B) * ENNReal.ofReal K with hE
  -- the finite-partial-sum bound
  have hbd : ∀ F : Finset ℕ, ∑ j ∈ F, ∫⁻ p, ENNReal.ofReal (k j p ^ 2) ∂(mu.prod mu) ≤ E := by
    intro F
    rw [← lintegral_finset_sum (μ := mu.prod mu) F (f := fun j p => ENNReal.ofReal (k j p ^ 2))
      (fun j _ => (ENNReal.measurable_ofReal.comp ((hkm j).pow_const 2)))]
    have hpt : ∀ p : Euc d × Euc d, ∑ j ∈ F, ENNReal.ofReal (k j p ^ 2) ≤
        ENNReal.ofReal ((s + 1) ^ 2 * B) * ENNReal.ofReal ((1 + ‖p.1‖) ^ (2 * Pw) * (1 + ‖p.2‖) ^ (2 * Pw) *
          (1 + HRS.Whole.rieszWeight s (p.1 - p.2)) ^ 2) := by
      intro p
      rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => sq_nonneg _),
        ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      refine (s111k2_pointwise hs0 f hf hB hPw hsum F p.1 p.2).trans (le_of_eq ?_)
      ring
    calc ∫⁻ p, ∑ j ∈ F, ENNReal.ofReal (k j p ^ 2) ∂(mu.prod mu)
        ≤ ∫⁻ p, ENNReal.ofReal ((s + 1) ^ 2 * B) * ENNReal.ofReal ((1 + ‖p.1‖) ^ (2 * Pw) *
            (1 + ‖p.2‖) ^ (2 * Pw) * (1 + HRS.Whole.rieszWeight s (p.1 - p.2)) ^ 2) ∂(mu.prod mu) :=
          lintegral_mono hpt
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ E := mul_le_mul' le_rfl hDbl
  have hLle : ∀ j, ∫⁻ p, ENNReal.ofReal (k j p ^ 2) ∂(mu.prod mu) ≤ E := fun j => by
    simpa using hbd {j}
  have hEne : E ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  have hLne : ∀ j, ∫⁻ p, ENNReal.ofReal (k j p ^ 2) ∂(mu.prod mu) ≠ ⊤ := fun j =>
    ne_top_of_le_ne_top hEne (hLle j)
  have hint : ∀ j, Integrable (fun p => k j p ^ 2) (mu.prod mu) := fun j =>
    ⟨((hkm j).pow_const 2).aestronglyMeasurable, by
      rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun p => sq_nonneg _)]
      exact lt_top_iff_ne_top.2 (hLne j)⟩
  have hvj : ∀ j, v j = (∫⁻ p, ENNReal.ofReal (k j p ^ 2) ∂(mu.prod mu)).toReal := by
    intro j
    exact integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun p => sq_nonneg _)
      ((hkm j).pow_const 2).aestronglyMeasurable
  have hsumL : ∑' j, ∫⁻ p, ENNReal.ofReal (k j p ^ 2) ∂(mu.prod mu) ≤ E := by
    rw [ENNReal.tsum_eq_iSup_sum]
    exact iSup_le hbd
  refine ⟨fun j => ?_, ?_, ?_⟩
  · show MemLp (k j) 2 (mu.prod mu)
    rw [memLp_two_iff_integrable_sq (hkm j).aestronglyMeasurable]
    exact hint j
  · have : v = fun j => (∫⁻ p, ENNReal.ofReal (k j p ^ 2) ∂(mu.prod mu)).toReal := funext hvj
    rw [this]
    exact ENNReal.summable_toReal (ne_top_of_le_ne_top hEne hsumL)
  · have : v = fun j => (∫⁻ p, ENNReal.ofReal (k j p ^ 2) ∂(mu.prod mu)).toReal := funext hvj
    rw [this, ← ENNReal.tsum_toReal_eq hLne]
    have h1 : (∑' j, ∫⁻ p, ENNReal.ofReal (k j p ^ 2) ∂(mu.prod mu)).toReal ≤ E.toReal :=
      ENNReal.toReal_mono hEne hsumL
    refine h1.trans (le_of_eq ?_)
    rw [hE, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal hK0]
    ring

end HRS.MS.S111K2
