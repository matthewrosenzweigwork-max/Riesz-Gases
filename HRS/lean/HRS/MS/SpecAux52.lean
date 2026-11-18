import HRS.MS.SpecAux51
import HRS.MS.QsfStat1
import HRS.MS.ShiftFldAux5

/-!
# S8R: second moment of a linear statistic under the canonical Gibbs law (S8.7, packet C2)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  From `S45.S45Static` (linear variance bound, bounded marginal density with
`‖φ-1‖_{L²(μ)} ≤ C δ_N`, exchangeability): for a measurable `f ∈ L²(μ)`,
`E_Q (μ_N(f) - μ(f))² ≤ (C/N + C² δ_N²) ∫ f² dμ` (`s8p_linStat_moment`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace HRS.MS.Spec

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

/-- The canonical Gibbs law of the critical quadratic model. -/
abbrev s8p_QN (d : ℕ) (s a β : ℝ) (N : ℕ) : Measure (EucConfig d N) :=
  HRS.Whole.canonicalGibbs (HRS.Whole.rieszKernel d s) (HRS.Whole.confinement a) N β

theorem s8p_map_eval {N : ℕ} (hN : 0 < N) {Q : Measure (EucConfig d N)} (hQ : HRS.Whole.IsExchangeable Q)
    (i : Fin N) : Q.map (fun X => X i) = HRS.Whole.firstMarginal Q := by
  have hT : ∀ τ : Equiv.Perm (Fin N), Measurable (fun X : EucConfig d N => X ∘ τ) :=
    fun τ => measurable_pi_iff.2 fun i => measurable_pi_apply (τ i)
  ext A hA
  unfold HRS.Whole.firstMarginal
  rw [dif_pos hN, Measure.map_apply (measurable_pi_apply i) hA,
    Measure.map_apply (measurable_pi_apply (⟨0, hN⟩ : Fin N)) hA]
  have h := hQ (Equiv.swap i ⟨0, hN⟩)
  have hm : MeasurableSet {X : EucConfig d N | X i ∈ A} := measurable_pi_apply i hA
  calc Q {X | X i ∈ A} = (Q.map (fun X : EucConfig d N => X ∘ (Equiv.swap i ⟨0, hN⟩))) {X | X i ∈ A} := by
        rw [h]
    _ = Q {X | X ⟨0, hN⟩ ∈ A} := by
        rw [Measure.map_apply (hT _) hm]
        congr 1
        ext X
        simp

theorem s8p_linStat_eq {N : ℕ} (hN : 0 < N) (f : Euc d → ℝ) :
    linStat f = fun X : EucConfig d N => (N : ℝ)⁻¹ * ∑ i, f (X i) := by
  funext X
  unfold linStat
  exact HRS.Whole.pair_empirical hN X f

theorem s8p_measurable_linStat {N : ℕ} (hN : 0 < N) {f : Euc d → ℝ} (hf : Measurable f) :
    Measurable (linStat f : EucConfig d N → ℝ) := by
  rw [s8p_linStat_eq hN]
  exact (Finset.measurable_sum _ fun i _ => hf.comp (measurable_pi_apply i)).const_mul _

theorem s8p_integral_linStat {N : ℕ} (hN : 0 < N) {Q : Measure (EucConfig d N)}
    [IsProbabilityMeasure Q] (hQ : HRS.Whole.IsExchangeable Q) {f : Euc d → ℝ} (hf : Measurable f)
    (hfi : Integrable f (HRS.Whole.firstMarginal Q)) :
    Integrable (linStat f) Q ∧ ∫ X, linStat f X ∂Q = ∫ x, f x ∂(HRS.Whole.firstMarginal Q) := by
  have hint : ∀ i : Fin N, Integrable (fun X : EucConfig d N => f (X i)) Q := by
    intro i
    have h := hfi
    rw [← s8p_map_eval hN hQ i] at h
    exact (integrable_map_measure hf.aestronglyMeasurable
      (measurable_pi_apply i).aemeasurable).1 h
  have hsum : Integrable (fun X : EucConfig d N => ∑ i, f (X i)) Q := integrable_finset_sum _ fun i _ => hint i
  rw [s8p_linStat_eq hN]
  refine ⟨hsum.const_mul _, ?_⟩
  rw [integral_const_mul, integral_finsetSum _ fun i _ => hint i]
  have : ∀ i : Fin N, ∫ X : EucConfig d N, f (X i) ∂Q = ∫ x, f x ∂(HRS.Whole.firstMarginal Q) := by
    intro i
    rw [← s8p_map_eval hN hQ i, integral_map (measurable_pi_apply i).aemeasurable hf.aestronglyMeasurable]
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

theorem s8p_cs_sq {μ : Measure (Euc d)} [IsFiniteMeasure μ] {f g : Euc d → ℝ} (hf : MemLp f 2 μ)
    (hg : MemLp g 2 μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * ∫ x, g x ^ 2 ∂μ := by
  have h1 : Integrable (fun x => f x * g x) μ := hf.integrable_mul hg
  have h2 : Integrable (fun x => f x ^ 2) μ := hf.integrable_sq
  have h3 : Integrable (fun x => g x ^ 2) μ := hg.integrable_sq
  have key : ∀ t : ℝ, 0 ≤ (∫ x, f x ^ 2 ∂μ) * (t * t) + (2 * ∫ x, f x * g x ∂μ) * t +
      ∫ x, g x ^ 2 ∂μ := by
    intro t
    have e : ∫ x, (t * f x + g x) ^ 2 ∂μ = (∫ x, f x ^ 2 ∂μ) * (t * t) +
        (2 * ∫ x, f x * g x ∂μ) * t + ∫ x, g x ^ 2 ∂μ := by
      have : ∀ x, (t * f x + g x) ^ 2 = t * t * f x ^ 2 + 2 * t * (f x * g x) + g x ^ 2 := fun x => by ring
      simp_rw [this]
      have i1 : Integrable (fun x => t * t * f x ^ 2) μ := h2.const_mul _
      have i2 : Integrable (fun x => 2 * t * (f x * g x)) μ := h1.const_mul _
      have i12 : Integrable (fun x => t * t * f x ^ 2 + 2 * t * (f x * g x)) μ := i1.add i2
      rw [integral_add i12 h3, integral_add i1 i2, integral_const_mul, integral_const_mul]
      ring
    rw [← e]
    exact integral_nonneg fun x => sq_nonneg _
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith

theorem s8p_linStat_moment {N : ℕ} (hN : 2 ≤ N) {s a β Cs : ℝ} (hCs : 0 ≤ Cs)
    (hS : S45.S45Static d s a β Cs N) [IsProbabilityMeasure (thermalMeasure d s a β)]
    (f : Euc d → ℝ) (hfm : Measurable f) (hf : MemLp f 2 (thermalMeasure d s a β)) :
    ∫⁻ X, ENNReal.ofReal ((HRS.Whole.linStat f X - ∫ x, f x ∂(thermalMeasure d s a β)) ^ 2)
        ∂(s8p_QN d s a β N) ≤
      ENNReal.ofReal ((Cs / N + Cs ^ 2 * HRS.deltaN d s N ^ 2) *
        ∫ x, f x ^ 2 ∂(thermalMeasure d s a β)) := by
  have hN0 : 0 < N := by omega
  set μ := thermalMeasure d s a β with hμ
  set Q := s8p_QN d s a β N with hQ
  have := hS.prob
  obtain ⟨φ, hφm, hφeq, hφb, hφ2, hφn⟩ := hS.marg
  have hXm : Measurable (linStat f : EucConfig d N → ℝ) := s8p_measurable_linStat hN0 hfm
  set F2 := ∫ x, f x ^ 2 ∂μ with hF2
  have hF20 : 0 ≤ F2 := integral_nonneg fun x => sq_nonneg _
  -- the marginal is dominated by `Cs • μ`
  have hfmle : HRS.Whole.firstMarginal Q ≤ ENNReal.ofReal Cs • μ := by
    rw [hφeq]
    refine (withDensity_mono (g := fun _ => ENNReal.ofReal Cs)
      (Filter.Eventually.of_forall fun x => ?_)).trans (le_of_eq ?_)
    · exact ENNReal.ofReal_le_ofReal (hφb x).2
    · rw [withDensity_const]
  have hfi : Integrable f (HRS.Whole.firstMarginal Q) :=
    ((hf.integrable one_le_two).smul_measure ENNReal.ofReal_ne_top).mono_measure hfmle
  obtain ⟨hXi, hXE⟩ := s8p_integral_linStat hN0 hS.exch hfm hfi
  -- `X ∈ L²`
  have hXL2 : MemLp (linStat f : EucConfig d N → ℝ) 2 Q := by
    refine (evariance_lt_top_iff_memLp hXm.aestronglyMeasurable).1 ?_
    exact lt_of_le_of_lt (hS.linear f hf) ENNReal.ofReal_lt_top
  have hvar : variance (linStat f : EucConfig d N → ℝ) Q ≤ Cs / N * F2 := by
    have h1 := hXL2.ofReal_variance_eq
    have h2 := hS.linear f hf
    have h3 : (0 : ℝ) ≤ Cs / N * F2 := by positivity
    exact (ENNReal.ofReal_le_ofReal_iff h3).1 (h1.le.trans h2)
  -- bias
  set m := ∫ x, f x ∂μ with hm
  have hEm : (∫ X, linStat f X ∂Q - m) ^ 2 ≤ F2 * (Cs * HRS.deltaN d s N) ^ 2 := by
    have hE1 : ∫ x, f x ∂(HRS.Whole.firstMarginal Q) = ∫ x, f x * φ x ∂μ := by
      rw [hφeq, integral_withDensity_eq_integral_toReal_smul (by fun_prop) (by simp)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [smul_eq_mul, ENNReal.toReal_ofReal (hφb x).1]
      ring
    have hfφ : Integrable (fun x => f x * φ x) μ := by
      have : MemLp φ 2 μ := by
        have h := hφ2.add (memLp_const (1 : ℝ) : MemLp (fun _ : Euc d => (1 : ℝ)) 2 μ)
        have e : φ = (fun x => φ x - 1) + fun _ => (1 : ℝ) := by funext x; simp
        rw [e]; exact h
      exact hf.integrable_mul this
    have hE2 : ∫ X, linStat f X ∂Q - m = ∫ x, f x * (φ x - 1) ∂μ := by
      rw [hXE, hE1, hm]
      have : ∀ x, f x * (φ x - 1) = f x * φ x - f x := fun x => by ring
      simp_rw [this]
      rw [integral_sub hfφ (hf.integrable one_le_two)]
    rw [hE2]
    refine (s8p_cs_sq hf hφ2).trans ?_
    rw [hF2]
    refine mul_le_mul_of_nonneg_left ?_ hF20
    have h0 : 0 ≤ ∫ x, (φ x - 1) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
    have : l2Norm μ (fun x => φ x - 1) ^ 2 = ∫ x, (φ x - 1) ^ 2 ∂μ := Real.sq_sqrt h0
    rw [← this]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hφn 2
  -- assemble
  have hY2 : MemLp (fun X : EucConfig d N => linStat f X - m) 2 Q := hXL2.sub (memLp_const m)
  have hvar2 : ∫ X, (linStat f X - m) ^ 2 ∂Q =
      variance (linStat f : EucConfig d N → ℝ) Q + (∫ X, linStat f X ∂Q - m) ^ 2 := by
    have h := variance_eq_sub hY2
    have hv : variance (fun X : EucConfig d N => linStat f X - m) Q =
        variance (linStat f : EucConfig d N → ℝ) Q := by
      have := variance_add_const (μ := Q) hXm.aestronglyMeasurable (-m)
      simpa [sub_eq_add_neg] using this
    have hE : ∫ X, (linStat f X - m) ∂Q = ∫ X, linStat f X ∂Q - m := by
      have hXi' : Integrable (linStat f : EucConfig d N → ℝ) Q := hXi
      rw [integral_sub hXi' (integrable_const m)]; simp
    simp only [Pi.pow_apply] at h
    rw [hv, hE] at h
    linarith
  have hint : Integrable (fun X : EucConfig d N => (linStat f X - m) ^ 2) Q := hY2.integrable_sq
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun X => sq_nonneg _),
    hvar2]
  refine ENNReal.ofReal_le_ofReal ?_
  have := mul_nonneg hF20 (sq_nonneg (Cs * HRS.deltaN d s N))
  nlinarith [hvar, hEm, this]

end HRS.MS.Spec
