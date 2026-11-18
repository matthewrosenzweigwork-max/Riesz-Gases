import HRS.MS.SpecAux55

/-!
# S8R: the trace bound `E ‖S - Sb‖²_HS ≤ C (N⁻¹ + δ_N²)` for the canonical Gibbs law (S8.7, packet C4)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.

* `s8p_Q_sum_bound`: expectation of the relative quadratic form of the entries over the canonical Gibbs law;
* `s8p_config_hs_bound`: for a configuration with good particles, the Hilbert-Schmidt distance of the square roots is at most
  four times the relative quadratic form of the entries `Δ_{ij}(X)`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace ContDiff

namespace HRS.MS.Spec

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

/-- The relative quadratic form of the entries, as a function of the configuration. -/
def s8p_Qform {N : ℕ} (β : ℝ) (om : ℕ → ℝ) (τ : ℝ) (e : ℕ → Euc d → ℝ) (μ : Measure (Euc d))
    (X : EucConfig d N) : ℝ≥0∞ :=
  ∑' p : ℕ × ℕ, ENNReal.ofReal (((2 / β) * Real.exp (-(τ * (om p.1 + om p.2)) / 2) *
        (linStat (s8p_f e p.1 p.2) X - ∫ x, s8p_f e p.1 p.2 x ∂μ)) ^ 2 /
        (s8p_dv β om τ p.1 + s8p_dv β om τ p.2))

theorem s8p_measurable_Qform {N : ℕ} (hN : 0 < N) (β : ℝ) (om : ℕ → ℝ) (τ : ℝ) (e : ℕ → Euc d → ℝ)
    (he : ∀ l, ContDiff ℝ ∞ (e l)) (μ : Measure (Euc d)) :
    Measurable (s8p_Qform (N := N) β om τ e μ) := by
  unfold s8p_Qform
  refine Measurable.ennreal_tsum fun p => ?_
  refine ENNReal.measurable_ofReal.comp ?_
  have hm := s8p_measurable_linStat hN (s8p_continuous_f he p.1 p.2).measurable
  exact ((measurable_const.mul (hm.sub measurable_const)).pow_const 2).div_const _

theorem s8p_Q_sum_bound {N : ℕ} (hN : 2 ≤ N) {s a β Cs : ℝ} (hCs : 0 ≤ Cs)
    (hS : S45.S45Static d s a β Cs N) [IsProbabilityMeasure (thermalMeasure d s a β)]
    (hβ : 0 < β) {om : ℕ → ℝ} (hom : ∀ l, 0 < om l) (hmono : Monotone om) {τ : ℝ} (hτ : 0 < τ)
    {t₀ C4 : ℝ} (hC4 : 0 ≤ C4) (e : ℕ → Euc d → ℝ) (he : ∀ l, ContDiff ℝ ∞ (e l))
    (hgrad : ∀ i j, ∫ x, s8p_f e i j x ∂(thermalMeasure d s a β) = if i = j then om i else 0)
    (hL4 : ∀ l, eLpNorm (fun x => ‖gradient (e l) x‖) 4 (thermalMeasure d s a β) ≤
      ENNReal.ofReal (C4 * Real.exp (t₀ * om l))) :
    ∫⁻ X, s8p_Qform β om τ e (thermalMeasure d s a β) X ∂(s8p_QN d s a β N) ≤
      ENNReal.ofReal (C4 ^ 4 / (β * om 0) * (Cs / N + Cs ^ 2 * HRS.deltaN d s N ^ 2)) *
        (∑' l, ENNReal.ofReal (Real.exp (-(τ / 2 - 2 * t₀) * om l))) ^ 2 := by
  have hN0 : 0 < N := by omega
  unfold s8p_Qform
  rw [lintegral_tsum fun p => ?_]
  · set K := C4 ^ 4 / (β * om 0) * (Cs / N + Cs ^ 2 * HRS.deltaN d s N ^ 2) with hK
    have hK0 : 0 ≤ K := by
      have : (0 : ℝ) ≤ Cs / N := by positivity
      have h0 := hom 0
      positivity
    calc _ ≤ ∑' p : ℕ × ℕ, ENNReal.ofReal (K * Real.exp (-(τ / 2 - 2 * t₀) * (om p.1 + om p.2))) :=
          ENNReal.tsum_le_tsum fun p => s8p_term_bound hN hCs hS hβ hom hmono hτ hC4 e he hgrad hL4 p
      _ = ENNReal.ofReal K * ∑' p : ℕ × ℕ, ENNReal.ofReal
            (Real.exp (-(τ / 2 - 2 * t₀) * (om p.1 + om p.2))) := by
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun p => ?_
          rw [ENNReal.ofReal_mul hK0]
      _ = _ := by rw [s8p_tsum_prod_exp]
  · refine (ENNReal.measurable_ofReal.comp ?_).aemeasurable
    have hm := s8p_measurable_linStat hN0 (s8p_continuous_f he p.1 p.2).measurable
    exact ((measurable_const.mul (hm.sub measurable_const)).pow_const 2).div_const _

/-- For a configuration with good particles, `‖S - Sb‖²_HS` is bounded by four times the relative quadratic form. -/
theorem s8p_config_hs_bound {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 0 < β) {om : ℕ → ℝ}
    (hom : ∀ l, 0 < om l) {τ : ℝ} (hτ : 0 < τ) (hsum : Summable (s8p_dv β om τ))
    (e : ℕ → Euc d → ℝ) (μ : Measure (Euc d))
    (hgrad : ∀ i j, ∫ x, s8p_f e i j x ∂μ = if i = j then om i else 0)
    (X : EucConfig d N) (hX : ∀ i, s8p_good om e τ (X i))
    {S Sb : SeqL2 →L[ℝ] SeqL2}
    (hS : IsSqrtOfForm S (hsCovForm (fun ia : Fin N × Fin d =>
      Real.sqrt (2 / (N * β)) • s8p_Gv om e τ (X ia.1) ia.2)))
    (hSb : IsSqrtOfForm Sb (s8p_Cdet hβ hom hτ)) :
    ∑' j, ‖(S - Sb) (S45.s45_seqBasis j)‖ₑ ^ 2 ≤ 4 * s8p_Qform β om τ e μ X := by
  refine (s8p_hs_pointwise hβ hom hτ hsum _ hS hSb).trans (le_of_eq ?_)
  unfold s8p_Qform
  congr 1
  refine tsum_congr fun p => ?_
  congr 1
  rw [s8p_hsCov_entry hN hβ om e τ X hX]
  obtain ⟨i, j⟩ := p
  simp only [hgrad]
  by_cases hij : i = j
  · subst hij
    simp only [if_true]
    unfold s8p_dv
    have : Real.exp (-(τ * (om i + om i)) / 2) = Real.exp (-τ * om i) := by
      congr 1; ring
    rw [this]
    congr 1
    ring
  · simp only [hij, if_false]
    ring_nf

end HRS.MS.Spec
