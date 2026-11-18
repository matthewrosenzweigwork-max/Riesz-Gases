import HRS.MS.SpecAux56

/-!
# S8R: square summability a.e. and the size of the empirical integrand (S8.7, packet C3)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  With `Fq x = ∑_l e^{-τ om_l} |∇e_l(x)|²` (in `ℝ≥0∞`):

* `s8p_lintegral_Fq`: `∫ Fq dμ = ∑_l om_l e^{-τ om_l} < ∞`;
* `s8p_good_ae`: `μ`-a.e. point is `good` (the coordinate sequences are square summable);
* `s8p_Phi_enorm_sum_le`: `∑_{ia} ‖√(2/(Nβ)) s8p_Gv (X_i) a‖² ≤ (2/(Nβ)) ∑_i Fq(X_i)`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace ContDiff

namespace HRS.MS.Spec

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

/-- `Fq x = ∑_l e^{-τ om_l} |∇e_l(x)|²`. -/
def s8p_Fq (om : ℕ → ℝ) (e : ℕ → Euc d → ℝ) (τ : ℝ) (x : Euc d) : ℝ≥0∞ :=
  ∑' l, ENNReal.ofReal (Real.exp (-τ * om l) * s8p_f e l l x)

theorem s8p_measurable_Fq (om : ℕ → ℝ) {e : ℕ → Euc d → ℝ} (he : ∀ l, ContDiff ℝ ∞ (e l)) (τ : ℝ) :
    Measurable (s8p_Fq om e τ) := by
  unfold s8p_Fq
  exact Measurable.ennreal_tsum fun l =>
    ENNReal.measurable_ofReal.comp (measurable_const.mul (s8p_continuous_f he l l).measurable)

theorem s8p_f_self_nonneg (e : ℕ → Euc d → ℝ) (l : ℕ) (x : Euc d) : 0 ≤ s8p_f e l l x := by
  unfold s8p_f; exact real_inner_self_nonneg

theorem s8p_lintegral_Fq {μ : Measure (Euc d)} {om : ℕ → ℝ} {e : ℕ → Euc d → ℝ}
    (he : ∀ l, ContDiff ℝ ∞ (e l)) (τ : ℝ) (hint : ∀ l, Integrable (s8p_f e l l) μ)
    (hgrad : ∀ l, ∫ x, s8p_f e l l x ∂μ = om l) :
    ∫⁻ x, s8p_Fq om e τ x ∂μ = ∑' l, ENNReal.ofReal (Real.exp (-τ * om l) * om l) := by
  unfold s8p_Fq
  rw [lintegral_tsum (f := fun l x => ENNReal.ofReal (Real.exp (-τ * om l) * s8p_f e l l x))
    fun l => (ENNReal.measurable_ofReal.comp
      (measurable_const.mul (s8p_continuous_f he l l).measurable)).aemeasurable]
  refine tsum_congr fun l => ?_
  rw [← ofReal_integral_eq_lintegral_ofReal ((hint l).const_mul _)
    (Filter.Eventually.of_forall fun x => mul_nonneg (Real.exp_pos _).le (s8p_f_self_nonneg e l x)),
    integral_const_mul, hgrad]

theorem s8p_good_of_Fq_lt_top {om : ℕ → ℝ} {e : ℕ → Euc d → ℝ} {τ : ℝ} {x : Euc d}
    (hx : s8p_Fq om e τ x < ⊤) : s8p_good om e τ x := by
  intro a
  rw [memℓp_two_iff]
  have hsq : ∀ l, s8p_cs om e τ x a l ^ 2 ≤ Real.exp (-τ * om l) * s8p_f e l l x := by
    intro l
    have h1 := s8p_cs_mul_sum om e τ x l l
    have h2 : s8p_cs om e τ x a l * s8p_cs om e τ x a l ≤
        ∑ a', s8p_cs om e τ x a' l * s8p_cs om e τ x a' l :=
      Finset.single_le_sum (f := fun a' => s8p_cs om e τ x a' l * s8p_cs om e τ x a' l)
        (fun a' _ => mul_self_nonneg _) (Finset.mem_univ a)
    rw [h1] at h2
    have h3 : Real.exp (-(τ * (om l + om l)) / 2) = Real.exp (-τ * om l) := by
      congr 1; ring
    rw [h3] at h2
    nlinarith [h2]
  have hfin : ∑' l, ENNReal.ofReal (s8p_cs om e τ x a l ^ 2) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hx.ne (ENNReal.tsum_le_tsum fun l => ?_)
    exact ENNReal.ofReal_le_ofReal (hsq l)
  have := ENNReal.summable_toReal hfin
  refine this.congr fun l => ?_
  exact ENNReal.toReal_ofReal (sq_nonneg _)

theorem s8p_good_ae {μ : Measure (Euc d)} {om : ℕ → ℝ} {e : ℕ → Euc d → ℝ}
    (he : ∀ l, ContDiff ℝ ∞ (e l)) (τ : ℝ) (hint : ∀ l, Integrable (s8p_f e l l) μ)
    (hgrad : ∀ l, ∫ x, s8p_f e l l x ∂μ = om l)
    (hfin : ∑' l, ENNReal.ofReal (Real.exp (-τ * om l) * om l) < ⊤) :
    ∀ᵐ x ∂μ, s8p_good om e τ x := by
  have := s8p_lintegral_Fq (om := om) he τ hint hgrad
  have hlt : ∫⁻ x, s8p_Fq om e τ x ∂μ < ⊤ := by rw [this]; exact hfin
  filter_upwards [ae_lt_top (s8p_measurable_Fq om he τ) hlt.ne] with x hx
  exact s8p_good_of_Fq_lt_top hx

theorem s8p_norm_ofSeq_le (v : ℕ → ℝ) :
    ‖SeqL2.ofSeq v‖ₑ ^ 2 ≤ ∑' l, ENNReal.ofReal (v l ^ 2) := by
  by_cases h : Memℓp v 2
  · have hv : SeqL2.ofSeq v = (⟨v, h⟩ : lp (fun _ : ℕ => ℝ) 2) := by
      unfold SeqL2.ofSeq; exact dif_pos h
    have hs : Summable fun l => v l ^ 2 := memℓp_two_iff.1 h
    have h1 : ‖SeqL2.ofSeq v‖ ^ 2 = ∑' l, v l ^ 2 := by
      rw [← u11_norm_sq, hv]
      exact tsum_congr fun l => rfl
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), h1,
      ENNReal.ofReal_tsum_of_nonneg (fun l => sq_nonneg _) hs]
  · have : SeqL2.ofSeq v = 0 := by unfold SeqL2.ofSeq; exact dif_neg h
    rw [this]; simp

theorem s8p_Phi_enorm_sum_le {N : ℕ} (hN : 0 < N) {β : ℝ} (hβ : 0 < β) (om : ℕ → ℝ)
    (e : ℕ → Euc d → ℝ) (τ : ℝ) (X : EucConfig d N) :
    ∑' ia : Fin N × Fin d, ‖Real.sqrt (2 / (N * β)) • s8p_Gv om e τ (X ia.1) ia.2‖ₑ ^ 2 ≤
      ENNReal.ofReal (2 / (N * β)) * ∑ i, s8p_Fq om e τ (X i) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [tsum_fintype, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : ∀ a : Fin d, ‖Real.sqrt (2 / (N * β)) • s8p_Gv om e τ (X i) a‖ₑ ^ 2 ≤
      ENNReal.ofReal (2 / (N * β)) * ∑' l, ENNReal.ofReal (s8p_cs om e τ (X i) a l ^ 2) := by
    intro a
    rw [enorm_smul, mul_pow, Real.enorm_eq_ofReal (Real.sqrt_nonneg _), ← ENNReal.ofReal_pow
      (Real.sqrt_nonneg _), Real.sq_sqrt (by positivity)]
    exact mul_le_mul_right (s8p_norm_ofSeq_le _) _
  refine (Finset.sum_le_sum fun a _ => h1 a).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_right ?_ _
  unfold s8p_Fq
  rw [← Summable.tsum_finsetSum (fun a _ => ENNReal.summable)]
  refine le_of_eq (tsum_congr fun l => ?_)
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => sq_nonneg _)]
  congr 1
  have h2 := s8p_cs_mul_sum om e τ (X i) l l
  have h3 : Real.exp (-(τ * (om l + om l)) / 2) = Real.exp (-τ * om l) := by
    congr 1; ring
  rw [h3] at h2
  rw [← h2]
  exact Finset.sum_congr rfl fun a _ => sq _

end HRS.MS.Spec
