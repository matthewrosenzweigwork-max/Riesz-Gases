import HRS.MS.S21L_G11E
import HRS.MS.S21L_G11F1
import HRS.MS.S21G2_K11b

/-!
# S21L G11F -- a Hilbert-valued `L²` element whose coordinates are in the scalar second chaos lies in `InSecondChaos` (R26-T3.G11, seventh step)

Let `B` be a separable Hilbert space and `Q ∈ L²(P;B)` with `ω ↦ ⟪v, Q ω⟫ ∈ InQ2` for every `v ∈ B`.  Then `‖Q‖⁴ ∈ L¹`
(coordinatewise fourth moments `E W_s⁴ ≤ 15 (E W_s²)²` of `s21l_inQ2_four`, Cauchy-Schwarz on finite sums, Fatou along an
exhaustion of the Hilbert basis), and `Q ∈ InSecondChaos P ξ 3 Q` by the pinned transfer lemma `inSecondChaos_of_approx`
with the finite-rank projections of the basis.  Prefix `s21l_`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.deprecated false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3

open HRS HRS.MC.E213U13

section Four

variable {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]
  [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem s21l_fatou_pw {Qn : ℕ → Ω → ℝ} {Q : Ω → ℝ} (hmeas : ∀ n, AEStronglyMeasurable (Qn n) P)
    (hQm : AEStronglyMeasurable Q P) (hae : ∀ᵐ ω ∂P, Tendsto (fun n => Qn n ω) atTop (𝓝 (Q ω))) {C : ℝ}
    (hC : ∀ n, Integrable (fun ω => Qn n ω ^ 2) P ∧ ∫ ω, Qn n ω ^ 2 ∂P ≤ C) :
    Integrable (fun ω => Q ω ^ 2) P ∧ ∫ ω, Q ω ^ 2 ∂P ≤ C := by
  have hC0 : 0 ≤ C := (integral_nonneg fun ω => by positivity).trans (hC 0).2
  have hc : Continuous fun x : ℝ => ENNReal.ofReal (x ^ 2) :=
    ENNReal.continuous_ofReal.comp (continuous_pow 2)
  have key : ∫⁻ ω, ENNReal.ofReal (Q ω ^ 2) ∂P ≤ ENNReal.ofReal C := by
    calc ∫⁻ ω, ENNReal.ofReal (Q ω ^ 2) ∂P
        = ∫⁻ ω, liminf (fun i => ENNReal.ofReal (Qn i ω ^ 2)) atTop ∂P := by
          refine lintegral_congr_ae ?_
          filter_upwards [hae] with ω hω
          exact (((hc.tendsto _).comp hω).liminf_eq).symm
      _ ≤ liminf (fun i => ∫⁻ ω, ENNReal.ofReal (Qn i ω ^ 2) ∂P) atTop :=
          lintegral_liminf_le' fun i => ((hmeas _).aemeasurable.pow_const 2).ennreal_ofReal
      _ ≤ ENNReal.ofReal C := by
          refine liminf_le_of_frequently_le' (Frequently.of_forall fun i => ?_)
          rw [← ofReal_integral_eq_lintegral_ofReal (hC _).1
            (Filter.Eventually.of_forall fun ω => by positivity)]
          exact ENNReal.ofReal_le_ofReal (hC _).2
  have hQm : AEStronglyMeasurable (fun ω => Q ω ^ 2) P := hQm.pow 2
  refine ⟨⟨hQm, ?_⟩, ?_⟩
  · rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun ω => by positivity)]
    exact lt_of_le_of_lt key ENNReal.ofReal_lt_top
  · rw [integral_eq_lintegral_of_nonneg_ae (f := fun ω => Q ω ^ 2)
      (Filter.Eventually.of_forall fun ω => by positivity) hQm]
    exact ENNReal.toReal_le_of_le_ofReal hC0 key

theorem s21l_finite_four {ι : Type*} (b : HilbertBasis ι ℝ B) {Q : Ω → B} (hQ2 : MemLp Q 2 P)
    (hW : ∀ s, Integrable (fun ω => (inner ℝ (b s) (Q ω)) ^ 4) P ∧
      ∫ ω, (inner ℝ (b s) (Q ω)) ^ 4 ∂P ≤ 15 * (∫ ω, (inner ℝ (b s) (Q ω)) ^ 2 ∂P) ^ 2)
    (F : Finset ι) :
    ∫ ω, (∑ s ∈ F, (inner ℝ (b s) (Q ω)) ^ 2) ^ 2 ∂P ≤
      15 * (∑ s ∈ F, ∫ ω, (inner ℝ (b s) (Q ω)) ^ 2 ∂P) ^ 2 := by
  set f : ι → Ω → ℝ := fun s ω => (inner ℝ (b s) (Q ω)) ^ 2 with hf
  set a : ι → ℝ := fun s => ∫ ω, (inner ℝ (b s) (Q ω)) ^ 2 ∂P with ha
  have ha0 : ∀ s, 0 ≤ a s := fun s => integral_nonneg fun ω => sq_nonneg _
  have hfm : ∀ s, AEStronglyMeasurable (f s) P := fun s =>
    (aestronglyMeasurable_const.inner hQ2.aestronglyMeasurable).pow 2
  have hfL : ∀ s, MemLp (f s) 2 P := fun s => by
    refine (memLp_two_iff_integrable_sq (hfm s)).2 ?_
    refine (hW s).1.congr (ae_of_all _ fun ω => ?_)
    simp only [hf]; ring
  have hf2 : ∀ s, ∫ ω, (f s ω) ^ 2 ∂P ≤ 15 * a s ^ 2 := fun s => by
    refine le_trans (le_of_eq (integral_congr_ae (ae_of_all _ fun ω => ?_))) (hW s).2
    simp only [hf]; ring
  change ∫ ω, (∑ s ∈ F, f s ω) ^ 2 ∂P ≤ 15 * (∑ s ∈ F, a s) ^ 2
  have hexp : ∀ ω, (∑ s ∈ F, f s ω) ^ 2 = ∑ s ∈ F, ∑ t ∈ F, f s ω * f t ω := fun ω => by
    rw [sq, Finset.sum_mul_sum]
  have hcs : ∀ s t, ∫ ω, f s ω * f t ω ∂P ≤ 15 * (a s * a t) := fun s t => by
    have h1 := s21g2_k11b_cs (hfL s) (hfL t)
    refine (le_abs_self _).trans (h1.trans ?_)
    have hA0 : 0 ≤ ∫ ω, (f s ω) ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
    have hB0 : 0 ≤ ∫ ω, (f t ω) ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
    rw [← Real.sqrt_mul hA0]
    refine Real.sqrt_le_iff.2 ⟨by have := ha0 s; have := ha0 t; positivity, ?_⟩
    have := hf2 s
    have := hf2 t
    have h5 := mul_le_mul (hf2 s) (hf2 t) hB0 (by have := ha0 s; positivity)
    nlinarith [ha0 s, ha0 t, mul_nonneg (ha0 s) (ha0 t)]
  have hi : ∀ s t, Integrable (fun ω => f s ω * f t ω) P := fun s t => (hfL s).integrable_mul (hfL t)
  simp_rw [hexp]
  rw [integral_finset_sum _ fun s _ => integrable_finset_sum _ fun t _ => hi s t]
  have : ∀ s ∈ F, ∫ ω, ∑ t ∈ F, f s ω * f t ω ∂P = ∑ t ∈ F, ∫ ω, f s ω * f t ω ∂P := fun s _ =>
    integral_finset_sum _ fun t _ => hi s t
  rw [Finset.sum_congr rfl this]
  calc ∑ s ∈ F, ∑ t ∈ F, ∫ ω, f s ω * f t ω ∂P ≤ ∑ s ∈ F, ∑ t ∈ F, 15 * (a s * a t) :=
        Finset.sum_le_sum fun s _ => Finset.sum_le_sum fun t _ => hcs s t
    _ = 15 * (∑ s ∈ F, a s) ^ 2 := by
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.mul_sum]

theorem s21l_vec_four {ι : Type*} (b : HilbertBasis ι ℝ B) {Q : Ω → B} (hQ : MemLp Q 2 P)
    (hW : ∀ s, Integrable (fun ω => (inner ℝ (b s) (Q ω)) ^ 4) P ∧
      ∫ ω, (inner ℝ (b s) (Q ω)) ^ 4 ∂P ≤ 15 * (∫ ω, (inner ℝ (b s) (Q ω)) ^ 2 ∂P) ^ 2) :
    MemLp Q 4 P := by
  haveI : Countable ι := HilbertCLTAux.countable_of_orthonormal b.orthonormal
  obtain ⟨F, hF⟩ := Filter.exists_seq_tendsto (atTop : Filter (Finset ι))
  have hsum := s21l_hasSum_sq b hQ
  have hfm : ∀ s, AEStronglyMeasurable (fun ω => (inner ℝ (b s) (Q ω)) ^ 2) P := fun s =>
    (aestronglyMeasurable_const.inner hQ.aestronglyMeasurable).pow 2
  have hfL : ∀ s, MemLp (fun ω => (inner ℝ (b s) (Q ω)) ^ 2) 2 P := fun s => by
    refine (memLp_two_iff_integrable_sq (hfm s)).2 ?_
    refine (hW s).1.congr (ae_of_all _ fun ω => ?_)
    ring
  have hQn : ∀ n, MemLp (fun ω => ∑ s ∈ F n, (inner ℝ (b s) (Q ω)) ^ 2) 2 P := fun n =>
    memLp_finsetSum _ fun s _ => hfL s
  have hae : ∀ ω, Tendsto (fun n => ∑ s ∈ F n, (inner ℝ (b s) (Q ω)) ^ 2) atTop (𝓝 (‖Q ω‖ ^ 2)) := fun ω =>
    (show Tendsto (fun s : Finset ι => ∑ i ∈ s, (inner ℝ (b i) (Q ω)) ^ 2) atTop (𝓝 (‖Q ω‖ ^ 2)) from
      s21l_hasSum_norm_sq b (Q ω)).comp hF
  have hnorm : AEStronglyMeasurable (fun ω => ‖Q ω‖ ^ 2) P := hQ.aestronglyMeasurable.norm.pow 2
  obtain ⟨hint, hle⟩ := s21l_fatou_pw (Qn := fun n ω => ∑ s ∈ F n, (inner ℝ (b s) (Q ω)) ^ 2)
    (Q := fun ω => ‖Q ω‖ ^ 2) (fun n => (hQn n).aestronglyMeasurable) hnorm (ae_of_all _ hae)
    (C := 15 * (∫ ω, ‖Q ω‖ ^ 2 ∂P) ^ 2) fun n => ⟨(hQn n).integrable_sq, by
      refine (s21l_finite_four b hQ hW (F n)).trans ?_
      have h0 : 0 ≤ ∑ s ∈ F n, ∫ ω, (inner ℝ (b s) (Q ω)) ^ 2 ∂P :=
        Finset.sum_nonneg fun s _ => integral_nonneg fun ω => sq_nonneg _
      have h1 : ∑ s ∈ F n, ∫ ω, (inner ℝ (b s) (Q ω)) ^ 2 ∂P ≤ ∫ ω, ‖Q ω‖ ^ 2 ∂P :=
        sum_le_hasSum (F n) (fun s _ => integral_nonneg fun ω => sq_nonneg _) hsum
      nlinarith⟩
  refine (integrable_norm_rpow_iff hQ.aestronglyMeasurable (by norm_num) (by norm_num)).1 ?_
  refine hint.congr (ae_of_all _ fun ω => ?_)
  show (‖Q ω‖ ^ 2) ^ 2 = ‖Q ω‖ ^ ((4 : ℝ≥0∞).toReal)
  rw [show ((4 : ℝ≥0∞).toReal) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  ring

end Four

section Coords

variable {B : Type*} [NormedAddCommGroup B] [InnerProductSpace ℝ B] [CompleteSpace B]
  [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]
variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {ξ : ℕ → Ω → ℝ}

theorem s21l_inSecondChaos_of_coords (hξ : IsStdGaussianSeq P ξ) (hm : ∀ i, Measurable (ξ i)) {Q : Ω → B}
    (hQ : AEStronglyMeasurable Q P) (hQ2 : MemLp Q 2 P)
    (hc : ∀ v : B, InQ2 hξ (fun ω => inner ℝ v (Q ω))) : InSecondChaos P ξ 3 Q := by
  obtain ⟨ι, hι, b, -⟩ := HilbertCLTAux.exists_hilbertBasis_type (H := B)
  have hQ4 : MemLp Q 4 P := s21l_vec_four b hQ2 fun s => s21l_inQ2_four (hc (b s))
  obtain ⟨F, hF⟩ := Filter.exists_seq_tendsto (atTop : Filter (Finset ι))
  set Pn : ℕ → B →L[ℝ] B := fun n => ∑ s ∈ F n, (innerSL ℝ (b s)).smulRight (b s) with hPn
  have hfin : ∀ n x, Pn n x = ∑ s ∈ F n, (innerSL ℝ (b s)) x • b s := fun n x => by
    simp [hPn, ContinuousLinearMap.sum_apply]
  have hnorm : ∀ n x, ‖Pn n x‖ ≤ ‖x‖ := fun n x => by
    have hy : ‖Pn n x‖ ^ 2 = ∑ s ∈ F n, (inner ℝ (b s) x) ^ 2 := by
      rw [hfin, ← real_inner_self_eq_norm_sq]
      have h1 := b.orthonormal.inner_sum (fun s => inner ℝ (b s) x) (fun s => inner ℝ (b s) x) (F n)
      simp only [innerSL_apply_apply, conj_trivial, sq] at h1 ⊢
      exact h1
    have h2 := b.orthonormal.sum_inner_products_le x (s := F n)
    simp only [Real.norm_eq_abs, sq_abs] at h2
    have h3 : ‖Pn n x‖ ^ 2 ≤ ‖x‖ ^ 2 := by rw [hy]; exact h2
    by_contra hlt
    push_neg at hlt
    nlinarith [norm_nonneg x, norm_nonneg (Pn n x)]
  have hlim : ∀ x, Tendsto (fun n => Pn n x) atTop (𝓝 x) := fun x => by
    have h := b.hasSum_repr x
    have h' : Tendsto (fun s : Finset ι => ∑ i ∈ s, b.repr x i • b i) atTop (𝓝 x) := h
    refine (h'.comp hF).congr fun n => ?_
    rw [hfin]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp [HilbertBasis.repr_apply_apply]
  exact inSecondChaos_of_approx hξ hm hQ (q := 3) (r := 4) (by norm_num) (by norm_num)
    (by simpa using hQ4) Pn hnorm hlim F (fun s => innerSL ℝ (b s)) (fun _ s => b s) hfin
    (fun n s _ => hc (b s))

end Coords

end HRS.MS.R26T3
