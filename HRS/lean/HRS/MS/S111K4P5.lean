import HRS.MS.S111K4P4

/-!
# S11.1 / T03 (S11K4), packet `R26-T6C.P06`: the static screened triple identity with exact signs
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K4

open HRS HRS.Whole
open HRS.MS.TcR (tc2_integrable_nu tc2_integral_nu)
open HRS.MS.S111X1 (KData Wf Wf_bdd Wf_meas kA kA_nonneg)
open HRS.MS.S111X2 (s111x2_L s111x2_cb1_bounds s111x2_gradient_continuous s111x2_norm_gradient)

variable {d : ℕ}

/-- The screened forcing `r ↦ -∑ ∬ κ_{f_i} h_{i+1} h_{i+2} + (2/β) ∑ ∫ ⟨∇f_i,∇f_{i+1}⟩ h_{i+2}` (Pro `R26-T6.D00`). -/
def k4_screenedForcing {d : ℕ} (s β : ℝ) (μ : Measure (Euc d)) (f h : Fin 3 → ℝ → Euc d → ℝ) (r : ℝ) : ℝ :=
  -(∑ i : Fin 3, ∫ xy, commutatorKernel d s (gradient (f i r)) xy.1 xy.2 *
      h (i + 1) r xy.1 * h (i + 2) r xy.2 ∂(μ.prod μ)) +
    (2 / β) * ∑ i : Fin 3, ∫ x, inner ℝ (gradient (f i r) x) (gradient (f (i + 1) r) x) *
      h (i + 2) r x ∂μ

/-- The per-index identity. -/
theorem k4_static_index (hd : 2 ≤ d) (s a β : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (ha : 0 < a)
    (hβ : 0 < β) (ρ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s a β ρ)
    (fi fj fk hj hk : Euc d → ℝ) (hfi : MemCb 2 fi) (hfj : MemCb 2 fj) (hfk : MemCb 2 fk)
    (hhj : MemCb 2 hj) (hhk : MemCb 2 hk)
    (hrj : HRS.Whole.IsResponse (rieszKernel d s) (HRS.Whole.withDensityReal ρ) β fj hj)
    (hrk : HRS.Whole.IsResponse (rieszKernel d s) (HRS.Whole.withDensityReal ρ) β fk hk) :
    (∫ x, β⁻¹ * s111x2_L ρ fi x * hj x * hk x ∂(HRS.Whole.withDensityReal ρ)) =
      β⁻¹ * ((∫ x, inner ℝ (gradient fi x) (gradient fj x) * hk x ∂(HRS.Whole.withDensityReal ρ)) +
        ∫ x, inner ℝ (gradient fi x) (gradient fk x) * hj x ∂(HRS.Whole.withDensityReal ρ)) -
      ∫ xy, commutatorKernel d s (gradient fi) xy.1 xy.2 * hj xy.1 * hk xy.2
        ∂((HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ)) := by
  obtain ⟨M, T⟩ := HRS.MS.S111X2.s111x2_td_of_thermal hd hs0 hs ha hβ hρ
  haveI := HRS.Whole.Q34.isProbabilityMeasure_nu T.prob
  have K := T.en.K
  set μ := HRS.Whole.withDensityReal ρ with hμ
  obtain ⟨hic, Bi0, Bi1, hi0, hi1⟩ := s111x2_cb1_bounds (k4_cb1_of_cb2 hfi)
  obtain ⟨hjc, Bj0, Bj1, hj0, hj1⟩ := s111x2_cb1_bounds (k4_cb1_of_cb2 hfj)
  obtain ⟨hkc, Bk0, Bk1, hk0, hk1⟩ := s111x2_cb1_bounds (k4_cb1_of_cb2 hfk)
  obtain ⟨hhjc, Bhj0, Bhj1, hhj0, hhj1⟩ := s111x2_cb1_bounds (k4_cb1_of_cb2 hhj)
  obtain ⟨hhkc, Bhk0, Bhk1, hhk0, hhk1⟩ := s111x2_cb1_bounds (k4_cb1_of_cb2 hhk)
  have hgi := s111x2_gradient_continuous hic
  have hgj := s111x2_gradient_continuous hjc
  have hgk := s111x2_gradient_continuous hkc
  have hBi : ∀ y, ‖gradient fi y‖ ≤ Bi1 := fun y => by rw [s111x2_norm_gradient]; exact hi1 y
  have hBj : ∀ y, ‖gradient fj y‖ ≤ Bj1 := fun y => by rw [s111x2_norm_gradient]; exact hj1 y
  have hBk : ∀ y, ‖gradient fk y‖ ≤ Bk1 := fun y => by rw [s111x2_norm_gradient]; exact hk1 y
  have hBhj : ∀ y, |hj y| ≤ Bhj0 := fun y => by simpa using hhj0 y
  have hBhk : ∀ y, |hk y| ≤ Bhk0 := fun y => by simpa using hhk0 y
  have hBi0 : 0 ≤ Bi1 := (norm_nonneg _).trans (hBi 0)
  have hBj0 : 0 ≤ Bj1 := (norm_nonneg _).trans (hBj 0)
  have hBk0 : 0 ≤ Bk1 := (norm_nonneg _).trans (hBk 0)
  have hBhj0 : 0 ≤ Bhj0 := (abs_nonneg _).trans (hBhj 0)
  have hBhk0 : 0 ≤ Bhk0 := (abs_nonneg _).trans (hBhk 0)
  have hA0 := kA_nonneg K
  have hhjm : Measurable hj := hhjc.continuous.measurable
  have hhkm : Measurable hk := hhkc.continuous.measurable
  -- P04 and P03
  have h4 := k4_weighted_triple_ibp hd s a β hs0 hs ha hβ ρ hρ fi hj hk hfi hhj hhk
  have g3j := k4_response_gradient hd s a β hs0 hs ha hβ ρ hρ fj hj hfj hhj hrj
  have g3k := k4_response_gradient hd s a β hs0 hs ha hβ ρ hρ fk hk hfk hhk hrk
  -- the four bounded integrable functions
  have iF1 : Integrable (fun x => inner ℝ (gradient fi x) (gradient fj x) * hk x) μ := by
    refine Integrable.of_bound ((hgi.inner hgj).mul hhkc.continuous).aestronglyMeasurable (Bi1 * Bj1 * Bhk0)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul ((abs_real_inner_le_norm _ _).trans (mul_le_mul (hBi x) (hBj x) (norm_nonneg _) hBi0))
      (hBhk x) (abs_nonneg _) (mul_nonneg hBi0 hBj0)
  have iF2 : Integrable (fun x => inner ℝ (gradient fi x) (gradient fk x) * hj x) μ := by
    refine Integrable.of_bound ((hgi.inner hgk).mul hhjc.continuous).aestronglyMeasurable (Bi1 * Bk1 * Bhj0)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul ((abs_real_inner_le_norm _ _).trans (mul_le_mul (hBi x) (hBk x) (norm_nonneg _) hBi0))
      (hBhj x) (abs_nonneg _) (mul_nonneg hBi0 hBk0)
  have iF3 : Integrable (fun x => hk x * inner ℝ (gradient fi x) (Wf d s ρ hj x)) μ := by
    refine Integrable.of_bound (hhkc.continuous.measurable.aestronglyMeasurable.mul
      ((Measurable.inner hgi.measurable (Wf_meas K hhjm)).aestronglyMeasurable)) (Bhk0 * (Bi1 * (kA d s M ρ * Bhj0)))
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hBhk x) ((abs_real_inner_le_norm _ _).trans
      (mul_le_mul (hBi x) (Wf_bdd K hBhj x) (norm_nonneg _) hBi0)) (abs_nonneg _) hBhk0
  have iF4 : Integrable (fun x => hj x * inner ℝ (gradient fi x) (Wf d s ρ hk x)) μ := by
    refine Integrable.of_bound (hhjc.continuous.measurable.aestronglyMeasurable.mul
      ((Measurable.inner hgi.measurable (Wf_meas K hhkm)).aestronglyMeasurable)) (Bhj0 * (Bi1 * (kA d s M ρ * Bhk0)))
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hBhj x) ((abs_real_inner_le_norm _ _).trans
      (mul_le_mul (hBi x) (Wf_bdd K hBhk x) (norm_nonneg _) hBi0)) (abs_nonneg _) hBhj0
  have hsplit := k4_comm_split_nu K T.prob (a := gradient fi) hgi.measurable hBi hhjm hBhj hhkm hBhk
  have hpt : ∀ x, inner ℝ (gradient fi x) (gradient hj x) * hk x + inner ℝ (gradient fi x) (gradient hk x) * hj x =
      (inner ℝ (gradient fi x) (gradient fj x) * hk x + inner ℝ (gradient fi x) (gradient fk x) * hj x) -
        β * (hk x * inner ℝ (gradient fi x) (Wf d s ρ hj x) + hj x * inner ℝ (gradient fi x) (Wf d s ρ hk x)) := by
    intro x
    rw [g3j x, g3k x, inner_sub_right, inner_sub_right, inner_smul_right, inner_smul_right]
    ring
  have hL : (∫ x, β⁻¹ * s111x2_L ρ fi x * hj x * hk x ∂μ) = β⁻¹ * ∫ x, s111x2_L ρ fi x * hj x * hk x ∂μ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    ring
  rw [hL, h4]
  simp_rw [hpt]
  have iA : Integrable (fun x => inner ℝ (gradient fi x) (gradient fj x) * hk x +
      inner ℝ (gradient fi x) (gradient fk x) * hj x) μ := iF1.add iF2
  have iB : Integrable (fun x => hk x * inner ℝ (gradient fi x) (Wf d s ρ hj x) +
      hj x * inner ℝ (gradient fi x) (Wf d s ρ hk x)) μ := iF3.add iF4
  rw [integral_sub iA (iB.const_mul β), integral_add iF1 iF2, integral_const_mul, integral_add iF3 iF4]
  rw [← hsplit]
  have e : (∫ x, hj x * inner ℝ (gradient fi x) (Wf d s ρ hk x) ∂μ) + (∫ x, hk x * inner ℝ (gradient fi x) (Wf d s ρ hj x) ∂μ) =
      (∫ x, hk x * inner ℝ (gradient fi x) (Wf d s ρ hj x) ∂μ) + (∫ x, hj x * inner ℝ (gradient fi x) (Wf d s ρ hk x) ∂μ) := add_comm _ _
  rw [e]
  field_simp

theorem k4_fin3_add (i : Fin 3) : i + 1 + 2 = i ∧ i + 1 + 1 = i + 2 := by
  fin_cases i <;> decide

/-- Pro `R26-T6C.P06`: the static screened cubic identity with exact signs. -/
theorem k4_static_screened_triple (hd : 2 ≤ d) (s a β : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (ha : 0 < a)
    (hβ : 0 < β) (ρ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s a β ρ) (f h : Fin 3 → Euc d → ℝ)
    (hf : ∀ i, MemCb 2 (f i)) (hh : ∀ i, MemCb 2 (h i))
    (hresp : ∀ i, HRS.Whole.IsResponse (rieszKernel d s) (HRS.Whole.withDensityReal ρ) β (f i) (h i)) :
    (∑ i : Fin 3, ∫ x, β⁻¹ * s111x2_L ρ (f i) x * h (i + 1) x * h (i + 2) x ∂(HRS.Whole.withDensityReal ρ)) =
      k4_screenedForcing s β (HRS.Whole.withDensityReal ρ) (fun i _ => f i) (fun i _ => h i) 0 := by
  have per : ∀ i : Fin 3, (∫ x, β⁻¹ * s111x2_L ρ (f i) x * h (i + 1) x * h (i + 2) x ∂(HRS.Whole.withDensityReal ρ)) =
      β⁻¹ * ((∫ x, inner ℝ (gradient (f i) x) (gradient (f (i + 1)) x) * h (i + 2) x ∂(HRS.Whole.withDensityReal ρ)) +
        ∫ x, inner ℝ (gradient (f i) x) (gradient (f (i + 2)) x) * h (i + 1) x ∂(HRS.Whole.withDensityReal ρ)) -
      ∫ xy, commutatorKernel d s (gradient (f i)) xy.1 xy.2 * h (i + 1) xy.1 * h (i + 2) xy.2
        ∂((HRS.Whole.withDensityReal ρ).prod (HRS.Whole.withDensityReal ρ)) := fun i =>
    k4_static_index hd s a β hs0 hs ha hβ ρ hρ (f i) (f (i + 1)) (f (i + 2)) (h (i + 1)) (h (i + 2))
      (hf i) (hf (i + 1)) (hf (i + 2)) (hh (i + 1)) (hh (i + 2)) (hresp (i + 1)) (hresp (i + 2))
  simp_rw [per]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_add_distrib]
  have hre : (∑ i : Fin 3, ∫ x, inner ℝ (gradient (f i) x) (gradient (f (i + 2)) x) * h (i + 1) x
      ∂(HRS.Whole.withDensityReal ρ)) =
      ∑ i : Fin 3, ∫ x, inner ℝ (gradient (f i) x) (gradient (f (i + 1)) x) * h (i + 2) x
        ∂(HRS.Whole.withDensityReal ρ) := by
    rw [← Equiv.sum_comp (Equiv.addRight (1 : Fin 3))]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Equiv.coe_addRight]
    rw [(k4_fin3_add i).1, (k4_fin3_add i).2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [real_inner_comm]
  rw [hre]
  unfold k4_screenedForcing
  field_simp
  ring

end HRS.MS.S111K4
