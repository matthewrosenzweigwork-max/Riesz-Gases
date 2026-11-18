import HRS.MS.SA16U3K7b

/-!
# S.A.16 K7, part (c): pointwise and integral decomposition at `θ = 1` (worker SA16U3)
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16Cutoff
open HRS HRS.Whole HRS.Whole.AppendixA HRS.CZ.Pv HRS.CZ.Pvk HRS.CZ.PvAsm HRS.CZ.ElemA Phase2SA16

section K7c
variable {d : ℕ}

lemma sa16u3_pt_decomp {μ : Euc d → ℝ} {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (x z : Euc d) (w : ℝ) :
    {z : Euc d | δ < ‖z‖}.indicator
        (fun z => (μ x - μ (x - z)) * w / ‖z‖ ^ ((d : ℝ) + 1)) z =
      sa16u3_kA d μ δ x z * w + ∑ i : Fin d, gradient μ x i *
        (pvkKtr (pvasmK d i) δ z * w - pvkKtr (pvasmK d i) 1 z * w) := by
  simp only [sa16u3_Ktr_formula hδ.le, sa16u3_Ktr_formula zero_le_one]
  by_cases h1 : δ < ‖z‖
  · rw [Set.indicator_of_mem (show z ∈ {z : Euc d | δ < ‖z‖} from h1)]
    by_cases h2 : ‖z‖ ≤ 1
    · have h3 : ¬ (1 : ℝ) < ‖z‖ := not_lt.2 h2
      have hs : ∑ i : Fin d, gradient μ x i * ((if δ < ‖z‖ then z i / ‖z‖ ^ ((d : ℝ) + 1) else 0) * w -
          (if (1 : ℝ) < ‖z‖ then z i / ‖z‖ ^ ((d : ℝ) + 1) else 0) * w) =
          fderiv ℝ μ x z / ‖z‖ ^ ((d : ℝ) + 1) * w := by
        rw [← elema_grad_sum, Finset.sum_div, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [if_pos h1, if_neg h3]
        ring
      rw [hs]
      unfold sa16u3_kA elema_R
      rw [if_pos ⟨h1, h2⟩]
      ring
    · have h3 : (1 : ℝ) < ‖z‖ := not_le.1 h2
      have hs : ∑ i : Fin d, gradient μ x i * ((if δ < ‖z‖ then z i / ‖z‖ ^ ((d : ℝ) + 1) else 0) * w -
          (if (1 : ℝ) < ‖z‖ then z i / ‖z‖ ^ ((d : ℝ) + 1) else 0) * w) = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [if_pos h1, if_pos h3, sub_self, mul_zero]
      rw [hs, add_zero]
      unfold sa16u3_kA
      rw [if_neg (fun h => h2 h.2), if_pos h3]
      ring
  · rw [Set.indicator_of_notMem (show z ∉ {z : Euc d | δ < ‖z‖} from h1)]
    have h2 : ¬ (1 : ℝ) < ‖z‖ := fun h => h1 (lt_of_le_of_lt hδ1 h)
    have hs : ∑ i : Fin d, gradient μ x i * ((if δ < ‖z‖ then z i / ‖z‖ ^ ((d : ℝ) + 1) else 0) * w -
        (if (1 : ℝ) < ‖z‖ then z i / ‖z‖ ^ ((d : ℝ) + 1) else 0) * w) = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [if_neg h1, if_neg h2]
      ring
    rw [hs]
    unfold sa16u3_kA
    rw [if_neg (fun h => h1 h.1), if_neg h2]
    ring

/-- integral decomposition of the commutator at `θ = 1` -/
lemma sa16u3_F_decomp (hd : 1 ≤ d) {μ : Euc d → ℝ} (hμ : ContDiff ℝ 2 μ) {B0 B2 : ℝ} (hB0 : 0 ≤ B0)
    (hB2 : 0 ≤ B2) (h0 : ∀ y, |μ y| ≤ B0) (h2 : ∀ y, ‖iteratedFDeriv ℝ 2 μ y‖ ≤ B2) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (W : SchwartzMap (Euc d) ℝ) {p : ℝ} (hp : 1 < p) (x : Euc d) :
    ∫ z in {z : Euc d | δ < ‖z‖}, (μ x - μ (x - z)) * W (x - z) / ‖z‖ ^ ((d : ℝ) + 1) =
      (∫ z, sa16u3_kA d μ δ x z * W (x - z)) + ∑ i : Fin d, gradient μ x i *
        (pvTrunc d 1 (fun v : Euc d => v i) W δ x - pvTrunc d 1 (fun v : Euc d => v i) W 1 x) := by
  have hKint : ∀ (ε : ℝ), 0 < ε → ∀ i : Fin d,
      Integrable (fun z => pvkKtr (pvasmK d i) ε z * W (x - z)) := fun ε hε i =>
    (pvasm_holder_int hp (pvasm_Ktr_meas hd i ε) W.continuous.measurable
      (pvasm_Lq_Ktr hd i (pvasm_conj_gt hp) hε) (W.memLp _ _) x).1
  have hS : MeasurableSet {z : Euc d | δ < ‖z‖} := measurableSet_lt measurable_const measurable_norm
  rw [← integral_indicator hS]
  have hfun : (fun z : Euc d => {z : Euc d | δ < ‖z‖}.indicator
      (fun z => (μ x - μ (x - z)) * W (x - z) / ‖z‖ ^ ((d : ℝ) + 1)) z) =
      fun z => sa16u3_kA d μ δ x z * W (x - z) + ∑ i : Fin d, gradient μ x i *
        (pvkKtr (pvasmK d i) δ z * W (x - z) - pvkKtr (pvasmK d i) 1 z * W (x - z)) :=
    funext fun z => sa16u3_pt_decomp hδ hδ1 x z (W (x - z))
  rw [hfun]
  have iS : ∀ i ∈ (Finset.univ : Finset (Fin d)), Integrable (fun z => gradient μ x i *
      (pvkKtr (pvasmK d i) δ z * W (x - z) - pvkKtr (pvasmK d i) 1 z * W (x - z))) :=
    fun i _ => ((hKint δ hδ i).sub (hKint 1 one_pos i)).const_mul _
  rw [integral_add (sa16u3_kA_int hd hμ hB0 hB2 h0 h2 hδ W x) (integrable_finset_sum _ iS),
    integral_finset_sum _ iS]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, integral_sub (hKint δ hδ i) (hKint 1 one_pos i), pvasm_trunc_eq, pvasm_trunc_eq]

end K7c
end HRS.Whole.AppendixA.Phase2SA16Cutoff
