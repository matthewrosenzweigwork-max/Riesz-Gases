import HRS.MC.S7WQAux1

/-!
# Packet `s7_WQ_weak_ui_wasserstein`, helper 2: two measures on a common finite set, and tail estimates
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.WQ

open HRS

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  [SecondCountableTopology B] [MeasurableSpace B] [BorelSpace B]

lemma wq_discrete {p : ℝ} (hp : 1 ≤ p) {L : ℕ} (z : Fin L → B) (w w' : Fin L → ℝ) (hw : ∀ k, 0 ≤ w k)
    (hw' : ∀ k, 0 ≤ w' k) (hs : ∑ k, w k = 1) (hs' : ∑ k, w' k = 1) (D : ℝ) (hD0 : 0 ≤ D)
    (hD : ∀ k l, ‖z k - z l‖ ≤ D) {θ : ℝ} (hθ : 0 ≤ θ) (hθD : D ^ p * ∑ k, |w k - w' k| ≤ θ ^ p) :
    wassersteinE p (∑ k, ENNReal.ofReal (w k) • Measure.dirac (z k))
      (∑ k, ENNReal.ofReal (w' k) • Measure.dirac (z k)) ≤ ENNReal.ofReal θ := by
  classical
  set m : Fin L → ℝ := fun k => min (w k) (w' k) with hm
  have hm0 : ∀ k, 0 ≤ m k := fun k => le_min (hw k) (hw' k)
  have hmw : ∀ k, m k ≤ w k := fun k => min_le_left _ _
  have hmw' : ∀ k, m k ≤ w' k := fun k => min_le_right _ _
  set s : ℝ := ∑ k, (w k - m k) with hsdef
  have hs2 : ∑ k, (w' k - m k) = s := by
    simp only [hsdef, Finset.sum_sub_distrib, hs, hs']
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun k _ => sub_nonneg.2 (hmw k)
  set π : Fin L × Fin L → ℝ := fun q =>
    (if q.1 = q.2 then m q.1 else 0) + (w q.1 - m q.1) * (w' q.2 - m q.2) / s with hπ
  have hπ0 : ∀ q, 0 ≤ π q := fun q => by
    simp only [hπ]
    refine add_nonneg (by split_ifs; exacts [hm0 _, le_rfl]) ?_
    exact div_nonneg (mul_nonneg (sub_nonneg.2 (hmw _)) (sub_nonneg.2 (hmw' _))) hs0
  have hrow : ∀ k, ∑ l, π (k, l) = w k := by
    intro k
    simp only [hπ, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true, hs2]
    by_cases h : s = 0
    · have : w k - m k = 0 := by
        have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sub_nonneg.2 (hmw j))).1 h k (Finset.mem_univ k)
        exact h1
      have e : m k = w k := by linarith
      simp [e]
    · field_simp; ring
  have hcol : ∀ l, ∑ k, π (k, l) = w' l := by
    intro l
    simp only [hπ, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_div, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
    have e : ∑ k, (w k - m k) = s := rfl
    rw [e]
    by_cases h : s = 0
    · have : w' l - m l = 0 := by
        have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sub_nonneg.2 (hmw' j))).1
          (hs2.trans h) l (Finset.mem_univ l)
        exact h1
      have e : m l = w' l := by linarith
      simp [e]
    · field_simp; ring
  have hcoup := coupling_sum_dirac z π w w' hπ0 hrow hcol
  have hp0 : 0 < p := by linarith
  refine wq_le_of_cost hp hcoup hθ hθD ?_
  have hmeas : Measurable fun x : B × B => ENNReal.ofReal (‖x.1 - x.2‖ ^ p) :=
    ENNReal.measurable_ofReal.comp (((measurable_fst.sub measurable_snd).norm).pow_const p)
  rw [lintegral_finsetSum_measure]
  simp only [lintegral_smul_measure, lintegral_dirac' _ hmeas, smul_eq_mul]
  simp_rw [← ENNReal.ofReal_mul (hπ0 _)]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun q _ => mul_nonneg (hπ0 q) (Real.rpow_nonneg (norm_nonneg _) p))]
  refine ENNReal.ofReal_le_ofReal ?_
  -- cost estimate
  have hterm : ∀ q : Fin L × Fin L, π q * ‖z q.1 - z q.2‖ ^ p ≤
      D ^ p * ((w q.1 - m q.1) * (w' q.2 - m q.2) / s) := by
    intro q
    simp only [hπ]
    by_cases hq : q.1 = q.2
    · rw [show (if q.1 = q.2 then m q.1 else 0) = m q.1 by simp [hq], hq, sub_self, norm_zero]
      have : 0 ≤ (w q.2 - m q.2) * (w' q.2 - m q.2) / s :=
        div_nonneg (mul_nonneg (sub_nonneg.2 (hmw _)) (sub_nonneg.2 (hmw' _))) hs0
      have h2 : 0 ≤ D ^ p := Real.rpow_nonneg hD0 p
      rw [Real.zero_rpow hp0.ne', mul_zero]
      positivity
    · rw [show (if q.1 = q.2 then m q.1 else 0) = 0 by simp [hq], zero_add]
      have hD2 : ‖z q.1 - z q.2‖ ^ p ≤ D ^ p := by
        have := hD q.1 q.2
        exact Real.rpow_le_rpow (norm_nonneg _) this hp0.le
      have hnn : 0 ≤ (w q.1 - m q.1) * (w' q.2 - m q.2) / s :=
        div_nonneg (mul_nonneg (sub_nonneg.2 (hmw _)) (sub_nonneg.2 (hmw' _))) hs0
      calc _ ≤ _ := mul_le_mul_of_nonneg_left hD2 hnn
        _ = _ := mul_comm _ _
  have htot : ∑ q : Fin L × Fin L, (w q.1 - m q.1) * (w' q.2 - m q.2) / s ≤ s := by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, ← Finset.sum_div, hs2, ← Finset.sum_mul]
    have e : ∑ k, (w k - m k) = s := rfl
    rw [e]
    by_cases h : s = 0
    · simp [h]
    · rw [div_le_iff₀ (lt_of_le_of_ne hs0 (Ne.symm h))]
  have hsle : s ≤ ∑ k, |w k - w' k| := by
    refine Finset.sum_le_sum fun k _ => ?_
    have : w k - m k ≤ |w k - w' k| := by
      simp only [hm]
      rcases le_total (w k) (w' k) with h | h
      · rw [min_eq_left h]; simp
      · rw [min_eq_right h]; exact le_abs_self _
    exact this
  calc ∑ q : Fin L × Fin L, π q * ‖z q.1 - z q.2‖ ^ p
      ≤ ∑ q : Fin L × Fin L, D ^ p * ((w q.1 - m q.1) * (w' q.2 - m q.2) / s) :=
        Finset.sum_le_sum fun q _ => hterm q
    _ = D ^ p * ∑ q : Fin L × Fin L, (w q.1 - m q.1) * (w' q.2 - m q.2) / s := by
        rw [← Finset.mul_sum]
    _ ≤ D ^ p * ∑ k, |w k - w' k| :=
        mul_le_mul_of_nonneg_left (htot.trans hsle) (Real.rpow_nonneg hD0 p)


end HRS.MC.Sec7.WQ
