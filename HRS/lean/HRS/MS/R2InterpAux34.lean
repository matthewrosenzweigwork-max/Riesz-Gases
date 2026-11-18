import HRS.MS.R2InterpAux33

/-!
# S10.2 (worker S102), part 34 (packet S7): `obsCov(v) = obsCov(u) + ∫_{(v,u]} rate`
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2Interp

open HRS HRS.Whole

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ}

/-- Integrability of the (cut-off) Gram integrands `1[v ≤ t_k ∧ t_{k'}] ∫ ∇ψ_k·∇ψ_{k'} ρ_v` on `[0,T]`
(only the cut-off function matters: beyond `t_k` the propagator is an arbitrary choice). -/
abbrev S102GramInt (C : WholeCoeff d) (m : ℝ) {T : ℝ} (hT : 0 < T) (L : ℕ) : Prop :=
  ∀ k k' : Fin (s102_q d L), IntegrableOn (fun v => if v ≤ min (s102_tk hT L k) (s102_tk hT L k') then
    s102_gram C m hT L v k k' else 0) (Icc 0 T)

/-- The pure real-analysis identity behind the additivity of the covariance. -/
theorem s102_cov_split {G : ℝ → ℝ} {T : ℝ} (hG : IntegrableOn G (Icc 0 T)) {v u μ : ℝ} (hv : 0 ≤ v) (hvu : v ≤ u)
    (huT : u ≤ T) (hμ : μ ≤ T) (hμ0 : 0 ≤ μ) :
    ∫ r in Icc v μ, G r = (∫ r in Icc u μ, G r) + ∫ r in Ioc v u, (if r ≤ μ then G r else 0) := by
  classical
  have hint : ∀ a b, 0 ≤ a → b ≤ T → IntegrableOn G (Ioc a b) := fun a b ha hb =>
    hG.mono_set (Ioc_subset_Icc_self.trans (Icc_subset_Icc ha hb))
  by_cases h1 : μ < v
  · have e1 : Icc v μ = ∅ := Icc_eq_empty (not_le.2 h1)
    have e2 : Icc u μ = ∅ := Icc_eq_empty (not_le.2 (h1.trans_le hvu))
    have e3 : ∫ r in Ioc v u, (if r ≤ μ then G r else 0) = 0 := by
      refine setIntegral_eq_zero_of_forall_eq_zero fun r hr => ?_
      rw [if_neg (not_le.2 (h1.trans hr.1))]
    rw [e1, e2, e3]; simp
  · push Not at h1
    by_cases h2 : μ < u
    · have e2 : Icc u μ = ∅ := Icc_eq_empty (not_le.2 h2)
      have e3 : ∫ r in Ioc v u, (if r ≤ μ then G r else 0) = ∫ r in Ioc v μ, G r := by
        have hfun : (fun r => if r ≤ μ then G r else 0) = (Iic μ).indicator G := by
          funext r; simp [indicator]
        have hset : Ioc v u ∩ Iic μ = Ioc v μ := by
          ext r
          simp only [mem_inter_iff, mem_Ioc, mem_Iic]
          constructor
          · rintro ⟨⟨a, _⟩, c⟩; exact ⟨a, c⟩
          · rintro ⟨a, c⟩; exact ⟨⟨a, c.trans h2.le⟩, c⟩
        rw [hfun, setIntegral_indicator measurableSet_Iic, hset]
      rw [e2, e3]
      simp only [Measure.restrict_empty, integral_zero_measure, zero_add]
      exact (setIntegral_congr_set Ioc_ae_eq_Icc).symm
    · push Not at h2
      have e3 : ∫ r in Ioc v u, (if r ≤ μ then G r else 0) = ∫ r in Ioc v u, G r := by
        refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
        simp only [if_pos (hr.2.trans h2)]
      rw [e3, ← setIntegral_congr_set (Ioc_ae_eq_Icc (a := v) (b := μ)),
        ← setIntegral_congr_set (Ioc_ae_eq_Icc (a := u) (b := μ)),
        ← Set.Ioc_union_Ioc_eq_Ioc hvu h2, setIntegral_union (Set.Ioc_disjoint_Ioc_of_le le_rfl)
          measurableSet_Ioc (hint v u hv huT) (hint u μ (hv.trans hvu) hμ)]
      ring

theorem s102_obsCov_eq_rate (hT : 0 < T) (L : ℕ)
    (hG : S102GramInt C m hT L) {v u : ℝ} (hv : 0 ≤ v)
    (hvu : v ≤ u) (huT : u ≤ T) (k k' : Fin (s102_q d L)) :
    s102_obsCov C m (s102_tauk hT L) (s102_alk L) v k k' =
      s102_obsCov C m (s102_tauk hT L) (s102_alk L) u k k' + ∫ r in Ioc v u, s102_rateM C m hT L r k k' := by
  have hμT : min (s102_tk hT L k) (s102_tk hT L k') ≤ T :=
    (min_le_left _ _).trans (s102_tauk hT L k).2.2
  have hμ0 : 0 ≤ min (s102_tk hT L k) (s102_tk hT L k') :=
    le_min (s102_tauk hT L k).2.1 (s102_tauk hT L k').2.1
  have h0 := s102_cov_split (hG k k') hv hvu huT hμT hμ0
  have hc : ∀ w : ℝ, ∫ r in Icc w (min (s102_tk hT L k) (s102_tk hT L k')),
      (if r ≤ min (s102_tk hT L k) (s102_tk hT L k') then s102_gram C m hT L r k k' else 0) =
      ∫ r in Icc w (min (s102_tk hT L k) (s102_tk hT L k')), s102_gram C m hT L r k k' := fun w =>
    setIntegral_congr_fun measurableSet_Icc fun r hr => if_pos hr.2
  have h : (∫ r in Icc v (min (s102_tk hT L k) (s102_tk hT L k')), s102_gram C m hT L r k k') =
      (∫ r in Icc u (min (s102_tk hT L k) (s102_tk hT L k')), s102_gram C m hT L r k k') +
      ∫ r in Ioc v u, (if r ≤ min (s102_tk hT L k) (s102_tk hT L k') then s102_gram C m hT L r k k' else 0) := by
    have hnest : ∀ r : ℝ, (if r ≤ min (s102_tk hT L k) (s102_tk hT L k') then
        (if r ≤ min (s102_tk hT L k) (s102_tk hT L k') then s102_gram C m hT L r k k' else 0) else 0) =
        (if r ≤ min (s102_tk hT L k) (s102_tk hT L k') then s102_gram C m hT L r k k' else 0) := fun r => by
      by_cases hr : r ≤ min (s102_tk hT L k) (s102_tk hT L k') <;> simp [hr]
    rw [← hc v, ← hc u]
    simp only [hnest] at h0
    exact h0
  simp only [s102_obsCov, s102_rateM, Matrix.of_apply]
  have e : ∫ r in Ioc v u, 2 * C.ν * (if r ≤ min (s102_tk hT L k) (s102_tk hT L k') then
      s102_gram C m hT L r k k' else 0) = 2 * C.ν * ∫ r in Ioc v u,
      (if r ≤ min (s102_tk hT L k) (s102_tk hT L k') then s102_gram C m hT L r k k' else 0) :=
    integral_const_mul _ _
  rw [e]
  have h' : (∫ r in Icc v (min (s102_tk hT L k) (s102_tk hT L k')), s102_gram C m hT L r k k') =
      (∫ r in Icc u (min (s102_tk hT L k) (s102_tk hT L k')), s102_gram C m hT L r k k') +
      ∫ r in Ioc v u, (if r ≤ min (s102_tk hT L k) (s102_tk hT L k') then s102_gram C m hT L r k k' else 0) := h
  simp only [s102_gram, s102_tk] at h' ⊢
  rw [h']
  ring

end HRS.MS.R2Interp

end
