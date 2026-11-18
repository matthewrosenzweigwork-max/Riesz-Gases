import HRS.MC.CepH0Aux1

/-!
# Packet CEPH0, auxiliary 5: the `EReal` bookkeeping of the entropy additivity
-/

open scoped ENNReal NNReal

noncomputable section

namespace HRS.MC.CepH0

theorem h0_coe_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∑ c ∈ s, f c : ℝ) : EReal) = ∑ c ∈ s, (f c : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, EReal.coe_add, ih]

theorem h0_term (p : ℝ) (hp : 0 ≤ p) (k : ℝ≥0∞) (L : ℝ) :
    (k ≠ ⊤ → (p : EReal) * ((k : EReal) - (L : EReal)) = ((p * (k.toReal - L) : ℝ) : EReal)) ∧
    (k = ⊤ → 0 < p → (p : EReal) * ((k : EReal) - (L : EReal)) = ⊤) ∧
    (k = ⊤ → p = 0 → (p : EReal) * ((k : EReal) - (L : EReal)) = 0) := by
  refine ⟨fun hk => ?_, fun hk hp0 => ?_, fun hk hp0 => ?_⟩
  · rw [← EReal.coe_ennreal_toReal hk, ← EReal.coe_sub, ← EReal.coe_mul]
  · subst hk
    rw [EReal.coe_ennreal_top, EReal.top_sub_coe, EReal.coe_mul_top_of_pos hp0]
  · subst hk
    rw [EReal.coe_ennreal_top, EReal.top_sub_coe, hp0]
    simp

theorem h0_esum_top {ι : Type*} [Fintype ι] (t : ι → EReal) (ht : ∀ c, t c ≠ ⊥) (c0 : ι)
    (h : t c0 = ⊤) : ∑ c, t c = ⊤ := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ c0), h]
  refine EReal.top_add_of_ne_bot ?_
  refine Finset.sum_induction t (fun x => x ≠ ⊥) (fun a b ha hb => EReal.add_ne_bot_iff.mpr ⟨ha, hb⟩)
    (by simp) (fun c _ => ht c)

theorem h0_ereal_mix {ι : Type*} [Fintype ι] (k : ι → ℝ≥0∞) (K : ℝ≥0∞) (L : ℝ) (p : ι → ℝ)
    (hp0 : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1)
    (htop : (∃ c, 0 < p c ∧ k c = ⊤) → K = ⊤)
    (hfin : (∀ c, 0 < p c → k c ≠ ⊤) → K ≠ ⊤ ∧
      K.toReal = ∑ c, p c * (k c).toReal + ∑ c, p c * Real.log (p c)) :
    (K : EReal) - (L : EReal) = ∑ c, (p c : EReal) * ((k c : EReal) - (L : EReal))
      + ∑ c, ((p c * Real.log (p c) : ℝ) : EReal) := by
  by_cases h : ∃ c, 0 < p c ∧ k c = ⊤
  · obtain ⟨c0, hc0, hk0⟩ := h
    rw [htop ⟨c0, hc0, hk0⟩, EReal.coe_ennreal_top, EReal.top_sub_coe]
    have hne : ∀ c, (p c : EReal) * ((k c : EReal) - (L : EReal)) ≠ ⊥ := by
      intro c
      by_cases hk : k c = ⊤
      · rcases (hp0 c).lt_or_eq with hc | hc
        · rw [(h0_term (p c) (hp0 c) (k c) L).2.1 hk hc]; simp
        · rw [(h0_term (p c) (hp0 c) (k c) L).2.2 hk hc.symm]; simp
      · rw [(h0_term (p c) (hp0 c) (k c) L).1 hk]; exact EReal.coe_ne_bot _
    rw [h0_esum_top _ hne c0 ((h0_term (p c0) (hp0 c0) (k c0) L).2.1 hk0 hc0)]
    rw [← h0_coe_sum]
    exact (EReal.top_add_coe _).symm
  · push_neg at h
    obtain ⟨hK, hKr⟩ := hfin fun c hc => h c hc
    have hterm : ∀ c, (p c : EReal) * ((k c : EReal) - (L : EReal))
        = ((p c * ((k c).toReal - L) : ℝ) : EReal) := by
      intro c
      by_cases hk : k c = ⊤
      · have : p c = 0 := by
          rcases (hp0 c).lt_or_eq with hc | hc
          · exact absurd hk (h c hc)
          · exact hc.symm
        rw [(h0_term (p c) (hp0 c) (k c) L).2.2 hk this, this]; simp
      · exact (h0_term (p c) (hp0 c) (k c) L).1 hk
    rw [← EReal.coe_ennreal_toReal hK, ← EReal.coe_sub]
    simp_rw [hterm]
    rw [← h0_coe_sum, ← h0_coe_sum, ← EReal.coe_add]
    congr 1
    rw [hKr]
    have : ∑ c, p c * ((k c).toReal - L) = ∑ c, p c * (k c).toReal - L := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hp1, one_mul]
    rw [this]; ring

end HRS.MC.CepH0
