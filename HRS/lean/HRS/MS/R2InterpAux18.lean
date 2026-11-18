import HRS.MS.R2InterpAux17

/-!
# S10.2 (worker S102), part 18 (packet I4): the drift measure `𝒟_b`

`g_{a,a'}(t) = ∫_{(a, a'∧t]} V^{t,u}b(u) du`.  Under `S102Drift`: `‖g_{a,a'}(t)‖ ≤ K_V ∫_{(a,a'∧t]} Mb`, `g` is continuous in `t`
(so `r2DriftInc` is not the junk zero path), additive in the interval, and `‖𝒟_b((a,a'])‖ ≤ K_V ∫_{(a,a']} Mb`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas HRS.MS.FixEq

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ} {Pw : ℝ}
  {b : ℝ → (Euc d → ℝ) → ℝ} {Mb : ℝ → ℝ}

/-- The value at time `t` of the increment `𝒟_b((a,a'])`. -/
def s102_g (C : WholeCoeff d) (m : ℝ) (b : ℝ → (Euc d → ℝ) → ℝ) (a a' t : ℝ) : OscDual d m :=
  ∫ u in Ioc a (min a' t), s102_w C m b u t

theorem s102_g_norm_le (hP : (d : ℝ) < 2 * Pw) (hD : S101Data C m T r c) (hlin : S102Lin C m T)
    (hb : S102Drift C m T r Pw b Mb) {a a' t : ℝ} (ha : 0 ≤ a) (ht : t ∈ Icc (0 : ℝ) T) :
    ‖s102_g C m b a a' t‖ ≤ s102_KV d r Pw c * ∫ u in Ioc a (min a' t), Mb u := by
  have hs : Ioc a (min a' t) ⊆ Icc 0 t := fun u hu => ⟨ha.trans hu.1.le, hu.2.trans (min_le_right _ _)⟩
  have hI : IntegrableOn Mb (Ioc a (min a' t)) :=
    hb.Mb_int.mono_set (hs.trans (Icc_subset_Icc le_rfl ht.2))
  unfold s102_g
  calc _ ≤ ∫ u in Ioc a (min a' t), Mb u * s102_KV d r Pw c :=
        norm_integral_le_of_norm_le (hI.mul_const _)
          ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun u hu =>
            s102_w_norm_le hP hD hlin hb ht (hs hu)))
    _ = _ := by rw [integral_mul_const]; ring

/-- The primitive of `Mb`. -/
def s102_H (Mb : ℝ → ℝ) (s : ℝ) : ℝ := ∫ x in (0 : ℝ)..s, Mb x

theorem s102_H_continuousOn (hT : 0 ≤ T) (hMb : IntegrableOn Mb (Icc 0 T)) :
    ContinuousOn (s102_H Mb) (Icc 0 T) := by
  have : IntegrableOn Mb (uIcc 0 T) := by rwa [uIcc_of_le hT]
  have h := intervalIntegral.continuousOn_primitive_interval this
  rwa [uIcc_of_le hT] at h

theorem s102_setIntegral_Mb {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) (hq : q ≤ T)
    (hMb : IntegrableOn Mb (Icc 0 T)) : ∫ u in Ioc p q, Mb u = s102_H Mb q - s102_H Mb p := by
  unfold s102_H
  have h1 : IntervalIntegrable Mb volume 0 p := by
    refine (intervalIntegrable_iff_integrableOn_Icc_of_le hp).2 (hMb.mono_set (Icc_subset_Icc le_rfl (hpq.trans hq)))
  have h2 : IntervalIntegrable Mb volume p q := by
    refine (intervalIntegrable_iff_integrableOn_Icc_of_le hpq).2
      (hMb.mono_set (Icc_subset_Icc hp hq))
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2, add_sub_cancel_left,
    intervalIntegral.integral_of_le hpq]

/-- Difference of the drift increment at two times. -/
theorem s102_g_diff (hP : (d : ℝ) < 2 * Pw) (hD : S101Data C m T r c) (hlin : S102Lin C m T)
    (hb : S102Drift C m T r Pw b Mb) {a a' t' t : ℝ} (ha : 0 ≤ a) (ha' : 0 ≤ a')
    (ht' : t' ∈ Icc (0 : ℝ) T) (ht : t ∈ Icc (0 : ℝ) T) (htt : t' ≤ t) :
    ‖s102_g C m b a a' t - s102_g C m b a a' t'‖ ≤ s102_KV d r Pw c *
      ((t - t') * (∫ u in Icc 0 T, Mb u) + (s102_H Mb (min a' t) - s102_H Mb (min a' t'))) := by
  set KV := s102_KV d r Pw c with hKV
  have hKV0 : 0 ≤ KV := s102_KV_nonneg d r Pw c
  set p := min a' t' with hp
  set q := min a' t with hq
  have hp0 : 0 ≤ p := le_min ha' ht'.1
  have hpq : p ≤ q := min_le_min le_rfl htt
  have hqT : q ≤ T := (min_le_right _ _).trans ht.2
  have hI0 : 0 ≤ ∫ u in Icc 0 T, Mb u := setIntegral_nonneg measurableSet_Icc (fun u _ => hb.Mb_nonneg u)
  have hHpq : s102_H Mb q - s102_H Mb p = ∫ u in Ioc p q, Mb u :=
    (s102_setIntegral_Mb hp0 hpq hqT hb.Mb_int).symm
  have hHnn : 0 ≤ s102_H Mb q - s102_H Mb p := by
    rw [hHpq]; exact setIntegral_nonneg measurableSet_Ioc (fun u _ => hb.Mb_nonneg u)
  by_cases hap : a ≤ p
  · -- main case
    have hsub1 : Ioc a p ⊆ Icc 0 t' := fun u hu => ⟨ha.trans hu.1.le, hu.2.trans (min_le_right _ _)⟩
    have hsub1t : Ioc a p ⊆ Icc 0 t := hsub1.trans (Icc_subset_Icc le_rfl htt)
    have hsub2 : Ioc p q ⊆ Icc 0 t := fun u hu => ⟨hp0.trans hu.1.le, hu.2.trans (min_le_right _ _)⟩
    have hint1 : IntegrableOn (fun u => s102_w C m b u t) (Ioc a p) :=
      s102_w_integrableOn hP hD hlin hb ht hsub1t measurableSet_Ioc
    have hint1' : IntegrableOn (fun u => s102_w C m b u t') (Ioc a p) :=
      s102_w_integrableOn hP hD hlin hb ht' hsub1 measurableSet_Ioc
    have hint2 : IntegrableOn (fun u => s102_w C m b u t) (Ioc p q) :=
      s102_w_integrableOn hP hD hlin hb ht hsub2 measurableSet_Ioc
    have hg : s102_g C m b a a' t - s102_g C m b a a' t' =
        (∫ u in Ioc a p, (s102_w C m b u t - s102_w C m b u t')) + ∫ u in Ioc p q, s102_w C m b u t := by
      unfold s102_g
      rw [integral_sub hint1 hint1', ← hp, ← hq,
        ← Set.Ioc_union_Ioc_eq_Ioc hap hpq, setIntegral_union (Set.Ioc_disjoint_Ioc_of_le le_rfl)
          measurableSet_Ioc hint1 hint2]
      abel
    rw [hg]
    have h1 : ‖∫ u in Ioc a p, (s102_w C m b u t - s102_w C m b u t')‖ ≤ KV * ((t - t') * ∫ u in Icc 0 T, Mb u) := by
      have hI : IntegrableOn Mb (Ioc a p) := hb.Mb_int.mono_set (hsub1.trans (Icc_subset_Icc le_rfl ht'.2))
      calc _ ≤ ∫ u in Ioc a p, Mb u * KV * (t - t') :=
            norm_integral_le_of_norm_le ((hI.mul_const _).mul_const _)
              ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun u hu => by
                have hu' := hsub1 hu
                have huT : u ∈ Icc (0 : ℝ) T := ⟨hu'.1, hu'.2.trans ht'.2⟩
                have := s102_Vprop_lip_M hP hD (hb.hZ u huT) hlin (hb.hM u huT) huT
                  (t' := t') (t := t) ⟨hu'.2, ht'.2⟩ ⟨hu'.2.trans htt, ht.2⟩ htt
                rw [abs_of_nonneg (hb.Mb_nonneg u)] at this
                exact this))
        _ = (∫ u in Ioc a p, Mb u) * KV * (t - t') := by rw [integral_mul_const, integral_mul_const]
        _ ≤ (∫ u in Icc 0 T, Mb u) * KV * (t - t') := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hKV0) (sub_nonneg.2 htt)
            exact setIntegral_mono_set hb.Mb_int (Filter.Eventually.of_forall fun u => hb.Mb_nonneg u)
              (Filter.Eventually.of_forall (hsub1.trans (Icc_subset_Icc le_rfl ht'.2)))
        _ = _ := by ring
    have h2 : ‖∫ u in Ioc p q, s102_w C m b u t‖ ≤ KV * (s102_H Mb q - s102_H Mb p) := by
      have hI : IntegrableOn Mb (Ioc p q) := hb.Mb_int.mono_set (hsub2.trans (Icc_subset_Icc le_rfl ht.2))
      calc _ ≤ ∫ u in Ioc p q, Mb u * KV :=
            norm_integral_le_of_norm_le (hI.mul_const _)
              ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun u hu =>
                s102_w_norm_le hP hD hlin hb ht (hsub2 hu)))
        _ = _ := by rw [integral_mul_const, hHpq]; ring
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ KV * ((t - t') * ∫ u in Icc 0 T, Mb u) + KV * (s102_H Mb q - s102_H Mb p) := add_le_add h1 h2
      _ = _ := by ring
  · -- `p < a`: the earlier increment is empty
    have hpa : p < a := not_le.1 hap
    have hg0 : s102_g C m b a a' t' = 0 := by
      unfold s102_g
      rw [← hp, Set.Ioc_eq_empty (not_lt.2 hpa.le)]
      simp
    rw [hg0, sub_zero]
    have h3 := s102_g_norm_le hP hD hlin hb (a' := a') ha ht
    rw [← hq] at h3
    have h4 : ∫ u in Ioc a q, Mb u ≤ ∫ u in Ioc p q, Mb u :=
      setIntegral_mono_set (hb.Mb_int.mono_set ((Ioc_subset_Icc_self.trans
        (Icc_subset_Icc hp0 hqT)))) (Filter.Eventually.of_forall fun u => hb.Mb_nonneg u)
        (Filter.Eventually.of_forall (Ioc_subset_Ioc_left hpa.le))
    calc _ ≤ KV * ∫ u in Ioc a q, Mb u := h3
      _ ≤ KV * ∫ u in Ioc p q, Mb u := mul_le_mul_of_nonneg_left h4 hKV0
      _ = KV * (s102_H Mb q - s102_H Mb p) := by rw [hHpq]
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left ?_ hKV0
          have : 0 ≤ (t - t') * ∫ u in Icc 0 T, Mb u := mul_nonneg (sub_nonneg.2 htt) hI0
          linarith

end HRS.MS.R2Interp

end
