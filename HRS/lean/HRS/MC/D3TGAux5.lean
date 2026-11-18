import HRS.MC.D3TGAux4

/-!
# Packet D3TG, helper 5: integrated bounds for the derivatives of the tail integral `H_λ`
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal ContDiff

namespace HRS.MC.D3TG

open HRS HRS.MC.D3EW HRS.MC.Per HRS.MC.D3T1 HRS.MC.FDLE

variable {d : ℕ}

/-- Tail integral of the power function against the indicator of `[c, ∞)`. -/
lemma d3tg_tail {e c κ : ℝ} (he : 0 < e) (hc : 0 < c) (hκ : 0 ≤ κ) (J : Set ℝ) :
    ∫ t in J, (Ici c).indicator (fun t : ℝ => κ * t ^ (-e - 1)) t ≤ κ * (c ^ (-e) / e) := by
  have hint : IntegrableOn (fun t : ℝ => t ^ (-e - 1)) (Ioi c) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hc
  have hint0 : IntegrableOn (fun t : ℝ => t ^ (-e - 1)) (Ici c) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact hint
  have hint' : IntegrableOn (fun t : ℝ => κ * t ^ (-e - 1)) (Ici c) := hint0.const_mul κ
  rw [setIntegral_indicator measurableSet_Ici]
  calc ∫ t in J ∩ Ici c, κ * t ^ (-e - 1)
      ≤ ∫ t in Ici c, κ * t ^ (-e - 1) := by
        refine setIntegral_mono_set hint' ?_ (Filter.Eventually.of_forall fun x hx => hx.2)
        filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
        have : 0 < t := lt_of_lt_of_le hc ht
        exact mul_nonneg hκ (Real.rpow_nonneg this.le _)
    _ = κ * (c ^ (-e) / e) := by
        rw [integral_const_mul, integral_Ici_eq_integral_Ioi, integral_Ioi_rpow_of_lt (by linarith) hc]
        congr 1
        rw [show -e - 1 + 1 = -e by ring]
        field_simp

theorem d3tgH_deriv_bound (hd : 1 ≤ d) {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {s : ℝ} (hs0 : 0 ≤ s)
    (hsd : s < d) (b : ℝ) (j : ℕ) :
    ∃ A T : ℝ, 0 ≤ A ∧ 0 ≤ T ∧ ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ (y : Euc d) (a : ℝ),
      (∀ n : Lattice d, a ≤ ‖y + Lattice.toEuc n‖) →
      ‖iteratedFDeriv ℝ j (d3tgH ψ s b lam) y‖ ≤
        (∫ t in Ioc lam 1, (Ici (max lam a)).indicator
          (fun t : ℝ => A * t ^ (-((j : ℝ) + s) - 1)) t) + T := by
  obtain ⟨A, A', Cl, hA, hA', hCl, hb⟩ := d3tgK_bound hd hψ s b j
  have hr : -1 < (d : ℝ) - s - 1 := by linarith
  have hT1int : IntegrableOn (fun t : ℝ => t ^ ((d : ℝ) - s - 1)) (Ioc 0 1) :=
    (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) hr).1
  set T1 : ℝ := ∫ t in Ioc (0 : ℝ) 1, t ^ ((d : ℝ) - s - 1) with hT1
  set T2 : ℝ := ∫ t in Ioi (1 : ℝ), t ^ (-s - 2) with hT2
  have hT1nn : 0 ≤ T1 := setIntegral_nonneg measurableSet_Ioc fun t ht => Real.rpow_nonneg ht.1.le _
  have hT2nn : 0 ≤ T2 := setIntegral_nonneg measurableSet_Ioi fun t ht =>
    Real.rpow_nonneg (lt_trans one_pos ht).le _
  refine ⟨A, A' * T1 + Cl * T2, hA, by positivity, fun lam hl0 hl1 y a ha => ?_⟩
  rw [d3tgH_iter hd hψ hs0 b hl0 hl1 j y]
  set c : ℝ := max lam a with hc
  have hcpos : 0 < c := lt_of_lt_of_le hl0 (le_max_left _ _)
  set g1 : ℝ → ℝ := (Ici c).indicator (fun t : ℝ => A * t ^ (-((j : ℝ) + s) - 1)) with hg1
  set g2 : ℝ → ℝ := fun t => A' * t ^ ((d : ℝ) - s - 1) with hg2
  set g3 : ℝ → ℝ := fun t => Cl * t ^ (-s - 2) with hg3
  have hg1i : IntegrableOn g1 (Ioc lam 1) :=
    ((d3tg_int_rpow_Ioc hl0 _).const_mul A).indicator measurableSet_Ici
  have hg2i : IntegrableOn g2 (Ioc lam 1) := (d3tg_int_rpow_Ioc hl0 _).const_mul A'
  have hg3i : IntegrableOn g3 (Ioi 1) := (d3tg_int_rpow_Ioi hs0).const_mul Cl
  set ρ : ℝ → ℝ := fun t => (Ioc lam 1).indicator (fun t => g1 t + g2 t) t
      + (Ioi (1 : ℝ)).indicator g3 t with hρ
  have hρ1 : Integrable ((Ioc lam 1).indicator (fun t => g1 t + g2 t)) :=
    (integrable_indicator_iff measurableSet_Ioc).2 (hg1i.add hg2i)
  have hρ2 : Integrable ((Ioi (1 : ℝ)).indicator g3) :=
    (integrable_indicator_iff measurableSet_Ioi).2 hg3i
  have hdom : ∀ t ∈ Ioi lam, ‖iteratedFDeriv ℝ j (d3tgK ψ s b t) y‖ ≤ ρ t := by
    intro t ht
    have ht0 : 0 < t := lt_trans hl0 ht
    have hbt := hb y a ha t ht0
    by_cases ht1 : t ≤ 1
    · rw [if_pos ht1] at hbt
      refine hbt.trans (le_of_eq ?_)
      have hg1t : g1 t = if a ≤ t then A * t ^ (-((j : ℝ) + s) - 1) else 0 := by
        by_cases hat : a ≤ t
        · rw [hg1, Set.indicator_of_mem (show t ∈ Ici c from max_le (le_of_lt ht) hat), if_pos hat]
        · rw [hg1, Set.indicator_of_notMem
            (show t ∉ Ici c from fun h => hat ((le_max_right _ _).trans h)), if_neg hat]
      simp only [hρ]
      rw [Set.indicator_of_mem (show t ∈ Ioc lam 1 from ⟨ht, ht1⟩),
        Set.indicator_of_notMem (show t ∉ Ioi (1 : ℝ) from fun h => absurd h.out (not_lt.2 ht1)),
        add_zero, hg1t]
    · rw [if_neg ht1] at hbt
      refine hbt.trans (le_of_eq ?_)
      simp only [hρ]
      rw [Set.indicator_of_notMem (show t ∉ Ioc lam 1 from fun h => ht1 h.2),
        Set.indicator_of_mem (show t ∈ Ioi (1 : ℝ) from not_le.1 ht1), zero_add]
  have hsub1 : Ioc lam 1 ⊆ Ioi lam := fun t ht => ht.1
  have hsub2 : Ioi (1 : ℝ) ⊆ Ioi lam := Ioi_subset_Ioi hl1.le
  calc ‖∫ t in Ioi lam, iteratedFDeriv ℝ j (d3tgK ψ s b t) y‖
      ≤ ∫ t in Ioi lam, ‖iteratedFDeriv ℝ j (d3tgK ψ s b t) y‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi lam, ρ t := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => norm_nonneg _)
          (hρ1.add hρ2).integrableOn ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using hdom t ht
    _ = (∫ t in Ioc lam 1, g1 t + g2 t) + ∫ t in Ioi (1 : ℝ), g3 t := by
        simp only [hρ]
        rw [integral_add hρ1.integrableOn hρ2.integrableOn,
          setIntegral_indicator measurableSet_Ioc, setIntegral_indicator measurableSet_Ioi,
          inter_eq_right.2 hsub1, inter_eq_right.2 hsub2]
    _ = (∫ t in Ioc lam 1, g1 t) + (∫ t in Ioc lam 1, g2 t) + ∫ t in Ioi (1 : ℝ), g3 t := by
        rw [integral_add hg1i hg2i]
    _ ≤ (∫ t in Ioc lam 1, g1 t) + A' * T1 + Cl * T2 := by
        have e2 : ∫ t in Ioc lam 1, g2 t ≤ A' * T1 := by
          simp only [hg2]
          rw [integral_const_mul]
          refine mul_le_mul_of_nonneg_left ?_ hA'
          refine setIntegral_mono_set hT1int ?_ ?_
          · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht using
              Real.rpow_nonneg ht.1.le _
          · exact Filter.Eventually.of_forall (Ioc_subset_Ioc_left hl0.le)
        have e3 : ∫ t in Ioi (1 : ℝ), g3 t = Cl * T2 := by
          simp only [hg3]
          rw [integral_const_mul]
        linarith
    _ = _ := by ring

/-- Case `j + s > 0`. -/
theorem d3tgH_deriv_pos (hd : 1 ≤ d) {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {s : ℝ} (hs0 : 0 ≤ s)
    (hsd : s < d) (b : ℝ) (j : ℕ) (hj : 0 < (j : ℝ) + s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ (y : Euc d) (a : ℝ),
      (∀ n : Lattice d, a ≤ ‖y + Lattice.toEuc n‖) →
      ‖iteratedFDeriv ℝ j (d3tgH ψ s b lam) y‖ ≤ C * (max lam a) ^ (-s - (j : ℝ)) + C := by
  obtain ⟨A, T, hA, hT, hmain⟩ := d3tgH_deriv_bound hd hψ hs0 hsd b j
  refine ⟨A / ((j : ℝ) + s) + T, by positivity, fun lam hl0 hl1 y a ha => ?_⟩
  have hcpos : 0 < max lam a := lt_of_lt_of_le hl0 (le_max_left _ _)
  have h1 := hmain lam hl0 hl1 y a ha
  have h2 := d3tg_tail hj hcpos hA (Ioc lam 1)
  have hcp : 0 ≤ (max lam a) ^ (-s - (j : ℝ)) := Real.rpow_nonneg hcpos.le _
  have e : (max lam a) ^ (-s - (j : ℝ)) = (max lam a) ^ (-((j : ℝ) + s)) := by
    congr 1; ring
  rw [e] at hcp ⊢
  have : A * ((max lam a) ^ (-((j : ℝ) + s)) / ((j : ℝ) + s))
      = A / ((j : ℝ) + s) * (max lam a) ^ (-((j : ℝ) + s)) := by ring
  have hAe : 0 ≤ A / ((j : ℝ) + s) := div_nonneg hA hj.le
  nlinarith [mul_nonneg hT hcp, hAe]

/-- Case `j = s = 0`. -/
theorem d3tgH_log (hd : 1 ≤ d) {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) (hsd : (0 : ℝ) < d) (b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, 0 < lam → lam < 1 → ∀ (y : Euc d),
      ‖iteratedFDeriv ℝ 0 (d3tgH ψ 0 b lam) y‖ ≤ C * (1 + |Real.log lam|) := by
  obtain ⟨A, T, hA, hT, hmain⟩ := d3tgH_deriv_bound hd hψ (le_refl (0 : ℝ)) hsd b 0
  refine ⟨A + T, by positivity, fun lam hl0 hl1 y => ?_⟩
  have h1 := hmain lam hl0 hl1 y 0 (fun n => norm_nonneg _)
  have hS : (∫ t in Ioc lam 1, (Ici (max lam 0)).indicator
      (fun t : ℝ => A * t ^ (-(((0 : ℕ) : ℝ) + 0) - 1)) t) ≤ A * (-Real.log lam) := by
    have e1 : ∀ t : ℝ, t ^ (-(((0 : ℕ) : ℝ) + 0) - 1) = t⁻¹ := fun t => by
      rw [show -(((0 : ℕ) : ℝ) + 0) - 1 = -1 by simp, Real.rpow_neg_one]
    simp only [e1]
    have hint : IntegrableOn (fun t : ℝ => A * t⁻¹) (Ioc lam 1) := by
      have e : (fun t : ℝ => A * t ^ (-1 : ℝ)) = fun t => A * t⁻¹ := by
        funext t; rw [Real.rpow_neg_one]
      rw [← e]
      exact (d3tg_int_rpow_Ioc hl0 (-1)).const_mul A
    calc (∫ t in Ioc lam 1, (Ici (max lam 0)).indicator (fun t : ℝ => A * t⁻¹) t)
        ≤ ∫ t in Ioc lam 1, A * t⁻¹ := by
          refine integral_mono_of_nonneg ?_ hint ?_
          · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
            by_cases hm : t ∈ Ici (max lam 0)
            · rw [Set.indicator_of_mem hm]
              have : 0 < t := lt_trans hl0 ht.1
              positivity
            · rw [Set.indicator_of_notMem hm]; simp
          · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
            by_cases hm : t ∈ Ici (max lam 0)
            · rw [Set.indicator_of_mem hm]
            · rw [Set.indicator_of_notMem hm]
              have : 0 < t := lt_trans hl0 ht.1
              positivity
      _ = A * (-Real.log lam) := by
          rw [← intervalIntegral.integral_of_le hl1.le, intervalIntegral.integral_const_mul,
            integral_inv_of_pos hl0 one_pos, one_div, Real.log_inv]
  have hlog : -Real.log lam ≤ |Real.log lam| := neg_le_abs _
  calc ‖iteratedFDeriv ℝ 0 (d3tgH ψ 0 b lam) y‖
      ≤ _ := h1
    _ ≤ A * (-Real.log lam) + T := by gcongr
    _ ≤ A * |Real.log lam| + T := by gcongr
    _ ≤ (A + T) * (1 + |Real.log lam|) := by
        nlinarith [mul_nonneg hT (abs_nonneg (Real.log lam))]

end HRS.MC.D3TG
