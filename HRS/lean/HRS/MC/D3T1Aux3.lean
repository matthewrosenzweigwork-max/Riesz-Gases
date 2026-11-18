import HRS.MC.D3T1Aux2

/-!
# Packet D3T1, auxiliary facts: the one-sided lower bound of the periodic Riesz kernel
`g(x) ≥ b ∫_0^1 t^{d-s} Pφ_t(x) dt/t - B` (from `IsFDLConst` and the decay of `Pφ_t - ∫φ`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HRS.MC.D3T1

open HRS HRS.MC.FDLE HRS.MC.Per

variable {d : ℕ}

/-- The integrand `t^{d-s} Pφ_t(x) / t` is integrable on `(0, R]` for `x ≠ 0`. -/
lemma d3t_F_integrable {ψ : Euc d → ℝ} {s : ℝ} (hsd : s < d) {b : ℝ}
    (hb : IsFDLConst ψ s b) {x : Torus d} (hx : x ≠ 0) {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun t : ℝ => t ^ ((d : ℝ) - s) * fdlPer (fdlPhiScale ψ t) x / t) (Ioc 0 R) := by
  have hds : 0 < (d : ℝ) - s := by linarith
  have hH := ((hb.2.2.2 x hx).1).mono_set (Ioc_subset_Ioi_self : Ioc (0 : ℝ) R ⊆ Ioi 0)
  have hiv : IntervalIntegrable (fun t : ℝ => t ^ ((d : ℝ) - s - 1)) volume 0 R :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hR.le] at hiv
  have hsum := hH.add (hiv.const_mul (∫ y, fdlPhi ψ y))
  refine hsum.congr_fun (fun t ht => ?_) measurableSet_Ioc
  simp only [Pi.add_apply]
  rw [Real.rpow_sub_one ht.1.ne']
  field_simp
  ring

/-- The key one-sided bound. -/
lemma d3t_g_lower (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ψ : Euc d → ℝ}
    (hψ : IsFDLProfile ψ) {b : ℝ} (hb : IsFDLConst ψ s b) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : Torus d, x ≠ 0 →
      b * (∫ t in Ioc (0 : ℝ) 1, t ^ ((d : ℝ) - s) * fdlPer (fdlPhiScale ψ t) x / t) - B
        ≤ periodicRiesz d s x := by
  have hb0 : 0 < b := hb.1
  have hds : 0 < (d : ℝ) - s := by linarith
  obtain ⟨C, hC⟩ := per_decay_const hd hψ (d + 1)
  have hC0 : 0 ≤ C := by
    have := hC 1 le_rfl 0
    simp only [Real.one_rpow, mul_one] at this
    exact (abs_nonneg _).trans this
  set c : ℝ := ∫ y, fdlPhi ψ y with hc
  have hc0 : 0 ≤ c := integral_nonneg (fdle_phi_nonneg hψ)
  set A : ℝ := ∫ t in Ioi (1 : ℝ), C * t ^ (-s - 2) with hA
  have hA0 : 0 ≤ A := setIntegral_nonneg measurableSet_Ioi (fun t ht =>
    mul_nonneg hC0 (Real.rpow_nonneg (lt_trans zero_lt_one ht).le _))
  have hAint : IntegrableOn (fun t : ℝ => C * t ^ (-s - 2)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul C
  refine ⟨b * (c / ((d : ℝ) - s) + A), mul_nonneg hb0.le (add_nonneg (div_nonneg hc0 hds.le) hA0),
    fun x hx => ?_⟩
  obtain ⟨hHint, hg⟩ := hb.2.2.2 x hx
  set H : ℝ → ℝ := fun t => t ^ ((d : ℝ) - s) * (fdlPer (fdlPhiScale ψ t) x - c) / t with hH
  set F : ℝ → ℝ := fun t => t ^ ((d : ℝ) - s) * fdlPer (fdlPhiScale ψ t) x / t with hF
  have hFint : IntegrableOn F (Ioc 0 1) := d3t_F_integrable hsd hb hx one_pos
  have hsplit : ∫ t in Ioi (0 : ℝ), H t = (∫ t in Ioc (0 : ℝ) 1, H t) + ∫ t in Ioi (1 : ℝ), H t := by
    rw [← setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hHint.mono_set Ioc_subset_Ioi_self)
      (hHint.mono_set (Ioi_subset_Ioi zero_le_one)), Set.Ioc_union_Ioi_eq_Ioi zero_le_one]
  have hr : IntegrableOn (fun t : ℝ => c * t ^ ((d : ℝ) - s - 1)) (Ioc 0 1) := by
    have hiv : IntervalIntegrable (fun t : ℝ => t ^ ((d : ℝ) - s - 1)) volume 0 1 :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at hiv
    exact hiv.const_mul c
  have hHF : ∫ t in Ioc (0 : ℝ) 1, H t
      = (∫ t in Ioc (0 : ℝ) 1, F t) - c / ((d : ℝ) - s) := by
    have h1 : ∫ t in Ioc (0 : ℝ) 1, H t
        = ∫ t in Ioc (0 : ℝ) 1, (F t - c * t ^ ((d : ℝ) - s - 1)) := by
      refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
      simp only [hH, hF]
      rw [Real.rpow_sub_one ht.1.ne']
      field_simp
    rw [h1, integral_sub hFint hr]
    congr 1
    rw [integral_const_mul, ← intervalIntegral.integral_of_le zero_le_one,
      integral_rpow (Or.inl (by linarith))]
    rw [show (d : ℝ) - s - 1 + 1 = (d : ℝ) - s by ring, Real.one_rpow,
      Real.zero_rpow (by linarith), sub_zero]
    ring
  have htail : -A ≤ ∫ t in Ioi (1 : ℝ), H t := by
    have hle : ∫ t in Ioi (1 : ℝ), -(C * t ^ (-s - 2)) ≤ ∫ t in Ioi (1 : ℝ), H t := by
      refine setIntegral_mono_on hAint.neg (hHint.mono_set (Ioi_subset_Ioi zero_le_one))
        measurableSet_Ioi (fun t ht => ?_)
      have ht1 : 1 ≤ t := le_of_lt ht
      have ht0 : 0 < t := lt_of_lt_of_le one_pos ht1
      have hd1 := hC t ht1 x
      have hrw : t ^ ((d : ℝ) - s) * (C * t ^ (-((d + 1 : ℕ) : ℝ))) / t = C * t ^ (-s - 2) := by
        have : t ^ ((d : ℝ) - s) * t ^ (-((d + 1 : ℕ) : ℝ)) / t = t ^ (-s - 2) := by
          rw [← Real.rpow_add ht0, div_eq_mul_inv, ← Real.rpow_neg_one, ← Real.rpow_add ht0]
          congr 1
          push_cast
          ring
        calc t ^ ((d : ℝ) - s) * (C * t ^ (-((d + 1 : ℕ) : ℝ))) / t
            = C * (t ^ ((d : ℝ) - s) * t ^ (-((d + 1 : ℕ) : ℝ)) / t) := by ring
          _ = C * t ^ (-s - 2) := by rw [this]
      have h2 : -(C * t ^ (-s - 2)) ≤ H t := by
        rw [← hrw]
        simp only [hH]
        have hpos : 0 ≤ t ^ ((d : ℝ) - s) / t := div_nonneg (Real.rpow_nonneg ht0.le _) ht0.le
        have : t ^ ((d : ℝ) - s) * (fdlPer (fdlPhiScale ψ t) x - c) / t
            = (t ^ ((d : ℝ) - s) / t) * (fdlPer (fdlPhiScale ψ t) x - c) := by ring
        have h3 : t ^ ((d : ℝ) - s) * (C * t ^ (-((d + 1 : ℕ) : ℝ))) / t
            = (t ^ ((d : ℝ) - s) / t) * (C * t ^ (-((d + 1 : ℕ) : ℝ))) := by ring
        rw [this, h3, ← mul_neg]
        exact mul_le_mul_of_nonneg_left (by
          have := (abs_le.mp hd1).1
          push_cast at this ⊢
          linarith) hpos
      exact h2
    rw [integral_neg] at hle
    exact hle
  rw [hg, hsplit, hHF]
  have : b * ((∫ t in Ioc (0 : ℝ) 1, F t) - c / ((d : ℝ) - s) + ∫ t in Ioi (1 : ℝ), H t)
      ≥ b * ((∫ t in Ioc (0 : ℝ) 1, F t) - c / ((d : ℝ) - s) + -A) := by
    apply mul_le_mul_of_nonneg_left _ hb0.le
    linarith
  nlinarith [this]

end HRS.MC.D3T1
