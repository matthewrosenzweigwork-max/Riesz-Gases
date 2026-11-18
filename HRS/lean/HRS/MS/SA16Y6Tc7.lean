import HRS.MS.SA16Y6Tc6

/-!
# S.A.16 (SA16Y6) Tc7: jets bound of `g_a ⋆ eucNonlocal` for `s = d-1` (copy of SA16Y5Jt3 with `T → Tc`)

`sa16y6_Fam_pd_bound` (`p ≥ 2`): `‖∂^idx Fam φ‖_p ≤ C a^{-1/2} ‖wJet k φ‖_p` for `idx` of length `≤ k`, `0 < a ≤ 1`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q

section Tc7
variable {d : ℕ}

set_option maxHeartbeats 1600000 in
theorem sa16y6_Fam_pd_bound (hd : 1 ≤ d) (p : ℝ) (hp : 2 ≤ p) (k : ℕ) (MB W : ℝ)
    (hMB : 0 ≤ MB) (hW : 0 ≤ W) :
    ∃ CJ : ℝ, 0 ≤ CJ ∧ ∀ (M : Matrix (Fin d) (Fin d) ℝ), (∀ i j, |M i j| ≤ MB) → ∀ {μ : Euc d → ℝ},
      ContDiff ℝ ∞ μ → (∀ κ ≤ k + 1, ∀ x, ‖iteratedFDeriv ℝ κ μ x‖ ≤ W) → ∀ {a : ℝ}, 0 < a → a ≤ 1 →
      ∀ (φ : ccSub d) {l : ℕ}, l ≤ k → ∀ idx : Fin l → Fin d,
        eLpNorm (partialDeriv idx (sa16y6_Fam d a M μ φ.1)) (ENNReal.ofReal p) volume ≤
          ENNReal.ofReal (CJ * a ^ (-(1 / 2 : ℝ))) * eLpNorm (wJet k φ.1) (ENNReal.ofReal p) volume := by
  obtain ⟨CT, hCT0, hCT⟩ := sa16y6_Tc_bound hd hp
  refine ⟨(d : ℝ) * d * (MB * (CT * (2 * (2 ^ k * (W * (d : ℝ) ^ k))))), by positivity, ?_⟩
  intro M hM μ hμ hμb a ha ha1 φ l hl idx
  have hp1 : (1 : ℝ) ≤ p := by linarith
  set X : ℝ := a ^ (-(1 / 2 : ℝ)) with hX
  have hX0 : 0 ≤ X := Real.rpow_nonneg ha.le _
  set E := eLpNorm (wJet k φ.1) (ENNReal.ofReal p) volume with hE
  have hdm : ∀ j : Fin d, ContDiff ℝ ∞ (fun y => fderiv ℝ μ y (sa16z_e j)) := fun j =>
    (hμ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hP : IsCcInfty (fun y => μ y * φ.1 y) := sa16y5_cc_mul hμ φ.2
  have hQ : ∀ j : Fin d, IsCcInfty (fun y => fderiv ℝ μ y (sa16z_e j) * φ.1 y) := fun j =>
    sa16y5_cc_mul (hdm j) φ.2
  have hT : ∀ i j : Fin d, ContDiff ℝ ∞ (sa16y6_Tc d a i j (fun y => μ y * φ.1 y)
      (fun y => fderiv ℝ μ y (sa16z_e j) * φ.1 y)) := fun i j =>
    sa16y6_Tc_smooth hd ha i j hP (hQ j)
  have e1 : partialDeriv idx (sa16y6_Fam d a M μ φ.1) = fun x => ∑ i, ∑ j, M j i *
      sa16y6_Tc d a i j (partialDeriv idx (fun y => μ y * φ.1 y))
        (partialDeriv idx (fun y => fderiv ℝ μ y (sa16z_e j) * φ.1 y)) x := by
    unfold sa16y6_Fam
    rw [sa16y5_pd_dsum hT (fun i j => M j i) idx]
    funext x
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [sa16y6_Tc_pd hd ha i j hP (hQ j) idx]
  rw [e1]
  have hp' : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp1
  refine (sa16q_eLpNorm_dsum_le _ hp').trans ?_
  -- each term
  have hb : ∀ i j : Fin d, eLpNorm (fun x => M j i * sa16y6_Tc d a i j
      (partialDeriv idx (fun y => μ y * φ.1 y))
        (partialDeriv idx (fun y => fderiv ℝ μ y (sa16z_e j) * φ.1 y)) x) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (MB * (CT * (2 * (2 ^ k * (W * (d : ℝ) ^ k)))) * X) * E := by
    intro i j
    have h1 : eLpNorm (fun x => M j i * sa16y6_Tc d a i j
        (partialDeriv idx (fun y => μ y * φ.1 y))
          (partialDeriv idx (fun y => fderiv ℝ μ y (sa16z_e j) * φ.1 y)) x) (ENNReal.ofReal p) volume =
        ENNReal.ofReal |M j i| * eLpNorm (sa16y6_Tc d a i j
        (partialDeriv idx (fun y => μ y * φ.1 y))
          (partialDeriv idx (fun y => fderiv ℝ μ y (sa16z_e j) * φ.1 y))) (ENNReal.ofReal p) volume := by
      have := eLpNorm_const_smul (μ := volume) (p := ENNReal.ofReal p) (M j i)
        (sa16y6_Tc d a i j (partialDeriv idx (fun y => μ y * φ.1 y))
          (partialDeriv idx (fun y => fderiv ℝ μ y (sa16z_e j) * φ.1 y)))
      rw [show (fun x => M j i * sa16y6_Tc d a i j
        (partialDeriv idx (fun y => μ y * φ.1 y))
          (partialDeriv idx (fun y => fderiv ℝ μ y (sa16z_e j) * φ.1 y)) x) =
        (M j i) • sa16y6_Tc d a i j (partialDeriv idx (fun y => μ y * φ.1 y))
          (partialDeriv idx (fun y => fderiv ℝ μ y (sa16z_e j) * φ.1 y)) from rfl, this,
        Real.enorm_eq_ofReal_abs]
    have h2 := hCT a ha ha1 i j (partialDeriv idx (fun y => μ y * φ.1 y))
      (partialDeriv idx (fun y => fderiv ℝ μ y (sa16z_e j) * φ.1 y))
      (sa16s_cc_partialDeriv hP idx) (sa16s_cc_partialDeriv (hQ j) idx)
    have hbd1 : ∀ κ ≤ l, ∀ x, ‖iteratedFDeriv ℝ κ μ x‖ ≤ W := fun κ hκ x => hμb κ (by omega) x
    have hbd2 : ∀ κ ≤ l, ∀ x, ‖iteratedFDeriv ℝ κ (fun y => fderiv ℝ μ y (sa16z_e j)) x‖ ≤ W :=
      fun κ hκ x => (sa16q_norm_iter_pd_le hμ j κ x).trans (hμb (κ + 1) (by omega) x)
    have h3 := sa16y5_leib_lp hd hμ hW hl hbd1 φ idx hp1
    have h4 := sa16y5_leib_lp hd (hdm j) hW hl hbd2 φ idx hp1
    have hpow : (2 : ℝ) ^ l * (W * (d : ℝ) ^ k) ≤ 2 ^ k * (W * (d : ℝ) ^ k) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hl) (by positivity)
    have h5 : eLpNorm (partialDeriv idx (fun y => μ y * φ.1 y)) (ENNReal.ofReal p) volume +
        eLpNorm (partialDeriv idx (fun y => fderiv ℝ μ y (sa16z_e j) * φ.1 y)) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (2 * (2 ^ k * (W * (d : ℝ) ^ k))) * E := by
      have h3' := h3.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hpow) le_rfl)
      have h4' := h4.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hpow) le_rfl)
      calc _ ≤ ENNReal.ofReal (2 ^ k * (W * (d : ℝ) ^ k)) * E + ENNReal.ofReal (2 ^ k * (W * (d : ℝ) ^ k)) * E :=
            add_le_add h3' h4'
        _ = _ := by
          rw [← two_mul, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat, mul_assoc]
    rw [h1]
    calc ENNReal.ofReal |M j i| * eLpNorm (sa16y6_Tc d a i j _ _) (ENNReal.ofReal p) volume
        ≤ ENNReal.ofReal MB * (ENNReal.ofReal (CT * X) * (ENNReal.ofReal (2 * (2 ^ k * (W * (d : ℝ) ^ k))) * E)) := by
          gcongr
          · exact hM j i
          · exact h2.trans (by gcongr)
      _ = _ := by
          rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul hMB, ← ENNReal.ofReal_mul (by positivity)]
          congr 2
          ring
  calc ∑ i : Fin d, ∑ j : Fin d, eLpNorm (fun x => M j i * sa16y6_Tc d a i j
        (partialDeriv idx (fun y => μ y * φ.1 y))
          (partialDeriv idx (fun y => fderiv ℝ μ y (sa16z_e j) * φ.1 y)) x) (ENNReal.ofReal p) volume
      ≤ ∑ i : Fin d, ∑ j : Fin d, ENNReal.ofReal (MB * (CT * (2 * (2 ^ k * (W * (d : ℝ) ^ k)))) * X) * E :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hb i j
    _ = (d : ℝ≥0∞) * ((d : ℝ≥0∞) * (ENNReal.ofReal (MB * (CT * (2 * (2 ^ k * (W * (d : ℝ) ^ k)))) * X) * E)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        congr 1
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = ENNReal.ofReal ((d : ℝ) * d * (MB * (CT * (2 * (2 ^ k * (W * (d : ℝ) ^ k))))) * X) * E := by
        generalize hB : MB * (CT * (2 * (2 ^ k * (W * (d : ℝ) ^ k)))) * X = B
        have hB0 : 0 ≤ B := by rw [← hB]; positivity
        rw [show ((d : ℝ) * d * (MB * (CT * (2 * (2 ^ k * (W * (d : ℝ) ^ k))))) * X) = ((d : ℝ) * d) * B by
          rw [← hB]; ring, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]
        ring

end Tc7

end HRS.Whole.AppendixA.Phase2SA16R
