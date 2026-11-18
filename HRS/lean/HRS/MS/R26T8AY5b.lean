import HRS.MS.R26T8AY5b0
import HRS.MS.R26T8AY5a
import HRS.MS.R26T8AY3b
import HRS.MS.R26T8AP11e

/-!
# S8.2 T8A Y5b: the induction step for the near-diagonal part of the local Riesz potential
`r26t8a_Y5b_zeta`: assume the same-`k` Riesz bound for `Conormal (k-1) b M (σ+1)` (`σ < 0`).  Then for `Conormal k b M σ A F` the local Riesz potential of
`Fz = chi(4(x-y)) F` is `Conormal k (b+1) M (σ-α) (C A)`.  Induction on the `z`-derivative order `q`, using `∂_z = ∂_x - (1/2) ∂_X` (Y3b), the commutation
`∂_x localRiesz = localRiesz ∂_x` (Y5b0), the weak order-zero bound (P11e) and the hypothesis at `(k-1, σ+1)`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

set_option maxHeartbeats 6400000 in
theorem r26t8a_Y5b_zeta (hd : 2 ≤ d) {α : ℝ} (hα : 0 < α) (hαd : α < d) {chi : Euc d → ℝ} (hchi : NewtonCutoff chi)
    (k b : ℕ) (M σ : ℝ) (hM : 0 ≤ M) (hσ : σ < 0)
    (hIH : ∃ CIH : ℝ, 0 ≤ CIH ∧ ∀ (F' : Euc d → Euc d → ℝ) (A' : ℝ), 0 ≤ A' →
      Conormal (k - 1) b M (σ + 1) A' F' →
        Conormal (k - 1) (b + 1) M (σ + 1 - α) (CIH * A') (r26t8a_localRiesz α chi F')) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : Euc d → Euc d → ℝ) (A : ℝ), 0 ≤ A → Conormal k b M σ A F →
      Conormal k (b + 1) M (σ - α) (C * A) (r26t8a_localRiesz α chi (r26t8a_Z5a2_Fz chi F)) := by
  obtain ⟨CIH, hCIH0, hIH'⟩ := hIH
  obtain ⟨cz, hcz0, hFz⟩ := r26t8a_Z5a2_conormal hchi k b M σ
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  obtain ⟨Cw, hCw0, hCw⟩ := r26t8a_local_riesz_gain_nonneg d hd k b α M 0 hα hαd hM le_rfl hd0 chi hchi
  obtain ⟨Kw, hKw1, hKw⟩ := r26t8a_Y5a_weak_env b k α hα
  -- the weak bound
  have weak : ∀ (F : Euc d → Euc d → ℝ) (A : ℝ), 0 ≤ A → Conormal k b M σ A F →
      ∀ p q : ℕ, p + q ≤ k → ∀ X z : Euc d, z ≠ 0 → (q = 0 ∨ 1 / 4 ≤ ‖z‖) →
      ‖mixedJet p q (r26t8a_localRiesz α chi (r26t8a_Z5a2_Fz chi F)) X z‖ ≤
        (Cw * cz * Kw) * A * HRS.MS.Phase2S82.pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) *
          (1 + (min 1 ‖z‖) ^ (-((σ - α) + (q : ℝ))) * (1 + |Real.log (min 1 ‖z‖)|) ^ (b + 1)) := by
    intro F A hA hF p q hpq X z hz hcase
    have hFz' : Conormal k b M σ (cz * A) (r26t8a_Z5a2_Fz chi F) := hFz F A hA hF
    have hczA : 0 ≤ cz * A := mul_nonneg hcz0 hA
    have hFz0 : Conormal k b M 0 (cz * A) (r26t8a_Z5a2_Fz chi F) :=
      r26t8a_conormal_mono_sA hczA le_rfl hσ.le hFz'
    obtain ⟨-, hW⟩ := hCw _ (cz * A) hczA hFz0
    have hb := hW.2 p q hpq X z hz
    have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
    have hpw0 := r26t8a_pairWeight_nonneg (d := d) M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z)
    set r : ℝ := min 1 ‖z‖ with hr
    have hr0 : 0 < r := lt_min one_pos hzn
    have hr1 : r ≤ 1 := min_le_left _ _
    have hbr : 1 ≤ 1 + r ^ (-((σ - α) + (q : ℝ))) * (1 + |Real.log r|) ^ (b + 1) := by
      have : 0 ≤ r ^ (-((σ - α) + (q : ℝ))) * (1 + |Real.log r|) ^ (b + 1) := by positivity
      linarith
    have hK := hKw q (by omega) r hr0 hr1 (by
      rcases hcase with h | h
      · exact Or.inl h
      · exact Or.inr (le_min (by norm_num) h))
    refine hb.trans ?_
    set pw := HRS.MS.Phase2S82.pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) with hpw
    calc Cw * (cz * A) * pw * (1 + r ^ (-((0 - α : ℝ) + (q : ℝ))) * (1 + |Real.log r|) ^ (b + 1))
        ≤ Cw * (cz * A) * pw * Kw := mul_le_mul_of_nonneg_left hK (by positivity)
      _ = (Cw * cz * Kw) * A * pw * 1 := by ring
      _ ≤ (Cw * cz * Kw) * A * pw * (1 + r ^ (-((σ - α) + (q : ℝ))) * (1 + |Real.log r|) ^ (b + 1)) :=
          mul_le_mul_of_nonneg_left hbr (by positivity)
  -- the induction on q
  have claim : ∀ q0 : ℕ, q0 ≤ k → ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : Euc d → Euc d → ℝ) (A : ℝ), 0 ≤ A →
      Conormal k b M σ A F → ∀ q : ℕ, q ≤ q0 → ∀ p : ℕ, p + q ≤ k → ∀ X z : Euc d, z ≠ 0 →
      ‖mixedJet p q (r26t8a_localRiesz α chi (r26t8a_Z5a2_Fz chi F)) X z‖ ≤
        C * A * HRS.MS.Phase2S82.pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) *
          (1 + (min 1 ‖z‖) ^ (-((σ - α) + (q : ℝ))) * (1 + |Real.log (min 1 ‖z‖)|) ^ (b + 1)) := by
    intro q0
    induction q0 with
    | zero =>
      intro _
      refine ⟨Cw * cz * Kw, by positivity, fun F A hA hF q hq p hpq X z hz => ?_⟩
      have hq0 : q = 0 := by omega
      exact weak F A hA hF p q hpq X z hz (Or.inl hq0)
    | succ q0 ih =>
      intro hq0k
      obtain ⟨Cq, hCq0, hCq⟩ := ih (by omega)
      refine ⟨Cw * cz * Kw + d * (CIH * (2 * cz) + Cq), by positivity, fun F A hA hF q hq p hpq X z hz => ?_⟩
      have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
      have hpw0 := r26t8a_pairWeight_nonneg (d := d) M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z)
      set pw := HRS.MS.Phase2S82.pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) with hpw
      set r : ℝ := min 1 ‖z‖ with hr
      have hr0 : 0 < r := lt_min one_pos hzn
      have hr1 : r ≤ 1 := min_le_left _ _
      have hcomm : ∀ q' : ℕ, 0 ≤ (1 + r ^ (-((σ - α) + (q' : ℝ))) * (1 + |Real.log r|) ^ (b + 1)) := fun q' => by
        positivity
      have hnn : ∀ q' : ℕ, 0 ≤ A * pw * (1 + r ^ (-((σ - α) + (q' : ℝ))) * (1 + |Real.log r|) ^ (b + 1)) :=
        fun q' => by have := hcomm q'; positivity
      by_cases hq : q ≤ q0
      · refine (hCq F A hA hF q hq p hpq X z hz).trans ?_
        have h0 : 0 ≤ Cw * cz * Kw + (d - 1) * Cq + d * (CIH * (2 * cz)) := by
          have : 0 ≤ (d - 1 : ℝ) * Cq := mul_nonneg (by linarith) hCq0
          positivity
        have := mul_le_mul_of_nonneg_right (show Cq ≤ Cw * cz * Kw + d * (CIH * (2 * cz) + Cq) by nlinarith [h0])
          (hnn q)
        calc _ = Cq * (A * pw * (1 + r ^ (-((σ - α) + (q : ℝ))) * (1 + |Real.log r|) ^ (b + 1))) := by ring
          _ ≤ _ := this
          _ = _ := by ring
      · have hqe : q = q0 + 1 := by omega
        by_cases hz4 : 1 / 4 ≤ ‖z‖
        · refine (weak F A hA hF p q hpq X z hz (Or.inr hz4)).trans ?_
          have := mul_le_mul_of_nonneg_right
            (show Cw * cz * Kw ≤ Cw * cz * Kw + d * (CIH * (2 * cz) + Cq) by
              have : 0 ≤ (d : ℝ) * (CIH * (2 * cz) + Cq) := by positivity
              linarith) (hnn q)
          calc _ = Cw * cz * Kw * (A * pw * (1 + r ^ (-((σ - α) + (q : ℝ))) * (1 + |Real.log r|) ^ (b + 1))) := by ring
            _ ≤ _ := this
            _ = _ := by ring
        · push Not at hz4
          -- the strong step
          subst hqe
          obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
          have hFz' : Conormal (k' + 1) b M σ (cz * A) (r26t8a_Z5a2_Fz chi F) := hFz F A hA hF
          have hczA : 0 ≤ cz * A := mul_nonneg hcz0 hA
          have hFz0 : Conormal (k' + 1) b M 0 (cz * A) (r26t8a_Z5a2_Fz chi F) :=
            r26t8a_conormal_mono_sA hczA le_rfl hσ.le hFz'
          obtain ⟨-, hW⟩ := hCw _ (cz * A) hczA hFz0
          set H : Fin d → Euc d → Euc d → ℝ := fun i => r26t8a_dx i (r26t8a_Z5a2_Fz chi F) with hH
          have hHc : ∀ i, Conormal k' b M (σ + 1) (2 * (cz * A)) (H i) := fun i =>
            r26t8a_f8_dx_conormal hchi hczA hFz' i
          have hRi : ∀ i, Conormal k' (b + 1) M (σ + 1 - α) (CIH * (2 * (cz * A)))
              (r26t8a_localRiesz α chi (H i)) := fun i =>
            hIH' (H i) (2 * (cz * A)) (by positivity) (hHc i)
          have hFz1 : Conormal 1 b M σ (cz * A) (r26t8a_Z5a2_Fz chi F) :=
            r26t8a_conormal_mono (by omega : 1 ≤ k' + 1) hFz'
          have hx : ∀ i x y, x ≠ y → ‖x - y‖ < 1 →
              r26t8a_dx i (r26t8a_localRiesz α chi (r26t8a_Z5a2_Fz chi F)) x y =
                r26t8a_localRiesz α chi (H i) x y := fun i x y hxy hx1 =>
            r26t8a_Y5b0_dx_eq hd hα hchi b M σ hM hσ hczA hFz1 (fun x y h => r26t8a_Z5a2_supp hchi F x y h) i hxy hx1
          have hjets := r26t8a_Y3b_jets hchi (k' := k') (R0 := r26t8a_localRiesz α chi (r26t8a_Z5a2_Fz chi F))
            (fun i => r26t8a_localRiesz α chi (H i)) hW.1 (fun i => (hRi i).1) hx p q0 (by omega) X z hz
            (by linarith)
          refine hjets.trans ?_
          have hEq : -((σ + 1 - α) + (q0 : ℝ)) = -((σ - α) + ((q0 + 1 : ℕ) : ℝ)) := by push_cast; ring
          have hexp : r ^ (-((σ - α) + (q0 : ℝ))) ≤ r ^ (-((σ - α) + ((q0 + 1 : ℕ) : ℝ))) :=
            Real.rpow_le_rpow_of_exponent_ge hr0 hr1 (by push_cast; linarith)
          have hLog : 0 ≤ (1 + |Real.log r|) ^ (b + 1) := by positivity
          have hE : (1 + r ^ (-((σ - α) + (q0 : ℝ))) * (1 + |Real.log r|) ^ (b + 1)) ≤
              (1 + r ^ (-((σ - α) + ((q0 + 1 : ℕ) : ℝ))) * (1 + |Real.log r|) ^ (b + 1)) := by
            have := mul_le_mul_of_nonneg_right hexp hLog
            linarith
          set E1 := (1 + r ^ (-((σ - α) + ((q0 + 1 : ℕ) : ℝ))) * (1 + |Real.log r|) ^ (b + 1)) with hE1
          have hE1n : 0 ≤ E1 := by rw [hE1]; positivity
          have hbi : ∀ i, ‖mixedJet p q0 (r26t8a_localRiesz α chi (H i)) X z‖ ≤
              (CIH * (2 * (cz * A))) * pw * E1 := by
            intro i
            have := (hRi i).2 p q0 (by omega) X z hz
            rw [hEq] at this
            exact this
          have hbj : ‖mixedJet (p + 1) q0 (r26t8a_localRiesz α chi (r26t8a_Z5a2_Fz chi F)) X z‖ ≤
              Cq * A * pw * E1 := by
            refine (hCq F A hA hF q0 le_rfl (p + 1) (by omega) X z hz).trans ?_
            exact mul_le_mul_of_nonneg_left hE (by positivity)
          calc ∑ i : Fin d, (‖mixedJet p q0 (r26t8a_localRiesz α chi (H i)) X z‖ +
                ‖mixedJet (p + 1) q0 (r26t8a_localRiesz α chi (r26t8a_Z5a2_Fz chi F)) X z‖)
              ≤ ∑ _i : Fin d, ((CIH * (2 * (cz * A))) * pw * E1 + Cq * A * pw * E1) :=
                Finset.sum_le_sum fun i _ => add_le_add (hbi i) hbj
            _ = (d * (CIH * (2 * cz) + Cq)) * A * pw * E1 := by
                simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
            _ ≤ (Cw * cz * Kw + d * (CIH * (2 * cz) + Cq)) * A * pw * E1 := by
                have h0 : 0 ≤ Cw * cz * Kw := by positivity
                have h1 : 0 ≤ A * pw * E1 := by positivity
                nlinarith [mul_nonneg h0 h1]
  obtain ⟨C, hC0, hC⟩ := claim k le_rfl
  have hd0' : (0 : ℝ) < d := hd0
  refine ⟨C, hC0, fun F A hA hF => ?_⟩
  have hFz' : Conormal k b M σ (cz * A) (r26t8a_Z5a2_Fz chi F) := hFz F A hA hF
  have hczA : 0 ≤ cz * A := mul_nonneg hcz0 hA
  have hFz0 : Conormal k b M 0 (cz * A) (r26t8a_Z5a2_Fz chi F) :=
    r26t8a_conormal_mono_sA hczA le_rfl hσ.le hFz'
  obtain ⟨-, hW⟩ := hCw _ (cz * A) hczA hFz0
  exact ⟨hW.1, fun p q hpq X z hz => hC F A hA hF q (by omega) p hpq X z hz⟩

end HRS.MS.R26T8A
