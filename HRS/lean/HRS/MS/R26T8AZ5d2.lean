import HRS.MS.R26T8AZ5d1
import HRS.MS.R26T8AP07

/-!
# S8.2 T8A Z5d2: the induction step for the near-diagonal part
`r26t8a_Z5d2_zeta`: assume the same-`k` Newton bound for `Conormal (k-1) b M (σ+1)` (`σ < 0`).  Then for `Conormal k b M σ A F`, the potential of the
cutoff `Fz = chi(4(x-y)) F` is `Conormal k (b+1) M (σ-2) (C A)`.
Jets with `q = 0` or `|z| ≥ 1/4`: the order-zero bound (P07, `0 ≤ σ`); jets of order `q+1` with `|z| < 1/4`: `∂_{e_i}` of the potential is the potential of
`pdir (0,e_i) Fz` (Z4b), whose jets are controlled by the induction hypothesis (Z5c).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

set_option maxHeartbeats 6400000 in
theorem r26t8a_Z5d2_zeta (hd : 2 ≤ d) (nu : ℝ) (hnu : 0 < nu) {chi : Euc d → ℝ} (hchi : NewtonCutoff chi)
    (k b : ℕ) (M σ : ℝ) (hM : 0 ≤ M) (hσ : σ < 0)
    (hIH : ∃ CIH : ℝ, 0 ≤ CIH ∧ ∀ (F' : Euc d → Euc d → ℝ) (A' : ℝ), 0 ≤ A' →
      Conormal (k - 1) b M (σ + 1) A' F' →
        Conormal (k - 1) (b + 1) M (σ + 1 - 2) (CIH * A') (rawNewton nu chi F')) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : Euc d → Euc d → ℝ) (A : ℝ), 0 ≤ A → Conormal k b M σ A F →
      Conormal k (b + 1) M (σ - 2) (C * A) (rawNewton nu chi (r26t8a_Z5a2_Fz chi F)) := by
  obtain ⟨CIH, hCIH0, hIH'⟩ := hIH
  obtain ⟨cz, hcz0, hFz⟩ := r26t8a_Z5a2_conormal hchi k b M σ
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  obtain ⟨Cw, hCw0, hCw⟩ := r26t8a_raw_newton_bound_nonneg d hd k b nu M 0 hnu hM le_rfl hd0 chi hchi
  obtain ⟨CB, hCB0, hCB⟩ := r26t8a_Z5a3_slice (d := d) b M σ hM hσ
  obtain ⟨Kw, hKw1, hKw⟩ := r26t8a_Z5d1_weak_env b k
  refine ⟨Cw * cz * Kw + d * (CIH * cz), by positivity, fun F A hA hF => ?_⟩
  set Fz := r26t8a_Z5a2_Fz chi F with hFzdef
  have hFz' : Conormal k b M σ (cz * A) Fz := hFz F A hA hF
  have hczA : 0 ≤ cz * A := mul_nonneg hcz0 hA
  have hFz0 : Conormal k b M 0 (cz * A) Fz :=
    r26t8a_conormal_mono_sA hczA le_rfl hσ.le hFz'
  obtain ⟨hint, hW⟩ := hCw Fz (cz * A) hczA hFz0
  refine ⟨hW.1, fun p q hpq X z hz => ?_⟩
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hpw0 := r26t8a_pairWeight_nonneg (d := d) M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z)
  set r : ℝ := min 1 ‖z‖ with hr
  have hr0 : 0 < r := lt_min one_pos hzn
  have hr1 : r ≤ 1 := min_le_left _ _
  have hbr : 1 ≤ 1 + r ^ (-((σ - 2) + (q : ℝ))) * (1 + |Real.log r|) ^ (b + 1) := by
    have : 0 ≤ r ^ (-((σ - 2) + (q : ℝ))) * (1 + |Real.log r|) ^ (b + 1) := by positivity
    linarith
  by_cases hcase : q = 0 ∨ 1 / 4 ≤ ‖z‖
  · have hb := hW.2 p q hpq X z hz
    have hq : q ≤ k := by omega
    have hK := hKw q hq r hr0 hr1 (by
      rcases hcase with h | h
      · exact Or.inl h
      · exact Or.inr (le_min (by norm_num) h))
    refine hb.trans ?_
    set pw := HRS.MS.Phase2S82.pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) with hpw
    calc Cw * (cz * A) * pw * (1 + r ^ (-((0 - 2 : ℝ) + (q : ℝ))) * (1 + |Real.log r|) ^ (b + 1))
        ≤ Cw * (cz * A) * pw * Kw := mul_le_mul_of_nonneg_left hK (by positivity)
      _ = (Cw * cz * Kw) * A * pw * 1 := by ring
      _ ≤ (Cw * cz * Kw) * A * pw * (1 + r ^ (-((σ - 2) + (q : ℝ))) * (1 + |Real.log r|) ^ (b + 1)) :=
          mul_le_mul_of_nonneg_left hbr (by positivity)
      _ ≤ (Cw * cz * Kw + d * (CIH * cz)) * A * pw *
            (1 + r ^ (-((σ - 2) + (q : ℝ))) * (1 + |Real.log r|) ^ (b + 1)) := by
          have h0 : 0 ≤ (d : ℝ) * (CIH * cz) := by positivity
          have h1 : 0 ≤ A * pw * (1 + r ^ (-((σ - 2) + (q : ℝ))) * (1 + |Real.log r|) ^ (b + 1)) := by positivity
          nlinarith [mul_nonneg h0 h1]
  · push Not at hcase
    obtain ⟨hq0, hz4⟩ := hcase
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hk1 : k' + 1 - 1 = k' := rfl
    set H : Fin d → Euc d → Euc d → ℝ := fun i => r26t8a_pdir (0, r26t8a_e d i) Fz with hH
    have hHc : ∀ i, Conormal k' b M (σ + 1) (cz * A) (H i) := fun i =>
      r26t8a_pdir_conormal_Z hchi hczA hFz' (r26t8a_e d i) (le_of_eq (by simp [r26t8a_e_norm]))
    have hRi : ∀ i, Conormal k' (b + 1) M (σ + 1 - 2) (CIH * (cz * A)) (rawNewton nu chi (H i)) := fun i =>
      hIH' (H i) (cz * A) hczA (hHc i)
    -- the derivative identity
    have hsuppFz : ∀ x y : Euc d, 1 / 2 ≤ ‖x - y‖ → Fz x y = 0 := fun x y h =>
      r26t8a_Z5a2_supp hchi F x y h
    have hFz1 : Conormal 1 b M σ (cz * A) Fz := r26t8a_conormal_mono (by omega : 1 ≤ k' + 1) hFz'
    have hder : ∀ X' w : Euc d, w ≠ 0 → ‖w‖ < 1 →
        DifferentiableAt ℝ (fun w' => midPair (rawNewton nu chi Fz) X' w') w ∧
        ∀ i, fderiv ℝ (fun w' => midPair (rawNewton nu chi Fz) X' w') w (r26t8a_e d i) =
          midPair (rawNewton nu chi (H i)) X' w := by
      intro X' w hw hw1
      obtain ⟨h0b, h1b⟩ := hCB (cz * A) hczA Fz hFz1 hsuppFz X'
      have hsupp' : ∀ w' : Euc d, 1 / 2 < ‖w'‖ → midPair Fz X' w' = 0 := fun w' hw' =>
        hsuppFz _ _ (by
          have e : (X' + (1 / 2 : ℝ) • w') - (X' - (1 / 2 : ℝ) • w') = w' := by module
          rw [e]; exact hw'.le)
      have hmain := r26t8a_Z4b_deriv hd nu hchi (P := Fz) (by simpa using hFz1.1) X' hsupp' (c0 := CB * (cz * A) * jbracket X' ^ (2 * M))
        (c1 := CB * (cz * A) * jbracket X' ^ (2 * M)) (s1 := 1) h0b h1b one_pos
        (by have : (2 : ℝ) ≤ d := by exact_mod_cast hd
            linarith) hw hw1
      refine ⟨hmain.1.differentiableAt, fun i => ?_⟩
      rw [hmain.1.fderiv]
      exact hmain.2 (r26t8a_e d i)
    have hjets := r26t8a_Z5c_jets hchi (k' := k') (R0 := rawNewton nu chi Fz)
      (fun i => rawNewton nu chi (H i)) hW.1 (fun i => (hRi i).1) hder p q' (by omega) X z hz (by linarith)
    refine hjets.trans ?_
    set pw := HRS.MS.Phase2S82.pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) with hpw
    have hEq : -((σ + 1 - 2) + (q' : ℝ)) = -((σ - 2) + ((q' + 1 : ℕ) : ℝ)) := by push_cast; ring
    have hbi : ∀ i, ‖mixedJet p q' (rawNewton nu chi (H i)) X z‖ ≤
        CIH * (cz * A) * pw * (1 + r ^ (-((σ - 2) + ((q' + 1 : ℕ) : ℝ))) * (1 + |Real.log r|) ^ (b + 1)) := by
      intro i
      have := (hRi i).2 p q' (by omega) X z hz
      rw [hEq] at this
      exact this
    calc ∑ i : Fin d, ‖mixedJet p q' (rawNewton nu chi (H i)) X z‖
        ≤ ∑ _i : Fin d, CIH * (cz * A) * pw *
            (1 + r ^ (-((σ - 2) + ((q' + 1 : ℕ) : ℝ))) * (1 + |Real.log r|) ^ (b + 1)) :=
          Finset.sum_le_sum fun i _ => hbi i
      _ = (d * (CIH * cz)) * A * pw *
            (1 + r ^ (-((σ - 2) + ((q' + 1 : ℕ) : ℝ))) * (1 + |Real.log r|) ^ (b + 1)) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ ≤ (Cw * cz * Kw + d * (CIH * cz)) * A * pw *
            (1 + r ^ (-((σ - 2) + ((q' + 1 : ℕ) : ℝ))) * (1 + |Real.log r|) ^ (b + 1)) := by
          have h0 : 0 ≤ Cw * cz * Kw := by positivity
          have h1 : 0 ≤ A * pw * (1 + r ^ (-((σ - 2) + ((q' + 1 : ℕ) : ℝ))) * (1 + |Real.log r|) ^ (b + 1)) := by
            positivity
          nlinarith [mul_nonneg h0 h1]

end HRS.MS.R26T8A
