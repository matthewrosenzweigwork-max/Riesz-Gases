import HRS.MS.SA16QFin3

/-!
# S.A.16 (SA16Q), E6 part 18: uniform bound for smooth weighted coefficients; data of the mollifications
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16Q
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixA.Phase2SA16

section Fin4
variable {d : ℕ} (hd : 2 ≤ d) {s : ℝ} (hs : 0 ≤ s) (hs2 : s ≤ (d : ℝ) - 2)
include hd hs hs2

theorem sa16q_unif_master {p : ℝ} (hp : 2 ≤ p) (hfar : (d : ℝ) < p * (s + 1)) (m : ℕ) (MB W : ℝ)
    (hW : 0 ≤ W) :
    ∃ K : ℝ≥0∞, K ≠ ⊤ ∧ ∀ (M : Matrix (Fin d) (Fin d) ℝ), (∀ i j, |M i j| ≤ MB) →
      ∀ {a : Euc d → ℝ} (ha : sa16q_SB a),
        (∀ κ ≤ m + 1, ∀ x, ‖iteratedFDeriv ℝ κ a x‖ ≤ W * (1 + ‖x‖) ^ (-((d + 3 : ℕ) : ℝ))) →
        ∀ (u : 𝓢(Euc d, ℝ)) {l : ℕ}, l ≤ m → ∀ (idx : Fin l → Fin d),
        eLpNorm (partialDeriv idx (HRS.MH.AdjointRd.eucNonlocal s M a ⇑u)) (ENNReal.ofReal p) volume ≤
          K * eLpNorm (wJet m (⇑u)) (ENNReal.ofReal p) volume := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨q, r, C1, C2, hq1, hqp, hqa, hr1, hr, hC1, hC2, hmaster⟩ :=
    sa16q_master_exps hd hs hs2 hp hfar
  have hp1 : 1 < p := by linarith
  obtain ⟨KP, hKP, hP⟩ := sa16q_term_unif hd1 hp1 hr1 hr m hW
  obtain ⟨KQ, hKQ, hQ⟩ := sa16q_term_unif hd1 hp1 hq1 (Or.inr ⟨hqp, hqa⟩) m hW
  refine ⟨((d : ℝ≥0∞) * (d : ℝ≥0∞) * ENNReal.ofReal MB) * ENNReal.ofReal (2 ^ m) *
      (ENNReal.ofReal C2 * KP + ENNReal.ofReal C1 * KQ), ?_, ?_⟩
  · refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top d) (ENNReal.natCast_ne_top d)) ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top) (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKP,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hKQ⟩)
  intro M hM a ha hκ u l hl idx
  set Wj := eLpNorm (wJet m (⇑u)) (ENNReal.ofReal p) volume with hWj
  have h2l : ENNReal.ofReal (2 ^ l) ≤ ENNReal.ofReal (2 ^ m) :=
    ENNReal.ofReal_le_ofReal (pow_le_pow_right₀ (by norm_num) hl)
  have hNP : sa16q_NP a u l r ≤ ENNReal.ofReal (2 ^ m) * (KP * Wj) :=
    (sa16q_NP_le (KP * Wj) (fun k hk => hP ha.1 hκ u (κ := k) (n := l - k) (by omega) (by omega))).trans
      (mul_le_mul' h2l le_rfl)
  have hNQ : sa16q_NQ a u l q ≤ ENNReal.ofReal (2 ^ m) * (KQ * Wj) :=
    (sa16q_NQ_le (KQ * Wj) (fun k hk => hQ ha.1 hκ u (κ := k + 1) (n := l - k) (by omega) (by omega))).trans
      (mul_le_mul' h2l le_rfl)
  refine (hmaster M MB hM ha u idx).trans ?_
  calc ((d : ℝ≥0∞) * (d : ℝ≥0∞) * ENNReal.ofReal MB) *
        (ENNReal.ofReal C2 * sa16q_NP a u l r + ENNReal.ofReal C1 * sa16q_NQ a u l q)
      ≤ ((d : ℝ≥0∞) * (d : ℝ≥0∞) * ENNReal.ofReal MB) *
        (ENNReal.ofReal C2 * (ENNReal.ofReal (2 ^ m) * (KP * Wj)) +
          ENNReal.ofReal C1 * (ENNReal.ofReal (2 ^ m) * (KQ * Wj))) :=
        sa16q_mul_le6 (add_le_add (sa16q_mul_le6 hNP) (sa16q_mul_le6 hNQ))
    _ = _ := by ring

end Fin4

section Fin4b
variable {d : ℕ}

/-- sup bound of a regular density -/
lemma sa16q_reg_abs {m : ℕ} {Λ : ℝ} {μ : Euc d → ℝ} (hμ : IsRegularDensityW (m + 3) Λ μ) (x : Euc d) :
    |μ x| ≤ max Λ 0 := by
  obtain ⟨hC, hbd, hw⟩ := sa16q_reg_data hμ
  have := hbd 0 (Nat.zero_le _) x
  rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this

lemma sa16q_reg_fderiv {m : ℕ} {Λ : ℝ} {μ : Euc d → ℝ} (hμ : IsRegularDensityW (m + 3) Λ μ) (x : Euc d) :
    ‖fderiv ℝ μ x‖ ≤ max Λ 0 := by
  obtain ⟨hC, hbd, hw⟩ := sa16q_reg_data hμ
  have := hbd 1 (by omega) x
  rwa [norm_iteratedFDeriv_one] at this

/-- the mollifications of a regular density: smooth bounded coefficients with uniform weights -/
lemma sa16q_mol_data (hd1 : 1 ≤ d) {m : ℕ} {Λ : ℝ} {μ : Euc d → ℝ} (hμ : IsRegularDensityW (m + 3) Λ μ)
    (N : ℕ) :
    sa16q_SB (sa16q_mol N μ) ∧
      (∀ κ ≤ m + 1, ∀ x, ‖iteratedFDeriv ℝ κ (sa16q_mol N μ) x‖ ≤
        (d : ℝ) ^ (m + 1) * (2 ^ (d + 3) * (2 ^ (d + 3) * max Λ 0)) * (1 + ‖x‖) ^ (-((d + 3 : ℕ) : ℝ))) := by
  obtain ⟨hC, hbd, hw⟩ := sa16q_reg_data hμ
  have hμc : Continuous μ := hC.continuous
  refine ⟨sa16q_mol_SB N hμc (sa16q_reg_abs hμ), fun κ hκ x => ?_⟩
  have hμκ : ContDiff ℝ κ μ := hC.of_le (by exact_mod_cast (by omega : κ ≤ m + 3))
  have hΛ : 0 ≤ max Λ 0 := le_max_right _ _
  have h1 := sa16q_weight_conv (a := sa16q_mol N μ) (κ := κ) (Λ2 := 2 ^ (d + 3) * (2 ^ (d + 3) * max Λ 0))
    (fun r y => sa16q_mol_pd_weight N hμκ (Λ1 := 2 ^ (d + 3) * max Λ 0)
      (fun r' y' => hw κ (by omega) r' y') r y) x
  refine h1.trans ?_
  have hω : 0 ≤ (1 + ‖x‖) ^ (-((d + 3 : ℕ) : ℝ)) := Real.rpow_nonneg (by positivity) _
  have hd0 : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hpw : (d : ℝ) ^ κ ≤ (d : ℝ) ^ (m + 1) := pow_le_pow_right₀ hd0 (by omega)
  have hc : 0 ≤ 2 ^ (d + 3) * (2 ^ (d + 3) * max Λ 0) := by positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpw hc) hω

end Fin4b

end HRS.Whole.AppendixA.Phase2SA16Q
