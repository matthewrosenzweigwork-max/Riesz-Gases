/-
# HRS.Equilibrium.L49Aux3 — Proposition 4.9, part 3: radial integrals of the model functions

The model functions of the local computation (`R:eq:compensated-integral`), as radial functions
`w ↦ 1_{(ε,δ]}(|w|) |w|^{-a}`, their integrability and integrals (`l49_int_ind1`-`l49_int_ind4`).
-/
import HRS.Equilibrium.L49Aux2

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS

namespace L49

open HRS.LocalDivAux

variable {d : ℕ}

/-- The radial model function `1_{(ε,δ]}(|w|) |w|^{-a}`. -/
def l49_ind (d : ℕ) (ε δ a : ℝ) (w : Euc d) : ℝ :=
  (Ioc ε δ).indicator (fun r : ℝ => r ^ (-a)) ‖w‖

theorem l49_ind_nonneg (ε δ a : ℝ) (hε : 0 ≤ ε) (w : Euc d) : 0 ≤ l49_ind d ε δ a w := by
  unfold l49_ind
  by_cases h : ‖w‖ ∈ Ioc ε δ
  · rw [indicator_of_mem h]; exact Real.rpow_nonneg (hε.trans h.1.le) _
  · rw [indicator_of_notMem h]

theorem l49_measurable_ind (ε δ a : ℝ) : Measurable (l49_ind d ε δ a) := by
  unfold l49_ind
  exact ((Measurable.indicator (measurable_id.pow_const _) measurableSet_Ioc)).comp measurable_norm

theorem l49_ind_of_mem {ε δ a : ℝ} {w : Euc d} (h : ‖w‖ ∈ Ioc ε δ) :
    l49_ind d ε δ a w = ‖w‖ ^ (-a) := by
  unfold l49_ind; rw [indicator_of_mem h]

theorem l49_ind_of_notMem {ε δ a : ℝ} {w : Euc d} (h : ‖w‖ ∉ Ioc ε δ) :
    l49_ind d ε δ a w = 0 := by
  unfold l49_ind; rw [indicator_of_notMem h]

theorem l49_ind_supp {ε δ a : ℝ} {w : Euc d} (h : δ < ‖w‖) : l49_ind d ε δ a w = 0 :=
  l49_ind_of_notMem (fun hm => absurd hm.2 (not_le.2 h))

theorem l49_int_ind1 (hd : 1 ≤ d) {s rl : ℝ} (hs : 0 < s) (hds : (d : ℝ) = 2 * s) (hrl : 0 < rl) :
    Integrable (l49_ind d 0 rl s) ∧
      ∫ w, l49_ind d 0 rl s w = ballConst d * (rl ^ s / s) := by
  have hs1 : -1 < (d : ℝ) - 1 - s := by rw [hds]; linarith
  obtain ⟨h1, h2⟩ := l49_radial_ind hd (le_refl (0 : ℝ)) hrl.le s (Or.inl hs1)
  refine ⟨h1, ?_⟩
  unfold l49_ind
  rw [h2]
  congr 1
  have e : (d : ℝ) - 1 - s = s - 1 := by rw [hds]; ring
  rw [e, integral_rpow (Or.inl (by linarith : -1 < s - 1))]
  have e2 : s - 1 + 1 = s := by ring
  rw [e2, Real.zero_rpow hs.ne']
  ring

theorem l49_int_ind2 (hd : 1 ≤ d) {s rl δ : ℝ} (hs : 0 < s) (hds : (d : ℝ) = 2 * s) (hrl : 0 < rl)
    (hrd : rl ≤ δ) :
    Integrable (l49_ind d rl δ (2 * s - 1)) ∧
      ∫ w, l49_ind d rl δ (2 * s - 1) w = ballConst d * (δ - rl) := by
  obtain ⟨h1, h2⟩ := l49_radial_ind hd hrl.le hrd (2 * s - 1) (Or.inr hrl)
  refine ⟨h1, ?_⟩
  unfold l49_ind
  rw [h2]
  congr 1
  have e : (d : ℝ) - 1 - (2 * s - 1) = 0 := by rw [hds]; ring
  rw [e]
  simp

theorem l49_int_ind3 (hd : 1 ≤ d) {s rl δ : ℝ} (hs : 0 < s) (hds : (d : ℝ) = 2 * s) (hrl : 0 < rl)
    (hrd : rl ≤ δ) :
    Integrable (l49_ind d rl δ (3 * s)) ∧
      ∫ w, l49_ind d rl δ (3 * s) w ≤ ballConst d * (rl ^ (-s) / s) := by
  obtain ⟨h1, h2⟩ := l49_radial_ind hd hrl.le hrd (3 * s) (Or.inr hrl)
  refine ⟨h1, ?_⟩
  unfold l49_ind
  rw [h2]
  have e : (d : ℝ) - 1 - 3 * s = -s - 1 := by rw [hds]; ring
  have hδ : 0 < δ := hrl.trans_le hrd
  have hI : ∫ r in rl..δ, r ^ ((d : ℝ) - 1 - 3 * s) = (δ ^ (-s) - rl ^ (-s)) / (-s) := by
    rw [e, integral_rpow (Or.inr ⟨by linarith, by
      rw [uIcc_of_le hrd]; exact fun h => absurd h.1 (not_le.2 hrl)⟩)]
    have e2 : -s - 1 + 1 = -s := by ring
    rw [e2]
  rw [hI]
  have hδs : 0 ≤ δ ^ (-s) := Real.rpow_nonneg hδ.le _
  have : (δ ^ (-s) - rl ^ (-s)) / (-s) = (rl ^ (-s) - δ ^ (-s)) / s := by
    field_simp
    ring
  rw [this]
  refine mul_le_mul_of_nonneg_left ?_ ballConst_nonneg
  exact div_le_div_of_nonneg_right (by linarith) hs.le

theorem l49_int_ind4 (hd : 1 ≤ d) {s rl δ : ℝ} (hs : 0 < s) (hds : (d : ℝ) = 2 * s) (hrl : 0 < rl)
    (hrd : rl ≤ δ) :
    Integrable (l49_ind d rl δ (2 * s)) ∧
      ∫ w, l49_ind d rl δ (2 * s) w = ballConst d * (Real.log δ - Real.log rl) := by
  obtain ⟨h1, h2⟩ := l49_radial_ind hd hrl.le hrd (2 * s) (Or.inr hrl)
  refine ⟨h1, ?_⟩
  unfold l49_ind
  rw [h2]
  congr 1
  have e : (d : ℝ) - 1 - 2 * s = -1 := by rw [hds]; ring
  have hδ : 0 < δ := hrl.trans_le hrd
  rw [e]
  have : ∫ r in rl..δ, r ^ (-1 : ℝ) = ∫ r in rl..δ, r⁻¹ := by
    refine intervalIntegral.integral_congr fun r _ => ?_
    simp [Real.rpow_neg_one]
  rw [this, integral_inv_of_pos hrl hδ, Real.log_div hδ.ne' hrl.ne']

end L49

end HRS

end
