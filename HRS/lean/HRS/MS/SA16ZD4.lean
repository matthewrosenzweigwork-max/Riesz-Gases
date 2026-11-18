import HRS.MS.SA16ZD3

/-!
# S.A.16 (SA16Z) D4: `‖Err_idx‖_p ≤ K Λ S_j(φ)`
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section D4
variable {d : ℕ} {s : ℝ}

/-- the commutator constants -/
theorem sa16z_comm_consts (hd : 1 ≤ d) {θ : ℝ} (hθ1 : 1 < θ) (hθ2 : θ < 2) {p : ℝ} (hp : 2 ≤ p) :
    ∃ cθ Ce Cp : ℝ, 0 ≤ Ce ∧ 0 ≤ Cp ∧
      (∀ {μ φ : Euc d → ℝ}, HRS.MemCb 2 μ → IsCcInfty φ → ∀ {k : ℕ} (κ : Fin k → Fin d),
        eLpNorm (fun x => sa16z_Rp d θ cθ μ (partialDeriv κ φ) x) (ENNReal.ofReal p) volume ≤
          ENNReal.ofReal (Ce * HRS.cbNorm 2 μ) * eLpNorm (partialDeriv κ φ) (ENNReal.ofReal p) volume) ∧
      (∀ {a φ : Euc d → ℝ}, HRS.MemCb 1 a → IsCcInfty φ → ∀ (l : Fin d) {k : ℕ} (κ : Fin k → Fin d),
        eLpNorm (fun x => sa16z_Cm d θ l a (partialDeriv κ φ) x) (ENNReal.ofReal p) volume ≤
          ENNReal.ofReal (Cp * HRS.cbNorm 1 a) * eLpNorm (partialDeriv κ φ) (ENNReal.ofReal p) volume) := by
  obtain ⟨cθ, C, hexp⟩ := HRS.CZ.ElemA.lp_Lambda_commutator_expansion_proof hd θ p hθ1 hθ2 hp
  have hcm : ∀ l : Fin d, ∃ Cl : ℝ, 0 ≤ Cl ∧ ∀ {a φ : Euc d → ℝ}, HRS.MemCb 1 a → IsCcInfty φ → ∀ {k : ℕ} (κ : Fin k → Fin d),
      eLpNorm (fun x => sa16z_Cm d θ l a (partialDeriv κ φ) x) (ENNReal.ofReal p) volume ≤
          ENNReal.ofReal (Cl * HRS.cbNorm 1 a) * eLpNorm (partialDeriv κ φ) (ENNReal.ofReal p) volume := by
    intro l
    obtain ⟨C0, h0⟩ := HRS.CZ.Asm15.lp_positive_order_product_proof hd θ p hθ1 hθ2 hp l
    refine ⟨max C0 0, le_max_right _ _, fun {a φ} ha hφ {k} κ => ?_⟩
    have := (h0 a ha).1 (sa16z_schw (sa16s_cc_partialDeriv hφ κ))
    exact this.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) sa16z_cbNorm_nonneg)) le_rfl)
  choose Cl hCl0 hCl using hcm
  refine ⟨cθ, max C 0, ∑ l, Cl l, le_max_right _ _, Finset.sum_nonneg fun l _ => hCl0 l, ?_, ?_⟩
  · intro μ φ hμ hφ k κ
    have := hexp μ hμ (sa16z_schw (sa16s_cc_partialDeriv hφ κ))
    have e : (fun x => sa16z_Rp d θ cθ μ (partialDeriv κ φ) x) = fun x => lamComm d θ μ (sa16z_schw (sa16s_cc_partialDeriv hφ κ)) x -
        cθ * ∑ i : Fin d, gradient μ x i * pvOdd d θ (fun u : Euc d => u i) (sa16z_schw (sa16s_cc_partialDeriv hφ κ)) x := by
      funext x
      simp only [sa16z_Rp, sa16z_dm, sa16z_pv]
      congr 3
      funext i
      rw [sa16sp_gradient_apply]
      rfl
    rw [e]
    exact this.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) sa16z_cbNorm_nonneg)) le_rfl)
  · intro a φ ha hφ l k κ
    refine (hCl l ha hφ κ).trans ?_
    have : Cl l ≤ ∑ l, Cl l := Finset.single_le_sum (f := Cl) (fun l _ => hCl0 l) (Finset.mem_univ l)
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right this sa16z_cbNorm_nonneg)) le_rfl

end D4

end HRS.Whole.AppendixA.Phase2SA16R
