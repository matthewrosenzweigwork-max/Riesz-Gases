import HRS.MS.SA16Y4Ct4

/-!
# S.A.16 (SA16Y4) Ct5: the mollification operator `R_n` on `WmpSpace d k p`

`sa16y4_Rop k n`: a CLM `R` with `‖R‖ ≤ card(WIndex d k)` and `R (Jcc ψ) = Jcc (ρ_n ⋆ ψ)` for `ψ ∈ C_c^∞`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Q Phase2SA16Evolution Phase2SA16Transfer

section Ct5
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

lemma sa16y4_Jcc_norm' (k : ℕ) (ψ : ccSub d) :
    ‖sa16r_Jcc d k p ψ‖ = (eLpNorm (fun x => ‖wJet k ψ.1 x‖) (ENNReal.ofReal p) volume).toReal := by
  rw [sa16r_Jcc_norm d k p ψ, sa16y3_norm_wJet_eq ψ.2 k]

theorem sa16y4_Rop (k n : ℕ) :
    ∃ R : WmpSpace d k p →L[ℝ] WmpSpace d k p, ‖R‖ ≤ (Fintype.card (WIndex d k) : ℝ) ∧
      ∀ ψ : ccSub d, R (sa16r_Jcc d k p ψ) = sa16r_Jcc d k p ⟨sa16q_mol n ψ.1, sa16y4_mol_cc ψ.2 n⟩ := by
  have hp1 : 1 ≤ p := le_trans one_le_two (Fact.out : 2 ≤ p)
  have hc0 : (0 : ℝ) ≤ (Fintype.card (WIndex d k) : ℝ) := Nat.cast_nonneg _
  have hb : ∀ ψ : ccSub d, ‖sa16r_J d k p (sa16y4_Rl k p n ψ)‖ ≤ (Fintype.card (WIndex d k) : ℝ) * ‖sa16r_Jcc d k p ψ‖ := by
    intro ψ
    rw [sa16y4_Rl_eq, sa16y4_Jcc_norm', sa16y4_Jcc_norm']
    have hmc := sa16y4_mol_cc ψ.2 n
    have hE : eLpNorm (fun x => ‖wJet k (sa16q_mol n ψ.1) x‖) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (Fintype.card (WIndex d k) : ℝ) *
          eLpNorm (fun x => ‖wJet k ψ.1 x‖) (ENNReal.ofReal p) volume := by
      refine (sa16y4_jet_eLp_le hmc k hp1).trans ?_
      calc ∑ τ : WIndex d k, eLpNorm (partialDeriv τ.2 (sa16q_mol n ψ.1)) (ENNReal.ofReal p) volume
          ≤ ∑ τ : WIndex d k, eLpNorm (fun x => ‖wJet k ψ.1 x‖) (ENNReal.ofReal p) volume :=
            Finset.sum_le_sum fun τ _ => (sa16y3_mol_jet_le hp1 n ψ.2 τ.2).trans (sa16y4_pd_eLp_le_jet ψ.2 k τ)
        _ = ENNReal.ofReal (Fintype.card (WIndex d k) : ℝ) *
            eLpNorm (fun x => ‖wJet k ψ.1 x‖) (ENNReal.ofReal p) volume := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ENNReal.ofReal_natCast]
    have hfin : eLpNorm (fun x => ‖wJet k ψ.1 x‖) (ENNReal.ofReal p) volume ≠ ⊤ := by
      rw [sa16y3_norm_wJet_eq ψ.2 k]
      exact (sa16r_jet_memLp_cc (p := p) ψ.2 k).eLpNorm_lt_top.ne
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hE
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc0] at h2
    exact h2
  obtain ⟨R, hR1, hR2, -⟩ := sa16r_extend_cc d k k p (sa16y4_Rl k p n) hc0 hb
  exact ⟨R, hR1, fun ψ => by rw [hR2 ψ, sa16y4_Rl_eq]⟩

end Ct5

end HRS.Whole.AppendixA.Phase2SA16R
