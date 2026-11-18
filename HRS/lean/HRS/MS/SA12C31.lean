import HRS.MS.SA12C30

/-!
# S.A.12(c), packet E7.05 (part 3): the averaged cell functionals, and the Young splitting of the pairing
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12C

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
open HRS.MH.AdjointRd.Phase2SA12Construction HRS.MH.AdjointRd.Phase2SA12 HRS.MH.AdjointRd.Phase2SA12Near

variable {d : ℕ}

/-- Integrability in `c` of the inner integrals. -/
theorem sa12c_inner_int {L : ℝ} {χ χh : Euc d → ℝ} (hχ : IsCutoffPair χ χh) {h : Euc d → ℝ}
    (hh : Continuous h) (p : Euc d) :
    Integrable (fun c => ∫ x, χ (x - (c + p)) ^ 2 * h x) (volume.restrict (periodBox d L)) := by
  refine sa12v_integrableOn_box L (sa12c_avg_inner_cont (F := fun c x => χ (x - (c + p)) ^ 2 * h x) ?_
    (R := 2 + ‖p‖) ?_)
  · exact (((hχ.1.1.continuous.comp (continuous_snd.sub (continuous_fst.add continuous_const))).pow 2).mul
      (hh.comp continuous_snd))
  · intro c x hx
    have : 2 ≤ ‖x - (c + p)‖ := by
      calc 2 ≤ ‖x - c‖ - ‖p‖ := by linarith
        _ ≤ ‖x - (c + p)‖ := by
          have := norm_sub_le_norm_sub_add_norm_sub x (c + p) c
          have h2 : ‖(c + p) - c‖ = ‖p‖ := by congr 1; abel
          linarith
    simp [sa12c_chi_support hχ _ this]

theorem sa12c_avg_jetPair {L : ℝ} (hL : 0 < L) {χ χh : Euc d → ℝ} (hχ : IsCutoffPair χ χh) {m : ℕ}
    {F G : Euc d → ℝ} (hF : ContDiff ℝ ∞ F) (hG : ContDiff ℝ m G)
    (hFp : ∀ (x : Euc d) (k : Fin d → ℤ), F (x + L • latticePt k) = F x)
    (hGp : ∀ (x : Euc d) (k : Fin d → ℤ), G (x + L • latticePt k) = G x) :
    Integrable (fun c => jetPair m (fun x => χ (x - c)) F G) (volume.restrict (periodBox d L)) ∧
    ∫ c in periodBox d L, jetPair m (fun x => χ (x - c)) F G = (∫ v, χ v ^ 2) * boxJetPair m L F G := by
  unfold jetPair boxJetPair
  have hterm : ∀ j ∈ Finset.range (m + 1), ∀ α : Fin j → Fin d,
      ∫ c in periodBox d L, ∫ x, (fun x => χ (x - c)) x ^ 2 *
        (partialDeriv α F x * partialDeriv α G x) =
      (∫ v, χ v ^ 2) * ∫ x in periodBox d L, partialDeriv α F x * partialDeriv α G x := by
    intro j hj α
    have hjm : j ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have hcN : Continuous (partialDeriv α G) :=
      (sa12x2_pd_cd (k := 0) (by simpa using hG.of_le (by exact_mod_cast hjm)) α).continuous
    have hc : Continuous fun x => partialDeriv α F x * partialDeriv α G x := (sa12c_pd_cont hF α).mul hcN
    have hper : ∀ (x : Euc d) (k : Fin d → ℤ), partialDeriv α F (x + L • latticePt k) *
        partialDeriv α G (x + L • latticePt k) = partialDeriv α F x * partialDeriv α G x := by
      intro x k; rw [sa12c_pd_periodic hFp α x k, sa12c_pd_periodic hGp α x k]
    have := sa12c_avg_shift hL hχ hc hper 0
    simpa using this
  have hI : ∀ j ∈ Finset.range (m + 1), ∀ α : Fin j → Fin d,
      Integrable (fun c => ∫ x, (fun x => χ (x - c)) x ^ 2 * (partialDeriv α F x * partialDeriv α G x))
        (volume.restrict (periodBox d L)) := by
    intro j hj α
    have hjm : j ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have hcN : Continuous (partialDeriv α G) :=
      (sa12x2_pd_cd (k := 0) (by simpa using hG.of_le (by exact_mod_cast hjm)) α).continuous
    have := sa12c_inner_int (L := L) hχ ((sa12c_pd_cont hF α).mul hcN) 0
    simpa using this
  refine ⟨integrable_finset_sum _ fun j hj => (integrable_finset_sum _ fun α _ => hI j hj α).const_mul _, ?_⟩
  rw [integral_finset_sum _ fun j hj => (integrable_finset_sum _ fun α _ => hI j hj α).const_mul _]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [integral_const_mul, integral_finset_sum _ fun α _ => hI j hj α]
  simp_rw [hterm j hj]
  simp only [Finset.mul_sum]
  ring

end HRS.MH.AdjointRd.Phase2SA12C
