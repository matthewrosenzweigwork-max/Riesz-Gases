import HRS.MS.SA12X3C15G
import HRS.MS.SA12CellR35
import HRS.MS.SA12Z3NearN7E

/-!
# S.A.12 C15 (SA12X3), part H: the cell dissipation of a classical solution is continuous in time
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12 HRS.MH.AdjointRd.Phase2SA12Near

variable {d : ℕ}

theorem sa12x3_cellDissip_cont (hd : 1 ≤ d) (m : ℕ) (Cb T : ℝ) (χ χh : Euc d → ℝ) (hχ : IsCutoffPair χ χh)
    (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d) (hb : IsAdvectingDrift m Cb T b)
    (hΨ : IsNegDriftFlow T b Ψ) (ν : ℝ) (G : ℝ → Euc d → ℝ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T)
    (F : ℝ → Euc d → ℝ) (hF : IsClassicalSol m ν b G t F) (c : Euc d) :
    ContinuousOn (fun τ => cellDissip m χ Ψ τ c (F τ)) (Icc (0 : ℝ) t) := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have ht0 : 0 ≤ t := ht.1
  have hfl := HRS.MS.UniqC3.uc3_flowFacts hT hb hΨ
  have hsub : Icc (0 : ℝ) t ×ˢ (univ : Set (Euc d)) ⊆ Icc (0 : ℝ) T ×ˢ univ :=
    prod_mono (Icc_subset_Icc_right ht.2) subset_rfl
  obtain ⟨B, R, -, -, hf⟩ := advected_cutoff_jets d hd m Cb T χ χh hχ
  obtain ⟨Mc, hMc⟩ : ∃ Mc : ℝ, ∀ σ ∈ Icc (0 : ℝ) t, ‖Ψ σ c‖ ≤ Mc := by
    have hcomp : IsCompact (Icc (0 : ℝ) t ×ˢ ({c} : Set (Euc d))) := isCompact_Icc.prod isCompact_singleton
    have hcont : ContinuousOn (fun p : ℝ × Euc d => Ψ p.1 p.2) (Icc (0 : ℝ) t ×ˢ ({c} : Set (Euc d))) :=
      hfl.cont.mono (prod_mono (Icc_subset_Icc_right ht.2) (subset_univ _))
    obtain ⟨M, hM⟩ := hcomp.exists_bound_of_continuousOn hcont
    exact ⟨M, fun σ hσ => hM (σ, c) ⟨hσ, rfl⟩⟩
  have hsupp : ∀ σ ∈ Icc (0 : ℝ) t, ∀ x : Euc d, |Mc| + R < ‖x‖ → advCutoff χ Ψ σ c x = 0 := by
    intro σ hσ x hx
    by_contra hne
    have h1 := (sa12z3_adv_support_le hχ Ψ σ c) (Function.mem_support.2 hne)
    have h2 := (hf b Ψ hb hΨ σ ⟨hσ.1, hσ.2.trans ht.2⟩ c).2.2 h1
    rw [mem_closedBall, dist_eq_norm] at h2
    have h3 : ‖x‖ ≤ ‖x - Ψ σ c‖ + ‖Ψ σ c‖ := by
      calc ‖x‖ = ‖(x - Ψ σ c) + Ψ σ c‖ := by simp
        _ ≤ _ := norm_add_le _ _
    have := hMc σ hσ
    linarith [le_abs_self Mc]
  have hw : ContinuousOn (fun p : ℝ × Euc d => advCutoff χ Ψ p.1 c p.2) (Icc (0 : ℝ) t ×ˢ univ) := by
    have := (hfl.cont_inv.mono hsub).sub (continuousOn_const (c := c))
    exact hχ.1.1.continuous.comp_continuousOn this
  unfold cellDissip dissipSq
  refine continuousOn_finsetSum _ fun j _ => ?_
  refine ContinuousOn.mul continuousOn_const ?_
  refine continuousOn_finsetSum _ fun idx _ => ?_
  refine continuousOn_finsetSum _ fun i _ => ?_
  refine sa12x3_param_cont (R := |Mc| + R) ht0 ?_ ?_
  · exact (hw.mul (hF.contF (j + 1) (Fin.snoc idx i))).pow 2
  · intro σ hσ x hx
    show (advCutoff χ Ψ σ c x * _) ^ 2 = 0
    rw [hsupp σ hσ x hx]; simp

end HRS.MH.AdjointRd.Phase2SA12Construction
