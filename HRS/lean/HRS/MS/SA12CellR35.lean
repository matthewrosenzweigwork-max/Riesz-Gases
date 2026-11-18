import HRS.MH.AdjointRdDefs
import HRS.MS.UniqC3
import HRS.MS.FlowEAux1
import HRS.MS.FlowC

/-!
# S.A.12 R35: center-uniform jet budget of the advected cutoffs

`χ(Ψ_τ^{-1}(·) - z)` and its companion are `C^{m+1}` with every derivative of order `≤ m+1` bounded by a constant
independent of the centre, the time `τ ∈ [0,T]`, the drift and the flow (only the constants `m, Cb, T` and the
cutoff pair enter); the support of the companion lies in a ball of radius `R` about `Ψ_τ z`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd

theorem sa12r35_single_le_cb {d : ℕ} {k : ℕ} {f : Euc d → ℝ} (hf : MemCb k f) {j : ℕ} (hj : j ≤ k)
    (x : Euc d) : ‖iteratedFDeriv ℝ j f x‖ ≤ cbNorm k f := by
  unfold cbNorm
  refine le_trans ?_ (Finset.single_le_sum (f := fun j => ⨆ z : Euc d, ‖iteratedFDeriv ℝ j f z‖)
    (fun j _ => Real.iSup_nonneg fun z => norm_nonneg _) (Finset.mem_range.2 (Nat.lt_succ_of_le hj)))
  exact le_ciSup (hf.2 j hj) x

-- BEGIN SA12.R35
theorem advected_cutoff_jets (d : ℕ) (hd : 1 ≤ d) (m : ℕ) (Cb T : ℝ)
    (χ χh : Euc d → ℝ) (hχ : IsCutoffPair χ χh) :
    ∃ B R : ℝ, 0 < B ∧ 1 ≤ R ∧
      ∀ b : ℝ → Euc d → Euc d, ∀ Ψ : ℝ → Euc d → Euc d,
      IsAdvectingDrift m Cb T b → IsNegDriftFlow T b Ψ →
      ∀ τ ∈ Icc (0 : ℝ) T, ∀ z : Euc d,
      (ContDiff ℝ (m+1) (advCutoff χ Ψ τ z) ∧
        ContDiff ℝ (m+1) (advCutoff χh Ψ τ z)) ∧
      (∀ j ≤ m+1, ∀ x,
        ‖iteratedFDeriv ℝ j (advCutoff χ Ψ τ z) x‖ ≤ B ∧
        ‖iteratedFDeriv ℝ j (advCutoff χh Ψ τ z) x‖ ≤ B) ∧
      Function.support (advCutoff χh Ψ τ z) ⊆ Metric.closedBall (Ψ τ z) R := by
  by_cases hT : 0 ≤ T
  swap
  · refine ⟨1, 1, one_pos, le_rfl, fun b Ψ _ _ τ hτ => absurd (hτ.1.trans hτ.2) hT⟩
  obtain ⟨⟨hχ1, hχ2, hχ3, hχ4, hχ5⟩, ⟨hh1, hh2, hh3, hh4, hh5⟩⟩ := hχ
  obtain ⟨C0, hC0, hC0b⟩ := HRS.MS.FlowC.flow_iter_bound d m T Cb hT
  obtain ⟨K1, hK1, hK1b⟩ := HRS.MS.FlowE.cb_comp_bound (d := d) m χ hχ1 hχ2
  obtain ⟨K2, hK2, hK2b⟩ := HRS.MS.FlowE.cb_comp_bound (d := d) m χh hh1 hh2
  set D : ℝ := max 1 (max (Real.exp (|Cb| * T)) (C0 * Real.exp (C0 * m * T))) with hD
  have hD1 : 1 ≤ D := le_max_left _ _
  refine ⟨max (K1 * D ^ (m + 1)) (max (K2 * D ^ (m + 1)) 1),
    max 1 (8 * Real.exp (|Cb| * T)), lt_of_lt_of_le one_pos ((le_max_right _ _).trans (le_max_right _ _)),
    le_max_left _ _, fun b Ψ hb hΨ τ hτ z => ?_⟩
  have hF := HRS.MS.UniqC3.uc3_flowFacts hT hb hΨ
  have hbD := HRS.MS.UniqC3.uc3_drift hb
  have hinv := HRS.MS.UniqC3.uc3_hinv hΨ
  have hCb0 : 0 ≤ Cb := HRS.MS.UniqC3.uc3_Cb_nonneg hT hb
  have hexp : Real.exp (Cb * τ) ≤ Real.exp (|Cb| * T) := by
    refine Real.exp_le_exp.2 ?_
    calc Cb * τ ≤ |Cb| * τ := mul_le_mul_of_nonneg_right (le_abs_self Cb) hτ.1
      _ ≤ |Cb| * T := mul_le_mul_of_nonneg_left hτ.2 (abs_nonneg _)
  have hDexp : Real.exp (|Cb| * T) ≤ D := (le_max_left _ _).trans (le_max_right 1 _)
  have hDC : C0 * Real.exp (C0 * m * T) ≤ D := (le_max_right _ _).trans (le_max_right 1 _)
  have hDb : ∀ x, ∀ i : ℕ, 1 ≤ i → i ≤ m + 1 →
      ‖iteratedFDeriv ℝ i (Function.invFun (Ψ τ)) x‖ ≤ D := by
    intro x i hi1 hi2
    by_cases hi : i = 1
    · subst hi
      rw [norm_iteratedFDeriv_one (𝕜 := ℝ)]
      exact (HRS.MS.FlowB.fderiv_le_of_lip (Real.exp_pos _).le
        (fun x y => hF.lip_inv τ hτ x y) x).trans (hexp.trans hDexp)
    · have h2 := (hC0b b hbD Ψ (HRS.MS.UniqC3.uc3_flow hΨ) τ hτ).2 (Function.invFun (Ψ τ))
        (hinv τ hτ).1 (hinv τ hτ).2 i (by omega) hi2 x
      refine h2.trans (le_trans ?_ hDC)
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC0.le
      have : (0 : ℝ) ≤ C0 * m := by positivity
      exact mul_le_mul_of_nonneg_left hτ.2 this
  have hcb1 := hK1b D hD1 (Function.invFun (Ψ τ)) (hF.contDiff_inv τ hτ) hDb z
  have hcb2 := hK2b D hD1 (Function.invFun (Ψ τ)) (hF.contDiff_inv τ hτ) hDb z
  have hDpos : 0 ≤ D ^ (m + 1) := by positivity
  refine ⟨⟨hcb1.1.1, hcb2.1.1⟩, fun j hj x => ⟨?_, ?_⟩, ?_⟩
  · exact (sa12r35_single_le_cb hcb1.1 hj x).trans (hcb1.2.trans (le_max_left _ _))
  · exact (sa12r35_single_le_cb hcb2.1 hj x).trans
      (hcb2.2.trans ((le_max_left _ _).trans (le_max_right _ _)))
  · intro x hx
    have hxs : advCutoff χh Ψ τ z x ≠ 0 := hx
    have hxn : ‖Function.invFun (Ψ τ) x - z‖ < 8 := by
      by_contra hcon
      push Not at hcon
      apply hxs
      have : Function.invFun (Ψ τ) x - z ∉ tsupport χh := fun hmem => by
        have := hh3 hmem
        rw [Metric.mem_ball, dist_zero_right] at this
        linarith
      have h0 : χh (Function.invFun (Ψ τ) x - z) = 0 := image_eq_zero_of_notMem_tsupport this
      exact h0
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hx' : Ψ τ (Function.invFun (Ψ τ) x) = x := (hinv τ hτ).2 x
    calc ‖x - Ψ τ z‖ = ‖Ψ τ (Function.invFun (Ψ τ) x) - Ψ τ z‖ := by rw [hx']
      _ ≤ Real.exp (Cb * τ) * ‖Function.invFun (Ψ τ) x - z‖ := hF.lip τ hτ _ _
      _ ≤ Real.exp (|Cb| * T) * 8 :=
          mul_le_mul hexp hxn.le (norm_nonneg _) (Real.exp_pos _).le
      _ = 8 * Real.exp (|Cb| * T) := mul_comm _ _
      _ ≤ _ := le_max_right _ _
-- END SA12.R35

end HRS.MH.AdjointRd.Phase2SA12
