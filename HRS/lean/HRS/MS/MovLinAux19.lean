import HRS.MS.MovLinAux18

/-!
# MOV-LIN, part 10: short-time smoothing hypothesis for the adjoint semigroup `T(t)†` on `L²_0`

Namespace `HRS.MS.MovLin`, helpers `movlin_`.  Infrastructure for S6.2 (`W:lem:r2mov-linear`); not a manuscript row.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovLin

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1

variable {d : ℕ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

section AdjHs

variable {s : ℝ} {β q : ℝ} {ρ : Euc d → ℝ}

set_option maxHeartbeats 1600000 in
lemma movlin_adj_mem (H : Mov2dTh d s β q ρ) (ψ0 : 𝓢R)
    (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x)) {ρ' σ : ℝ} (hρ' : 0 ≤ ρ') (hρσ : ρ' ≤ σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ w W : MovL2Zero ρ,
      (∀ v : MovL2Zero ρ, inner ℝ (W : Lp ℝ 2 (volume : Measure (Euc d))) (v : Lp ℝ 2 (volume : Measure (Euc d))) =
        inner ℝ (w : Lp ℝ 2 (volume : Measure (Euc d)))
          ((mov2d_T H ψ0 hψ0 t v : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d)))) →
      MemOsc ρ' (movFun w) → MemOsc σ (movFun W) ∧
        oscNorm σ (movFun W) ≤ C * t ^ (-((σ - ρ') / 2)) * oscNorm ρ' (movFun w) := by
  obtain ⟨Cc, hCc, hC⟩ := movlin_adj_seq H ψ0 hρ' hρσ
  refine ⟨Cc, hCc, fun t ht w W hW hw => ?_⟩
  have hσ : 0 ≤ σ := hρ'.trans hρσ
  have hj : mov2d_j hρ' (OscSpace.ofFun ρ' (movFun w)) = (mov2d_Phi d).symm (w : Lp ℝ 2 (volume : Measure (Euc d))) := by
    rw [mov2d_j_ofFun hρ' hw]
    exact (movlin_L2_osc (w : Lp ℝ 2 (volume : Measure (Euc d)))).2.2
  have hu1 : inner ℝ (OscSpace.ofFun 0 (⇑ψ0 : Euc d → ℝ))
      ((mov2d_Phi d).symm (W : Lp ℝ 2 (volume : Measure (Euc d)))) = 0 :=
    movlin_orth H ψ0 hψ0 W
  have hpair : ∀ y : OscSpace d 0, inner ℝ (OscSpace.ofFun 0 (⇑ψ0 : Euc d → ℝ)) y = 0 →
      inner ℝ ((mov2d_Phi d).symm (W : Lp ℝ 2 (volume : Measure (Euc d)))) y =
      inner ℝ (mov2d_j hρ' (OscSpace.ofFun ρ' (movFun w))) (mov2d_G H 0 t y) := by
    intro y hy
    rw [hj]
    exact movlin_adj_pair H ψ0 hψ0 ht.1.le w W hW y hy
  obtain ⟨z, hz1, hz2⟩ := hC t ht (OscSpace.ofFun ρ' (movFun w)) _ hu1 hpair
  have hlev : mov2d_j hσ z = OscSpace.ofFun 0 (movFun W) := by
    rw [(movlin_L2_osc (W : Lp ℝ 2 (volume : Measure (Euc d)))).2.2]
    exact hz1
  obtain ⟨hm, hzeq⟩ := movlin_memOsc_of_lev hσ (Lp.memLp (W : Lp ℝ 2 (volume : Measure (Euc d)))) hlev
  refine ⟨hm, ?_⟩
  have e1 : oscNorm σ (movFun W) = ‖z‖ := by
    rw [← OscSpace.norm_ofFun _ hm, hzeq]
  rw [e1]
  have e2 : ‖OscSpace.ofFun ρ' (movFun w)‖ = oscNorm ρ' (movFun w) := OscSpace.norm_ofFun _ hw
  rw [e2] at hz2
  exact hz2

set_option maxHeartbeats 1600000 in
theorem movlin_Hs_adj (H : Mov2dTh d s β q ρ) (ψ0 : 𝓢R)
    (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x)) :
    HsOK (fun t => ContinuousLinearMap.adjoint (mov2d_T H ψ0 hψ0 t)) := by
  intro ρ' σ hρ' hρσ
  obtain ⟨C, hC0, hC⟩ := movlin_adj_mem H ψ0 hψ0 hρ' hρσ
  exact ⟨C, hC0, fun t ht w hw =>
    hC t ht w _ (fun v => movlin_adj_inner (mov2d_T H ψ0 hψ0 t) w v) hw⟩

end AdjHs

end HRS.MS.MovLin
