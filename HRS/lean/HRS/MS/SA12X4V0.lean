import HRS.MS.SA12X4W3
import HRS.MS.LcWtAux1
import HRS.MS.UniqC3c
import HRS.MS.UniqC3

/-!
# S.A.12 (SA12X4) V0: three geometric facts for the comparison of the moving weighted energy with `varpiNormE`

* `sa12x4_varpi_comp`: `‖x-a‖ ≤ R → ⟨a⟩^{-p} ≤ c_R ⟨x⟩^{-p}` (Peetre);
* `sa12x4_lattice_count`: the number of fine-lattice centres within `R` of any point is bounded;
* `sa12x4_flow_growth`: `e^{-C_bτ}(1+‖y‖) ≤ 1+‖Ψ_τ y‖ ≤ e^{C_bτ}(1+‖y‖)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12X4

open HRS HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

theorem sa12x4_varpi_comp (p : ℝ) (hp : 0 ≤ p) (R : ℝ) (x a : Euc d) (h : ‖x - a‖ ≤ R) :
    jbracket a ^ (-p) ≤ (Real.sqrt 2 * Real.sqrt (1 + R ^ 2)) ^ p * jbracket x ^ (-p) := by
  have h1 := sa12x4_jbracket_peetre p hp x (x - a)
  rw [sub_sub_cancel] at h1
  refine h1.trans ?_
  have hj : jbracket (x - a) ≤ Real.sqrt (1 + R ^ 2) := by
    unfold jbracket
    refine Real.sqrt_le_sqrt ?_
    have : ‖x - a‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    linarith
  have hx0 : 0 ≤ jbracket x ^ (-p) := Real.rpow_nonneg (by unfold jbracket; positivity) _
  refine mul_le_mul_of_nonneg_right ?_ hx0
  exact Real.rpow_le_rpow (mul_nonneg (Real.sqrt_nonneg _) (by unfold jbracket; positivity))
    (mul_le_mul_of_nonneg_left hj (Real.sqrt_nonneg _)) hp

theorem sa12x4_lattice_count (hd : 1 ≤ d) (R : ℝ) :
    ∃ N : ℕ, ∀ x : Euc d, ∃ S : Finset (Fin d → ℤ), S.card ≤ N ∧
      ∀ c : Fin d → ℤ, ‖cellPt d c - x‖ ≤ R → c ∈ S := by
  classical
  have hfin := HRS.MH.AdjointRd.Phase2SA12Construction.sa12c12_finite_cells hd (R + 1)
  set K : Finset (Fin d → ℤ) := hfin.toFinset with hK
  refine ⟨K.card, fun x => ?_⟩
  obtain ⟨z, hz⟩ := HRS.MS.UniqC3.exists_cellPt_near hd x
  refine ⟨K.image (fun k => z + k), Finset.card_image_le, fun c hc => ?_⟩
  rw [Finset.mem_image]
  refine ⟨c - z, ?_, by simp⟩
  rw [hK, Set.Finite.mem_toFinset]
  show ‖cellPt d (c - z)‖ ≤ R + 1
  have hadd : cellPt d c = cellPt d z + cellPt d (c - z) := by
    have := HRS.MH.AdjointRd.Phase2SA12Near.sa12z3_cellPt_add (d := d) z (c - z)
    rw [add_sub_cancel] at this
    exact this
  have : cellPt d (c - z) = cellPt d c - cellPt d z := by rw [hadd]; abel
  rw [this]
  calc ‖cellPt d c - cellPt d z‖ = ‖(cellPt d c - x) + (x - cellPt d z)‖ := by congr 1; abel
    _ ≤ ‖cellPt d c - x‖ + ‖x - cellPt d z‖ := norm_add_le _ _
    _ ≤ R + 1 := by linarith

theorem sa12x4_flow_growth {m : ℕ} {Cb T : ℝ} (hT : 0 ≤ T) {b : ℝ → Euc d → Euc d}
    (hb : IsAdvectingDrift m Cb T b) {Ψ : ℝ → Euc d → Euc d} (hΨ : IsNegDriftFlow T b Ψ)
    {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T) (y : Euc d) :
    1 + ‖Ψ τ y‖ ≤ (1 + ‖y‖) * Real.exp (Cb * τ) ∧
      1 + ‖y‖ ≤ (1 + ‖Ψ τ y‖) * Real.exp (Cb * τ) := by
  have hCb : 0 ≤ Cb := HRS.MS.UniqC3.uc3_Cb_nonneg hT hb
  have hHyp := HRS.MS.FlowA.hyp_of_drift hT (HRS.MS.UniqC3.uc3_drift hb)
  have hsol : HRS.MS.FlowA.Sol T b (fun s => Ψ s y) :=
    HRS.MS.FlowA.sol_of_flow (HRS.MS.UniqC3.uc3_flow hΨ) y
  have h0 : Ψ 0 y = y := hΨ.init y
  refine ⟨?_, ?_⟩
  · have := HRS.MS.Lc.lc2_sol_growth hCb hHyp.growth hsol τ hτ
    rwa [h0] at this
  · have hrev := hHyp.rev hτ.2
    have hsτ : HRS.MS.FlowA.Sol τ b (fun s => Ψ s y) := hsol.mono hτ.2
    have hsr := hsτ.rev
    have := HRS.MS.Lc.lc2_sol_growth hCb hrev.growth hsr τ ⟨hτ.1, le_rfl⟩
    simp only [sub_self, sub_zero, h0] at this
    exact this

end HRS.MH.AdjointRd.Phase2SA12X4
