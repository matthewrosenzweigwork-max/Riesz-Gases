import HRS.MS.R26T8AY3a
import HRS.MS.R26T8AY3b0

/-!
# S8.2 T8A Y3b: mixed jets of order `q+1` from `x`-derivative jets (Riesz version of Z5c)
`r26t8a_Y3b_jets`: `R0` is `C^{k'+1}` off the diagonal, `Ri i = dx_i R0` for `|x-y| < 1`.  For `p + q ≤ k'`, `0 < |z| < 1/2`:
`‖mixedJet p (q+1) R0 X z‖ ≤ Σ_i (‖mixedJet p q (Ri i) X z‖ + ‖mixedJet (p+1) q R0 X z‖)`.
Uses `∂_z = ∂_x - (1/2) ∂_X`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

set_option maxHeartbeats 1600000 in
theorem r26t8a_Y3b_jets {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {k' : ℕ} {R0 : Euc d → Euc d → ℝ}
    (Ri : Fin d → Euc d → Euc d → ℝ)
    (hR0 : ContDiffOn ℝ ((k' + 1 : ℕ) : WithTop ℕ∞) (Function.uncurry R0) {p : Euc d × Euc d | p.1 ≠ p.2})
    (hRi : ∀ i, ContDiffOn ℝ (k' : WithTop ℕ∞) (Function.uncurry (Ri i)) {p : Euc d × Euc d | p.1 ≠ p.2})
    (hx : ∀ i x y, x ≠ y → ‖x - y‖ < 1 → r26t8a_dx i R0 x y = Ri i x y)
    (p q : ℕ) (hpq : p + q ≤ k') (X z : Euc d) (hz : z ≠ 0) (hz1 : ‖z‖ < 1 / 2) :
    ‖mixedJet p (q + 1) R0 X z‖ ≤
      ∑ i : Fin d, (‖mixedJet p q (Ri i) X z‖ + ‖mixedJet (p + 1) q R0 X z‖) := by
  have hR01 : ContDiffOn ℝ 1 (Function.uncurry R0) {p : Euc d × Euc d | p.1 ≠ p.2} :=
    hR0.of_le (by exact_mod_cast (by omega : 1 ≤ k' + 1))
  have hder : ∀ X' w : Euc d, w ≠ 0 → ‖w‖ < 1 → DifferentiableAt ℝ (fun w' => midPair R0 X' w') w ∧
      ∀ i, fderiv ℝ (fun w' => midPair R0 X' w') w (r26t8a_e d i) =
        midPair (r26t8a_pdir (0, r26t8a_e d i) R0) X' w := by
    intro X' w hw _
    have h1 := r26t8a_midPair_contDiffOn hR01
    have h2 : ContDiffOn ℝ 1 (fun w' : Euc d => (fun Yw : Euc d × Euc d => midPair R0 Yw.1 Yw.2) (X', w')) {0}ᶜ :=
      h1.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun w' hw' => hw')
    refine ⟨(h2.contDiffAt (isOpen_compl_singleton.mem_nhds hw)).differentiableAt (by norm_num), fun i => ?_⟩
    rw [r26t8a_Z4a_slice hR01 X' w hw]
  have hmain := r26t8a_Z5c_jets hchi (k' := k') (R0 := R0) (fun i => r26t8a_pdir (0, r26t8a_e d i) R0)
    hR0 (fun i => r26t8a_pdir_contDiffOn hR0 _) hder p q hpq X z hz hz1
  refine hmain.trans (Finset.sum_le_sum fun i _ => ?_)
  set G := r26t8a_pdir (0, r26t8a_e d i) R0 with hG
  set H := r26t8a_pdir (((1 / 2 : ℝ) • r26t8a_e d i), 0) R0 with hH
  have hGc : ContDiffOn ℝ (k' : WithTop ℕ∞) (Function.uncurry G) {p : Euc d × Euc d | p.1 ≠ p.2} :=
    r26t8a_pdir_contDiffOn hR0 _
  have hHc : ContDiffOn ℝ (k' : WithTop ℕ∞) (Function.uncurry H) {p : Euc d × Euc d | p.1 ≠ p.2} :=
    r26t8a_pdir_contDiffOn hR0 _
  have hRiG : mixedJet p q (Ri i) X z = mixedJet p q G X z + mixedJet p q H X z := by
    rw [← r26t8a_Y3a_jet_add hchi hGc hHc p q hpq X z hz]
    refine (r26t8a_Y3a_jet_congr p q X z (fun x y hxy h1 => ?_) hz hz1).symm
    rw [← hx i x y hxy h1, r26t8a_Y3b0_dx_split hR0 i hxy]
  have hHn : ‖mixedJet p q H X z‖ ≤ ‖mixedJet (p + 1) q R0 X z‖ :=
    r26t8a_pdir_jet_X hchi hR0 _ (by
      rw [norm_smul, r26t8a_e_norm]; norm_num) p q hpq X z hz
  have : mixedJet p q G X z = mixedJet p q (Ri i) X z - mixedJet p q H X z := eq_sub_of_add_eq hRiG.symm
  rw [this]
  exact (norm_sub_le _ _).trans (add_le_add le_rfl hHn)

end HRS.MS.R26T8A
