import HRS.MS.SA12X3C7C13

/-!
# S.A.12 C7 (SA12X3), part C14 (7C): a shifted flowed cube is controlled by the cell masses
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.MH.AdjointRd

variable {d : ℕ}

theorem sa12x3_mass_ge {Ψ : ℝ → Euc d → Euc d} {τ : ℝ} (hΨ : Continuous (Ψ τ)) {m : ℕ} (hm : 1 ≤ m)
    {F : Euc d → ℝ} (hF : ContDiff ℝ ∞ F) (j : Fin d) (z : Fin d → ℤ) :
    ∫ x in flowCell Ψ τ z, (fderiv ℝ F x (EuclideanSpace.single j (1 : ℝ))) ^ 2 ≤ cellMass m Ψ τ z F := by
  have hcpt := sa12x3_flowCell_compact hΨ z
  have hnn : ∀ (k : ℕ) (idx : Fin k → Fin d), 0 ≤ ∫ x in flowCell Ψ τ z, (partialDeriv idx F x) ^ 2 :=
    fun k idx => integral_nonneg fun x => sq_nonneg _
  unfold cellMass
  have h1 : (∫ x in flowCell Ψ τ z, (fderiv ℝ F x (EuclideanSpace.single j (1 : ℝ))) ^ 2) =
      ∫ x in flowCell Ψ τ z, (partialDeriv (fun _ : Fin 1 => j) F x) ^ 2 := by
    simp_rw [sa12x3_pd_one]
  rw [h1]
  have hinner : ∫ x in flowCell Ψ τ z, (partialDeriv (fun _ : Fin 1 => j) F x) ^ 2 ≤
      ∑ idx : Fin 1 → Fin d, ∫ x in flowCell Ψ τ z, (partialDeriv idx F x) ^ 2 :=
    Finset.single_le_sum (f := fun idx : Fin 1 → Fin d => ∫ x in flowCell Ψ τ z, (partialDeriv idx F x) ^ 2)
      (fun idx _ => hnn 1 idx) (Finset.mem_univ _)
  have hc : (1 : ℝ) ≤ (Nat.choose m 1 : ℝ) := by
    have : 1 ≤ Nat.choose m 1 := by rw [Nat.choose_one_right]; exact hm
    exact_mod_cast this
  have hterm : ∫ x in flowCell Ψ τ z, (partialDeriv (fun _ : Fin 1 => j) F x) ^ 2 ≤
      (Nat.choose m 1 : ℝ) * ∑ idx : Fin 1 → Fin d, ∫ x in flowCell Ψ τ z, (partialDeriv idx F x) ^ 2 := by
    calc _ ≤ ∑ idx : Fin 1 → Fin d, ∫ x in flowCell Ψ τ z, (partialDeriv idx F x) ^ 2 := hinner
      _ ≤ _ := le_mul_of_one_le_left (Finset.sum_nonneg fun idx _ => hnn 1 idx) hc
  refine hterm.trans ?_
  exact Finset.single_le_sum (f := fun k : ℕ => (Nat.choose m k : ℝ) *
    ∑ idx : Fin k → Fin d, ∫ x in flowCell Ψ τ z, (partialDeriv idx F x) ^ 2)
    (fun k _ => mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun idx _ => hnn k idx))
    (Finset.mem_range.2 (by omega))

theorem sa12x3_shifted_cell_le {Ψ : ℝ → Euc d → Euc d} {τ : ℝ} (hΨ : Continuous (Ψ τ)) {m : ℕ} (hm : 1 ≤ m)
    {F : Euc d → ℝ} (hF : ContDiff ℝ ∞ F) (j : Fin d) (z : Fin d → ℤ) {e : Euc d} (he0 : ∀ i, 0 ≤ e i)
    (he1 : ∀ i, e i < 1) :
    ENNReal.ofReal (∫ x in flowCellAt Ψ τ (latticePt z + e), (fderiv ℝ F x (EuclideanSpace.single j (1 : ℝ))) ^ 2) ≤
      ∑ ε : Fin d → Fin 2, ENNReal.ofReal (cellMass m Ψ τ (z + fun i => ((ε i : ℕ) : ℤ)) F) := by
  have hdc : Continuous (fun x => (fderiv ℝ F x (EuclideanSpace.single j (1 : ℝ))) ^ 2) :=
    (((hF.fderiv_right (m := ∞) (by simp)).continuous).clm_apply continuous_const).pow 2
  have hint : ∀ S : Set (Euc d), IsCompact S →
      IntegrableOn (fun x => (fderiv ℝ F x (EuclideanSpace.single j (1 : ℝ))) ^ 2) S :=
    fun S hS => hdc.continuousOn.integrableOn_compact hS
  have hA := sa12x3_flowCellAt_compact hΨ (latticePt z + e)
  rw [ofReal_integral_eq_lintegral_ofReal (hint _ hA) (Eventually.of_forall fun x => sq_nonneg _)]
  calc ∫⁻ x in flowCellAt Ψ τ (latticePt z + e), ENNReal.ofReal ((fderiv ℝ F x (EuclideanSpace.single j (1 : ℝ))) ^ 2)
      ≤ ∫⁻ x in ⋃ ε : Fin d → Fin 2, flowCell Ψ τ (z + fun i => ((ε i : ℕ) : ℤ)),
          ENNReal.ofReal ((fderiv ℝ F x (EuclideanSpace.single j (1 : ℝ))) ^ 2) :=
        lintegral_mono_set (sa12x3_cell_cover Ψ τ z he0 he1)
    _ ≤ ∑' ε : Fin d → Fin 2, ∫⁻ x in flowCell Ψ τ (z + fun i => ((ε i : ℕ) : ℤ)),
          ENNReal.ofReal ((fderiv ℝ F x (EuclideanSpace.single j (1 : ℝ))) ^ 2) := lintegral_iUnion_le _ _
    _ = ∑ ε : Fin d → Fin 2, ∫⁻ x in flowCell Ψ τ (z + fun i => ((ε i : ℕ) : ℤ)),
          ENNReal.ofReal ((fderiv ℝ F x (EuclideanSpace.single j (1 : ℝ))) ^ 2) := tsum_fintype _
    _ ≤ ∑ ε : Fin d → Fin 2, ENNReal.ofReal (cellMass m Ψ τ (z + fun i => ((ε i : ℕ) : ℤ)) F) := by
        refine Finset.sum_le_sum fun ε _ => ?_
        rw [← ofReal_integral_eq_lintegral_ofReal (hint _ (sa12x3_flowCell_compact hΨ _))
          (Eventually.of_forall fun x => sq_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (sa12x3_mass_ge hΨ hm hF j _)

end HRS.MH.AdjointRd.Phase2SA12Near
