import HRS.MS.R26T8ARow2

/-!
# S8.2 row lemma, step 3: measurability of slice jets
`r26t8a_row_slice_cont`: for `Φ` globally `C^i`, `u |-> D^i_x Φ(., u)` is continuous.
`r26t8a_row_slice_meas`: if `Ψ_n` are `C^i` and equal `H u` on the `x`-slice for `u != 0` eventually, then `u |-> D^i (H u) x` is a.e. strongly measurable.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ContDiff
open HRS HRS.Whole HRS.MS.Phase2S82

namespace HRS.MS.R26T8A

variable {d : ℕ}

theorem r26t8a_row_slice_cont {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Φ : Euc d × Euc d → V} (i : ℕ)
    (hΦ : ContDiff ℝ (i : WithTop ℕ∞) Φ) (x : Euc d) :
    Continuous (fun u : Euc d => iteratedFDeriv ℝ i (fun x' : Euc d => Φ (x', u)) x) := by
  have hform : ∀ u : Euc d, iteratedFDeriv ℝ i (fun x' : Euc d => Φ (x', u)) x =
      (iteratedFDeriv ℝ i Φ (x, u)).compContinuousLinearMap (fun _ => ContinuousLinearMap.inl ℝ (Euc d) (Euc d)) := by
    intro u
    have h1 : (fun x' : Euc d => Φ (x', u)) = (fun p : Euc d × Euc d => Φ (p + (0, u))) ∘
        (ContinuousLinearMap.inl ℝ (Euc d) (Euc d)) := by
      funext x'; simp
    have hc : ContDiff ℝ (i : WithTop ℕ∞) (fun p : Euc d × Euc d => Φ (p + (0, u))) :=
      hΦ.comp (contDiff_id.add contDiff_const)
    rw [h1, ContinuousLinearMap.iteratedFDeriv_comp_right _ hc x le_rfl,
      iteratedFDeriv_comp_add_right (f := Φ) i (0, u)]
    simp
  simp_rw [hform]
  let hL : (ContinuousMultilinearMap ℝ (fun _ : Fin i => Euc d × Euc d) V) →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin i => Euc d) V :=
    ContinuousMultilinearMap.compContinuousLinearMapL (fun _ => ContinuousLinearMap.inl ℝ (Euc d) (Euc d))
  have hc : Continuous (fun u : Euc d => iteratedFDeriv ℝ i Φ (x, u)) :=
    (hΦ.continuous_iteratedFDeriv le_rfl).comp (continuous_const.prodMk continuous_id)
  have := hL.continuous.comp hc
  exact this.congr fun u => rfl

theorem r26t8a_row_slice_meas {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (hd : 2 ≤ d) (i : ℕ)
    (H : Euc d → Euc d → V) (Ψ : ℕ → Euc d × Euc d → V)
    (hΨ : ∀ n, ContDiff ℝ (i : WithTop ℕ∞) (Ψ n))
    (hev : ∀ u : Euc d, u ≠ 0 → ∀ᶠ n in atTop, ∀ x' : Euc d, Ψ n (x', u) = H u x') (x : Euc d) :
    AEStronglyMeasurable (fun u : Euc d => iteratedFDeriv ℝ i (H u) x) volume := by
  refine aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun n u => iteratedFDeriv ℝ i (fun x' : Euc d => Ψ n (x', u)) x) (fun n =>
      (r26t8a_row_slice_cont i (hΨ n) x).aestronglyMeasurable) ?_
  filter_upwards [r26t8a_ae_ne_zero hd] with u hu
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hev u hu] with n hn
  have : (fun x' : Euc d => Ψ n (x', u)) = H u := funext hn
  rw [this]

end HRS.MS.R26T8A
