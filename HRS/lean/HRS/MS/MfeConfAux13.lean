import HRS.MS.MfeConfAux12

/-!
# S.B.1, packet F1 (part 8): from `WholeMFEHyp` to the classical trajectory

`sb1_traj_of_hyp`: the standing hypotheses of the frozen S.B.1 statements (`WholeMFEHyp`, `V ∈ C³` with bounded `D²V`,
`1 ≤ d`, `0 ≤ s < d`) give the data `Sb1Traj` with the uniform slice constant `C = d^r max(Λ,0) 2^{d+3}`.
`sb1_traj_classical`: hence the trajectory is a classical `C^{1,2}` test with time derivative `A(ρ_r)` (F1).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

open HRS.MP.RdGen HRS.MH.DualityRd

variable {d : ℕ}

theorem sb1_weightedSupE_mono {k k' : ℕ} (hk : k ≤ k') (L : ℝ) (f : Euc d → ℝ) :
    Whole.weightedSupE k L f ≤ Whole.weightedSupE k' L f := by
  unfold Whole.weightedSupE Whole.derivSupE
  refine iSup_le fun j => iSup_le fun i => iSup_le fun x => ?_
  exact le_iSup_of_le (⟨j, by omega⟩ : Fin (k' + 1)) (le_iSup_of_le i (le_iSup_of_le x le_rfl))

theorem sb1_regSlice_of_regular {r : ℕ} (hr : 3 ≤ r) {Λ : ℝ} {ρ : Euc d → ℝ}
    (hρ : Whole.IsProbDensity ρ) (hreg : Whole.IsRegularDensityW r Λ ρ) : RegSliceRd ρ := by
  have hw : Whole.weightedSupE r ((d : ℝ) + 3) ρ ≤ ENNReal.ofReal Λ := le_trans le_add_self hreg.2.2
  have hfin : Whole.weightedSupE r ((d : ℝ) + 3) ρ < ⊤ := lt_of_le_of_lt hw ENNReal.ofReal_lt_top
  exact ⟨hρ, ⟨hreg.2.1.1.of_le (by exact_mod_cast hr), fun j hj => hreg.2.1.2 j (hj.trans hr)⟩,
    lt_of_le_of_lt (sb1_weightedSupE_mono hr _ _) hfin⟩

/-- The data of the classical regularity packet from the frozen hypotheses. -/
theorem sb1_traj_of_hyp {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    {D : Whole.WholeDyn d} {N : ℕ} {T Λ : ℝ} {r : ℕ} {ρ : ℝ → Euc d → ℝ} {X₀ : Ω → Whole.EucConfig d N}
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Whole.EucConfig d N}
    (h : Whole.WholeMFEHyp P D N T Λ r ρ X₀ W X) (hd : 1 ≤ d) (hs0 : 0 ≤ D.s) (hsd : D.s < d)
    {B : ℝ} (hV : Sb1Pot D.V B) :
    Sb1Traj D T ((d : ℝ) ^ r * max Λ 0 * 2 ^ ((d : ℝ) + 3)) B ρ where
  hC := by positivity
  hd := hd
  hs0 := hs0
  hsd := hsd
  hM := h.gradient
  V := hV
  mf := h.mf
  slice := fun t ht => sb1_slice_of_regular hd h.r_ge (h.mf.density t ht) (h.mf_reg t ht)
  reg := fun t ht => sb1_regSlice_of_regular h.r_ge (h.mf.density t ht) (h.mf_reg t ht)

/-- **F1** (whole-space `movT_isC12Test_of_weak`): under the standing hypotheses of S.B.1 the mean-field trajectory is
`C^{1,2}` in the classical sense (`IsC12TestRd`) with `∂_t ρ_r = A(ρ_r) = β⁻¹ Δρ_r + Div(ρ_r(∇V + ∇g*ρ_r))`. -/
theorem sb1_traj_classical {Ω : Type*} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω}
    {D : Whole.WholeDyn d} {N : ℕ} {T Λ : ℝ} {r : ℕ} {ρ : ℝ → Euc d → ℝ} {X₀ : Ω → Whole.EucConfig d N}
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Whole.EucConfig d N}
    (h : Whole.WholeMFEHyp P D N T Λ r ρ X₀ W X) (hd : 1 ≤ d) (hs0 : 0 ≤ D.s) (hsd : D.s < d)
    (hV3 : ContDiff ℝ 3 D.V) (hV2 : ∃ B : ℝ, ∀ x, ‖iteratedFDeriv ℝ 2 D.V x‖ ≤ B) (hT : 0 ≤ T) :
    IsC12TestRd T ρ (fun s x => sb1A D (ρ s) x) := by
  obtain ⟨B, hB⟩ := hV2
  exact sb1_isC12TestRd (sb1_traj_of_hyp h hd hs0 hsd ⟨hV3, hB⟩) hT

end HRS.MS.MfeConf
