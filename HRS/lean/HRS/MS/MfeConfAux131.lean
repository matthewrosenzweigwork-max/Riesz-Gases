import HRS.MS.MfeConfAux130

/-!
# S.B.1, R2 (part 2): measurability in time of the level-`M` source mean

`sb1_ent_M_meas`: for the flow of an arbitrary initial law, `s ↦ ∫ [-βN(C^k_s - E_{Q^k_s}C^k_s) + B^k_s] dm_s` is
`AEStronglyMeasurable` on `[0,T]` (this is the hypothesis `hTM` of `sb1_bdd_movEnt`).
-/

open MeasureTheory Filter Topology ProbabilityTheory InformationTheory
open HRS HRS.Whole HRS.MD.EQLawPath HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Mol HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace HRS.MS.MfeConf

variable {d N : ℕ}

section EntM

variable {D : Whole.WholeDyn d} {T C B C3 : ℝ} {ρ : ℝ → Euc d → ℝ} (H : Sb1Tr3 D T C B C3 ρ) (hT : 0 ≤ T)
  {r₀ : ℝ} {k : Euc d → ℝ}

include H hT

theorem sb1_ent_M_meas (hθ : 0 < D.invβ) (hN : 1 ≤ N) (hk4 : IsP4Kernel d D.s r₀ k)
    (Kf : ℝ → ℝ) (hKi : IntegrableOn Kf (Set.Icc 0 T))
    (hLip : ∀ t ∈ Set.Icc (0 : ℝ) T, Whole.HasLipBoundW (Whole.mfeTransportW D (ρ t)) (Kf t))
    (ν₀ : Measure (Whole.EucConfig d N)) [IsProbabilityMeasure ν₀] (hmom : ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂ν₀ < ⊤)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} (hW : IsBrownianFiltration Pm ℱ W') :
    AEStronglyMeasurable (fun s => ∫ y, (-(D.invβ⁻¹ * N) * (sb1_lv_Ck D k N ρ s y - sb1_lv_EQ D k N ρ s) +
        sb1_lv_B D k hT ρ s y) ∂(sb1Flow D k N ν₀ (Pm.map (bfPath hW)) s)) (volume.restrict (Set.Icc 0 T)) := by
  obtain ⟨Ω', mΩ', P', hP', ℱ', W'', Wc, Y, hA, h0, hlaw⟩ := sb1_flow_of_init D hk4 H.tr.V ν₀ (T + 1) hW
  have hS : (0 : ℝ) < T + 1 := by linarith
  have hμ0 := sb1_flow_hyp D H.tr.V hk4 hθ.le hS hA (by rw [h0]; exact hmom)
  have hμ := sb1_flowHyp_mono hμ0 (by linarith : T ≤ T + 1)
  obtain ⟨Kl, B', K', M', CV', hMol⟩ := sb1_molData_regularised hT D hk4 H.tr.V N hμ
  have hmT : ∀ r ∈ Set.Icc (0 : ℝ) T, law P' (Y (Real.toNNReal (p4m_clamp T r))) =
      sb1Flow D k N ν₀ (Pm.map (bfPath hW)) r := fun r hr => by
    rw [p4m_clamp_eq hr]; exact hlaw r hr.1
  refine ((sb1_lv_src_int H hT hθ hN hk4 Kf hKi hLip hMol).aestronglyMeasurable).congr ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun s hs => ?_)
  dsimp only
  rw [hmT s hs]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => sb1_lv_S_decomp H hT hk4 hθ hN hs y)

end EntM

end HRS.MS.MfeConf
