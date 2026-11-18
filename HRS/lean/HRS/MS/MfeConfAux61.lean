import HRS.MS.MfeConfAux60

/-!
# S.B.1, packet F6 (part 22): the `P4MolData` of a static gradient flow

`sb1_molData_static`: the laws of a gradient flow `dY = -∇H(Y) ds + √(2θ) dW` with a Lipschitz drift `b = -∇H` and the flow
hypotheses `P4FlowHyp` carry the data `P4MolData θ T b H 0 μ(clamp ·)` of the mollified entropy inequality
(`sb1_level_ineq`, with the explicit `∂_s H = 0`; the transplant of `p4m_data_of_hyp` without the confinement of `H`).
-/

open MeasureTheory Filter Topology InformationTheory
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Mol HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MS.MfeConf

variable {d N : ℕ}

theorem sb1_molData_static {θ T : ℝ} (hT : 0 ≤ T) {H : EucConfig d N → ℝ} {b : EucConfig d N → EucConfig d N}
    {Kl : ℝ≥0} (hbl : LipschitzWith Kl b) (hHc : Continuous H) (hH : ∀ x, HasFDerivAt H (-(p4InnerL (b x))) x)
    {μ : ℝ → Measure (EucConfig d N)} (hμ : P4FlowHyp θ (fun _ => b) T μ) :
    ∃ B K M CV : ℝ, P4MolData θ T (fun _ => b) (fun _ => H) (fun _ _ => 0)
      (fun r => μ (p4m_clamp T r)) Kl B K M CV := by
  have hbc : Continuous (Function.uncurry fun (_ : ℝ) => b) := hbl.continuous.comp continuous_snd
  have hlip : ∀ τ ∈ Set.Icc (0 : ℝ) T, LipschitzWith Kl ((fun _ : ℝ => b) τ) := fun τ _ => hbl
  obtain ⟨B, hB, hbg⟩ := p4m_b_growth hbc hlip
  obtain ⟨CV, hCV, hVg⟩ := p4m_V_bound (V := fun _ => H) (b := fun _ => b) (hHc.comp continuous_snd) hbc
    (fun _ x => hH x) hlip
  obtain ⟨C, hC, hmom⟩ := hμ.mom
  have hmem := p4m_clamp_mem hT
  have hcl := p4m_clamp_continuous T
  refine ⟨B, Kl, N * C.toReal, CV, ?_⟩
  exact
    { prob := fun r => hμ.prob _
      hm := fun r => (p4m_moment hC (hmom _ (hmem r))).1
      hM := fun r => (p4m_moment hC (hmom _ (hmem r))).2
      narrow := fun g hg hgb => (hμ.narrow g hg hgb).comp_continuous hcl hmem
      bc := hbc
      bl := fun r => hbl
      hB := hB
      hK := Kl.2
      bg := fun r y => hbg 0 ⟨le_rfl, hT⟩ y
      Vc := hHc.comp continuous_snd
      grad := fun r x => hH x
      Vg := fun r x => hVg 0 ⟨le_rfl, hT⟩ x
      Wc := continuous_const
      Wd := fun r hr x => hasDerivAt_const r (H x)
      Wle := fun r x => le_rfl
      fp := fun g hg t ht => by
        have e0 : p4m_clamp T 0 = 0 := p4m_clamp_eq ⟨le_rfl, hT⟩
        have et : p4m_clamp T t = t := p4m_clamp_eq ht
        simp only [e0, et]
        rw [hμ.fp g hg t ht]
        congr 1
        refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
        have hr' : r ∈ Set.Icc (0 : ℝ) T := ⟨hr.1, hr.2.trans ht.2⟩
        simp only [p4m_clamp_eq hr'] }

end HRS.MS.MfeConf
