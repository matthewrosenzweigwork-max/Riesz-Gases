import HRS.MS.MfeConfAux102

/-!
# S.B.1, packet F9 (part 6): the level-`k` entropy inequality for the flow of an arbitrary initial law

For a probability measure `ν₀` on configuration space (finite second moment) the regularised flow started at `ν₀` has the laws
`m_t(ν₀) = (ν₀ ⊗ Wiener).map Ψ_t` (`sb1Flow`), realised on an enlarged probability space (`sb1_flow_of_init`).  Combining
`sb1_lv_ineq` with the source decomposition `sb1_lv_S_decomp` we get `sb1_ent_M`:
`H(m_t|Q^k_t) ≤ H(ν₀|Q^k_0) + ∫_0^t ∫ [-βN (C^k_s - E_{Q^k_s} C^k_s) + ∑_i B^k_s] dm_s ds`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory InformationTheory
open HRS HRS.Whole HRS.MD.EQLawPath HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Mol HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d N : ℕ}

/-- the law at time `t` of the regularised flow started at `ν₀`, driven by the noise path law `ν` -/
def sb1Flow (D : Whole.WholeDyn d) (k : Euc d → ℝ) (N : ℕ) (ν₀ : Measure (Whole.EucConfig d N))
    (ν : Measure (C(ℝ≥0, (Fin N × Fin d) → ℝ))) (t : ℝ) : Measure (Whole.EucConfig d N) :=
  (ν₀.prod ν).map (sb1Ψ (fun _ => sb1DriftM D k N) (p4r_sigma d N D.invβ) t)

theorem sb1_flowHyp_mono {θ S T : ℝ} {b : ℝ → EucConfig d N → EucConfig d N} {μ : ℝ → Measure (EucConfig d N)}
    (h : P4FlowHyp θ b S μ) (hT : T ≤ S) : P4FlowHyp θ b T μ where
  prob := h.prob
  mom := by
    obtain ⟨C, hC, hm⟩ := h.mom
    exact ⟨C, hC, fun t ht => hm t ⟨ht.1, ht.2.trans hT⟩⟩
  narrow := fun g hg hb => (h.narrow g hg hb).mono (Set.Icc_subset_Icc le_rfl hT)
  fp := fun g hg t ht => h.fp g hg t ⟨ht.1, ht.2.trans hT⟩

/-- **the flow of an arbitrary initial law**, realised on an enlarged probability space -/
theorem sb1_flow_of_init (D : Whole.WholeDyn d) {s r₀ : ℝ} {k : Euc d → ℝ} (hk : IsP4Kernel d s r₀ k) {B : ℝ}
    (P : Sb1Pot D.V B) (ν₀ : Measure (Whole.EucConfig d N)) [IsProbabilityMeasure ν₀] (S : ℝ)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} (hW : IsBrownianFiltration Pm ℱ W') :
    ∃ (Ω' : Type) (mΩ' : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
      (ℱ' : Filtration ℝ mΩ') (W'' : ℝ≥0 → Ω' → (Fin N × Fin d) → ℝ) (Wc : ℝ≥0 → Ω' → (Fin N → Euc d))
      (Y : ℝ≥0 → Ω' → Whole.EucConfig d N),
      P4AddSol P' D.invβ (fun _ => sb1DriftM D k N) S ℱ' W'' Wc Y ∧ law P' (Y 0) = ν₀ ∧
      ∀ t : ℝ, 0 ≤ t → law P' (Y (Real.toNNReal t)) = sb1Flow D k N ν₀ (Pm.map (bfPath hW)) t := by
  obtain ⟨Wn, hWn, -, hW0, hWc, hBF⟩ := exists_enlargement (Fin N × Fin d) (Whole.EucConfig d N) ν₀
  set P' : Measure (Whole.EucConfig d N × ((Fin N × Fin d) → WienerSeq)) :=
    ν₀.prod (Measure.pi fun _ : Fin N × Fin d => wienerMeasure) with hP'
  set ℱ' := generatedFiltration P' Prod.fst measurable_fst Wn hWn with hℱ'
  have hWsh : IsBrownianFiltration P' (p4r_shiftFil ℱ') Wn := p4r_shiftFil_brownian hBF
  have hY0 : ∀ u : ℝ, Measurable[p4r_shiftFil ℱ' u] (Prod.fst : Whole.EucConfig d N × ((Fin N × Fin d) → WienerSeq) → _) :=
    fun u => generatedFiltration_measurable_init P' Prod.fst measurable_fst Wn hWn (max u 0)
  have hLip := sb1_driftM_isLip D hk P N
  obtain ⟨Ys, hYs⟩ := exists_sde_solution_global_exists hWsh (fun _ => sb1DriftM D k N) hLip
    (p4r_sigma d N D.invβ) hY0
  set Wc : ℝ≥0 → (Whole.EucConfig d N × ((Fin N × Fin d) → WienerSeq)) → (Fin N → Euc d) :=
    fun u ζ i => WithLp.toLp 2 (fun j => Wn u ζ (i, j)) with hWc'
  have hF : IsWholeFilteredSolution P' ℱ' Wn Wc (fun _ ζ => ζ.1) := by
    have hadt : ∀ u : ℝ, Measurable[ℱ' u] (ofNNRealTime (fun (_ : ℝ≥0) (ζ : Whole.EucConfig d N × ((Fin N × Fin d) → WienerSeq)) => ζ.1) u) :=
      fun u => generatedFiltration_measurable_init P' Prod.fst measurable_fst Wn hWn u
    refine ⟨hBF, Eventually.of_forall fun ζ u i j => rfl,
      fun u => generatedFiltration_measurable_init P' Prod.fst measurable_fst Wn hWn u, ?_⟩
    exact (StronglyAdapted.isStronglyProgressive_of_continuous
      (fun u => (hadt u).stronglyMeasurable)
      (fun ζ => by
        show Continuous fun _ : ℝ => ζ.1
        exact continuous_const)).isProgressive
  have hA : P4AddSol P' D.invβ (fun _ => sb1DriftM D k N) S ℱ' Wn Wc (fun u ζ => Ys (u : ℝ) ζ) :=
    p4r_addSol hF hYs
  have hproj : P'.map (Prod.fst : Whole.EucConfig d N × ((Fin N × Fin d) → WienerSeq) → _) = ν₀ := by
    rw [hP', Measure.map_fst_prod, measure_univ, one_smul]
  refine ⟨_, inferInstance, P', inferInstance, ℱ', Wn, Wc, fun u ζ => Ys (u : ℝ) ζ, hA, ?_, ?_⟩
  · have : (fun ζ : Whole.EucConfig d N × ((Fin N × Fin d) → WienerSeq) => Ys ((0 : ℝ≥0) : ℝ) ζ) = Prod.fst :=
      funext fun ζ => by simpa using hYs.init ζ
    change P'.map (fun ζ : Whole.EucConfig d N × ((Fin N × Fin d) → WienerSeq) => Ys ((0 : ℝ≥0) : ℝ) ζ) = _
    rw [this, hproj]
  · intro t ht
    have hrepr := sb1_law_repr hWsh hLip (hY0 0) hYs ht
    have hν := bf_path_law_eq hWsh hW
    rw [hproj, hν] at hrepr
    have hYt : (fun ζ : Whole.EucConfig d N × ((Fin N × Fin d) → WienerSeq) => Ys ((Real.toNNReal t : ℝ≥0) : ℝ) ζ) = Ys t := by
      rw [Real.coe_toNNReal t ht]
    change P'.map (fun ζ : Whole.EucConfig d N × ((Fin N × Fin d) → WienerSeq) => Ys ((Real.toNNReal t : ℝ≥0) : ℝ) ζ) = _
    rw [hYt, hrepr]
    rfl

section EntM

variable {D : Whole.WholeDyn d} {T C B C3 : ℝ} {ρ : ℝ → Euc d → ℝ} (H : Sb1Tr3 D T C B C3 ρ) (hT : 0 ≤ T)
  {r₀ : ℝ} {k : Euc d → ℝ}

include H hT

/-- **the level-`k` entropy inequality for the flow of an arbitrary initial law**, with the decomposed source -/
theorem sb1_ent_M (hθ : 0 < D.invβ) (hN : 1 ≤ N) (hk4 : IsP4Kernel d D.s r₀ k)
    (Kf : ℝ → ℝ) (hKi : IntegrableOn Kf (Set.Icc 0 T))
    (hLip : ∀ t ∈ Set.Icc (0 : ℝ) T, Whole.HasLipBoundW (Whole.mfeTransportW D (ρ t)) (Kf t))
    (ν₀ : Measure (Whole.EucConfig d N)) [IsProbabilityMeasure ν₀] (hmom : ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂ν₀ < ⊤)
    (hfin0 : relEntropy ν₀ (Whole.modulatedGibbs k N D.invβ⁻¹ (Whole.withDensityReal (ρ 0))) ≠ ⊤)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} (hW : IsBrownianFiltration Pm ℱ W')
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    relEntropy (sb1Flow D k N ν₀ (Pm.map (bfPath hW)) t)
        (Whole.modulatedGibbs k N D.invβ⁻¹ (Whole.withDensityReal (ρ t))) ≠ ⊤ ∧
      (relEntropy (sb1Flow D k N ν₀ (Pm.map (bfPath hW)) t)
          (Whole.modulatedGibbs k N D.invβ⁻¹ (Whole.withDensityReal (ρ t)))).toReal ≤
        (relEntropy ν₀ (Whole.modulatedGibbs k N D.invβ⁻¹ (Whole.withDensityReal (ρ 0)))).toReal +
          ∫ s in Set.Icc (0 : ℝ) t, ∫ y, (-(D.invβ⁻¹ * N) * (sb1_lv_Ck D k N ρ s y - sb1_lv_EQ D k N ρ s) +
            sb1_lv_B D k hT ρ s y) ∂(sb1Flow D k N ν₀ (Pm.map (bfPath hW)) s) := by
  obtain ⟨Ω', mΩ', P', hP', ℱ', W'', Wc, Y, hA, h0, hlaw⟩ := sb1_flow_of_init D hk4 H.tr.V ν₀ (T + 1) hW
  have hS : (0 : ℝ) < T + 1 := by linarith
  have hμ0 := sb1_flow_hyp D H.tr.V hk4 hθ.le hS hA (by rw [h0]; exact hmom)
  have hμ := sb1_flowHyp_mono hμ0 (by linarith : T ≤ T + 1)
  obtain ⟨Kl, B', K', M', CV', hMol⟩ := sb1_molData_regularised hT D hk4 H.tr.V N hμ
  have hmT : ∀ r ∈ Set.Icc (0 : ℝ) T, law P' (Y (Real.toNNReal (p4m_clamp T r))) =
      sb1Flow D k N ν₀ (Pm.map (bfPath hW)) r := fun r hr => by
    rw [p4m_clamp_eq hr]; exact hlaw r hr.1
  have h00 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  have hfin0' : relEntropy (law P' (Y (Real.toNNReal (p4m_clamp T 0))))
      (Whole.modulatedGibbs k N D.invβ⁻¹ (Whole.withDensityReal (ρ 0))) ≠ ⊤ := by
    rw [hmT 0 h00]
    have : sb1Flow D k N ν₀ (Pm.map (bfPath hW)) 0 = ν₀ := by
      rw [← hlaw 0 le_rfl, Real.toNNReal_zero, h0]
    rw [this]; exact hfin0
  have key := sb1_lv_ineq H hT hθ hN hk4 Kf hKi hLip hMol hfin0' ht
  rw [hmT t ht, hmT 0 h00] at key
  obtain ⟨hne, hle⟩ := key
  have hm0 : sb1Flow D k N ν₀ (Pm.map (bfPath hW)) 0 = ν₀ := by
    rw [← hlaw 0 le_rfl, Real.toNNReal_zero, h0]
  rw [hm0] at hle
  refine ⟨hne, hle.trans (le_of_eq ?_)⟩
  congr 1
  refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
  have hsT : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans ht.2⟩
  rw [hmT s hsT]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  exact sb1_lv_S_decomp H hT hk4 hθ hN hsT y

end EntM

end HRS.MS.MfeConf
