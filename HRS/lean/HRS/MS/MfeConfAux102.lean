import HRS.MS.MfeConfAux101
import HRS.Stochastic.Wiener

/-!
# S.B.1, packet F9 (part 5): canonical-Gibbs domination of the regularised flow (D01-D04 of the Pro note SB1-Dissipation)

* `sb1_gam_stationary`: `(Γ_k ⊗ Wiener).map Ψ_t = Γ_k` (the flow started at `Γ_k` on an enlarged space is `Γ_k` at every time, by the
  entropy argument `sb1_gam_invariant`; the law of the Brownian path does not depend on the space, `bf_path_law_eq`);
* `sb1_flow_dom`: **domination**: if the initial law of a regularised strong solution is `≤ c Γ_k`, then so is its law at every
  time `t ∈ [0,S]`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory InformationTheory
open HRS HRS.Whole HRS.MD.EQLawPath HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Mol HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d N : ℕ}

theorem sb1_gam_stationary (D : Whole.WholeDyn d) {s r₀ : ℝ} {k : Euc d → ℝ} (hk : IsP4Kernel d s r₀ k) {B : ℝ}
    (P : Sb1Pot D.V B) (hθ : 0 < D.invβ) {cV CV : ℝ} (hcV : 0 < cV) (hV : ∀ x, cV * ‖x‖ ^ 2 - CV ≤ D.V x)
    {S : ℝ} (hS : 0 < S) {Ω : Type*} [mΩ : MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} (hW : IsBrownianFiltration Pm ℱ W')
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S) :
    ((sb1Gam D k N).prod (Pm.map (bfPath hW))).map
        (sb1Ψ (fun _ => sb1DriftM D k N) (p4r_sigma d N D.invβ) t) = sb1Gam D k N := by
  have hHc := sb1_Hs_cont D hk P N
  haveI hΓ := sb1_gam_prob hθ hHc hk.lower hcV hV
  obtain ⟨Wn, hWn, -, hW0, hWc, hBF⟩ := exists_enlargement (Fin N × Fin d) (Whole.EucConfig d N) (sb1Gam D k N)
  set P' : Measure (Whole.EucConfig d N × ((Fin N × Fin d) → WienerSeq)) :=
    (sb1Gam D k N).prod (Measure.pi fun _ : Fin N × Fin d => wienerMeasure) with hP'
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
  have hlaw0 : law P' ((fun (u : ℝ≥0) (ζ : Whole.EucConfig d N × ((Fin N × Fin d) → WienerSeq)) => Ys (u : ℝ) ζ) 0) =
      sb1Gam D k N := by
    have : (fun ζ : Whole.EucConfig d N × ((Fin N × Fin d) → WienerSeq) => Ys ((0 : ℝ≥0) : ℝ) ζ) = Prod.fst :=
      funext fun ζ => by simpa using hYs.init ζ
    change P'.map (fun ζ : Whole.EucConfig d N × ((Fin N × Fin d) → WienerSeq) => Ys ((0 : ℝ≥0) : ℝ) ζ) = _
    rw [this, hP', Measure.map_fst_prod, measure_univ, one_smul]
  have hinv := sb1_gam_invariant D hk P hθ hcV hV hS hA hlaw0 ht
  have hYt : (fun ζ : Whole.EucConfig d N × ((Fin N × Fin d) → WienerSeq) => Ys ((Real.toNNReal t : ℝ≥0) : ℝ) ζ) = Ys t := by
    rw [Real.coe_toNNReal t ht.1]
  have hrepr := sb1_law_repr hWsh hLip (hY0 0) hYs ht.1
  have hproj : P'.map (Prod.fst : Whole.EucConfig d N × ((Fin N × Fin d) → WienerSeq) → _) = sb1Gam D k N := by
    rw [hP', Measure.map_fst_prod, measure_univ, one_smul]
  have hν := bf_path_law_eq hWsh hW
  rw [hproj, hν] at hrepr
  have : law P' ((fun (u : ℝ≥0) (ζ : Whole.EucConfig d N × ((Fin N × Fin d) → WienerSeq)) => Ys (u : ℝ) ζ) (Real.toNNReal t)) =
      sb1Gam D k N := hinv
  simp only [hYt] at this
  rw [← hrepr]
  exact this

/-- **canonical-Gibbs domination**: if the initial law of a regularised strong solution is dominated by `c Γ_k`, so is its law
at every time of `[0,S]` (D01-D04 of the Pro note SB1-Dissipation: no assumption on the measure other than the initial
comparison). -/
theorem sb1_flow_dom (D : Whole.WholeDyn d) {s r₀ : ℝ} {k : Euc d → ℝ} (hk : IsP4Kernel d s r₀ k) {B : ℝ}
    (P : Sb1Pot D.V B) (hθ : 0 < D.invβ) {cV CV : ℝ} (hcV : 0 < cV) (hV : ∀ x, cV * ‖x‖ ^ 2 - CV ≤ D.V x)
    {S : ℝ} (hS : 0 < S) {Ω : Type*} [mΩ : MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} (hW : IsBrownianFiltration Pm ℱ W')
    {Y₀ : Ω → Whole.EucConfig d N} (hY0 : Measurable[ℱ 0] Y₀) {Ys : ℝ → Ω → Whole.EucConfig d N}
    (hYs : IsAdditiveSDESolution Pm ℱ W' (fun _ => sb1DriftM D k N) (p4r_sigma d N D.invβ) Y₀ (fun _ => ⊤) Ys)
    {c : ℝ≥0∞} (hc : Pm.map Y₀ ≤ c • sb1Gam D k N) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S) :
    Pm.map (Ys t) ≤ c • sb1Gam D k N := by
  have hLip := sb1_driftM_isLip D hk P N
  haveI : IsProbabilityMeasure (Pm.map (bfPath hW)) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_bfPath hW).aemeasurable).2 inferInstance
  rw [sb1_law_repr hW hLip hY0 hYs ht.1]
  have hΨm := sb1Ψ_meas (fun _ => sb1DriftM D k N) hLip (p4r_sigma d N D.invβ) t
  calc ((Pm.map Y₀).prod (Pm.map (bfPath hW))).map (sb1Ψ (fun _ => sb1DriftM D k N) (p4r_sigma d N D.invβ) t)
      ≤ ((c • sb1Gam D k N).prod (Pm.map (bfPath hW))).map
          (sb1Ψ (fun _ => sb1DriftM D k N) (p4r_sigma d N D.invβ) t) :=
        Measure.map_mono (Measure.prod_mono hc le_rfl) hΨm
    _ = c • ((sb1Gam D k N).prod (Pm.map (bfPath hW))).map
          (sb1Ψ (fun _ => sb1DriftM D k N) (p4r_sigma d N D.invβ) t) := by
        rw [Measure.prod_smul_left, Measure.map_smul _ hΨm.aemeasurable]
    _ = c • sb1Gam D k N := by
        rw [sb1_gam_stationary D hk P hθ hcV hV hS hW ht]

end HRS.MS.MfeConf
