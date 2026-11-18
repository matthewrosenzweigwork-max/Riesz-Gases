import HRS.MS.MfeConfAux140

/-!
# S.B.1 (SB5), packet R3a (part 1): laws of the regularised flow under a conditioned initial law

* `sb1_flowLaw_dom`: law-level canonical-Gibbs domination of `sb1Flow` (the content of `sb1_Y_dom` without any process);
* `sb1_cond_flow_law`: for an event `A = (X 0)⁻¹ E` of the initial value, the conditioned measure `Pc = cond Pm A` has
  `Pc.map (Ys t) = sb1Flow (Pc.map (X 0)) ν t`, where `ν` is the (unconditioned) Wiener path law.
The filtration is *not* conditioned.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS HRS.Whole HRS.MD.EQLawPath HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d N : ℕ}

theorem sb1_flowLaw_dom (D : Whole.WholeDyn d) (hs0 : 0 ≤ D.s) (hd : 1 ≤ d) {B : ℝ} (P : Sb1Pot D.V B) (hθ : 0 < D.invβ)
    {cV CV : ℝ} (hcV : 0 < cV) (hV : ∀ x, cV * ‖x‖ ^ 2 - CV ≤ D.V x) {T : ℝ} (hT : 0 < T)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} (hW : IsBrownianFiltration Pm ℱ W')
    (M : ℕ) {μ : Measure (Whole.EucConfig d N)} {c0 : ℝ} (hc0 : 0 ≤ c0)
    (hbdd : μ ≤ ENNReal.ofReal c0 • sb1Dm (fun Z => sb1Gw D (Whole.rieszKernel d D.s) N Z))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    sb1Flow D (sb1kM d D.s M) N μ (Pm.map (bfPath hW)) t ≤
      ENNReal.ofReal c0 • sb1Dm (fun Z => sb1Gw D (sb1kM d D.s M) N Z) := by
  have hk := sb1kM_isKernel (d := d) D.s hs0 M
  have hHc := sb1_Hs_cont D hk P N
  have hlow := hk.lower
  have hz := sb1_gz_pos hθ hHc hlow hcV hV
  have hGM : ∀ Z, sb1Gw D (sb1kM d D.s M) N Z = sb1Gz D (sb1kM d D.s M) N * sb1Gq D (sb1kM d D.s M) N Z := by
    intro Z
    unfold sb1Gw sb1Gq
    field_simp
  have hscale : sb1Dm (fun Z => sb1Gw D (sb1kM d D.s M) N Z) =
      ENNReal.ofReal (sb1Gz D (sb1kM d D.s M) N) • sb1Gam D (sb1kM d D.s M) N := by
    unfold sb1Gam sb1Dm
    rw [← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    funext Z
    show ENNReal.ofReal (sb1Gw D (sb1kM d D.s M) N Z) = ENNReal.ofReal (sb1Gz D (sb1kM d D.s M) N) *
      ENNReal.ofReal (sb1Gq D (sb1kM d D.s M) N Z)
    rw [hGM Z, ENNReal.ofReal_mul hz.le]
  have hmono : sb1Dm (fun Z => sb1Gw D (Whole.rieszKernel d D.s) N Z) ≤ sb1Dm (fun Z => sb1Gw D (sb1kM d D.s M) N Z) := by
    unfold sb1Dm
    exact withDensity_mono ((sb1_sing_le D hθ hs0 hd M).mono fun Z hZ => ENNReal.ofReal_le_ofReal hZ)
  have hc : μ ≤ (ENNReal.ofReal c0 * ENNReal.ofReal (sb1Gz D (sb1kM d D.s M) N)) • sb1Gam D (sb1kM d D.s M) N := by
    refine hbdd.trans ?_
    rw [mul_smul, ← hscale]
    exact Measure.le_iff'.2 fun A => by
      simp only [Measure.smul_apply, smul_eq_mul]
      exact mul_le_mul' le_rfl (hmono A)
  haveI : IsProbabilityMeasure (Pm.map (bfPath hW)) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_bfPath hW).aemeasurable).2 inferInstance
  have hLip := sb1_driftM_isLip D hk P N
  have hΨm := sb1Ψ_meas (fun _ => sb1DriftM D (sb1kM d D.s M) N) hLip (p4r_sigma d N D.invβ) t
  unfold sb1Flow
  calc (μ.prod (Pm.map (bfPath hW))).map (sb1Ψ (fun _ => sb1DriftM D (sb1kM d D.s M) N) (p4r_sigma d N D.invβ) t)
      ≤ (((ENNReal.ofReal c0 * ENNReal.ofReal (sb1Gz D (sb1kM d D.s M) N)) • sb1Gam D (sb1kM d D.s M) N).prod
          (Pm.map (bfPath hW))).map
          (sb1Ψ (fun _ => sb1DriftM D (sb1kM d D.s M) N) (p4r_sigma d N D.invβ) t) :=
        Measure.map_mono (Measure.prod_mono hc le_rfl) hΨm
    _ = (ENNReal.ofReal c0 * ENNReal.ofReal (sb1Gz D (sb1kM d D.s M) N)) •
          ((sb1Gam D (sb1kM d D.s M) N).prod (Pm.map (bfPath hW))).map
          (sb1Ψ (fun _ => sb1DriftM D (sb1kM d D.s M) N) (p4r_sigma d N D.invβ) t) := by
        rw [Measure.prod_smul_left, Measure.map_smul _ hΨm.aemeasurable]
    _ = _ := by
        rw [sb1_gam_stationary D hk P hθ hcV hV hT hW ht, mul_smul, ← hscale]

end HRS.MS.MfeConf
