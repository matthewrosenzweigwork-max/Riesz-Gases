import HRS.MS.MfeConfAux143

/-!
# S.B.1 (SB5), packet R3a (part 4): `SbMovEnt` for an initial law conditioned on an event of the initial value

`sb1_bdd_movEnt_cond`: for a measurable set `S` of configurations with `Pm (X₀ ∈ S) ≠ 0` and `Pc = cond Pm {X₀ ∈ S}`, if the conditioned
initial law is dominated by the unnormalised singular canonical Gibbs measure, then `SbMovEnt D N T ρ Pc X₀ X`.
The filtration is not conditioned: the regularised solutions `Ys` of the unconditioned space are used, and their conditioned laws are
identified through `sb1_cond_flow_law`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory InformationTheory
open HRS HRS.Whole HRS.MD.EQLawPath HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d N : ℕ}

section Main

variable {D : Whole.WholeDyn d} {T C B C3 : ℝ} {ρ : ℝ → Euc d → ℝ} (H : Sb1Tr3 D T C B C3 ρ)

include H

theorem sb1_bdd_movEnt_cond (hM : D.M = -1) (hT : 0 < T) (hN : 1 ≤ N) (hβ : 0 < D.invβ) {cV CV : ℝ} (hcV : 0 < cV)
    (hV : ∀ x, cV * ‖x‖ ^ 2 - CV ≤ D.V x) (Kf : ℝ → ℝ) (hKi : IntegrableOn Kf (Set.Icc 0 T))
    (hLip : ∀ t ∈ Set.Icc (0 : ℝ) T, Whole.HasLipBoundW (Whole.mfeTransportW D (ρ t)) (Kf t))
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X₀ : Ω → Whole.EucConfig d N} {X : ℝ≥0 → Ω → Whole.EucConfig d N}
    (hX : Whole.IsWholeStrongSolution Pm D T X₀ W X) (hF : Whole.IsWholeFilteredSolution Pm ℱ W' W X)
    (hX₀ : Measurable X₀) {S : Set (Whole.EucConfig d N)} (hS : MeasurableSet S) (hpS : Pm (X₀ ⁻¹' S) ≠ 0)
    (hmom : ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂((cond Pm (X₀ ⁻¹' S)).map X₀) < ⊤)
    (c0 : ℝ) (hc0 : 0 ≤ c0)
    (hbdd : (cond Pm (X₀ ⁻¹' S)).map X₀ ≤
      ENNReal.ofReal c0 • sb1Dm (fun Z => sb1Gw D (Whole.rieszKernel d D.s) N Z))
    (η : ℕ → ℝ) (A3 A4 : ℝ) (hη : Tendsto η atTop (𝓝 0)) (hη0 : ∀ M, 0 ≤ η M) (hA3 : 0 < A3) (hA4 : 0 ≤ A4)
    (hB : ∀ (M : ℕ), ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ Z : Whole.EucConfig d N,
      |sb1_lv_B (N := N) D (sb1kM d D.s M) hT.le ρ r Z| ≤ η M * (1 + Kf r) *
        (A3 * (sb1PM (sb1kM d D.s M) N Z + sb1ell d N Z) + A4)) :
    SbMovEnt D N T ρ (cond Pm (X₀ ⁻¹' S)) X₀ X := by
  intro hprem
  have hs0 := H.tr.hs0
  have hd := H.tr.hd
  have hsd := H.tr.hsd
  have hW := p4r_shiftFil_brownian hF.brownian
  have hXm : ∀ t : ℝ≥0, Measurable (X t) := hX.adapted
  -- the event of the initial value
  have hA : (X₀ ⁻¹' S : Set Ω) =ᵐ[Pm] ((X 0) ⁻¹' S : Set Ω) := by
    filter_upwards [hX.init] with ζ hζ
    exact propext (by simp [hζ])
  have hcond : cond Pm (X₀ ⁻¹' S) = cond Pm ((X 0) ⁻¹' S) := by
    unfold ProbabilityTheory.cond
    rw [Measure.restrict_congr_set hA, measure_congr hA]
  have hpS' : Pm ((X 0) ⁻¹' S) ≠ 0 := by rw [← measure_congr hA]; exact hpS
  haveI : IsProbabilityMeasure (cond Pm ((X 0) ⁻¹' S)) := cond_isProbabilityMeasure hpS'
  rw [hcond] at hmom hbdd hprem ⊢
  set Pc := cond Pm ((X 0) ⁻¹' S) with hPc
  have h0eq : Pc.map X₀ = Pc.map (X 0) :=
    Measure.map_congr (cond_absolutelyContinuous.ae_le (by filter_upwards [hX.init] with ζ hζ using hζ.symm))
  haveI : IsProbabilityMeasure (Pc.map (X 0)) :=
    (Measure.isProbabilityMeasure_map_iff (hXm 0).aemeasurable).2 inferInstance
  rw [h0eq] at hmom hbdd hprem
  have hR := H.rho hd ⟨le_rfl, hT.le⟩
  have hβ0 : 0 < D.invβ⁻¹ := inv_pos.2 hβ
  obtain ⟨hν0, hEn0⟩ := sb1_Q_conv hd hs0 hsd hN hβ0 (sb1KerU_riesz d D.s hs0) hR hprem
  -- the regularised solutions and their conditioned laws
  obtain ⟨Ys, hYs, hae, -⟩ := sb1_Y_data D hM hs0 H.tr.V hT hX hF
  have hY0 : ∀ u : ℝ, Measurable[p4r_shiftFil ℱ u] (X 0) := fun u =>
    (hF.adapted 0).mono (ℱ.mono (le_max_right u 0)) le_rfl
  have hYsm : ∀ M (u : ℝ), Measurable (Ys M u) := fun M u =>
    ((hYs M).adapted u).mono ((p4r_shiftFil ℱ).le _) le_rfl
  have hlaw : ∀ (M : ℕ) (t : ℝ), 0 ≤ t → Pc.map (Ys M t) =
      sb1Flow D (sb1kM d D.s M) N (Pc.map (X 0)) (Pm.map (bfPath hW)) t := fun M t ht =>
    sb1_cond_flow_law hW (sb1_driftM_isLip D (sb1kM_isKernel D.s hs0 M) H.tr.V N) (hY0 0) (hYs M) hS ht
  have hnc : ∀ᵐ ζ ∂Pc, ∀ t : ℝ≥0, (t : ℝ) ≤ T → X t ζ ∉ eucCollisionSet d N :=
    cond_absolutelyContinuous.ae_le hX.no_collision
  have hBmeas := sb1_hBmeas H hT (N := N)
  have hTM : ∀ M : ℕ, AEStronglyMeasurable (fun s => ∫ y, (-(D.invβ⁻¹ * N) *
        (sb1_lv_Ck D (sb1kM d D.s M) N ρ s y - sb1_lv_EQ D (sb1kM d D.s M) N ρ s) +
        sb1_lv_B (N := N) D (sb1kM d D.s M) hT.le ρ s y)
        ∂(sb1Flow D (sb1kM d D.s M) N (Pc.map (X 0)) (Pm.map (bfPath hW)) s)) (volume.restrict (Set.Icc 0 T)) :=
    fun M => sb1_ent_M_meas H hT.le hβ hN (sb1kM_isKernel D.s hs0 M) Kf hKi hLip (Pc.map (X 0)) hmom hW
  obtain ⟨hc1, hc2, hmain⟩ := sb1_bdd_entropy_core H hT hN hβ hcV hV Kf hKi hLip hW hXm hYsm
    (cond_absolutelyContinuous.ae_le hae) hnc hlaw hν0 hEn0 hmom c0 hc0 hbdd η A3 A4 hη hη0 hA3 hA4 hBmeas hB hTM
  rw [h0eq]
  refine ⟨fun t ht => ?_, fun r hr => ?_⟩
  · obtain ⟨hfin, hle⟩ := hmain t ht
    have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc 0 T := Set.Icc_subset_Icc le_rfl ht.2
    exact ⟨hfin, fun r hr => hc1 r (hsub hr), hc2.mono_set hsub, hle⟩
  · obtain ⟨hK0, hL0⟩ := sb1_lip_of_hasLip (hLip r hr)
    exact sb1_CN_Qint H hN hβ hr hK0 hL0

end Main

end HRS.MS.MfeConf
