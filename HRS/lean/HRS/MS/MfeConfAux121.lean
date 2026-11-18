import HRS.MS.MfeConfAux120

/-!
# S.B.1, packet F9 (part 24): the entropy inequality for an initial law dominated by the canonical Gibbs measure

`sb1_bdd_entropy` assembles `sb1_AL` (abstract limit), the level-`M` inequality `sb1_ent_M`, the lower semicontinuity `sb1_lsc_Q`,
the initial convergence `sb1_init_tendsto` and the convergence of the time integrals of the sources (`sb1_src_tendsto_abs` with
`sb1_Cmean_limit`, `sb1_EQ_int_tendsto`).  Explicit hypotheses not proved here: the vanishing remainder `SM`, measurability of `B^M`
and of the level-`M` source mean in time.
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

theorem sb1_vm_of_lip {r : ℝ} {Kr : ℝ} (hKr : 0 ≤ Kr)
    (hL : ∀ x y, ‖Whole.mfeTransportW D (ρ r) x - Whole.mfeTransportW D (ρ r) y‖ ≤ Kr * ‖x - y‖) :
    Continuous (Whole.mfeTransportW D (ρ r)) := by
  have : LipschitzWith (Real.toNNReal Kr) (Whole.mfeTransportW D (ρ r)) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hKr]; exact hL x y
  exact this.continuous

theorem sb1_Ck_meas (M : ℕ) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) {Kr : ℝ} (hKr : 0 ≤ Kr)
    (hL : ∀ x y, ‖Whole.mfeTransportW D (ρ r) x - Whole.mfeTransportW D (ρ r) y‖ ≤ Kr * ‖x - y‖) :
    Measurable (sb1_lv_Ck D (sb1kM d D.s M) N ρ r) :=
  sb1_pairE_meas (H.rho H.tr.hd hr) (sb1_meas_hk (sb1kM d D.s M) (sb1_vm_of_lip H hKr hL).measurable)

theorem sb1_CN_meas {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T) {Kr : ℝ} (hKr : 0 ≤ Kr)
    (hL : ∀ x y, ‖Whole.mfeTransportW D (ρ r) x - Whole.mfeTransportW D (ρ r) y‖ ≤ Kr * ‖x - y‖) :
    Measurable (sb1CN D N ρ r) := by
  have : sb1CN D N ρ r = fun Z => Whole.pairEnergy (sb1hk (Whole.rieszKernel d D.s) (Whole.mfeTransportW D (ρ r)))
      Z (Whole.withDensityReal (ρ r)) := funext fun Z => by
    unfold sb1CN; rw [sb1_commKernel_eq]
  rw [this]
  exact sb1_pairE_meas (H.rho H.tr.hd hr) (sb1_meas_hk _ (sb1_vm_of_lip H hKr hL).measurable)

theorem sb1_bdd_entropy (hM : D.M = -1) (hT : 0 < T) (hN : 1 ≤ N) (hβ : 0 < D.invβ) {cV CV : ℝ} (hcV : 0 < cV)
    (hV : ∀ x, cV * ‖x‖ ^ 2 - CV ≤ D.V x) (Kf : ℝ → ℝ) (hKi : IntegrableOn Kf (Set.Icc 0 T))
    (hLip : ∀ t ∈ Set.Icc (0 : ℝ) T, Whole.HasLipBoundW (Whole.mfeTransportW D (ρ t)) (Kf t))
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X₀ : Ω → Whole.EucConfig d N} {X : ℝ≥0 → Ω → Whole.EucConfig d N}
    (hX : Whole.IsWholeStrongSolution Pm D T X₀ W X) (hF : Whole.IsWholeFilteredSolution Pm ℱ W' W X)
    (hX₀ : Measurable X₀)
    (hν0 : relEntropy (Pm.map X₀) (Measure.pi fun _ : Fin N => Whole.withDensityReal (ρ 0)) ≠ ⊤)
    (hEn0 : Integrable (sb1En (Whole.rieszKernel d D.s) (ρ 0) : Whole.EucConfig d N → ℝ) (Pm.map X₀))
    (hmom : ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂(Pm.map X₀) < ⊤)
    (c0 : ℝ) (hc0 : 0 ≤ c0)
    (hbdd : Pm.map X₀ ≤ ENNReal.ofReal c0 • sb1Dm (fun Z => sb1Gw D (Whole.rieszKernel d D.s) N Z))
    (η : ℕ → ℝ) (A3 A4 : ℝ) (hη : Tendsto η atTop (𝓝 0)) (hη0 : ∀ M, 0 ≤ η M) (hA3 : 0 < A3) (hA4 : 0 ≤ A4)
    (hBmeas : ∀ (M : ℕ) (r : ℝ), Measurable (sb1_lv_B (N := N) D (sb1kM d D.s M) hT.le ρ r))
    (hB : ∀ (M : ℕ), ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ Z : Whole.EucConfig d N,
      |sb1_lv_B (N := N) D (sb1kM d D.s M) hT.le ρ r Z| ≤ η M * (1 + Kf r) *
        (A3 * (sb1PM (sb1kM d D.s M) N Z + sb1ell d N Z) + A4))
    (hTM : ∀ M : ℕ, AEStronglyMeasurable (fun s => ∫ y, (-(D.invβ⁻¹ * N) *
        (sb1_lv_Ck D (sb1kM d D.s M) N ρ s y - sb1_lv_EQ D (sb1kM d D.s M) N ρ s) +
        sb1_lv_B (N := N) D (sb1kM d D.s M) hT.le ρ s y)
        ∂(sb1Flow D (sb1kM d D.s M) N (Pm.map (X 0))
          (Pm.map (bfPath (p4r_shiftFil_brownian hF.brownian))) s)) (volume.restrict (Set.Icc 0 T))) :
    (∀ r ∈ Set.Icc (0 : ℝ) T, Integrable (sb1Src D N ρ r) (Pm.map (X r.toNNReal))) ∧
    IntegrableOn (fun r => ∫ Z, sb1Src D N ρ r Z ∂(Pm.map (X r.toNNReal))) (Set.Icc 0 T) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      relEntropy (Pm.map (X t.toNNReal)) (sb1Q D N ρ t) ≠ ⊤ ∧
      (relEntropy (Pm.map (X t.toNNReal)) (sb1Q D N ρ t)).toReal ≤
        (relEntropy (Pm.map X₀) (sb1Q D N ρ 0)).toReal +
          ∫ r in Set.Icc (0 : ℝ) t, ∫ Z, sb1Src D N ρ r Z ∂(Pm.map (X r.toNNReal)) := by
  have hs0 := H.tr.hs0
  have hd := H.tr.hd
  have hsd := H.tr.hsd
  have hβ0 : 0 < D.invβ⁻¹ := inv_pos.2 hβ
  have hT0 := hT.le
  set hW' := p4r_shiftFil_brownian hF.brownian with hW'def
  set ν := Pm.map (bfPath hW') with hν
  obtain ⟨Ys, hYs, hae, hlaw⟩ := sb1_Y_data D hM hs0 H.tr.V hT hX hF
  have hXm : ∀ t : ℝ≥0, Measurable (X t) := hX.adapted
  have h0eq : Pm.map (X 0) = Pm.map X₀ := Measure.map_congr hX.init
  haveI : IsProbabilityMeasure (Pm.map X₀) := (Measure.isProbabilityMeasure_map_iff hX₀.aemeasurable).2 inferInstance
  have hY0 : ∀ u : ℝ, Measurable[p4r_shiftFil ℱ u] (X 0) := fun u =>
    (hF.adapted 0).mono (ℱ.mono (le_max_right u 0)) le_rfl
  have hYsm : ∀ M (u : ℝ), Measurable (Ys M u) := fun M u =>
    ((hYs M).adapted u).mono ((p4r_shiftFil ℱ).le _) le_rfl
  have hbdd' : Pm.map (X 0) ≤ ENNReal.ofReal c0 • sb1Dm (fun Z => sb1Gw D (Whole.rieszKernel d D.s) N Z) := by
    rw [h0eq]; exact hbdd
  -- domination of all the laws by the unnormalised regularised Gibbs measures
  have hdom : ∀ i : ℕ × Set.Icc (0 : ℝ) T, Pm.map (Ys i.1 (i.2 : ℝ)) ≤ ENNReal.ofReal c0 •
      sb1Dm (fun Z => Real.exp (-D.invβ⁻¹ * sb1Hs D (sb1kM d D.s i.1) N Z)) := fun i =>
    sb1_Y_dom D hs0 hd H.tr.V hβ hcV hV hT hW' (hY0 0) i.1 (hYs i.1) hc0 hbdd' i.2.2
  obtain ⟨A1, A2, hA1, hA2, henv⟩ := sb1_Ck_env H hN
  obtain ⟨Cc, hCc0, hCc⟩ := sb1_env_mean_le H hN hβ hcV hV hA1 hA2 (fun i : ℕ × Set.Icc (0 : ℝ) T => i.1)
    (fun i => Ys i.1 (i.2 : ℝ)) (fun i => hYsm _ _) c0 hdom
  obtain ⟨Cb, hCb0, hCb⟩ := sb1_env_mean_le H hN hβ hcV hV hA3 hA4 (fun i : ℕ × Set.Icc (0 : ℝ) T => i.1)
    (fun i => Ys i.1 (i.2 : ℝ)) (fun i => hYsm _ _) c0 hdom
  -- the pieces
  set κ : ℝ := D.invβ⁻¹ * (N : ℝ) with hκ
  have hn0 : (0 : ℝ) < N := Nat.cast_pos.2 (by omega)
  have hκ0 : 0 ≤ κ := by positivity
  have hLs : ∀ s ∈ Set.Icc (0 : ℝ) T, 0 ≤ Kf s ∧
      ∀ x y, ‖Whole.mfeTransportW D (ρ s) x - Whole.mfeTransportW D (ρ s) y‖ ≤ Kf s * ‖x - y‖ :=
    fun s hs => sb1_lip_of_hasLip (hLip s hs)
  have hLs1 : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ x y,
      ‖Whole.mfeTransportW D (ρ s) x - Whole.mfeTransportW D (ρ s) y‖ ≤ (Kf s + 1) * ‖x - y‖ :=
    fun s hs x y => ((hLs s hs).2 x y).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  haveI hprob : ∀ (M : ℕ) (s : ℝ), IsProbabilityMeasure (Pm.map (Ys M s)) := fun M s =>
    (Measure.isProbabilityMeasure_map_iff (hYsm M s).aemeasurable).2 inferInstance
  have hflow : ∀ (M : ℕ) (s : ℝ), 0 ≤ s →
      sb1Flow D (sb1kM d D.s M) N (Pm.map (X 0)) ν s = Pm.map (Ys M s) := fun M s hs => (hlaw M s hs).symm
  have hCint : ∀ (M : ℕ) (s : ℝ), s ∈ Set.Icc (0 : ℝ) T →
      Integrable (sb1_lv_Ck D (sb1kM d D.s M) N ρ s) (Pm.map (Ys M s)) ∧
        ∫ y, |sb1_lv_Ck D (sb1kM d D.s M) N ρ s y| ∂(Pm.map (Ys M s)) ≤ Cc * (Kf s + 1) := by
    intro M s hs
    have hmeas := sb1_Ck_meas (N := N) H M hs (hLs s hs).1 (hLs s hs).2
    have := hCc (Kr := Kf s + 1) (by linarith [(hLs s hs).1]) (M, ⟨s, hs⟩)
      (fun Z => |sb1_lv_Ck D (sb1kM d D.s M) N ρ s Z|) hmeas.abs (fun Z => abs_nonneg _)
      (fun Z => henv M hs (by linarith [(hLs s hs).1]) (hLs1 s hs) Z)
    exact ⟨(integrable_norm_iff hmeas.aestronglyMeasurable).1 (by simpa [Real.norm_eq_abs] using this.1), this.2⟩
  have hBint : ∀ (M : ℕ) (s : ℝ), s ∈ Set.Icc (0 : ℝ) T →
      Integrable (sb1_lv_B (N := N) D (sb1kM d D.s M) hT0 ρ s) (Pm.map (Ys M s)) ∧
        ∫ y, |sb1_lv_B (N := N) D (sb1kM d D.s M) hT0 ρ s y| ∂(Pm.map (Ys M s)) ≤ Cb * (η M * (1 + Kf s)) := by
    intro M s hs
    have hmeas := hBmeas M s
    have hK1 : 0 < 1 + Kf s := by linarith [(hLs s hs).1]
    rcases (hη0 M).eq_or_lt with h0 | hpos
    · have hB0 : ∀ Z, sb1_lv_B (N := N) D (sb1kM d D.s M) hT0 ρ s Z = 0 := fun Z => by
        have := hB M s hs Z
        rw [← h0] at this
        simpa using this
      have : sb1_lv_B (N := N) D (sb1kM d D.s M) hT0 ρ s = fun _ => 0 := funext hB0
      rw [this]
      refine ⟨integrable_zero _ _ _, ?_⟩
      simp [← h0]
    · have := hCb (Kr := η M * (1 + Kf s)) (by positivity) (M, ⟨s, hs⟩)
        (fun Z => |sb1_lv_B (N := N) D (sb1kM d D.s M) hT0 ρ s Z|) hmeas.abs (fun Z => abs_nonneg _)
        (fun Z => by have := hB M s hs Z; linarith)
      exact ⟨(integrable_norm_iff hmeas.aestronglyMeasurable).1 (by simpa [Real.norm_eq_abs] using this.1), this.2⟩
  obtain ⟨ηb, hηb⟩ : ∃ ηb : ℝ, ∀ M, η M ≤ ηb := by
    obtain ⟨b, hb⟩ := hη.bddAbove_range
    exact ⟨b, fun M => hb ⟨M, rfl⟩⟩
  have hηb0 : 0 ≤ ηb := (hη0 0).trans (hηb 0)
  -- convergence of the laws and the collision-free limit
  have hconvs : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ξ ∂Pm, (∀ i j, i ≠ j → X s.toNNReal ξ i ≠ X s.toNNReal ξ j) ∧
      ∀ᶠ M in atTop, Ys M s ξ = X s.toNNReal ξ := by
    intro s hs
    have hle : ((s.toNNReal : ℝ≥0) : ℝ) ≤ T := by rw [Real.coe_toNNReal s hs.1]; exact hs.2
    filter_upwards [hX.no_collision, hae] with ξ hnc hev
    refine ⟨fun i j hij heq => hnc s.toNNReal hle ⟨i, j, hij, heq⟩, ?_⟩
    filter_upwards [hev] with M hM
    have := hM s.toNNReal hle
    rwa [Real.coe_toNNReal s hs.1] at this
  have hCmean : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun ξ => sb1CN D N ρ s (X s.toNNReal ξ)) Pm ∧
      Tendsto (fun M => ∫ ξ, sb1_lv_Ck D (sb1kM d D.s M) N ρ s (Ys M s ξ) ∂Pm) atTop
        (𝓝 (∫ ξ, sb1CN D N ρ s (X s.toNNReal ξ) ∂Pm)) := fun s hs =>
    sb1_Cmean_limit H hN hβ hcV hV hs (hLs s hs).1 (hLs s hs).2 (fun M => Ys M s) (X s.toNNReal)
      (fun M => hYsm M s) (hXm _) c0 (fun M => hdom (M, ⟨s, hs⟩)) (hconvs s hs)
  have hCNint : ∀ s ∈ Set.Icc (0 : ℝ) T, Integrable (sb1CN D N ρ s) (Pm.map (X s.toNNReal)) := fun s hs =>
    (integrable_map_measure (sb1_CN_meas (N := N) H hs (hLs s hs).1 (hLs s hs).2).aestronglyMeasurable
      (hXm _).aemeasurable).2 (hCmean s hs).1
  haveI hprobX : ∀ s : ℝ, IsProbabilityMeasure (Pm.map (X s.toNNReal)) := fun s =>
    (Measure.isProbabilityMeasure_map_iff (hXm _).aemeasurable).2 inferInstance
  -- the abstract convergence of the time integrals of the sources
  have hsrc := fun (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) => sb1_src_tendsto_abs (T := T) (κ := κ)
    (aM := fun M s => ∫ y, (-κ * (sb1_lv_Ck D (sb1kM d D.s M) N ρ s y - sb1_lv_EQ D (sb1kM d D.s M) N ρ s) +
      sb1_lv_B (N := N) D (sb1kM d D.s M) hT0 ρ s y) ∂(sb1Flow D (sb1kM d D.s M) N (Pm.map (X 0)) ν s))
    (cM := fun M s => ∫ y, sb1_lv_Ck D (sb1kM d D.s M) N ρ s y ∂(Pm.map (Ys M s)))
    (bM := fun M s => ∫ y, sb1_lv_B (N := N) D (sb1kM d D.s M) hT0 ρ s y ∂(Pm.map (Ys M s)))
    (EQM := fun M s => sb1_lv_EQ D (sb1kM d D.s M) N ρ s)
    (a := fun s => ∫ Z, sb1Src D N ρ s Z ∂(Pm.map (X s.toNNReal)))
    (c := fun s => ∫ Z, sb1CN D N ρ s Z ∂(Pm.map (X s.toNNReal)))
    (EQ := fun s => sb1EQ D N ρ s)
    (fun M s hs => by
      rw [hflow M s hs.1]
      obtain ⟨hCi, -⟩ := hCint M s hs
      obtain ⟨hBi, -⟩ := hBint M s hs
      have h1 : Integrable (fun y => -κ * (sb1_lv_Ck D (sb1kM d D.s M) N ρ s y -
          sb1_lv_EQ D (sb1kM d D.s M) N ρ s)) (Pm.map (Ys M s)) :=
        (hCi.sub (integrable_const _)).const_mul _
      rw [integral_add h1 hBi, integral_const_mul, integral_sub hCi (integrable_const _)]
      simp)
    (fun s hs => by
      have : ∫ Z, sb1Src D N ρ s Z ∂(Pm.map (X s.toNNReal)) = -(D.invβ⁻¹ * N) *
          ((∫ Z, sb1CN D N ρ s Z ∂(Pm.map (X s.toNNReal))) - sb1EQ D N ρ s) := by
        unfold sb1Src
        rw [integral_const_mul, integral_sub (hCNint s hs) (integrable_const _)]
        simp
      exact this)
    (fun s hs => by
      have key := (hCmean s hs).2
      have e1 : ∀ M, ∫ y, sb1_lv_Ck D (sb1kM d D.s M) N ρ s y ∂(Pm.map (Ys M s)) =
          ∫ ξ, sb1_lv_Ck D (sb1kM d D.s M) N ρ s (Ys M s ξ) ∂Pm := fun M =>
        integral_map (hYsm M s).aemeasurable
          (sb1_Ck_meas (N := N) H M hs (hLs s hs).1 (hLs s hs).2).aestronglyMeasurable
      have e2 : ∫ y, sb1CN D N ρ s y ∂(Pm.map (X s.toNNReal)) = ∫ ξ, sb1CN D N ρ s (X s.toNNReal ξ) ∂Pm :=
        integral_map (hXm _).aemeasurable (sb1_CN_meas (N := N) H hs (hLs s hs).1 (hLs s hs).2).aestronglyMeasurable
      simp only [e1, e2]
      exact key)
    (fun s hs => by
      refine squeeze_zero_norm (fun M => ?_) ((hη.mul_const (Cb * (1 + Kf s))).trans_eq (by simp))
      rw [Real.norm_eq_abs]
      refine ((abs_integral_le_integral_abs).trans (hBint M s hs).2).trans (le_of_eq ?_)
      ring)
    (G := fun s => (κ * Cc + ηb * Cb) * (Kf s + 1))
    (((hKi.add (integrableOn_const (by simp))).const_mul (κ * Cc + ηb * Cb)).congr
      (Eventually.of_forall fun s => rfl))
    (fun M s hs => by
      have h1 := (abs_integral_le_integral_abs (μ := Pm.map (Ys M s))
        (f := sb1_lv_Ck D (sb1kM d D.s M) N ρ s)).trans (hCint M s hs).2
      have h2 := (abs_integral_le_integral_abs (μ := Pm.map (Ys M s))
        (f := sb1_lv_B (N := N) D (sb1kM d D.s M) hT0 ρ s)).trans (hBint M s hs).2
      have hK1 : 0 < 1 + Kf s := by linarith [(hLs s hs).1]
      calc |-κ * ∫ y, sb1_lv_Ck D (sb1kM d D.s M) N ρ s y ∂(Pm.map (Ys M s)) +
            ∫ y, sb1_lv_B (N := N) D (sb1kM d D.s M) hT0 ρ s y ∂(Pm.map (Ys M s))|
          ≤ κ * |∫ y, sb1_lv_Ck D (sb1kM d D.s M) N ρ s y ∂(Pm.map (Ys M s))| +
            |∫ y, sb1_lv_B (N := N) D (sb1kM d D.s M) hT0 ρ s y ∂(Pm.map (Ys M s))| := by
            refine (abs_add_le _ _).trans (add_le_add (le_of_eq ?_) le_rfl)
            rw [abs_mul, abs_neg, abs_of_nonneg hκ0]
        _ ≤ κ * (Cc * (Kf s + 1)) + Cb * (ηb * (1 + Kf s)) := by
            refine add_le_add (mul_le_mul_of_nonneg_left h1 hκ0) (h2.trans ?_)
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hηb M) hK1.le) hCb0
        _ = (κ * Cc + ηb * Cb) * (Kf s + 1) := by ring)
    (fun M => by simpa using hTM M)
    (fun M => sb1_EQ_integrableOn H hT0 hβ hN Kf hKi hLip M)
    (sb1_logK_main H hT0 hβ hN Kf hKi hLip).1
    (fun t ht => sb1_EQ_int_tendsto H hT0 hβ hN Kf hKi hLip ht) ht
  -- the entropy inputs
  have hmom' : ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂(Pm.map (X 0)) < ⊤ := by rw [h0eq]; exact hmom
  have hinit := sb1_init_tendsto hd hs0 hsd hN hβ0.le (fun M => sb1kM_ker D.s hs0 M)
    (fun z hz => sb1kM_tend D.s hs0 hz) (H.rho hd ⟨le_rfl, hT0⟩) (ν := Pm.map X₀) hν0 hmom hEn0
  haveI hp0 : IsProbabilityMeasure (Pm.map (X 0)) :=
    (Measure.isProbabilityMeasure_map_iff (hXm 0).aemeasurable).2 inferInstance
  have hent := fun (M : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) =>
    sb1_ent_M H hT0 hβ hN (sb1kM_isKernel D.s hs0 M) Kf hKi hLip (Pm.map (X 0)) hmom'
      (by rw [h0eq]; exact hinit.1 M) hW' ht
  have hlsc : ∀ t ∈ Set.Icc (0 : ℝ) T, relEntropy (Pm.map (X t.toNNReal)) (sb1Q D N ρ t) ≤
      liminf (fun M => relEntropy (sb1Flow D (sb1kM d D.s M) N (Pm.map (X 0)) ν t)
        (Whole.modulatedGibbs (sb1kM d D.s M) N D.invβ⁻¹ (Whole.withDensityReal (ρ t)))) atTop := by
    intro t ht
    haveI : ∀ M, IsProbabilityMeasure (sb1Flow D (sb1kM d D.s M) N (Pm.map (X 0)) ν t) := fun M => by
      rw [hflow M t ht.1]; exact hprob M t
    exact sb1_lsc_Q hd hs0 hsd hN hβ0.le (fun M => sb1kM_ker D.s hs0 M) (sb1KerU_riesz d D.s hs0)
      (fun z hz => sb1kM_tend D.s hs0 hz) (H.rho hd ht) (m := Pm.map (X t.toNNReal))
      (mM := fun M => sb1Flow D (sb1kM d D.s M) N (Pm.map (X 0)) ν t)
      (fun A hA => by
        simp only [hflow _ t ht.1]
        exact sb1_setwise (fun M => hYsm M t) (hXm _) (hconvs t ht |>.mono fun ξ h => h.2) A hA)
  refine ⟨fun r hr => ((hCNint r hr).sub (integrable_const (sb1EQ D N ρ r))).const_mul (-(D.invβ⁻¹ * N)),
    (hsrc 0 ⟨le_rfl, hT0⟩).1, ?_⟩
  intro t ht
  have := sb1_AL (T := T)
    (mM := fun M t => sb1Flow D (sb1kM d D.s M) N (Pm.map (X 0)) ν t)
    (QM := fun M t => Whole.modulatedGibbs (sb1kM d D.s M) N D.invβ⁻¹ (Whole.withDensityReal (ρ t)))
    (m := fun t => Pm.map (X t.toNNReal)) (Q := fun t => sb1Q D N ρ t) (ν₀ := Pm.map (X 0))
    (aM := fun M s => ∫ y, (-κ * (sb1_lv_Ck D (sb1kM d D.s M) N ρ s y - sb1_lv_EQ D (sb1kM d D.s M) N ρ s) +
      sb1_lv_B (N := N) D (sb1kM d D.s M) hT0 ρ s y) ∂(sb1Flow D (sb1kM d D.s M) N (Pm.map (X 0)) ν s))
    (a := fun s => ∫ Z, sb1Src D N ρ s Z ∂(Pm.map (X s.toNNReal)))
    hent hlsc (by rw [h0eq]; exact hinit.2.2) (fun t ht => (hsrc t ht).2) ht
  simpa only [h0eq] using this

end Main

end HRS.MS.MfeConf
