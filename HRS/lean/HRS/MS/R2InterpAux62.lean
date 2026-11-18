import HRS.MS.R2InterpAux61

/-!
# S10.2 (worker S102), part 62 (packet F10): the conclusion for the cylindrical functional `Φ ∘ P_L`
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators MatrixOrder Matrix

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas HRS.MC.Sec7.PI HRS.MC.Sec7.S7PIF6 HRS.MC.Sec7.S7PIG6

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ} {Pw : ℝ}

theorem s102_memCb4 {q : ℕ} {G : EuclideanSpace ℝ (Fin q) → ℝ} (hG : MemCb 5 G) : MemCb 4 G :=
  ⟨hG.1.of_le (by norm_num), fun j hj => hG.2 j (by omega)⟩

theorem s102_heatEv_contOn (hT : 0 < T) (L : ℕ) (hs : S102Std C m T r c)
    (γ : ℝ → Measure (OscPath d m T)) (hγ : ∀ u ∈ Icc (0 : ℝ) T, IsR2FutureGaussian C m T u (γ u))
    {G : EuclideanSpace ℝ (Fin (s102_q d L)) → ℝ} {k : ℕ} (hGk : MemCb k G) {j : ℕ} (hj : j ≤ k)
    (w : Fin j → EuclideanSpace ℝ (Fin (s102_q d L))) (Y : ℝ → OscPath d m T) (hY : ContinuousOn Y (Icc 0 T)) :
    ContinuousOn (fun t => iteratedFDeriv ℝ j
      (gaussHeat (s102_obsCov C m (s102_tauk hT L) (s102_alk L)) G t)
      (s102_obs (s102_tauk hT L) (s102_alk L) (Y t)) w) (Icc 0 T) := by
  have hcont := s102_heatDeriv_cont hT L (s102_gramInt hs hT L) γ hγ hGk hj
  have h1 : ContinuousOn (fun t : ℝ => (t, s102_obs (s102_tauk hT L) (s102_alk L) (Y t))) (Icc 0 T) :=
    continuousOn_id.prodMk ((s102_obs (s102_tauk hT L) (s102_alk L)).continuous.comp_continuousOn hY)
  have h2 := hcont.comp h1 (fun t ht => ⟨ht, mem_univ _⟩)
  exact (HRS.MC.Sec7.S7PIL.S7PIL_ev w).continuous.comp_continuousOn h2

theorem s102_cylA_integrableOn (hs : S102Std C m T r c) (hP : (d : ℝ) < 2 * Pw) (hT : 0 < T) (L : ℕ) (sQ : ℝ)
    (μ : Measure (Euc d)) (γ : ℝ → Measure (OscPath d m T))
    (hγ : ∀ u ∈ Icc (0 : ℝ) T, IsR2FutureGaussian C m T u (γ u))
    {N : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → EucConfig d N) (ζ : Ω)
    {Mb : ℝ → ℝ} (hb : S102Drift C m T r Pw (fun u => r2QuadField sQ μ P X u ζ) Mb)
    {G : EuclideanSpace ℝ (Fin (s102_q d L)) → ℝ} (hG : MemCb 2 G) (hYc : ContinuousOn (s102_Y C m T P X ζ) (Icc 0 T)) :
    IntegrableOn (s102_cylA C m T sQ μ P X (s102_tauk hT L) (s102_alk L) G ζ) (Ioc 0 T) := by
  unfold s102_cylA
  refine IntegrableOn.mono_set ?_ (Ioc_subset_Icc_self (a := (0 : ℝ)) (b := T))
  refine integrable_finsetSum _ fun i _ => ?_
  have hg : ContinuousOn (fun t => fderiv ℝ (gaussHeat (s102_obsCov C m (s102_tauk hT L) (s102_alk L)) G t)
      (s102_obs (s102_tauk hT L) (s102_alk L) (s102_Y C m T P X ζ t)) (EuclideanSpace.single i 1)) (Icc 0 T) := by
    have := s102_heatEv_contOn hT L hs γ hγ hG (j := 1) (by norm_num) (fun _ => EuclideanSpace.single i (1 : ℝ))
      _ hYc
    refine this.congr fun t ht => ?_
    simp [iteratedFDeriv_one_apply]
  exact IntegrableOn.continuousOn_mul hg (s102_hh_integrableOn hP hs.hD hb _ _ i) isCompact_Icc

theorem s102_cylJ_integrableOn (hs : S102Std C m T r c) (hT : 0 < T) (L : ℕ) (μ : Measure (Euc d))
    (γ : ℝ → Measure (OscPath d m T)) (hγ : ∀ u ∈ Icc (0 : ℝ) T, IsR2FutureGaussian C m T u (γ u))
    {N : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (X : ℝ≥0 → Ω → EucConfig d N) (ζ : Ω)
    {G : EuclideanSpace ℝ (Fin (s102_q d L)) → ℝ} (hG : MemCb 2 G) (hYc : ContinuousOn (s102_Y C m T P X ζ) (Icc 0 T))
    (hzi : ∀ i j, IntegrableOn (s102_hh2 C m (s102_tauk hT L) (s102_alk L) (s102_etaf μ X ζ) i j) (Icc 0 T)) :
    IntegrableOn (s102_cylJ C m T μ P X (s102_tauk hT L) (s102_alk L) G ζ) (Ioc 0 T) := by
  unfold s102_cylJ
  refine IntegrableOn.mono_set ?_ (Ioc_subset_Icc_self (a := (0 : ℝ)) (b := T))
  refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_
  have hg := s102_heatEv_contOn hT L hs γ hγ hG (j := 2) le_rfl ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single j 1]
    _ hYc
  have := IntegrableOn.continuousOn_mul hg ((hzi i j).const_mul (2 * C.ν)) isCompact_Icc
  exact this.congr_fun (fun u _ => by ring) measurableSet_Icc

set_option maxSynthPendingDepth 3 in
/-- **F10**: the conclusion of `r2_path_interpolation` for `Φ ∘ P_L`. -/
theorem s102_cyl_concl (hs : S102Std C m T r c) (hP : (d : ℝ) < 2 * Pw) (hlin : S102Lin C m T) (hT : 0 < T)
    (L : ℕ) (sQ : ℝ) (μ : Measure (Euc d))
    (hμ : ∀ u ∈ Icc (0 : ℝ) T, ∀ g : Euc d → ℝ, HRS.Whole.pair μ g = ∫ x, g x * C.ρ u x)
    (γ : ℝ → Measure (OscPath d m T)) (hγp : ∀ u, IsProbabilityMeasure (γ u))
    (hγ : ∀ u ∈ Icc (0 : ℝ) T, IsR2FutureGaussian C m T u (γ u))
    (hLP : S102LipProj γ (fun L => s102_Pj T hT L))
    {N : ℕ} (hN : 0 < N) {Ω : Type} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → EucConfig d N) {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hW : IsBrownianFiltration P ℱ W') (hrep : S102ItoRep C m T sQ μ hT L P X ℱ W')
    {Φ : OscPath d m T → ℝ} (hΦ : MemCb 5 Φ)
    (Mb : Ω → ℝ → ℝ)
    (hdr : ∀ᵐ ζ ∂P, S102Drift C m T r Pw (fun u => r2QuadField sQ μ P X u ζ) (Mb ζ))
    (hMint : Integrable (fun ζ => ∫ u in Ioc 0 T, Mb ζ u) P)
    (hY : ∀ᵐ ζ ∂P, ContinuousOn (s102_Y C m T P X ζ) (Icc 0 T))
    (Vf : Ω → ℝ) (hVf : Integrable Vf P)
    (hJc : ∀ᵐ ζ ∂P, ∃ (Jc : ℝ → TensorDual (OscPath d m T) 2), Jc 0 = 0 ∧
      (∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ T → IsR2JValue C m T (s102_etaf μ X ζ) (Ioc a b) (Jc b - Jc a)) ∧
      BoundedVariationOn Jc (Icc 0 T) ∧ (eVariationOn Jc (Icc 0 T)).toReal ≤ Vf ζ)
    (hzi : ∀ᵐ ζ ∂P, ∀ i j, IntegrableOn
      (s102_hh2 C m (s102_tauk hT L) (s102_alk L) (s102_etaf μ X ζ) i j) (Icc 0 T))
    (hAm : AEStronglyMeasurable (fun ζ => ∫ u in Ioc 0 T, s102_cylA C m T sQ μ P X (s102_tauk hT L) (s102_alk L)
      (fun x => Φ (s102_Lam T L x)) ζ u) P)
    (hJm : AEStronglyMeasurable (fun ζ => ∫ u in Ioc 0 T, s102_cylJ C m T μ P X (s102_tauk hT L) (s102_alk L)
      (fun x => Φ (s102_Lam T L x)) ζ u) P)
    (hE1 : ∀ᵐ ζ ∂P, s102_obs (s102_tauk hT L) (s102_alk L) (s102_Y C m T P X ζ T) =
      s102_obs (s102_tauk hT L) (s102_alk L) (zetaPathW m T 0 P X ζ))
    (hzW : AEMeasurable (fun ζ => zetaPathW m T 0 P X ζ) P)
    (hy : AEMeasurable (fun ζ => s102_y0 C m T P X ζ) P) :
    S102Concl C m T sQ μ γ P X Φ (s102_Pj T hT L) := by

  classical
  set τ := s102_tauk hT L with hτ
  set α := s102_alk L with hα
  set G : EuclideanSpace ℝ (Fin (s102_q d L)) → ℝ := fun x => Φ (s102_Lam T L x) with hGdef
  have hG5 : MemCb 5 G := (HRS.MC.Sec7.S7PIS2.s7_PIS_memCb_comp_proof (s102_Lam T L) hΦ).1
  have hG4 : MemCb 4 G := s102_memCb4 hG5
  have hG2 : MemCb 2 G := ⟨hG5.1.of_le (by norm_num), fun j hj => hG5.2 j (by omega)⟩
  have hΦG : (fun w => Φ (s102_Pj T hT L w)) = fun w => G (s102_obs τ α w) := by
    funext w
    simp only [hGdef]
    rw [s102_Pj_eq_Lam hT L w]
  have hGi := s102_gramInt hs hT L
  have hcov : ∀ k k', ContinuousOn (fun u => s102_obsCov C m τ α u k k') (Icc 0 T) :=
    fun k k' => s102_obsCov_cont hT L hGi k k'
  obtain ⟨hP1, hconv, hTconv⟩ := s102_projection_strong (d := d) m T hT
  obtain ⟨bd, Φc, hbd, hΦ', hX0, hbform, hΦform, hid⟩ := hrep
  obtain ⟨Mart, hMi, hM0, hM⟩ := s102_ito_cyl hs hT L sQ μ hμ γ hγ hN P X hW bd Φc hbd hΦ' hX0 hbform hΦform
    hid hG4
  set A : Ω → ℝ := fun ζ => ∫ u in Ioc 0 T, s102_cylA C m T sQ μ P X τ α G ζ u with hAdef
  set J : Ω → ℝ := fun ζ => ∫ u in Ioc 0 T, s102_cylJ C m T μ P X τ α G ζ u with hJdef
  have hC0 : 0 ≤ cbNorm 5 Φ := HRS.MC.Sec7.S7PIL.S7PIL_cbNorm_nonneg hΦ 0
  have hAae : ∀ᵐ ζ ∂P, IsR2RS T (fun t a b => fderiv ℝ (r2HeatFn γ (fun w => Φ (s102_Pj T hT L w)) t)
      (s102_Y C m T P X ζ t) (r2DriftInc C m T (fun u => r2QuadField sQ μ P X u ζ) a b)) (A ζ) ∧
      |A ζ| ≤ s102_KV d r Pw c * cbNorm 5 Φ * ∫ u in Ioc 0 T, Mb ζ u := by
    filter_upwards [hdr, hY] with ζ hb hYc
    have h8 := s102_F8 hP hs.hD hlin hb hT γ hγ τ α hcov hG2 _ hYc
    have h8' : IsR2RS T (fun t a b => fderiv ℝ (r2HeatFn γ (fun w => Φ (s102_Pj T hT L w)) t)
        (s102_Y C m T P X ζ t) (r2DriftInc C m T (fun u => r2QuadField sQ μ P X u ζ) a b)) (A ζ) := by
      rw [hΦG]; exact h8
    obtain ⟨-, -, -, IL, hIL, hILb, -⟩ := s102_RS_drift hP hs.hD hlin hb hT γ hγp (fun L => s102_Pj T hT L)
      hP1 hconv hLP hΦ _ hYc
    have heq : A ζ = IL L := HRS.MC.Sec7.S7PIS2.S7PIS2_RS_unique T hT _ _ _ ((s102_isR2RS_iff _ _ _).1 h8')
      ((s102_isR2RS_iff _ _ _).1 (hIL L))
    exact ⟨h8', heq ▸ hILb L⟩
  have hJae : ∀ᵐ ζ ∂P, IsR2RS T (fun t a b => r2JPair C m T (s102_etaf μ X ζ) (Ioc a b)
      (iteratedFDeriv ℝ 2 (r2HeatFn γ (fun w => Φ (s102_Pj T hT L w)) t) (s102_Y C m T P X ζ t))) (J ζ) ∧
      |J ζ| ≤ cbNorm 5 Φ * Vf ζ := by
    filter_upwards [hJc, hY, hzi] with ζ hz hYc hzi'
    obtain ⟨Jc, hJc0, hJv, hBV, hVle⟩ := hz
    have h9 := s102_F9 hT γ hγ τ α hcov hG2 _ hYc (s102_etaf μ X ζ) Jc hJv hzi'
    have h9' : IsR2RS T (fun t a b => r2JPair C m T (s102_etaf μ X ζ) (Ioc a b)
        (iteratedFDeriv ℝ 2 (r2HeatFn γ (fun w => Φ (s102_Pj T hT L w)) t) (s102_Y C m T P X ζ t))) (J ζ) := by
      rw [hΦG]; exact h9
    obtain ⟨-, -, -, IL, hIL, hILb, -⟩ := s102_RS_J_bv C hT γ hγp (fun L => s102_Pj T hT L) hP1 hconv hTconv hLP hΦ
      _ hYc (s102_etaf μ X ζ) Jc hJc0 hJv hBV
    have heq : J ζ = IL L := HRS.MC.Sec7.S7PIS2.S7PIS2_RS_unique T hT _ _ _ ((s102_isR2RS_iff _ _ _).1 h9')
      ((s102_isR2RS_iff _ _ _).1 (hIL L))
    refine ⟨h9', ?_⟩
    rw [heq]
    exact (hILb L).trans (mul_le_mul_of_nonneg_left hVle hC0)
  have hAint : Integrable A P := by
    refine Integrable.mono' (hMint.const_mul (s102_KV d r Pw c * cbNorm 5 Φ)) hAm ?_
    filter_upwards [hAae] with ζ h
    rw [Real.norm_eq_abs]; exact h.2
  have hJint : Integrable J P := by
    refine Integrable.mono' (hVf.const_mul (cbNorm 5 Φ)) hJm ?_
    filter_upwards [hJae] with ζ h
    rw [Real.norm_eq_abs]; exact h.2
  -- boundedness of `Φ`
  obtain ⟨K0, hK0⟩ : ∃ K : ℝ, ∀ x, |Φ x| ≤ K := by
    obtain ⟨K, hK⟩ := hΦ.2 0 (Nat.zero_le _)
    refine ⟨K, fun x => ?_⟩
    have := hK ⟨x, rfl⟩
    simpa [norm_iteratedFDeriv_zero] using this
  have hΦc : Continuous Φ := hΦ.1.continuous
  have hPjc : Continuous (s102_Pj (d := d) (m := m) T hT L) := (s102_Pj (d := d) (m := m) T hT L).continuous
  have hΦint : Integrable (fun ζ => Φ (s102_Pj T hT L (zetaPathW m T 0 P X ζ))) P :=
    Integrable.of_bound (C := K0) (((hΦc.comp hPjc).measurable.comp_aemeasurable hzW).aestronglyMeasurable)
      (Eventually.of_forall fun ζ => by simpa using hK0 _)
  have hcH : Continuous (r2HeatFn γ (fun w => Φ (s102_Pj T hT L w)) 0) := by
    haveI := hγp 0
    exact S7PIG6_heat_cont (γ 0) (hΦc.comp hPjc) K0 (fun x => hK0 _)
  have hH0int : Integrable (fun ζ => r2HeatFn γ (fun w => Φ (s102_Pj T hT L w)) 0 (s102_y0 C m T P X ζ)) P := by
    haveI := hγp 0
    refine Integrable.of_bound (C := K0) ((hcH.measurable.comp_aemeasurable hy).aestronglyMeasurable)
      (Eventually.of_forall fun ζ => ?_)
    have := norm_integral_le_of_norm_le_const (μ := γ 0)
      (f := fun z => Φ (s102_Pj T hT L (s102_y0 C m T P X ζ + z))) (C := K0)
      (Eventually.of_forall fun z => by simpa using hK0 _)
    simpa [r2HeatFn] using this
  have hid2 : ∀ᵐ ζ ∂P, Φ (s102_Pj T hT L (zetaPathW m T 0 P X ζ)) -
      r2HeatFn γ (fun w => Φ (s102_Pj T hT L w)) 0 (s102_y0 C m T P X ζ) =
      (-(Real.sqrt N)⁻¹ * A ζ + (1 / (2 * Real.sqrt N)) * J ζ) + Mart ζ := by
    filter_upwards [hM, hE1, hY, hdr, hzi] with ζ hMζ hE hYc hb hzi'
    obtain ⟨hint, hident⟩ := hMζ
    have hIA := s102_cylA_integrableOn hs hP hT L sQ μ γ hγ P X ζ hb hG2 hYc
    have hIJ := s102_cylJ_integrableOn hs hT L μ γ hγ P X ζ hG2 hYc hzi'
    have hsplit : (∫ u in Ioc 0 T, (-(Real.sqrt N)⁻¹ * s102_cylA C m T sQ μ P X τ α G ζ u +
        (1 / (2 * Real.sqrt N)) * s102_cylJ C m T μ P X τ α G ζ u)) =
        -(Real.sqrt N)⁻¹ * A ζ + (1 / (2 * Real.sqrt N)) * J ζ := by
      rw [integral_add (hIA.const_mul _) (hIJ.const_mul _), integral_const_mul, integral_const_mul]
    have hh0 : r2HeatFn γ (fun w => Φ (s102_Pj T hT L w)) 0 (s102_y0 C m T P X ζ) =
        gaussHeat (s102_obsCov C m τ α) G 0 (s102_obs τ α (s102_y0 C m T P X ζ)) := by
      rw [hΦG]
      exact s102_heat_obs C γ hγ τ α G hG2 0 ⟨le_rfl, hT.le⟩ _
    rw [hh0, ← hsplit]
    have : Φ (s102_Pj T hT L (zetaPathW m T 0 P X ζ)) =
        G (s102_obs τ α (s102_Y C m T P X ζ T)) := by
      rw [hE]; exact congrFun hΦG _
    rw [this]
    exact hident
  refine ⟨A, J, hAint, hJint, ?_, ?_, ?_⟩
  · filter_upwards [hAae] with ζ h; exact h.1
  · filter_upwards [hJae] with ζ h; exact h.1
  · have h := integral_congr_ae hid2
    have h1 : Integrable (fun ζ => -(Real.sqrt N)⁻¹ * A ζ + (1 / (2 * Real.sqrt N)) * J ζ) P :=
      (hAint.const_mul _).add (hJint.const_mul _)
    have e1 : ∫ ζ, ((-(Real.sqrt N)⁻¹ * A ζ + (1 / (2 * Real.sqrt N)) * J ζ) + Mart ζ) ∂P =
        (∫ ζ, (-(Real.sqrt N)⁻¹ * A ζ + (1 / (2 * Real.sqrt N)) * J ζ) ∂P) + ∫ ζ, Mart ζ ∂P :=
      integral_add h1 hMi
    have e2 : ∫ ζ, (-(Real.sqrt N)⁻¹ * A ζ + (1 / (2 * Real.sqrt N)) * J ζ) ∂P =
        (∫ ζ, -(Real.sqrt N)⁻¹ * A ζ ∂P) + ∫ ζ, (1 / (2 * Real.sqrt N)) * J ζ ∂P :=
      integral_add (hAint.const_mul _) (hJint.const_mul _)
    rw [integral_sub hΦint hH0int, e1, e2, integral_const_mul, integral_const_mul, hM0] at h
    linarith

end HRS.MS.R2Interp

end
