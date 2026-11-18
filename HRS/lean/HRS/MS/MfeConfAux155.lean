import HRS.MS.MfeConfAux154

/-!
# S.B.1 (SB5), packet R3c (part 5): `SbMovEnt` from `SbMovEnt` for the conditioned laws
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory InformationTheory
open HRS HRS.Whole HRS.MP.SelfSimP4Mol HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d N : ℕ}

section Main

variable {D : Whole.WholeDyn d} {T C B C3 : ℝ} {ρ : ℝ → Euc d → ℝ} (H : Sb1Tr3 D T C B C3 ρ)

include H

set_option maxHeartbeats 1600000 in
theorem sb1_uncondition (hT : 0 ≤ T) (hN : 1 ≤ N) (hβ : 0 < D.invβ) (Kf : ℝ → ℝ) (hKi : IntegrableOn Kf (Set.Icc 0 T))
    (hLip : ∀ t ∈ Set.Icc (0 : ℝ) T, Whole.HasLipBoundW (Whole.mfeTransportW D (ρ t)) (Kf t)) {a b : ℝ}
    (hco : Sb1Coarse D N T ρ a b) {Ω : Type*} [MeasurableSpace Ω] {Pm : Measure Ω} [IsProbabilityMeasure Pm]
    {X₀ : Ω → Whole.EucConfig d N} {X : ℝ≥0 → Ω → Whole.EucConfig d N} (hXm : ∀ t, Measurable (X t))
    (hX₀ : Measurable X₀) (hx0 : ∀ᵐ ζ ∂Pm, X 0 ζ = X₀ ζ)
    (hnc : ∀ᵐ ζ ∂Pm, ∀ t : ℝ≥0, (t : ℝ) ≤ T → X t ζ ∉ eucCollisionSet d N)
    {E : ℕ → Set (Whole.EucConfig d N)} (hE : ∀ j, MeasurableSet (E j)) (hmono : Monotone E)
    (hpos : ∀ j, Pm (X₀ ⁻¹' E j) ≠ 0) (hcov : ∀ᵐ ζ ∂Pm, ∃ j, X₀ ζ ∈ E j)
    (hcond : ∀ j, SbMovEnt D N T ρ (ProbabilityTheory.cond Pm (X₀ ⁻¹' E j)) X₀ X) :
    SbMovEnt D N T ρ Pm X₀ X := by
  intro hfin0
  have hab := hco
  obtain ⟨ha, hb, -⟩ := hab
  have hd := H.tr.hd
  have hs0 := H.tr.hs0
  have hsd := H.tr.hsd
  have hβ0 : 0 < D.invβ⁻¹ := inv_pos.2 hβ
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hκ : 0 < D.invβ⁻¹ * N := mul_pos hβ0 hn
  set κ : ℝ := D.invβ⁻¹ * N with hκdef
  set M1 : ℝ := C3 * ∫ y : Euc d, sb1w ((d : ℝ) + 2) y with hM1
  set CE : ℝ := sb1CE d D.s C3 M1 with hCE
  have hCE0 : 0 ≤ CE := sb1CE_nonneg (H.rho hd (r := 0) ⟨le_rfl, hT⟩)
  have hLs : ∀ s ∈ Set.Icc (0 : ℝ) T, 0 ≤ Kf s ∧
      ∀ x y, ‖Whole.mfeTransportW D (ρ s) x - Whole.mfeTransportW D (ρ s) y‖ ≤ Kf s * ‖x - y‖ :=
    fun s hs => sb1_lip_of_hasLip (hLip s hs)
  set A : ℕ → Set Ω := fun j => X₀ ⁻¹' E j with hAdef
  have hAm : ∀ j, MeasurableSet (A j) := fun j => hX₀ (hE j)
  have hAmono : Monotone A := fun i j h => Set.preimage_mono (hmono h)
  set Pj : ℕ → Measure Ω := fun j => ProbabilityTheory.cond Pm (A j) with hPjdef
  haveI hPjp : ∀ j, IsProbabilityMeasure (Pj j) := fun j => cond_isProbabilityMeasure (hpos j)
  haveI hQ0 : IsProbabilityMeasure (sb1Q D N ρ 0) :=
    sb1_modGibbs_prob hd hs0 hsd hN hβ0.le (sb1KerU_riesz d D.s hs0) (H.rho hd (r := 0) ⟨le_rfl, hT⟩)
  haveI hμ : ∀ t : ℝ, IsProbabilityMeasure (Pm.map (X t.toNNReal)) := fun t =>
    (Measure.isProbabilityMeasure_map_iff (hXm _).aemeasurable).2 inferInstance
  haveI hmj : ∀ j (t : ℝ), IsProbabilityMeasure ((Pj j).map (X t.toNNReal)) := fun j t =>
    (Measure.isProbabilityMeasure_map_iff (hXm _).aemeasurable).2 inferInstance
  haveI hμ0 : IsProbabilityMeasure (Pm.map X₀) :=
    (Measure.isProbabilityMeasure_map_iff hX₀.aemeasurable).2 inferInstance
  obtain ⟨hinit_fin, hinit_lim⟩ := sb1_init_cond hX₀ hE hmono hpos hcov (sb1Q D N ρ 0) hfin0
  have hac : ∀ j, Pj j ≪ Pm := fun j => cond_absolutelyContinuous
  have hPjx0 : ∀ j, (Pj j).map X₀ = (Pj j).map (X 0) := fun j =>
    Measure.map_congr ((hac j).ae_le (hx0.mono fun ζ h => h.symm))
  have hPjnc : ∀ j, ∀ᵐ ζ ∂(Pj j), ∀ t : ℝ≥0, (t : ℝ) ≤ T → X t ζ ∉ eucCollisionSet d N := fun j => (hac j).ae_le hnc
  have hS : ∀ j, _ := fun j => hcond j (hinit_fin j)
  have hP := fun j => sb1_pj_gronwall H hT hN hβ Kf hKi hLip hco (P := Pj j) hXm (hPjx0 j) (hPjnc j) (hcond j) (hinit_fin j)
  -- the uniform bound
  set α : ℝ := a + κ * b with hα
  have hα0 : 0 ≤ α := by have := mul_nonneg hκ.le hb; linarith
  have hHq0 : ∀ j, sb1Hq D N ρ (Pj j) X 0 = (klDiv ((Pj j).map X₀) (sb1Q D N ρ 0)).toReal := by
    intro j; simp only [sb1Hq, Real.toNNReal_zero, ← hPjx0 j, relEntropy]
  have hu0lim : Tendsto (fun j => sb1uu D N ρ (Pj j) X CE 0) atTop
      (𝓝 ((klDiv (Pm.map X₀) (sb1Q D N ρ 0)).toReal - sb1logK D N ρ 0 + κ * CE)) := by
    refine ((hinit_lim.sub_const (sb1logK D N ρ 0)).add_const (κ * CE)).congr fun j => ?_
    simp only [sb1uu, hHq0]
    rfl
  obtain ⟨Bd, hBd⟩ := hu0lim.bddAbove_range
  set B1 : ℝ := max (Bd + 1) 1 with hB1
  set U : ℝ := B1 * Real.exp (α * ∫ r in Set.Icc (0 : ℝ) T, Kf r) with hU
  have hB10 : 0 ≤ B1 := (zero_le_one).trans (le_max_right _ _)
  have hU0 : 0 ≤ U := mul_nonneg hB10 (Real.exp_pos _).le
  have hUj : ∀ j, ∀ t ∈ Set.Icc (0 : ℝ) T, sb1uu D N ρ (Pj j) X CE t + 1 ≤ U := by
    intro j t ht
    refine ((hP j t ht).2.2.1).trans ?_
    have h1 : sb1uu D N ρ (Pj j) X CE 0 + 1 ≤ B1 := by have := hBd ⟨j, rfl⟩; simp only at this; exact le_trans (by linarith) (le_max_left _ _)
    have h2 : ∫ r in Set.Icc (0 : ℝ) t, Kf r ≤ ∫ r in Set.Icc (0 : ℝ) T, Kf r :=
      setIntegral_mono_set hKi ((ae_restrict_iff' measurableSet_Icc).2
        (Filter.Eventually.of_forall fun r hr => (hLs r hr).1))
        ((Set.Icc_subset_Icc le_rfl ht.2).eventuallyLE)
    calc _ ≤ B1 * Real.exp (α * ∫ r in Set.Icc (0 : ℝ) t, Kf r) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ ≤ U := mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left h2 hα0)) hB10
  -- per-time limits
  have hC : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (sb1En (Whole.rieszKernel d D.s) (ρ t) : Whole.EucConfig d N → ℝ) (Pm.map (X t.toNNReal)) ∧
      Integrable (sb1CN D N ρ t) (Pm.map (X t.toNNReal)) ∧
      Tendsto (fun j => ∫ Z, sb1CN D N ρ t Z ∂((Pj j).map (X t.toNNReal))) atTop
        (𝓝 (∫ Z, sb1CN D N ρ t Z ∂(Pm.map (X t.toNNReal)))) ∧
      ∀ j, |∫ Z, sb1CN D N ρ t Z ∂((Pj j).map (X t.toNNReal))| ≤ Kf t * (a * (U / κ) + b) := by
    intro t ht
    have hRt := H.rho hd ht
    have hEnm := sb1_En_meas (N := N) (sb1KerU_riesz d D.s hs0) hRt
    have hIb : ∀ j, (∫ Z, sb1En (Whole.rieszKernel d D.s) (ρ t) Z ∂((Pj j).map (X t.toNNReal))) + CE ≤ U / κ := by
      intro j
      have h1 := (hP j t ht).2.1
      have h2 := hUj j t ht
      rw [le_div_iff₀ hκ]
      have h3 : sb1uu D N ρ (Pj j) X CE t ≤ U - 1 := by linarith
      nlinarith
    have hEnμ : Integrable (sb1En (Whole.rieszKernel d D.s) (ρ t) : Whole.EucConfig d N → ℝ) (Pm.map (X t.toNNReal)) :=
      sb1_unc_L1 hAm hAmono hcov hpos (hXm _) hEnm (c := CE) (B := U / κ)
        (fun x => sb1_En_lower hd hs0 hsd hN hRt x) (div_nonneg hU0 hκ.le)
        (fun j => (hP j t ht).1) hIb
    have hCNm := sb1_CN_meas (N := N) H ht (hLs t ht).1 (hLs t ht).2
    have hCNi : Integrable (sb1CN D N ρ t) (Pm.map (X t.toNNReal)) := by
      refine Integrable.mono' (((hEnμ.const_mul a).add (integrable_const b)).const_mul (Kf t))
        hCNm.aestronglyMeasurable ?_
      filter_upwards [sb1_coll_ae hXm hnc ht] with Z hZ
      rw [Real.norm_eq_abs]
      exact hco.2.2 t ht (Kf t) (hLs t ht).1 (hLs t ht).2 Z hZ
    refine ⟨hEnμ, hCNi, ?_, fun j => ?_⟩
    · have h2 := sb1_cond_tendsto (Pm := Pm) hAm hAmono hcov
        ((integrable_map_measure hCNm.aestronglyMeasurable (hXm _).aemeasurable).1 hCNi)
      have h3 := integral_map (μ := Pm) (hXm t.toNNReal).aemeasurable hCNm.aestronglyMeasurable
      rw [h3]
      refine h2.congr fun j => ?_
      exact (sb1_cond_integral (Pm := Pm) (A := A j) (hXm _) hCNm).symm
    · refine (hP j t ht).2.2.2.2.trans (mul_le_mul_of_nonneg_left ?_ (hLs t ht).1)
      have := hIb j
      have : a * (∫ Z, sb1En (Whole.rieszKernel d D.s) (ρ t) Z ∂((Pj j).map (X t.toNNReal))) ≤ a * (U / κ) :=
        mul_le_mul_of_nonneg_left (by linarith) ha.le
      linarith
  -- the sources
  have hSrcEq : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ (ν : Measure (Whole.EucConfig d N)) [IsProbabilityMeasure ν],
      Integrable (sb1CN D N ρ r) ν →
        ∫ Z, sb1Src D N ρ r Z ∂ν = -κ * ((∫ Z, sb1CN D N ρ r Z ∂ν) - sb1EQ D N ρ r) := by
    intro r hr ν _ hi
    unfold sb1Src
    rw [integral_const_mul, integral_sub hi (integrable_const _)]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    rw [hκdef]
  have hEQi : IntegrableOn (sb1EQ D N ρ) (Set.Icc 0 T) := (sb1_logK_main H hT hβ hN Kf hKi hLip).1
  set Bnd : ℝ → ℝ := fun r => κ * (Kf r * (a * (U / κ) + b) + |sb1EQ D N ρ r|) with hBnd
  have hBndi : IntegrableOn Bnd (Set.Icc 0 T) :=
    ((hKi.mul_const (a * (U / κ) + b)).add hEQi.abs).const_mul κ
  set Sj : ℕ → ℝ → ℝ := fun j r => ∫ Z, sb1Src D N ρ r Z ∂((Pj j).map (X r.toNNReal)) with hSj
  set S : ℝ → ℝ := fun r => ∫ Z, sb1Src D N ρ r Z ∂(Pm.map (X r.toNNReal)) with hSdef
  have hSjb : ∀ j, ∀ r ∈ Set.Icc (0 : ℝ) T, |Sj j r| ≤ Bnd r := by
    intro j r hr
    simp only [hSj]
    rw [hSrcEq r hr _ (hP j r hr).2.2.2.1, abs_mul, abs_neg, abs_of_pos hκ]
    refine mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add ((hC r hr).2.2.2 j) le_rfl)) hκ.le
  have hSlim : ∀ r ∈ Set.Icc (0 : ℝ) T, Tendsto (fun j => Sj j r) atTop (𝓝 (S r)) := by
    intro r hr
    simp only [hSdef]
    rw [hSrcEq r hr _ (hC r hr).2.1]
    refine (((hC r hr).2.2.1.sub_const (sb1EQ D N ρ r)).const_mul (-κ)).congr fun j => ?_
    simp only [hSj]
    rw [hSrcEq r hr _ (hP j r hr).2.2.2.1]
  have hDCT : ∀ t ∈ Set.Icc (0 : ℝ) T, IntegrableOn S (Set.Icc 0 t) ∧
      Tendsto (fun j => ∫ r in Set.Icc (0 : ℝ) t, Sj j r) atTop (𝓝 (∫ r in Set.Icc (0 : ℝ) t, S r)) := by
    intro t ht
    have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc 0 T := Set.Icc_subset_Icc le_rfl ht.2
    have hae : ∀ᵐ r ∂(volume.restrict (Set.Icc (0 : ℝ) t)), r ∈ Set.Icc (0 : ℝ) T :=
      (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun r hr => hsub hr)
    have hmeas : ∀ j, AEStronglyMeasurable (Sj j) (volume.restrict (Set.Icc (0 : ℝ) t)) := fun j =>
      ((hS j).1 t ht).2.2.1.aestronglyMeasurable
    have hlim : ∀ᵐ r ∂(volume.restrict (Set.Icc (0 : ℝ) t)), Tendsto (fun j => Sj j r) atTop (𝓝 (S r)) :=
      hae.mono fun r hr => hSlim r hr
    have hSi : IntegrableOn S (Set.Icc 0 t) := by
      refine Integrable.mono' (hBndi.mono_set hsub)
        (aestronglyMeasurable_of_tendsto_ae atTop hmeas hlim) ?_
      filter_upwards [hae, hlim] with r hr hl
      rw [Real.norm_eq_abs]
      exact le_of_tendsto hl.abs (Filter.Eventually.of_forall fun j => hSjb j r hr)
    refine ⟨hSi, tendsto_integral_of_dominated_convergence Bnd hmeas (hBndi.mono_set hsub) ?_ hlim⟩
    exact fun j => hae.mono fun r hr => by rw [Real.norm_eq_abs]; exact hSjb j r hr
  -- the entropy at time t
  refine ⟨fun t ht => ?_, fun r hr => (hS 0).2 r hr⟩
  have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc 0 T := Set.Icc_subset_Icc le_rfl ht.2
  have hSrcI : ∀ r ∈ Set.Icc (0 : ℝ) t, Integrable (sb1Src D N ρ r) (Pm.map (X r.toNNReal)) := fun r hr => by
    unfold sb1Src
    exact ((hC r (hsub hr)).2.1.sub (integrable_const _)).const_mul _
  obtain ⟨hSi, hSlimt⟩ := hDCT t ht
  set R0 : ℝ := (relEntropy (Pm.map X₀) (sb1Q D N ρ 0)).toReal with hR0
  have hRlim : Tendsto (fun j => (relEntropy ((Pj j).map X₀) (sb1Q D N ρ 0)).toReal +
      ∫ r in Set.Icc (0 : ℝ) t, Sj j r) atTop (𝓝 (R0 + ∫ r in Set.Icc (0 : ℝ) t, S r)) :=
    hinit_lim.add hSlimt
  have hRnn : 0 ≤ R0 + ∫ r in Set.Icc (0 : ℝ) t, S r := by
    refine ge_of_tendsto hRlim (Filter.Eventually.of_forall fun j => ?_)
    exact (ENNReal.toReal_nonneg).trans ((hS j).1 t ht).2.2.2
  have hlsc : relEntropy (Pm.map (X t.toNNReal)) (sb1Q D N ρ t) ≤
      liminf (fun j => relEntropy ((Pj j).map (X t.toNNReal)) (sb1Q D N ρ t)) atTop := by
    haveI : IsProbabilityMeasure (sb1Q D N ρ t) :=
      sb1_modGibbs_prob hd hs0 hsd hN hβ0.le (sb1KerU_riesz d D.s hs0) (H.rho hd ht)
    refine p4lm_klDiv_liminf (μn := fun j => (Pj j).map (X t.toNNReal)) (ρn := fun _ => sb1Q D N ρ t) ?_
      (fun ψ _ _ => tendsto_const_nhds)
    intro ψ hψ ⟨Cψ, hCψ⟩
    have hi : Integrable (fun ζ => ψ (X t.toNNReal ζ)) Pm :=
      Integrable.of_bound (hψ.comp (hXm _)).aestronglyMeasurable Cψ
        (Filter.Eventually.of_forall fun ζ => by rw [Real.norm_eq_abs]; exact hCψ _)
    have h2 := sb1_cond_tendsto (Pm := Pm) hAm hAmono hcov hi
    rw [← integral_map (hXm _).aemeasurable hψ.aestronglyMeasurable] at h2
    exact h2.congr fun j => (sb1_cond_integral (Pm := Pm) (A := A j) (hXm _) hψ).symm
  have hfinj : ∀ j, relEntropy ((Pj j).map (X t.toNNReal)) (sb1Q D N ρ t) =
      ENNReal.ofReal (relEntropy ((Pj j).map (X t.toNNReal)) (sb1Q D N ρ t)).toReal := fun j =>
    (ENNReal.ofReal_toReal ((hS j).1 t ht).1).symm
  have hle : relEntropy (Pm.map (X t.toNNReal)) (sb1Q D N ρ t) ≤ ENNReal.ofReal (R0 + ∫ r in Set.Icc (0 : ℝ) t, S r) := by
    refine hlsc.trans ?_
    have hlim2 : Tendsto (fun j => ENNReal.ofReal ((relEntropy ((Pj j).map X₀) (sb1Q D N ρ 0)).toReal +
        ∫ r in Set.Icc (0 : ℝ) t, Sj j r)) atTop (𝓝 (ENNReal.ofReal (R0 + ∫ r in Set.Icc (0 : ℝ) t, S r))) :=
      ENNReal.tendsto_ofReal hRlim
    rw [← hlim2.liminf_eq]
    refine Filter.liminf_le_liminf (Filter.Eventually.of_forall fun j => ?_)
    rw [hfinj j]
    exact ENNReal.ofReal_le_ofReal ((hS j).1 t ht).2.2.2
  have hfin : relEntropy (Pm.map (X t.toNNReal)) (sb1Q D N ρ t) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  exact ⟨hfin, hSrcI, hSi, ENNReal.toReal_le_of_le_ofReal hRnn hle⟩

end Main

end HRS.MS.MfeConf
