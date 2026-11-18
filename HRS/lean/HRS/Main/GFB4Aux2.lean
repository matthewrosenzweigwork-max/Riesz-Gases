import HRS.Main.GFB4Aux1
import HRS.Uniform.Q45Cov4

/-!
# GFB4, part 2: covariance limit for weakly continuous test paths, and Gaussianity of the limit vector
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.GF

open HRS.Uniform.Q54c

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

theorem gfb4_cov_sum_tendsto {T ta tb : ℝ} (hT : 0 < T) (hta : ta ∈ Set.Icc 0 T) (htb : tb ∈ Set.Icc 0 T)
    {ya yb : ℝ → H} (hya_m : Measurable ya) (hyb_m : Measurable yb) {Ya Yb : ℝ}
    (hYa : ∀ σ, ‖ya σ‖ ≤ Ya) (hYb : ∀ σ, ‖yb σ‖ ≤ Yb)
    (hya_w : ∀ x : H, Continuous fun σ => inner ℝ (ya σ) x)
    (hyb_w : ∀ x : H, Continuous fun σ => inner ℝ (yb σ) x)
    {C : ℝ → H →L[ℝ] H →L[ℝ] ℝ} {c : ℝ → ℝ}
    (hCtc : ∀ σ ∈ Set.Icc 0 T, IsTraceClassCov (C σ))
    (hc0 : ∀ σ, 0 ≤ c σ) (hCb : ∀ σ ∈ Set.Icc 0 T, ∀ u v : H, |C σ u v| ≤ c σ * (‖u‖ * ‖v‖))
    (hc : IntegrableOn c (Set.Icc 0 T)) (hCm : ∀ u v : H, Measurable fun σ => C σ u v) :
    Tendsto (fun N : ℕ => ∑ i ∈ Finset.range (N + 1), ∫ σ in Set.Ioc (gridPt T N i) (gridPt T N (i + 1)) ∩
        Set.Iic (min ta tb), C σ (ya (min (gridPt T N i) ta)) (yb (min (gridPt T N i) tb))) atTop
      (𝓝 (∫ σ in Set.Icc 0 (min ta tb), C σ (ya σ) (yb σ))) := by
  classical
  set tab : ℝ := min ta tb with htab
  have htabT : tab ≤ T := (min_le_left _ _).trans hta.2
  have htab0 : 0 ≤ tab := le_min hta.1 htb.1
  have hYa0 : 0 ≤ Ya := (norm_nonneg _).trans (hYa 0)
  have hYb0 : 0 ≤ Yb := (norm_nonneg _).trans (hYb 0)
  -- the step functions
  set Fn : ℕ → ℝ → ℝ := fun N σ => C σ (ya (min (gridPt T N (cellIdx T N σ)) ta))
    (yb (min (gridPt T N (cellIdx T N σ)) tb)) with hFn
  have hFm : ∀ N, Measurable (Fn N) := by
    intro N
    have hg : Measurable fun σ : ℝ => gridPt T N (cellIdx T N σ) :=
      (measurable_from_top (f := fun n : ℕ => gridPt T N n)).comp (measurable_cellIdx T N)
    have h1 : Measurable fun σ : ℝ => ((ya (min (gridPt T N (cellIdx T N σ)) ta),
        yb (min (gridPt T N (cellIdx T N σ)) tb)), σ) :=
      (((hya_m.comp (hg.min measurable_const)).prodMk
        (hyb_m.comp (hg.min measurable_const))).prodMk measurable_id)
    exact (measurable_form_apply hCm).comp h1
  have hcell : ∀ N : ℕ, ∀ σ ∈ Set.Ioc (0 : ℝ) tab, cellIdx T N σ ≤ N ∧
      σ ∈ Set.Ioc (gridPt T N (cellIdx T N σ)) (gridPt T N (cellIdx T N σ + 1)) :=
    fun N σ hσ => cellIdx_spec hT N ⟨hσ.1, hσ.2.trans htabT⟩
  -- bound
  have hbd : ∀ N : ℕ, ∀ σ ∈ Set.Ioc (0 : ℝ) tab, ‖Fn N σ‖ ≤ c σ * (Ya * Yb) := by
    intro N σ hσ
    obtain ⟨hk, hmem⟩ := hcell N σ hσ
    have hσT : σ ∈ Set.Icc 0 T := ⟨hσ.1.le, hσ.2.trans htabT⟩
    have hga : min (gridPt T N (cellIdx T N σ)) ta ∈ Set.Icc 0 T :=
      ⟨le_min (gridPt_nonneg hT.le N _) hta.1, (min_le_right _ _).trans hta.2⟩
    have hgb : min (gridPt T N (cellIdx T N σ)) tb ∈ Set.Icc 0 T :=
      ⟨le_min (gridPt_nonneg hT.le N _) htb.1, (min_le_right _ _).trans htb.2⟩
    rw [Real.norm_eq_abs]
    refine (hCb σ hσT _ _).trans ?_
    have h1 := hYa (min (gridPt T N (cellIdx T N σ)) ta)
    have h2 := hYb (min (gridPt T N (cellIdx T N σ)) tb)
    exact mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (norm_nonneg _) hYa0) (hc0 σ)
  -- the integrals
  have hIc : IntegrableOn c (Set.Ioc 0 tab) :=
    (hc.mono_set (fun σ hσ => ⟨hσ.1.le, hσ.2.trans htabT⟩))
  have hFint : ∀ N, IntegrableOn (Fn N) (Set.Ioc 0 tab) := by
    intro N
    refine Integrable.mono' (hIc.mul_const (Ya * Yb)) (hFm N).aestronglyMeasurable ?_
    exact (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun σ hσ => hbd N σ hσ)
  -- the sum equals the integral of the step function
  have hsum : ∀ N : ℕ, (∑ i ∈ Finset.range (N + 1), ∫ σ in Set.Ioc (gridPt T N i) (gridPt T N (i + 1)) ∩
        Set.Iic tab, C σ (ya (min (gridPt T N i) ta)) (yb (min (gridPt T N i) tb))) =
      ∫ σ in Set.Ioc 0 tab, Fn N σ := by
    intro N
    have hD : ∀ i ∈ Finset.range (N + 1), ∫ σ in Set.Ioc (gridPt T N i) (gridPt T N (i + 1)) ∩
        Set.Iic tab, C σ (ya (min (gridPt T N i) ta)) (yb (min (gridPt T N i) tb)) =
        ∫ σ in Set.Ioc (gridPt T N i) (gridPt T N (i + 1)) ∩ Set.Iic tab, Fn N σ := by
      intro i hi
      refine setIntegral_congr_fun (measurableSet_Ioc.inter measurableSet_Iic) fun σ hσ => ?_
      have hidx := cellIdx_eq hT N hσ.1
      simp only [hFn, hidx]
    rw [Finset.sum_congr rfl hD]
    have hU : (⋃ i ∈ Finset.range (N + 1), Set.Ioc (gridPt T N i) (gridPt T N (i + 1)) ∩
        Set.Iic tab) = Set.Ioc 0 tab := by
      ext σ
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iic, exists_prop]
      constructor
      · rintro ⟨i, hi, ⟨h1, h2⟩, h3⟩
        exact ⟨(gridPt_nonneg hT.le N i).trans_lt h1, h3⟩
      · rintro ⟨h1, h2⟩
        obtain ⟨hk, hmem⟩ := hcell N σ ⟨h1, h2⟩
        exact ⟨cellIdx T N σ, Finset.mem_range.2 (Nat.lt_succ_of_le hk), hmem, h2⟩
    rw [← integral_biUnion_finset (Finset.range (N + 1))
      (fun i _ => measurableSet_Ioc.inter measurableSet_Iic) ?_ ?_, hU]
    · intro i hi j hj hij
      exact ((grid_cells_disjoint hT.le N hij).mono Set.inter_subset_left Set.inter_subset_left)
    · intro i hi
      exact (hFint N).mono_set (by
        intro σ hσ
        exact ⟨(gridPt_nonneg hT.le N i).trans_lt hσ.1.1, hσ.2⟩)
  -- pointwise convergence
  have hlim : ∀ σ ∈ Set.Ioc (0 : ℝ) tab, Tendsto (fun N => Fn N σ) atTop
      (𝓝 (C σ (ya σ) (yb σ))) := by
    intro σ hσ
    set v : ℕ → ℝ := fun N => gridPt T N (cellIdx T N σ) with hv
    have hvσ : ∀ N, v N < σ ∧ σ - T / ((N : ℝ) + 1) ≤ v N := by
      intro N
      obtain ⟨hk, hmem⟩ := hcell N σ hσ
      refine ⟨hmem.1, ?_⟩
      have := hmem.2
      have h2 := gridPt_succ_sub T N (cellIdx T N σ)
      simp only [hv]
      linarith
    have hvt : Tendsto v atTop (𝓝 σ) := by
      have h0 : Tendsto (fun N : ℕ => T * (1 / ((N : ℝ) + 1))) atTop (𝓝 (T * 0)) :=
        (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul T
      rw [mul_zero] at h0
      have h1 : Tendsto (fun N : ℕ => σ - T / ((N : ℝ) + 1)) atTop (𝓝 σ) := by
        have := (tendsto_const_nhds (x := σ)).sub h0
        rw [sub_zero] at this
        refine this.congr fun N => ?_
        simp [div_eq_mul_inv]
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le h1 tendsto_const_nhds
        (fun N => (hvσ N).2) (fun N => (hvσ N).1.le)
    have hFeq : ∀ N, Fn N σ = C σ (ya (v N)) (yb (v N)) := by
      intro N
      have h1 : min (v N) ta = v N := min_eq_left ((hvσ N).1.le.trans (hσ.2.trans (min_le_left _ _)))
      have h2 : min (v N) tb = v N := min_eq_left ((hvσ N).1.le.trans (hσ.2.trans (min_le_right _ _)))
      simp only [hFn, hv]
      rw [h1, h2]
    simp_rw [hFeq]
    have hσT : σ ∈ Set.Icc 0 T := ⟨hσ.1.le, hσ.2.trans htabT⟩
    exact HRS.Uniform.Q45.psd_tendsto_weak (hCtc σ hσT) (fun N => ya (v N)) (fun N => yb (v N))
      (ya σ) (yb σ) (B := max Ya Yb) (le_max_of_le_left hYa0)
      (Filter.Eventually.of_forall fun N => (hYa _).trans (le_max_left _ _))
      (Filter.Eventually.of_forall fun N => (hYb _).trans (le_max_right _ _))
      (fun x => ((hya_w x).tendsto σ).comp hvt) (fun x => ((hyb_w x).tendsto σ).comp hvt)
  simp_rw [hsum]
  rw [integral_Icc_eq_integral_Ioc]
  refine tendsto_integral_of_dominated_convergence (fun σ => c σ * (Ya * Yb))
    (fun N => (hFm N).aestronglyMeasurable) (hIc.mul_const _) ?_ ?_
  · intro N
    exact (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun σ hσ => hbd N σ hσ)
  · exact (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun σ hσ => hlim σ hσ)



end HRS.GF
