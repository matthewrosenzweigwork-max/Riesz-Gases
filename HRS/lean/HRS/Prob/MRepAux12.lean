import HRS.Prob.MRepAux11

/-!
# MREP, part 12: the base-level data (progressive covariation, regularised martingale)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MRep

section Prelim

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- Progressive measurability is monotone in the filtration. -/
lemma IsProgressive.mono_filtration {ℱ ℱ' : Filtration ℝ mΩ} (h : ∀ t, ℱ t ≤ ℱ' t) {β : Type*}
    [MeasurableSpace β] {f : ℝ → Ω → β} (hf : IsProgressive ℱ f) : IsProgressive ℱ' f := by
  intro i
  refine (hf i).mono ?_ le_rfl
  exact sup_le_sup le_rfl (MeasurableSpace.comap_mono (h i))

lemma tsum_diag_le_traceNormForm {ι : Type*} (e : HilbertBasis ι ℝ H) {C : H →L[ℝ] H →L[ℝ] ℝ}
    (hC : IsTraceClassCov C) : ∑' i, C (e i) (e i) ≤ traceNormForm C := by
  classical
  obtain ⟨T, hT, -⟩ := hC.hasSum_basis e
  refine hT.summable.tsum_le_of_sum_le fun F => ?_
  have hinj : Function.Injective (fun k : Fin F.card => ((F.equivFin.symm k : {x // x ∈ F}) : ι)) :=
    fun a b hab => F.equivFin.symm.injective (Subtype.ext hab)
  have horth : Orthonormal ℝ (fun k : Fin F.card => e ((F.equivFin.symm k : {x // x ∈ F}) : ι)) :=
    e.orthonormal.comp _ hinj
  let p : OrthonormalPairs H := ⟨⟨F.card, (fun k => e ((F.equivFin.symm k : {x // x ∈ F}) : ι)),
    (fun k => e ((F.equivFin.symm k : {x // x ∈ F}) : ι))⟩, horth, horth⟩
  have h1 := pairSum_le_traceNormForm (bddAbove_pairSum hC) p
  have h2 : ∑ i, |C (p.1.2.1 i) (p.1.2.2 i)| = ∑ i ∈ F, C (e i) (e i) := by
    have : ∑ i, |C (p.1.2.1 i) (p.1.2.2 i)| = ∑ i : {x // x ∈ F}, |C (e i) (e i)| :=
      Equiv.sum_comp F.equivFin.symm (fun i : {x // x ∈ F} => |C (e i) (e i)|)
    rw [this, Finset.sum_coe_sort F (fun i => |C (e i) (e i)|)]
    exact Finset.sum_congr rfl fun i _ => abs_of_nonneg (hC.nonneg _)
  rw [← h2]; exact h1

end Prelim

section Ct

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {ι : Type*} [Countable ι]

theorem exists_Ct {T : ℝ} {M : ℝ → Ω → H} {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)}
    (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg) (e : HilbertBasis ι ℝ H) :
    ∃ Ct : ℝ → Ω → H →L[ℝ] H →L[ℝ] ℝ,
      (∀ r ω, IsTraceClassCov (Ct r ω)) ∧ (∀ x y, IsProgressive ℱ (fun r ω => Ct r ω x y)) ∧
      (∀ r ∈ Set.Icc 0 T, ∀ᵐ ω ∂P, Ct r ω = Sg r ω) ∧
      (∀ᵐ ω ∂P, ∀ᵐ r ∂(volume.restrict (Set.Icc 0 T)), Ct r ω = Sg r ω) ∧
      (∀ᵐ ω ∂P, ∀ i j, IntegrableOn (fun r => Ct r ω (e i) (e j)) (Set.Icc 0 T)) ∧
      (∫⁻ ω, (∫⁻ r in Set.Icc 0 T, ENNReal.ofReal (∑' i, Ct r ω (e i) (e i))) ∂P ≠ ∞) := by
  obtain ⟨Ct, h1, h2, h3⟩ := exists_progressive_forms e T Sg hM.sigma_meas hM.sigma_adapted
    hM.sigma_traceClass
  have hCtm : ∀ i j, Measurable fun p : ℝ × Ω => Ct p.1 p.2 (e i) (e j) := fun i j =>
    isProgressive_measurable_uncurry (h2 (e i) (e j))
  have hSm : ∀ i j, Measurable fun p : ℝ × Ω => Sg p.1 p.2 (e i) (e j) := fun i j =>
    hM.sigma_meas _ _
  set Eset : Set (ℝ × Ω) := {p | ∃ i j, Ct p.1 p.2 (e i) (e j) ≠ Sg p.1 p.2 (e i) (e j)} with hE
  have hEm : MeasurableSet Eset := by
    have : Eset = ⋃ i, ⋃ j, {p : ℝ × Ω | Ct p.1 p.2 (e i) (e j) ≠ Sg p.1 p.2 (e i) (e j)} := by
      ext p; simp [hE]
    rw [this]
    exact MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun j =>
      (measurableSet_eq_fun (hCtm i j) (hSm i j)).compl
  have hsec : ∀ r ∈ Set.Icc (0 : ℝ) T, P (Prod.mk r ⁻¹' Eset) = 0 := by
    intro r hr
    have := h3 r hr
    rw [ae_iff] at this
    refine measure_mono_null (fun ω hω => ?_) this
    obtain ⟨i, j, hij⟩ := hω
    intro heq
    exact hij (by rw [heq])
  have hprod : ((volume.restrict (Set.Icc (0 : ℝ) T)).prod P) Eset = 0 := by
    rw [Measure.measure_prod_null hEm]
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact hsec r hr
  have hae1 : ∀ᵐ p ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod P), p ∉ Eset := by
    rw [ae_iff]; simpa using hprod
  have hae2 : ∀ᵐ r ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P, (r, ω) ∉ Eset :=
    Measure.ae_ae_of_ae_prod hae1
  have hae3 : ∀ᵐ ω ∂P, ∀ᵐ r ∂(volume.restrict (Set.Icc (0 : ℝ) T)), (r, ω) ∉ Eset :=
    (Measure.ae_ae_comm (μ := volume.restrict (Set.Icc (0 : ℝ) T)) (ν := P)
      (p := fun r ω => (r, ω) ∉ Eset) hEm.compl).1 hae2
  have h4 : ∀ᵐ ω ∂P, ∀ᵐ r ∂(volume.restrict (Set.Icc (0 : ℝ) T)), Ct r ω = Sg r ω := by
    filter_upwards [hae3] with ω hω
    filter_upwards [hω] with r hr
    refine form_ext_basis e fun i j => ?_
    by_contra hne
    exact hr ⟨i, j, hne⟩
  refine ⟨Ct, h1, h2, h3, h4, ?_, ?_⟩
  · filter_upwards [hM.sigma_entry_int, h4] with ω hω h4ω i j
    exact (hω (e i) (e j)).congr_fun_ae
      (h4ω.mono fun r hr => (congrArg (fun C => C (e i) (e j)) hr).symm)
  · have hb : ∀ᵐ ω ∂P, ∫⁻ r in Set.Icc 0 T, ENNReal.ofReal (∑' i, Ct r ω (e i) (e i)) ≤
        ENNReal.ofReal (∫ σ in Set.Icc 0 T, traceNormForm (Sg σ ω)) := by
      filter_upwards [hM.sigma_traceClass, hM.sigma_pathint, h4] with ω htc hpath h4ω
      rw [ofReal_integral_eq_lintegral_ofReal hpath
        (Eventually.of_forall fun σ => traceNormForm_nonneg _)]
      refine lintegral_mono_ae ?_
      filter_upwards [h4ω, ae_restrict_mem measurableSet_Icc] with r hr hrI
      refine ENNReal.ofReal_le_ofReal ?_
      rw [hr]
      exact tsum_diag_le_traceNormForm e (htc r hrI)
    refine ne_top_of_le_ne_top ?_ (lintegral_mono_ae hb)
    exact hM.sigma_int.lintegral_lt_top.ne

end Ct

section Reg

open Classical

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

lemma martingale_stopped {U : ℝ → Ω → ℝ} (hU : Martingale U ℱ P) (hU2 : ∀ t, MemLp (U t) 2 P)
    (c : ℝ) : Martingale (fun s ω => U (min c s) ω) ℱ P := by
  have := martingale_stop_mul hU (martingale_const ℱ P (1 : ℝ)) hU2 (fun t => memLp_const 1)
    (Λ := fun _ _ => 0) (by simpa using hU) c
  simpa using this

lemma martingale_stopped_mul {U V Λ : ℝ → Ω → ℝ} (hU : Martingale U ℱ P) (hV : Martingale V ℱ P)
    (hU2 : ∀ t, MemLp (U t) 2 P) (hV2 : ∀ t, MemLp (V t) 2 P)
    (hΛ : Martingale (fun t ω => U t ω * V t ω - Λ t ω) ℱ P) (c : ℝ) :
    Martingale (fun s ω => U (min c s) ω * V (min c s) ω - Λ (min c s) ω) ℱ P := by
  have h1 := martingale_stop_mul hU hV hU2 hV2 hΛ c
  have hU' := martingale_stopped hU hU2 c
  have hU2' : ∀ t, MemLp (fun ω => U (min c t) ω) 2 P := fun t => hU2 _
  have e1 : (fun t ω => V t ω * U (min c t) ω - Λ (min c t) ω) =
      fun t ω => U (min c t) ω * V t ω - Λ (min c t) ω := by
    funext t ω; ring
  have h2 := martingale_stop_mul (U := V) (V := fun s ω => U (min c s) ω)
    (Λ := fun s ω => Λ (min c s) ω) hV hU' hV2 hU2' (by
      show Martingale (fun t ω => V t ω * U (min c t) ω - Λ (min c t) ω) ℱ P
      rw [e1]; exact h1) c
  have e2 : (fun s ω => U (min c s) ω * V (min c s) ω - Λ (min c s) ω) =
      fun s ω => V (min c s) ω * U (min c (s)) ω - Λ (min c (min c s)) ω := by
    funext s ω
    rw [← min_assoc, min_self]
    ring
  rw [e2]
  exact h2

end Reg

section Reg2

open Classical

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
variable {ι : Type*} [Countable ι]

/-- Clamping of time to `[0,T]`. -/
def clampT (T t : ℝ) : ℝ := max 0 (min t T)

lemma clampT_mem {T : ℝ} (hT : 0 ≤ T) (t : ℝ) : clampT T t ∈ Set.Icc 0 T :=
  ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩

lemma clampT_of_mem {T : ℝ} {t : ℝ} (ht : t ∈ Set.Icc 0 T) : clampT T t = t := by
  simp [clampT, min_eq_left ht.2, max_eq_right ht.1]

lemma clampT_of_nonneg {T : ℝ} (hT : 0 ≤ T) {t : ℝ} (ht : 0 ≤ t) : clampT T t = min t T := by
  simp only [clampT]
  exact max_eq_right (le_min ht hT)

lemma clampT_of_nonpos {T : ℝ} {t : ℝ} (ht : t ≤ 0) : clampT T t = 0 := by
  simp only [clampT]
  exact max_eq_left ((min_le_left t T).trans ht)

lemma continuous_clampT (T : ℝ) : Continuous (clampT T) :=
  continuous_const.max (continuous_id.min continuous_const)

/-- The regularised martingale. -/
def regM (T : ℝ) (N : Set Ω) (M : ℝ → Ω → H) : ℝ → Ω → H :=
  fun t ω => if ω ∈ N then 0 else M (clampT T t) ω

lemma regM_cont {T : ℝ} (hT : 0 ≤ T) {N : Set Ω} {M : ℝ → Ω → H}
    (hN : ∀ ω, ω ∉ N → M 0 ω = 0 ∧ ContinuousOn (fun τ => M τ ω) (Set.Icc 0 T)) (ω : Ω) :
    Continuous fun t => regM T N M t ω := by
  by_cases hω : ω ∈ N
  · simp only [regM, hω, if_true]; exact continuous_const
  · simp only [regM, hω, if_false]
    exact (hN ω hω).2.comp_continuous (continuous_clampT T) (fun t => clampT_mem hT t)

lemma regM_zero {T : ℝ} {N : Set Ω} {M : ℝ → Ω → H}
    (hN : ∀ ω, ω ∉ N → M 0 ω = 0 ∧ ContinuousOn (fun τ => M τ ω) (Set.Icc 0 T)) {t : ℝ}
    (ht : t ≤ 0) (ω : Ω) : regM T N M t ω = 0 := by
  by_cases hω : ω ∈ N
  · simp [regM, hω]
  · simp only [regM, hω, if_false, clampT_of_nonpos ht]
    exact (hN ω hω).1

lemma regM_of_mem {T : ℝ} {N : Set Ω} {M : ℝ → Ω → H} {t : ℝ} (ht : t ∈ Set.Icc 0 T) {ω : Ω}
    (hω : ω ∉ N) : regM T N M t ω = M t ω := by
  simp only [regM, hω, if_false, clampT_of_mem ht]

lemma measurable_M_adapted {T : ℝ} {M : ℝ → Ω → H} {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)}
    (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg) (e : HilbertBasis ι ℝ H) (τ : ℝ) :
    Measurable[ℱ τ] (M τ) := by
  letI : MeasurableSpace Ω := ℱ τ
  refine measurable_of_inner_basis e (fun j => ?_)
  have h := ((hM.martingale (e j)).stronglyAdapted τ).measurable
  have : (fun ω => inner ℝ (e j) (M τ ω)) = fun ω => inner ℝ (M τ ω) (e j) := by
    funext ω; exact real_inner_comm _ _
  rw [this]; exact h

lemma regM_adapted {T : ℝ} (hT : 0 ≤ T) {N : Set Ω} {M : ℝ → Ω → H}
    {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)}
    (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg) (e : HilbertBasis ι ℝ H)
    (hN : ∀ ω, ω ∉ N → M 0 ω = 0 ∧ ContinuousOn (fun τ => M τ ω) (Set.Icc 0 T))
    (hNm : MeasurableSet N) (hN0 : P N = 0) (t : ℝ) :
    Measurable[augFiltration P ℱ t] (regM T N M t) := by
  by_cases ht : t ≤ 0
  · have : regM T N M t = fun _ => 0 := funext fun ω => regM_zero hN ht ω
    rw [this]; exact measurable_const
  · push Not at ht
    have hNa : MeasurableSet[augFiltration P ℱ t] N := augFiltration_isComplete ℱ t N hNm hN0
    have hM' : Measurable[augFiltration P ℱ t] (M (min t T)) :=
      (measurable_M_adapted hM e (min t T)).mono
        ((ℱ.mono (min_le_left t T)).trans le_sup_left) le_rfl
    have : regM T N M t = fun ω => if ω ∈ N then 0 else M (min t T) ω := by
      funext ω; simp only [regM, clampT_of_nonneg hT ht.le]
    rw [this]
    exact Measurable.ite hNa measurable_const hM'

lemma regM_ae {T : ℝ} {N : Set Ω} (hN0 : P N = 0) {M : ℝ → Ω → H} (t : ℝ) :
    ∀ᵐ ω ∂P, regM T N M t ω = M (clampT T t) ω := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with ω hω
  simp [regM, hω]

lemma regM_sq {T : ℝ} (hT : 0 ≤ T) {N : Set Ω} (hN0 : P N = 0) {M : ℝ → Ω → H}
    {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)}
    (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg) (t : ℝ) (x : H) :
    MemLp (fun ω => inner ℝ (regM T N M t ω) x) 2 P := by
  have h := (hM.sq_int (clampT T t) (clampT_mem hT t)).inner_const (𝕜 := ℝ) x
  refine h.ae_eq ?_
  filter_upwards [regM_ae (P := P) (T := T) hN0 (M := M) t] with ω hω
  rw [hω]

lemma martingale_stop_time {F : ℝ → Ω → ℝ} (hF : Martingale F ℱ P) (T : ℝ) :
    Martingale (fun s ω => F (min T s) ω) ℱ P := by
  refine ⟨fun s => (hF.1 (min T s)).mono (ℱ.mono (min_le_right T s)), fun s t hst => ?_⟩
  by_cases htT : t ≤ T
  · have h1 : min T t = t := min_eq_right htT
    have h2 : min T s = s := min_eq_right (hst.trans htT)
    simp only [h1, h2]
    exact hF.2 s t hst
  · push Not at htT
    have h1 : min T t = T := min_eq_left htT.le
    simp only [h1]
    by_cases hsT : s ≤ T
    · have h2 : min T s = s := min_eq_right hsT
      simp only [h2]
      exact hF.2 s T hsT
    · push Not at hsT
      have h2 : min T s = T := min_eq_left hsT.le
      simp only [h2]
      exact condExp_of_stronglyMeasurable (ℱ.le s) ((hF.1 T).mono (ℱ.mono hsT.le))
        (hF.integrable T) |>.eventuallyEq

lemma M_nonpos_ae {T : ℝ} {M : ℝ → Ω → H} {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)}
    (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg) {t : ℝ} (ht : t ≤ 0) (x : H) :
    ∀ᵐ ω ∂P, inner ℝ (M t ω) x = 0 := by
  have h1 := (hM.martingale x).2 t 0 ht
  have h0 : (fun ω => inner ℝ (M 0 ω) x) =ᵐ[P] 0 := by
    filter_upwards [hM.zero] with ω hω
    simp [hω]
  have h2 := condExp_congr_ae (m := ℱ t) h0
  rw [condExp_zero] at h2
  filter_upwards [h1, h2] with ω hω1 hω2
  rw [← hω1, hω2]; rfl

lemma integral_ite_Icc (T s : ℝ) (g : ℝ → ℝ) :
    ∫ r in Set.Icc 0 s, (if r ≤ T then g r else 0) = ∫ r in Set.Icc 0 (min T s), g r := by
  have h1 : (fun r => if r ≤ T then g r else 0) = (Set.Iic T).indicator g := by
    funext r; by_cases h : r ≤ T <;> simp [h, Set.indicator]
  have h2 : Set.Icc 0 s ∩ Set.Iic T = Set.Icc 0 (min T s) := by
    ext r
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iic, le_min_iff]
    tauto
  rw [h1, setIntegral_indicator measurableSet_Iic, h2]

lemma regM_mart {T : ℝ} (hT : 0 ≤ T) {N : Set Ω} {M : ℝ → Ω → H}
    {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)}
    (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg) (e : HilbertBasis ι ℝ H)
    (hN : ∀ ω, ω ∉ N → M 0 ω = 0 ∧ ContinuousOn (fun τ => M τ ω) (Set.Icc 0 T))
    (hNm : MeasurableSet N) (hN0 : P N = 0) (x : H) :
    Martingale (fun t ω => inner ℝ (regM T N M t ω) x) (augFiltration P ℱ) P := by
  have hX := martingale_aug (martingale_stop_time (hM.martingale x) T)
  refine martingale_congr_complete (augFiltration_isComplete ℱ) hX (fun t => ?_) (fun t => ?_)
  · have h := (regM_adapted hT hM e hN hNm hN0 t).mono (augFiltration P ℱ |>.le t) le_rfl
    exact h.inner measurable_const
  · by_cases ht : 0 ≤ t
    · filter_upwards [regM_ae (P := P) (T := T) hN0 (M := M) t] with ω hω
      show inner ℝ (M (min T t) ω) x = inner ℝ (regM T N M t ω) x
      rw [hω, clampT_of_nonneg hT ht, min_comm]
    · push Not at ht
      filter_upwards [M_nonpos_ae hM ht.le x] with ω hω
      show inner ℝ (M (min T t) ω) x = inner ℝ (regM T N M t ω) x
      rw [min_eq_right (ht.le.trans hT), regM_zero hN ht.le, inner_zero_left, hω]

lemma regM_cov {T : ℝ} (hT : 0 ≤ T) {N : Set Ω} {M : ℝ → Ω → H}
    {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)}
    (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg) (e : HilbertBasis ι ℝ H)
    (hN : ∀ ω, ω ∉ N → M 0 ω = 0 ∧ ContinuousOn (fun τ => M τ ω) (Set.Icc 0 T))
    (hNm : MeasurableSet N) (hN0 : P N = 0) {Ct : ℝ → Ω → H →L[ℝ] H →L[ℝ] ℝ}
    (hCprog : ∀ x y, IsProgressive ℱ (fun r ω => Ct r ω x y))
    (h4 : ∀ᵐ ω ∂P, ∀ᵐ r ∂(volume.restrict (Set.Icc 0 T)), Ct r ω = Sg r ω) (x y : H) :
    Martingale (fun t ω => inner ℝ (regM T N M t ω) x * inner ℝ (regM T N M t ω) y -
      ∫ r in Set.Icc 0 t, (if r ≤ T then Ct r ω x y else 0)) (augFiltration P ℱ) P := by
  have hX := martingale_aug (martingale_stop_time (hM.covariation x y) T)
  refine martingale_congr_complete (augFiltration_isComplete ℱ) hX (fun t => ?_) (fun t => ?_)
  · have h := (regM_adapted hT hM e hN hNm hN0 t).mono (augFiltration P ℱ |>.le t) le_rfl
    refine (h.inner measurable_const).mul (h.inner measurable_const) |>.sub ?_
    refine measurable_setIntegral_Icc (g := fun r ω => if r ≤ T then Ct r ω x y else 0) ?_ t
    exact Measurable.ite (measurableSet_le measurable_fst measurable_const)
      (isProgressive_measurable_uncurry (hCprog x y)) measurable_const
  · by_cases ht : 0 ≤ t
    · filter_upwards [regM_ae (P := P) (T := T) hN0 (M := M) t, h4] with ω hω h4ω
      show inner ℝ (M (min T t) ω) x * inner ℝ (M (min T t) ω) y -
          ∫ σ in Set.Icc 0 (min T t), Sg σ ω x y =
        inner ℝ (regM T N M t ω) x * inner ℝ (regM T N M t ω) y -
          ∫ r in Set.Icc 0 t, (if r ≤ T then Ct r ω x y else 0)
      rw [hω, clampT_of_nonneg hT ht, min_comm t T, integral_ite_Icc T t (fun r => Ct r ω x y)]
      congr 1
      have h5 : ∀ᵐ r ∂(volume.restrict (Set.Icc 0 (min T t))), Ct r ω = Sg r ω :=
        ae_restrict_of_ae_restrict_of_subset (Set.Icc_subset_Icc_right (min_le_left T t)) h4ω
      refine integral_congr_ae ?_
      filter_upwards [h5] with r hr
      rw [hr]
    · push Not at ht
      filter_upwards [M_nonpos_ae hM ht.le x, M_nonpos_ae hM ht.le y] with ω hx hy
      show inner ℝ (M (min T t) ω) x * inner ℝ (M (min T t) ω) y -
          ∫ σ in Set.Icc 0 (min T t), Sg σ ω x y =
        inner ℝ (regM T N M t ω) x * inner ℝ (regM T N M t ω) y -
          ∫ r in Set.Icc 0 t, (if r ≤ T then Ct r ω x y else 0)
      rw [min_eq_right (ht.le.trans hT), regM_zero hN ht.le, inner_zero_left, hx, hy,
        Set.Icc_eq_empty (not_le.2 ht)]
      simp

end Reg2

end HRS.MRep
