import HRS.MC.E213U13i

/-!
# E213U13j: closure properties of the second-chaos class `InQ2`, Gaussian moments of `InQ1` elements,
the product of two first-chaos elements.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false

noncomputable section

namespace HRS.MC.E213U13

section Q2

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {ξ : ℕ → Ω → ℝ}

theorem InQ2.add {hξ : IsStdGaussianSeq P ξ} {Y Z : Ω → ℝ} (hY : InQ2 hξ Y) (hZ : InQ2 hξ Z) :
    InQ2 hξ (fun ω => Y ω + Z ω) := by
  obtain ⟨h1, c1⟩ := hY
  obtain ⟨h2, c2⟩ := hZ
  refine ⟨h1.add h2, ?_⟩
  have e : MemLp.toLp (fun ω => Y ω + Z ω) (h1.add h2) = h1.toLp Y + h2.toLp Z := MemLp.toLp_add h1 h2
  rw [e]
  exact add_mem c1 c2

theorem InQ2.const_mul {hξ : IsStdGaussianSeq P ξ} {Y : Ω → ℝ} (c : ℝ) (hY : InQ2 hξ Y) :
    InQ2 hξ (fun ω => c * Y ω) := by
  obtain ⟨h1, c1⟩ := hY
  refine ⟨h1.const_mul c, ?_⟩
  have e : MemLp.toLp (fun ω => c * Y ω) (h1.const_mul c) = c • h1.toLp Y := by
    have := MemLp.toLp_const_smul (μ := P) c h1
    exact this
  rw [e]
  exact Submodule.smul_mem _ _ c1

theorem InQ2.zero {hξ : IsStdGaussianSeq P ξ} : InQ2 hξ (fun _ : Ω => (0 : ℝ)) := by
  have hz : MemLp (fun _ : Ω => (0 : ℝ)) 2 P := MemLp.zero
  refine ⟨hz, ?_⟩
  have e : hz.toLp (fun _ : Ω => (0 : ℝ)) = 0 := MemLp.toLp_zero hz
  rw [e]
  exact zero_mem _

theorem InQ2.sum {hξ : IsStdGaussianSeq P ξ} {ι : Type*} (s : Finset ι) {Y : ι → Ω → ℝ}
    (hY : ∀ i ∈ s, InQ2 hξ (Y i)) : InQ2 hξ (fun ω => ∑ i ∈ s, Y i ω) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using InQ2.zero (hξ := hξ)
  | insert a s ha ih =>
    have h1 := InQ2.add (hY a (Finset.mem_insert_self _ _)) (ih fun i hi => hY i (Finset.mem_insert_of_mem hi))
    simpa [Finset.sum_insert ha] using h1

theorem InQ2.congr_ae {hξ : IsStdGaussianSeq P ξ} {Y Z : Ω → ℝ} (h : Y =ᵐ[P] Z) (hY : InQ2 hξ Y) :
    InQ2 hξ Z := by
  obtain ⟨h1, c1⟩ := hY
  refine ⟨h1.ae_eq h, ?_⟩
  rwa [← MemLp.toLp_congr h1 (h1.ae_eq h) h]

theorem InQ2.of_tendsto {hξ : IsStdGaussianSeq P ξ} {ι : Type*} {l : Filter ι} [l.NeBot] {Y : ι → Ω → ℝ}
    {Z : Ω → ℝ} (hY : ∀ i, InQ2 hξ (Y i)) (hZ : AEStronglyMeasurable Z P)
    (hlim : Tendsto (fun i => ∫⁻ ω, ‖Y i ω - Z ω‖ₑ ^ (2 : ℝ) ∂P) l (𝓝 0)) : InQ2 hξ Z := by
  choose h hc using hY
  have hsub : ∀ i, AEStronglyMeasurable (fun ω => Y i ω - Z ω) P := fun i =>
    (h i).aestronglyMeasurable.sub hZ
  have hE : ∀ i, ∫⁻ ω, ‖Y i ω - Z ω‖ₑ ^ (2 : ℝ) ∂P = eLpNorm (fun ω => Y i ω - Z ω) 2 P ^ (2 : ℝ) :=
    fun i => lintegral_enorm_rpow_two (hsub i)
  have hN : Tendsto (fun i => eLpNorm (fun ω => Y i ω - Z ω) 2 P) l (𝓝 0) := by
    have h1 : Tendsto (fun i => eLpNorm (fun ω => Y i ω - Z ω) 2 P ^ (2 : ℝ)) l (𝓝 0) := by
      simpa only [hE] using hlim
    have h2 := ((ENNReal.continuous_rpow_const (y := ((2 : ℝ))⁻¹)).tendsto 0).comp h1
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h2
    refine h2.congr fun i => ?_
    simp only [Function.comp]
    exact ENNReal.rpow_rpow_inv (by norm_num) _
  have hfin : ∀ᶠ i in l, eLpNorm (fun ω => Y i ω - Z ω) 2 P < ∞ :=
    hN.eventually (gt_mem_nhds ENNReal.zero_lt_top)
  obtain ⟨i0, hi0⟩ := hfin.exists
  have hd : MemLp (fun ω => Y i0 ω - Z ω) 2 P := hi0
  have hZ2 : MemLp Z 2 P := by
    have h3 : MemLp (fun ω => Y i0 ω - (Y i0 ω - Z ω)) 2 P := (h i0).sub hd
    have e : (fun ω => Y i0 ω - (Y i0 ω - Z ω)) = Z := by funext ω; ring
    rwa [e] at h3
  refine ⟨hZ2, ?_⟩
  have hcl : IsClosed ((Qc (K2 hξ) : Submodule ℝ (Lp ℝ 2 P)) : Set (Lp ℝ 2 P)) :=
    Submodule.isClosed_topologicalClosure _
  refine hcl.mem_of_tendsto (b := l) (f := fun i => (h i).toLp (Y i)) ?_ (Eventually.of_forall hc)
  rw [tendsto_iff_dist_tendsto_zero]
  have hd2 : ∀ i, dist ((h i).toLp (Y i)) (hZ2.toLp Z) = (eLpNorm (fun ω => Y i ω - Z ω) 2 P).toReal := by
    intro i
    have := eLpNorm_sub_eq_dist ((h i).toLp (Y i)) hZ2
    have h1 : eLpNorm ((((h i).toLp (Y i) : Lp ℝ 2 P) : Ω → ℝ) - Z) 2 P =
        eLpNorm (fun ω => Y i ω - Z ω) 2 P :=
      eLpNorm_congr_ae (by filter_upwards [(h i).coeFn_toLp] with ω hω; simp [hω])
    rw [h1] at this
    rw [this, ENNReal.toReal_ofReal dist_nonneg]
  simp_rw [hd2]
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hN
  exact this.congr fun i => rfl |>.trans (by simp)

theorem InQ2_term (hξ : IsStdGaussianSeq P ξ) (i j : ℕ) :
    InQ2 hξ (fun ω => ξ i ω * ξ j ω - if i = j then 1 else 0) := by
  refine ⟨memLp_term hξ i j, ?_⟩
  show g2 hξ i j ∈ Qc (K2 hξ)
  have h1 : g2 hξ i j ∈ K2 hξ (max i j + 1) := by
    refine Submodule.subset_span ⟨(⟨i, by omega⟩, ⟨j, by omega⟩), rfl⟩
  exact Submodule.le_topologicalClosure _ ((le_iSup (K2 hξ) (max i j + 1)) h1)

end Q2

section Gauss1

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {ξ : ℕ → Ω → ℝ}
  (hξ : IsStdGaussianSeq P ξ) (hm : ∀ i, Measurable (ξ i))

include hm in
theorem InQ1.exists_gaussian {X : Ω → ℝ} (hX : InQ1 hξ hm X) : ∃ v : ℝ≥0, P.map X = gaussianReal 0 v := by
  obtain ⟨h, hc⟩ := hX
  have hG : (Qc (K1 hξ hm) : Set (Lp ℝ 2 P)) ⊆
      {z : Lp ℝ 2 P | ∃ v : ℝ≥0, P.map (z : Ω → ℝ) = gaussianReal 0 v} := by
    unfold Qc
    rw [Submodule.topologicalClosure_coe]
    refine closure_minimal ?_ isClosed_gaussian
    intro z hz
    have hz' : z ∈ ⨆ n, K1 hξ hm n := hz
    rw [Submodule.mem_iSup_of_directed _ (K1_mono hξ hm).directed_le] at hz'
    obtain ⟨n, hn⟩ := hz'
    obtain ⟨a, ha⟩ := K1_poly hξ hm z hn
    obtain ⟨v, hv⟩ := xi_linear_gauss hξ hm n a
    refine ⟨v, ?_⟩
    rw [Measure.map_congr ha]
    simpa [smul_eq_mul] using hv
  obtain ⟨v, hv⟩ := hG hc
  refine ⟨v, ?_⟩
  rw [← hv]
  exact Measure.map_congr h.coeFn_toLp.symm

include hm in
theorem InQ1.memLp {X : Ω → ℝ} (hX : InQ1 hξ hm X) (p : ℝ≥0) : MemLp X p P := by
  obtain ⟨v, hv⟩ := InQ1.exists_gaussian hξ hm hX
  obtain ⟨h, -⟩ := hX
  have h1 : MemLp id (p : ℝ≥0∞) (P.map X) := by rw [hv]; exact memLp_id_gaussianReal p
  have := (memLp_map_measure_iff aestronglyMeasurable_id h.aestronglyMeasurable.aemeasurable).1 h1
  simpa using this

end Gauss1

section Prod

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {ξ : ℕ → Ω → ℝ}
  (hξ : IsStdGaussianSeq P ξ) (hm : ∀ i, Measurable (ξ i))

instance holder442 : ENNReal.HolderTriple (4 : ℝ≥0∞) 4 2 := by
  refine ⟨?_⟩
  have h : (4 : ℝ≥0∞) = 2 * 2 := by norm_num
  rw [h, ENNReal.mul_inv (by simp) (by simp), ← two_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]

theorem eLpNorm_mul_two_le {f g : Ω → ℝ} (hf : AEStronglyMeasurable f P) (hg : AEStronglyMeasurable g P) :
    eLpNorm (fun ω => f ω * g ω) 2 P ≤ eLpNorm f 4 P * eLpNorm g 4 P :=
  eLpNorm_smul_le_mul_eLpNorm (p := 4) (q := 4) (r := 2) hf hg

theorem eLpNorm_const_integral_le {f : Ω → ℝ} (hf : AEStronglyMeasurable f P) :
    eLpNorm (fun _ : Ω => ∫ ω, f ω ∂P) 2 P ≤ eLpNorm f 2 P := by
  rw [eLpNorm_const _ (by norm_num) (NeZero.ne P)]
  simp only [measure_univ, ENNReal.one_rpow, mul_one]
  calc ‖∫ ω, f ω ∂P‖ₑ ≤ ∫⁻ ω, ‖f ω‖ₑ ∂P := enorm_integral_le_lintegral_enorm f
    _ = eLpNorm f 1 P := (eLpNorm_one_eq_lintegral_enorm hf).symm
    _ ≤ eLpNorm f 2 P := eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)

theorem InQ2.mul_centered {X Y : Ω → ℝ} (hX : InQ1 hξ hm X) (hY : InQ1 hξ hm Y) :
    InQ2 hξ (fun ω => X ω * Y ω - ∫ ω', X ω' * Y ω' ∂P) := by
  classical
  have hX5 : MemLp X (ENNReal.ofReal 5) P := by
    have := InQ1.memLp hξ hm hX 5
    simpa using this
  have hY5 : MemLp Y (ENNReal.ofReal 5) P := by
    have := InQ1.memLp hξ hm hY 5
    simpa using this
  have hXm : AEStronglyMeasurable X P := hX5.aestronglyMeasurable
  have hYm : AEStronglyMeasurable Y P := hY5.aestronglyMeasurable
  obtain ⟨c, hc⟩ := firstApprox_of_InQ1 hξ hm hX (q := 4) (r := 5) (by norm_num) (by norm_num) hX5
  obtain ⟨d, hd⟩ := firstApprox_of_InQ1 hξ hm hY (q := 4) (r := 5) (by norm_num) (by norm_num) hY5
  set p : ℕ → Ω → ℝ := fun m ω => ∑ i ∈ Finset.range m, ξ i ω • c m i with hp
  set q : ℕ → Ω → ℝ := fun m ω => ∑ j ∈ Finset.range m, ξ j ω • d m j with hq
  have hpmeas : ∀ m, Measurable (p m) := fun m =>
    Finset.measurable_sum _ fun i _ => (hm i).smul_const _
  have hqmeas : ∀ m, Measurable (q m) := fun m =>
    Finset.measurable_sum _ fun i _ => (hm i).smul_const _
  have hpL : ∀ m, MemLp (p m) 4 P := fun m => by
    have : MemLp (fun ω => ∑ i ∈ Finset.range m, ξ i ω * c m i) 4 P := by
      refine memLp_finsetSum _ fun i _ => ?_
      have h4 : MemLp (ξ i) 4 P := by
        have := (hξ.2 i)
        have hg : MemLp id (4 : ℝ≥0) (gaussianReal 0 1) := memLp_id_gaussianReal 4
        rw [← this] at hg
        have := (memLp_map_measure_iff aestronglyMeasurable_id (hm i).aemeasurable).1 hg
        simpa using this
      exact h4.mul_const _
    simpa [hp, smul_eq_mul] using this
  have hqL : ∀ m, MemLp (q m) 4 P := fun m => by
    have : MemLp (fun ω => ∑ i ∈ Finset.range m, ξ i ω * d m i) 4 P := by
      refine memLp_finsetSum _ fun i _ => ?_
      have h4 : MemLp (ξ i) 4 P := by
        have := (hξ.2 i)
        have hg : MemLp id (4 : ℝ≥0) (gaussianReal 0 1) := memLp_id_gaussianReal 4
        rw [← this] at hg
        have := (memLp_map_measure_iff aestronglyMeasurable_id (hm i).aemeasurable).1 hg
        simpa using this
      exact h4.mul_const _
    simpa [hq, smul_eq_mul] using this
  have hX4 : MemLp X 4 P := by simpa using InQ1.memLp hξ hm hX 4
  have hY4 : MemLp Y 4 P := by simpa using InQ1.memLp hξ hm hY 4
  have ha : Tendsto (fun m => eLpNorm (fun ω => p m ω - X ω) 4 P) atTop (𝓝 0) := by
    have := (tendsto_lintegral_iff_eLpNorm (fun m => ((hpmeas m).aestronglyMeasurable.sub hXm))
      (by norm_num : (0 : ℝ) < 4)).1 hc
    rwa [show ENNReal.ofReal 4 = 4 by norm_num] at this
  have hb : Tendsto (fun m => eLpNorm (fun ω => q m ω - Y ω) 4 P) atTop (𝓝 0) := by
    have := (tendsto_lintegral_iff_eLpNorm (fun m => ((hqmeas m).aestronglyMeasurable.sub hYm))
      (by norm_num : (0 : ℝ) < 4)).1 hd
    rwa [show ENNReal.ofReal 4 = 4 by norm_num] at this
  -- the product error
  set W : ℕ → Ω → ℝ := fun m ω => p m ω * q m ω - X ω * Y ω with hW
  have hWbound : ∀ m, eLpNorm (W m) 2 P ≤ eLpNorm (fun ω => p m ω - X ω) 4 P *
      (eLpNorm Y 4 P + eLpNorm (fun ω => q m ω - Y ω) 4 P) +
      eLpNorm X 4 P * eLpNorm (fun ω => q m ω - Y ω) 4 P := by
    intro m
    have e : W m = fun ω => (p m ω - X ω) * q m ω + X ω * (q m ω - Y ω) := by
      funext ω; simp only [hW]; ring
    rw [e]
    have hpX : AEStronglyMeasurable (fun ω => p m ω - X ω) P := (hpmeas m).aestronglyMeasurable.sub hXm
    have hqY : AEStronglyMeasurable (fun ω => q m ω - Y ω) P := (hqmeas m).aestronglyMeasurable.sub hYm
    have h1 : eLpNorm (fun ω => (p m ω - X ω) * q m ω + X ω * (q m ω - Y ω)) 2 P ≤
        eLpNorm (fun ω => (p m ω - X ω) * q m ω) 2 P + eLpNorm (fun ω => X ω * (q m ω - Y ω)) 2 P :=
      eLpNorm_add_le (by norm_num)
    have h2 := eLpNorm_mul_two_le hpX (hqmeas m).aestronglyMeasurable
    have h3 := eLpNorm_mul_two_le hXm hqY
    have h4 : eLpNorm (q m) 4 P ≤ eLpNorm Y 4 P + eLpNorm (fun ω => q m ω - Y ω) 4 P := by
      have e2 : q m = fun ω => Y ω + (q m ω - Y ω) := by funext ω; ring
      calc eLpNorm (q m) 4 P = eLpNorm (fun ω => Y ω + (q m ω - Y ω)) 4 P := by rw [← e2]
        _ ≤ _ := eLpNorm_add_le (by norm_num)
    calc _ ≤ _ := h1
      _ ≤ eLpNorm (fun ω => p m ω - X ω) 4 P * eLpNorm (q m) 4 P +
          eLpNorm X 4 P * eLpNorm (fun ω => q m ω - Y ω) 4 P := add_le_add h2 h3
      _ ≤ _ := by gcongr
  have hWlim : Tendsto (fun m => eLpNorm (W m) 2 P) atTop (𝓝 0) := by
    have hfinY : eLpNorm Y 4 P ≠ ∞ := hY4.eLpNorm_lt_top.ne
    have hfinX : eLpNorm X 4 P ≠ ∞ := hX4.eLpNorm_lt_top.ne
    have h1 : Tendsto (fun m => eLpNorm Y 4 P + eLpNorm (fun ω => q m ω - Y ω) 4 P) atTop
        (𝓝 (eLpNorm Y 4 P + 0)) := tendsto_const_nhds.add hb
    have h2 := ENNReal.Tendsto.mul ha (Or.inr (by simpa using hfinY)) h1 (Or.inr (by simp))
    have h3 := ENNReal.Tendsto.const_mul hb (Or.inr hfinX : (0 : ℝ≥0∞) ≠ 0 ∨ eLpNorm X 4 P ≠ ∞)
    have h4 := h2.add h3
    simp only [zero_mul, mul_zero, add_zero] at h4
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h4 (fun m => bot_le) hWbound
  -- the polynomials
  set Yp : ℕ → Ω → ℝ := fun m ω => ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
      (c m i * d m j) * (ξ i ω * ξ j ω - if i = j then 1 else 0) with hYp
  have hYpQ : ∀ m, InQ2 hξ (Yp m) := fun m =>
    InQ2.sum (Y := fun i ω => ∑ j ∈ Finset.range m,
      (c m i * d m j) * (ξ i ω * ξ j ω - if i = j then 1 else 0)) _ fun i _ =>
      InQ2.sum (Y := fun j ω => (c m i * d m j) * (ξ i ω * ξ j ω - if i = j then 1 else 0)) _ fun j _ =>
        InQ2.const_mul _ (InQ2_term hξ i j)
  have hxx : ∀ i j, Integrable (fun ω => ξ i ω * ξ j ω) P := fun i j =>
    (memLp_xi hξ hm i).integrable_mul (memLp_xi hξ hm j)
  have hpq : ∀ m, ∀ ω, p m ω * q m ω = ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
      (c m i * d m j) * (ξ i ω * ξ j ω) := by
    intro m ω
    simp only [hp, hq, smul_eq_mul, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hEq : ∀ m, ∫ ω, p m ω * q m ω ∂P = ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range m,
      (c m i * d m j) * (if i = j then 1 else 0) := by
    intro m
    simp_rw [hpq]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hxx i j).const_mul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun j _ => (hxx i j).const_mul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, integral_xi_mul hξ hm]
  have hYpeq : ∀ m ω, Yp m ω = p m ω * q m ω - ∫ ω', p m ω' * q m ω' ∂P := by
    intro m ω
    rw [hEq m, hpq m ω]
    simp only [hYp, mul_sub, Finset.sum_sub_distrib]
  have hpqL : ∀ m, MemLp (fun ω => p m ω * q m ω) 2 P := fun m => (hpL m).mul (hqL m)
  have hXYL : MemLp (fun ω => X ω * Y ω) 2 P := hX4.mul hY4
  set Z : Ω → ℝ := fun ω => X ω * Y ω - ∫ ω', X ω' * Y ω' ∂P with hZ
  have hZm : AEStronglyMeasurable Z P := (hXm.mul hYm).sub aestronglyMeasurable_const
  have hWm : ∀ m, AEStronglyMeasurable (W m) P := fun m =>
    ((hpqL m).aestronglyMeasurable).sub (hXm.mul hYm)
  have hdiff : ∀ m ω, Yp m ω - Z ω = W m ω - ∫ ω', W m ω' ∂P := by
    intro m ω
    have : ∫ ω', W m ω' ∂P = (∫ ω', p m ω' * q m ω' ∂P) - ∫ ω', X ω' * Y ω' ∂P :=
      integral_sub ((hpqL m).integrable (by norm_num)) (hXYL.integrable (by norm_num))
    rw [this, hYpeq m ω]
    simp only [hZ, hW]
    ring
  have hN : Tendsto (fun m => eLpNorm (fun ω => Yp m ω - Z ω) 2 P) atTop (𝓝 0) := by
    have hle : ∀ m, eLpNorm (fun ω => Yp m ω - Z ω) 2 P ≤ eLpNorm (W m) 2 P + eLpNorm (W m) 2 P := by
      intro m
      have e : (fun ω => Yp m ω - Z ω) = fun ω => W m ω - ∫ ω', W m ω' ∂P := by
        funext ω; exact hdiff m ω
      rw [e]
      calc eLpNorm (fun ω => W m ω - ∫ ω', W m ω' ∂P) 2 P
          ≤ eLpNorm (W m) 2 P + eLpNorm (fun _ : Ω => ∫ ω', W m ω' ∂P) 2 P := by
            have := eLpNorm_sub_le (f := W m) (g := fun _ : Ω => ∫ ω', W m ω' ∂P)
              (p := 2) (μ := P) (by norm_num)
            exact this
        _ ≤ _ := add_le_add le_rfl (eLpNorm_const_integral_le (hWm m))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun m => bot_le) hle
    have := hWlim.add hWlim
    simpa using this
  refine InQ2.of_tendsto (l := atTop) hYpQ hZm ?_
  have hEL : ∀ m, ∫⁻ ω, ‖Yp m ω - Z ω‖ₑ ^ (2 : ℝ) ∂P = eLpNorm (fun ω => Yp m ω - Z ω) 2 P ^ (2 : ℝ) :=
    fun m => lintegral_enorm_rpow_two (((hYpQ m).1.aestronglyMeasurable).sub hZm)
  simp_rw [hEL]
  have := (ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto 0 |>.comp hN
  rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at this

end Prod

end HRS.MC.E213U13
