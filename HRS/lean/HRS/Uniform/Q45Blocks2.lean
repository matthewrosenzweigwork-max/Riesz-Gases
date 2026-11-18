import HRS.Uniform.Q45Blocks1

/-!
# Q45: the cell interface of a block transform
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators Matrix

namespace HRS.Uniform.Q45

open HRS HRS.LindebergAux

variable {m q : ℕ}

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]

lemma blockProc_apply (A : ℕ → Matrix (Fin m) (Fin q) ℝ) (Nb : ℕ) (T : ℝ) (N : ℝ → Ω → ℝ^q) (s : ℝ)
    (ω : Ω) (i : Fin m) :
    blockProc A Nb T N s ω i = ∑ k ∈ Finset.range Nb, ∑ c, A k i c *
      (N (min s (rr Nb T (k + 1))) ω c - N (min s (rr Nb T k)) ω c) := by
  unfold blockProc
  have : (∑ k ∈ Finset.range Nb, actCLM (A k)
      (N (min s (rr Nb T (k + 1))) ω - N (min s (rr Nb T k)) ω)) i =
      ∑ k ∈ Finset.range Nb, (actCLM (A k)
      (N (min s (rr Nb T (k + 1))) ω - N (min s (rr Nb T k)) ω)) i := by
    have := congrFun (WithLp.ofLp_sum 2 (Fin m → ℝ) (Finset.range Nb) (fun k => actCLM (A k)
      (N (min s (rr Nb T (k + 1))) ω - N (min s (rr Nb T k)) ω))) i
    simpa [Finset.sum_apply] using this
  rw [this]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [actCLM_apply]
  simp


lemma blockProc_memLp {T : ℝ} (hT : 0 ≤ T) {Nb : ℕ} {A : ℕ → Matrix (Fin m) (Fin q) ℝ}
    {ℱ : Filtration ℝ mΩ} {N : ℝ → Ω → ℝ^q} {Sq : ℝ → Ω → Matrix (Fin q) (Fin q) ℝ}
    (hN : IsVectorMartingaleWithCovariation P ℱ T N Sq) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) T) :
    MemLp (blockProc A Nb T N τ) 2 P := by
  have hmem : ∀ r : ℝ, 0 ≤ r → r ∈ Set.Icc (0 : ℝ) T ∨ True → min τ r ∈ Set.Icc (0 : ℝ) T := by
    intro r hr _
    exact ⟨le_min hτ.1 hr, (min_le_left _ _).trans hτ.2⟩
  have : blockProc A Nb T N τ = ∑ k ∈ Finset.range Nb, fun ω => actCLM (A k)
      (N (min τ (rr Nb T (k + 1))) ω - N (min τ (rr Nb T k)) ω) := by
    funext ω
    simp [blockProc, Finset.sum_apply]
  rw [this]
  refine memLp_finset_sum' _ fun k _ => ?_
  have h1 := hN.sq_int (min τ (rr Nb T (k + 1))) (hmem _ (rr_nonneg hT _) (Or.inr trivial))
  have h2 := hN.sq_int (min τ (rr Nb T k)) (hmem _ (rr_nonneg hT _) (Or.inr trivial))
  exact (actCLM (A k)).comp_memLp' (h1.sub h2)

lemma blockProc_adapted {T : ℝ} (hT : 0 ≤ T) {Nb : ℕ} {A : ℕ → Matrix (Fin m) (Fin q) ℝ}
    {ℱ : Filtration ℝ mΩ} {N : ℝ → Ω → ℝ^q} {Sq : ℝ → Ω → Matrix (Fin q) (Fin q) ℝ}
    (hN : IsVectorMartingaleWithCovariation P ℱ T N Sq) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) T)
    (i : Fin m) : StronglyMeasurable[ℱ τ] (fun ω => blockProc A Nb T N τ ω i) := by
  simp only [blockProc_apply]
  refine Finset.stronglyMeasurable_fun_sum _ fun k _ => Finset.stronglyMeasurable_fun_sum _ fun c _ => ?_
  refine StronglyMeasurable.const_mul ?_ _
  have a1 : StronglyMeasurable[ℱ τ] (fun ω => N (min τ (rr Nb T (k + 1))) ω c) :=
    ((hN.martingale c).1 _).mono (ℱ.mono (min_le_left _ _))
  have a2 : StronglyMeasurable[ℱ τ] (fun ω => N (min τ (rr Nb T k)) ω c) :=
    ((hN.martingale c).1 _).mono (ℱ.mono (min_le_left _ _))
  exact a1.sub a2


lemma blockProc_cell_apply {T : ℝ} (hT : 0 ≤ T) {Nb : ℕ} (hNb : 1 ≤ Nb)
    {A : ℕ → Matrix (Fin m) (Fin q) ℝ} (N : ℝ → Ω → ℝ^q) {k : ℕ} (hk : k < Nb) {τ τ' : ℝ}
    (h1 : rr Nb T k ≤ τ) (h2 : τ ≤ τ') (h3 : τ' ≤ rr Nb T (k + 1)) (ω : Ω) (i : Fin m) :
    blockProc A Nb T N τ' ω i = blockProc A Nb T N τ ω i +
      ∑ c, A k i c * (N τ' ω c - N τ ω c) := by
  have := congrArg (fun v : ℝ^m => v i) (blockProc_cell (A := A) hT hNb N hk h1 h2 h3 ω)
  simp only [PiLp.sub_apply, actCLM_apply] at this
  linarith [this]


lemma blockCov_entry (A : ℕ → Matrix (Fin m) (Fin q) ℝ) (Nb : ℕ) (T : ℝ) (S : Matrix (Fin q) (Fin q) ℝ)
    (σ : ℝ) (a b : Fin m) :
    blockCov A Nb T S σ a b = ∑ c, ∑ c', A (blk Nb T σ) a c * S c c' * A (blk Nb T σ) b c' := by
  unfold blockCov
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

lemma measurable_blockCov_entry (A : ℕ → Matrix (Fin m) (Fin q) ℝ) (Nb : ℕ) (T : ℝ)
    {α : Type*} [MeasurableSpace α] (σf : α → ℝ) (hσ : Measurable σf)
    (S : α → Matrix (Fin q) (Fin q) ℝ) (hS : ∀ c c', Measurable fun x => S x c c') (a b : Fin m) :
    Measurable fun x => blockCov A Nb T (S x) (σf x) a b := by
  simp only [blockCov_entry]
  refine Finset.measurable_sum _ fun c _ => Finset.measurable_sum _ fun c' _ => ?_
  have hA : ∀ (i : Fin m) (j : Fin q), Measurable fun x => A (blk Nb T (σf x)) i j := fun i j =>
    (measurable_from_nat (f := fun n => A n i j)).comp ((measurable_blk Nb T).comp hσ)
  exact ((hA a c).mul (hS c c')).mul (hA b c')

lemma measurable_blockCov (A : ℕ → Matrix (Fin m) (Fin q) ℝ) (Nb : ℕ) (T : ℝ)
    {α : Type*} [MeasurableSpace α] (σf : α → ℝ) (hσ : Measurable σf)
    (S : α → Matrix (Fin q) (Fin q) ℝ) (hS : ∀ c c', Measurable fun x => S x c c') :
    Measurable fun x => blockCov A Nb T (S x) (σf x) :=
  Measurable.of_eval fun a => Measurable.of_eval fun b => measurable_blockCov_entry A Nb T σf hσ S hS a b


section CellIfaceBlock

variable {ℱ : Filtration ℝ mΩ} {T : ℝ} {Nb : ℕ} {A : ℕ → Matrix (Fin m) (Fin q) ℝ}
  {N : ℝ → Ω → ℝ^q} {Sq : ℝ → Ω → Matrix (Fin q) (Fin q) ℝ}

lemma blockProc_orth (hT : 0 < T) (hNb : 1 ≤ Nb)
    (hN : IsVectorMartingaleWithCovariation P ℱ T N Sq) {τ τ' : ℝ} (hτ : 0 ≤ τ) (hττ' : τ ≤ τ')
    (hτ' : τ' ≤ T) (hadm : ∃ k < Nb, rr Nb T k ≤ τ ∧ τ' ≤ rr Nb T (k + 1)) (w : Ω → ℝ)
    (hw : StronglyMeasurable[ℱ τ] w) (hw2 : MemLp w 2 P) (i : Fin m) :
    ∫ ω, w ω * blockProc A Nb T N τ' ω i ∂P = ∫ ω, w ω * blockProc A Nb T N τ ω i ∂P := by
  obtain ⟨k, hk, h1, h3⟩ := hadm
  have hτT : τ ∈ Set.Icc (0 : ℝ) T := ⟨hτ, hττ'.trans hτ'⟩
  have hτ'T : τ' ∈ Set.Icc (0 : ℝ) T := ⟨hτ.trans hττ', hτ'⟩
  have hL2 := memLp_coord P (blockProc_memLp P hT.le hN (A := A) (Nb := Nb) hτT) i
  have hNc : ∀ c, ∫ ω, w ω * N τ' ω c ∂P = ∫ ω, w ω * N τ ω c ∂P := fun c =>
    integral_mul_martingale P ℱ (hN.martingale c) hττ' hw hw2 (memLp_coord P (hN.sq_int τ' hτ'T) c)
  have i1 : Integrable (fun ω => w ω * blockProc A Nb T N τ ω i) P := hw2.integrable_mul hL2
  have i2 : ∀ c, Integrable (fun ω => w ω * N τ ω c) P := fun c =>
    hw2.integrable_mul (memLp_coord P (hN.sq_int τ hτT) c)
  have i3 : ∀ c, Integrable (fun ω => w ω * N τ' ω c) P := fun c =>
    hw2.integrable_mul (memLp_coord P (hN.sq_int τ' hτ'T) c)
  have e : (fun ω => w ω * blockProc A Nb T N τ' ω i) = fun ω =>
      w ω * blockProc A Nb T N τ ω i +
        ∑ c, A k i c * (w ω * N τ' ω c - w ω * N τ ω c) := by
    funext ω
    rw [blockProc_cell_apply hT.le hNb N hk h1 hττ' h3 ω i, mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  have i4 : ∀ c, Integrable (fun ω => A k i c * (w ω * N τ' ω c - w ω * N τ ω c)) P := fun c =>
    ((i3 c).sub (i2 c)).const_mul (A k i c)
  rw [e, integral_add i1 (integrable_finsetSum _ fun c _ => i4 c),
    integral_finsetSum _ fun c _ => i4 c]
  have : ∀ c ∈ Finset.univ, ∫ ω, A k i c * (w ω * N τ' ω c - w ω * N τ ω c) ∂P = 0 := by
    intro c _
    rw [integral_const_mul, integral_sub (i3 c) (i2 c), hNc c, sub_self, mul_zero]
  rw [Finset.sum_eq_zero this, add_zero]

lemma blockProc_cov (hT : 0 < T) (hNb : 1 ≤ Nb)
    (hN : IsVectorMartingaleWithCovariation P ℱ T N Sq) {τ τ' : ℝ} (hτ : 0 ≤ τ) (hττ' : τ ≤ τ')
    (hτ' : τ' ≤ T) (hadm : ∃ k < Nb, rr Nb T k ≤ τ ∧ τ' ≤ rr Nb T (k + 1)) (z : Ω → ℝ)
    (hz : StronglyMeasurable[ℱ τ] z) (K : ℝ) (hzK : ∀ ω, |z ω| ≤ K) (a b : Fin m) :
    Integrable (fun ω => z ω * ((blockProc A Nb T N τ' ω - blockProc A Nb T N τ ω) a *
      (blockProc A Nb T N τ' ω - blockProc A Nb T N τ ω) b)) P ∧
    Integrable (fun ω => z ω * (∫ σ in Set.Icc τ τ', blockCov A Nb T (Sq σ ω) σ a b)) P ∧
    ∫ ω, z ω * ((blockProc A Nb T N τ' ω - blockProc A Nb T N τ ω) a *
      (blockProc A Nb T N τ' ω - blockProc A Nb T N τ ω) b) ∂P =
      ∫ ω, z ω * (∫ σ in Set.Icc τ τ', blockCov A Nb T (Sq σ ω) σ a b) ∂P := by
  obtain ⟨k, hk, h1, h3⟩ := hadm
  have hcp := fun c c' => cov_pair P ℱ T N Sq hN τ τ' hτ hττ' hτ' z hz K hzK c c'
  have hΔ : ∀ ω i, (blockProc A Nb T N τ' ω - blockProc A Nb T N τ ω) i =
      ∑ c, A k i c * (N τ' ω c - N τ ω c) := by
    intro ω i
    have := blockProc_cell_apply (A := A) hT.le hNb N hk h1 hττ' h3 ω i
    simp only [PiLp.sub_apply]
    linarith [this]
  have e1 : (fun ω => z ω * ((blockProc A Nb T N τ' ω - blockProc A Nb T N τ ω) a *
      (blockProc A Nb T N τ' ω - blockProc A Nb T N τ ω) b)) = fun ω =>
      ∑ c, ∑ c', (A k a c * A k b c') *
        (z ω * ((N τ' ω - N τ ω) c * (N τ' ω - N τ ω) c')) := by
    funext ω
    rw [hΔ ω a, hΔ ω b, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c' _ => ?_
    simp only [PiLp.sub_apply]
    ring
  have hR : ∀ᵐ ω ∂P, ∫ σ in Set.Icc τ τ', blockCov A Nb T (Sq σ ω) σ a b =
      ∑ c, ∑ c', (A k a c * A k b c') * ∫ σ in Set.Icc τ τ', Sq σ ω c c' := by
    filter_upwards [hN.sigma_entry_int] with ω he
    have hsub : Set.Icc τ τ' ⊆ Set.Icc 0 T := Set.Icc_subset_Icc hτ hτ'
    have e2 : ∫ σ in Set.Icc τ τ', blockCov A Nb T (Sq σ ω) σ a b =
        ∫ σ in Set.Icc τ τ', ∑ c, ∑ c', (A k a c * A k b c') * Sq σ ω c c' := by
      refine setIntegral_congr_ae measurableSet_Icc ?_
      filter_upwards [Measure.ae_ne volume (rr Nb T (k + 1))] with σ hne hσ
      rw [blockCov_entry, blk_eq hT hNb hk (h1.trans hσ.1) (lt_of_le_of_ne (hσ.2.trans h3) hne)]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun c' _ => ?_
      ring
    have i5 : ∀ c c', IntegrableOn (fun σ => (A k a c * A k b c') * Sq σ ω c c') (Set.Icc τ τ') :=
      fun c c' => ((he c c').mono_set hsub).const_mul (A k a c * A k b c')
    rw [e2, integral_finsetSum _ fun c _ => integrable_finsetSum _ fun c' _ => i5 c c']
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [integral_finsetSum _ fun c' _ => i5 c c']
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [integral_const_mul]
  have e3 : (fun ω => z ω * (∫ σ in Set.Icc τ τ', blockCov A Nb T (Sq σ ω) σ a b)) =ᵐ[P] fun ω =>
      ∑ c, ∑ c', (A k a c * A k b c') * (z ω * ∫ σ in Set.Icc τ τ', Sq σ ω c c') := by
    filter_upwards [hR] with ω hω
    rw [hω, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c' _ => ?_
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [e1]
    exact integrable_finsetSum _ fun c _ => integrable_finsetSum _ fun c' _ =>
      (hcp c c').1.const_mul _
  · refine Integrable.congr ?_ e3.symm
    exact integrable_finsetSum _ fun c _ => integrable_finsetSum _ fun c' _ =>
      (hcp c c').2.1.const_mul _
  · rw [e1, integral_congr_ae e3,
      integral_finsetSum _ fun c _ => integrable_finsetSum _ fun c' _ => (hcp c c').1.const_mul _,
      integral_finsetSum _ fun c _ => integrable_finsetSum _ fun c' _ => (hcp c c').2.1.const_mul _]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [integral_finsetSum _ fun c' _ => (hcp c c').1.const_mul _,
      integral_finsetSum _ fun c' _ => (hcp c c').2.1.const_mul _]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [integral_const_mul, integral_const_mul, (hcp c c').2.2]

/-- The block transform of a vector martingale satisfies the Lindeberg cell interface on the cells inside blocks. -/
theorem cellIface_block (hT : 0 < T) (hNb : 1 ≤ Nb) {c : ℝ} (hc : 0 ≤ c)
    (hA : ∀ k (u : Fin q → ℝ), ((A k).mulVec u) ⬝ᵥ ((A k).mulVec u) ≤ c ^ 2 * (u ⬝ᵥ u))
    (hN : IsVectorMartingaleWithCovariation P ℱ T N Sq) :
    CellIface P ℱ T (blockProc A Nb T N) (fun σ ω => blockCov A Nb T (Sq σ ω) σ)
      (fun τ τ' => ∃ k < Nb, rr Nb T k ≤ τ ∧ τ' ≤ rr Nb T (k + 1)) := by
  have hbd : ∀ σ ω, s1Norm (blockCov A Nb T (Sq σ ω) σ) ≤ c ^ 2 * s1Norm (Sq σ ω) := fun σ ω =>
    s1Norm_conj_le (A (blk Nb T σ)) hc (hA _) _
  have hmeasQ : ∀ c c' : Fin q, Measurable fun p : ℝ × Ω => Sq p.1 p.2 c c' := fun c c' =>
    (measurable_pi_apply c').comp ((measurable_pi_apply c).comp hN.sigma_meas)
  have hmeasP : Measurable (fun p : ℝ × Ω => blockCov A Nb T (Sq p.1 p.2) p.1) :=
    measurable_blockCov A Nb T Prod.fst measurable_fst _ hmeasQ
  have hmeasQ' : ∀ c c' : Fin q, Measurable fun p : Ω × ℝ => Sq p.2 p.1 c c' := fun c c' =>
    (hmeasQ c c').comp measurable_swap
  have hmeasF : Measurable (fun p : Ω × ℝ => s1Norm (blockCov A Nb T (Sq p.2 p.1) p.2)) :=
    continuous_s1Norm.measurable.comp
      (measurable_blockCov A Nb T Prod.snd measurable_snd _ hmeasQ')
  have hmeasσ : ∀ ω, Measurable fun σ : ℝ => blockCov A Nb T (Sq σ ω) σ := fun ω =>
    measurable_blockCov A Nb T id measurable_id _ (fun c c' => (hmeasQ c c').comp
      (measurable_id.prodMk measurable_const))
  have hpath : ∀ᵐ ω ∂P, IntegrableOn (fun σ => s1Norm (blockCov A Nb T (Sq σ ω) σ)) (Set.Icc 0 T) := by
    filter_upwards [hN.sigma_pathint] with ω h
    exact Integrable.mono' (h.const_mul (c ^ 2))
      (continuous_s1Norm.measurable.comp (hmeasσ ω)).aestronglyMeasurable
      (ae_of_all _ fun σ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (traceNormMatrix_nonneg _)]
        exact hbd σ ω)
  refine
    { adapted := fun τ hτ i => blockProc_adapted P hT.le hN hτ i
      sq_int := fun τ hτ => blockProc_memLp P hT.le hN hτ
      zero := ae_of_all _ fun ω => blockProc_zero hT.le N ω
      orth := fun τ τ' hτ hττ' hτ' hadm w hw hw2 i =>
        blockProc_orth P hT hNb hN hτ hττ' hτ' hadm w hw hw2 i
      cov := fun τ τ' hτ hττ' hτ' hadm z hz K hzK a b =>
        blockProc_cov P hT hNb hN hτ hττ' hτ' hadm z hz K hzK a b
      sigma_meas := hmeasP
      sigma_int := ?_
      sigma_pathint := hpath
      sigma_entry_int := ?_ }
  · refine Integrable.mono' (hN.sigma_int.const_mul (c ^ 2))
      (hmeasF.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Set.Icc 0 T))
        ).aestronglyMeasurable ?_
    filter_upwards [hN.sigma_pathint, hpath] with ω h1 h2
    have e0 : 0 ≤ ∫ σ in Set.Icc 0 T, s1Norm (blockCov A Nb T (Sq σ ω) σ) :=
      setIntegral_nonneg measurableSet_Icc fun σ _ => traceNormMatrix_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg e0, ← integral_const_mul]
    exact integral_mono h2 (h1.const_mul _) fun σ => hbd σ ω
  · filter_upwards [hpath] with ω h a b
    refine Integrable.mono' h ?_ (ae_of_all _ fun σ => ?_)
    · exact ((measurable_pi_apply b).comp ((measurable_pi_apply a).comp (hmeasσ ω))).aestronglyMeasurable
    · rw [Real.norm_eq_abs]
      exact abs_entry_le_s1 _ a b

end CellIfaceBlock

end HRS.Uniform.Q45
