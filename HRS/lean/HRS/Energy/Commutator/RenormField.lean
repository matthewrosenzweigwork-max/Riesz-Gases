import HRS.Energy.Commutator.RenormPolar

/-!
# Route S, packet S4: the local energy of the far field (`B4`)
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS.Commutator.RoughLimit

namespace HRS.Commutator.Renorm

variable {d : ℕ}

theorem sgv_apply (l : ℝ) (z : Torus d) (j : Fin d) : (SliceAux.sgv l z) j = SliceAux.sgc j l z := rfl

theorem integrable_sgv_sub_near {N : ℕ} {l : ℝ} (hl : 0 ≤ l) {X : Fin N → Torus d} {η : Fin N → ℝ}
    {σ : Fin N → Measure (Torus d)} (hS : SliceCharges l X η σ) [∀ i, IsFiniteMeasure (σ i)] {i : Fin N} {y : Torus d}
    (hy : η i < KernelGrad.tdist y (X i)) : Integrable (fun z => SliceAux.sgv l (y - z)) (σ i) := by
  have h := integrable_w_sub_near (w := SliceAux.sgv l) (measurable_sgv_l l)
    (fun δ hδ => sgv_bdd_away hl hδ) hS.supp hy
  refine h.neg.congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [Pi.neg_apply]
  rw [← sgv_odd]; congr 1; abel

theorem rep_comp {N : ℕ} {l : ℝ} (hl : 0 ≤ l) {X : Fin N → Torus d} {η : Fin N → ℝ}
    {σ : Fin N → Measure (Torus d)} (hS : SliceCharges l X η σ) {i : Fin N} {y : Torus d}
    (hy : η i < KernelGrad.tdist y (X i)) (j : Fin d) :
    ∫ z, SliceAux.sgc j l (y - z) ∂σ i = SliceAux.sgc j l (y - X i) := by
  haveI : ∀ i, IsFiniteMeasure (σ i) := hS.fin
  have h := hS.rep i y hy
  have hint : ∀ j : Fin d, Integrable (fun z => (SliceAux.sgv l (y - z)) j) (σ i) := fun j =>
    (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).integrable_comp (integrable_sgv_sub_near hl hS hy)
  have := congrArg (fun u : Euc d => u j) h
  simp only [] at this
  rw [eval_integral_piLp (hf := hint) j] at this
  exact this

theorem integral_avgM {N : ℕ} (hN : N ≠ 0) {σ : Fin N → Measure (Torus d)} {f : Torus d → ℝ}
    (hf : ∀ k, Integrable f (σ k)) : ∫ x, f x ∂(avgM σ) = (1 / (N : ℝ)) * ∑ k, ∫ x, f x ∂σ k := by
  unfold avgM
  rw [integral_smul_measure, ENNReal.toReal_inv, integral_finset_sum_measure (fun k _ => hf k)]
  simp [smul_eq_mul, one_div]

theorem integrable_sgc_sub_mu {l : ℝ} (hl : 0 ≤ l) (j : Fin d) (x : Torus d) {μ : Measure (Torus d)}
    [IsFiniteMeasure μ] {c : ℝ≥0∞} (hc : c ≠ ⊤) (hμ : μ ≤ c • (volume : Measure (Torus d))) :
    Integrable (fun y => SliceAux.sgc j l (x - y)) μ := by
  have h := ((RoughKernel.integrable_sgc (d := d) j hl).comp_sub_left x).smul_measure hc
  exact h.mono_measure hμ

theorem fieldF_apply {N : ℕ} {l : ℝ} (hl : 0 ≤ l) (X : Fin N → Torus d) {μ : Measure (Torus d)}
    [IsFiniteMeasure μ] {c : ℝ≥0∞} (hc : c ≠ ⊤) (hμ : μ ≤ c • (volume : Measure (Torus d))) (i : Fin N)
    (x : Torus d) (j : Fin d) :
    fieldF l X μ i x j = (1 / (N : ℝ)) * ∑ k ∈ Finset.univ.erase i, SliceAux.sgc j l (x - X k) -
      ∫ y, SliceAux.sgc j l (x - y) ∂μ := by
  unfold fieldF
  have hint : ∀ j : Fin d, Integrable (fun y => (SliceAux.sgv l (x - y)) j) μ := fun j =>
    integrable_sgc_sub_mu hl j x hc hμ
  rw [PiLp.sub_apply, PiLp.smul_apply, eval_integral_piLp (hf := hint) j]
  simp only [smul_eq_mul]
  congr 2
  simp [sgv_apply]

theorem tdist_far {N : ℕ} {X : Fin N → Torus d} {r : Fin N → ℝ}
    (hsep : ∀ i j, i ≠ j → r i + r j < KernelGrad.tdist (X i) (X j)) {i k : Fin N} (hik : k ≠ i) {x : Torus d}
    (hx : KernelGrad.tdist x (X i) < r i) : r k < KernelGrad.tdist x (X k) := by
  have h1 := tdist_tri (X i) x (X k)
  rw [tdist_symm' (X i) x] at h1
  have h2 := hsep i k hik.symm
  linarith

theorem field_ident {N : ℕ} (hN : N ≠ 0) {l : ℝ} (hl : 0 ≤ l) {X : Fin N → Torus d} {η : Fin N → ℝ}
    {σ : Fin N → Measure (Torus d)} (hS : SliceCharges l X η σ) {r : Fin N → ℝ} (hη : ∀ i, η i ≤ r i)
    (hsep : ∀ i j, i ≠ j → r i + r j < KernelGrad.tdist (X i) (X j)) {μ : Measure (Torus d)} [IsFiniteMeasure μ]
    {c : ℝ≥0∞} (hc : c ≠ ⊤) (hμ : μ ≤ c • (volume : Measure (Torus d))) (i : Fin N) {x : Torus d}
    (hx : KernelGrad.tdist x (X i) < r i) (hxi : ∀ j, Integrable (fun z => SliceAux.sgc j l (x - z)) (σ i))
    (j : Fin d) :
    (∫ z, SliceAux.sgc j l (x - z) ∂(avgM σ)) - ∫ z, SliceAux.sgc j l (x - z) ∂μ =
      fieldF l X μ i x j + (1 / (N : ℝ)) * ∫ z, SliceAux.sgc j l (x - z) ∂(σ i) := by
  haveI : ∀ i, IsFiniteMeasure (σ i) := hS.fin
  have hint : ∀ k, Integrable (fun z => SliceAux.sgc j l (x - z)) (σ k) := by
    intro k
    by_cases hk : k = i
    · subst hk; exact hxi j
    · have hy : η k < KernelGrad.tdist x (X k) := (hη k).trans_lt (tdist_far hsep hk hx)
      exact (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).integrable_comp (integrable_sgv_sub_near hl hS hy)
  rw [integral_avgM hN hint, fieldF_apply hl X hc hμ i x j, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have : ∑ k ∈ Finset.univ.erase i, ∫ z, SliceAux.sgc j l (x - z) ∂(σ k) =
      ∑ k ∈ Finset.univ.erase i, SliceAux.sgc j l (x - X k) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' : k ≠ i := Finset.ne_of_mem_erase hk
    exact rep_comp hl hS ((hη k).trans_lt (tdist_far hsep hk' hx)) j
  rw [this]
  ring

theorem integral_sgc_vol (l : ℝ) (j : Fin d) : ∫ z : Torus d, SliceAux.sgc j l z = 0 := by
  have h : ∫ z : Torus d, SliceAux.sgc j l (-z) = ∫ z : Torus d, SliceAux.sgc j l z :=
    integral_neg_eq_self (fun z : Torus d => SliceAux.sgc j l z) volume
  have hodd : ∀ z : Torus d, SliceAux.sgc j l (-z) = -SliceAux.sgc j l z := fun z => by
    have := congrArg (fun u : Euc d => u j) (sgv_odd l z); simpa [sgv_apply] using this
  simp_rw [hodd, integral_neg] at h
  linarith

theorem G_int_neutral {l : ℝ} (hl : 0 ≤ l) {σ : Measure (Torus d)} [IsFiniteMeasure σ]
    (hG : Integrable (fun p : Torus d × Torus d => sliceGfull d l (p.1 - p.2)) (σ.prod σ)) :
    Integrable (fun p : Torus d × Torus d => sliceGfull d l (p.1 - p.2))
      ((σ + ENNReal.ofReal (σ.real Set.univ) • (volume : Measure (Torus d))).prod
        (σ + ENNReal.ofReal (σ.real Set.univ) • (volume : Measure (Torus d)))) := by
  set α : Measure (Torus d) := ENNReal.ofReal (σ.real Set.univ) • (volume : Measure (Torus d)) with hα
  have hc : ENNReal.ofReal (σ.real Set.univ) ≠ ⊤ := ENNReal.ofReal_ne_top
  haveI : IsFiniteMeasure α := Measure.smul_finite _ hc
  have hle : α ≤ ENNReal.ofReal (σ.real Set.univ) • (volume : Measure (Torus d)) := le_rfl
  rw [Measure.add_prod, Measure.prod_add, Measure.prod_add]
  exact integrable_add_measure.mpr ⟨integrable_add_measure.mpr ⟨hG, integrable_G_mu hl σ hc hle⟩,
    integrable_add_measure.mpr ⟨integrable_G_mu_swap hl σ hc hle, integrable_G_mu hl α hc hle⟩⟩

theorem LE_self (hd : 1 ≤ d) {l : ℝ} (hl : 0 ≤ l) {σ : Measure (Torus d)} [IsFiniteMeasure σ]
    (hat : 2 ≤ d → ∀ x, σ {x} = 0)
    (hG : Integrable (fun p : Torus d × Torus d => sliceGfull d l (p.1 - p.2)) (σ.prod σ)) :
    Integrable (fun x => ∑ j, (∫ z, SliceAux.sgc j l (x - z) ∂σ) ^ 2) volume ∧
    ∫ x, ∑ j, (∫ z, SliceAux.sgc j l (x - z) ∂σ) ^ 2 ≤ quadForm (fun x y => sliceGfull d l (x - y)) σ
        (ENNReal.ofReal (σ.real Set.univ) • (volume : Measure (Torus d))) := by
  set α : Measure (Torus d) := ENNReal.ofReal (σ.real Set.univ) • (volume : Measure (Torus d)) with hα
  have hc : ENNReal.ofReal (σ.real Set.univ) ≠ ⊤ := ENNReal.ofReal_ne_top
  haveI : IsFiniteMeasure α := Measure.smul_finite _ hc
  have hle : α ≤ ENNReal.ofReal (σ.real Set.univ) • (volume : Measure (Torus d)) := le_rfl
  have h := LE_measures hd hl σ α
    (fun _ => by
      have hv1 : (volume : Measure (Torus d)) Set.univ = 1 := measure_univ
      rw [hα, Measure.smul_apply, hv1, smul_eq_mul, mul_one, Measure.real,
        ENNReal.ofReal_toReal (measure_ne_top σ _)])
    (fun h2 => ⟨hat h2, atomless_of_le_vol (by omega) hc hle⟩) (G_int_neutral hl hG)
  have hz : ∀ (x : Torus d) (j : Fin d), ∫ z, SliceAux.sgc j l (x - z) ∂α = 0 := by
    intro x j
    rw [hα, integral_smul_measure, integral_sub_left_eq_self (fun z => SliceAux.sgc j l z) volume x,
      integral_sgc_vol]
    simp
  simpa [hz] using h

theorem measurable_fieldF {N : ℕ} (l : ℝ) (X : Fin N → Torus d) (μ : Measure (Torus d)) [IsFiniteMeasure μ]
    (i : Fin N) : Measurable (fieldF l X μ i) := by
  unfold fieldF
  have hs : Measurable fun x : Torus d => ∑ j ∈ Finset.univ.erase i, SliceAux.sgv l (x - X j) :=
    Finset.measurable_sum _ fun j _ => (measurable_sgv_l l).comp (measurable_id.sub_const (X j))
  have h1 : Measurable fun x : Torus d => (1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i, SliceAux.sgv l (x - X j) :=
    hs.const_smul (1 / (N : ℝ))
  have h2 : Measurable fun x : Torus d => ∫ y, SliceAux.sgv l (x - y) ∂μ := by
    have : StronglyMeasurable (fun p : Torus d × Torus d => SliceAux.sgv l (p.1 - p.2)) :=
      ((measurable_sgv_l l).comp (measurable_fst.sub measurable_snd)).stronglyMeasurable
    exact (this.integral_prod_right' (ν := μ)).measurable
  exact h1.sub h2

theorem local_field_energy (hd : 1 ≤ d) {N : ℕ} (hN : N ≠ 0) {l : ℝ} (hl : 0 ≤ l) {X : Fin N → Torus d}
    {η : Fin N → ℝ} {σ : Fin N → Measure (Torus d)} (hS : SliceCharges l X η σ) {r : Fin N → ℝ}
    (hη : ∀ i, η i ≤ r i) (hsep : ∀ i j, i ≠ j → r i + r j < KernelGrad.tdist (X i) (X j))
    {μ : Measure (Torus d)} [IsFiniteMeasure μ] {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hμ : μ ≤ c • (volume : Measure (Torus d))) (hμ1 : μ Set.univ = 1) :
    (∀ i, Integrable (fun x => if KernelGrad.tdist x (X i) < r i then ‖fieldF l X μ i x‖ ^ 2 else 0) volume) ∧
    ∑ i, ∫ x, (if KernelGrad.tdist x (X i) < r i then ‖fieldF l X μ i x‖ ^ 2 else 0) ≤
      2 * quadForm (fun x y => sliceGfull d l (x - y)) (avgM σ) μ +
        2 * (1 / (N : ℝ)) ^ 2 * ∑ i, quadForm (fun x y => sliceGfull d l (x - y)) (σ i)
          (ENNReal.ofReal ((σ i).real Set.univ) • (volume : Measure (Torus d))) := by
  haveI : ∀ i, IsFiniteMeasure (σ i) := hS.fin
  haveI := isFiniteMeasure_avgM hN σ
  obtain ⟨hQHi, hQHle⟩ := LE_measures hd hl (avgM σ) μ
    (fun h0 => by rw [avgM_univ_one hN σ (hS.neutral h0), hμ1])
    (fun h2 => ⟨avgM_atomless σ (hS.atom h2), atomless_of_le_vol hd hc hμ⟩) (G_int_sum hN hl hS hc hμ)
  have hQi := fun i => LE_self hd hl (fun h2 => hS.atom h2 i) (hS.Gii i)
  set QH : Torus d → ℝ := fun x => ∑ j, ((∫ z, SliceAux.sgc j l (x - z) ∂(avgM σ)) -
    ∫ z, SliceAux.sgc j l (x - z) ∂μ) ^ 2 with hQH
  set Qi : Fin N → Torus d → ℝ := fun i x => ∑ j, (∫ z, SliceAux.sgc j l (x - z) ∂(σ i)) ^ 2 with hQi'
  have hQH0 : ∀ x, 0 ≤ QH x := fun x => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hQi0 : ∀ i x, 0 ≤ Qi i x := fun i x => Finset.sum_nonneg fun j _ => sq_nonneg _
  -- the good set
  have hgood : ∀ᵐ x ∂(volume : Measure (Torus d)), ∀ i j, Integrable (fun z => SliceAux.sgc j l (x - z)) (σ i) := by
    rw [ae_all_iff]; intro i; rw [ae_all_iff]; intro j
    have hsgm : Measurable (SliceAux.sgc j l : Torus d → ℝ) :=
      (SliceAux.measurable_sgc j).comp (measurable_const.prodMk measurable_id)
    have h := integrable_conv_swap hsgm (RoughKernel.integrable_sgc (d := d) j hl) (σ i)
    exact h.prod_left_ae
  -- the pointwise bound
  have hpt : ∀ᵐ x ∂(volume : Measure (Torus d)), ∀ i,
      (if KernelGrad.tdist x (X i) < r i then ‖fieldF l X μ i x‖ ^ 2 else 0) ≤
        2 * QH x + 2 * (1 / (N : ℝ)) ^ 2 * Qi i x := by
    filter_upwards [hgood] with x hx i
    by_cases hxi : KernelGrad.tdist x (X i) < r i
    · rw [if_pos hxi, EuclideanSpace.norm_sq_eq]
      simp only [Real.norm_eq_abs, sq_abs]
      have key : ∀ j, fieldF l X μ i x j = ((∫ z, SliceAux.sgc j l (x - z) ∂(avgM σ)) -
          ∫ z, SliceAux.sgc j l (x - z) ∂μ) - (1 / (N : ℝ)) * ∫ z, SliceAux.sgc j l (x - z) ∂(σ i) := fun j => by
        rw [field_ident hN hl hS hη hsep hc hμ i hxi (hx i) j]; ring
      simp_rw [key]
      rw [hQH, hQi', Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun j _ => ?_
      nlinarith [sq_nonneg ((∫ z, SliceAux.sgc j l (x - z) ∂(avgM σ)) - ∫ z, SliceAux.sgc j l (x - z) ∂μ +
        (1 / (N : ℝ)) * ∫ z, SliceAux.sgc j l (x - z) ∂(σ i))]
    · rw [if_neg hxi]
      have := hQH0 x; have := hQi0 i x
      positivity
  have hmeas : ∀ i, Measurable (fun x => if KernelGrad.tdist x (X i) < r i then ‖fieldF l X μ i x‖ ^ 2 else 0) := by
    intro i
    have hB : MeasurableSet {x : Torus d | KernelGrad.tdist x (X i) < r i} := by
      have : Measurable fun x : Torus d => KernelGrad.tdist x (X i) := by
        have h := EnergyAux.measurable_tdist_zero (d := d)
        have e1 : (fun x : Torus d => KernelGrad.tdist x (X i)) = fun x => KernelGrad.tdist (x - X i) 0 := by
          funext x; exact EnergyAux.tdist_def x (X i)
        rw [e1]; exact h.comp (measurable_id.sub_const _)
      exact measurableSet_lt this measurable_const
    exact Measurable.ite hB ((measurable_fieldF l X μ i).norm.pow_const 2) measurable_const
  have hbd : ∀ i, Integrable (fun x => 2 * QH x + 2 * (1 / (N : ℝ)) ^ 2 * Qi i x) volume := fun i =>
    (hQHi.const_mul 2).add ((hQi i).1.const_mul _)
  have hint : ∀ i, Integrable (fun x => if KernelGrad.tdist x (X i) < r i then ‖fieldF l X μ i x‖ ^ 2 else 0) volume := by
    intro i
    refine Integrable.mono' (hbd i) (hmeas i).aestronglyMeasurable ?_
    filter_upwards [hpt] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by split_ifs <;> positivity)]
    exact hx i
  refine ⟨hint, ?_⟩
  rw [← integral_finset_sum _ (fun i _ => hint i)]
  -- pointwise bound for the sum (disjointness)
  have hsum : ∀ᵐ x ∂(volume : Measure (Torus d)),
      ∑ i, (if KernelGrad.tdist x (X i) < r i then ‖fieldF l X μ i x‖ ^ 2 else 0) ≤
        2 * QH x + 2 * (1 / (N : ℝ)) ^ 2 * ∑ i, Qi i x := by
    filter_upwards [hpt] with x hx
    by_cases hex : ∃ i0, KernelGrad.tdist x (X i0) < r i0
    · obtain ⟨i0, hi0⟩ := hex
      rw [Finset.sum_eq_single i0]
      · refine (hx i0).trans ?_
        have : Qi i0 x ≤ ∑ i, Qi i x := Finset.single_le_sum (fun i _ => hQi0 i x) (Finset.mem_univ i0)
        have h2 : 0 ≤ (1 / (N : ℝ)) ^ 2 := by positivity
        nlinarith
      · intro k _ hk
        rw [if_neg]
        intro hk'
        have := tdist_tri (X i0) x (X k)
        rw [tdist_symm' (X i0) x] at this
        have := hsep i0 k (Ne.symm hk)
        linarith
      · intro h; exact absurd (Finset.mem_univ i0) h
    · push Not at hex
      simp only [if_neg (not_lt.mpr (hex _)), Finset.sum_const_zero]
      have h2 : 0 ≤ ∑ i, Qi i x := Finset.sum_nonneg fun i _ => hQi0 i x
      have := hQH0 x
      positivity
  have hI2 : Integrable (fun x => 2 * QH x + 2 * (1 / (N : ℝ)) ^ 2 * ∑ i, Qi i x) volume := by
    refine (hQHi.const_mul 2).add ?_
    have : Integrable (fun x => ∑ i, Qi i x) volume := integrable_finset_sum _ fun i _ => (hQi i).1
    exact this.const_mul _
  calc ∫ x, ∑ i, (if KernelGrad.tdist x (X i) < r i then ‖fieldF l X μ i x‖ ^ 2 else 0)
      ≤ ∫ x, (2 * QH x + 2 * (1 / (N : ℝ)) ^ 2 * ∑ i, Qi i x) :=
        integral_mono_ae (integrable_finset_sum _ fun i _ => hint i) hI2 hsum
    _ = 2 * (∫ x, QH x) + 2 * (1 / (N : ℝ)) ^ 2 * ∑ i, ∫ x, Qi i x := by
        rw [integral_add (hQHi.const_mul 2) (by
          have : Integrable (fun x => ∑ i, Qi i x) volume := integrable_finset_sum _ fun i _ => (hQi i).1
          exact this.const_mul _), integral_const_mul, integral_const_mul,
          integral_finset_sum _ fun i _ => (hQi i).1]
    _ ≤ _ := by
        have h2 : 0 ≤ (1 / (N : ℝ)) ^ 2 := by positivity
        have : ∑ i, ∫ x, Qi i x ≤ ∑ i, quadForm (fun x y => sliceGfull d l (x - y)) (σ i)
            (ENNReal.ofReal ((σ i).real Set.univ) • (volume : Measure (Torus d))) :=
          Finset.sum_le_sum fun i _ => (hQi i).2
        have h3 := mul_le_mul_of_nonneg_left this h2
        have h4 : ∫ x, QH x ≤ quadForm (fun x y => sliceGfull d l (x - y)) (avgM σ) μ := hQHle
        nlinarith [h3, h4]

theorem field_ident_ann {N : ℕ} (hN : N ≠ 0) {l : ℝ} (hl : 0 ≤ l) {X : Fin N → Torus d} {η : Fin N → ℝ}
    {σ : Fin N → Measure (Torus d)} (hS : SliceCharges l X η σ) {r : Fin N → ℝ}
    (hη : ∀ i, η i ≤ r i / 2) (hr : ∀ i, 0 < r i)
    (hsep : ∀ i j, i ≠ j → r i + r j < KernelGrad.tdist (X i) (X j)) {μ : Measure (Torus d)} [IsFiniteMeasure μ]
    {c : ℝ≥0∞} (hc : c ≠ ⊤) (hμ : μ ≤ c • (volume : Measure (Torus d))) (i : Fin N) {x : Torus d}
    (hx : r i / 2 < KernelGrad.tdist x (X i) ∧ KernelGrad.tdist x (X i) < r i) (j : Fin d) :
    (∫ z, SliceAux.sgc j l (x - z) ∂(avgM σ)) - ∫ z, SliceAux.sgc j l (x - z) ∂μ =
      fieldF l X μ i x j + (1 / (N : ℝ)) * SliceAux.sgc j l (x - X i) := by
  haveI : ∀ i, IsFiniteMeasure (σ i) := hS.fin
  have hfar : ∀ k, η k < KernelGrad.tdist x (X k) := by
    intro k
    by_cases hk : k = i
    · subst hk; have := hη k; have := hr k; linarith [hx.1]
    · exact (le_trans (hη k) (by linarith [hr k])).trans_lt (tdist_far hsep hk hx.2) |>.trans_le le_rfl
  have hint : ∀ k, Integrable (fun z => SliceAux.sgc j l (x - z)) (σ k) := fun k =>
    (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).integrable_comp (integrable_sgv_sub_near hl hS (hfar k))
  rw [integral_avgM hN hint, fieldF_apply hl X hc hμ i x j, ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have : ∑ k ∈ Finset.univ.erase i, ∫ z, SliceAux.sgc j l (x - z) ∂(σ k) =
      ∑ k ∈ Finset.univ.erase i, SliceAux.sgc j l (x - X k) :=
    Finset.sum_congr rfl fun k _ => rep_comp hl hS (hfar k) j
  rw [this, rep_comp hl hS (hfar i) j]
  ring

theorem local_field_energy_ann (hd : 1 ≤ d) {N : ℕ} (hN : N ≠ 0) {l : ℝ} (hl : 0 ≤ l) {X : Fin N → Torus d}
    {η : Fin N → ℝ} {σ : Fin N → Measure (Torus d)} (hS : SliceCharges l X η σ) {r : Fin N → ℝ}
    (hη : ∀ i, η i ≤ r i / 2) (hr : ∀ i, 0 < r i)
    (hsep : ∀ i j, i ≠ j → r i + r j < KernelGrad.tdist (X i) (X j))
    {μ : Measure (Torus d)} [IsFiniteMeasure μ] {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hμ : μ ≤ c • (volume : Measure (Torus d))) (hμ1 : μ Set.univ = 1) :
    (∀ i, Integrable (fun x => if r i / 2 < KernelGrad.tdist x (X i) ∧ KernelGrad.tdist x (X i) < r i
        then ‖fieldF l X μ i x‖ ^ 2 else 0) volume) ∧
    ∑ i, ∫ x, (if r i / 2 < KernelGrad.tdist x (X i) ∧ KernelGrad.tdist x (X i) < r i
        then ‖fieldF l X μ i x‖ ^ 2 else 0) ≤
      2 * quadForm (fun x y => sliceGfull d l (x - y)) (avgM σ) μ +
        2 * (1 / (N : ℝ)) ^ 2 * ∑ i, ∫ x, (if r i / 2 < KernelGrad.tdist x (X i) ∧ KernelGrad.tdist x (X i) < r i
          then ‖SliceAux.sgv l (x - X i)‖ ^ 2 else 0) := by
  haveI : ∀ i, IsFiniteMeasure (σ i) := hS.fin
  haveI := isFiniteMeasure_avgM hN σ
  obtain ⟨hQHi, hQHle⟩ := LE_measures hd hl (avgM σ) μ
    (fun h0 => by rw [avgM_univ_one hN σ (hS.neutral h0), hμ1])
    (fun h2 => ⟨avgM_atomless σ (hS.atom h2), atomless_of_le_vol hd hc hμ⟩) (G_int_sum hN hl hS hc hμ)
  obtain ⟨QH, hQH⟩ : ∃ QH : Torus d → ℝ, QH = fun x => ∑ j, ((∫ z, SliceAux.sgc j l (x - z) ∂(avgM σ)) -
    ∫ z, SliceAux.sgc j l (x - z) ∂μ) ^ 2 := ⟨_, rfl⟩
  have hQH0 : ∀ x, 0 ≤ QH x := fun x => by rw [hQH]; exact Finset.sum_nonneg fun j _ => sq_nonneg _
  rw [← hQH] at hQHi hQHle
  have hAm : ∀ i, MeasurableSet {x : Torus d | r i / 2 < KernelGrad.tdist x (X i) ∧ KernelGrad.tdist x (X i) < r i} := by
    intro i
    have : Measurable fun x : Torus d => KernelGrad.tdist x (X i) := by
      have h := EnergyAux.measurable_tdist_zero (d := d)
      have e1 : (fun x : Torus d => KernelGrad.tdist x (X i)) = fun x => KernelGrad.tdist (x - X i) 0 := by
        funext x; exact EnergyAux.tdist_def x (X i)
      rw [e1]; exact h.comp (measurable_id.sub_const _)
    exact (measurableSet_lt measurable_const this).inter (measurableSet_lt this measurable_const)
  have hmeasW : ∀ i, Measurable (fun x => if r i / 2 < KernelGrad.tdist x (X i) ∧ KernelGrad.tdist x (X i) < r i
      then ‖SliceAux.sgv l (x - X i)‖ ^ 2 else 0) := fun i =>
    Measurable.ite (hAm i) (((measurable_sgv_l l).comp (measurable_id.sub_const _)).norm.pow_const 2) measurable_const
  have hintW : ∀ i, Integrable (fun x => if r i / 2 < KernelGrad.tdist x (X i) ∧ KernelGrad.tdist x (X i) < r i
      then ‖SliceAux.sgv l (x - X i)‖ ^ 2 else 0) volume := by
    intro i
    obtain ⟨B, hB⟩ := sgv_bdd_away (d := d) hl (half_pos (hr i))
    refine Integrable.mono' (integrable_const (B ^ 2)) (hmeasW i).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    split_ifs with hx
    · have h1 : ‖SliceAux.sgv l (x - X i)‖ ≤ B := by
        refine hB _ ?_
        rw [← EnergyAux.tdist_def]; exact hx.1.le
      rw [abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    · simp only [abs_zero]; positivity
  -- pointwise bound
  have hpt : ∀ x, ∀ i, (if r i / 2 < KernelGrad.tdist x (X i) ∧ KernelGrad.tdist x (X i) < r i
        then ‖fieldF l X μ i x‖ ^ 2 else 0) ≤
      2 * QH x + 2 * (1 / (N : ℝ)) ^ 2 * (if r i / 2 < KernelGrad.tdist x (X i) ∧ KernelGrad.tdist x (X i) < r i
        then ‖SliceAux.sgv l (x - X i)‖ ^ 2 else 0) := by
    intro x i
    by_cases hxi : r i / 2 < KernelGrad.tdist x (X i) ∧ KernelGrad.tdist x (X i) < r i
    · rw [if_pos hxi, if_pos hxi, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
      simp only [Real.norm_eq_abs, sq_abs]
      have key : ∀ j, fieldF l X μ i x j = ((∫ z, SliceAux.sgc j l (x - z) ∂(avgM σ)) -
          ∫ z, SliceAux.sgc j l (x - z) ∂μ) - (1 / (N : ℝ)) * SliceAux.sgc j l (x - X i) := fun j => by
        rw [field_ident_ann hN hl hS hη hr hsep hc hμ i hxi j]; ring
      simp_rw [key, sgv_apply]
      rw [hQH, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun j _ => ?_
      nlinarith [sq_nonneg ((∫ z, SliceAux.sgc j l (x - z) ∂(avgM σ)) - ∫ z, SliceAux.sgc j l (x - z) ∂μ +
        (1 / (N : ℝ)) * SliceAux.sgc j l (x - X i))]
    · rw [if_neg hxi, if_neg hxi]
      have := hQH0 x
      positivity
  have hmeas : ∀ i, Measurable (fun x => if r i / 2 < KernelGrad.tdist x (X i) ∧ KernelGrad.tdist x (X i) < r i
      then ‖fieldF l X μ i x‖ ^ 2 else 0) := fun i =>
    Measurable.ite (hAm i) ((measurable_fieldF l X μ i).norm.pow_const 2) measurable_const
  have hbd : ∀ i, Integrable (fun x => 2 * QH x + 2 * (1 / (N : ℝ)) ^ 2 * (if r i / 2 < KernelGrad.tdist x (X i) ∧
      KernelGrad.tdist x (X i) < r i then ‖SliceAux.sgv l (x - X i)‖ ^ 2 else 0)) volume := fun i =>
    (hQHi.const_mul 2).add ((hintW i).const_mul _)
  have hint : ∀ i, Integrable (fun x => if r i / 2 < KernelGrad.tdist x (X i) ∧ KernelGrad.tdist x (X i) < r i
      then ‖fieldF l X μ i x‖ ^ 2 else 0) volume := by
    intro i
    refine Integrable.mono' (hbd i) (hmeas i).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by split_ifs <;> positivity)]
    exact hpt x i
  refine ⟨hint, ?_⟩
  rw [← integral_finsetSum _ (fun i _ => hint i)]
  have hsum : ∀ x : Torus d,
      ∑ i, (if r i / 2 < KernelGrad.tdist x (X i) ∧ KernelGrad.tdist x (X i) < r i then ‖fieldF l X μ i x‖ ^ 2 else 0) ≤
        2 * QH x + 2 * (1 / (N : ℝ)) ^ 2 * ∑ i, (if r i / 2 < KernelGrad.tdist x (X i) ∧
          KernelGrad.tdist x (X i) < r i then ‖SliceAux.sgv l (x - X i)‖ ^ 2 else 0) := by
    intro x
    have hW0 : ∀ i, 0 ≤ (if r i / 2 < KernelGrad.tdist x (X i) ∧ KernelGrad.tdist x (X i) < r i
        then ‖SliceAux.sgv l (x - X i)‖ ^ 2 else 0) := fun i => by split_ifs <;> positivity
    by_cases hex : ∃ i0, r i0 / 2 < KernelGrad.tdist x (X i0) ∧ KernelGrad.tdist x (X i0) < r i0
    · obtain ⟨i0, hi0⟩ := hex
      rw [Finset.sum_eq_single i0]
      · refine (hpt x i0).trans ?_
        have : (if r i0 / 2 < KernelGrad.tdist x (X i0) ∧ KernelGrad.tdist x (X i0) < r i0
            then ‖SliceAux.sgv l (x - X i0)‖ ^ 2 else 0) ≤ ∑ i, (if r i / 2 < KernelGrad.tdist x (X i) ∧
              KernelGrad.tdist x (X i) < r i then ‖SliceAux.sgv l (x - X i)‖ ^ 2 else 0) :=
          Finset.single_le_sum (fun i _ => hW0 i) (Finset.mem_univ i0)
        have h2 : 0 ≤ (1 / (N : ℝ)) ^ 2 := by positivity
        nlinarith
      · intro k _ hk
        rw [if_neg]
        intro hk'
        have := tdist_tri (X i0) x (X k)
        rw [tdist_symm' (X i0) x] at this
        have := hsep i0 k (Ne.symm hk)
        linarith [hi0.2, hk'.2]
      · intro h; exact absurd (Finset.mem_univ i0) h
    · push Not at hex
      have h0 : ∀ i, (if r i / 2 < KernelGrad.tdist x (X i) ∧ KernelGrad.tdist x (X i) < r i
          then ‖fieldF l X μ i x‖ ^ 2 else 0) = 0 := fun i => by
        rw [if_neg]; intro h; exact absurd (hex i h.1) (not_le.mpr h.2)
      simp only [h0, Finset.sum_const_zero]
      have h2 : 0 ≤ ∑ i, (if r i / 2 < KernelGrad.tdist x (X i) ∧ KernelGrad.tdist x (X i) < r i
          then ‖SliceAux.sgv l (x - X i)‖ ^ 2 else 0) := Finset.sum_nonneg fun i _ => hW0 i
      have := hQH0 x
      positivity
  have hI2 : Integrable (fun x => 2 * QH x + 2 * (1 / (N : ℝ)) ^ 2 * ∑ i, (if r i / 2 < KernelGrad.tdist x (X i) ∧
      KernelGrad.tdist x (X i) < r i then ‖SliceAux.sgv l (x - X i)‖ ^ 2 else 0)) volume := by
    refine (hQHi.const_mul 2).add ?_
    exact (integrable_finsetSum _ fun i _ => hintW i).const_mul _
  calc ∫ x, ∑ i, (if r i / 2 < KernelGrad.tdist x (X i) ∧ KernelGrad.tdist x (X i) < r i
        then ‖fieldF l X μ i x‖ ^ 2 else 0)
      ≤ ∫ x, (2 * QH x + 2 * (1 / (N : ℝ)) ^ 2 * ∑ i, (if r i / 2 < KernelGrad.tdist x (X i) ∧
          KernelGrad.tdist x (X i) < r i then ‖SliceAux.sgv l (x - X i)‖ ^ 2 else 0)) :=
        integral_mono (integrable_finsetSum _ fun i _ => hint i) hI2 hsum
    _ = 2 * (∫ x, QH x) + 2 * (1 / (N : ℝ)) ^ 2 * ∑ i, ∫ x, (if r i / 2 < KernelGrad.tdist x (X i) ∧
          KernelGrad.tdist x (X i) < r i then ‖SliceAux.sgv l (x - X i)‖ ^ 2 else 0) := by
        rw [integral_add (hQHi.const_mul 2) ((integrable_finsetSum _ fun i _ => hintW i).const_mul _),
          integral_const_mul, integral_const_mul, integral_finsetSum _ fun i _ => hintW i]
    _ ≤ _ := by
        have h2 : 0 ≤ (1 / (N : ℝ)) ^ 2 := by positivity
        nlinarith [hQHle]

end HRS.Commutator.Renorm
