import HRS.Energy.Commutator.RenormStj0IntE

/-!
# Route S, packet STJ: the local field energy with the self field restricted to the ball (`s = 0`)
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS.Commutator.Renorm

namespace HRS.Commutator.Stj

variable {d : ℕ}

theorem measurable_selfField {l : ℝ} (j : Fin d) (σ : Measure (Torus d)) [IsFiniteMeasure σ] :
    Measurable fun x : Torus d => ∫ z, SliceAux.sgc j l (x - z) ∂σ := by
  have : StronglyMeasurable (fun p : Torus d × Torus d => SliceAux.sgc j l (p.1 - p.2)) :=
    (((SliceAux.measurable_sgc j).comp (measurable_const.prodMk (measurable_fst.sub measurable_snd)))).stronglyMeasurable
  exact (this.integral_prod_right' (ν := σ)).measurable

theorem local_field_energy_loc (hd : 1 ≤ d) {N : ℕ} (hN : N ≠ 0) {l : ℝ} (hl : 0 ≤ l) {X : Fin N → Torus d}
    {η : Fin N → ℝ} {σ : Fin N → Measure (Torus d)} (hS : SliceCharges l X η σ) {r : Fin N → ℝ}
    (hη : ∀ i, η i ≤ r i) (hsep : ∀ i j, i ≠ j → r i + r j < KernelGrad.tdist (X i) (X j))
    {μ : Measure (Torus d)} [IsFiniteMeasure μ] {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hμ : μ ≤ c • (volume : Measure (Torus d))) (hμ1 : μ Set.univ = 1) :
    (∀ i, Integrable (fun x => if KernelGrad.tdist x (X i) < r i then ‖fieldF l X μ i x‖ ^ 2 else 0) volume) ∧
    ∑ i, ∫ x, (if KernelGrad.tdist x (X i) < r i then ‖fieldF l X μ i x‖ ^ 2 else 0) ≤
      2 * quadForm (fun x y => sliceGfull d l (x - y)) (avgM σ) μ +
        2 * (1 / (N : ℝ)) ^ 2 * ∑ i, ∫ x, (if KernelGrad.tdist x (X i) < r i then
          ∑ j, (∫ z, SliceAux.sgc j l (x - z) ∂(σ i)) ^ 2 else 0) := by
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
  have hQim : ∀ i, Measurable (Qi i) := fun i =>
    Finset.measurable_sum _ fun j _ => (measurable_selfField (l := l) j (σ i)).pow_const 2
  have hBm : ∀ i, MeasurableSet {x : Torus d | KernelGrad.tdist x (X i) < r i} := fun i =>
    measurableSet_lt (measurable_tdist_to (X i)) measurable_const
  set Qi' : Fin N → Torus d → ℝ := fun i x => if KernelGrad.tdist x (X i) < r i then Qi i x else 0 with hQi''
  have hQi'0 : ∀ i x, 0 ≤ Qi' i x := fun i x => by simp only [hQi'']; split_ifs <;> [exact hQi0 i x; exact le_rfl]
  have hQi'm : ∀ i, Measurable (Qi' i) := fun i => Measurable.ite (hBm i) (hQim i) measurable_const
  have hQi'int : ∀ i, Integrable (Qi' i) volume := fun i => by
    refine Integrable.mono' (hQi i).1 (hQi'm i).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hQi'0 i x)]
    simp only [hQi'']; split_ifs
    · exact le_rfl
    · exact hQi0 i x
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
        2 * QH x + 2 * (1 / (N : ℝ)) ^ 2 * Qi' i x := by
    filter_upwards [hgood] with x hx i
    by_cases hxi : KernelGrad.tdist x (X i) < r i
    · rw [if_pos hxi]
      simp only [hQi'', if_pos hxi]
      rw [EuclideanSpace.norm_sq_eq]
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
      have := hQH0 x; have := hQi'0 i x
      positivity
  have hmeas : ∀ i, Measurable (fun x => if KernelGrad.tdist x (X i) < r i then ‖fieldF l X μ i x‖ ^ 2 else 0) := by
    intro i
    exact Measurable.ite (hBm i) ((measurable_fieldF l X μ i).norm.pow_const 2) measurable_const
  have hbd : ∀ i, Integrable (fun x => 2 * QH x + 2 * (1 / (N : ℝ)) ^ 2 * Qi' i x) volume := fun i =>
    (hQHi.const_mul 2).add ((hQi'int i).const_mul _)
  have hint : ∀ i, Integrable (fun x => if KernelGrad.tdist x (X i) < r i then ‖fieldF l X μ i x‖ ^ 2 else 0) volume := by
    intro i
    refine Integrable.mono' (hbd i) (hmeas i).aestronglyMeasurable ?_
    filter_upwards [hpt] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by split_ifs <;> positivity)]
    exact hx i
  refine ⟨hint, ?_⟩
  rw [← integral_finsetSum _ (fun i _ => hint i)]
  have hsum : ∀ᵐ x ∂(volume : Measure (Torus d)),
      ∑ i, (if KernelGrad.tdist x (X i) < r i then ‖fieldF l X μ i x‖ ^ 2 else 0) ≤
        2 * QH x + 2 * (1 / (N : ℝ)) ^ 2 * ∑ i, Qi' i x := by
    filter_upwards [hpt] with x hx
    by_cases hex : ∃ i0, KernelGrad.tdist x (X i0) < r i0
    · obtain ⟨i0, hi0⟩ := hex
      rw [Finset.sum_eq_single i0]
      · refine (hx i0).trans ?_
        have : Qi' i0 x ≤ ∑ i, Qi' i x := Finset.single_le_sum (fun i _ => hQi'0 i x) (Finset.mem_univ i0)
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
      have h2 : 0 ≤ ∑ i, Qi' i x := Finset.sum_nonneg fun i _ => hQi'0 i x
      have := hQH0 x
      positivity
  have hI2 : Integrable (fun x => 2 * QH x + 2 * (1 / (N : ℝ)) ^ 2 * ∑ i, Qi' i x) volume := by
    refine (hQHi.const_mul 2).add ?_
    have : Integrable (fun x => ∑ i, Qi' i x) volume := integrable_finsetSum _ fun i _ => hQi'int i
    exact this.const_mul _
  calc ∫ x, ∑ i, (if KernelGrad.tdist x (X i) < r i then ‖fieldF l X μ i x‖ ^ 2 else 0)
      ≤ ∫ x, (2 * QH x + 2 * (1 / (N : ℝ)) ^ 2 * ∑ i, Qi' i x) :=
        integral_mono_ae (integrable_finsetSum _ fun i _ => hint i) hI2 hsum
    _ = 2 * (∫ x, QH x) + 2 * (1 / (N : ℝ)) ^ 2 * ∑ i, ∫ x, Qi' i x := by
        rw [integral_add (hQHi.const_mul 2) (by
          have : Integrable (fun x => ∑ i, Qi' i x) volume := integrable_finsetSum _ fun i _ => hQi'int i
          exact this.const_mul _), integral_const_mul, integral_const_mul,
          integral_finsetSum _ fun i _ => hQi'int i]
    _ ≤ _ := by
        have h2 : 0 ≤ (1 / (N : ℝ)) ^ 2 := by positivity
        have h3 : 2 * (∫ x, QH x) ≤ 2 * quadForm (fun x y => sliceGfull d l (x - y)) (avgM σ) μ := by
          linarith [hQHle]
        have : ∀ i, ∫ x, Qi' i x = ∫ x, (if KernelGrad.tdist x (X i) < r i then
            ∑ j, (∫ z, SliceAux.sgc j l (x - z) ∂(σ i)) ^ 2 else 0) := fun i => rfl
        simp_rw [this]
        linarith

theorem ae_not_atom (hd : 1 ≤ d) (σ : Measure (Torus d)) [IsFiniteMeasure σ] :
    ∀ᵐ x ∂(volume : Measure (Torus d)), σ {x} = 0 := by
  have hc : Set.Countable {x : Torus d | 0 < σ {x}} :=
    Measure.countable_meas_pos_of_disjoint_iUnion (μ := σ) (As := fun x : Torus d => ({x} : Set (Torus d)))
      (fun x => measurableSet_singleton x) (fun x y hxy => by simpa using hxy)
  rw [ae_iff]
  have : {x : Torus d | ¬ σ {x} = 0} = {x : Torus d | 0 < σ {x}} := by
    ext x; simp [pos_iff_ne_zero]
  rw [this]
  have h2 : (volume : Measure (Torus d)) (⋃ x ∈ {x : Torus d | 0 < σ {x}}, ({x} : Set (Torus d))) = 0 :=
    (measure_biUnion_null_iff hc).2 fun x _ => volume_singleton_torus hd x
  rwa [Set.biUnion_of_singleton] at h2

theorem selfField_le_d1 :
    ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ {l : ℝ}, 0 ≤ l → ∀ (σ : Measure (Torus 1)) [IsFiniteMeasure σ] (x : Torus 1), σ {x} = 0 →
      ∑ j : Fin 1, (∫ z, SliceAux.sgc j l (x - z) ∂σ) ^ 2 ≤ (2 * Kc * σ.real Set.univ) ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := sgc_unif_bound (d := 1) le_rfl
  refine ⟨K, hK0, fun {l} hl σ _ x hx => ?_⟩
  have hae : ∀ᵐ z ∂σ, z ≠ x :=
    (measure_eq_zero_iff_ae_notMem.mp hx).mono fun z hz => by simpa using hz
  have hbound : ∀ᵐ z ∂σ, ‖SliceAux.sgc 0 l (x - z)‖ ≤ 2 * K := by
    filter_upwards [hae] with z hz
    have hxz : x - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
    have h := hK 0 l hl (x - z) hxz
    rw [Real.norm_eq_abs]
    refine h.trans (le_of_eq ?_)
    simp only [Nat.cast_one, sub_self, Real.rpow_zero]
    ring
  have h1 := norm_integral_le_of_norm_le_const hbound
  rw [Real.norm_eq_abs] at h1
  simp only [Fin.sum_univ_one]
  have : (∫ z, SliceAux.sgc 0 l (x - z) ∂σ) ^ 2 = |∫ z, SliceAux.sgc 0 l (x - z) ∂σ| ^ 2 := (sq_abs _).symm
  rw [this]
  exact pow_le_pow_left₀ (abs_nonneg _) h1 2

theorem Qi_int_le_d1 :
    ∃ Kc : ℝ, 0 ≤ Kc ∧ ∀ {l : ℝ}, 0 ≤ l → ∀ (σ : Measure (Torus 1)) [IsFiniteMeasure σ] (a : Torus 1) {r : ℝ},
      0 < r → r ≤ 1 / 2 →
      ∫ x, (if KernelGrad.tdist x a < r then ∑ j : Fin 1, (∫ z, SliceAux.sgc j l (x - z) ∂σ) ^ 2 else 0) ≤
        (2 * Kc * σ.real Set.univ) ^ 2 * (r * (volume : Measure (Euc 1)).real (Metric.ball 0 1)) := by
  obtain ⟨Kc, hKc0, hKc⟩ := selfField_le_d1
  refine ⟨Kc, hKc0, fun {l} hl σ _ a r hr hr2 => ?_⟩
  set C : ℝ := (2 * Kc * σ.real Set.univ) ^ 2 with hC
  have hC0 : 0 ≤ C := sq_nonneg _
  have hBm : MeasurableSet {x : Torus 1 | KernelGrad.tdist x a < r} :=
    measurableSet_lt (measurable_tdist_to a) measurable_const
  have hba := ball_ratio (d := 1) le_rfl hr hr2 a
  have hg : ∫ x : Torus 1, (if KernelGrad.tdist x a < r then C else 0) =
      C * (r * (volume : Measure (Euc 1)).real (Metric.ball 0 1)) := by
    have e1 : ∀ x : Torus 1, (if KernelGrad.tdist x a < r then C else 0) =
        C * (if KernelGrad.tdist x a < r then (1 : ℝ) else 0) := fun x => by split_ifs <;> simp
    simp_rw [e1]
    rw [integral_const_mul]
    congr 1
    have h1 : ∫ x : Torus 1, (if KernelGrad.tdist x a < r then (1 : ℝ) else 0) =
        (∫⁻ x : Torus 1, (if KernelGrad.tdist x a < r then (1 : ℝ≥0∞) else 0)).toReal := by
      rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => by show (0 : ℝ) ≤ _; split_ifs <;> simp)
        (Measurable.ite hBm measurable_const measurable_const).aestronglyMeasurable]
      congr 1
      refine lintegral_congr fun x => ?_
      split_ifs <;> simp
    rw [h1, hba, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
    simp [Measure.real]
  have hgi : Integrable (fun x : Torus 1 => if KernelGrad.tdist x a < r then C else 0) volume := by
    refine (integrable_const C).mono' (Measurable.ite hBm measurable_const measurable_const).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    split_ifs
    · rw [abs_of_nonneg hC0]
    · simpa using hC0
  rw [← hg]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => ?_) hgi ?_
  · dsimp only; split_ifs
    · exact Finset.sum_nonneg fun j _ => sq_nonneg _
    · exact le_rfl
  · filter_upwards [ae_not_atom (le_refl 1) σ] with x hx
    split_ifs
    · exact hKc hl σ x hx
    · exact le_rfl

theorem sumY0_le (s : ℝ) {N : ℕ} (hN : N ≠ 0) {X : Config 1 N} {r : Fin N → ℝ}
    (hr0 : ∀ i, 0 < r i) (hr8 : ∀ i, r i ≤ 1 / 8)
    (hsep : ∀ i j, i ≠ j → r i + r j < KernelGrad.tdist (X i) (X j))
    {μ : Measure (Torus 1)} [IsFiniteMeasure μ] {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hμ : μ ≤ ENNReal.ofReal Λ • (volume : Measure (Torus 1))) (hμ1 : μ Set.univ = 1) {Kc : ℝ}
    (hKc0 : 0 ≤ Kc)
    (hKc : ∀ {l : ℝ}, 0 ≤ l → ∀ (σ : Measure (Torus 1)) [IsFiniteMeasure σ] (a : Torus 1) {r : ℝ},
      0 < r → r ≤ 1 / 2 →
      ∫ x, (if KernelGrad.tdist x a < r then ∑ j : Fin 1, (∫ z, SliceAux.sgc j l (x - z) ∂σ) ^ 2 else 0) ≤
        (2 * Kc * σ.real Set.univ) ^ 2 * (r * (volume : Measure (Euc 1)).real (Metric.ball 0 1))) :
    ∑ i, Yloc 1 s (r i) (X i) (fun l => fieldF l X μ i) ≤
      ∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp 1 s)) *
        ENNReal.ofReal (2 * Ebar0 X (fun i => r i / 4) μ Λ l + 2 * (1 / (N : ℝ)) ^ 2 *
          ∑ i, 4 * Kc ^ 2 * mass 1 l (r i / 4) * (r i * (volume : Measure (Euc 1)).real (Metric.ball 0 1))) := by
  set η0 : Fin N → ℝ := fun i => r i / 4 with hη0def
  have hη0 : ∀ i, 0 < η0 i ∧ η0 i ≤ 1 / 8 := fun i => ⟨by have := hr0 i; simp only [hη0def]; positivity,
    by have := hr8 i; simp only [hη0def]; linarith⟩
  have hη02 : ∀ i, 0 < η0 i ∧ η0 i < 1 / 2 := fun i => ⟨(hη0 i).1, by linarith [(hη0 i).2]⟩
  have hdisj0 : ∀ i j, i ≠ j → η0 i + η0 j < KernelGrad.tdist (X i) (X j) := fun i j hij => by
    have := hsep i j hij; have := hr0 i; have := hr0 j; simp only [hη0def]; linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hc : ENNReal.ofReal Λ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmeas : ∀ i, Measurable fun l : ℝ => ENNReal.ofReal (l ^ (-bexp 1 s)) * ∫⁻ x : Torus 1,
      (if KernelGrad.tdist x (X i) < r i then ENNReal.ofReal (‖fieldF l X μ i x‖ ^ 2) else 0) := fun i =>
    (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)).mul (measurable_Wloc X μ i (r i))
  have hpt : ∀ l : ℝ, 0 < l → ∑ i, ∫⁻ x : Torus 1,
      (if KernelGrad.tdist x (X i) < r i then ENNReal.ofReal (‖fieldF l X μ i x‖ ^ 2) else 0) ≤
      ENNReal.ofReal (2 * Ebar0 X η0 μ Λ l + 2 * (1 / (N : ℝ)) ^ 2 *
          ∑ i, 4 * Kc ^ 2 * mass 1 l (r i / 4) * (r i * (volume : Measure (Euc 1)).real (Metric.ball 0 1))) := by
    intro l hl
    have hS := sliceCharges_stj (d := 1) le_rfl hl hη02 hdisj0
    obtain ⟨hint, hsum⟩ := local_field_energy_loc (d := 1) le_rfl hN hl.le hS (r := r)
      (fun i => by simp only [hη0def]; linarith [hr0 i]) hsep hc hμ hμ1
    have h1 : ∀ i, ∫⁻ x : Torus 1,
        (if KernelGrad.tdist x (X i) < r i then ENNReal.ofReal (‖fieldF l X μ i x‖ ^ 2) else 0) =
        ENNReal.ofReal (∫ x : Torus 1, (if KernelGrad.tdist x (X i) < r i then ‖fieldF l X μ i x‖ ^ 2 else 0)) := by
      intro i
      rw [ofReal_integral_eq_lintegral_ofReal (hint i)]
      · refine lintegral_congr fun x => ?_
        by_cases hx : KernelGrad.tdist x (X i) < r i
        · simp only [if_pos hx]
        · simp only [if_neg hx, ENNReal.ofReal_zero]
      · exact Filter.Eventually.of_forall fun x => by dsimp only; split_ifs <;> positivity
    simp_rw [h1]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => integral_nonneg fun x => by dsimp only; split_ifs <;> positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    refine hsum.trans ?_
    have hE := energy_le_Ebar0 hN hl hη0 hdisj0 hΛ0 hμ hμ1
    have hQ : ∀ i, ∫ x, (if KernelGrad.tdist x (X i) < r i then
        ∑ j, (∫ z, SliceAux.sgc j l (x - z) ∂(chS 1 l (η0 i) (X i))) ^ 2 else 0) ≤
        4 * Kc ^ 2 * mass 1 l (r i / 4) * (r i * (volume : Measure (Euc 1)).real (Metric.ball 0 1)) := by
      intro i
      haveI := isFiniteMeasure_chS (d := 1) le_rfl hl (hη02 i).1 (hη02 i).2 (X i)
      have h := hKc hl.le (chS 1 l (η0 i) (X i)) (X i) (hr0 i) (by linarith [hr8 i])
      rw [chS_real_univ] at h
      refine h.trans ?_
      have hm0 : 0 ≤ mass 1 l (r i / 4) := measureReal_nonneg
      have hm1 : mass 1 l (r i / 4) ≤ 1 := mass_le_one le_rfl hl (hη02 i).1 (hη02 i).2
      have hm2 : mass 1 l (r i / 4) ^ 2 ≤ mass 1 l (r i / 4) := by nlinarith
      have hω : 0 ≤ (volume : Measure (Euc 1)).real (Metric.ball 0 1) := measureReal_nonneg
      have : (2 * Kc * mass 1 l (r i / 4)) ^ 2 = 4 * Kc ^ 2 * mass 1 l (r i / 4) ^ 2 := by ring
      rw [this]
      have hr' := (hr0 i).le
      calc 4 * Kc ^ 2 * mass 1 l (r i / 4) ^ 2 * (r i * (volume : Measure (Euc 1)).real (Metric.ball 0 1))
          ≤ 4 * Kc ^ 2 * mass 1 l (r i / 4) * (r i * (volume : Measure (Euc 1)).real (Metric.ball 0 1)) := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm2 (by positivity)) (by positivity)
        _ = _ := rfl
    have hQs := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hQ i
    have h2 : 0 ≤ 2 * (1 / (N : ℝ)) ^ 2 := by positivity
    have h3 := mul_le_mul_of_nonneg_left hQs h2
    linarith [hE, h3]
  calc ∑ i, ∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal (l ^ (-bexp 1 s)) * ∫⁻ x : Torus 1,
        (if KernelGrad.tdist x (X i) < r i then ENNReal.ofReal (‖fieldF l X μ i x‖ ^ 2) else 0)
      = ∫⁻ l in Ioi (0 : ℝ), ∑ i, ENNReal.ofReal (l ^ (-bexp 1 s)) * ∫⁻ x : Torus 1,
        (if KernelGrad.tdist x (X i) < r i then ENNReal.ofReal (‖fieldF l X μ i x‖ ^ 2) else 0) :=
        (lintegral_finset_sum _ (fun i _ => hmeas i)).symm
    _ ≤ _ := by
        refine setLIntegral_mono' measurableSet_Ioi fun l hl => ?_
        rw [← Finset.mul_sum]
        exact mul_le_mul' le_rfl (hpt l hl)

end HRS.Commutator.Stj
