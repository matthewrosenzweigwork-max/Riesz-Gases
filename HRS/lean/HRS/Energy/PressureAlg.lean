import HRS.Energy.Modulated

/-!
# HRS.Energy.PressureAlg — algebra of modulated energies of pair kernels (for Proposition 5.5)

* `RowOK μ k`: a measurable pair kernel with integrable rows of uniformly bounded `L¹(μ)` norm;
  the modulated energy is additive/homogeneous on such kernels.
* off-diagonal congruence of the energy for atomless `μ`;
* the energy of a finite positive-definite trigonometric kernel is `≥ -(1/2N) ∑_i G(x_i,x_i)`;
* the expectation `E[F_N^k] = -(2N)⁻¹ ∬ k dμ²` of a general pair kernel under `μ^{⊗N}` and its
  integrability (Jensen lower bounds of Proposition 5.5).
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HRS

variable {d : ℕ}

/-- A measurable pair kernel with integrable rows of uniformly bounded `L¹(μ)` norm. -/
structure RowOK (μ : Measure (Torus d)) (k : Torus d → Torus d → ℝ) : Prop where
  meas : Measurable (Function.uncurry k)
  int : ∀ x, Integrable (k x) μ
  bound : ∃ M : ℝ, ∀ x, ∫ y, |k x y| ∂μ ≤ M

namespace RowOK

variable {μ : Measure (Torus d)} {k k₁ k₂ : Torus d → Torus d → ℝ}

lemma measurable_row (h : RowOK μ k) (x : Torus d) : Measurable (k x) :=
  h.meas.comp (measurable_const.prodMk measurable_id)

lemma measurable_rowInt [SFinite μ] (h : RowOK μ k) : Measurable (fun x => ∫ y, k x y ∂μ) :=
  (h.meas.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable

lemma abs_rowInt_le [IsFiniteMeasure μ] (h : RowOK μ k) {M : ℝ} (hM : ∀ x, ∫ y, |k x y| ∂μ ≤ M)
    (x : Torus d) : |∫ y, k x y ∂μ| ≤ M := by
  refine (abs_integral_le_integral_abs).trans (hM x)

lemma integrable_rowInt [IsFiniteMeasure μ] (h : RowOK μ k) :
    Integrable (fun x => ∫ y, k x y ∂μ) μ := by
  obtain ⟨M, hM⟩ := h.bound
  exact Integrable.of_bound h.measurable_rowInt.aestronglyMeasurable M
    (Filter.Eventually.of_forall fun x => by simpa using h.abs_rowInt_le hM x)

lemma integrable_prod [IsFiniteMeasure μ] (h : RowOK μ k) :
    Integrable (Function.uncurry k) (μ.prod μ) := by
  obtain ⟨M, hM⟩ := h.bound
  refine (integrable_prod_iff h.meas.aestronglyMeasurable).2
    ⟨Filter.Eventually.of_forall h.int, ?_⟩
  have hm : Measurable (fun x => ∫ y, ‖k x y‖ ∂μ) :=
    (h.meas.norm.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable
  refine Integrable.of_bound hm.aestronglyMeasurable M (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
  simpa using hM x

lemma add [IsFiniteMeasure μ] (h₁ : RowOK μ k₁) (h₂ : RowOK μ k₂) :
    RowOK μ (fun x y => k₁ x y + k₂ x y) := by
  refine ⟨?_, fun x => (h₁.int x).add (h₂.int x), ?_⟩
  · exact h₁.meas.add h₂.meas
  · obtain ⟨M₁, hM₁⟩ := h₁.bound
    obtain ⟨M₂, hM₂⟩ := h₂.bound
    refine ⟨M₁ + M₂, fun x => ?_⟩
    calc ∫ y, |k₁ x y + k₂ x y| ∂μ ≤ ∫ y, (|k₁ x y| + |k₂ x y|) ∂μ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => abs_nonneg _)
            ((h₁.int x).abs.add (h₂.int x).abs) (Filter.Eventually.of_forall fun y => abs_add_le _ _)
      _ = ∫ y, |k₁ x y| ∂μ + ∫ y, |k₂ x y| ∂μ := integral_add (h₁.int x).abs (h₂.int x).abs
      _ ≤ M₁ + M₂ := add_le_add (hM₁ x) (hM₂ x)

lemma smul [IsFiniteMeasure μ] (c : ℝ) (h : RowOK μ k) : RowOK μ (fun x y => c * k x y) := by
  refine ⟨measurable_const.mul h.meas, fun x => (h.int x).const_mul c, ?_⟩
  obtain ⟨M, hM⟩ := h.bound
  refine ⟨|c| * M, fun x => ?_⟩
  simp_rw [abs_mul]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (hM x) (abs_nonneg c)

lemma const [IsFiniteMeasure μ] (c : ℝ) : RowOK μ (fun _ _ => c) := by
  refine ⟨measurable_const, fun x => integrable_const c, ⟨|c| * (μ Set.univ).toReal, fun x => ?_⟩⟩
  simp [integral_const, Measure.real, mul_comm]

lemma neg [IsFiniteMeasure μ] (h : RowOK μ k) : RowOK μ (fun x y => -k x y) := by
  have := h.smul (-1)
  simpa using this

lemma sub [IsFiniteMeasure μ] (h₁ : RowOK μ k₁) (h₂ : RowOK μ k₂) :
    RowOK μ (fun x y => k₁ x y - k₂ x y) := by
  simpa [sub_eq_add_neg] using h₁.add h₂.neg

end RowOK

section Linear

variable {N : ℕ} {μ : Measure (Torus d)} [IsFiniteMeasure μ] {k₁ k₂ : Torus d → Torus d → ℝ}

theorem modulatedEnergy_add (h₁ : RowOK μ k₁) (h₂ : RowOK μ k₂) (X : Config d N) :
    modulatedEnergy (fun x y => k₁ x y + k₂ x y) X μ =
      modulatedEnergy k₁ X μ + modulatedEnergy k₂ X μ := by
  unfold modulatedEnergy
  have e1 : ∀ i, ∫ y, (k₁ (X i) y + k₂ (X i) y) ∂μ = ∫ y, k₁ (X i) y ∂μ + ∫ y, k₂ (X i) y ∂μ :=
    fun i => integral_add (h₁.int _) (h₂.int _)
  have e2 : ∫ x, ∫ y, (k₁ x y + k₂ x y) ∂μ ∂μ =
      ∫ x, ∫ y, k₁ x y ∂μ ∂μ + ∫ x, ∫ y, k₂ x y ∂μ ∂μ := by
    have : ∀ x, ∫ y, (k₁ x y + k₂ x y) ∂μ = ∫ y, k₁ x y ∂μ + ∫ y, k₂ x y ∂μ :=
      fun x => integral_add (h₁.int x) (h₂.int x)
    simp_rw [this]
    exact integral_add h₁.integrable_rowInt h₂.integrable_rowInt
  simp only [e1, e2, Finset.sum_add_distrib, mul_add]
  ring

theorem modulatedEnergy_smul (c : ℝ) (h : RowOK μ k₁) (X : Config d N) :
    modulatedEnergy (fun x y => c * k₁ x y) X μ = c * modulatedEnergy k₁ X μ := by
  unfold modulatedEnergy
  simp only [← Finset.mul_sum, integral_const_mul]
  ring

theorem modulatedEnergy_sub (h₁ : RowOK μ k₁) (h₂ : RowOK μ k₂) (X : Config d N) :
    modulatedEnergy (fun x y => k₁ x y - k₂ x y) X μ =
      modulatedEnergy k₁ X μ - modulatedEnergy k₂ X μ := by
  have := modulatedEnergy_add h₁ h₂.neg X
  have h3 := modulatedEnergy_smul (-1) h₂ X
  simp only [neg_mul, one_mul] at this h3
  simp only [sub_eq_add_neg]
  rw [this, h3]

end Linear

section Offdiag

variable {N : ℕ} {μ : Measure (Torus d)}

theorem modulatedEnergy_congr_offdiag (hμ : ∀ x, μ {x} = 0) {k₁ k₂ : Torus d → Torus d → ℝ}
    (hk : ∀ x y, x ≠ y → k₁ x y = k₂ x y) (X : Config d N) (hX : ∀ i j, i ≠ j → X i ≠ X j) :
    modulatedEnergy k₁ X μ = modulatedEnergy k₂ X μ := by
  have hae : ∀ x, ∀ᵐ y ∂μ, k₁ x y = k₂ x y := fun x => by
    have : ∀ᵐ y ∂μ, y ≠ x := by
      rw [ae_iff]; simpa using hμ x
    filter_upwards [this] with y hy using hk x y hy.symm
  unfold modulatedEnergy
  have e1 : ∀ i, ∫ y, k₁ (X i) y ∂μ = ∫ y, k₂ (X i) y ∂μ := fun i => integral_congr_ae (hae _)
  have e2 : ∀ x, ∫ y, k₁ x y ∂μ = ∫ y, k₂ x y ∂μ := fun x => integral_congr_ae (hae x)
  have e3 : ∀ i, ∑ j ∈ Finset.univ.erase i, k₁ (X i) (X j) = ∑ j ∈ Finset.univ.erase i, k₂ (X i) (X j) :=
    fun i => Finset.sum_congr rfl fun j hj =>
      hk _ _ (hX i j (Finset.ne_of_mem_erase hj).symm)
  simp only [e1, e2, e3]

theorem ae_injective_pi [IsProbabilityMeasure μ] (hμ : ∀ x, μ {x} = 0) :
    ∀ᵐ X ∂(Measure.pi fun _ : Fin N => μ), ∀ i j, i ≠ j → X i ≠ X j := by
  rw [ae_all_iff]; intro i
  rw [ae_all_iff]; intro j
  by_cases hij : i = j
  · exact Filter.Eventually.of_forall fun X h => absurd hij h
  · have hdiag : MeasurableSet {p : Torus d × Torus d | p.1 = p.2} :=
      measurableSet_eq_fun measurable_fst measurable_snd
    have hm : Measurable (fun X : Fin N → Torus d => (X i, X j)) :=
      (measurable_pi_apply i).prodMk (measurable_pi_apply j)
    have h0 : (μ.prod μ) {p : Torus d × Torus d | p.1 = p.2} = 0 := by
      rw [Measure.prod_apply hdiag]
      have : ∀ x : Torus d, μ (Prod.mk x ⁻¹' {p : Torus d × Torus d | p.1 = p.2}) = 0 := by
        intro x
        have : Prod.mk x ⁻¹' {p : Torus d × Torus d | p.1 = p.2} = {x} := by
          ext y; simp [eq_comm]
        rw [this]; exact hμ x
      simp only [this, lintegral_zero]
    have h1 : (Measure.pi fun _ : Fin N => μ) {X | X i = X j} = 0 := by
      have := Measure.map_apply hm hdiag (μ := Measure.pi fun _ : Fin N => μ)
      rw [pi_map_pair μ hij, h0] at this
      exact this.symm
    rw [ae_iff]
    have : {a : Fin N → Torus d | ¬(i ≠ j → a i ≠ a j)} = {X | X i = X j} := by
      ext X; simp [hij]
    rw [this]; exact h1

end Offdiag

section Expectation

variable {N : ℕ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {k : Torus d → Torus d → ℝ}

theorem integrable_modulatedEnergy_pair (hk : RowOK μ k) :
    Integrable (fun X : Config d N => modulatedEnergy k X μ) (Measure.pi fun _ : Fin N => μ) := by
  have hint : Integrable (fun p : Torus d × Torus d => k p.1 p.2) (μ.prod μ) := hk.integrable_prod
  have hpair : ∀ i j : Fin N, i ≠ j →
      Integrable (fun X : Config d N => k (X i) (X j)) (Measure.pi fun _ : Fin N => μ) :=
    fun i j hij => integrable_pair_comp μ hij (H := fun p => k p.1 p.2) hint
  have hconv_int : Integrable (fun x => ∫ y, k x y ∂μ) μ := hk.integrable_rowInt
  have h1 : ∀ i : Fin N, Integrable (fun X : Config d N => ∫ y, k (X i) y ∂μ)
      (Measure.pi fun _ : Fin N => μ) := fun i =>
    integrable_comp_eval (μ := fun _ : Fin N => μ) (i := i) hconv_int
  have hT1 : Integrable (fun X : Config d N => ∑ i, ∑ j ∈ Finset.univ.erase i, k (X i) (X j))
      (Measure.pi fun _ : Fin N => μ) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j hj =>
      hpair i j (Finset.ne_of_mem_erase hj).symm
  have hT2 : Integrable (fun X : Config d N => ∑ i, ∫ y, k (X i) y ∂μ)
      (Measure.pi fun _ : Fin N => μ) := integrable_finsetSum _ fun i _ => h1 i
  unfold modulatedEnergy
  exact ((hT1.const_mul _).sub (hT2.const_mul _)).add (integrable_const _)

theorem expectation_modulatedEnergy_pair (hk : RowOK μ k) (hN : 1 ≤ N) :
    ∫ X : Config d N, modulatedEnergy k X μ ∂(Measure.pi fun _ : Fin N => μ) =
      -(1 / (2 * N)) * ∫ p : Torus d × Torus d, k p.1 p.2 ∂(μ.prod μ) := by
  set G := ∫ p : Torus d × Torus d, k p.1 p.2 ∂(μ.prod μ) with hG
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have hint : Integrable (fun p : Torus d × Torus d => k p.1 p.2) (μ.prod μ) := hk.integrable_prod
  have hpair : ∀ i j : Fin N, i ≠ j →
      Integrable (fun X : Config d N => k (X i) (X j)) (Measure.pi fun _ : Fin N => μ) :=
    fun i j hij => integrable_pair_comp μ hij (H := fun p => k p.1 p.2) hint
  have hpair' : ∀ i j : Fin N, i ≠ j →
      ∫ X : Config d N, k (X i) (X j) ∂(Measure.pi fun _ : Fin N => μ) = G :=
    fun i j hij => integral_pair_comp μ hij (H := fun p => k p.1 p.2) hint
  have hconv_int : Integrable (fun x => ∫ y, k x y ∂μ) μ := hk.integrable_rowInt
  have hconv_mean : ∫ x, ∫ y, k x y ∂μ ∂μ = G := by
    rw [hG, integral_prod _ hint]
  have h1 : ∀ i : Fin N, Integrable (fun X : Config d N => ∫ y, k (X i) y ∂μ)
      (Measure.pi fun _ : Fin N => μ) := fun i =>
    integrable_comp_eval (μ := fun _ : Fin N => μ) (i := i) hconv_int
  have h1' : ∀ i : Fin N, ∫ X : Config d N, ∫ y, k (X i) y ∂μ ∂(Measure.pi fun _ : Fin N => μ) = G :=
    fun i => by
      have := integral_comp_eval (μ := fun _ : Fin N => μ) (i := i) hconv_int.aestronglyMeasurable
      exact this.trans hconv_mean
  have hT1 : Integrable (fun X : Config d N => ∑ i, ∑ j ∈ Finset.univ.erase i, k (X i) (X j))
      (Measure.pi fun _ : Fin N => μ) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j hj =>
      hpair i j (Finset.ne_of_mem_erase hj).symm
  have hT2 : Integrable (fun X : Config d N => ∑ i, ∫ y, k (X i) y ∂μ)
      (Measure.pi fun _ : Fin N => μ) := integrable_finsetSum _ fun i _ => h1 i
  have E1 : ∫ X : Config d N, ∑ i, ∑ j ∈ Finset.univ.erase i, k (X i) (X j)
      ∂(Measure.pi fun _ : Fin N => μ) = (N : ℝ) * ((N : ℝ) - 1) * G := by
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j hj =>
      hpair i j (Finset.ne_of_mem_erase hj).symm]
    have : ∀ i : Fin N, ∫ X : Config d N, ∑ j ∈ Finset.univ.erase i, k (X i) (X j)
        ∂(Measure.pi fun _ : Fin N => μ) = ((N : ℝ) - 1) * G := by
      intro i
      rw [integral_finsetSum _ fun j hj => hpair i j (Finset.ne_of_mem_erase hj).symm]
      rw [Finset.sum_congr rfl fun j hj => hpair' i j (Finset.ne_of_mem_erase hj).symm]
      rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i)]
      simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [Nat.cast_sub hN]; simp
    simp_rw [this]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have E2 : ∫ X : Config d N, ∑ i, ∫ y, k (X i) y ∂μ ∂(Measure.pi fun _ : Fin N => μ) = N * G := by
    rw [integral_finsetSum _ fun i _ => h1 i]
    simp_rw [h1']
    simp
  unfold modulatedEnergy
  rw [integral_add, integral_sub, integral_const_mul, integral_const_mul, E1, E2, integral_const]
  · have hμ : (Measure.pi fun _ : Fin N => μ).real Set.univ = 1 := by simp [Measure.real]
    rw [hμ, one_smul]
    rw [hconv_mean]
    field_simp
    ring
  all_goals first
    | exact (hT1.const_mul _)
    | exact (hT2.const_mul _)
    | exact ((hT1.const_mul _).sub (hT2.const_mul _))
    | exact integrable_const _

end Expectation

section Jensen

/-- Jensen's inequality in `lintegral` form: `e^{∫ Y} ≤ ∫⁻ e^Y` for an integrable `Y`. -/
theorem ofReal_exp_integral_le_lintegral {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] {Y : α → ℝ} (hY : Integrable Y ν) :
    ENNReal.ofReal (Real.exp (∫ x, Y x ∂ν)) ≤ ∫⁻ x, ENNReal.ofReal (Real.exp (Y x)) ∂ν := by
  set m := ∫ x, Y x ∂ν with hm
  set f : α → ℝ := fun x => Real.exp m * (1 + Y x - m) with hf
  have hfi : Integrable f ν := by
    have : Integrable (fun x => 1 + Y x - m) ν := ((integrable_const 1).add hY).sub (integrable_const m)
    exact this.const_mul _
  have hfint : ∫ x, f x ∂ν = Real.exp m := by
    have e1 : ∫ x, (1 + Y x - m) ∂ν = 1 := by
      have a1 : Integrable (fun x => 1 + Y x) ν := (integrable_const 1).add hY
      rw [integral_sub a1 (integrable_const m), integral_add (integrable_const 1) hY]
      simp [hm]
    rw [hf]; simp only
    rw [integral_const_mul, e1, mul_one]
  have hpt : ∀ x, ENNReal.ofReal (max (f x) 0) ≤ ENNReal.ofReal (Real.exp (Y x)) := by
    intro x
    refine ENNReal.ofReal_le_ofReal (max_le ?_ (Real.exp_pos _).le)
    have h1 : 1 + (Y x - m) ≤ Real.exp (Y x - m) := by linarith [Real.add_one_le_exp (Y x - m)]
    have h2 : Real.exp (Y x) = Real.exp m * Real.exp (Y x - m) := by
      rw [← Real.exp_add]; ring_nf
    rw [hf]; simp only
    rw [h2]
    exact mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
  calc ENNReal.ofReal (Real.exp m) = ENNReal.ofReal (∫ x, f x ∂ν) := by rw [hfint]
    _ ≤ ENNReal.ofReal (∫ x, max (f x) 0 ∂ν) :=
        ENNReal.ofReal_le_ofReal (integral_mono hfi hfi.pos_part (fun x => le_max_left _ _))
    _ = ∫⁻ x, ENNReal.ofReal (max (f x) 0) ∂ν :=
        ofReal_integral_eq_lintegral_ofReal hfi.pos_part
          (Filter.Eventually.of_forall fun x => le_max_right _ _)
    _ ≤ _ := lintegral_mono hpt

end Jensen

section PSD

variable {N : ℕ}

theorem cosMode_sq_add_sinMode_sq (k : Lattice d) (x : Torus d) :
    Torus.cosMode k x ^ 2 + Torus.sinMode k x ^ 2 = 1 := by
  have h := Torus.norm_mode k x
  have h2 : ‖Torus.mode k x‖ ^ 2 = 1 := by rw [h]; norm_num
  rw [Complex.sq_norm, Complex.normSq_apply] at h2
  simp only [Torus.cosMode, Torus.sinMode]
  nlinarith

theorem cosMode_sub_expand (k : Lattice d) (x y : Torus d) :
    Torus.cosMode k (x - y) =
      Torus.cosMode k x * Torus.cosMode k y + Torus.sinMode k x * Torus.sinMode k y :=
  StaticLimitAux.cosMode_sub' k x y

/-- The energy of a finite positive-definite cosine kernel is `≥ -(∑ a)/(2N)`: `N F ≥ -(∑ a_k)/2`. -/
theorem psd_energy_lower (hN : 1 ≤ N) (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (Λ : Finset (Lattice d)) (a : Lattice d → ℝ) (ha : ∀ k ∈ Λ, 0 ≤ a k) (X : Config d N) :
    -(∑ k ∈ Λ, a k) / 2 ≤
      (N : ℝ) * modulatedEnergy (fun x y => ∑ k ∈ Λ, a k * Torus.cosMode k (x - y)) X μ := by
  set c : Lattice d → Torus d → ℝ := fun k => Torus.cosMode k with hc
  set sn : Lattice d → Torus d → ℝ := fun k => Torus.sinMode k with hsn
  have hcm : ∀ k, Measurable (c k) := fun k => (Torus.continuous_cosMode k).measurable
  have hsm : ∀ k, Measurable (sn k) := fun k => (Torus.continuous_sinMode k).measurable
  have hci : ∀ k, Integrable (c k) μ := fun k =>
    Integrable.of_bound (hcm k).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun x => Torus.norm_cosMode_le k x)
  have hsi : ∀ k, Integrable (sn k) μ := fun k =>
    Integrable.of_bound (hsm k).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun x => Torus.norm_sinMode_le k x)
  set m : Lattice d → ℝ := fun k => ∫ y, c k y ∂μ with hm
  set n : Lattice d → ℝ := fun k => ∫ y, sn k y ∂μ with hn
  have hG : ∀ x y, ∑ k ∈ Λ, a k * Torus.cosMode k (x - y) =
      ∑ k ∈ Λ, (a k * (c k x * c k y) + a k * (sn k x * sn k y)) := by
    intro x y
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [cosMode_sub_expand]; simp only [hc, hsn]; ring
  have hdiag : ∀ x, ∑ k ∈ Λ, a k * Torus.cosMode k (x - x) = ∑ k ∈ Λ, a k := by
    intro x
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sub_self, show Torus.cosMode k (0 : Torus d) = 1 by simp [Torus.cosMode, StaticLimitAux.mode_apply_zero], mul_one]
  have hrow : ∀ x, ∫ y, ∑ k ∈ Λ, a k * Torus.cosMode k (x - y) ∂μ =
      ∑ k ∈ Λ, (a k * (c k x * m k) + a k * (sn k x * n k)) := by
    intro x
    simp_rw [hG]
    refine (integral_finset_sum Λ fun k _ => ((((hci k).const_mul (c k x)).const_mul (a k)).add
      (((hsi k).const_mul (sn k x)).const_mul (a k)))).trans ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    refine (integral_add (((hci k).const_mul (c k x)).const_mul (a k))
      (((hsi k).const_mul (sn k x)).const_mul (a k))).trans ?_
    simp only [integral_const_mul, hm, hn]
  have hdbl : ∫ x, ∫ y, ∑ k ∈ Λ, a k * Torus.cosMode k (x - y) ∂μ ∂μ =
      ∑ k ∈ Λ, (a k * (m k * m k) + a k * (n k * n k)) := by
    simp_rw [hrow]
    refine (integral_finset_sum Λ fun k _ => ((((hci k).mul_const (m k)).const_mul (a k)).add
      (((hsi k).mul_const (n k)).const_mul (a k)))).trans ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    refine (integral_add (((hci k).mul_const (m k)).const_mul (a k))
      (((hsi k).mul_const (n k)).const_mul (a k))).trans ?_
    simp only [integral_const_mul, integral_mul_const]
    simp only [hm, hn]
  -- the energy identity
  set C : Lattice d → ℝ := fun k => ∑ i, c k (X i) with hC
  set S : Lattice d → ℝ := fun k => ∑ i, sn k (X i) with hS
  have hT0 : ∑ i, ∑ j, ∑ k ∈ Λ, a k * Torus.cosMode k (X i - X j) =
      ∑ k ∈ Λ, a k * (C k ^ 2 + S k ^ 2) := by
    simp_rw [hG]
    have h1 : ∀ i : Fin N, ∑ j : Fin N, ∑ k ∈ Λ, (a k * (c k (X i) * c k (X j)) +
        a k * (sn k (X i) * sn k (X j))) =
        ∑ k ∈ Λ, ∑ j : Fin N, (a k * (c k (X i) * c k (X j)) +
        a k * (sn k (X i) * sn k (X j))) := fun i => Finset.sum_comm
    simp_rw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hC, hS]
    ring
  have hT1 : ∑ i, ∑ j ∈ Finset.univ.erase i, ∑ k ∈ Λ, a k * Torus.cosMode k (X i - X j) =
      ∑ k ∈ Λ, a k * (C k ^ 2 + S k ^ 2) - N * ∑ k ∈ Λ, a k := by
    have e1 : ∀ i, ∑ j ∈ Finset.univ.erase i, ∑ k ∈ Λ, a k * Torus.cosMode k (X i - X j) =
        ∑ j, ∑ k ∈ Λ, a k * Torus.cosMode k (X i - X j) - ∑ k ∈ Λ, a k := by
      intro i
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ i), hdiag]
    simp_rw [e1]
    rw [Finset.sum_sub_distrib, hT0]
    simp
  have hT2 : ∑ i, ∫ y, ∑ k ∈ Λ, a k * Torus.cosMode k (X i - y) ∂μ =
      ∑ k ∈ Λ, (a k * (m k * C k) + a k * (n k * S k)) := by
    simp_rw [hrow]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Finset.sum_add_distrib, hC, hS, Finset.mul_sum]
    congr 1 <;> refine Finset.sum_congr rfl fun i _ => by ring
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have key : (N : ℝ) * modulatedEnergy (fun x y => ∑ k ∈ Λ, a k * Torus.cosMode k (x - y)) X μ =
      ∑ k ∈ Λ, a k / (2 * N) * ((C k - N * m k) ^ 2 + (S k - N * n k) ^ 2) - (∑ k ∈ Λ, a k) / 2 := by
    unfold modulatedEnergy
    rw [hT1, hT2, hdbl]
    have : ∀ k ∈ Λ, a k / (2 * N) * ((C k - N * m k) ^ 2 + (S k - N * n k) ^ 2) =
        a k * (C k ^ 2 + S k ^ 2) / (2 * N) - (a k * (m k * C k) + a k * (n k * S k)) +
          N * (a k * (m k * m k) + a k * (n k * n k)) / 2 := by
      intro k _; field_simp; ring
    rw [Finset.sum_congr rfl this]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum]
    field_simp
    ring
  rw [key]
  have : 0 ≤ ∑ k ∈ Λ, a k / (2 * N) * ((C k - N * m k) ^ 2 + (S k - N * n k) ^ 2) :=
    Finset.sum_nonneg fun k hk => mul_nonneg (div_nonneg (ha k hk) (by positivity)) (by positivity)
  linarith

end PSD

end HRS

end
