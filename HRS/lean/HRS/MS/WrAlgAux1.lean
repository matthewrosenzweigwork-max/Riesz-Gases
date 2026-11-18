import HRS.MS.WrKerAux3

/-!
# HRS.MS.WrAlgAux1 -- algebra of the pair-kernel energy on `EucConfig d N` (WR-2)

Packet WR-2 of `docs/SUPP_FOUND_PACKETS.md` (Track D).  Port of `HRS/Energy/PressureAlg.lean`
(sections `RowOK`, `Linear`, `Offdiag`, `Expectation`) from `Torus d`, `Config d N` to an arbitrary
measurable space `E` (Euclidean case `E = Euc d`, `Fin N → Euc d = EucConfig d N`); the torus file is
not edited.  The energy is `modEnergyE`, which is definitionally `HRS.Whole.pairEnergy`
(`modEnergyE_eq_pairEnergy`), and the Euclidean statements are given for `pairEnergy` itself.

* `RowOKE μ k`: measurable pair kernel with integrable rows of uniformly bounded `L¹(μ)` norm
  (the junk-free hypothesis: all Bochner integrals below are of integrable functions).
  Closure under `add`, `smul`, `neg`, `sub`, `const`; every `EWeakKernel` is `RowOKE` (`EWeakKernel.rowOKE`).
* `integrable_prod`, `integrable_rowInt`: the integrability of `k` on `μ ⊗ μ` and of its row integral,
  the `pair_integrable` / `conv_integrable` ingredients of `HRS.Whole.GibbsWellDefined`.
* additivity: `pairEnergy_add`, `pairEnergy_smul`, `pairEnergy_sub`, `pairEnergy_neg` (for `RowOKE` kernels).
* `pairEnergy_congr_offdiag`: two kernels that agree off the diagonal give the same energy at a configuration
  with pairwise distinct particles, when `μ` has no atoms.
* `diag_null_E`, `ae_injective_pi_E`: for atomless `μ`, the diagonal of `μ ⊗ μ` is null and
  `μ^{⊗N}`-a.e. configurations have pairwise distinct particles.
* `integrable_pairEnergy`, `integral_pairEnergy`: `X ↦ pairEnergy k X μ` is `μ^{⊗N}`-integrable and
  `E[pairEnergy k] = -(2N)⁻¹ ∬ k dμ²`, i.e. `E[N F^k] = -½ ∬ k` (`N ≥ 1`).

Only statements: the torus proofs port verbatim.  No hypothesis is added or dropped, except that the
generic `ae_injective_pi_E` needs `[MeasurableEq E]` (the torus statement used `measurableSet_eq_fun`).
Helper lemmas carry the prefix `wr2_`.
-/

set_option linter.unusedSectionVars false

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wr

variable {E : Type*} [MeasurableSpace E]

/-- A measurable pair kernel with integrable rows of uniformly bounded `L¹(μ)` norm. -/
structure RowOKE (μ : Measure E) (k : E → E → ℝ) : Prop where
  meas : Measurable (Function.uncurry k)
  int : ∀ x, Integrable (k x) μ
  bound : ∃ M : ℝ, ∀ x, ∫ y, |k x y| ∂μ ≤ M

namespace RowOKE

variable {μ : Measure E} {k k₁ k₂ : E → E → ℝ}

lemma measurable_row (h : RowOKE μ k) (x : E) : Measurable (k x) :=
  h.meas.comp (measurable_const.prodMk measurable_id)

lemma measurable_rowInt [SFinite μ] (h : RowOKE μ k) : Measurable (fun x => ∫ y, k x y ∂μ) :=
  (h.meas.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable

lemma abs_rowInt_le (h : RowOKE μ k) {M : ℝ} (hM : ∀ x, ∫ y, |k x y| ∂μ ≤ M) (x : E) :
    |∫ y, k x y ∂μ| ≤ M :=
  (abs_integral_le_integral_abs).trans (hM x)

lemma integrable_rowInt [IsFiniteMeasure μ] (h : RowOKE μ k) :
    Integrable (fun x => ∫ y, k x y ∂μ) μ := by
  obtain ⟨M, hM⟩ := h.bound
  exact Integrable.of_bound h.measurable_rowInt.aestronglyMeasurable M
    (Filter.Eventually.of_forall fun x => by simpa using h.abs_rowInt_le hM x)

lemma integrable_prod [IsFiniteMeasure μ] (h : RowOKE μ k) :
    Integrable (Function.uncurry k) (μ.prod μ) := by
  obtain ⟨M, hM⟩ := h.bound
  refine (integrable_prod_iff h.meas.aestronglyMeasurable).2
    ⟨Filter.Eventually.of_forall h.int, ?_⟩
  have hm : Measurable (fun x => ∫ y, ‖k x y‖ ∂μ) :=
    (h.meas.norm.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable
  refine Integrable.of_bound hm.aestronglyMeasurable M (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
  simpa using hM x

lemma add [IsFiniteMeasure μ] (h₁ : RowOKE μ k₁) (h₂ : RowOKE μ k₂) :
    RowOKE μ (fun x y => k₁ x y + k₂ x y) := by
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

lemma smul [IsFiniteMeasure μ] (c : ℝ) (h : RowOKE μ k) : RowOKE μ (fun x y => c * k x y) := by
  refine ⟨measurable_const.mul h.meas, fun x => (h.int x).const_mul c, ?_⟩
  obtain ⟨M, hM⟩ := h.bound
  refine ⟨|c| * M, fun x => ?_⟩
  simp_rw [abs_mul]
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (hM x) (abs_nonneg c)

lemma const [IsFiniteMeasure μ] (c : ℝ) : RowOKE μ (fun _ _ => c) := by
  refine ⟨measurable_const, fun x => integrable_const c, ⟨|c| * (μ Set.univ).toReal, fun x => ?_⟩⟩
  simp [integral_const, Measure.real, mul_comm]

lemma neg [IsFiniteMeasure μ] (h : RowOKE μ k) : RowOKE μ (fun x y => -k x y) := by
  have := h.smul (-1)
  simpa using this

lemma sub [IsFiniteMeasure μ] (h₁ : RowOKE μ k₁) (h₂ : RowOKE μ k₂) :
    RowOKE μ (fun x y => k₁ x y - k₂ x y) := by
  simpa [sub_eq_add_neg] using h₁.add h₂.neg

end RowOKE

/-- Every `EWeakKernel` (nonnegative, measurable, row mass `≤ a`) is `RowOKE`. -/
lemma EWeakKernel.rowOKE {μ : Measure E} [IsProbabilityMeasure μ] {a : ℝ} {q : E → E → ℝ}
    (h : EWeakKernel μ a q) (ha : 0 ≤ a) : RowOKE μ q := by
  refine ⟨h.meas, fun x => h.wr1_integrable_row x, a, fun x => ?_⟩
  have : ∫ y, |q x y| ∂μ = rowIntE q μ x := by
    unfold rowIntE
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => abs_of_nonneg (h.nonneg x y))
  rw [this]
  exact h.wr1_rowInt_le ha x

section Linear

variable {N : ℕ} {μ : Measure E} [IsFiniteMeasure μ] {k₁ k₂ : E → E → ℝ}

theorem modEnergyE_add (h₁ : RowOKE μ k₁) (h₂ : RowOKE μ k₂) (X : Fin N → E) :
    modEnergyE (fun x y => k₁ x y + k₂ x y) X μ = modEnergyE k₁ X μ + modEnergyE k₂ X μ := by
  unfold modEnergyE
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

theorem modEnergyE_smul (c : ℝ) (_h : RowOKE μ k₁) (X : Fin N → E) :
    modEnergyE (fun x y => c * k₁ x y) X μ = c * modEnergyE k₁ X μ := by
  unfold modEnergyE
  simp only [← Finset.mul_sum, integral_const_mul]
  ring

theorem modEnergyE_sub (h₁ : RowOKE μ k₁) (h₂ : RowOKE μ k₂) (X : Fin N → E) :
    modEnergyE (fun x y => k₁ x y - k₂ x y) X μ = modEnergyE k₁ X μ - modEnergyE k₂ X μ := by
  have := modEnergyE_add h₁ h₂.neg X
  have h3 := modEnergyE_smul (-1) h₂ X
  simp only [neg_mul, one_mul] at this h3
  simp only [sub_eq_add_neg]
  rw [this, h3]

end Linear

section Offdiag

variable {N : ℕ} {μ : Measure E}

theorem modEnergyE_congr_offdiag (hμ : ∀ x, μ {x} = 0) {k₁ k₂ : E → E → ℝ}
    (hk : ∀ x y, x ≠ y → k₁ x y = k₂ x y) (X : Fin N → E) (hX : ∀ i j, i ≠ j → X i ≠ X j) :
    modEnergyE k₁ X μ = modEnergyE k₂ X μ := by
  have hae : ∀ x, ∀ᵐ y ∂μ, k₁ x y = k₂ x y := fun x => by
    have : ∀ᵐ y ∂μ, y ≠ x := by
      rw [ae_iff]; simpa using hμ x
    filter_upwards [this] with y hy using hk x y hy.symm
  unfold modEnergyE
  have e1 : ∀ i, ∫ y, k₁ (X i) y ∂μ = ∫ y, k₂ (X i) y ∂μ := fun i => integral_congr_ae (hae _)
  have e2 : ∀ x, ∫ y, k₁ x y ∂μ = ∫ y, k₂ x y ∂μ := fun x => integral_congr_ae (hae x)
  have e3 : ∀ i, ∑ j ∈ Finset.univ.erase i, k₁ (X i) (X j) =
      ∑ j ∈ Finset.univ.erase i, k₂ (X i) (X j) :=
    fun i => Finset.sum_congr rfl fun j hj =>
      hk _ _ (hX i j (Finset.ne_of_mem_erase hj).symm)
  simp only [e1, e2, e3]

/-- For atomless `μ` the diagonal of `μ ⊗ μ` is null. -/
theorem diag_null_E [MeasurableEq E] [SFinite μ] (hμ : ∀ x, μ {x} = 0) :
    (μ.prod μ) {p : E × E | p.1 = p.2} = 0 := by
  have hdiag : MeasurableSet {p : E × E | p.1 = p.2} :=
    measurableSet_eq_fun measurable_fst measurable_snd
  rw [Measure.prod_apply hdiag]
  have : ∀ x : E, μ (Prod.mk x ⁻¹' {p : E × E | p.1 = p.2}) = 0 := by
    intro x
    have : Prod.mk x ⁻¹' {p : E × E | p.1 = p.2} = {x} := by
      ext y; simp [eq_comm]
    rw [this]; exact hμ x
  simp only [this, lintegral_zero]

/-- For atomless `μ`, `μ^{⊗N}`-a.e. configuration has pairwise distinct particles. -/
theorem ae_injective_pi_E [MeasurableEq E] [IsProbabilityMeasure μ] (hμ : ∀ x, μ {x} = 0) :
    ∀ᵐ X ∂(Measure.pi fun _ : Fin N => μ), ∀ i j, i ≠ j → X i ≠ X j := by
  rw [ae_all_iff]; intro i
  rw [ae_all_iff]; intro j
  by_cases hij : i = j
  · exact Filter.Eventually.of_forall fun X h => absurd hij h
  · have hdiag : MeasurableSet {p : E × E | p.1 = p.2} :=
      measurableSet_eq_fun measurable_fst measurable_snd
    have hm : Measurable (fun X : Fin N → E => (X i, X j)) :=
      (measurable_pi_apply i).prodMk (measurable_pi_apply j)
    have h1 : (Measure.pi fun _ : Fin N => μ) {X | X i = X j} = 0 := by
      have := Measure.map_apply hm hdiag (μ := Measure.pi fun _ : Fin N => μ)
      rw [pi_map_pair μ hij, diag_null_E hμ] at this
      exact this.symm
    rw [ae_iff]
    have : {a : Fin N → E | ¬(i ≠ j → a i ≠ a j)} = {X | X i = X j} := by
      ext X; simp [hij]
    rw [this]; exact h1

end Offdiag

section Expectation

variable {N : ℕ} {μ : Measure E} [IsProbabilityMeasure μ] {k : E → E → ℝ}

theorem integrable_modEnergyE (hk : RowOKE μ k) :
    Integrable (fun X : Fin N → E => modEnergyE k X μ) (Measure.pi fun _ : Fin N => μ) := by
  have hint : Integrable (fun p : E × E => k p.1 p.2) (μ.prod μ) := hk.integrable_prod
  have hpair : ∀ i j : Fin N, i ≠ j →
      Integrable (fun X : Fin N → E => k (X i) (X j)) (Measure.pi fun _ : Fin N => μ) :=
    fun i j hij => integrable_pair_comp μ hij (H := fun p => k p.1 p.2) hint
  have hconv_int : Integrable (fun x => ∫ y, k x y ∂μ) μ := hk.integrable_rowInt
  have h1 : ∀ i : Fin N, Integrable (fun X : Fin N → E => ∫ y, k (X i) y ∂μ)
      (Measure.pi fun _ : Fin N => μ) := fun i =>
    integrable_comp_eval (μ := fun _ : Fin N => μ) (i := i) hconv_int
  have hT1 : Integrable (fun X : Fin N → E => ∑ i, ∑ j ∈ Finset.univ.erase i, k (X i) (X j))
      (Measure.pi fun _ : Fin N => μ) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j hj =>
      hpair i j (Finset.ne_of_mem_erase hj).symm
  have hT2 : Integrable (fun X : Fin N → E => ∑ i, ∫ y, k (X i) y ∂μ)
      (Measure.pi fun _ : Fin N => μ) := integrable_finsetSum _ fun i _ => h1 i
  unfold modEnergyE
  exact ((hT1.const_mul _).sub (hT2.const_mul _)).add (integrable_const _)

theorem integral_modEnergyE (hk : RowOKE μ k) (hN : 1 ≤ N) :
    ∫ X : Fin N → E, modEnergyE k X μ ∂(Measure.pi fun _ : Fin N => μ) =
      -(1 / (2 * N)) * ∫ p : E × E, k p.1 p.2 ∂(μ.prod μ) := by
  set G := ∫ p : E × E, k p.1 p.2 ∂(μ.prod μ) with hG
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have hint : Integrable (fun p : E × E => k p.1 p.2) (μ.prod μ) := hk.integrable_prod
  have hpair : ∀ i j : Fin N, i ≠ j →
      Integrable (fun X : Fin N → E => k (X i) (X j)) (Measure.pi fun _ : Fin N => μ) :=
    fun i j hij => integrable_pair_comp μ hij (H := fun p => k p.1 p.2) hint
  have hpair' : ∀ i j : Fin N, i ≠ j →
      ∫ X : Fin N → E, k (X i) (X j) ∂(Measure.pi fun _ : Fin N => μ) = G :=
    fun i j hij => integral_pair_comp μ hij (H := fun p => k p.1 p.2) hint
  have hconv_int : Integrable (fun x => ∫ y, k x y ∂μ) μ := hk.integrable_rowInt
  have hconv_mean : ∫ x, ∫ y, k x y ∂μ ∂μ = G := by
    rw [hG, integral_prod _ hint]
  have h1 : ∀ i : Fin N, Integrable (fun X : Fin N → E => ∫ y, k (X i) y ∂μ)
      (Measure.pi fun _ : Fin N => μ) := fun i =>
    integrable_comp_eval (μ := fun _ : Fin N => μ) (i := i) hconv_int
  have h1' : ∀ i : Fin N,
      ∫ X : Fin N → E, ∫ y, k (X i) y ∂μ ∂(Measure.pi fun _ : Fin N => μ) = G :=
    fun i => by
      have := integral_comp_eval (μ := fun _ : Fin N => μ) (i := i) hconv_int.aestronglyMeasurable
      exact this.trans hconv_mean
  have hT1 : Integrable (fun X : Fin N → E => ∑ i, ∑ j ∈ Finset.univ.erase i, k (X i) (X j))
      (Measure.pi fun _ : Fin N => μ) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j hj =>
      hpair i j (Finset.ne_of_mem_erase hj).symm
  have hT2 : Integrable (fun X : Fin N → E => ∑ i, ∫ y, k (X i) y ∂μ)
      (Measure.pi fun _ : Fin N => μ) := integrable_finsetSum _ fun i _ => h1 i
  have E1 : ∫ X : Fin N → E, ∑ i, ∑ j ∈ Finset.univ.erase i, k (X i) (X j)
      ∂(Measure.pi fun _ : Fin N => μ) = (N : ℝ) * ((N : ℝ) - 1) * G := by
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j hj =>
      hpair i j (Finset.ne_of_mem_erase hj).symm]
    have : ∀ i : Fin N, ∫ X : Fin N → E, ∑ j ∈ Finset.univ.erase i, k (X i) (X j)
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
  have E2 : ∫ X : Fin N → E, ∑ i, ∫ y, k (X i) y ∂μ ∂(Measure.pi fun _ : Fin N => μ) = N * G := by
    rw [integral_finsetSum _ fun i _ => h1 i]
    simp_rw [h1']
    simp
  unfold modEnergyE
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

/-- `E[N F^k] = -½ ∬ k dμ²` (for `N ≥ 1`). -/
theorem integral_mul_modEnergyE (hk : RowOKE μ k) (hN : 1 ≤ N) :
    ∫ X : Fin N → E, (N : ℝ) * modEnergyE k X μ ∂(Measure.pi fun _ : Fin N => μ) =
      -(1 / 2) * ∫ p : E × E, k p.1 p.2 ∂(μ.prod μ) := by
  have hN' : (N : ℝ) ≠ 0 := by positivity
  rw [integral_const_mul, integral_modEnergyE hk hN]
  field_simp

end Expectation

/-! ### Euclidean statements for `HRS.Whole.pairEnergy` -/

section Euclid

open HRS.Whole

variable {d N : ℕ}

theorem pairEnergy_add {μ : Measure (Euc d)} [IsFiniteMeasure μ] {k₁ k₂ : Euc d → Euc d → ℝ}
    (h₁ : RowOKE μ k₁) (h₂ : RowOKE μ k₂) (X : EucConfig d N) :
    pairEnergy (fun x y => k₁ x y + k₂ x y) X μ = pairEnergy k₁ X μ + pairEnergy k₂ X μ :=
  modEnergyE_add h₁ h₂ X

theorem pairEnergy_smul {μ : Measure (Euc d)} [IsFiniteMeasure μ] {k : Euc d → Euc d → ℝ}
    (c : ℝ) (h : RowOKE μ k) (X : EucConfig d N) :
    pairEnergy (fun x y => c * k x y) X μ = c * pairEnergy k X μ :=
  modEnergyE_smul c h X

theorem pairEnergy_sub {μ : Measure (Euc d)} [IsFiniteMeasure μ] {k₁ k₂ : Euc d → Euc d → ℝ}
    (h₁ : RowOKE μ k₁) (h₂ : RowOKE μ k₂) (X : EucConfig d N) :
    pairEnergy (fun x y => k₁ x y - k₂ x y) X μ = pairEnergy k₁ X μ - pairEnergy k₂ X μ :=
  modEnergyE_sub h₁ h₂ X

theorem pairEnergy_neg {μ : Measure (Euc d)} [IsFiniteMeasure μ] {k : Euc d → Euc d → ℝ}
    (h : RowOKE μ k) (X : EucConfig d N) :
    pairEnergy (fun x y => -k x y) X μ = -pairEnergy k X μ := by
  have := pairEnergy_smul (N := N) (-1) h X
  simpa using this

theorem pairEnergy_congr_offdiag {μ : Measure (Euc d)} (hμ : ∀ x, μ {x} = 0)
    {k₁ k₂ : Euc d → Euc d → ℝ} (hk : ∀ x y, x ≠ y → k₁ x y = k₂ x y)
    (X : EucConfig d N) (hX : ∀ i j, i ≠ j → X i ≠ X j) :
    pairEnergy k₁ X μ = pairEnergy k₂ X μ :=
  modEnergyE_congr_offdiag hμ hk X hX

theorem diag_null_Euc {μ : Measure (Euc d)} [SFinite μ] (hμ : ∀ x, μ {x} = 0) :
    (μ.prod μ) {p : Euc d × Euc d | p.1 = p.2} = 0 :=
  diag_null_E hμ

theorem ae_injective_pi_Euc {μ : Measure (Euc d)} [IsProbabilityMeasure μ] (hμ : ∀ x, μ {x} = 0) :
    ∀ᵐ X ∂(Measure.pi fun _ : Fin N => μ), ∀ i j, i ≠ j → X i ≠ X j :=
  ae_injective_pi_E hμ

theorem integrable_pairEnergy {μ : Measure (Euc d)} [IsProbabilityMeasure μ]
    {k : Euc d → Euc d → ℝ} (hk : RowOKE μ k) :
    Integrable (fun X : EucConfig d N => pairEnergy k X μ) (Measure.pi fun _ : Fin N => μ) :=
  integrable_modEnergyE hk

theorem integral_pairEnergy {μ : Measure (Euc d)} [IsProbabilityMeasure μ]
    {k : Euc d → Euc d → ℝ} (hk : RowOKE μ k) (hN : 1 ≤ N) :
    ∫ X : EucConfig d N, pairEnergy k X μ ∂(Measure.pi fun _ : Fin N => μ) =
      -(1 / (2 * N)) * ∫ p : Euc d × Euc d, k p.1 p.2 ∂(μ.prod μ) :=
  integral_modEnergyE hk hN

/-- `E[N F_N^k] = -½ ∬ k dμ²`. -/
theorem integral_mul_pairEnergy {μ : Measure (Euc d)} [IsProbabilityMeasure μ]
    {k : Euc d → Euc d → ℝ} (hk : RowOKE μ k) (hN : 1 ≤ N) :
    ∫ X : EucConfig d N, (N : ℝ) * pairEnergy k X μ ∂(Measure.pi fun _ : Fin N => μ) =
      -(1 / 2) * ∫ p : Euc d × Euc d, k p.1 p.2 ∂(μ.prod μ) :=
  integral_mul_modEnergyE hk hN

end Euclid

end HRS.MS.Wr
