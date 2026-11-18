import HRS.MS.WrTruncAux1
import HRS.MS.WrAlgAux1
import HRS.MS.WrDiagAux1

/-!
# HRS.MS.WrPressAux1 -- algebra with log-growing rows and the abstract pressure lemma (WR-8, part 1)

Packet WR-8 of `docs/SUPP_FOUND_PACKETS.md` (Track D), namespace `HRS.MS.Wr`.  Infrastructure for
`euclidean_pressure_proof` (S3.1, main bound).

* `Wr8Ok μ k`: measurable pair kernel with integrable rows and integrable on `μ ⊗ μ` (weaker than `RowOKE`: no
  uniform row bound, which fails for the logarithmic kernel `kTauLog`).  Closure under `add`, `const`;
  every `RowOKE` is `Wr8Ok`.  Ports of `modEnergyE_add`, `integrable_modEnergyE`, `integral_modEnergyE`.
* `wr8_modEnergyE_const`: `N F^{c} = -c/2` for a constant kernel.
* `wr8_pressure_abstract`: if `G = P + q_θ - c'` (`P` of class `Wr8Ok` with `N F^P ≥ -κ/2` and
  `∬ P ≥ -m`, `q_θ` an `EWeakKernel`, `c' ≥ 0`), then `GibbsWellDefined G`,
  `exp(-β(m + c')/2) ≤ K^G ≤ e^{βκ/2} K^{q_θ}` (Jensen lower bound, discarding the positive definite part).
* `wr8_gwd_congr`, `wr8_pairNormalizer_congr`: kernels that agree off the diagonal (atomless `μ`) have the same
  well-definedness and the same normaliser.

Helper lemmas carry the prefix `wr8_`.  Nothing here is a manuscript statement.
-/

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Function Set
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wr

variable {E : Type*} [MeasurableSpace E]

/-- A measurable pair kernel with integrable rows, integrable on `μ ⊗ μ`. -/
structure Wr8Ok (μ : Measure E) (k : E → E → ℝ) : Prop where
  meas : Measurable (Function.uncurry k)
  int : ∀ x, Integrable (k x) μ
  prod : Integrable (Function.uncurry k) (μ.prod μ)

namespace Wr8Ok

variable {μ : Measure E} {k k₁ k₂ : E → E → ℝ}

lemma integrable_prod (h : Wr8Ok μ k) : Integrable (Function.uncurry k) (μ.prod μ) := h.prod

lemma integrable_rowInt [SFinite μ] (h : Wr8Ok μ k) : Integrable (fun x => ∫ y, k x y ∂μ) μ :=
  h.prod.integral_prod_left

lemma add [SFinite μ] (h₁ : Wr8Ok μ k₁) (h₂ : Wr8Ok μ k₂) :
    Wr8Ok μ (fun x y => k₁ x y + k₂ x y) :=
  ⟨h₁.meas.add h₂.meas, fun x => (h₁.int x).add (h₂.int x), h₁.prod.add h₂.prod⟩

lemma const [IsFiniteMeasure μ] (c : ℝ) : Wr8Ok μ (fun _ _ => c) :=
  ⟨measurable_const, fun _ => integrable_const c, integrable_const c⟩

end Wr8Ok

lemma RowOKE.wr8_ok {μ : Measure E} [IsFiniteMeasure μ] {k : E → E → ℝ} (h : RowOKE μ k) : Wr8Ok μ k :=
  ⟨h.meas, h.int, h.integrable_prod⟩

section Linear

variable {N : ℕ} {μ : Measure E} [IsFiniteMeasure μ] {k₁ k₂ : E → E → ℝ}

theorem wr8_modEnergyE_add (h₁ : Wr8Ok μ k₁) (h₂ : Wr8Ok μ k₂) (X : Fin N → E) :
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

end Linear

section Expectation

variable {N : ℕ} {μ : Measure E} [IsProbabilityMeasure μ] {k : E → E → ℝ}

theorem wr8_integrable_modEnergyE (hk : Wr8Ok μ k) :
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

theorem wr8_integral_modEnergyE (hk : Wr8Ok μ k) (hN : 1 ≤ N) :
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

/-- `E[N F^k] = -½ ∬ k dμ²` (for `N ≥ 1`), for `Wr8Ok` kernels. -/
theorem wr8_integral_mul_modEnergyE (hk : Wr8Ok μ k) (hN : 1 ≤ N) :
    ∫ X : Fin N → E, (N : ℝ) * modEnergyE k X μ ∂(Measure.pi fun _ : Fin N => μ) =
      -(1 / 2) * ∫ p : E × E, k p.1 p.2 ∂(μ.prod μ) := by
  have hN' : (N : ℝ) ≠ 0 := by positivity
  rw [integral_const_mul, wr8_integral_modEnergyE hk hN]
  field_simp

end Expectation

section Const

variable {N : ℕ} {μ : Measure E} [IsProbabilityMeasure μ]

/-- `N F^{c} = -c/2` for the constant kernel. -/
theorem wr8_modEnergyE_const (c : ℝ) (X : Fin N → E) (hN : 1 ≤ N) :
    (N : ℝ) * modEnergyE (fun _ _ => c) X μ = -c / 2 := by
  have hN' : (N : ℝ) ≠ 0 := by positivity
  unfold modEnergyE
  have e1 : ∀ i : Fin N, ∑ j ∈ Finset.univ.erase i, c = ((N : ℝ) - 1) * c := by
    intro i
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Nat.cast_sub hN]; simp
  simp only [e1, integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

end Const


section Abstract

open HRS.Whole

variable {d N : ℕ}

/-- **Abstract pressure lemma.**  For `G = P + q - c'` with `P` of class `Wr8Ok` (`N F^P ≥ -κ/2`, `∬ P ≥ -m`),
`q` an `EWeakKernel` and `c' ≥ 0`: `G` is Gibbs well defined and
`exp (-β(m + c')/2) ≤ K^G ≤ e^{βκ/2} K^q` (Bochner normalisers). -/
theorem wr8_pressure_abstract {μ : Measure (Euc d)} [IsProbabilityMeasure μ]
    {P q : Euc d → Euc d → ℝ} {a κ m c' β : ℝ}
    (hP : Wr8Ok μ P) (hq : EWeakKernel μ a q) (ha : 0 ≤ a) (hc' : 0 ≤ c')
    (hN : 1 ≤ N) (hβ : 0 ≤ β)
    (hdiag : ∀ X : EucConfig d N, -(κ / 2) ≤ (N : ℝ) * pairEnergy P X μ)
    (hm : -m ≤ ∫ p : Euc d × Euc d, P p.1 p.2 ∂(μ.prod μ)) :
    GibbsWellDefined (fun x y => (P x y + q x y) + (-c')) N β μ ∧
      Real.exp (-(β * (m + c') / 2)) ≤ pairNormalizer (fun x y => (P x y + q x y) + (-c')) N β μ ∧
      pairNormalizer (fun x y => (P x y + q x y) + (-c')) N β μ ≤
        Real.exp (β * κ / 2) * pairNormalizer q N β μ := by
  have hN0 : 0 < N := hN
  have hqok : Wr8Ok μ q := (hq.rowOKE ha).wr8_ok
  have hPq : Wr8Ok μ (fun x y => P x y + q x y) := hP.add hqok
  have hG : Wr8Ok μ (fun x y => (P x y + q x y) + (-c')) := hPq.add (Wr8Ok.const (-c'))
  set G : Euc d → Euc d → ℝ := fun x y => (P x y + q x y) + (-c') with hGdef
  obtain ⟨hqW, -⟩ := hq.gibbsWellDefined_E ha hβ hN0
  -- energy identity
  have hE : ∀ X : EucConfig d N, (N : ℝ) * pairEnergy G X μ =
      (N : ℝ) * pairEnergy P X μ + (N : ℝ) * pairEnergy q X μ + c' / 2 := by
    intro X
    have e1 := wr8_modEnergyE_add (N := N) hPq (Wr8Ok.const (-c')) X
    have e2 := wr8_modEnergyE_add (N := N) hP hqok X
    have e3 := wr8_modEnergyE_const (μ := μ) (N := N) (-c') X hN
    have : pairEnergy G X μ = pairEnergy P X μ + pairEnergy q X μ + pairEnergy (fun _ _ => -c') X μ := by
      show modEnergyE G X μ = _
      rw [hGdef]
      rw [e1, e2]; rfl
    rw [this]
    have e4 : (N : ℝ) * pairEnergy (fun _ _ => -c') X μ = c' / 2 := by
      have := e3; simp only [modEnergyE_eq_pairEnergy] at this; linarith
    nlinarith [e4]
  -- pointwise weight bound
  have hwt : ∀ X : EucConfig d N, Real.exp (-β * N * pairEnergy G X μ) ≤
      Real.exp (β * κ / 2) * Real.exp (-β * N * pairEnergy q X μ) := by
    intro X
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have h1 := hdiag X
    have h2 : -β * N * pairEnergy G X μ = -β * ((N : ℝ) * pairEnergy G X μ) := by ring
    have h3 : -β * N * pairEnergy q X μ = -β * ((N : ℝ) * pairEnergy q X μ) := by ring
    rw [h2, h3, hE X]
    nlinarith [mul_nonneg hβ hc', mul_nonneg hβ (sub_nonneg.2 h1)]
  -- integrability of the weight and of the energy
  have hEint : Integrable (fun X : EucConfig d N => pairEnergy G X μ) (Measure.pi fun _ : Fin N => μ) :=
    wr8_integrable_modEnergyE hG
  have hYint : Integrable (fun X : EucConfig d N => -β * N * pairEnergy G X μ)
      (Measure.pi fun _ : Fin N => μ) := hEint.const_mul _
  have hexpm : AEStronglyMeasurable (fun X : EucConfig d N => Real.exp (-β * N * pairEnergy G X μ))
      (Measure.pi fun _ : Fin N => μ) :=
    Real.continuous_exp.comp_aestronglyMeasurable hYint.aestronglyMeasurable
  have hWint : Integrable (fun X : EucConfig d N => Real.exp (-β * N * pairEnergy G X μ))
      (Measure.pi fun _ : Fin N => μ) := by
    refine Integrable.mono' (hqW.weight_integrable.const_mul (Real.exp (β * κ / 2))) hexpm
      (Filter.Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hwt X
  -- Jensen lower bound
  have hmean : ∫ X : EucConfig d N, -β * N * pairEnergy G X μ ∂(Measure.pi fun _ : Fin N => μ) =
      β / 2 * ∫ p : Euc d × Euc d, G p.1 p.2 ∂(μ.prod μ) := by
    have : ∀ X : EucConfig d N, -β * N * pairEnergy G X μ = -β * ((N : ℝ) * pairEnergy G X μ) :=
      fun X => by ring
    simp_rw [this]
    rw [integral_const_mul]
    have h5 := wr8_integral_mul_modEnergyE (N := N) (μ := μ) hG hN
    simp only [modEnergyE_eq_pairEnergy] at h5
    rw [h5]; ring
  have hint2 : ∫ p : Euc d × Euc d, G p.1 p.2 ∂(μ.prod μ) =
      (∫ p : Euc d × Euc d, P p.1 p.2 ∂(μ.prod μ)) + (∫ p : Euc d × Euc d, q p.1 p.2 ∂(μ.prod μ)) - c' := by
    have hA : Integrable (fun p : Euc d × Euc d => P p.1 p.2) (μ.prod μ) := hP.prod
    have hB : Integrable (fun p : Euc d × Euc d => q p.1 p.2) (μ.prod μ) := hqok.prod
    have : (fun p : Euc d × Euc d => G p.1 p.2) =
        fun p => (P p.1 p.2 + q p.1 p.2) + (-c') := rfl
    rw [this]
    have h1 : ∫ p : Euc d × Euc d, ((P p.1 p.2 + q p.1 p.2) + (-c')) ∂(μ.prod μ) =
        (∫ p : Euc d × Euc d, (P p.1 p.2 + q p.1 p.2) ∂(μ.prod μ)) + ∫ _p : Euc d × Euc d, (-c') ∂(μ.prod μ) :=
      integral_add (hA.add hB) (integrable_const _)
    rw [h1, integral_add hA hB]
    simp [Measure.real]
    ring
  have hqnn : 0 ≤ ∫ p : Euc d × Euc d, q p.1 p.2 ∂(μ.prod μ) :=
    integral_nonneg fun p => hq.nonneg _ _
  have hlow : Real.exp (-(β * (m + c') / 2)) ≤ pairNormalizer G N β μ := by
    have hj := ConvexOn.map_integral_le (μ := Measure.pi fun _ : Fin N => μ) convexOn_exp
      Real.continuous_exp.continuousOn isClosed_univ (Filter.Eventually.of_forall fun _ => mem_univ _)
      hYint (by exact hWint)
    unfold pairNormalizer
    refine le_trans (Real.exp_le_exp.2 ?_) hj
    rw [hmean, hint2]
    nlinarith [mul_nonneg hβ hqnn, mul_nonneg hβ (show 0 ≤ ∫ p : Euc d × Euc d, P p.1 p.2 ∂(μ.prod μ) + m
      by linarith)]
  have hpos : 0 < pairNormalizer G N β μ := lt_of_lt_of_le (Real.exp_pos _) hlow
  refine ⟨⟨fun x => hG.int x, hG.prod, hWint, hpos⟩, hlow, ?_⟩
  unfold pairNormalizer
  rw [← integral_const_mul]
  exact integral_mono hWint (hqW.weight_integrable.const_mul _) hwt

end Abstract

end HRS.MS.Wr
