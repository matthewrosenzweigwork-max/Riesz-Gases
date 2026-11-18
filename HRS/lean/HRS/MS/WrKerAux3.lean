import HRS.MS.WrKerAux2

/-!
# HRS.MS.WrKerAux3 -- lower bound `K ≥ 1`, weak potential, Euclidean ties (WR-1, part 3)

Port of `HRS/Energy/WeakReference.lean` lines 675-816 and 2265-2336 to a general measurable space `E`,
plus the ties to the frozen Euclidean definitions of `HRS/Whole/Static.lean` for `E = Euc d`.

* `EWeakKernel.one_le_partition_E`: `1 ≤ pairPartitionE q N β μ` for `β ≥ 0`.
* `mkV_E`: the weak potential `φ = κ₀ (q*μ)` of an `EWeakKernel` (the unchanged structure
  `HRS.External.WeakPotential`), with the identification of the Gibbs weight/law with the
  pinned weak ensemble (`pairGibbsLawE_eq_pinnedLaw_E`).
* Euclidean ties: `modEnergyE`, `pairWeightE` are definitionally `HRS.Whole.pairEnergy` and the ENNReal weight;
  `pairNormalizer_eq_toReal_pairPartitionE` (Bochner normaliser = real part of the ENNReal partition function
  under `GibbsWellDefined`), `pairGibbs_eq_pairGibbsLawE`, and `EWeakKernel.gibbsWellDefined_E`
  (an `EWeakKernel` on `Euc d` gives `GibbsWellDefined q N β μ` for `β ≥ 0`, `0 < N`).
-/

set_option linter.unusedSectionVars false

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wr

open HRS.External

variable {E : Type*} [MeasurableSpace E] {N : ℕ}

section Lower

set_option linter.unusedSectionVars false

variable {μ : Measure (E)} [IsProbabilityMeasure μ] {a : ℝ} {q : E → E → ℝ}

lemma EWeakKernel.wr1_integrable_prod (h : EWeakKernel μ a q) :
    Integrable (fun p : E × E => q p.1 p.2) (μ.prod μ) := by
  refine ⟨h.meas.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have : ∀ p : E × E, ‖q p.1 p.2‖ₑ = ENNReal.ofReal (q p.1 p.2) := fun p => by
    rw [Real.enorm_eq_ofReal (h.nonneg _ _)]
  simp_rw [this]
  have hm : Measurable fun p : E × E => ENNReal.ofReal (q p.1 p.2) :=
    ENNReal.measurable_ofReal.comp h.meas
  rw [lintegral_prod (fun p : E × E => ENNReal.ofReal (q p.1 p.2)) hm.aemeasurable]
  calc ∫⁻ x, ∫⁻ y, ENNReal.ofReal (q x y) ∂μ ∂μ ≤ ∫⁻ _x, ENNReal.ofReal a ∂μ :=
        lintegral_mono fun x => h.row x
    _ < ⊤ := by simp

lemma EWeakKernel.wr1_integrable_energy (h : EWeakKernel μ a q) (N : ℕ) :
    Integrable (fun X : (Fin N → E) => modEnergyE q X μ) (Measure.pi fun _ : Fin N => μ) := by
  have hI := h.wr1_integrable_prod
  have hpair : ∀ i j : Fin N, i ≠ j →
      Integrable (fun X : (Fin N → E) => q (X i) (X j)) (Measure.pi fun _ : Fin N => μ) :=
    fun i j hij => integrable_pair_comp μ hij (H := fun p => q p.1 p.2) hI
  have hconv_int : Integrable (fun x => ∫ y, q x y ∂μ) μ := hI.integral_prod_left
  have h1 : ∀ i : Fin N, Integrable (fun X : (Fin N → E) => ∫ y, q (X i) y ∂μ)
      (Measure.pi fun _ : Fin N => μ) := fun i =>
    integrable_comp_eval (μ := fun _ : Fin N => μ) (i := i) hconv_int
  have hT1 : Integrable (fun X : (Fin N → E) => ∑ i, ∑ j ∈ Finset.univ.erase i, q (X i) (X j))
      (Measure.pi fun _ : Fin N => μ) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j hj =>
      hpair i j (Finset.ne_of_mem_erase hj).symm
  have hT2 : Integrable (fun X : (Fin N → E) => ∑ i, ∫ y, q (X i) y ∂μ)
      (Measure.pi fun _ : Fin N => μ) := integrable_finsetSum _ fun i _ => h1 i
  unfold modEnergyE
  exact ((hT1.const_mul _).sub (hT2.const_mul _)).add (integrable_const _)

lemma EWeakKernel.wr1_integral_energy (h : EWeakKernel μ a q) {N : ℕ} (hN : 1 ≤ N) :
    ∫ X : (Fin N → E), modEnergyE q X μ ∂(Measure.pi fun _ : Fin N => μ) =
      -(1 / (2 * N)) * ∫ p : E × E, q p.1 p.2 ∂(μ.prod μ) := by
  have hI := h.wr1_integrable_prod
  set G := ∫ p : E × E, q p.1 p.2 ∂(μ.prod μ) with hG
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have hpair : ∀ i j : Fin N, i ≠ j →
      Integrable (fun X : (Fin N → E) => q (X i) (X j)) (Measure.pi fun _ : Fin N => μ) :=
    fun i j hij => integrable_pair_comp μ hij (H := fun p => q p.1 p.2) hI
  have hpair' : ∀ i j : Fin N, i ≠ j →
      ∫ X : (Fin N → E), q (X i) (X j) ∂(Measure.pi fun _ : Fin N => μ) = G :=
    fun i j hij => integral_pair_comp μ hij (H := fun p => q p.1 p.2) hI
  have hconv_int : Integrable (fun x => ∫ y, q x y ∂μ) μ := hI.integral_prod_left
  have hconv_mean : ∫ x, ∫ y, q x y ∂μ ∂μ = G := by
    rw [hG, integral_prod _ hI]
  have h1 : ∀ i : Fin N, Integrable (fun X : (Fin N → E) => ∫ y, q (X i) y ∂μ)
      (Measure.pi fun _ : Fin N => μ) := fun i =>
    integrable_comp_eval (μ := fun _ : Fin N => μ) (i := i) hconv_int
  have h1' : ∀ i : Fin N, ∫ X : (Fin N → E), ∫ y, q (X i) y ∂μ ∂(Measure.pi fun _ : Fin N => μ) = G :=
    fun i => by
      have := integral_comp_eval (μ := fun _ : Fin N => μ) (i := i) hconv_int.aestronglyMeasurable
      exact this.trans hconv_mean
  have hT1 : Integrable (fun X : (Fin N → E) => ∑ i, ∑ j ∈ Finset.univ.erase i, q (X i) (X j))
      (Measure.pi fun _ : Fin N => μ) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j hj =>
      hpair i j (Finset.ne_of_mem_erase hj).symm
  have hT2 : Integrable (fun X : (Fin N → E) => ∑ i, ∫ y, q (X i) y ∂μ)
      (Measure.pi fun _ : Fin N => μ) := integrable_finsetSum _ fun i _ => h1 i
  have E1 : ∫ X : (Fin N → E), ∑ i, ∑ j ∈ Finset.univ.erase i, q (X i) (X j)
      ∂(Measure.pi fun _ : Fin N => μ) = (N : ℝ) * ((N : ℝ) - 1) * G := by
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j hj =>
      hpair i j (Finset.ne_of_mem_erase hj).symm]
    have : ∀ i : Fin N, ∫ X : (Fin N → E), ∑ j ∈ Finset.univ.erase i, q (X i) (X j)
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
  have E2 : ∫ X : (Fin N → E), ∑ i, ∫ y, q (X i) y ∂μ ∂(Measure.pi fun _ : Fin N => μ) = N * G := by
    rw [integral_finsetSum _ fun i _ => h1 i]
    simp_rw [h1']
    simp
  unfold modEnergyE
  rw [integral_add, integral_sub, integral_const_mul, integral_const_mul, E1, E2, integral_const]
  · have hμ : (Measure.pi fun _ : Fin N => μ).real Set.univ = 1 := by simp [Measure.real]
    rw [hμ, one_smul]
    have : ∫ x, ∫ y, (fun x y => q x y) x y ∂μ ∂μ = G := hconv_mean
    rw [this]
    field_simp
    ring
  all_goals first
    | exact (hT1.const_mul _)
    | exact (hT2.const_mul _)
    | exact ((hT1.const_mul _).sub (hT2.const_mul _))
    | exact integrable_const _

lemma EWeakKernel.one_le_partition_E (h : EWeakKernel μ a q) (ha : 0 ≤ a) {β' : ℝ} (hβ : 0 ≤ β')
    {N : ℕ} (hN : 0 < N) : 1 ≤ pairPartitionE q N β' μ := by
  set t : (Fin N → E) → ℝ := fun X => -β' * N * modEnergyE q X μ with ht
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have it : Integrable t (Measure.pi fun _ : Fin N => μ) :=
    (h.wr1_integrable_energy N).const_mul _
  have iet : Integrable (fun X => Real.exp (t X)) (Measure.pi fun _ : Fin N => μ) := by
    refine Integrable.of_bound (Real.continuous_exp.comp_aestronglyMeasurable it.1)
      (Real.exp (β' * N * a)) (Filter.Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.2 ?_
    have := h.wr1_pairWeight_le ha hβ hN X
    unfold pairWeightE at this
    exact (ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le).1 this |> Real.exp_le_exp.1
  have hK : pairPartitionE q N β' μ = ENNReal.ofReal (∫ X, Real.exp (t X) ∂(Measure.pi fun _ : Fin N => μ)) := by
    unfold pairPartitionE pairWeightE
    rw [ofReal_integral_eq_lintegral_ofReal iet (Filter.Eventually.of_forall fun X => (Real.exp_pos _).le)]
  rw [hK]
  refine ENNReal.one_le_ofReal.2 ?_
  have h1 : ∫ X, (1 + t X) ∂(Measure.pi fun _ : Fin N => μ) ≤ ∫ X, Real.exp (t X) ∂(Measure.pi fun _ : Fin N => μ) :=
    integral_mono ((integrable_const _).add it) iet fun X => by
      have := Real.add_one_le_exp (t X); linarith
  refine le_trans ?_ h1
  rw [integral_add (integrable_const _) it]
  have e : ∫ X, t X ∂(Measure.pi fun _ : Fin N => μ)
      = -β' * N * (-(1 / (2 * N)) * ∫ p : E × E, q p.1 p.2 ∂(μ.prod μ)) := by
    rw [ht]; simp only
    rw [integral_const_mul, h.wr1_integral_energy hN]
  have hG : 0 ≤ ∫ p : E × E, q p.1 p.2 ∂(μ.prod μ) :=
    integral_nonneg fun p => h.nonneg _ _
  have e2 : -β' * N * (-(1 / (2 * N)) * ∫ p : E × E, q p.1 p.2 ∂(μ.prod μ))
      = β' / 2 * ∫ p : E × E, q p.1 p.2 ∂(μ.prod μ) := by
    field_simp
  have : 0 ≤ β' / 2 * ∫ p : E × E, q p.1 p.2 ∂(μ.prod μ) :=
    mul_nonneg (by positivity) hG
  rw [e, e2]
  simp
  linarith

end Lower


section WM_D

variable {μ : Measure E} [IsProbabilityMeasure μ] {a : ℝ}
  {q : E → E → ℝ}

/-- The weak potential of a weak kernel at coupling `κ₀`: `φ = κ₀ (q*μ)`. -/
def mkV_E (hK : EWeakKernel μ a q) (ha : 0 ≤ a) {κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) : WeakPotential μ where
  φ := fun x => κ₀ * rowIntE q μ x
  q := q
  M := κ₀ * a
  M' := 0
  γ := a
  measurable_φ := hK.wr1_measurable_rowInt.const_mul κ₀
  measurable_q := hK.meas
  q_nonneg := hK.nonneg
  q_symm := hK.symm
  γ_nonneg := ha
  φ_le := fun x => mul_le_mul_of_nonneg_left (hK.wr1_rowInt_le ha x) hκ₀
  integrable_φ := by
    refine Integrable.of_bound (hK.wr1_measurable_rowInt.const_mul κ₀).aestronglyMeasurable (κ₀ * a)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hκ₀ (hK.wr1_rowInt_nonneg x))]
    exact mul_le_mul_of_nonneg_left (hK.wr1_rowInt_le ha x) hκ₀
  neg_le_integral_φ := by
    have : 0 ≤ ∫ x, κ₀ * rowIntE q μ x ∂μ :=
      integral_nonneg fun x => mul_nonneg hκ₀ (hK.wr1_rowInt_nonneg x)
    simpa using this
  integrable_q := hK.wr1_integrable_row
  row_le := fun x => hK.wr1_rowInt_le ha x

lemma wr1_pairWeightE_eq_fieldWeight (hK : EWeakKernel μ a q) (ha : 0 ≤ a) {κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀)
    {N : ℕ} (hN : 0 < N) (X : (Fin N → E)) :
    pairWeightE q N κ₀ μ X
      = ENNReal.ofReal (Real.exp (-(κ₀ * N * (∫ x, ∫ y, q x y ∂μ ∂μ) / 2)))
        * fieldWeight (mkV_E hK ha hκ₀) (pinField (mkV_E hK ha hκ₀) (κ₀ / N) (fun e : Empty => e.elim))
            (κ₀ / N) X := by
  unfold pairWeightE fieldWeight
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  rw [wr1_exponent_eq q μ κ₀ X hN]
  have hpe : External.pairEnergy (mkV_E hK ha hκ₀) X = (1 / 2) * pairSumE q X := by
    simp [External.pairEnergy, pairSumE, mkV_E]
  rw [hpe]
  have : (N : ℝ) ≠ 0 := by positivity
  simp only [pinField, mkV_E, Finset.univ_eq_empty, Finset.sum_empty, mul_zero, sub_zero, rowIntE]
  simp only [← Finset.mul_sum]
  field_simp
  ring


lemma pairGibbsLawE_eq_pinnedLaw_E (hK : EWeakKernel μ a q) (ha : 0 ≤ a) {κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀)
    {N : ℕ} (hN : 0 < N) :
    pairGibbsLawE q N κ₀ μ
      = pinnedLaw (mkV_E hK ha hκ₀) (κ₀ / N) N (fun e : Empty => e.elim) := by
  set V := mkV_E hK ha hκ₀ with hV
  have hlam : 0 ≤ κ₀ / N := div_nonneg hκ₀ (Nat.cast_nonneg N)
  have hψ := isField_pinField V hlam (fun e : Empty => e.elim)
  set K₀ : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(κ₀ * N * (∫ x, ∫ y, q x y ∂μ ∂μ) / 2))) with hK₀
  have hK0 : K₀ ≠ 0 := (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have hKt : K₀ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpw : ∀ X : (Fin N → E), pairWeightE q N κ₀ μ X
      = K₀ * fieldWeight V (pinField V (κ₀ / N) (fun e : Empty => e.elim)) (κ₀ / N) X :=
    fun X => wr1_pairWeightE_eq_fieldWeight hK ha hκ₀ hN X
  have hpp : pairPartitionE q N κ₀ μ
      = K₀ * fieldNorm V (pinField V (κ₀ / N) (fun e : Empty => e.elim)) (κ₀ / N) N := by
    unfold pairPartitionE fieldNorm
    simp_rw [hpw]
    exact lintegral_const_mul _ (measurable_fieldWeight hψ.measurable V _)
  unfold pairGibbsLawE pinnedLaw fieldLaw fieldDensity
  congr 1
  funext X
  rw [hpw, hpp, ENNReal.mul_div_mul_left _ _ hK0 hKt, div_eq_mul_inv]


end WM_D

/-! ### Non-vacuity and Euclidean ties -/

section Ties

variable {μ : Measure E} {a : ℝ} {q : E → E → ℝ}

/-- The zero kernel is an `EWeakKernel` with any `a ≥ 0` (the structure is inhabited). -/
lemma wr1_EWeakKernel_zero (μ : Measure E) {a : ℝ} (ha : 0 ≤ a) :
    EWeakKernel μ a (fun _ _ => (0 : ℝ)) :=
  ⟨measurable_const, fun _ _ => rfl, fun _ _ => le_rfl, fun _ => by simpa using ENNReal.ofReal_nonneg⟩

variable {d : ℕ}

/-- The generic modulated energy is `HRS.Whole.pairEnergy` (definitional). -/
theorem modEnergyE_eq_pairEnergy (h : Euc d → Euc d → ℝ) (X : HRS.Whole.EucConfig d N) (μ : Measure (Euc d)) :
    modEnergyE h X μ = HRS.Whole.pairEnergy h X μ := rfl

/-- The ENNReal weight is `ofReal` of the real Gibbs weight of `HRS.Whole.pairNormalizer`'s integrand. -/
theorem pairWeightE_eq_ofReal (h : Euc d → Euc d → ℝ) (N : ℕ) (b : ℝ) (μ : Measure (Euc d))
    (X : HRS.Whole.EucConfig d N) :
    pairWeightE h N b μ X = ENNReal.ofReal (Real.exp (-b * N * HRS.Whole.pairEnergy h X μ)) := rfl

/-- **Normaliser tie.**  Under `GibbsWellDefined` the Bochner normaliser `HRS.Whole.pairNormalizer` is the real
part of the ENNReal partition function (and it is not `⊤`). -/
theorem pairNormalizer_eq_toReal_pairPartitionE {h : Euc d → Euc d → ℝ} {N : ℕ} {b : ℝ}
    {μ : Measure (Euc d)} (hW : HRS.Whole.GibbsWellDefined h N b μ) :
    HRS.Whole.pairNormalizer h N b μ = (pairPartitionE h N b μ).toReal ∧
      pairPartitionE h N b μ = ENNReal.ofReal (HRS.Whole.pairNormalizer h N b μ) ∧
      pairPartitionE h N b μ ≠ ⊤ := by
  have hP : pairPartitionE h N b μ
      = ENNReal.ofReal (HRS.Whole.pairNormalizer h N b μ) := by
    unfold pairPartitionE HRS.Whole.pairNormalizer
    exact (ofReal_integral_eq_lintegral_ofReal hW.weight_integrable
      (Filter.Eventually.of_forall fun X => (Real.exp_pos _).le)).symm
  refine ⟨?_, hP, by rw [hP]; exact ENNReal.ofReal_ne_top⟩
  rw [hP, ENNReal.toReal_ofReal hW.normalizer_pos.le]

/-- The partition function is positive under `GibbsWellDefined`. -/
theorem pairPartitionE_pos {h : Euc d → Euc d → ℝ} {N : ℕ} {b : ℝ}
    {μ : Measure (Euc d)} (hW : HRS.Whole.GibbsWellDefined h N b μ) :
    0 < pairPartitionE h N b μ := by
  rw [(pairNormalizer_eq_toReal_pairPartitionE hW).2.1]
  exact ENNReal.ofReal_pos.2 hW.normalizer_pos

/-- **Gibbs law tie.**  The frozen `HRS.Whole.pairGibbs` is `pairGibbsLawE` under `GibbsWellDefined`. -/
theorem pairGibbs_eq_pairGibbsLawE {h : Euc d → Euc d → ℝ} {N : ℕ} {b : ℝ}
    {μ : Measure (Euc d)} (hW : HRS.Whole.GibbsWellDefined h N b μ) :
    HRS.Whole.pairGibbs h N b μ = pairGibbsLawE h N b μ := by
  obtain ⟨-, hP, -⟩ := pairNormalizer_eq_toReal_pairPartitionE hW
  unfold HRS.Whole.pairGibbs pairGibbsLawE
  rw [← hP]
  have hw : (fun X : HRS.Whole.EucConfig d N => pairWeightE h N b μ X / pairPartitionE h N b μ)
      = (pairPartitionE h N b μ)⁻¹ • fun X => pairWeightE h N b μ X := by
    funext X; simp [div_eq_mul_inv, mul_comm]
  rw [hw, withDensity_smul' _ _ (ENNReal.inv_ne_top.2 (pairPartitionE_pos hW).ne')]
  rfl

/-- **Well-definedness.**  An `EWeakKernel` on `Euc d` with `β ≥ 0`, `0 < N` gives `GibbsWellDefined`: the
background terms are integrable, the weight is integrable (it is bounded by `e^{β N a}`) and the normaliser is
`≥ 1`. -/
theorem EWeakKernel.gibbsWellDefined_E {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {a : ℝ}
    {q : Euc d → Euc d → ℝ} (h : EWeakKernel μ a q) (ha : 0 ≤ a) {β : ℝ} (hβ : 0 ≤ β) {N : ℕ}
    (hN : 0 < N) : HRS.Whole.GibbsWellDefined q N β μ ∧ 1 ≤ HRS.Whole.pairNormalizer q N β μ := by
  have hW := h.wr1_measurable_pairWeight N β
  have hfun : (fun X : HRS.Whole.EucConfig d N => Real.exp (-β * N * HRS.Whole.pairEnergy q X μ))
      = fun X => (pairWeightE q N β μ X).toReal := by
    funext X
    simp [pairWeightE, ENNReal.toReal_ofReal (Real.exp_pos _).le, modEnergyE_eq_pairEnergy]
  have hint : Integrable (fun X : HRS.Whole.EucConfig d N =>
      Real.exp (-β * N * HRS.Whole.pairEnergy q X μ)) (Measure.pi fun _ : Fin N => μ) := by
    rw [hfun]
    exact integrable_toReal_of_lintegral_ne_top hW.aemeasurable
      (h.wr1_partition_pos_lt ha hβ hN).2
  have hP : pairPartitionE q N β μ
      = ENNReal.ofReal (HRS.Whole.pairNormalizer q N β μ) := by
    unfold pairPartitionE HRS.Whole.pairNormalizer
    exact (ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun X => (Real.exp_pos _).le)).symm
  have h1 : 1 ≤ HRS.Whole.pairNormalizer q N β μ := by
    have := h.one_le_partition_E ha hβ hN
    rw [hP] at this
    exact ENNReal.one_le_ofReal.1 this
  exact ⟨⟨fun x => h.wr1_integrable_row x, h.wr1_integrable_prod, hint, by linarith⟩, h1⟩

end Ties

end HRS.MS.Wr
