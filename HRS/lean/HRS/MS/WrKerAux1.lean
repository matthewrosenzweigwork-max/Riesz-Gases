import HRS.Whole.Static
import HRS.External.WeakSpec

/-!
# HRS.MS.WrKerAux1 -- generic weak-kernel Gibbs weights (WR-1, part 1)

Packet WR-1 of `docs/SUPP_FOUND_PACKETS.md` (Track D).  Port of `HRS/Energy/WeakReference.lean`
lines 87-450 from `Torus d`, `Config d N` to an arbitrary measurable space `E` (the Euclidean case
is `E = Euc d`, configurations `Fin N → E = EucConfig d N`).  The torus file is not edited.

* `EWeakKernel μ a q`: the hypotheses of `WeakKernel` (measurable, symmetric, nonnegative, row bound
  `∫⁻ ofReal (q x y) dμ(y) ≤ ofReal a`), for any measurable space.
* `modEnergyE`, `pairWeightE`, `pairPartitionE`, `pairGibbsLawE`: the modulated energy (same formula as
  `HRS.Whole.pairEnergy`, definitionally equal for `E = Euc d`), the ENNReal Gibbs weight
  `ofReal (exp (-β N F))`, its partition function and the normalised law.
* the one-site factorisation `weight_update`, the conditional kernel formula `siteKernel_eq`.

No hypotheses are added or dropped with respect to the torus statements.  Helper lemmas carry the prefix `wr1_`
(or are `EWeakKernel.wr1_*`).
-/

set_option linter.unusedSectionVars false

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wr

variable {E : Type*} [MeasurableSpace E] {N : ℕ}

/-- The modulated energy of a pair kernel `q` (same formula as `HRS.Whole.pairEnergy`). -/
def modEnergyE (q : E → E → ℝ) (X : Fin N → E) (μ : Measure E) : ℝ :=
  (1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, q (X i) (X j)
    - (1 / (N : ℝ)) * ∑ i, ∫ y, q (X i) y ∂μ
    + (1 / 2) * ∫ x, ∫ y, q x y ∂μ ∂μ

/-- Unnormalised Gibbs weight `exp(-β N F_N^q(X, μ))`, as an extended nonnegative real. -/
def pairWeightE (q : E → E → ℝ) (N : ℕ) (β : ℝ) (μ : Measure E) (X : Fin N → E) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-β * N * modEnergyE q X μ))

/-- `K^q_{N,β}(μ) = ∫⁻ exp(-β N F_N^q) dμ^{⊗N}`. -/
def pairPartitionE (q : E → E → ℝ) (N : ℕ) (β : ℝ) (μ : Measure E) : ℝ≥0∞ :=
  ∫⁻ X, pairWeightE q N β μ X ∂(Measure.pi fun _ : Fin N => μ)

/-- The normalised Gibbs law of the pair kernel `q`. -/
def pairGibbsLawE (q : E → E → ℝ) (N : ℕ) (β : ℝ) (μ : Measure E) : Measure (Fin N → E) :=
  (Measure.pi fun _ : Fin N => μ).withDensity fun X => pairWeightE q N β μ X / pairPartitionE q N β μ

/-- row integral `H x = ∫ q(x,y) dμ(y)` -/
def rowIntE (q : E → E → ℝ) (μ : Measure E) (x : E) : ℝ :=
  ∫ y, q x y ∂μ

/-- Hypotheses on the weak kernel (any measurable space `E`). -/
structure EWeakKernel (μ : Measure E) (a : ℝ) (q : E → E → ℝ) : Prop where
  meas : Measurable (Function.uncurry q)
  symm : ∀ x y, q x y = q y x
  nonneg : ∀ x y, 0 ≤ q x y
  row : ∀ x, ∫⁻ y, ENNReal.ofReal (q x y) ∂μ ≤ ENNReal.ofReal a

section WK

variable {μ : Measure (E)} [IsProbabilityMeasure μ] {a : ℝ} {q : E → E → ℝ}

lemma EWeakKernel.wr1_measurable_left (h : EWeakKernel μ a q) (x : E) : Measurable (q x) :=
  h.meas.comp (measurable_const.prodMk measurable_id)

lemma EWeakKernel.wr1_measurable_right (h : EWeakKernel μ a q) (y : E) :
    Measurable (fun x => q x y) :=
  h.meas.comp (measurable_id.prodMk measurable_const)

lemma EWeakKernel.wr1_integrable_row (h : EWeakKernel μ a q) (x : E) : Integrable (q x) μ := by
  refine ⟨(h.wr1_measurable_left x).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have : ∀ y, ‖q x y‖ₑ = ENNReal.ofReal (q x y) := fun y => by
    rw [Real.enorm_eq_ofReal (h.nonneg x y)]
  simp_rw [this]
  exact lt_of_le_of_lt (h.row x) ENNReal.ofReal_lt_top

lemma EWeakKernel.wr1_integrable_col (h : EWeakKernel μ a q) (y : E) :
    Integrable (fun x => q x y) μ := by
  simpa [h.symm] using h.wr1_integrable_row y

lemma EWeakKernel.wr1_rowInt_nonneg (h : EWeakKernel μ a q) (x : E) : 0 ≤ rowIntE q μ x :=
  integral_nonneg fun y => h.nonneg x y

lemma EWeakKernel.wr1_rowInt_le (h : EWeakKernel μ a q) (ha : 0 ≤ a) (x : E) :
    rowIntE q μ x ≤ a := by
  have h1 : ENNReal.ofReal (rowIntE q μ x) = ∫⁻ y, ENNReal.ofReal (q x y) ∂μ :=
    ofReal_integral_eq_lintegral_ofReal (h.wr1_integrable_row x)
      (Filter.Eventually.of_forall fun y => h.nonneg x y)
  have := (h.row x)
  rw [← h1] at this
  exact (ENNReal.ofReal_le_ofReal_iff ha).1 this

lemma EWeakKernel.wr1_integral_col (h : EWeakKernel μ a q) (y : E) :
    ∫ x, q x y ∂μ = rowIntE q μ y := by
  unfold rowIntE; simp_rw [h.symm _ y]

lemma EWeakKernel.wr1_measurable_rowInt (h : EWeakKernel μ a q) : Measurable (rowIntE q μ) := by
  have : StronglyMeasurable (Function.uncurry q) := h.meas.stronglyMeasurable
  exact (this.integral_prod_right' (ν := μ)).measurable

end WK

lemma wr1_abs_exp_neg_sub_le {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    |Real.exp (-s) - Real.exp (-t)| ≤ |s - t| := by
  have key : ∀ s t : ℝ, 0 ≤ s → s ≤ t → Real.exp (-s) - Real.exp (-t) ≤ t - s := by
    intro s t hs hst
    have h1 : Real.exp (-s) ≤ 1 := by rw [Real.exp_le_one_iff]; linarith
    have h2 : -(t - s) + 1 ≤ Real.exp (-(t - s)) := Real.add_one_le_exp _
    have h3 : Real.exp (-t) = Real.exp (-s) * Real.exp (-(t - s)) := by
      rw [← Real.exp_add]; congr 1; ring
    have h4 : 0 ≤ Real.exp (-s) := (Real.exp_pos _).le
    have : Real.exp (-s) - Real.exp (-t) = Real.exp (-s) * (1 - Real.exp (-(t - s))) := by
      rw [h3]; ring
    rw [this]
    nlinarith
  rcases le_total s t with h | h
  · have := key s t hs h
    have h5 : Real.exp (-t) ≤ Real.exp (-s) := Real.exp_le_exp.2 (by linarith)
    rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]; linarith
  · have := key t s ht h
    have h5 : Real.exp (-s) ≤ Real.exp (-t) := Real.exp_le_exp.2 (by linarith)
    rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]; linarith




/-- pair sum -/
def pairSumE (q : E → E → ℝ) (X : (Fin N → E)) : ℝ :=
  ∑ k, ∑ l ∈ Finset.univ.erase k, q (X k) (X l)

/-- part of the pair sum not involving coordinate `i` -/
def pairRestE (q : E → E → ℝ) (i : Fin N) (x : (Fin N → E)) : ℝ :=
  ∑ k ∈ Finset.univ.erase i, ∑ l ∈ (Finset.univ.erase k).erase i, q (x k) (x l)

lemma wr1_pairSumE_update (q : E → E → ℝ) (hq : ∀ x y, q x y = q y x) (i : Fin N)
    (x : (Fin N → E)) (z : E) :
    pairSumE q (Function.update x i z)
      = 2 * ∑ l ∈ Finset.univ.erase i, q z (x l) + pairRestE q i x := by
  unfold pairSumE pairRestE
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have h1 : ∑ l ∈ Finset.univ.erase i, q (Function.update x i z i) (Function.update x i z l)
      = ∑ l ∈ Finset.univ.erase i, q z (x l) := by
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Function.update_self, Function.update_of_ne (Finset.ne_of_mem_erase hl)]
  have h2 : ∀ k ∈ Finset.univ.erase i,
      ∑ l ∈ Finset.univ.erase k, q (Function.update x i z k) (Function.update x i z l)
        = q (x k) z + ∑ l ∈ (Finset.univ.erase k).erase i, q (x k) (x l) := by
    intro k hk
    have hki : k ≠ i := Finset.ne_of_mem_erase hk
    have hi : i ∈ Finset.univ.erase k := Finset.mem_erase.2 ⟨hki.symm, Finset.mem_univ i⟩
    rw [← Finset.add_sum_erase _ _ hi]
    rw [Function.update_of_ne hki, Function.update_self]
    congr 1
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
  rw [h1, Finset.sum_congr rfl h2, Finset.sum_add_distrib]
  have h3 : ∑ k ∈ Finset.univ.erase i, q (x k) z = ∑ l ∈ Finset.univ.erase i, q z (x l) :=
    Finset.sum_congr rfl fun k _ => hq _ _
  rw [h3]; ring


/-- one-site factor -/
def vfunE (q : E → E → ℝ) (μ : Measure (E)) (N : ℕ) (β' : ℝ) (i : Fin N)
    (x : (Fin N → E)) (z : E) : ℝ :=
  Real.exp (-(β' / N) * ∑ l ∈ Finset.univ.erase i, q z (x l) + β' * rowIntE q μ z)

/-- the rest in the exponent -/
def restExpE (q : E → E → ℝ) (μ : Measure (E)) (N : ℕ) (β' : ℝ) (i : Fin N)
    (x : (Fin N → E)) : ℝ :=
  -(β' / (2 * N)) * pairRestE q i x + β' * ∑ k ∈ Finset.univ.erase i, rowIntE q μ (x k)
    - β' * N * (∫ x, ∫ y, q x y ∂μ ∂μ) / 2

lemma wr1_exponent_eq (q : E → E → ℝ) (μ : Measure (E)) (β' : ℝ) (X : (Fin N → E))
    (hN : 0 < N) :
    -β' * N * modEnergyE q X μ
      = -(β' / (2 * N)) * pairSumE q X + β' * ∑ k, rowIntE q μ (X k)
          - β' * N * (∫ x, ∫ y, q x y ∂μ ∂μ) / 2 := by
  unfold modEnergyE pairSumE rowIntE
  have : (N : ℝ) ≠ 0 := by positivity
  field_simp
  ring

lemma wr1_weight_update (q : E → E → ℝ) (hq : ∀ x y, q x y = q y x)
    (μ : Measure (E)) (β' : ℝ) (i : Fin N) (x : (Fin N → E)) (z : E) (hN : 0 < N) :
    pairWeightE q N β' μ (Function.update x i z)
      = ENNReal.ofReal (Real.exp (restExpE q μ N β' i x)) * ENNReal.ofReal (vfunE q μ N β' i x z) := by
  unfold pairWeightE vfunE
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  rw [wr1_exponent_eq q μ β' _ hN, wr1_pairSumE_update q hq]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have : (N : ℝ) ≠ 0 := by positivity
  simp only [restExpE, Function.update_self]
  have h : ∑ k ∈ Finset.univ.erase i, rowIntE q μ (Function.update x i z k)
      = ∑ k ∈ Finset.univ.erase i, rowIntE q μ (x k) :=
    Finset.sum_congr rfl fun k hk => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  rw [h]
  field_simp
  ring




section TVpart

lemma wr1_integrable_of_bdd' {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ]
    {f : E → ℝ} (hf : Measurable f) {M : ℝ}
    (hb : ∀ z, |f z| ≤ M) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable M (Filter.Eventually.of_forall fun z => by
    rw [Real.norm_eq_abs]; exact hb z)

lemma wr1_real_withDensity_ofReal {E : Type*} [MeasurableSpace E] (μ : Measure E) {f : E → ℝ}
    (h0 : ∀ z, 0 ≤ f z)
    (hint : Integrable f μ) {S : Set E} (hS : MeasurableSet S) :
    ((μ.withDensity (fun z => ENNReal.ofReal (f z))) S).toReal = ∫ z in S, f z ∂μ := by
  rw [withDensity_apply _ hS, ← ofReal_integral_eq_lintegral_ofReal hint.restrict
    (Filter.Eventually.of_forall h0)]
  exact ENNReal.toReal_ofReal (integral_nonneg h0)

lemma wr1_tv_normalized {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ]
    {u u' : E → ℝ} (hu : Measurable u)
    (hu' : Measurable u') (h0 : ∀ z, 0 ≤ u z) (h0' : ∀ z, 0 ≤ u' z) {M m : ℝ}
    (hM : ∀ z, u z ≤ M) (hM' : ∀ z, u' z ≤ M) (hm : 0 < m) (hZ : m ≤ ∫ z, u z ∂μ)
    (hZ' : m ≤ ∫ z, u' z ∂μ) (S : Set E) :
    |(∫ z in S, u z / ∫ z, u z ∂μ ∂μ) - ∫ z in S, u' z / ∫ z, u' z ∂μ ∂μ|
      ≤ 2 / m * ∫ z, |u z - u' z| ∂μ := by
  set Z := ∫ z, u z ∂μ with hZdef
  set Z' := ∫ z, u' z ∂μ with hZ'def
  have hZp : 0 < Z := lt_of_lt_of_le hm hZ
  have hZ'p : 0 < Z' := lt_of_lt_of_le hm hZ'
  have iu : Integrable u μ := wr1_integrable_of_bdd' μ hu (M := M) fun z => by
    rw [abs_of_nonneg (h0 z)]; exact hM z
  have iu' : Integrable u' μ := wr1_integrable_of_bdd' μ hu' (M := M) fun z => by
    rw [abs_of_nonneg (h0' z)]; exact hM' z
  have idiff : Integrable (fun z => |u z - u' z|) μ := (iu.sub iu').abs
  set D := ∫ z, |u z - u' z| ∂μ with hD
  have hD0 : 0 ≤ D := integral_nonneg fun z => abs_nonneg _
  have hZZ' : |Z' - Z| ≤ D := by
    have : Z' - Z = ∫ z, (u' z - u z) ∂μ := (integral_sub iu' iu).symm
    rw [this]
    calc |∫ z, (u' z - u z) ∂μ| ≤ ∫ z, |u' z - u z| ∂μ := abs_integral_le_integral_abs
      _ = D := by simp_rw [abs_sub_comm]; rfl
  have hpt : ∀ z, |u z / Z - u' z / Z'| ≤ |u z - u' z| / Z + u' z * (|Z' - Z| / (Z * Z')) := by
    intro z
    have : u z / Z - u' z / Z' = (u z - u' z) / Z + u' z * ((Z' - Z) / (Z * Z')) := by
      field_simp; ring
    rw [this]
    refine (abs_add_le _ _).trans ?_
    rw [abs_div, abs_of_pos hZp, abs_mul, abs_of_nonneg (h0' z), abs_div, abs_of_pos (mul_pos hZp hZ'p)]
  have ig : Integrable (fun z => |u z - u' z| / Z + u' z * (|Z' - Z| / (Z * Z'))) μ :=
    (idiff.div_const Z).add (iu'.mul_const _)
  have hint : ∫ z, (|u z - u' z| / Z + u' z * (|Z' - Z| / (Z * Z'))) ∂μ = D / Z + |Z' - Z| / Z := by
    rw [integral_add (idiff.div_const Z) (iu'.mul_const _), integral_div, integral_mul_const]
    congr 1
    rw [← hZ'def]; field_simp
  have e1 : (∫ z in S, u z / Z ∂μ) - ∫ z in S, u' z / Z' ∂μ = ∫ z in S, (u z / Z - u' z / Z') ∂μ :=
    (integral_sub (iu.div_const Z).restrict (iu'.div_const Z').restrict).symm
  rw [e1]
  have step : |∫ z in S, (u z / Z - u' z / Z') ∂μ| ≤ ∫ z, (|u z - u' z| / Z + u' z * (|Z' - Z| / (Z * Z'))) ∂μ := by
    calc |∫ z in S, (u z / Z - u' z / Z') ∂μ| ≤ ∫ z in S, |u z / Z - u' z / Z'| ∂μ :=
          abs_integral_le_integral_abs
      _ ≤ ∫ z in S, (|u z - u' z| / Z + u' z * (|Z' - Z| / (Z * Z'))) ∂μ :=
          integral_mono ((iu.div_const Z).sub (iu'.div_const Z')).abs.restrict ig.restrict hpt
      _ ≤ _ := setIntegral_le_integral ig (Filter.Eventually.of_forall fun z =>
            add_nonneg (div_nonneg (abs_nonneg _) hZp.le)
              (mul_nonneg (h0' z) (div_nonneg (abs_nonneg _) (mul_pos hZp hZ'p).le)))
  refine step.trans ?_
  rw [hint]
  have h1 : D / Z ≤ D / m := div_le_div_of_nonneg_left hD0 hm hZ
  have h2 : |Z' - Z| / Z ≤ D / m := by
    calc |Z' - Z| / Z ≤ D / Z := div_le_div_of_nonneg_right hZZ' hZp.le
      _ ≤ D / m := h1
  calc D / Z + |Z' - Z| / Z ≤ D / m + D / m := add_le_add h1 h2
    _ = 2 / m * D := by ring

end TVpart

section Site

set_option linter.unusedSectionVars false

variable {μ : Measure (E)} [IsProbabilityMeasure μ] {a : ℝ} {q : E → E → ℝ}

lemma EWeakKernel.wr1_measurable_vfun (h : EWeakKernel μ a q) (N : ℕ) (β' : ℝ) (i : Fin N)
    (x : (Fin N → E)) : Measurable (vfunE q μ N β' i x) := by
  unfold vfunE
  refine Real.measurable_exp.comp ?_
  refine Measurable.add ?_ (h.wr1_measurable_rowInt.const_mul _)
  exact (Finset.measurable_sum _ fun l _ => h.wr1_measurable_right (x l)).const_mul _

lemma wr1_vfunE_pos (N : ℕ) (β' : ℝ) (i : Fin N) (x : (Fin N → E)) (z : E) :
    0 < vfunE q μ N β' i x z := Real.exp_pos _

lemma EWeakKernel.wr1_vfun_le (h : EWeakKernel μ a q) (ha : 0 ≤ a) {β' : ℝ} (hβ : 0 ≤ β') (N : ℕ)
    (i : Fin N) (x : (Fin N → E)) (z : E) :
    vfunE q μ N β' i x z ≤ Real.exp (β' * a) := by
  unfold vfunE
  refine Real.exp_le_exp.2 ?_
  have h1 : 0 ≤ ∑ l ∈ Finset.univ.erase i, q z (x l) :=
    Finset.sum_nonneg fun l _ => h.nonneg _ _
  have h2 : 0 ≤ β' / N := div_nonneg hβ (Nat.cast_nonneg N)
  have h3 : β' * rowIntE q μ z ≤ β' * a := mul_le_mul_of_nonneg_left (h.wr1_rowInt_le ha z) hβ
  nlinarith

lemma EWeakKernel.wr1_integral_vfun_ge (h : EWeakKernel μ a q) (ha : 0 ≤ a) {β' : ℝ} (hβ : 0 ≤ β')
    {N : ℕ} (hN : 0 < N) (i : Fin N) (x : (Fin N → E)) :
    Real.exp (-(β' * a)) ≤ ∫ z, vfunE q μ N β' i x z ∂μ := by
  set t : E → ℝ := fun z =>
    -(β' / N) * ∑ l ∈ Finset.univ.erase i, q z (x l) + β' * rowIntE q μ z with ht
  have hvt : ∀ z, vfunE q μ N β' i x z = Real.exp (t z) := fun z => rfl
  set c0 : ℝ := -(β' * a) with hc0
  have ivf : Integrable (vfunE q μ N β' i x) μ :=
    wr1_integrable_of_bdd' μ (h.wr1_measurable_vfun N β' i x) (M := Real.exp (β' * a)) fun z => by
      rw [abs_of_pos (wr1_vfunE_pos N β' i x z)]; exact h.wr1_vfun_le ha hβ N i x z
  have iH : Integrable (rowIntE q μ) μ :=
    wr1_integrable_of_bdd' μ h.wr1_measurable_rowInt (M := a) fun z => by
      rw [abs_of_nonneg (h.wr1_rowInt_nonneg z)]; exact h.wr1_rowInt_le ha z
  have it : Integrable t μ := by
    refine Integrable.add ?_ (iH.const_mul _)
    exact (integrable_finsetSum _ fun l _ => h.wr1_integrable_col (x l)).const_mul _
  have hpt : ∀ z, Real.exp c0 * (1 + (t z - c0)) ≤ vfunE q μ N β' i x z := by
    intro z
    have := Real.add_one_le_exp (t z - c0)
    have h2 : Real.exp (t z) = Real.exp c0 * Real.exp (t z - c0) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hvt, h2]
    have := Real.exp_pos c0
    nlinarith
  have hint : ∫ z, Real.exp c0 * (1 + (t z - c0)) ∂μ ≤ ∫ z, vfunE q μ N β' i x z ∂μ :=
    integral_mono ((integrable_const _).add (it.sub (integrable_const _)) |>.const_mul _) ivf hpt
  refine le_trans ?_ hint
  have e1 : ∫ z, Real.exp c0 * (1 + (t z - c0)) ∂μ = Real.exp c0 * (1 + (∫ z, t z ∂μ - c0)) := by
    rw [integral_const_mul, integral_add (f := fun _ => (1:ℝ)) (g := fun z => t z - c0)
      (integrable_const _) (it.sub (integrable_const _)),
      integral_sub (f := t) (g := fun _ => c0) it (integrable_const _)]
    simp
  rw [e1]
  have ht0 : c0 ≤ ∫ z, t z ∂μ := by
    have e2 : ∫ z, t z ∂μ = -(β' / N) * ∑ l ∈ Finset.univ.erase i, rowIntE q μ (x l)
        + β' * ∫ z, rowIntE q μ z ∂μ := by
      rw [ht]
      simp only
      rw [integral_add ((integrable_finsetSum _ fun l _ => h.wr1_integrable_col (x l)).const_mul _)
        (iH.const_mul _), integral_const_mul, integral_const_mul, integral_finsetSum _
        fun l _ => h.wr1_integrable_col (x l)]
      simp_rw [h.wr1_integral_col]
    rw [e2]
    have h1 : ∑ l ∈ Finset.univ.erase i, rowIntE q μ (x l) ≤ N * a := by
      calc ∑ l ∈ Finset.univ.erase i, rowIntE q μ (x l)
          ≤ ∑ l ∈ Finset.univ.erase i, a := Finset.sum_le_sum fun l _ => h.wr1_rowInt_le ha _
        _ = ((Finset.univ.erase i).card : ℝ) * a := by simp
        _ ≤ N * a := by
          refine mul_le_mul_of_nonneg_right ?_ ha
          rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
          simp
    have h2 : 0 ≤ ∫ z, rowIntE q μ z ∂μ := integral_nonneg fun z => h.wr1_rowInt_nonneg z
    have h3 : 0 ≤ β' / N := div_nonneg hβ (Nat.cast_nonneg N)
    have h4 : -(β' / N) * ∑ l ∈ Finset.univ.erase i, rowIntE q μ (x l) ≥ -(β' / N) * (N * a) := by
      nlinarith
    have h5 : -(β' / N) * (N * a) = -(β' * a) := by
      have : (N : ℝ) ≠ 0 := by positivity
      field_simp
    have : 0 ≤ β' * ∫ z, rowIntE q μ z ∂μ := mul_nonneg hβ h2
    rw [hc0]; linarith
  have := Real.exp_pos c0
  nlinarith

end Site

section Site2

set_option linter.unusedSectionVars false

variable {μ : Measure (E)} [IsProbabilityMeasure μ] {a : ℝ} {q : E → E → ℝ}

lemma EWeakKernel.wr1_measurable_pairWeight (h : EWeakKernel μ a q) (N : ℕ) (β' : ℝ) :
    Measurable (pairWeightE q N β' μ) := by
  unfold pairWeightE
  refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ?_)
  unfold modEnergyE
  have h1 : Measurable (fun X : (Fin N → E) => ∑ i, ∑ j ∈ Finset.univ.erase i, q (X i) (X j)) :=
    Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => by
      have := h.meas.comp (f := fun X : (Fin N → E) => (X i, X j))
        ((measurable_pi_apply i).prodMk (measurable_pi_apply j))
      exact this
  have h2 : Measurable (fun X : (Fin N → E) => ∑ i, ∫ y, q (X i) y ∂μ) :=
    Finset.measurable_sum _ fun i _ => h.wr1_measurable_rowInt.comp (measurable_pi_apply i)
  exact (((h1.const_mul _).sub (h2.const_mul _)).add_const _).const_mul _

lemma EWeakKernel.wr1_siteKernel_eq (h : EWeakKernel μ a q) (ha : 0 ≤ a) {β' : ℝ} (hβ : 0 ≤ β')
    {N : ℕ} (hN : 0 < N) (i : Fin N) (x : (Fin N → E)) :
    External.siteKernel μ (pairWeightE q N β' μ) i x
      = μ.withDensity (fun z => ENNReal.ofReal (vfunE q μ N β' i x z / ∫ w, vfunE q μ N β' i x w ∂μ)) := by
  rw [External.siteKernel_apply (h.wr1_measurable_pairWeight N β')]
  set V := ∫ w, vfunE q μ N β' i x w ∂μ with hV
  have hVp : 0 < V := lt_of_lt_of_le (Real.exp_pos _) (h.wr1_integral_vfun_ge ha hβ hN i x)
  have ivf : Integrable (vfunE q μ N β' i x) μ :=
    wr1_integrable_of_bdd' μ (h.wr1_measurable_vfun N β' i x) (M := Real.exp (β' * a)) fun z => by
      rw [abs_of_pos (wr1_vfunE_pos N β' i x z)]; exact h.wr1_vfun_le ha hβ N i x z
  have hnorm : External.normalizer μ (pairWeightE q N β' μ) i x
      = ENNReal.ofReal (Real.exp (restExpE q μ N β' i x)) * ENNReal.ofReal V := by
    unfold External.normalizer
    simp_rw [wr1_weight_update q h.symm μ β' i x _ hN]
    have hmv : Measurable fun z => ENNReal.ofReal (vfunE q μ N β' i x z) :=
      ENNReal.measurable_ofReal.comp (h.wr1_measurable_vfun N β' i x)
    rw [lintegral_const_mul _ hmv,
      ← ofReal_integral_eq_lintegral_ofReal ivf (Filter.Eventually.of_forall fun z => (wr1_vfunE_pos N β' i x z).le)]
  rw [hnorm]
  congr 1
  funext z
  rw [wr1_weight_update q h.symm μ β' i x z hN]
  set c := ENNReal.ofReal (Real.exp (restExpE q μ N β' i x)) with hc
  have hc0 : c ≠ 0 := (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have hct : c ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [ENNReal.mul_inv (Or.inl hc0) (Or.inl hct)]
  rw [ENNReal.ofReal_div_of_pos hVp, div_eq_mul_inv]
  calc c * ENNReal.ofReal (vfunE q μ N β' i x z) * (c⁻¹ * (ENNReal.ofReal V)⁻¹)
      = (c * c⁻¹) * (ENNReal.ofReal (vfunE q μ N β' i x z) * (ENNReal.ofReal V)⁻¹) := by ring
    _ = _ := by rw [ENNReal.mul_inv_cancel hc0 hct, one_mul]

end Site2
end HRS.MS.Wr
