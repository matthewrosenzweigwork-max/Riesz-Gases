import HRS.MS.WrMargAux2

/-!
# HRS.MS.WrPresAux1 -- energy layer of the weak pressure bound (WR-5, part 1)

Packet WR-5 of `docs/SUPP_FOUND_PACKETS.md` (Track D).  Port, to an arbitrary measurable space `E`
(the Euclidean case is `E = Euc d`), of the torus block `HRS/Energy/WeakReference.lean:5030-5250`:

* `enGE q μ N X = N F_N^q(X, μ)` (`modEnergyE`), its measurability, the lower bound `-(N a)`,
  `∫ enGE = -(1/2) ∬ q`, integrability, `∬ q ≤ a`;
* `pairPartitionE q N t μ = ofReal (expZ P enGE 0 t)` (Laplace transform of the energy), the Gibbs
  integration formula, `vFun = variance` under the Gibbs law `pairGibbsLawE`;
* `EWeakKernel.pairPartition_upper_E`: from a variance bound `Var_{R_t} G ≤ V t` along the path
  `t ∈ (0, β]` and `W' = V`, `W 0 = 0`, one gets `K^q_{N,β}(μ) ≤ exp (β (a/2 + W β))`.

Hypotheses are exactly those of the torus statements (`EWeakKernel` replaces `WeakKernel`); the generic
lemmas `HRS.WeakRef.logZ_upper`, `expZ_zero_pos`, `integrable_expMoment` are reused.
Helper lemmas carry the prefix `wr5_`.
-/

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Function Set
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wr

variable {E : Type*} [MeasurableSpace E]

/-- The energy `G = N F_N^q(·, μ)`. -/
def enGE (q : E → E → ℝ) (μ : Measure E) (N : ℕ) (X : Fin N → E) : ℝ :=
  N * modEnergyE q X μ

section Basic

variable {μ : Measure E} [IsProbabilityMeasure μ] {a : ℝ} {q : E → E → ℝ}

lemma EWeakKernel.wr5_measurable_energy (h : EWeakKernel μ a q) (N : ℕ) :
    Measurable (fun X : Fin N → E => modEnergyE q X μ) := by
  unfold modEnergyE
  have h1 : Measurable (fun X : Fin N → E => ∑ i, ∑ j ∈ Finset.univ.erase i, q (X i) (X j)) :=
    Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => by
      have := h.meas.comp (f := fun X : Fin N → E => (X i, X j))
        ((measurable_pi_apply i).prodMk (measurable_pi_apply j))
      exact this
  have h2 : Measurable (fun X : Fin N → E => ∑ i, ∫ y, q (X i) y ∂μ) :=
    Finset.measurable_sum _ fun i _ => h.wr1_measurable_rowInt.comp (measurable_pi_apply i)
  exact (((h1.const_mul _).sub (h2.const_mul _)).add_const _)

lemma EWeakKernel.wr5_measurable_enG (h : EWeakKernel μ a q) (N : ℕ) : Measurable (enGE q μ N) :=
  (h.wr5_measurable_energy N).const_mul _

lemma EWeakKernel.wr5_enG_ge (h : EWeakKernel μ a q) (ha : 0 ≤ a) {N : ℕ} (hN : 0 < N)
    (X : Fin N → E) : -((N : ℝ) * a) ≤ enGE q μ N X := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  unfold enGE modEnergyE
  have h1 : 0 ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, q (X i) (X j) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => h.nonneg _ _
  have h2 : ∑ i, ∫ y, q (X i) y ∂μ ≤ N * a := by
    have : ∀ i, ∫ y, q (X i) y ∂μ ≤ a := fun i => h.wr1_rowInt_le ha (X i)
    calc ∑ i, ∫ y, q (X i) y ∂μ ≤ ∑ _i : Fin N, a := Finset.sum_le_sum fun i _ => this i
      _ = N * a := by simp
  have h3 : 0 ≤ ∫ x, ∫ y, q x y ∂μ ∂μ :=
    integral_nonneg fun x => integral_nonneg fun y => h.nonneg _ _
  have h4 : 0 ≤ 1 / (2 * (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, q (X i) (X j) := by
    positivity
  have h5 : 1 / (N : ℝ) * ∑ i, ∫ y, q (X i) y ∂μ ≤ a := by
    calc 1 / (N : ℝ) * ∑ i, ∫ y, q (X i) y ∂μ ≤ 1 / (N : ℝ) * (N * a) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = a := by field_simp
  have : -a ≤ 1 / (2 * (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, q (X i) (X j)
      - 1 / (N : ℝ) * ∑ i, ∫ y, q (X i) y ∂μ + 1 / 2 * ∫ x, ∫ y, q x y ∂μ ∂μ := by linarith
  calc -((N : ℝ) * a) = N * (-a) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left this hN'.le

lemma EWeakKernel.wr5_integral_enG (h : EWeakKernel μ a q) {N : ℕ} (hN : 1 ≤ N) :
    ∫ X, enGE q μ N X ∂(Measure.pi fun _ : Fin N => μ)
      = -(1 / 2) * ∫ p : E × E, q p.1 p.2 ∂(μ.prod μ) := by
  unfold enGE
  rw [integral_const_mul, h.wr1_integral_energy hN]
  have : (N : ℝ) ≠ 0 := by positivity
  field_simp

lemma EWeakKernel.wr5_integrable_enG (h : EWeakKernel μ a q) (N : ℕ) :
    Integrable (enGE q μ N) (Measure.pi fun _ : Fin N => μ) :=
  (h.wr1_integrable_energy N).const_mul _

lemma EWeakKernel.wr5_prod_le (h : EWeakKernel μ a q) (ha : 0 ≤ a) :
    ∫ p : E × E, q p.1 p.2 ∂(μ.prod μ) ≤ a := by
  rw [integral_prod _ h.wr1_integrable_prod]
  calc ∫ x, ∫ y, q (x, y).1 (x, y).2 ∂μ ∂μ ≤ ∫ _x, a ∂μ :=
        integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun x => integral_nonneg fun y => h.nonneg _ _)
          (integrable_const _) (Filter.Eventually.of_forall fun x => h.wr1_rowInt_le ha x)
    _ = a := by simp

lemma EWeakKernel.wr5_prod_nonneg (h : EWeakKernel μ a q) :
    0 ≤ ∫ p : E × E, q p.1 p.2 ∂(μ.prod μ) :=
  integral_nonneg fun p => h.nonneg _ _

/-- The partition function is the Laplace transform of the energy. -/
lemma EWeakKernel.wr5_pairPartition_eq (h : EWeakKernel μ a q) (ha : 0 ≤ a) {t : ℝ} (ht : 0 < t)
    {N : ℕ} (hN : 0 < N) :
    pairPartitionE q N t μ
      = ENNReal.ofReal (HRS.WeakRef.expZ (Measure.pi fun _ : Fin N => μ) (enGE q μ N) 0 t) := by
  have hK0 : 0 ≤ (N : ℝ) * a := by positivity
  have hi := HRS.WeakRef.integrable_expMoment (Measure.pi fun _ : Fin N => μ)
    (h.wr5_measurable_enG N) hK0 (h.wr5_enG_ge ha hN) 0 ht
  unfold HRS.WeakRef.expZ pairPartitionE
  simp only [pow_zero, one_mul] at hi ⊢
  rw [ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)]
  refine lintegral_congr fun X => ?_
  unfold pairWeightE enGE
  congr 2
  ring

lemma EWeakKernel.wr5_integral_gibbs (h : EWeakKernel μ a q) (ha : 0 ≤ a) {t : ℝ} (ht : 0 < t)
    {N : ℕ} (hN : 0 < N) (g : (Fin N → E) → ℝ) :
    ∫ X, g X ∂(pairGibbsLawE q N t μ)
      = ∫ X, (Real.exp (-(t * enGE q μ N X))
            / HRS.WeakRef.expZ (Measure.pi fun _ : Fin N => μ) (enGE q μ N) 0 t) * g X
          ∂(Measure.pi fun _ : Fin N => μ) := by
  set Pm : Measure (Fin N → E) := Measure.pi fun _ : Fin N => μ with hPm
  set Z := HRS.WeakRef.expZ Pm (enGE q μ N) 0 t with hZ
  have hK0 : 0 ≤ (N : ℝ) * a := by positivity
  have hZpos : 0 < Z :=
    HRS.WeakRef.expZ_zero_pos Pm (enGE q μ N) (h.wr5_measurable_enG N) hK0 (h.wr5_enG_ge ha hN) ht
  have hpp := h.wr5_pairPartition_eq ha ht hN
  unfold pairGibbsLawE
  rw [integral_withDensity_eq_integral_toReal_smul]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
    simp only [smul_eq_mul]
    congr 1
    rw [hpp, ENNReal.toReal_div, ENNReal.toReal_ofReal hZpos.le]
    unfold pairWeightE
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
    simp only [enGE]
    congr 3
    ring
  · exact (h.wr1_measurable_pairWeight N t).div_const _
  · refine Filter.Eventually.of_forall fun X => ?_
    rw [hpp]
    refine ENNReal.div_lt_top ENNReal.ofReal_ne_top ?_
    exact (ENNReal.ofReal_pos.2 hZpos).ne'

lemma EWeakKernel.wr5_vFun_eq (h : EWeakKernel μ a q) (ha : 0 ≤ a) {t : ℝ} (ht : 0 < t)
    {N : ℕ} (hN : 0 < N) :
    HRS.WeakRef.vFun (Measure.pi fun _ : Fin N => μ) (enGE q μ N) t
      = variance (enGE q μ N) (pairGibbsLawE q N t μ) := by
  set Pm : Measure (Fin N → E) := Measure.pi fun _ : Fin N => μ with hPm
  set G := enGE q μ N with hG
  set Z := HRS.WeakRef.expZ Pm G 0 t with hZ
  have hK0 : 0 ≤ (N : ℝ) * a := by positivity
  have hGm := h.wr5_measurable_enG N
  have hZpos : 0 < Z := HRS.WeakRef.expZ_zero_pos Pm G hGm hK0 (h.wr5_enG_ge ha hN) ht
  have hI := fun k => HRS.WeakRef.integrable_expMoment Pm hGm hK0 (h.wr5_enG_ge ha hN) k ht
  set E1 := HRS.WeakRef.expZ Pm G 1 t with hE1
  set E2 := HRS.WeakRef.expZ Pm G 2 t with hE2
  set m : ℝ := E1 / Z with hm
  have key := h.wr5_integral_gibbs ha ht hN G
  rw [← hG, ← hPm, ← hZ] at key
  have hmean : ∫ X, G X ∂(pairGibbsLawE q N t μ) = m := by
    rw [key]
    have : ∀ X, Real.exp (-(t * G X)) / Z * G X = (1 / Z) * (G X ^ 1 * Real.exp (-(t * G X))) := by
      intro X; ring
    simp_rw [this]
    rw [integral_const_mul]
    show 1 / Z * E1 = _
    rw [hm]; ring
  have key2 := h.wr5_integral_gibbs ha ht hN (fun X => (G X - m) ^ 2)
  rw [← hG, ← hPm, ← hZ] at key2
  rw [variance_eq_integral hGm.aemeasurable, hmean, key2]
  have e : ∀ X, Real.exp (-(t * G X)) / Z * (G X - m) ^ 2
      = (1 / Z) * (G X ^ 2 * Real.exp (-(t * G X))) - (2 * m / Z) * (G X ^ 1 * Real.exp (-(t * G X)))
        + (m ^ 2 / Z) * (G X ^ 0 * Real.exp (-(t * G X))) := by
    intro X; ring
  simp_rw [e]
  have i2 : Integrable (fun X => 1 / Z * (G X ^ 2 * Real.exp (-(t * G X)))) Pm := (hI 2).const_mul _
  have i1 : Integrable (fun X => 2 * m / Z * (G X ^ 1 * Real.exp (-(t * G X)))) Pm :=
    (hI 1).const_mul _
  have i0 : Integrable (fun X => m ^ 2 / Z * (G X ^ 0 * Real.exp (-(t * G X)))) Pm :=
    (hI 0).const_mul _
  have i21 : Integrable (fun X => 1 / Z * (G X ^ 2 * Real.exp (-(t * G X)))
      - 2 * m / Z * (G X ^ 1 * Real.exp (-(t * G X)))) Pm := i2.sub i1
  rw [integral_add i21 i0, integral_sub i2 i1, integral_const_mul, integral_const_mul,
    integral_const_mul]
  show E2 / Z - (E1 / Z) ^ 2 = 1 / Z * E2 - 2 * m / Z * E1 + m ^ 2 / Z * Z
  rw [← hm]
  have hE : E1 = m * Z := by rw [hm]; field_simp
  field_simp
  linear_combination (2 * m) * hE

/-- Upper bound of the partition function from a variance bound along the path `t ∈ (0, β]`. -/
theorem EWeakKernel.pairPartition_upper_E (h : EWeakKernel μ a q) (ha : 0 ≤ a) {N : ℕ} (hN : 0 < N)
    {β : ℝ} (hβ : 0 < β) {V W : ℝ → ℝ}
    (hv : ∀ t ∈ Ioc 0 β, variance (enGE q μ N) (pairGibbsLawE q N t μ) ≤ V t)
    (hV0 : ∀ t ∈ Ioc 0 β, 0 ≤ V t)
    (hW : ∀ t, 0 < t → HasDerivAt W (V t) t) (hWc : ContinuousWithinAt W (Ici 0) 0)
    (hW0 : W 0 = 0) :
    pairPartitionE q N β μ ≤ ENNReal.ofReal (Real.exp (β * (a / 2 + W β))) := by
  set Pm : Measure (Fin N → E) := Measure.pi fun _ : Fin N => μ with hPm
  have hK0 : 0 ≤ (N : ℝ) * a := by positivity
  have hlog := HRS.WeakRef.logZ_upper Pm (enGE q μ N) (h.wr5_measurable_enG N)
    (h.wr5_integrable_enG N) hK0 (h.wr5_enG_ge ha hN) hβ (V := V) (W := W)
    (fun t ht => by rw [h.wr5_vFun_eq ha ht.1 hN]; exact hv t ht) hV0 hW hWc hW0
  have hZpos : 0 < HRS.WeakRef.expZ Pm (enGE q μ N) 0 β :=
    HRS.WeakRef.expZ_zero_pos Pm (enGE q μ N) (h.wr5_measurable_enG N) hK0
      (h.wr5_enG_ge ha hN) hβ
  rw [h.wr5_pairPartition_eq ha hβ hN]
  refine ENNReal.ofReal_le_ofReal ?_
  have hexp : HRS.WeakRef.expZ Pm (enGE q μ N) 0 β
      = Real.exp (HRS.WeakRef.logZ Pm (enGE q μ N) β) := by
    unfold HRS.WeakRef.logZ; rw [Real.exp_log hZpos]
  rw [hexp]
  refine Real.exp_le_exp.2 (hlog.trans ?_)
  rw [h.wr5_integral_enG hN]
  have := h.wr5_prod_le ha
  have h0 := h.wr5_prod_nonneg
  have : β * (-(-(1 / 2) * ∫ p : E × E, q p.1 p.2 ∂(μ.prod μ)) + W β)
      ≤ β * (a / 2 + W β) := by
    refine mul_le_mul_of_nonneg_left ?_ hβ.le
    linarith
  exact this

end Basic

end HRS.MS.Wr
