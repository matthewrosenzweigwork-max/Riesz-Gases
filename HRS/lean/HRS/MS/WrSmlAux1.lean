import HRS.MS.WrAlgAux1
import HRS.MS.WrDiagAux1

/-!
# HRS.MS.WrSmlAux1 -- PSD diagonal bound and coarse energy lower bounds (WR-12a, part 1)

Packet WR-12a of `docs/WR_B_PLAN.md` (T5), namespace `HRS.MS.Wr`, helper prefix `wr12_`.

* `wr12_setK d s S`: the partial heat integral `∫_{t ∈ S} psd3_F d s t x`; `wr12_bandK a b` is the case
  `S = Ioc a b` (`kTau a = bandK a b + kTau b` for `0 < a ≤ b`).  For measurable `S ⊆ (a, ∞)`, `a > 0`:
  continuity, evenness, `0 ≤ K ≤ K 0 ≤ kTau a 0` and positive definiteness on finite signed measures
  (`wr12_setK_posdef`; `wr12_bandPosdef` is the band case, a copy of `kTau_posdef`).
* `wr12_psd_diag_bound`: the abstract (bounded, measurable, even, positive definite) version of
  `kTau_diag_bound`: `-(1/2) k 0 ≤ N * pairEnergy (k (x-y)) X μ`.
* `wr12_energy_split_lower`: if `h = q + P` off the origin with `q` a weak kernel (row mass `≤ a`)
  and `P` a bounded PSD kernel, then `-(N a) - P(0)/2 ≤ N * pairEnergy h X μ` at injective configurations.
* `euc_energy_lower` (item 2): `-(C N^{s/d}) ≤ N * pairEnergy (g (x-y)) X μ` for injective `X`, `ρ ≤ M`;
  `euc_energy_lower_q` the same for the kernel `q_τ` of `R0`.

Adjustments with respect to the plan: the Euclidean "off the collision set" is the hypothesis
`∀ i j, i ≠ j → X i ≠ X j` (the torus `collisionSet` does not exist here); `C` is quantified before `ρ`.
-/

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace HRS.MS.Wr

open HRS.Whole HRS.MS.Psd

variable {d N : ℕ}

/-! ### Partial heat integrals and their positive definiteness -/

/-- The partial heat integral `∫_{t ∈ S} psd3_F d s t x`. -/
def wr12_setK (d : ℕ) (s : ℝ) (S : Set ℝ) (x : Euc d) : ℝ := ∫ t in S, psd3_F d s t x

/-- The band `∫_{(a,b]} psd3_F`. -/
def wr12_bandK (d : ℕ) (s a b : ℝ) (x : Euc d) : ℝ := wr12_setK d s (Ioc a b) x

theorem wr12_setK_even {s : ℝ} {S : Set ℝ} (w : Euc d) :
    wr12_setK d s S (-w) = wr12_setK d s S w := by
  unfold wr12_setK psd3_F heatKerE
  simp only [norm_neg]

section SetK

variable {s : ℝ} (hs : 0 < s) {a : ℝ} (ha : 0 < a) {S : Set ℝ}

include hs ha

theorem wr12_setK_majorant (hS : S ⊆ Ioi a) :
    IntegrableOn (fun t : ℝ => psd3_F d s t 0) S :=
  (psd3_F_zero_integrableOn (d := d) hs ha).mono_set hS

theorem wr12_setK_integrableOn (hS : S ⊆ Ioi a) (x : Euc d) :
    IntegrableOn (fun t : ℝ => psd3_F d s t x) S :=
  (psd3_F_integrableOn hs ha x).mono_set hS

theorem wr12_setK_nonneg (hSm : MeasurableSet S) (hS : S ⊆ Ioi a) (x : Euc d) :
    0 ≤ wr12_setK d s S x :=
  setIntegral_nonneg hSm fun t ht => psd3_F_nonneg hs (lt_trans ha (hS ht)).le x

theorem wr12_setK_le_zero (hSm : MeasurableSet S) (hS : S ⊆ Ioi a) (x : Euc d) :
    wr12_setK d s S x ≤ wr12_setK d s S 0 :=
  setIntegral_mono_on (wr12_setK_integrableOn hs ha hS x) (wr12_setK_majorant hs ha hS) hSm
    fun t ht => psd3_F_le_zero hs (lt_trans ha (hS ht)) x

theorem wr12_setK_zero_le (hSm : MeasurableSet S) (hS : S ⊆ Ioi a) :
    wr12_setK d s S 0 ≤ kTau d s a 0 := by
  unfold wr12_setK kTau
  refine setIntegral_mono_set (psd3_F_zero_integrableOn (d := d) hs ha) ?_ (Eventually.of_forall hS)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact psd3_F_nonneg hs (lt_trans ha ht).le 0

theorem wr12_setK_abs_le (hSm : MeasurableSet S) (hS : S ⊆ Ioi a) (x : Euc d) :
    |wr12_setK d s S x| ≤ kTau d s a 0 := by
  rw [abs_of_nonneg (wr12_setK_nonneg hs ha hSm hS x)]
  exact (wr12_setK_le_zero hs ha hSm hS x).trans (wr12_setK_zero_le hs ha hSm hS)

theorem wr12_setK_continuous (hSm : MeasurableSet S) (hS : S ⊆ Ioi a) :
    Continuous (wr12_setK d s S : Euc d → ℝ) := by
  unfold wr12_setK
  refine continuous_of_dominated (bound := fun t => psd3_F d s t 0)
    (fun x => (psd3_F_meas_t (d := d) s x).aestronglyMeasurable) (fun x => ?_)
    (wr12_setK_majorant hs ha hS) ?_
  · filter_upwards [ae_restrict_mem hSm] with t ht
    have : 0 < t := lt_trans ha (hS ht)
    rw [Real.norm_eq_abs, abs_of_nonneg (psd3_F_nonneg hs this.le x)]
    exact psd3_F_le_zero hs this x
  · refine Eventually.of_forall fun t => ?_
    unfold psd3_F heatKerE
    fun_prop

/-- Positive definiteness of the partial heat integral on every finite signed measure `u ν`. -/
theorem wr12_setK_posdef (hSm : MeasurableSet S) (hS : S ⊆ Ioi a) {ν : Measure (Euc d)}
    [IsFiniteMeasure ν] {u : Euc d → ℝ} (hum : Measurable u) (hu : Integrable u ν) :
    0 ≤ ∫ z : Euc d × Euc d, wr12_setK d s S (z.1 - z.2) * (u z.1 * u z.2) ∂(ν.prod ν) := by
  set μt : Measure ℝ := volume.restrict S with hμt
  set Φ : (Euc d × Euc d) × ℝ → ℝ := fun p =>
    psd3_F d s p.2 (p.1.1 - p.1.2) * (u p.1.1 * u p.1.2) with hΦ
  have hΦm : Measurable Φ := by
    have h1 : Measurable (fun p : (Euc d × Euc d) × ℝ => (p.2, p.1.1 - p.1.2)) :=
      measurable_snd.prodMk ((measurable_fst.comp measurable_fst).sub
        (measurable_snd.comp measurable_fst))
    exact ((psd3_F_meas (d := d) s).comp h1).mul
      ((hum.comp (measurable_fst.comp measurable_fst)).mul
        (hum.comp (measurable_snd.comp measurable_fst)))
  have hmaj : Integrable (fun z : Euc d × Euc d => |u z.1| * |u z.2|) (ν.prod ν) :=
    hu.abs.mul_prod hu.abs
  have hmaj2 := hmaj.mul_prod (wr12_setK_majorant (d := d) hs ha hS)
  have hΦi : Integrable Φ ((ν.prod ν).prod μt) := by
    refine Integrable.mono' hmaj2 hΦm.aestronglyMeasurable ?_
    have h2 : ∀ᵐ p ∂((ν.prod ν).prod μt), 0 < p.2 := by
      have hm : MeasurableSet {p : (Euc d × Euc d) × ℝ | 0 < p.2} :=
        measurableSet_lt measurable_const measurable_snd
      refine (Measure.ae_prod_mem_iff_ae_ae_mem hm).2 (Eventually.of_forall fun z => ?_)
      filter_upwards [ae_restrict_mem hSm] with t ht using lt_trans ha (hS ht)
    filter_upwards [h2] with p hp
    simp only [hΦ, Real.norm_eq_abs, abs_mul]
    rw [abs_of_nonneg (psd3_F_nonneg hs hp.le _)]
    calc psd3_F d s p.2 (p.1.1 - p.1.2) * (|u p.1.1| * |u p.1.2|)
        ≤ psd3_F d s p.2 0 * (|u p.1.1| * |u p.1.2|) := by
          gcongr; exact psd3_F_le_zero hs hp _
      _ = _ := by ring
  have step1 : ∀ z : Euc d × Euc d, wr12_setK d s S (z.1 - z.2) * (u z.1 * u z.2) =
      ∫ t, Φ (z, t) ∂μt := by
    intro z
    simp only [hΦ, wr12_setK, hμt]
    rw [integral_mul_const]
  rw [integral_congr_ae (Eventually.of_forall step1)]
  rw [integral_integral_swap (f := fun z t => Φ (z, t)) hΦi]
  refine setIntegral_nonneg hSm fun t ht => ?_
  have ht0 : 0 < t := lt_trans ha (hS ht)
  have e : ∀ z : Euc d × Euc d, Φ (z, t) = psd3_F d s t 0 *
      (Real.exp (-(1 / (4 * t)) * ‖z.1 - z.2‖ ^ 2) * u z.1 * u z.2) := by
    intro z
    simp only [hΦ]
    rw [psd3_F_eq_gauss ht0]
    ring
  simp only [e]
  rw [integral_const_mul]
  exact mul_nonneg (psd3_F_nonneg hs ht0.le 0)
    (HRS.Whole.Q34.gauss_posdef hum hu (by positivity : 0 < 1 / (4 * t)))

end SetK

/-- Positive definiteness of the band `∫_{(a,b]} psd3_F` (`0 < a`). -/
theorem wr12_bandPosdef {s : ℝ} (hs : 0 < s) {a b : ℝ} (ha : 0 < a) {ν : Measure (Euc d)}
    [IsFiniteMeasure ν] {u : Euc d → ℝ} (hum : Measurable u) (hu : Integrable u ν) :
    0 ≤ ∫ z : Euc d × Euc d, wr12_bandK d s a b (z.1 - z.2) * (u z.1 * u z.2) ∂(ν.prod ν) :=
  wr12_setK_posdef hs ha measurableSet_Ioc Ioc_subset_Ioi_self hum hu

/-- `kTau a = band(a,b) + kTau b` for `0 < a ≤ b`. -/
theorem wr12_kTau_eq_band_add {s : ℝ} (hs : 0 < s) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (x : Euc d) : kTau d s a x = wr12_bandK d s a b x + kTau d s b x := by
  unfold wr12_bandK wr12_setK kTau
  rw [← Set.Ioc_union_Ioi_eq_Ioi hab]
  refine setIntegral_union (Set.disjoint_left.2 fun t h1 h2 => absurd h1.2 (not_le.2 h2))
    measurableSet_Ioi ?_ ?_
  · exact (psd3_F_integrableOn hs ha x).mono_set Ioc_subset_Ioi_self
  · exact (psd3_F_integrableOn hs ha x).mono_set (Ioi_subset_Ioi hab)

/-! ### Abstract diagonal bound -/

/-- **Abstract `kTau_diag_bound`.**  For a bounded measurable even kernel `k` that is positive
definite on every finite signed measure `u ν`, `-(1/2) k 0 ≤ N * pairEnergy (k (x-y)) X μ`
for every probability measure `μ` (atoms allowed) and every configuration `X`. -/
theorem wr12_psd_diag_bound {k : Euc d → ℝ} (hkm : Measurable k) {C0 : ℝ}
    (hC : ∀ w, |k w| ≤ C0) (hsymm : ∀ w, k (-w) = k w)
    (hpos : ∀ (ν : Measure (Euc d)) [IsFiniteMeasure ν] (u : Euc d → ℝ), Measurable u →
      Integrable u ν → 0 ≤ ∫ z : Euc d × Euc d, k (z.1 - z.2) * (u z.1 * u z.2) ∂(ν.prod ν))
    (hN : 1 ≤ N) (μ : Measure (Euc d)) [IsProbabilityMeasure μ] (X : EucConfig d N) :
    -(1 / 2) * k 0 ≤ (N : ℝ) * pairEnergy (fun x y => k (x - y)) X μ := by
  haveI := wr7_emp_prob hN X
  set α : Measure (Euc d) := HRS.Whole.empirical X with hαdef
  have hint : ∀ (a b : Measure (Euc d)) [IsFiniteMeasure a] [IsFiniteMeasure b],
      Integrable (fun z : Euc d × Euc d => k (z.1 - z.2)) (a.prod b) := fun a b _ _ =>
    wr7_int_of_bound hkm C0 (fun _ => 0)
      (integrable_zero _ _ _) (integrable_zero _ _ _) (fun x y => by
        simpa using hC (x - y))
  have hE := wr7_pairEnergy_eq hN μ k hsymm X (hint α α) (hint α μ) (hint μ μ)
  have hpos' := hpos (α + μ) _ (wr7_u_meas (α := α) (β := μ) (ν := α + μ))
    (wr7_u_int (α := α) (β := μ) (ν := α + μ))
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [hE]
  set T := ∫ z : Euc d × Euc d, k (z.1 - z.2) *
      (((α.rnDeriv (α + μ) z.1).toReal - (μ.rnDeriv (α + μ) z.1).toReal) *
        ((α.rnDeriv (α + μ) z.2).toReal - (μ.rnDeriv (α + μ) z.2).toReal))
        ∂((α + μ).prod (α + μ)) with hT
  have h0 : (N : ℝ) * ((1 / 2) * T - k 0 / (2 * N)) = (N : ℝ) / 2 * T - k 0 / 2 := by
    field_simp
  rw [h0]
  nlinarith [mul_nonneg hN'.le hpos']

/-! ### Elementary facts on `qTau` and the probability measure `ρ dx` -/

theorem wr12_qTau_meas {s τ : ℝ} : Measurable (qTau d s τ) := by
  unfold qTau
  have hm : Measurable (fun p : Euc d × ℝ => psd3_F d s p.2 p.1) :=
    (psd3_F_meas (d := d) s).comp measurable_swap
  exact (hm.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc (0 : ℝ) τ))).measurable

theorem wr12_qTau_even {s τ : ℝ} (z : Euc d) : qTau d s τ (-z) = qTau d s τ z := by
  unfold qTau psd3_F heatKerE
  simp only [norm_neg]

/-- `ρ dx` has no atoms. -/
theorem wr12_atomless (hd : 1 ≤ d) (ρ : Euc d → ℝ) (x : Euc d) :
    HRS.Whole.withDensityReal ρ {x} = 0 := by
  have : Nontrivial (Euc d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  exact (withDensity_absolutelyContinuous _ _) (measure_singleton x)

/-- The kernel `q_τ(x-y)` is a weak kernel for `μ = ρ dx`, `ρ ≤ M`, with row mass `M ∫ q_τ`. -/
theorem wr12_qTau_weak (hd : 1 ≤ d) {s : ℝ} (hs : 0 < s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ)
    {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) {M : ℝ} (hM : ∀ x, ρ x ≤ M) :
    EWeakKernel (HRS.Whole.withDensityReal ρ)
      (M * (aDS d s / (((d : ℝ) - s) / 2) * τ ^ (((d : ℝ) - s) / 2)))
      (fun x y : Euc d => qTau d s τ (x - y)) := by
  have hM0 : 0 ≤ M := (hρ.nonneg 0).trans (hM 0)
  obtain ⟨hqi, hqI⟩ := qTau_integrable_integral hs hsd hτ
  refine ⟨?_, ?_, fun x y => qTau_nonneg hs _, fun x => ?_⟩
  · exact (wr12_qTau_meas (d := d)).comp (measurable_fst.sub measurable_snd)
  · intro x y
    rw [← wr12_qTau_even (d := d) (x - y), neg_sub]
  · have hm : Measurable fun w : Euc d => ENNReal.ofReal (qTau d s τ w) :=
      ENNReal.measurable_ofReal.comp wr12_qTau_meas
    have h1 := HRS.Whole.Q34.lintegral_conv_le hρ hM (fun w => ENNReal.ofReal (qTau d s τ w)) hm x
    have h2 : ∫⁻ w, ENNReal.ofReal (qTau d s τ w) = ENNReal.ofReal (∫ w, qTau d s τ w) :=
      (ofReal_integral_eq_lintegral_ofReal hqi
        (Eventually.of_forall fun w => qTau_nonneg hs w)).symm
    rw [h2, hqI] at h1
    refine h1.trans ?_
    rw [← ENNReal.ofReal_mul hM0]

/-! ### The energy lower bound -/

/-- For a nonnegative kernel with row integrals `≤ a`, `N F_N ≥ -N a`. -/
theorem wr12_pairEnergy_nonneg_lower {μ : Measure (Euc d)} {q : Euc d → Euc d → ℝ}
    (hq0 : ∀ x y, 0 ≤ q x y) {a : ℝ} (hrow : ∀ x, ∫ y, q x y ∂μ ≤ a) (hN : 1 ≤ N)
    (X : EucConfig d N) : -((N : ℝ) * a) ≤ (N : ℝ) * pairEnergy q X μ := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : 0 ≤ ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, q (X i) (X j) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hq0 _ _
  have h2 : 0 ≤ ∫ x, ∫ y, q x y ∂μ ∂μ :=
    integral_nonneg fun x => integral_nonneg fun y => hq0 x y
  have h3 : ∑ i : Fin N, ∫ y, q (X i) y ∂μ ≤ N * a := by
    calc ∑ i : Fin N, ∫ y, q (X i) y ∂μ ≤ ∑ _i : Fin N, a := Finset.sum_le_sum fun i _ => hrow _
      _ = N * a := by simp
  have key : (N : ℝ) * pairEnergy q X μ =
      (1 / (2 * N)) * (∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, q (X i) (X j))
        - ∑ i : Fin N, ∫ y, q (X i) y ∂μ + (N / 2) * ∫ x, ∫ y, q x y ∂μ ∂μ := by
    unfold pairEnergy
    field_simp
  rw [key]
  have : 0 ≤ (1 / (2 * (N : ℝ))) * (∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, q (X i) (X j)) :=
    mul_nonneg (by positivity) h1
  have : 0 ≤ ((N : ℝ) / 2) * ∫ x, ∫ y, q x y ∂μ ∂μ := mul_nonneg (by positivity) h2
  linarith

/-- A bounded measurable even kernel is `RowOKE` for a probability measure. -/
theorem wr12_rowOKE_diff {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {P : Euc d → ℝ}
    (hPm : Measurable P) {C0 : ℝ} (hPb : ∀ w, |P w| ≤ C0) :
    RowOKE μ (fun x y : Euc d => P (x - y)) := by
  have hm : Measurable (Function.uncurry fun x y : Euc d => P (x - y)) :=
    hPm.comp (measurable_fst.sub measurable_snd)
  refine ⟨hm, fun x => ?_, C0, fun x => ?_⟩
  · exact Integrable.of_bound (hPm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable C0
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hPb _)
  · have hnn : 0 ≤ ∫ y, |P (x - y)| ∂μ := integral_nonneg fun y => abs_nonneg _
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun y => |P (x - y)|) (C := C0)
      (Eventually.of_forall fun y => by simpa using hPb (x - y))
    rw [Real.norm_eq_abs, abs_of_nonneg hnn] at this
    simpa using this

/-- **Generic lower bound.**  If `h = q + P` off the origin, `q(x-y)` is a weak kernel (row mass `≤ a`)
and `P` is bounded, even and positive definite, then at configurations of pairwise distinct particles
`N F_N^h ≥ -N a - P(0)/2`. -/
theorem wr12_energy_split_lower {μ : Measure (Euc d)} [IsProbabilityMeasure μ]
    (hμ : ∀ x, μ {x} = 0) {a : ℝ} (ha : 0 ≤ a) {q P h : Euc d → ℝ}
    (hq : EWeakKernel μ a (fun x y : Euc d => q (x - y)))
    (hPm : Measurable P) {C0 : ℝ} (hPb : ∀ w, |P w| ≤ C0) (hPs : ∀ w, P (-w) = P w)
    (hPpos : ∀ (ν : Measure (Euc d)) [IsFiniteMeasure ν] (u : Euc d → ℝ), Measurable u →
      Integrable u ν → 0 ≤ ∫ z : Euc d × Euc d, P (z.1 - z.2) * (u z.1 * u z.2) ∂(ν.prod ν))
    (hsplit : ∀ z, z ≠ 0 → h z = q z + P z) (hN : 1 ≤ N) (X : EucConfig d N)
    (hX : ∀ i j, i ≠ j → X i ≠ X j) :
    -((N : ℝ) * a) - (1 / 2) * P 0 ≤ (N : ℝ) * pairEnergy (fun x y => h (x - y)) X μ := by
  have hRq := hq.rowOKE ha
  have hRP := wr12_rowOKE_diff (μ := μ) hPm hPb
  have e1 : pairEnergy (fun x y : Euc d => h (x - y)) X μ =
      pairEnergy (fun x y : Euc d => q (x - y) + P (x - y)) X μ :=
    pairEnergy_congr_offdiag hμ (fun x y hxy => hsplit _ (sub_ne_zero.2 hxy)) X hX
  rw [e1, pairEnergy_add hRq hRP, mul_add]
  have h1 := wr12_pairEnergy_nonneg_lower (μ := μ) (q := fun x y : Euc d => q (x - y)) hq.nonneg
    (fun x => hq.wr1_rowInt_le ha x) hN X
  have h2 := wr12_psd_diag_bound hPm hPb hPs hPpos hN μ X
  linarith

/-! ### Scale `τ₀ = N^{-2/d}` -/

/-- The heat-time `η² = N^{-2/d}` of the split at the interparticle scale `η = N^{-1/d}`. -/
def wr12_tau0 (d N : ℕ) : ℝ := (N : ℝ) ^ (-(2 : ℝ) / d)

theorem wr12_tau0_pos (hN : 1 ≤ N) : 0 < wr12_tau0 d N :=
  Real.rpow_pos_of_pos (by exact_mod_cast hN) _

theorem wr12_tau0_rpow (r : ℝ) : wr12_tau0 d N ^ r = (N : ℝ) ^ (-(2 * r) / d) := by
  unfold wr12_tau0
  rw [← Real.rpow_mul (Nat.cast_nonneg N)]
  congr 1
  ring

/-- `N τ₀^{(d-s)/2} = N^{s/d}`. -/
theorem wr12_N_mul_alpha (hd : 1 ≤ d) (hN : 1 ≤ N) (s : ℝ) :
    (N : ℝ) * wr12_tau0 d N ^ (((d : ℝ) - s) / 2) = (N : ℝ) ^ (s / d) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hd0 : (d : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ d := by exact_mod_cast hd
                               linarith
  rw [wr12_tau0_rpow]
  have h1 : (N : ℝ) * (N : ℝ) ^ (-(2 * (((d : ℝ) - s) / 2)) / d) =
      (N : ℝ) ^ (1 + -(2 * (((d : ℝ) - s) / 2)) / d) := by
    rw [Real.rpow_add hN0, Real.rpow_one]
  rw [h1]
  congr 1
  field_simp
  ring

/-- `τ₀^{-s/2} = N^{s/d}`. -/
theorem wr12_tau0_neg (hd : 1 ≤ d) (s : ℝ) :
    wr12_tau0 d N ^ (-(s / 2)) = (N : ℝ) ^ (s / d) := by
  rw [wr12_tau0_rpow]
  congr 1
  ring

/-- The `L¹` norm constant of `q_τ`: `∫ q_τ = cq τ^{(d-s)/2}`. -/
def wr12_cq (d : ℕ) (s : ℝ) : ℝ := aDS d s / (((d : ℝ) - s) / 2)

/-- `k_τ(0) = ck τ^{-s/2}`. -/
def wr12_ck (d : ℕ) (s : ℝ) : ℝ := 2 * aDS d s / (s * (4 * Real.pi) ^ ((d : ℝ) / 2))

theorem wr12_cq_nonneg {s : ℝ} (hs : 0 < s) (hsd : s < d) : 0 ≤ wr12_cq d s := by
  unfold wr12_cq
  have : 0 < ((d : ℝ) - s) / 2 := by linarith
  exact div_nonneg (psd3_aDS_pos hs).le this.le

theorem wr12_ck_nonneg {s : ℝ} (hs : 0 < s) : 0 ≤ wr12_ck d s := by
  unfold wr12_ck
  have := psd3_aDS_pos (d := d) hs
  positivity

theorem wr12_kTau_zero_eq {s : ℝ} (hs : 0 < s) {τ : ℝ} (hτ : 0 < τ) :
    kTau d s τ 0 = wr12_ck d s * τ ^ (-(s / 2)) := kTau_zero hs hτ

/-! ### Energy lower bound for the Riesz kernel -/

/-- **Coarse energy lower bound** (T5, `euc_energy_lower`).  There is `C ≥ 0` depending only on
`(d, s, M)` such that for every probability density `ρ ≤ M`, every `N ≥ 1` and every configuration of
pairwise distinct particles, `N F_N^g(X, ρ dx) ≥ -C N^{s/d}`. -/
theorem euc_energy_lower (hd : 1 ≤ d) {s : ℝ} (hs : 0 < s) (hsd : s < d) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ N : ℕ, 1 ≤ N → ∀ X : EucConfig d N, (∀ i j, i ≠ j → X i ≠ X j) →
        -(C * (N : ℝ) ^ (s / d)) ≤
          (N : ℝ) * pairEnergy (fun x y => rieszKernel d s (x - y)) X (HRS.Whole.withDensityReal ρ) := by
  refine ⟨max M 0 * wr12_cq d s + wr12_ck d s / 2, ?_, ?_⟩
  · have := wr12_cq_nonneg (d := d) hs hsd
    have := wr12_ck_nonneg (d := d) hs
    positivity
  intro ρ hρ hM N hN X hX
  haveI := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  have hM0 : 0 ≤ M := (hρ.nonneg 0).trans (hM 0)
  have hτ := wr12_tau0_pos (d := d) hN
  have hq := wr12_qTau_weak hd hs hsd hτ hρ hM
  have hcq := wr12_cq_nonneg (d := d) hs hsd
  have hτα : 0 ≤ wr12_tau0 d N ^ (((d : ℝ) - s) / 2) := (Real.rpow_pos_of_pos hτ _).le
  have ha : 0 ≤ M * (aDS d s / (((d : ℝ) - s) / 2) * wr12_tau0 d N ^ (((d : ℝ) - s) / 2)) := by
    have : aDS d s / (((d : ℝ) - s) / 2) = wr12_cq d s := rfl
    rw [this]; positivity
  have key := wr12_energy_split_lower (μ := HRS.Whole.withDensityReal ρ) (wr12_atomless hd ρ) ha
    (q := qTau d s (wr12_tau0 d N)) (P := kTau d s (wr12_tau0 d N)) (h := rieszKernel d s) hq
    (kTau_continuous hs hτ).measurable (fun w => wr7_kTau_abs_le hs hτ w) wr7_kTau_symm
    (fun ν _ u hum hu => kTau_posdef hs hτ hum hu)
    (fun z hz => riesz_heat_split hs hτ hz) hN X hX
  have e1 : (N : ℝ) * (M * (aDS d s / (((d : ℝ) - s) / 2) * wr12_tau0 d N ^ (((d : ℝ) - s) / 2))) =
      M * wr12_cq d s * (N : ℝ) ^ (s / d) := by
    rw [← wr12_N_mul_alpha hd hN s]
    unfold wr12_cq
    ring
  rw [e1, wr12_kTau_zero_eq hs hτ, wr12_tau0_neg hd] at key
  have hNs : 0 ≤ (N : ℝ) ^ (s / d) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hmax : max M 0 = M := max_eq_left hM0
  rw [hmax]
  nlinarith

/-- **Coarse energy lower bound for the weak kernel `q_τ`** (kernel of the weak reference `R0`).
`C ≥ 0` depends only on `(d, s, M)` (not on `τ`): `N F_N^{q_τ}(X, ρ dx) ≥ -C N^{s/d}` for configurations of
pairwise distinct particles.  Proof: for `τ ≥ η² = N^{-2/d}` split `q_τ = q_{η²} + band(η², τ]`
(`band` is bounded positive definite with `band 0 ≤ k_{η²}(0)`); for `τ < η²` use `q_τ ≥ 0` and
`‖q_τ‖₁ ≤ ‖q_{η²}‖₁`. -/
theorem euc_energy_lower_q (hd : 1 ≤ d) {s : ℝ} (hs : 0 < s) (hsd : s < d) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 < τ → ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ →
      (∀ x, ρ x ≤ M) → ∀ N : ℕ, 1 ≤ N → ∀ X : EucConfig d N, (∀ i j, i ≠ j → X i ≠ X j) →
        -(C * (N : ℝ) ^ (s / d)) ≤
          (N : ℝ) * pairEnergy (fun x y => qTau d s τ (x - y)) X (HRS.Whole.withDensityReal ρ) := by
  refine ⟨max M 0 * wr12_cq d s + wr12_ck d s / 2, ?_, ?_⟩
  · have := wr12_cq_nonneg (d := d) hs hsd
    have := wr12_ck_nonneg (d := d) hs
    positivity
  intro τ hτ ρ hρ hM N hN X hX
  haveI := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  have hM0 : 0 ≤ M := (hρ.nonneg 0).trans (hM 0)
  have hτ0 := wr12_tau0_pos (d := d) hN
  have hcq := wr12_cq_nonneg (d := d) hs hsd
  have hck := wr12_ck_nonneg (d := d) hs
  have hα : 0 < ((d : ℝ) - s) / 2 := by linarith
  have hNs : 0 ≤ (N : ℝ) ^ (s / d) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hmax : max M 0 = M := max_eq_left hM0
  rw [hmax]
  rcases le_or_gt (wr12_tau0 d N) τ with hle | hlt
  · -- split at `η² = N^{-2/d}`
    have hq := wr12_qTau_weak hd hs hsd hτ0 hρ hM
    have ha : 0 ≤ M * (aDS d s / (((d : ℝ) - s) / 2) * wr12_tau0 d N ^ (((d : ℝ) - s) / 2)) := by
      have : aDS d s / (((d : ℝ) - s) / 2) = wr12_cq d s := rfl
      have := (Real.rpow_pos_of_pos hτ0 (((d : ℝ) - s) / 2)).le
      rw [show aDS d s / (((d : ℝ) - s) / 2) = wr12_cq d s from rfl]; positivity
    have key := wr12_energy_split_lower (μ := HRS.Whole.withDensityReal ρ) (wr12_atomless hd ρ) ha
      (q := qTau d s (wr12_tau0 d N)) (P := wr12_bandK d s (wr12_tau0 d N) τ) (h := qTau d s τ) hq
      (wr12_setK_continuous hs hτ0 measurableSet_Ioc Ioc_subset_Ioi_self).measurable
      (fun w => wr12_setK_abs_le hs hτ0 measurableSet_Ioc Ioc_subset_Ioi_self w)
      (fun w => wr12_setK_even w)
      (fun ν _ u hum hu => wr12_bandPosdef hs hτ0 hum hu)
      (fun z hz => by
        have h1 := riesz_heat_split hs hτ hz
        have h2 := riesz_heat_split hs hτ0 hz
        have h3 := wr12_kTau_eq_band_add hs hτ0 hle z
        linarith) hN X hX
    have e1 : (N : ℝ) * (M * (aDS d s / (((d : ℝ) - s) / 2) * wr12_tau0 d N ^ (((d : ℝ) - s) / 2))) =
        M * wr12_cq d s * (N : ℝ) ^ (s / d) := by
      rw [← wr12_N_mul_alpha hd hN s]
      unfold wr12_cq
      ring
    have h0 : wr12_bandK d s (wr12_tau0 d N) τ 0 ≤ kTau d s (wr12_tau0 d N) 0 :=
      wr12_setK_zero_le hs hτ0 measurableSet_Ioc Ioc_subset_Ioi_self
    rw [e1] at key
    rw [wr12_kTau_zero_eq hs hτ0, wr12_tau0_neg hd] at h0
    nlinarith
  · -- `τ < η²`: `q_τ ≥ 0` and `‖q_τ‖₁ ≤ ‖q_{η²}‖₁`
    have hq := wr12_qTau_weak hd hs hsd hτ hρ hM
    have ha : 0 ≤ M * (aDS d s / (((d : ℝ) - s) / 2) * τ ^ (((d : ℝ) - s) / 2)) := by
      have := (Real.rpow_pos_of_pos hτ (((d : ℝ) - s) / 2)).le
      rw [show aDS d s / (((d : ℝ) - s) / 2) = wr12_cq d s from rfl]; positivity
    have key := wr12_energy_split_lower (μ := HRS.Whole.withDensityReal ρ) (wr12_atomless hd ρ) ha
      (q := qTau d s τ) (P := fun _ => (0 : ℝ)) (h := qTau d s τ) hq measurable_const
      (C0 := 0) (fun w => by simp) (fun w => rfl)
      (fun ν _ u hum hu => by simp) (fun z hz => by simp) hN X hX
    have hmono : τ ^ (((d : ℝ) - s) / 2) ≤ wr12_tau0 d N ^ (((d : ℝ) - s) / 2) :=
      Real.rpow_le_rpow hτ.le hlt.le hα.le
    have e1 : (N : ℝ) * (M * (aDS d s / (((d : ℝ) - s) / 2) * wr12_tau0 d N ^ (((d : ℝ) - s) / 2))) =
        M * wr12_cq d s * (N : ℝ) ^ (s / d) := by
      rw [← wr12_N_mul_alpha hd hN s]
      unfold wr12_cq
      ring
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hle2 : (N : ℝ) * (M * (aDS d s / (((d : ℝ) - s) / 2) * τ ^ (((d : ℝ) - s) / 2))) ≤
        (N : ℝ) * (M * (aDS d s / (((d : ℝ) - s) / 2) * wr12_tau0 d N ^ (((d : ℝ) - s) / 2))) := by
      have : aDS d s / (((d : ℝ) - s) / 2) = wr12_cq d s := rfl
      rw [this]
      gcongr
    rw [e1] at hle2
    simp only [mul_zero, sub_zero] at key
    nlinarith

end HRS.MS.Wr
