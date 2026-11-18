import HRS.MS.WrCal
import HRS.MS.WrFeat
import HRS.MS.WrAlgAux1
import HRS.MS.WrSmlAux2

/-!
# HRS.MS.WrTrAux1 -- the exact density `dQ/dR_N` (WR-11b, part 1)

Packet WR-11b of `docs/WR_B_PLAN.md` (T6), namespace `HRS.MS.Wr`, helper prefix `wr11b_`.
Euclidean port of `HRS/Equilibrium/CalibratedReference.lean:608-930` (the energy of the split kernel,
`logQ_eq_RN`, `Q_eq_RN_tilted`), with the feature space `ℝ^M` replaced by a real Hilbert space `H`.

Setting (`TransferHyp μ a q k g Ψ`): `μ` is an atomless probability measure on `Euc d`,
`(x, y) ↦ q (x - y)` is an `EWeakKernel μ a` (row mass `≤ a`, `0 ≤ a`; this is the `q_τ` of the heat split,
`R0 = pairGibbsLawE (q (x-y)) N β μ`), `Ψ : Euc d → H` is a feature map with Gram kernel `k (x - y)`
(`FeatHyp Ψ k`) and `g = q + k` off the origin (`riesz_heat_split` for `g = rieszKernel d s`).

Exports:
* `TransferHyp`, `wr11b_Sstat` (`S_N = √N μ_N(Ξ)`), `wr11b_logW` (`-(β/2) ‖S_N - √N Ξ̄_N‖²`);
* `TransferHyp.Q_eq_RN_tilted`: `modulatedGibbs g N β μ = (RN ..).tilted (wr11b_logW ..)`
  (`β > 0`, `0 < N`; no smallness hypothesis is needed for the exact identity).

Adjustments with respect to the plan (documented, harmless): the statement is made for any
`g` that agrees with `q + k` off the origin (so it applies to `rieszKernel d s` through `riesz_heat_split`
without a separate congruence step), `H` is any real inner product space with `CompleteSpace H` where the
calibration needs it, and `FeatHyp` is used through `CalFeat Ψ √(k 0)`.
-/

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wr

variable {d : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The difference kernel `(x, y) ↦ q (x - y)`. -/
abbrev wr11b_dk (q : Euc d → ℝ) : Euc d → Euc d → ℝ := fun x y => q (x - y)

/-- The rescaled statistic `S_N = √N μ_N(Ξ)`. -/
def wr11b_Sstat (μ : Measure (Euc d)) (Ψ : Euc d → H) {N : ℕ} (X : Fin N → Euc d) : H :=
  Real.sqrt N • empXi μ Ψ X

/-- The Gaussian weight `-(β/2) ‖S_N - √N Ξ̄_N‖²` of `A:eq:bounded-transfer` (log form). -/
def wr11b_logW (q : Euc d → ℝ) (μ : Measure (Euc d)) (Ψ : Euc d → H) (β : ℝ) (N : ℕ)
    (X : Fin N → Euc d) : ℝ :=
  -(β / 2) * ‖wr11b_Sstat μ Ψ X - Real.sqrt N • Xibar (wr11b_dk q) μ Ψ β N‖ ^ 2

/-- Standing hypotheses of the transfer: `q (x - y)` is a weak kernel with row mass `≤ a`, the features have
Gram kernel `k (x - y)`, `g = q + k` off the origin, and `μ` has no atoms. -/
structure TransferHyp (μ : Measure (Euc d)) (a : ℝ) (q k g : Euc d → ℝ) (Ψ : Euc d → H) : Prop where
  weak : EWeakKernel μ a (fun x y : Euc d => q (x - y))
  a_nonneg : 0 ≤ a
  feat : FeatHyp Ψ k
  split : ∀ x : Euc d, x ≠ 0 → g x = q x + k x
  atomless : ∀ x : Euc d, μ {x} = 0

section Basic

variable {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {a : ℝ} {q k g : Euc d → ℝ} {Ψ : Euc d → H}
  {N : ℕ} {β : ℝ}

theorem TransferHyp.calFeat (h : TransferHyp μ a q k g Ψ) : CalFeat Ψ (Real.sqrt (k 0)) :=
  ⟨h.feat.continuous, fun x => (h.feat.norm_eq x).le⟩

theorem wr11b_Sstat_eq (hN : 0 < N) (X : Fin N → Euc d) :
    wr11b_Sstat μ Ψ X = (Real.sqrt N)⁻¹ • wr11_S μ Ψ X := by
  unfold wr11b_Sstat
  rw [wr11_empXi_eq, smul_smul]
  congr 1
  have h0 : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
  have h1 : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (Nat.cast_nonneg N)
  field_simp
  linarith

theorem wr11b_sq_norm_Sstat (X : Fin N → Euc d) :
    ‖wr11b_Sstat μ Ψ X‖ ^ 2 = N * ‖empXi μ Ψ X‖ ^ 2 := by
  unfold wr11b_Sstat
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (Nat.cast_nonneg N)]

theorem wr11b_continuous_empXi [CompleteSpace H] (h : TransferHyp μ a q k g Ψ) {N : ℕ} :
    Continuous (empXi μ Ψ (N := N)) := by
  have e : empXi μ Ψ = fun X : Fin N → Euc d => (1 / (N : ℝ)) • wr11_S μ Ψ X := rfl
  rw [e]
  exact h.calFeat.continuous_S.const_smul _

theorem wr11b_continuous_Sstat [CompleteSpace H] (h : TransferHyp μ a q k g Ψ) {N : ℕ} :
    Continuous (wr11b_Sstat μ Ψ (N := N)) :=
  (wr11b_continuous_empXi h).const_smul _

/-- `N * F_N^{k}(X, μ) = ½ ‖S_N‖² - ½ k 0`. -/
theorem wr11b_energy_k [CompleteSpace H] (h : TransferHyp μ a q k g Ψ) (hN : 0 < N)
    (X : Fin N → Euc d) :
    (N : ℝ) * HRS.Whole.pairEnergy (fun x y : Euc d => k (x - y)) X μ =
      (1 / 2) * ‖wr11b_Sstat μ Ψ X‖ ^ 2 - (1 / 2) * k 0 := by
  have := energy_identity_E h.feat μ hN X
  rw [this, wr11b_Sstat_eq hN]
  rfl

theorem wr11b_rowOKE_k (h : TransferHyp μ a q k g Ψ) :
    RowOKE μ (fun x y : Euc d => k (x - y)) := by
  have hkm : Measurable k := h.feat.k_continuous.measurable
  refine ⟨?_, fun x => ?_, ⟨k 0, fun x => ?_⟩⟩
  · exact hkm.comp (measurable_fst.sub measurable_snd)
  · exact Integrable.of_bound (hkm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable (k 0)
      (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact h.feat.k_abs_le _)
  · have hi : Integrable (fun y : Euc d => |k (x - y)|) μ :=
      (Integrable.of_bound (hkm.comp (measurable_const.sub measurable_id)).aestronglyMeasurable (k 0)
        (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact h.feat.k_abs_le _)).abs
    calc ∫ y, |k (x - y)| ∂μ ≤ ∫ _y, k 0 ∂μ :=
          integral_mono hi (integrable_const _) fun y => h.feat.k_abs_le _
      _ = k 0 := by simp

/-- Off the collision set, the energy of `g` splits: `F^g = F^q + F^k`. -/
theorem wr11b_energy_g [CompleteSpace H] (h : TransferHyp μ a q k g Ψ) {X : Fin N → Euc d}
    (hX : ∀ i j, i ≠ j → X i ≠ X j) :
    HRS.Whole.pairEnergy (fun x y : Euc d => g (x - y)) X μ =
      modEnergyE (wr11b_dk q) X μ + HRS.Whole.pairEnergy (fun x y : Euc d => k (x - y)) X μ := by
  have hq : RowOKE μ (wr11b_dk q) := h.weak.rowOKE h.a_nonneg
  have e1 := pairEnergy_congr_offdiag (N := N) h.atomless
    (k₁ := fun x y : Euc d => g (x - y)) (k₂ := fun x y : Euc d => q (x - y) + k (x - y))
    (fun x y hxy => h.split _ (sub_ne_zero.2 hxy)) X hX
  rw [e1, pairEnergy_add hq (wr11b_rowOKE_k h)]
  rfl

/-- Adding a constant to the log-density does not change the tilted measure. -/
theorem wr11b_tilted_add_const {α : Type*} [MeasurableSpace α] (P : Measure α) (f : α → ℝ) (c : ℝ) :
    P.tilted (fun x => f x + c) = P.tilted f := by
  unfold Measure.tilted
  have hZ : ∫ x, Real.exp (f x + c) ∂P = (∫ x, Real.exp (f x) ∂P) * Real.exp c := by
    simp_rw [Real.exp_add]
    exact integral_mul_const _ _
  congr 1
  funext x
  rw [hZ, Real.exp_add, mul_div_mul_right _ _ (Real.exp_pos c).ne']

/-- `Q_{N,β}(μ)` is the tilt of `μ^{⊗N}` by `-β N F_N^g` whenever the weight is integrable. -/
theorem wr11b_modulatedGibbs_eq_tilted {g : Euc d → ℝ}
    (hint : Integrable (fun X : Fin N → Euc d =>
      Real.exp (-β * N * HRS.Whole.modulatedEnergy g X μ)) (Measure.pi fun _ : Fin N => μ)) :
    HRS.Whole.modulatedGibbs g N β μ = (Measure.pi fun _ : Fin N => μ).tilted
      (fun X => -β * N * HRS.Whole.modulatedEnergy g X μ) := by
  have hZ := integral_exp_pos (μ := Measure.pi fun _ : Fin N => μ)
    (f := fun X : Fin N → Euc d => -β * N * HRS.Whole.modulatedEnergy g X μ) hint
  unfold HRS.Whole.modulatedGibbs HRS.Whole.gibbsNormalizer Measure.tilted
  have hr : (ENNReal.ofReal (∫ X : Fin N → Euc d,
      Real.exp (-β * N * HRS.Whole.modulatedEnergy g X μ) ∂(Measure.pi fun _ : Fin N => μ)))⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.2 (ENNReal.ofReal_pos.2 hZ).ne'
  rw [← withDensity_smul' _ _ hr]
  congr 1
  funext X
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [ENNReal.ofReal_div_of_pos hZ, div_eq_mul_inv, mul_comm]

variable [CompleteSpace H]

/-- The completed square: `-(β/2) ‖S_N‖² = ⟪t_N, Σ Ξ⟫ + log W + (β N/2) ‖Ξ̄_N‖²`
(`A:eq:bounded-transfer`, using `t_N = -β Ξ̄_N`). -/
theorem wr11b_logQ_eq (h : TransferHyp μ a q k g Ψ) (hβ : 0 < β) (hN : 0 < N) (X : Fin N → Euc d) :
    -(β / 2) * ‖wr11b_Sstat μ Ψ X‖ ^ 2 =
      Yf μ Ψ (tN (wr11b_dk q) μ Ψ β N) X + wr11b_logW q μ Ψ β N X +
        (β * N / 2) * ‖Xibar (wr11b_dk q) μ Ψ β N‖ ^ 2 := by
  have key : ‖wr11b_Sstat μ Ψ X - Real.sqrt N • Xibar (wr11b_dk q) μ Ψ β N‖ ^ 2 =
      N * (‖empXi μ Ψ X‖ ^ 2 - 2 * inner ℝ (empXi μ Ψ X) (Xibar (wr11b_dk q) μ Ψ β N) +
        ‖Xibar (wr11b_dk q) μ Ψ β N‖ ^ 2) := by
    unfold wr11b_Sstat
    rw [← smul_sub, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (Nat.cast_nonneg N),
      norm_sub_sq_real]
  rw [Yf_eq_inner hN, tN_eq h.weak h.calFeat hβ hN]
  unfold wr11b_logW
  have hS := wr11b_sq_norm_Sstat (μ := μ) (Ψ := Ψ) X
  rw [key, hS, inner_smul_left, real_inner_comm (Xibar (wr11b_dk q) μ Ψ β N)
    (empXi μ Ψ X)]
  simp only [conj_trivial]
  ring

theorem wr11b_integrable_exp_Yf_add (h : TransferHyp μ a q k g Ψ) (hβ : 0 ≤ β) (hN : 0 < N)
    (t : H) :
    Integrable (fun X : Fin N → Euc d => Real.exp (-β * N * modEnergyE (wr11b_dk q) X μ +
      Yf μ Ψ t X)) (Measure.pi fun _ : Fin N => μ) := by
  have hfq := h.weak.wr12_integrable_exp h.a_nonneg hβ hN
  have hm : Measurable (fun X : Fin N → Euc d => -β * N * modEnergyE (wr11b_dk q) X μ) :=
    (h.weak.wr12_measurable_energy N).const_mul _
  refine Integrable.mono' (hfq.mul_const (Real.exp (‖t‖ * (N * (2 * Real.sqrt (k 0)))))) ?_ ?_
  · exact (Real.measurable_exp.comp (hm.add (h.calFeat.measurable_Yf t))).aestronglyMeasurable
  · refine Eventually.of_forall fun X => ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
    exact (le_abs_self _).trans (h.calFeat.abs_Yf_le t X)

/-- **`A:eq:bounded-transfer` (exact density)**: `Q_{N,β}(μ)` is `R_N` tilted by
`-(β/2) ‖S_N - √N Ξ̄_N‖²`, i.e. `dQ/dR_N = e^{-β‖S_N-√NΞ̄_N‖²/2} / E_{R_N}[e^{-β‖S_N-√NΞ̄_N‖²/2}]`. -/
theorem TransferHyp.Q_eq_RN_tilted (h : TransferHyp μ a q k g Ψ) (hβ : 0 < β) (hN : 0 < N) :
    HRS.Whole.modulatedGibbs g N β μ =
      (RN (wr11b_dk q) μ Ψ β N).tilted (wr11b_logW q μ Ψ β N) := by
  set P : Measure (Fin N → Euc d) := Measure.pi fun _ : Fin N => μ with hP
  have hfq := h.weak.wr12_integrable_exp h.a_nonneg hβ.le hN
  have hfm : Measurable (fun X : Fin N → Euc d => -β * N * modEnergyE (wr11b_dk q) X μ) :=
    (h.weak.wr12_measurable_energy N).const_mul _
  set c : ℝ := β * k 0 / 2 with hc
  -- a.e. splitting of the weight
  have hae : (fun X : Fin N → Euc d => -β * N * HRS.Whole.modulatedEnergy g X μ) =ᵐ[P]
      fun X => -β * N * modEnergyE (wr11b_dk q) X μ + (-(β / 2) * ‖wr11b_Sstat μ Ψ X‖ ^ 2 + c) := by
    filter_upwards [ae_injective_pi_Euc (N := N) h.atomless] with X hX
    have e1 : HRS.Whole.modulatedEnergy g X μ = HRS.Whole.pairEnergy (fun x y : Euc d => g (x - y)) X μ :=
      rfl
    rw [e1, wr11b_energy_g h hX]
    have := wr11b_energy_k h hN X
    rw [hc]
    linear_combination (-β) * this
  -- integrability of the weight of Q
  have hG : Integrable (fun X : Fin N → Euc d => Real.exp (-β * N * modEnergyE (wr11b_dk q) X μ +
      (-(β / 2) * ‖wr11b_Sstat μ Ψ X‖ ^ 2 + c))) P := by
    refine Integrable.mono' (hfq.mul_const (Real.exp c)) ?_ ?_
    · refine (Real.measurable_exp.comp (hfm.add ?_)).aestronglyMeasurable
      exact (((wr11b_continuous_Sstat h).norm.measurable.pow_const 2).const_mul _).add_const _
    · refine Eventually.of_forall fun X => ?_
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← add_assoc, Real.exp_add]
      refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
      have : 0 ≤ (β / 2) * ‖wr11b_Sstat μ Ψ X‖ ^ 2 := by positivity
      linarith
  have hint : Integrable (fun X : Fin N → Euc d =>
      Real.exp (-β * N * HRS.Whole.modulatedEnergy g X μ)) P :=
    hG.congr (hae.mono fun X hX => by simp only [hX])
  rw [wr11b_modulatedGibbs_eq_tilted hint, tilted_congr hae]
  have hRN : RN (wr11b_dk q) μ Ψ β N = P.tilted (fun X => -β * N * modEnergyE (wr11b_dk q) X μ +
      Yf μ Ψ (tN (wr11b_dk q) μ Ψ β N) X) := by
    unfold RN
    rw [h.weak.wr12_eq_tilted h.a_nonneg hβ.le hN, tilted_tilted hfq]
    rfl
  rw [hRN, tilted_tilted (wr11b_integrable_exp_Yf_add h hβ.le hN _)]
  have e2 : (fun X : Fin N → Euc d => -β * N * modEnergyE (wr11b_dk q) X μ +
      (-(β / 2) * ‖wr11b_Sstat μ Ψ X‖ ^ 2 + c)) =
      fun X => (-β * N * modEnergyE (wr11b_dk q) X μ + Yf μ Ψ (tN (wr11b_dk q) μ Ψ β N) X +
        wr11b_logW q μ Ψ β N X) + (c + (β * N / 2) * ‖Xibar (wr11b_dk q) μ Ψ β N‖ ^ 2) := by
    funext X
    have := wr11b_logQ_eq h hβ hN X
    linarith
  rw [e2, wr11b_tilted_add_const P (fun X => -β * N * modEnergyE (wr11b_dk q) X μ +
    Yf μ Ψ (tN (wr11b_dk q) μ Ψ β N) X + wr11b_logW q μ Ψ β N X)]
  rfl

end Basic

end HRS.MS.Wr
