import HRS.External.WeakSpec
import HRS.MS.WrKerAux3
import HRS.MS.WrPressAux1
import HRS.MS.WrAlgAux1
import HRS.MS.WlSphAux1
import HRS.MS.WlRowAux1
import HRS.MS.WlRowAux2

/-!
# HRS.MS.WlEnsAux1 -- field-ensemble layer for S3.5, part 1 (WL-3)

Packet WL-3 of `docs/WR_LOG_PLAN.md` (Step 1 and Step 4 of the proof of `r2_log_static`).  Infrastructure
lemmas, not manuscript rows.  Namespace `HRS.MS.Wl`, helper prefix `wl3_`.  Contracts used:
C2 = `WlRowAux1-2` (`wl_row_pow`, `wl_logmoment`, `wl_schur`), `WlSphAux1` (`K = sphericalLogKernel`).

Standing notation: `μ = withDensityReal ρ`, `K = sphericalLogKernel`, `ℓ = logWeight`, `g = rieszKernel d 0`,
`G = fun x y => g (x - y)`.  By definition `K x y = G x y + ℓ x + ℓ y` for ALL `x y` (also on the diagonal:
`K x x = 2 ℓ x`, `G x x = -log 0 = 0`), so no off-diagonal argument or atomlessness is needed for the energy
identity.

* `wl_rep`: the representative `ρ' = min ρ (max A 1 (1+|x|²)^{-d})` with the `∀ x` bound, the same measure
  and `ρ' = ρ` a.e.; `wl_isProb`, `wl_atomless`.
* `wl_K_weak`: `K` is an `EWeakKernel μ C K` with `C` uniform (from `wl_row_pow`).
* `wl_energy_eq` (adjusted, harmless): `modulatedEnergy (rieszKernel d 0) X μ = pairEnergy K X μ +
  (1/N²) ∑ ℓ (X i)` for ALL `X` (the brief asked for injective `X`; injectivity is not needed) and `N ≥ 1`
  (for `N = 0` the identity is false, the background terms differ by `∫ ℓ`).
* `wlPot hq ha hφ`: the `WeakPotential μ` of an `EWeakKernel μ a q` and an arbitrary field `IsField μ φ M M₁`
  (`q`, `γ = a`, `M`, `M' = M₁`).
* `wl_Q_eq_fieldLaw` (abstract `wl_Q_eq_fieldLaw_abs`, `wl_Q_eq_pinnedLaw`): `modulatedGibbs (rieszKernel d 0) N β μ =
  fieldLaw V ψ (β/N) N` for every weak potential `V` with `V.q = K`, with `ψ = wl_Qfield = β rowIntE K μ - (β/N) ℓ`,
  together with `IsField μ ψ (β C) ((β/N) ∫ ℓ)` where `C` bounds the rows of `K` and `∫ ℓ ≤ Cℓ`; hence the
  field constants are `M = β C`, `M₁ = β Cℓ / N` (uniform in `N`: `M₁` is `O(1/N)`, no `M'` problem).
  Valid for all `N ≥ 1`, `β ≥ 0`.
-/

set_option linter.unusedSectionVars false

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wl

open HRS.Whole HRS.MS.Wr HRS.External

variable {d : ℕ}

/-! ### Representative and atomlessness -/

/-- **Representative.**  A density with the spherical bound a.e. has an a.e.-equal representative with the
bound at every point; same measure, same `HasSphericalBound` with constant `max A 1`. -/
theorem wl_rep {A : ℝ} {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) (hA : HasSphericalBound A ρ) :
    ∃ ρ' : Euc d → ℝ, HRS.Whole.IsProbDensity ρ' ∧
      (∀ x, ρ' x ≤ max A 1 * (1 + ‖x‖ ^ 2) ^ (-(d : ℝ))) ∧
      HRS.Whole.withDensityReal ρ' = HRS.Whole.withDensityReal ρ ∧ HasSphericalBound (max A 1) ρ' ∧
      (ρ' =ᵐ[volume] ρ) := by
  set w : Euc d → ℝ := fun x => max A 1 * (1 + ‖x‖ ^ 2) ^ (-(d : ℝ)) with hw
  have hw0 : ∀ x, 0 ≤ w x := fun x => by
    have : 0 ≤ max A 1 := le_trans zero_le_one (le_max_right A 1)
    positivity
  have hwm : Measurable w := by
    refine measurable_const.mul ?_
    exact (by fun_prop : Measurable fun x : Euc d => 1 + ‖x‖ ^ 2).pow_const _
  have hle : ∀ᵐ x ∂(volume : Measure (Euc d)), ρ x ≤ w x := by
    filter_upwards [hA] with x hx
    refine hx.trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left A 1) (by positivity)
  have hae : (fun x => min (ρ x) (w x)) =ᵐ[volume] ρ := by
    filter_upwards [hle] with x hx using min_eq_left hx
  refine ⟨fun x => min (ρ x) (w x), ⟨fun x => le_min (hρ.nonneg x) (hw0 x), hρ.measurable.min hwm, ?_⟩,
    fun x => min_le_right _ _, ?_, ?_, hae⟩
  · rw [integral_congr_ae hae]; exact hρ.integral_one
  · unfold HRS.Whole.withDensityReal
    exact withDensity_congr_ae (hae.mono fun x hx => by simp only [hx])
  · exact Filter.Eventually.of_forall fun x => min_le_right _ _

/-- `ρ dx` is a probability measure. -/
theorem wl_isProb {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) :=
  wl2_isProb hρ

/-- `ρ dx` has no atoms (`d ≥ 1`). -/
theorem wl_atomless (hd : 1 ≤ d) (ρ : Euc d → ℝ) (x : Euc d) : HRS.Whole.withDensityReal ρ {x} = 0 := by
  have h := wl2_ae_ne hd ρ x
  rw [ae_iff] at h
  simpa using h

/-! ### `K` as a weak kernel -/

/-- **`K` is an `EWeakKernel`** with a row constant `C` depending on `d, A` only. -/
theorem wl_K_weak (hd : 2 ≤ d) (A : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ,
    HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ →
      EWeakKernel (HRS.Whole.withDensityReal ρ) C (fun x y => sphericalLogKernel x y) := by
  obtain ⟨C, hC0, hC⟩ := wl_row_pow hd A 1
  refine ⟨C, hC0, fun ρ hρ hA => ⟨wl_K_measurable, wl_K_symm, HRS.MS.Comm.comm_log_nonneg,
    fun x => ?_⟩⟩
  obtain ⟨hint, hle⟩ := hC ρ hρ hA x
  simp only [pow_one] at hint hle
  have h1 := ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun y => HRS.MS.Comm.comm_log_nonneg x y)
  rw [← h1]
  exact ENNReal.ofReal_le_ofReal hle

/-! ### The exact diagonal identity -/

section Energy

variable {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

lemma wl3_wr8_sub {E : Type*} [MeasurableSpace E] {ν : Measure E} {k₁ k₂ : E → E → ℝ}
    (h₁ : Wr8Ok ν k₁) (h₂ : Wr8Ok ν k₂) : Wr8Ok ν (fun x y => k₁ x y - k₂ x y) :=
  ⟨h₁.meas.sub h₂.meas, fun x => (h₁.int x).sub (h₂.int x), h₁.prod.sub h₂.prod⟩

lemma wl3_wr8_L (hℓ : Integrable (logWeight : Euc d → ℝ) μ) :
    Wr8Ok μ (fun x y : Euc d => logWeight x + logWeight y) := by
  refine ⟨?_, fun x => (integrable_const _).add hℓ, ?_⟩
  · exact (wl2_logWeight_measurable.comp measurable_fst).add (wl2_logWeight_measurable.comp measurable_snd)
  · exact (hℓ.comp_fst μ).add (hℓ.comp_snd μ)

/-- The energy of the sum kernel `ℓ x + ℓ y` is `-(1/N²) ∑ ℓ (X i)`. -/
lemma wl3_modEnergyE_L (hℓ : Integrable (logWeight : Euc d → ℝ) μ) {N : ℕ} (hN : 1 ≤ N)
    (X : Fin N → Euc d) :
    modEnergyE (fun x y : Euc d => logWeight x + logWeight y) X μ =
      -(1 / (N : ℝ) ^ 2) * ∑ i, logWeight (X i) := by
  unfold modEnergyE
  set S : ℝ := ∑ i, logWeight (X i) with hS
  set I : ℝ := ∫ y, logWeight y ∂μ with hI
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have e1 : ∀ i : Fin N, ∑ j ∈ Finset.univ.erase i, (logWeight (X i) + logWeight (X j)) =
      ((N : ℝ) - 2) * logWeight (X i) + S := by
    intro i
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.sum_erase_eq_sub (Finset.mem_univ i)]
    simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Nat.cast_sub hN]
    simp only [Nat.cast_one]
    rw [hS]
    ring
  have e2 : ∀ x : Euc d, ∫ y, (logWeight x + logWeight y) ∂μ = logWeight x + I := by
    intro x
    rw [integral_add (integrable_const _) hℓ]
    simp [hI]
  have e3 : ∫ x, ∫ y, (logWeight x + logWeight y) ∂μ ∂μ = 2 * I := by
    simp_rw [e2]
    rw [integral_add hℓ (integrable_const _)]
    simp [hI]
    ring
  have e4 : ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, (logWeight (X i) + logWeight (X j)) =
      (2 * (N : ℝ) - 2) * S := by
    simp only [e1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    rw [← Finset.mul_sum, ← hS]
    ring
  have e5 : ∑ i : Fin N, (logWeight (X i) + I) = S + N * I := by
    simp [Finset.sum_add_distrib, hS]
  rw [e4, e3]
  simp only [e2]
  rw [e5]
  field_simp
  ring

/-- **`wl_energy_eq`.**  `F_N^{g}(X, μ) = 𝖥_N^{K}(X, μ) + N⁻² ∑ ℓ (X i)` for every configuration `X` and
`N ≥ 1`, where `g = rieszKernel d 0`, `K = sphericalLogKernel`.  Hypotheses: `K` weak (rows `≤ a`,
by `wl_K_weak`) and `ℓ ∈ L¹(μ)` (by `wl_logmoment`). -/
theorem wl_energy_eq {a : ℝ} (hK : EWeakKernel μ a (fun x y => sphericalLogKernel x y)) (ha : 0 ≤ a)
    (hℓ : Integrable (logWeight : Euc d → ℝ) μ) {N : ℕ} (hN : 1 ≤ N) (X : HRS.Whole.EucConfig d N) :
    HRS.Whole.modulatedEnergy (rieszKernel d 0) X μ =
      HRS.Whole.pairEnergy (fun x y => sphericalLogKernel x y) X μ
        + (1 / (N : ℝ) ^ 2) * ∑ i, logWeight (X i) := by
  have hKo : Wr8Ok μ (fun x y => sphericalLogKernel x y) := (hK.rowOKE ha).wr8_ok
  have hLo := wl3_wr8_L hℓ
  have hGe : (fun x y : Euc d => rieszKernel d 0 (x - y)) =
      fun x y => sphericalLogKernel x y - (logWeight x + logWeight y) := by
    funext x y
    simp only [rieszKernel, sphericalLogKernel, ite_true]
    ring
  have hGo : Wr8Ok μ (fun x y : Euc d => rieszKernel d 0 (x - y)) := by
    rw [hGe]; exact wl3_wr8_sub hKo hLo
  have e := wr8_modEnergyE_add (N := N) hGo hLo X
  have hKe : (fun x y : Euc d => sphericalLogKernel x y) =
      fun x y => rieszKernel d 0 (x - y) + (logWeight x + logWeight y) := by
    funext x y
    simp only [rieszKernel, sphericalLogKernel, ite_true]
    ring
  have e' : modEnergyE (fun x y : Euc d => sphericalLogKernel x y) X μ =
      modEnergyE (fun x y : Euc d => rieszKernel d 0 (x - y)) X μ
        + modEnergyE (fun x y : Euc d => logWeight x + logWeight y) X μ := by
    rw [← e, ← hKe]
  rw [wl3_modEnergyE_L hℓ hN] at e'
  change modEnergyE (fun x y : Euc d => rieszKernel d 0 (x - y)) X μ =
    modEnergyE (fun x y : Euc d => sphericalLogKernel x y) X μ + _
  rw [e']
  ring

end Energy

/-! ### `Q_N` as a field ensemble -/

/-- The one-body field of `Q_N`: `ψ = β rowIntE K μ - (β/N) ℓ`. -/
def wl_Qfield (μ : Measure (Euc d)) (β : ℝ) (N : ℕ) (x : Euc d) : ℝ :=
  β * rowIntE (fun x y : Euc d => sphericalLogKernel x y) μ x - (β / (N : ℝ)) * logWeight x

section Field

variable {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {a : ℝ}
  {hK : EWeakKernel μ a (fun x y : Euc d => sphericalLogKernel x y)}

/-- **The field of `Q_N`** is an `IsField` with `M = β a` and `M₁ = (β/N) ∫ ℓ`. -/
theorem wl_isField_Qfield (hK : EWeakKernel μ a (fun x y : Euc d => sphericalLogKernel x y))
    (ha : 0 ≤ a) (hℓ : Integrable (logWeight : Euc d → ℝ) μ) {β : ℝ} (hβ : 0 ≤ β) (N : ℕ) :
    IsField μ (wl_Qfield μ β N) (β * a) ((β / (N : ℝ)) * ∫ x, logWeight x ∂μ) := by
  have hβN : 0 ≤ β / (N : ℝ) := div_nonneg hβ (Nat.cast_nonneg N)
  have hrow : Integrable (rowIntE (fun x y : Euc d => sphericalLogKernel x y) μ) μ :=
    (hK.rowOKE ha).integrable_rowInt
  refine ⟨?_, fun z => ?_, ?_, ?_⟩
  · exact (hK.wr1_measurable_rowInt.const_mul β).sub (wl2_logWeight_measurable.const_mul _)
  · unfold wl_Qfield
    have h1 := hK.wr1_rowInt_le ha z
    have h2 : 0 ≤ (β / (N : ℝ)) * logWeight z := mul_nonneg hβN (wl2_logWeight_nonneg z)
    nlinarith
  · exact (hrow.const_mul β).sub (hℓ.const_mul _)
  · unfold wl_Qfield
    rw [integral_sub (hrow.const_mul β) (hℓ.const_mul _), integral_const_mul, integral_const_mul]
    have : 0 ≤ ∫ x, rowIntE (fun x y : Euc d => sphericalLogKernel x y) μ x ∂μ :=
      integral_nonneg fun x => hK.wr1_rowInt_nonneg x
    nlinarith [mul_nonneg hβ this]

/-- Pointwise weight identity: `exp(-β N F_N^g) = e^{-β N G/2} · fieldWeight V (wl_Qfield) (β/N)`. -/
lemma wl3_weight_eq (hK : EWeakKernel μ a (fun x y : Euc d => sphericalLogKernel x y)) (ha : 0 ≤ a)
    (hℓ : Integrable (logWeight : Euc d → ℝ) μ) (β : ℝ) {N : ℕ} (hN : 1 ≤ N)
    (V : WeakPotential μ) (hV : V.q = fun x y => sphericalLogKernel x y) (X : HRS.Whole.EucConfig d N) :
    ENNReal.ofReal (Real.exp (-β * N * HRS.Whole.modulatedEnergy (rieszKernel d 0) X μ)) =
      ENNReal.ofReal (Real.exp (-(β * N * (∫ x, ∫ y, sphericalLogKernel x y ∂μ ∂μ) / 2))) *
        fieldWeight V (wl_Qfield μ β N) (β / N) X := by
  unfold fieldWeight
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  rw [wl_energy_eq hK ha hℓ hN X]
  have hexp := wr1_exponent_eq (fun x y : Euc d => sphericalLogKernel x y) μ β X (by omega)
  have hpe : HRS.External.pairEnergy V X =
      (1 / 2) * pairSumE (fun x y : Euc d => sphericalLogKernel x y) X := by
    simp [HRS.External.pairEnergy, pairSumE, hV]
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have hmod : HRS.Whole.pairEnergy (fun x y : Euc d => sphericalLogKernel x y) X μ =
      modEnergyE (fun x y : Euc d => sphericalLogKernel x y) X μ := rfl
  rw [hmod, hpe]
  simp only [wl_Qfield, Finset.sum_sub_distrib, ← Finset.mul_sum, rowIntE] at *
  field_simp
  field_simp at hexp
  nlinarith [hexp]

/-- **`wl_Q_eq_fieldLaw`** (abstract form).  For every weak potential `V` whose pair kernel is `K`, the
modulated Gibbs law of `rieszKernel d 0` is the field ensemble `fieldLaw V (wl_Qfield μ β N) (β/N) N`. -/
theorem wl_Q_eq_fieldLaw_abs (hK : EWeakKernel μ a (fun x y : Euc d => sphericalLogKernel x y))
    (ha : 0 ≤ a) (hℓ : Integrable (logWeight : Euc d → ℝ) μ) {β : ℝ} (hβ : 0 ≤ β) {N : ℕ} (hN : 1 ≤ N)
    (V : WeakPotential μ) (hV : V.q = fun x y => sphericalLogKernel x y) :
    HRS.Whole.modulatedGibbs (rieszKernel d 0) N β μ = fieldLaw V (wl_Qfield μ β N) (β / N) N := by
  have hψ := wl_isField_Qfield hK ha hℓ hβ N
  have hlam : 0 ≤ β / (N : ℝ) := div_nonneg hβ (Nat.cast_nonneg N)
  set ψ := wl_Qfield μ β N with hψdef
  set K₀ : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(β * N * (∫ x, ∫ y, sphericalLogKernel x y ∂μ ∂μ) / 2)))
    with hK₀
  have hK0 : K₀ ≠ 0 := (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
  have hKt : K₀ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpw : ∀ X : HRS.Whole.EucConfig d N,
      ENNReal.ofReal (Real.exp (-β * N * HRS.Whole.modulatedEnergy (rieszKernel d 0) X μ))
        = K₀ * fieldWeight V ψ (β / N) X := fun X => wl3_weight_eq hK ha hℓ β hN V hV X
  have hfm : Measurable (fieldWeight V ψ (β / N) (n := N)) :=
    measurable_fieldWeight hψ.measurable V _
  have hfn0 : fieldNorm V ψ (β / N) N ≠ 0 := (fieldNorm_pos hψ.measurable V _ N).ne'
  have hfnt : fieldNorm V ψ (β / N) N ≠ ⊤ := (fieldNorm_lt_top hψ hlam N).ne
  have hwfun : (fun X : HRS.Whole.EucConfig d N =>
      ENNReal.ofReal (Real.exp (-β * N * HRS.Whole.modulatedEnergy (rieszKernel d 0) X μ)))
        = K₀ • fieldWeight V ψ (β / N) := funext hpw
  have hZ : ∫⁻ X : HRS.Whole.EucConfig d N,
      ENNReal.ofReal (Real.exp (-β * N * HRS.Whole.modulatedEnergy (rieszKernel d 0) X μ))
        ∂(Measure.pi fun _ : Fin N => μ) = K₀ * fieldNorm V ψ (β / N) N := by
    rw [hwfun]
    exact lintegral_const_mul _ hfm
  have hG : HRS.Whole.gibbsNormalizer (rieszKernel d 0) N β μ = (K₀ * fieldNorm V ψ (β / N) N).toReal := by
    unfold HRS.Whole.gibbsNormalizer
    rw [← hZ, ← integral_toReal]
    · exact integral_congr_ae (Filter.Eventually.of_forall fun X =>
        (ENNReal.toReal_ofReal (Real.exp_pos _).le).symm)
    · rw [hwfun]; exact (hfm.const_mul K₀).aemeasurable
    · refine Filter.Eventually.of_forall fun X => ?_
      rw [hpw X]
      exact ENNReal.mul_lt_top hKt.lt_top
        (lt_of_le_of_lt (fieldWeight_le hψ hlam X) ENNReal.ofReal_lt_top)
  unfold HRS.Whole.modulatedGibbs
  rw [hG, ENNReal.ofReal_toReal (ENNReal.mul_ne_top hKt hfnt), hwfun, withDensity_smul _ hfm,
    smul_smul]
  have hc : (K₀ * fieldNorm V ψ (β / N) N)⁻¹ * K₀ = (fieldNorm V ψ (β / N) N)⁻¹ := by
    rw [ENNReal.mul_inv (Or.inl hK0) (Or.inl hKt), mul_comm K₀⁻¹, mul_assoc,
      ENNReal.inv_mul_cancel hK0 hKt, mul_one]
  rw [hc]
  unfold fieldLaw fieldDensity
  rw [← withDensity_smul _ hfm]
  congr 1
  funext X
  simp [mul_comm]

end Field

/-! ### The weak potential `wlPot` and the ρ-level statement -/

section WlPot

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ] {a : ℝ}
  {q : E → E → ℝ}

/-- **`wlPot`**: the weak potential (`HRS.External.WeakPotential`) with pair kernel `q`
(`EWeakKernel μ a q`, row constant `γ = a`) and one-body field `φ` (`IsField μ φ M M₁`, `M' = M₁`).  The
field is arbitrary: `φ = β rowIntE q μ + h_N + v` and the poles `-λ ∑ t_b q(·, z_b)` can all be put into
`φ`, with explicit constants (`wl_isField_add`, `wl_isField_pole` in `WlEnsAux2`). -/
def wlPot (hq : EWeakKernel μ a q) (ha : 0 ≤ a) {φ : E → ℝ} {M M₁ : ℝ} (hφ : IsField μ φ M M₁) :
    WeakPotential μ where
  φ := φ
  q := q
  M := M
  M' := M₁
  γ := a
  measurable_φ := hφ.measurable
  measurable_q := hq.meas
  q_nonneg := hq.nonneg
  q_symm := hq.symm
  γ_nonneg := ha
  φ_le := hφ.le
  integrable_φ := hφ.integrable
  neg_le_integral_φ := hφ.ge
  integrable_q := hq.wr1_integrable_row
  row_le := hq.wr1_rowInt_le ha

end WlPot

/-- **`wl_Q_eq_fieldLaw`** (ρ-level, constants uniform in `ρ, β, N`).  With `C` the row constant of `K` and
`Cℓ` the bound of `∫ ℓ dμ` (`wl_row_pow`, `wl_logmoment` at `p = 1`):
for `β ≥ 0`, `N ≥ 1`: `K` is `EWeakKernel μ C`, `ℓ ∈ L¹(μ)`, the field `ψ = wl_Qfield μ β N` is an
`IsField μ ψ (β C) (β Cℓ / N)` (so `M' = O(1/N)`: uniform in `N`), and the weak potential
`V = wlPot … ψ` (kernel `K`, field `ψ`, constants `M = β C`, `M' = (β/N) ∫ ℓ`, `γ = C`) satisfies
`modulatedGibbs (rieszKernel d 0) N β μ = fieldLaw V ψ (β/N) N = pinnedLaw V (β/N) N ∅`. -/
theorem wl_Q_eq_fieldLaw (hd : 2 ≤ d) (A : ℝ) : ∃ C Cl : ℝ, 0 ≤ C ∧ ∀ ρ : Euc d → ℝ,
    HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ → ∀ β : ℝ, 0 ≤ β → ∀ N : ℕ, 1 ≤ N →
      EWeakKernel (HRS.Whole.withDensityReal ρ) C (fun x y : Euc d => sphericalLogKernel x y) ∧
      Integrable (logWeight : Euc d → ℝ) (HRS.Whole.withDensityReal ρ) ∧
      (∫ x, logWeight x ∂(HRS.Whole.withDensityReal ρ)) ≤ Cl ∧
      IsField (HRS.Whole.withDensityReal ρ) (wl_Qfield (HRS.Whole.withDensityReal ρ) β N)
        (β * C) (β * Cl / N) ∧
      (∀ V : WeakPotential (HRS.Whole.withDensityReal ρ),
        V.q = (fun x y : Euc d => sphericalLogKernel x y) →
        HRS.Whole.modulatedGibbs (rieszKernel d 0) N β (HRS.Whole.withDensityReal ρ) =
          fieldLaw V (wl_Qfield (HRS.Whole.withDensityReal ρ) β N) (β / N) N) := by
  obtain ⟨C, hC0, hC⟩ := wl_K_weak hd A
  obtain ⟨Cl, hCl⟩ := wl_logmoment hd A 1
  refine ⟨C, Cl, hC0, fun ρ hρ hA β hβ N hN => ?_⟩
  have := wl_isProb hρ
  have hK := hC ρ hρ hA
  obtain ⟨hℓ, hℓle⟩ := hCl ρ hρ hA
  simp only [pow_one] at hℓ hℓle
  refine ⟨hK, hℓ, hℓle, ?_, fun V hV => wl_Q_eq_fieldLaw_abs hK hC0 hℓ hβ hN V hV⟩
  have h := wl_isField_Qfield hK hC0 hℓ hβ N
  refine ⟨h.measurable, h.le, h.integrable, ?_⟩
  have := h.ge
  have hβN : 0 ≤ β / (N : ℝ) := div_nonneg hβ (Nat.cast_nonneg N)
  have h2 : (β / (N : ℝ)) * ∫ x, logWeight x ∂(HRS.Whole.withDensityReal ρ) ≤ β * Cl / N := by
    rw [mul_div_right_comm]
    exact mul_le_mul_of_nonneg_left hℓle hβN |>.trans_eq (by ring)
  linarith

/-- The field ensemble `Q_N` as the explicit pinned law of `wlPot` with no pins. -/
theorem wl_Q_eq_pinnedLaw {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {a : ℝ}
    (hK : EWeakKernel μ a (fun x y : Euc d => sphericalLogKernel x y)) (ha : 0 ≤ a)
    (hℓ : Integrable (logWeight : Euc d → ℝ) μ) {β : ℝ} (hβ : 0 ≤ β) {N : ℕ} (hN : 1 ≤ N) :
    HRS.Whole.modulatedGibbs (rieszKernel d 0) N β μ =
      pinnedLaw (wlPot hK ha (wl_isField_Qfield hK ha hℓ hβ N)) (β / N) N (fun e : Empty => e.elim) := by
  rw [wl_Q_eq_fieldLaw_abs hK ha hℓ hβ hN (wlPot hK ha (wl_isField_Qfield hK ha hℓ hβ N)) rfl]
  unfold pinnedLaw
  congr 1
  funext z
  simp [pinField, wlPot]

end HRS.MS.Wl
