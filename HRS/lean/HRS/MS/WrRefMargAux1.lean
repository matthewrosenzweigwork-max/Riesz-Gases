import HRS.MS.WrKernAux1
import HRS.MS.WrSmlAux2
import HRS.MS.WrFld
import HRS.MS.WrFeat
import HRS.Equilibrium.ReferenceMarginal

/-!
# HRS.MS.WrRefMargAux1 -- calibrated reference marginal, part 1: set-up and the sup bound (WR-13e)

Packet WR-13e (T11 of `docs/WR_B_PLAN.md`), first helper file.  Euclidean port of
`HRS/Equilibrium/ReferenceMarginal.lean` (torus template); the generic `WeakPotential` layer of the template
(`marginal_le_smul`, `cavU`, `cavTheta`, `cavMarg`, `cavD_bounds`, `field_event_comparison`) is imported and
used as is.

Setting.  `μ = withDensityReal ρ` (`ρ` a probability density, `ρ ≤ M`), `q x y = qTau d s τ (x - y)` the heat
part of the Riesz kernel (an `EWeakKernel μ a q` with `a = wr13e_a d s τ M`), `Ψ : Euc d → H` a feature map
with `FeatHyp Ψ (kTau d s τ)`, `RN = RN q μ Ψ β N` the calibrated reference.

Contents of this file.
* `wr13e_weakPotK`: the calibrated weak potential with a field bound `K` (generalisation of `weakPotE`);
  `wr13e_RN_eq_fieldLawK`, `wr13e_R0_eq_fieldLaw`: `RN` and `R0` are weak ensembles (`fieldLaw`).
* `wr13e_abs_tN_inner_le`: `|⟪t_N, Ξ x⟫| ≤ 4 β B²` for every `N ≥ 1`.
* `wr13e_firstMarginal_RN_leK`: `π^R_N ≤ e^{2βa + K} μ`.
* **`wr13e_reference_marginal_density_le`** (main theorem of this file, `dπ^R_N/dμ ≤ C`).
* the explicit one-point density `wr13e_theta` of the first marginal, `wr13e_log_theta_eq` (cavity equation),
  `wr13e_Xibar_eq_integral`, `wr13e_hh_eq` (the calibration identity `⟪t_N, Ξ x⟫ = -β (k * (θ - 1))(x) + const`).

Adjustments with respect to the torus statements (documented, harmless): `d ≥ 1` suffices here; the row bound is
`a = max M 0 * ∫ qTau` (so no sign hypothesis on `M`); constants are uniform in `β ∈ (0, βp]`.
Helper lemmas carry the prefix `wr13e_`.
-/

set_option linter.unusedSectionVars false

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wr

open HRS.External HRS.MS.Psd

variable {d : ℕ}

/-! ### The row bound -/

/-- Row bound `a = max M 0 * ∫ qTau` of the kernel `q_τ(x - y)` against `μ = ρ dx`, `ρ ≤ M`. -/
def wr13e_a (d : ℕ) (s τ M : ℝ) : ℝ :=
  max M 0 * (wr12_cq d s * τ ^ (((d : ℝ) - s) / 2))

theorem wr13e_a_nonneg {s : ℝ} (hs : 0 < s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ) (M : ℝ) :
    0 ≤ wr13e_a d s τ M := by
  unfold wr13e_a
  have := wr12_cq_nonneg (d := d) hs hsd
  have := Real.rpow_nonneg hτ.le (((d : ℝ) - s) / 2)
  positivity

theorem wr13e_weak (hd : 1 ≤ d) {s : ℝ} (hs : 0 < s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ)
    {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) {M : ℝ} (hM : ∀ x, ρ x ≤ M) :
    EWeakKernel (HRS.Whole.withDensityReal ρ) (wr13e_a d s τ M)
      (fun x y : Euc d => qTau d s τ (x - y)) :=
  wr12_qTau_weak hd hs hsd hτ hρ (M := max M 0) (fun x => (hM x).trans (le_max_left _ _))

/-! ### The calibrated weak potential with field bound `K` -/

section Pot

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {a : ℝ} {q : Euc d → Euc d → ℝ}
  {Ψ : Euc d → H} {B β : ℝ} {N : ℕ}

/-- The calibrated weak potential `φ = β (q*μ) + ⟪t, Ξ⟫` under `|⟪t, Ξ⟫| ≤ K`: `M = β a + K`, `M' = 0`,
`γ = a` (generalisation of `weakPotE`, which is the case `K = 1`). -/
def wr13e_weakPotK (hK : EWeakKernel μ a q) (ha : 0 ≤ a) (hβ : 0 ≤ β) (h : CalFeat Ψ B) (t : H) {K : ℝ}
    (ht : ∀ x, |inner ℝ t (Xi μ Ψ x)| ≤ K) : WeakPotential μ where
  φ := fun x => β * rowIntE q μ x + inner ℝ t (Xi μ Ψ x)
  q := q
  M := β * a + K
  M' := 0
  γ := a
  measurable_φ := (hK.wr1_measurable_rowInt.const_mul β).add (wr12b_measurable_inner_Xi h t)
  measurable_q := hK.meas
  q_nonneg := hK.nonneg
  q_symm := hK.symm
  γ_nonneg := ha
  φ_le := fun x => by
    have h1 : β * rowIntE q μ x ≤ β * a := mul_le_mul_of_nonneg_left (hK.wr1_rowInt_le ha x) hβ
    have h2 := (le_abs_self _).trans (ht x)
    linarith
  integrable_φ := by
    refine Integrable.of_bound
      ((hK.wr1_measurable_rowInt.const_mul β).add (wr12b_measurable_inner_Xi h t)).aestronglyMeasurable
      (β * a + K) (Filter.Eventually.of_forall fun x => ?_)
    have h1 : 0 ≤ β * rowIntE q μ x := mul_nonneg hβ (hK.wr1_rowInt_nonneg x)
    have h1' : β * rowIntE q μ x ≤ β * a := mul_le_mul_of_nonneg_left (hK.wr1_rowInt_le ha x) hβ
    have h2 := abs_le.1 (ht x)
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [h2.1, h2.2]
  neg_le_integral_φ := by
    have hi1 : Integrable (fun x => β * rowIntE q μ x) μ :=
      Integrable.of_bound (hK.wr1_measurable_rowInt.const_mul β).aestronglyMeasurable (β * a)
        (Filter.Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hβ (hK.wr1_rowInt_nonneg x))]
          exact mul_le_mul_of_nonneg_left (hK.wr1_rowInt_le ha x) hβ)
    have hi2 : Integrable (fun x => inner ℝ t (Xi μ Ψ x)) μ :=
      Integrable.of_bound (wr12b_measurable_inner_Xi h t).aestronglyMeasurable K
        (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact ht x)
    rw [integral_add hi1 hi2, wr12b_integral_inner_Xi h t, add_zero]
    have : 0 ≤ ∫ x, β * rowIntE q μ x ∂μ :=
      integral_nonneg fun x => mul_nonneg hβ (hK.wr1_rowInt_nonneg x)
    simpa using this
  integrable_q := hK.wr1_integrable_row
  row_le := fun x => hK.wr1_rowInt_le ha x

section Fields

variable (hK : EWeakKernel μ a q) (ha : 0 ≤ a) (hβ : 0 ≤ β) (h : CalFeat Ψ B) (t : H) {K : ℝ}
  (ht : ∀ x, |inner ℝ t (Xi μ Ψ x)| ≤ K)

@[simp] lemma wr13e_weakPotK_φ (x : Euc d) :
    (wr13e_weakPotK hK ha hβ h t ht).φ x = β * rowIntE q μ x + inner ℝ t (Xi μ Ψ x) := rfl

@[simp] lemma wr13e_weakPotK_q : (wr13e_weakPotK hK ha hβ h t ht).q = q := rfl

@[simp] lemma wr13e_weakPotK_M : (wr13e_weakPotK hK ha hβ h t ht).M = β * a + K := rfl

@[simp] lemma wr13e_weakPotK_M' : (wr13e_weakPotK hK ha hβ h t ht).M' = 0 := rfl

@[simp] lemma wr13e_weakPotK_γ : (wr13e_weakPotK hK ha hβ h t ht).γ = a := rfl

lemma wr13e_weakPotK_pairEnergy {n : ℕ} (y : Fin n → Euc d) :
    External.pairEnergy (wr13e_weakPotK hK ha hβ h t ht) y = External.pairEnergy (mkV_E hK ha hβ) y := rfl

end Fields

/-! ### `R0` and `RN` as weak ensembles -/

/-- The weak reference `R0 = pairGibbsLawE q N β μ` is the weak ensemble of any weak potential with kernel
`q` and one-body field `β (q*μ)`, pair coefficient `β / N`, `N` free coordinates. -/
theorem wr13e_R0_tilted (hK : EWeakKernel μ a q) (ha : 0 ≤ a) (hβ : 0 ≤ β) (hN : 0 < N)
    (V : WeakPotential μ) (hVq : V.q = q) :
    pairGibbsLawE q N β μ =
        (Measure.pi fun _ : Fin N => μ).tilted
          (fun y => ∑ i, β * rowIntE q μ (y i) - β / N * External.pairEnergy V y) ∧
      Integrable (fun y : Fin N → Euc d =>
        Real.exp (∑ i, β * rowIntE q μ (y i) - β / N * External.pairEnergy V y))
        (Measure.pi fun _ : Fin N => μ) := by
  obtain ⟨V0, hV0⟩ : ∃ V0 : WeakPotential μ, V0 = mkV_E hK ha hβ := ⟨_, rfl⟩
  have hlam : 0 ≤ β / N := div_nonneg hβ (Nat.cast_nonneg N)
  have hψ0 := isField_pinField V0 hlam (fun e : Empty => e.elim)
  have hR0 : pairGibbsLawE q N β μ
      = fieldLaw V0 (pinField V0 (β / N) (fun e : Empty => e.elim)) (β / N) N := by
    rw [hV0]; exact pairGibbsLawE_eq_pinnedLaw_E hK ha hβ hN
  have hpin : pinField V0 (β / N) (fun e : Empty => e.elim) = fun x => β * rowIntE q μ x := by
    funext x; simp [pinField, hV0, mkV_E]
  have hint0 := wr12b_integrable_exp_field (V := V0) hψ0 hlam N
  rw [hpin] at hR0 hint0
  have hV0q : V0.q = q := by rw [hV0]; rfl
  have hpe : ∀ y : Fin N → Euc d, External.pairEnergy V y = External.pairEnergy V0 y := by
    intro y; simp only [External.pairEnergy, hVq, hV0q]
  rw [wr12b_fieldLaw_eq_tilted (V := V0) (ψ := fun x => β * rowIntE q μ x) (lam := β / N) (n := N) hint0] at hR0
  simp_rw [hpe]
  exact ⟨hR0, hint0⟩

/-- `R_N` is the weak ensemble of `wr13e_weakPotK` (generalisation of `RN_eq_fieldLaw` to a field bound `K`). -/
theorem wr13e_RN_eq_fieldLawK (hK : EWeakKernel μ a q) (ha : 0 ≤ a) (hβ : 0 ≤ β) (h : CalFeat Ψ B)
    (hN : 0 < N) {K : ℝ} (ht : ∀ x, |inner ℝ (tN q μ Ψ β N) (Xi μ Ψ x)| ≤ K) :
    RN q μ Ψ β N = fieldLaw (wr13e_weakPotK hK ha hβ h (tN q μ Ψ β N) ht)
      (wr13e_weakPotK hK ha hβ h (tN q μ Ψ β N) ht).φ (β / N) N := by
  obtain ⟨V, hV⟩ : ∃ V : WeakPotential μ, V = wr13e_weakPotK hK ha hβ h (tN q μ Ψ β N) ht := ⟨_, rfl⟩
  rw [← hV]
  have hlam : 0 ≤ β / N := div_nonneg hβ (Nat.cast_nonneg N)
  have hVφ : V.φ = fun x => β * rowIntE q μ x + inner ℝ (tN q μ Ψ β N) (Xi μ Ψ x) := by
    rw [hV]; rfl
  have hVq : V.q = q := by rw [hV]; rfl
  obtain ⟨hR0, hint0⟩ := wr13e_R0_tilted hK ha hβ hN V hVq
  have hψ : IsField μ V.φ V.M V.M' :=
    ⟨V.measurable_φ, V.φ_le, V.integrable_φ, V.neg_le_integral_φ⟩
  have hint := wr12b_integrable_exp_field (V := V) hψ hlam N
  unfold RN
  rw [hR0, tilted_tilted hint0, wr12b_fieldLaw_eq_tilted (V := V) (ψ := V.φ) (lam := β / N) (n := N) hint]
  congr 1
  funext X
  simp only [Pi.add_apply, Yf, hVφ, Finset.sum_add_distrib]
  ring

/-- `R0` is a weak ensemble with the same pair part as `wr13e_weakPotK` and field `β (q*μ)`. -/
theorem wr13e_R0_eq_fieldLaw (hK : EWeakKernel μ a q) (ha : 0 ≤ a) (hβ : 0 ≤ β) (hN : 0 < N)
    (V : WeakPotential μ) (hVq : V.q = q) :
    pairGibbsLawE q N β μ = fieldLaw V (fun x => β * rowIntE q μ x) (β / N) N := by
  obtain ⟨hR0, hint0⟩ := wr13e_R0_tilted hK ha hβ hN V hVq
  rw [hR0, wr12b_fieldLaw_eq_tilted (V := V) (ψ := fun x => β * rowIntE q μ x) (lam := β / N) (n := N) hint0]

/-! ### Bounds on the calibration field and the sup bound for the first marginal -/

lemma wr13e_norm_empXi_le (h : CalFeat Ψ B) (hN : 0 < N) (X : Fin N → Euc d) :
    ‖empXi μ Ψ X‖ ≤ 2 * B := by
  unfold empXi
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have h1 : ‖∑ i, Xi μ Ψ (X i)‖ ≤ N * (2 * B) := by
    calc ‖∑ i, Xi μ Ψ (X i)‖ ≤ ∑ i, ‖Xi μ Ψ (X i)‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin N, 2 * B := Finset.sum_le_sum fun i _ => h.norm_Xi_le _
      _ = N * (2 * B) := by simp
  calc 1 / (N : ℝ) * ‖∑ i, Xi μ Ψ (X i)‖ ≤ 1 / (N : ℝ) * (N * (2 * B)) := by gcongr
    _ = 2 * B := by field_simp

/-- `|⟪t_N, Ξ x⟫| ≤ 4 β B²` for every `N ≥ 1` (torus: `abs_tN_inner_le`). -/
theorem wr13e_abs_tN_inner_le (hK : EWeakKernel μ a q) (h : CalFeat Ψ B) (hβ : 0 < β) (hN : 0 < N)
    (x : Euc d) :
    |inner ℝ (tN q μ Ψ β N) (Xi μ Ψ x)| ≤ 4 * β * B ^ 2 := by
  haveI := hK.wr11_isProb_R0 hβ.le hN
  have h1 := tN_norm_le hK h hβ hN
  have h2 : ‖∫ X, empXi μ Ψ X ∂(pairGibbsLawE q N β μ)‖ ≤ 2 * B := by
    have := norm_integral_le_of_norm_le_const (μ := pairGibbsLawE q N β μ) (f := empXi μ Ψ)
      (C := 2 * B) (Filter.Eventually.of_forall (wr13e_norm_empXi_le h hN))
    simpa using this
  have hB := h.B_nonneg
  calc |inner ℝ (tN q μ Ψ β N) (Xi μ Ψ x)| ≤ ‖tN q μ Ψ β N‖ * ‖Xi μ Ψ x‖ := abs_real_inner_le_norm _ _
    _ ≤ (β * (2 * B)) * (2 * B) :=
        mul_le_mul (h1.trans (mul_le_mul_of_nonneg_left h2 hβ.le)) (h.norm_Xi_le x) (norm_nonneg _)
          (by positivity)
    _ = 4 * β * B ^ 2 := by ring

/-- **Measure form of the sup bound**: `π^R_N ≤ e^{2βa + K} μ` for all `N ≥ 1`, for any bound `K` of the field
`⟪t_N, Ξ⟫` (torus: `firstMarginal_RN_leK`). -/
theorem wr13e_firstMarginal_RN_leK (hK : EWeakKernel μ a q) (ha : 0 ≤ a) (hβ : 0 < β) (h : CalFeat Ψ B)
    (hN : 1 ≤ N) {K : ℝ} (ht : ∀ x, |inner ℝ (tN q μ Ψ β N) (Xi μ Ψ x)| ≤ K) :
    HRS.Whole.firstMarginal (RN q μ Ψ β N) ≤
      ENNReal.ofReal (Real.exp ((β * a + K) + 0 + β * a)) • μ := by
  have hN0 : 0 < N := hN
  set V := wr13e_weakPotK hK ha hβ.le h (tN q μ Ψ β N) ht with hV
  have hRN := wr13e_RN_eq_fieldLawK hK ha hβ.le h hN0 ht
  rw [← hV] at hRN
  have hm := RefMarg.marginal_le_smul (B := Empty) V hβ.le hN0 (n := N) (by simp)
    (fun e : Empty => e.elim) ⟨0, hN0⟩
  rw [RefMarg.pinnedLaw_empty] at hm
  unfold HRS.Whole.firstMarginal
  rw [dif_pos hN0, hRN]
  exact hm

end Pot

lemma wr13e_calFeat {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {Ψ : Euc d → H}
    {k : Euc d → ℝ} (hΨ : FeatHyp Ψ k) : CalFeat Ψ (Real.sqrt (k 0)) :=
  ⟨hΨ.continuous, fun x => (hΨ.norm_eq x).le⟩

/-- **`dπ^R_N/dμ ≤ C`** (TeX `euc-reference-marginal`, first bound; torus `reference_marginal_density_le`):
`C` depends only on `(d, s, τ, βp, M)` and `k_τ(0)`, and the bound holds for every `N ≥ 1`,
`β ∈ (0, βp]`, uniformly in the probability densities `ρ ≤ M`. -/
theorem wr13e_reference_marginal_density_le (hd : 1 ≤ d) {s : ℝ} (hs : 0 < s) (hsd : s < d) {τ : ℝ}
    (hτ : 0 < τ) (βp M : ℝ) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Ψ : Euc d → H} (hΨ : FeatHyp Ψ (kTau d s τ)) :
    ∃ C : ℝ, ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ β : ℝ, 0 < β → β ≤ βp → ∀ N : ℕ, 1 ≤ N →
        HRS.Whole.firstMarginal
            (RN (fun x y : Euc d => qTau d s τ (x - y)) (HRS.Whole.withDensityReal ρ) Ψ β N)
          ≪ HRS.Whole.withDensityReal ρ ∧
        ∀ᵐ x ∂(HRS.Whole.withDensityReal ρ),
          (HRS.Whole.firstMarginal
            (RN (fun x y : Euc d => qTau d s τ (x - y)) (HRS.Whole.withDensityReal ρ) Ψ β N)).rnDeriv
              (HRS.Whole.withDensityReal ρ) x ≤ ENNReal.ofReal C := by
  set a : ℝ := wr13e_a d s τ M with ha_def
  set P : ℝ := max βp 0 with hP
  set B : ℝ := Real.sqrt (kTau d s τ 0) with hB
  have hcal : CalFeat Ψ B := wr13e_calFeat hΨ
  have ha : 0 ≤ a := wr13e_a_nonneg hs hsd hτ M
  have hB2 : B ^ 2 = kTau d s τ 0 := Real.sq_sqrt hΨ.k_zero_nonneg
  have hk0 : 0 ≤ kTau d s τ 0 := hΨ.k_zero_nonneg
  refine ⟨Real.exp (2 * P * a + 4 * P * B ^ 2), fun ρ hρ hM β hβ hβp N hN => ?_⟩
  haveI := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  set μ := HRS.Whole.withDensityReal ρ with hμ
  have hK : EWeakKernel μ a (fun x y : Euc d => qTau d s τ (x - y)) := wr13e_weak hd hs hsd hτ hρ hM
  have ht := wr13e_abs_tN_inner_le hK hcal hβ (by omega : 0 < N)
  have hle := wr13e_firstMarginal_RN_leK hK ha hβ hcal hN ht
  set C : ℝ := Real.exp (2 * P * a + 4 * P * B ^ 2) with hC
  have hβP : β ≤ P := hβp.trans (le_max_left _ _)
  have hexp : Real.exp ((β * a + 4 * β * B ^ 2) + 0 + β * a) ≤ C := by
    refine Real.exp_le_exp.2 ?_
    have h1 : β * a ≤ P * a := mul_le_mul_of_nonneg_right hβP ha
    have h2 : β * B ^ 2 ≤ P * B ^ 2 := mul_le_mul_of_nonneg_right hβP (sq_nonneg _)
    nlinarith
  have hle' : HRS.Whole.firstMarginal (RN (fun x y : Euc d => qTau d s τ (x - y)) μ Ψ β N) ≤
      μ.withDensity (fun _ => ENNReal.ofReal C) := by
    rw [withDensity_const]
    refine hle.trans ?_
    intro A
    simp only [Measure.smul_apply, smul_eq_mul]
    gcongr
  haveI : IsFiniteMeasure
      (HRS.Whole.firstMarginal (RN (fun x y : Euc d => qTau d s τ (x - y)) μ Ψ β N)) := by
    refine ⟨lt_of_le_of_lt (hle' Set.univ) ?_⟩
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, lintegral_const, measure_univ,
      mul_one]
    exact ENNReal.ofReal_lt_top
  exact HRS.PoleCavityAux.rnDeriv_le_of_le_withDensity _ _ _ hle'

/-! ### The explicit one-point density and the cavity equation -/

section Theta

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {a : ℝ} {q : Euc d → Euc d → ℝ}
  {Ψ : Euc d → H} {B β : ℝ}

/-- The explicit one-point density `θ = Θ / ∫ Θ` of the first marginal of an `(n+1)`-particle weak ensemble
(torus: `theta`). -/
def wr13e_theta (V : WeakPotential μ) (lam : ℝ) (n : ℕ) (x : Euc d) : ℝ :=
  RefMarg.cavTheta V lam n (fun e : Empty => e.elim) x /
    ∫ x', RefMarg.cavTheta V lam n (fun e : Empty => e.elim) x' ∂μ

theorem wr13e_measurable_theta (V : WeakPotential μ) {lam : ℝ} (hlam : 0 ≤ lam) (n : ℕ) :
    Measurable (wr13e_theta V lam n) :=
  (RefMarg.measurable_cavTheta V hlam (fun e : Empty => e.elim) n).div_const _

theorem wr13e_theta_pos (V : WeakPotential μ) {lam : ℝ} (hlam : 0 ≤ lam) (n : ℕ) (x : Euc d) :
    0 < wr13e_theta V lam n x :=
  div_pos (RefMarg.cavTheta_pos V hlam _ n x) (RefMarg.integral_cavTheta_pos V hlam _ n)

theorem wr13e_integral_theta (V : WeakPotential μ) {lam : ℝ} (hlam : 0 ≤ lam) (n : ℕ) :
    ∫ x, wr13e_theta V lam n x ∂μ = 1 := by
  unfold wr13e_theta
  rw [integral_div]
  exact div_self (RefMarg.integral_cavTheta_pos V hlam _ n).ne'

theorem wr13e_integrable_theta (V : WeakPotential μ) {lam : ℝ} (hlam : 0 ≤ lam) (n : ℕ) :
    Integrable (wr13e_theta V lam n) μ :=
  (RefMarg.integrable_cavTheta V hlam (fun e : Empty => e.elim) n).div_const _

/-- **The cavity equation** (pointwise): `log θ = φ + log u - log Z`. -/
theorem wr13e_log_theta_eq (V : WeakPotential μ) {lam : ℝ} (hlam : 0 ≤ lam) (n : ℕ) (x : Euc d) :
    Real.log (wr13e_theta V lam n x) = V.φ x +
      Real.log (RefMarg.cavU V lam n (fun e : Empty => e.elim) x) -
      Real.log (∫ x', RefMarg.cavTheta V lam n (fun e : Empty => e.elim) x' ∂μ) := by
  have hZ := RefMarg.integral_cavTheta_pos V hlam (fun e : Empty => e.elim) n
  have h1 := RefMarg.cavTheta_pos V hlam (fun e : Empty => e.elim) n x
  have e : RefMarg.cavTheta V lam n (fun e : Empty => e.elim) x = Real.exp (V.φ x) *
      RefMarg.cavU V lam n (fun e : Empty => e.elim) x := by
    unfold RefMarg.cavTheta; rw [RefMarg.pinField_empty]
  unfold wr13e_theta
  rw [Real.log_div h1.ne' hZ.ne', e,
    Real.log_mul (Real.exp_pos _).ne' (RefMarg.cavU_pos V hlam _ n x).ne', Real.log_exp]

/-- The first marginal of `R_{n+1}` has `μ`-density `θ` (`firstMarginal_RN_eq`). -/
theorem wr13e_firstMarginal_RN_eq (hK : EWeakKernel μ a q) (ha : 0 ≤ a) (hβ : 0 < β) (h : CalFeat Ψ B)
    {n : ℕ} {K : ℝ} (ht : ∀ x, |inner ℝ (tN q μ Ψ β (n + 1)) (Xi μ Ψ x)| ≤ K) :
    HRS.Whole.firstMarginal (RN q μ Ψ β (n + 1)) =
      μ.withDensity (fun x => ENNReal.ofReal
        (wr13e_theta (wr13e_weakPotK hK ha hβ.le h (tN q μ Ψ β (n + 1)) ht)
          (β / ((n + 1 : ℕ) : ℝ)) n x)) := by
  set V := wr13e_weakPotK hK ha hβ.le h (tN q μ Ψ β (n + 1)) ht with hV
  have hRN := wr13e_RN_eq_fieldLawK hK ha hβ.le h (Nat.succ_pos n) ht
  rw [← hV] at hRN
  have hlam : 0 ≤ β / ((n + 1 : ℕ) : ℝ) := div_nonneg hβ.le (Nat.cast_nonneg _)
  unfold HRS.Whole.firstMarginal
  rw [dif_pos (Nat.succ_pos n), hRN, ← RefMarg.pinnedLaw_empty V _ _ (fun e : Empty => e.elim)]
  exact RefMarg.marginal_eq_normalized V hlam (fun e : Empty => e.elim) (n := n) 0

/-- `Ξ̄_N = ∫ Ξ dπ_N` (all one-coordinate marginals of `R_N` coincide). -/
theorem wr13e_Xibar_eq_integral (hK : EWeakKernel μ a q) (ha : 0 ≤ a) (hβ : 0 < β) (h : CalFeat Ψ B)
    {n : ℕ} {K : ℝ} (ht : ∀ x, |inner ℝ (tN q μ Ψ β (n + 1)) (Xi μ Ψ x)| ≤ K) :
    Xibar q μ Ψ β (n + 1) = ∫ y, Xi μ Ψ y ∂(HRS.Whole.firstMarginal (RN q μ Ψ β (n + 1))) := by
  set V := wr13e_weakPotK hK ha hβ.le h (tN q μ Ψ β (n + 1)) ht with hV
  have hRN := wr13e_RN_eq_fieldLawK hK ha hβ.le h (Nat.succ_pos n) ht
  rw [← hV] at hRN
  haveI := isProb_RN hK h hβ.le (Nat.succ_pos n)
  have hmarg : ∀ i : Fin (n + 1), (RN q μ Ψ β (n + 1)).map (fun X => X i) =
      HRS.Whole.firstMarginal (RN q μ Ψ β (n + 1)) := by
    intro i
    unfold HRS.Whole.firstMarginal
    rw [dif_pos (Nat.succ_pos n)]
    rw [hRN]
    exact map_eval_eq_of_symm μ _ (measurable_fieldDensity V.measurable_φ V _ _)
      (fun σ y => fieldDensity_comp_perm V _ _ σ y) i ⟨0, Nat.succ_pos n⟩
  unfold Xibar empXi
  have hint : ∀ i : Fin (n + 1), Integrable (fun X : Fin (n + 1) → Euc d => Xi μ Ψ (X i))
      (RN q μ Ψ β (n + 1)) :=
    fun i => Integrable.of_bound (h.continuous_Xi.stronglyMeasurable.comp_measurable (measurable_pi_apply i)).aestronglyMeasurable
      (2 * B) (Filter.Eventually.of_forall fun X => h.norm_Xi_le _)
  rw [integral_smul, integral_finset_sum _ fun i _ => hint i]
  have h2 : ∀ i : Fin (n + 1), ∫ X : Fin (n + 1) → Euc d, Xi μ Ψ (X i) ∂(RN q μ Ψ β (n + 1)) =
      ∫ y, Xi μ Ψ y ∂(HRS.Whole.firstMarginal (RN q μ Ψ β (n + 1))) := by
    intro i
    rw [← hmarg i, integral_map (measurable_pi_apply i).aemeasurable
      h.continuous_Xi.stronglyMeasurable.aestronglyMeasurable]
  simp_rw [h2]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  have : (1 / ((n + 1 : ℕ) : ℝ)) * ((n + 1 : ℕ) : ℝ) = 1 := by field_simp
  rw [this, one_smul]

/-- The convolution `K_k f (x) = ∫ k(x - y) f(y) dμ(y)` (torus: `ResponseAux.Kt`). -/
def wr13e_Kt (k : Euc d → ℝ) (μ : Measure (Euc d)) (f : Euc d → ℝ) (x : Euc d) : ℝ :=
  ∫ y, k (x - y) * f y ∂μ

/-- **Calibration identity** (TeX `euc-calibration-potential`): `⟪t_N, Ξ(x)⟫ = -β (k * (θ - 1))(x) + const`,
`θ = dπ^R_N/dμ` (torus: `hh_eq`). -/
theorem wr13e_hh_eq {k : Euc d → ℝ} (hΨ : FeatHyp Ψ k) (hK : EWeakKernel μ a q) (ha : 0 ≤ a)
    (hβ : 0 < β) {n : ℕ} {K : ℝ} (ht : ∀ x, |inner ℝ (tN q μ Ψ β (n + 1)) (Xi μ Ψ x)| ≤ K) :
    ∃ c₀ : ℝ, ∀ x, inner ℝ (tN q μ Ψ β (n + 1)) (Xi μ Ψ x) =
      -β * wr13e_Kt k μ (fun y => wr13e_theta
        (wr13e_weakPotK hK ha hβ.le (wr13e_calFeat hΨ) (tN q μ Ψ β (n + 1)) ht)
        (β / ((n + 1 : ℕ) : ℝ)) n y - 1) x + c₀ := by
  have hcal := wr13e_calFeat hΨ
  set V := wr13e_weakPotK hK ha hβ.le hcal (tN q μ Ψ β (n + 1)) ht with hV
  set lam := β / ((n + 1 : ℕ) : ℝ) with hlam
  have hlam0 : 0 ≤ lam := div_nonneg hβ.le (Nat.cast_nonneg _)
  set θ := wr13e_theta V lam n with hθ
  have hθ0 : ∀ x, 0 < θ x := wr13e_theta_pos V hlam0 n
  have hθ1 : ∫ x, θ x ∂μ = 1 := wr13e_integral_theta V hlam0 n
  have hθi : Integrable θ μ := wr13e_integrable_theta V hlam0 n
  have hθm : Measurable θ := wr13e_measurable_theta V hlam0 n
  have hmarg := wr13e_firstMarginal_RN_eq hK ha hβ hcal ht (n := n)
  have hX := wr13e_Xibar_eq_integral hK ha hβ hcal ht (n := n)
  have htN := tN_eq hK hcal hβ (Nat.succ_pos n)
  set Ξ := Xi μ Ψ with hΞ
  set Ψbar := ∫ y, Ψ y ∂μ with hΨbar
  set u := Xibar q μ Ψ β (n + 1) with hu
  have hu' : u = ∫ y, θ y • Ξ y ∂μ := by
    rw [hX, hmarg, integral_withDensity_eq_integral_toReal_smul (f := fun x => ENNReal.ofReal (θ x))
      (ENNReal.measurable_ofReal.comp hθm) (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show (ENNReal.ofReal (θ y)).toReal • Ξ y = θ y • Ξ y
    rw [ENNReal.toReal_ofReal (hθ0 y).le]
  have hΞm : StronglyMeasurable Ξ := hcal.continuous_Xi.stronglyMeasurable
  have hΞi : ∀ x, Integrable (fun y => inner ℝ (Ξ x) (Ξ y) * θ y) μ := by
    intro x
    refine Integrable.bdd_mul (c := ‖Ξ x‖ * (2 * Real.sqrt (k 0))) hθi ?_ ?_
    · exact (continuous_const.inner hcal.continuous_Xi).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun y => ?_
      calc ‖inner ℝ (Ξ x) (Ξ y)‖ ≤ ‖Ξ x‖ * ‖Ξ y‖ := norm_inner_le_norm _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left (hcal.norm_Xi_le y) (norm_nonneg _)
  have hΨi : Integrable Ψ μ := hcal.integrable_Ψ
  set C1 : ℝ := ∫ y, inner ℝ Ψbar (Ψ y) * θ y ∂μ with hC1
  have hkm : ∀ x : Euc d, Measurable fun y => k (x - y) := fun x =>
    hΨ.k_continuous.measurable.comp (measurable_const.sub measurable_id)
  have hgi : ∀ x, Integrable (fun y => k (x - y) * θ y) μ := by
    intro x
    refine Integrable.bdd_mul (c := k 0) hθi ?_ (Filter.Eventually.of_forall fun y => ?_)
    · exact (hΨ.k_continuous.measurable.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    · rw [Real.norm_eq_abs]; exact hΨ.k_abs_le _
  refine ⟨-β * (inner ℝ Ψbar Ψbar - C1), fun x => ?_⟩
  have hint : Integrable (fun y => θ y • Ξ y) μ := by
    refine Integrable.mono' (hθi.mul_const (2 * Real.sqrt (k 0)))
      (hθm.stronglyMeasurable.smul hΞm).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hθ0 y)]
    exact mul_le_mul_of_nonneg_left (hcal.norm_Xi_le y) (hθ0 y).le
  have e1 : inner ℝ (tN q μ Ψ β (n + 1)) (Ξ x) = -β * inner ℝ u (Ξ x) := by
    rw [htN, real_inner_smul_left]
  have e2 : inner ℝ u (Ξ x) = ∫ y, inner ℝ (Ξ x) (Ξ y) * θ y ∂μ := by
    rw [real_inner_comm, hu', ← integral_inner hint (Ξ x)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [real_inner_smul_right]
    ring
  have hexp : ∀ y, inner ℝ (Ξ x) (Ξ y) * θ y = k (x - y) * θ y - inner ℝ (Ψ x) Ψbar * θ y -
      inner ℝ Ψbar (Ψ y) * θ y + inner ℝ Ψbar Ψbar * θ y := by
    intro y
    simp only [hΞ, Xi, ← hΨbar, inner_sub_left, inner_sub_right, hΨ.inner_eq x y]
    rw [real_inner_comm (Ψ y) Ψbar]
    ring
  have hi2 : Integrable (fun y => inner ℝ Ψbar (Ψ y) * θ y) μ := by
    refine Integrable.bdd_mul (c := ‖Ψbar‖ * Real.sqrt (k 0)) hθi
      (continuous_const.inner hΨ.continuous).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    calc ‖inner ℝ Ψbar (Ψ y)‖ ≤ ‖Ψbar‖ * ‖Ψ y‖ := norm_inner_le_norm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hcal.bound y) (norm_nonneg _)
  have e3 : ∫ y, inner ℝ (Ξ x) (Ξ y) * θ y ∂μ =
      ∫ y, k (x - y) * θ y ∂μ - inner ℝ (Ψ x) Ψbar - C1 + inner ℝ Ψbar Ψbar := by
    simp_rw [hexp]
    have j2 : Integrable (fun y => inner ℝ (Ψ x) Ψbar * θ y) μ := hθi.const_mul _
    have j4 : Integrable (fun y => inner ℝ Ψbar Ψbar * θ y) μ := hθi.const_mul _
    have j12 : Integrable (fun y => k (x - y) * θ y - inner ℝ (Ψ x) Ψbar * θ y) μ := (hgi x).sub j2
    have j123 : Integrable (fun y => k (x - y) * θ y - inner ℝ (Ψ x) Ψbar * θ y -
        inner ℝ Ψbar (Ψ y) * θ y) μ := j12.sub hi2
    rw [integral_add j123 j4, integral_sub j12 hi2, integral_sub (hgi x) j2,
      integral_const_mul, integral_const_mul, hθ1]
    ring
  have e4 : wr13e_Kt k μ (fun y => θ y - 1) x = ∫ y, k (x - y) * θ y ∂μ - inner ℝ (Ψ x) Ψbar := by
    unfold wr13e_Kt
    have hg1 : Integrable (fun y => k (x - y)) μ :=
      Integrable.of_bound (hkm x).aestronglyMeasurable (k 0)
        (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hΨ.k_abs_le _)
    have : ∫ y, k (x - y) ∂μ = inner ℝ (Ψ x) Ψbar := by
      rw [hΨbar, ← integral_inner hΨi (Ψ x)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      exact (hΨ.inner_eq x y).symm
    simp_rw [mul_sub, mul_one]
    rw [integral_sub (hgi x) hg1, this]
  rw [e1, e2, e3, e4]
  ring

end Theta

end HRS.MS.Wr
