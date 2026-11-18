import HRS.MS.WlSphAux1
import HRS.MS.WrFeat
import HRS.MS.WrCal

/-!
# WL-1 (part 2): the tensor feature map of the spherical head, `FeatHypP`, the energy identity

Packet WL-1 of `docs/WR_LOG_PLAN.md`, namespace `HRS.MS.Wl`, helper prefix `wl_`.

* `wl_w x = (1, u x)/√2 ∈ ℝ^(d+2)` has `‖w x‖ = 1` and `⟨w x, w y⟩ = τ x y` (`wl_w_inner`).
* `wl_psiG e : Euc d → EuclideanSpace ℝ (Σ j : κ, (Fin (e j + 1) → Fin (d+2)))`,
  `Ψ x (j, I) = (2 (e j + 1))^(-1/2) ∏_k w x (I k)`, has `⟪Ψ x, Ψ y⟫ = ∑_j (1/2) τ^(e j+1)/(e j+1)`
  (`wl_psiG_inner`, by `Finset.prod_univ_sum`) and is continuous.
* `wl_psi M := wl_psiG (j : Fin M ↦ j)`: `⟪Ψ x, Ψ y⟫ = km M x y`, `‖Ψ x‖² = k0 M` (`wl_psi_hyp`);
  `wl_psiBand M L := wl_psiG (j : Fin (L - M) ↦ M + j)` (`M ≤ L`): `⟪Ψ x, Ψ y⟫ = band M L x y`,
  `‖Ψ x‖² = k0 L - k0 M` (`wl_psiBand_hyp`).
* `FeatHypP Ψ k k0` (continuous, `⟪Ψ x, Ψ y⟫ = k x y`, `k x x = k0`), the pair-kernel version of
  `HRS.MS.Wr.FeatHyp`; `FeatHypP.norm_Xi_le` (`‖Ψ x - ∫ Ψ dμ‖ ≤ 2 √k0`, port of `WrFeat.FeatHyp.norm_Xi_le`),
  `energy_identity_P` (port of `energy_identity_E`: `N * pairEnergy k X μ = ½ ‖N^{-1/2} ∑ (Ψ (X i) - ∫ Ψ dμ)‖² - ½ k0`)
  and `FeatHypP.calFeat : CalFeat Ψ (√k0)` (`WrCal`).

Statement adjustments (documented): the index type of the feature map is a general `Σ j : κ, ...` with
a degree function `e : κ → ℕ`, specialised to `κ = Fin M` (`Fin (j+1)` fibres, as in the brief) and to the band;
`k0` is a parameter of `FeatHypP` as requested.
-/

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

noncomputable section

namespace HRS.MS.Wl

open HRS.Whole HRS.MS.Thm

variable {d : ℕ}

/-! ### The one-particle vector `w x = (1, u x)/√2` -/

/-- `w x = (1, stereoInv x)/√2 ∈ ℝ^(d+2)`. -/
def wl_w (x : Euc d) : Fin (d + 2) → ℝ :=
  Fin.cons (α := fun _ => ℝ) (1 / Real.sqrt 2) (fun i : Fin (d + 1) => stereoInv x i / Real.sqrt 2)

lemma wl_w_continuous (a : Fin (d + 2)) : Continuous (fun x : Euc d => wl_w x a) := by
  refine Fin.cases ?_ (fun i => ?_) a
  · simp only [wl_w, Fin.cons_zero]; exact continuous_const
  · simp only [wl_w, Fin.cons_succ]
    exact ((PiLp.continuous_apply 2 _ i).comp t67_stereo_continuous).div_const _

/-- `⟨w x, w y⟩ = τ x y`. -/
lemma wl_w_inner (x y : Euc d) : ∑ a : Fin (d + 2), wl_w x a * wl_w y a = wl_tau x y := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have h2' : Real.sqrt 2 ≠ 0 := by positivity
  rw [Fin.sum_univ_succ]
  simp only [wl_w, Fin.cons_zero, Fin.cons_succ]
  unfold wl_tau
  have : inner ℝ (stereoInv x) (stereoInv y) = ∑ i : Fin (d + 1), stereoInv x i * stereoInv y i := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [this]
  have e1 : ∑ i : Fin (d + 1), stereoInv x i / Real.sqrt 2 * (stereoInv y i / Real.sqrt 2)
      = (∑ i : Fin (d + 1), stereoInv x i * stereoInv y i) / 2 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
    rw [h2]
    ring
  rw [e1]
  field_simp
  rw [h2]
  ring

/-! ### The general tensor feature -/

/-- The index type of the tensor feature of degree function `e`. -/
abbrev WlIdx (d : ℕ) {κ : Type*} (e : κ → ℕ) := Σ j : κ, (Fin (e j + 1) → Fin (d + 2))

/-- `Ψ x (j, I) = (2 (e j + 1))^(-1/2) ∏_k w x (I k)`. -/
def wl_psiG {κ : Type*} (e : κ → ℕ) (x : Euc d) : EuclideanSpace ℝ (WlIdx d e) :=
  WithLp.toLp 2 (fun p : WlIdx d e => (Real.sqrt (2 * ((e p.1 : ℝ) + 1)))⁻¹ * ∏ k, wl_w x (p.2 k))

lemma wl_psiG_continuous {κ : Type*} [Fintype κ] (e : κ → ℕ) :
    Continuous (wl_psiG (d := d) e) := by
  unfold wl_psiG
  refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun p => ?_)
  exact continuous_const.mul (continuous_finsetProd _ fun k _ => wl_w_continuous _)

/-- `⟪Ψ x, Ψ y⟫ = ∑_j (1/2) τ^(e j + 1)/(e j + 1)`. -/
theorem wl_psiG_inner {κ : Type*} [Fintype κ] (e : κ → ℕ) (x y : Euc d) :
    inner ℝ (wl_psiG e x) (wl_psiG e y) = ∑ j : κ, wl_term (wl_tau x y) (e j) := by
  unfold wl_psiG
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hc : (Real.sqrt (2 * ((e j : ℝ) + 1)))⁻¹ * (Real.sqrt (2 * ((e j : ℝ) + 1)))⁻¹
      = 1 / (2 * ((e j : ℝ) + 1)) := by
    rw [← mul_inv, Real.mul_self_sqrt (by positivity)]; simp
  have hp : ∑ I : Fin (e j + 1) → Fin (d + 2), ∏ k, (wl_w x (I k) * wl_w y (I k))
      = (wl_tau x y) ^ (e j + 1) := by
    have := Finset.prod_univ_sum (fun _ : Fin (e j + 1) => (Finset.univ : Finset (Fin (d + 2))))
      (fun _ a => wl_w x a * wl_w y a)
    rw [Fintype.piFinset_univ] at this
    rw [← this]
    simp [wl_w_inner]
  calc ∑ I : Fin (e j + 1) → Fin (d + 2),
        ((Real.sqrt (2 * ((e j : ℝ) + 1)))⁻¹ * ∏ k, wl_w y (I k)) *
          ((Real.sqrt (2 * ((e j : ℝ) + 1)))⁻¹ * ∏ k, wl_w x (I k))
      = ((Real.sqrt (2 * ((e j : ℝ) + 1)))⁻¹ * (Real.sqrt (2 * ((e j : ℝ) + 1)))⁻¹) *
          ∑ I : Fin (e j + 1) → Fin (d + 2), ∏ k, (wl_w x (I k) * wl_w y (I k)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun I _ => ?_
        rw [Finset.prod_mul_distrib]; ring
    _ = wl_term (wl_tau x y) (e j) := by
        rw [hc, hp]; unfold wl_term; field_simp

/-! ### `FeatHypP` -/

/-- Hypothesis of an abstract Hilbert feature map for a pair kernel `k` with constant diagonal `k0`:
`Ψ` is continuous, `⟪Ψ x, Ψ y⟫ = k x y`, `k x x = k0`. -/
structure FeatHypP {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Ψ : Euc d → H) (k : Euc d → Euc d → ℝ) (k0 : ℝ) : Prop where
  continuous : Continuous Ψ
  inner_eq : ∀ x y : Euc d, inner ℝ (Ψ x) (Ψ y) = k x y
  diag : ∀ x : Euc d, k x x = k0

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {Ψ : Euc d → H}
  {k : Euc d → Euc d → ℝ} {k0 : ℝ}

theorem FeatHypP.norm_sq (h : FeatHypP Ψ k k0) (x : Euc d) : ‖Ψ x‖ ^ 2 = k0 := by
  rw [← real_inner_self_eq_norm_sq, h.inner_eq x x, h.diag x]

theorem FeatHypP.k0_nonneg (h : FeatHypP Ψ k k0) (x : Euc d) : 0 ≤ k0 := by
  rw [← h.norm_sq x]; positivity

theorem FeatHypP.norm_eq (h : FeatHypP Ψ k k0) (x : Euc d) : ‖Ψ x‖ = Real.sqrt k0 := by
  rw [← h.norm_sq x, Real.sqrt_sq (norm_nonneg _)]

theorem FeatHypP.symm (h : FeatHypP Ψ k k0) (x y : Euc d) : k x y = k y x := by
  rw [← h.inner_eq, ← h.inner_eq, real_inner_comm]

theorem FeatHypP.abs_le (h : FeatHypP Ψ k k0) (x y : Euc d) : |k x y| ≤ k0 := by
  rw [← h.inner_eq]
  refine (abs_real_inner_le_norm _ _).trans ?_
  rw [h.norm_eq, h.norm_eq]
  exact (Real.mul_self_sqrt (h.k0_nonneg x)).le

theorem FeatHypP.k_continuous (h : FeatHypP Ψ k k0) :
    Continuous (fun p : Euc d × Euc d => k p.1 p.2) := by
  have : (fun p : Euc d × Euc d => k p.1 p.2) = fun p => inner ℝ (Ψ p.1) (Ψ p.2) := by
    funext p; rw [h.inner_eq]
  rw [this]
  exact (h.continuous.comp continuous_fst).inner (h.continuous.comp continuous_snd)

/-- `Ψ` is Bochner integrable against every finite measure (it is bounded by `√k0`). -/
theorem FeatHypP.integrable (h : FeatHypP Ψ k k0) (μ : Measure (Euc d)) [IsFiniteMeasure μ] :
    Integrable Ψ μ :=
  Integrable.of_bound h.continuous.aestronglyMeasurable (Real.sqrt k0)
    (Filter.Eventually.of_forall fun x => le_of_eq (h.norm_eq x))

theorem FeatHypP.norm_integral_le (h : FeatHypP Ψ k k0) (μ : Measure (Euc d))
    [IsProbabilityMeasure μ] : ‖∫ y, Ψ y ∂μ‖ ≤ Real.sqrt k0 := by
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := Ψ) (C := Real.sqrt k0)
    (Filter.Eventually.of_forall fun x => le_of_eq (h.norm_eq x))
  simpa using this

/-- `‖Ξ‖ ≤ 2 √k0` for the centred feature `Ξ = Ψ - ∫ Ψ dμ` (port of `FeatHyp.norm_Xi_le`). -/
theorem FeatHypP.norm_Xi_le (h : FeatHypP Ψ k k0) (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    (x : Euc d) : ‖HRS.MS.Wr.featXi Ψ μ x‖ ≤ 2 * Real.sqrt k0 := by
  unfold HRS.MS.Wr.featXi
  calc ‖Ψ x - ∫ y, Ψ y ∂μ‖ ≤ ‖Ψ x‖ + ‖∫ y, Ψ y ∂μ‖ := norm_sub_le _ _
    _ ≤ Real.sqrt k0 + Real.sqrt k0 := by
        rw [h.norm_eq x]; exact add_le_add le_rfl (h.norm_integral_le μ)
    _ = 2 * Real.sqrt k0 := by ring

/-- A `FeatHypP` feature map is a `CalFeat` with bound `√k0` (`WrCal:81`). -/
theorem FeatHypP.calFeat (h : FeatHypP Ψ k k0) : HRS.MS.Wr.CalFeat Ψ (Real.sqrt k0) where
  cont := h.continuous
  bound x := le_of_eq (h.norm_eq x)

variable [CompleteSpace H]

/-! ### The energy identity -/

theorem wl_inner_mean (h : FeatHypP Ψ k k0) (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    (x : Euc d) : inner ℝ (Ψ x) (∫ y, Ψ y ∂μ) = ∫ y, k x y ∂μ := by
  rw [← integral_inner (h.integrable μ) (Ψ x)]
  simp only [h.inner_eq]

theorem wl_inner_mean' (h : FeatHypP Ψ k k0) (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    (y : Euc d) : inner ℝ (∫ z, Ψ z ∂μ) (Ψ y) = ∫ z, k y z ∂μ := by
  rw [real_inner_comm (Ψ y) (∫ z, Ψ z ∂μ)]
  exact wl_inner_mean h μ y

theorem wl_inner_mm (h : FeatHypP Ψ k k0) (μ : Measure (Euc d)) [IsProbabilityMeasure μ] :
    inner ℝ (∫ z, Ψ z ∂μ) (∫ z, Ψ z ∂μ) = ∫ x, ∫ y, k x y ∂μ ∂μ := by
  rw [← integral_inner (h.integrable μ) (∫ z, Ψ z ∂μ)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => wl_inner_mean' h μ y)

theorem wl_inner_centered (h : FeatHypP Ψ k k0) (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    (x y : Euc d) :
    inner ℝ (Ψ x - ∫ z, Ψ z ∂μ) (Ψ y - ∫ z, Ψ z ∂μ) =
      k x y - (∫ z, k x z ∂μ) - (∫ z, k y z ∂μ) + ∫ w, ∫ z, k w z ∂μ ∂μ := by
  rw [inner_sub_left, inner_sub_right, inner_sub_right, h.inner_eq x y, wl_inner_mean h μ x,
    wl_inner_mean' h μ y, wl_inner_mm h μ]
  ring

theorem wl_norm_sum_sq (h : FeatHypP Ψ k k0) (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    {N : ℕ} (X : EucConfig d N) :
    ‖∑ i, (Ψ (X i) - ∫ z, Ψ z ∂μ)‖ ^ 2 =
      ∑ i, ∑ j, (k (X i) (X j) - (∫ z, k (X i) z ∂μ) - (∫ z, k (X j) z ∂μ)
        + ∫ w, ∫ z, k w z ∂μ ∂μ) := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact wl_inner_centered h μ (X i) (X j)

/-- **Energy identity** (pair-kernel form, port of `energy_identity_E`): for a feature map `Ψ` with
Gram kernel `k x y` and constant diagonal `k0`, a probability measure `μ`, `1 ≤ N` and every
configuration `X`,
`N * 𝖥_N^k(X, μ) = ½ ‖N^{-1/2} ∑ (Ψ (X i) - ∫ Ψ dμ)‖² - ½ k0`. -/
theorem energy_identity_P (h : FeatHypP Ψ k k0) (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    {N : ℕ} (hN : 1 ≤ N) (X : EucConfig d N) :
    (N : ℝ) * pairEnergy k X μ =
      (1 / 2) * ‖(Real.sqrt N)⁻¹ • ∑ i, (Ψ (X i) - ∫ y, Ψ y ∂μ)‖ ^ 2 - (1 / 2) * k0 := by
  have hB : ‖(Real.sqrt N)⁻¹ • ∑ i, (Ψ (X i) - ∫ y, Ψ y ∂μ)‖ ^ 2 =
      (N : ℝ)⁻¹ * ∑ i, ∑ j, (k (X i) (X j) - (∫ z, k (X i) z ∂μ) - (∫ z, k (X j) z ∂μ)
        + ∫ w, ∫ z, k w z ∂μ ∂μ) := by
    rw [HRS.MS.Wr.wr10_scale, wl_norm_sum_sq h μ X]
  rw [hB]
  unfold pairEnergy
  exact HRS.MS.Wr.wr10_core N hN (fun i j => k (X i) (X j)) (fun i => ∫ z, k (X i) z ∂μ)
    (∫ w, ∫ z, k w z ∂μ ∂μ) k0 (fun i => h.diag _)

end Abstract

/-! ### The concrete features -/

/-- The tensor feature of the head `km M`: `Ψ x (j, I) = (2(j+1))^(-1/2) ∏_k w x (I k)`,
`j : Fin M`, `I : Fin (j+1) → Fin (d+2)`. -/
def wl_psi (M : ℕ) : Euc d → EuclideanSpace ℝ (Σ j : Fin M, (Fin ((j : ℕ) + 1) → Fin (d + 2))) :=
  wl_psiG (fun j : Fin M => (j : ℕ))

/-- `⟪Ψ x, Ψ y⟫ = km M x y`. -/
theorem wl_psi_inner (M : ℕ) (x y : Euc d) : inner ℝ (wl_psi M x) (wl_psi M y) = wl_km M x y := by
  unfold wl_psi wl_km
  rw [wl_psiG_inner]
  exact Fin.sum_univ_eq_sum_range (fun j => wl_term (wl_tau x y) j) M

theorem wl_psi_continuous (M : ℕ) : Continuous (wl_psi (d := d) M) := wl_psiG_continuous _

/-- `FeatHypP (wl_psi M) (km M) (k0 M)`. -/
theorem wl_psi_hyp (M : ℕ) : FeatHypP (wl_psi (d := d) M) (wl_km M) (wl_k0 M) where
  continuous := wl_psi_continuous M
  inner_eq := wl_psi_inner M
  diag := wl_km_diag M

/-- `‖Ψ x‖² = k0 M`. -/
theorem wl_psi_norm_sq (M : ℕ) (x : Euc d) : ‖wl_psi M x‖ ^ 2 = wl_k0 M :=
  (wl_psi_hyp M).norm_sq x

/-- The tensor feature of the band `(M, L]` (terms `j ∈ [M, L)`). -/
def wl_psiBand (M L : ℕ) : Euc d → EuclideanSpace ℝ (WlIdx d (fun j : Fin (L - M) => M + (j : ℕ))) :=
  wl_psiG (fun j : Fin (L - M) => M + (j : ℕ))

theorem wl_psiBand_inner {M L : ℕ} (hML : M ≤ L) (x y : Euc d) :
    inner ℝ (wl_psiBand M L x) (wl_psiBand M L y) = wl_band M L x y := by
  unfold wl_psiBand
  rw [wl_psiG_inner, wl_band_eq_sum_Ico hML, Finset.sum_Ico_eq_sum_range]
  exact Fin.sum_univ_eq_sum_range (fun j => wl_term (wl_tau x y) (M + j)) (L - M)

theorem wl_psiBand_continuous (M L : ℕ) : Continuous (wl_psiBand (d := d) M L) :=
  wl_psiG_continuous _

/-- `FeatHypP (wl_psiBand M L) (band M L) (k0 L - k0 M)` for `M ≤ L`. -/
theorem wl_psiBand_hyp {M L : ℕ} (hML : M ≤ L) :
    FeatHypP (wl_psiBand (d := d) M L) (wl_band M L) (wl_k0 L - wl_k0 M) where
  continuous := wl_psiBand_continuous M L
  inner_eq := wl_psiBand_inner hML
  diag := wl_band_diag M L

/-- `‖Ψ x‖² = k0 L - k0 M` for the band feature. -/
theorem wl_psiBand_norm_sq {M L : ℕ} (hML : M ≤ L) (x : Euc d) :
    ‖wl_psiBand M L x‖ ^ 2 = wl_k0 L - wl_k0 M :=
  (wl_psiBand_hyp hML).norm_sq x

/-- `CalFeat (wl_psi M) (√(k0 M))`. -/
theorem wl_psi_calFeat (M : ℕ) : HRS.MS.Wr.CalFeat (wl_psi (d := d) M) (Real.sqrt (wl_k0 M)) :=
  (wl_psi_hyp M).calFeat

end HRS.MS.Wl
