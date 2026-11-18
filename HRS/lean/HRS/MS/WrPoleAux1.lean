import HRS.MS.WrTr
import HRS.MS.WrFld
import HRS.MS.WrCavAux2
import HRS.Equilibrium.PoleVariance

/-!
# HRS.MS.WrPoleAux1 -- pole variance, part 1: second moment in `H`, exponent identity, tilts (WR-13b)

Packet WR-13b (T8 of `docs/WR_B_PLAN.md`), namespace `HRS.MS.Wr`, helper prefix `wr13b_`.
Euclidean port of `HRS/Equilibrium/PoleVariance.lean` with the feature space `ℝ^M` replaced by a
separable real Hilbert space `H` and the heat split `g = q_τ + k_τ` (constant `c = 0`).

* `wr13b_field_second_moment_H`: `E ‖∑ Ψ(y_i) + c‖² ≤ 2 n E ‖Ψ(y_0)‖² + ‖E(∑ Ψ(y_i) + c)‖²` for an
  exchangeable weak ensemble with a general one-body field (Wu's inequality per direction of a finite
  orthonormal family, then `wr11b_trace_limit`);
* `wr13b_pairSum_eq`, `wr13b_exponent_identity`: the exact exponent identity of the pole law;
* the pole law as a tilt of the weak reference with the pole (`wr13b_Rpole`, `wr13b_aPole`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wr

open HRS.External

/-! ### Second moment of a vector statistic -/

section SecondMoment

variable {d : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {V : WeakPotential μ} {ψ : Euc d → ℝ}
  {M₀ M₁ lam : ℝ}

/-- Vector form of Wu's second-moment bound for an exchangeable weak ensemble with a general field. -/
theorem wr13b_field_second_moment_H {n : ℕ} [NeZero n] (hψ : IsField μ ψ M₀ M₁) (hlam : 0 ≤ lam)
    {Λ : ℝ} (hΛ : M₁ + lam * n * V.γ ≤ Λ)
    (hrow : ∀ i : Fin n, ∑ _j ∈ Finset.univ.erase i, 4 * Real.exp (M₀ + Λ) * lam * V.γ ≤ 1 / 2)
    {Ψ : Euc d → H} (hΨ : Continuous Ψ) {r : ℝ} (hr : ∀ z, ‖Ψ z‖ ≤ r) (cv : H) :
    ∫ y, ‖∑ i, Ψ (y i) + cv‖ ^ 2 ∂(fieldLaw V ψ lam n)
      ≤ 2 * n * ∫ y, ‖Ψ (y 0)‖ ^ 2 ∂(fieldLaw V ψ lam n)
        + ‖∫ y, (∑ i, Ψ (y i) + cv) ∂(fieldLaw V ψ lam n)‖ ^ 2 := by
  have hPr : IsProbabilityMeasure (fieldLaw V ψ lam n) := (fieldSpec (V := V) hψ hlam n).isProb
  set ν := fieldLaw V ψ lam n with hν
  have hr0 : 0 ≤ r := (norm_nonneg _).trans (hr 0)
  have hDc : Continuous fun y : Fin n → Euc d => ∑ i, Ψ (y i) + cv :=
    (continuous_finsetSum _ fun i _ => hΨ.comp (continuous_apply i)).add continuous_const
  have hDb : ∀ y : Fin n → Euc d, ‖∑ i, Ψ (y i) + cv‖ ≤ n * r + ‖cv‖ := fun y => by
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i, ‖Ψ (y i)‖ ≤ ∑ _i : Fin n, r := Finset.sum_le_sum fun i _ => hr _
      _ = _ := by simp
  have hDint : Integrable (fun y : Fin n → Euc d => ∑ i, Ψ (y i) + cv) ν :=
    Integrable.of_bound hDc.aestronglyMeasurable _ (Eventually.of_forall hDb)
  have hfin : ∀ (m : ℕ) (e : Fin m → H), Orthonormal ℝ e →
      ∫ y, ∑ j, (inner ℝ (e j) (∑ i, Ψ (y i) + cv)) ^ 2 ∂ν
        ≤ 2 * n * ∫ y, ‖Ψ (y 0)‖ ^ 2 ∂ν + ‖∫ y, (∑ i, Ψ (y i) + cv) ∂ν‖ ^ 2 := by
    intro m e he
    have hfm : ∀ j, Continuous fun z => inner ℝ (e j) (Ψ z) := fun j =>
      continuous_const.inner hΨ
    have hfb : ∀ j z, |inner ℝ (e j) (Ψ z)| ≤ ‖e j‖ * r := fun j z =>
      (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hr z) (norm_nonneg _))
    -- the scalar bounds
    have hscal : ∀ j, ∫ y, (inner ℝ (e j) (∑ i, Ψ (y i) + cv)) ^ 2 ∂ν ≤
        2 * n * ∫ y, (inner ℝ (e j) (Ψ (y 0))) ^ 2 ∂ν
          + (inner ℝ (e j) (∫ y, (∑ i, Ψ (y i) + cv) ∂ν)) ^ 2 := by
      intro j
      have h1 := HRS.External.PoleVar.field_second_moment_le (V := V) hψ hlam hΛ hrow
        (f := fun z => inner ℝ (e j) (Ψ z)) (hfm j).measurable (hfb j) (inner ℝ (e j) cv)
      have e1 : ∀ y : Fin n → Euc d, inner ℝ (e j) (∑ i, Ψ (y i) + cv)
          = ∑ i, inner ℝ (e j) (Ψ (y i)) + inner ℝ (e j) cv := fun y => by
        rw [inner_add_right, inner_sum]
      have hsum : Integrable (fun y : Fin n → Euc d => ∑ i, inner ℝ (e j) (Ψ (y i))) ν :=
        integrable_finsetSum _ fun i _ => Integrable.of_bound
          ((hfm j).comp (continuous_apply i)).aestronglyMeasurable (‖e j‖ * r)
          (Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hfb j _)
      have e2 : inner ℝ (e j) (∫ y, (∑ i, Ψ (y i) + cv) ∂ν)
          = ∫ y, ∑ i, inner ℝ (e j) (Ψ (y i)) ∂ν + inner ℝ (e j) cv := by
        rw [← integral_inner hDint (e j)]
        simp_rw [e1]
        rw [integral_add hsum (integrable_const _)]
        simp
      simp_rw [e1]
      rw [e2]
      exact h1
    have hint1 : ∀ j, Integrable (fun y : Fin n → Euc d => (inner ℝ (e j) (∑ i, Ψ (y i) + cv)) ^ 2) ν :=
      fun j => Integrable.of_bound
        (((continuous_const.inner hDc).pow 2).aestronglyMeasurable) ((‖e j‖ * (n * r + ‖cv‖)) ^ 2)
        (Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          have hx : |inner ℝ (e j) (∑ i, Ψ (y i) + cv)| ≤ ‖e j‖ * (n * r + ‖cv‖) :=
            (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (hDb y) (norm_nonneg _))
          exact sq_le_sq' (by linarith [abs_le.1 hx]) (by linarith [abs_le.1 hx]))
    have hint0 : ∀ j, Integrable (fun y : Fin n → Euc d => (inner ℝ (e j) (Ψ (y 0))) ^ 2) ν :=
      fun j => Integrable.of_bound
        (((continuous_const.inner (hΨ.comp (continuous_apply 0))).pow 2).aestronglyMeasurable)
        ((‖e j‖ * r) ^ 2) (Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          have hx := hfb j (y 0)
          exact sq_le_sq' (by linarith [abs_le.1 hx]) (by linarith [abs_le.1 hx]))
    rw [integral_finsetSum _ fun j _ => hint1 j]
    have hbess0 : ∀ y : Fin n → Euc d, ∑ j, (inner ℝ (e j) (Ψ (y 0))) ^ 2 ≤ ‖Ψ (y 0)‖ ^ 2 := fun y => by
      have h1 := he.sum_inner_products_le (Ψ (y 0)) (s := Finset.univ)
      simpa only [Real.norm_eq_abs, sq_abs] using h1
    have hbess1 : ∑ j, (inner ℝ (e j) (∫ y, (∑ i, Ψ (y i) + cv) ∂ν)) ^ 2
        ≤ ‖∫ y, (∑ i, Ψ (y i) + cv) ∂ν‖ ^ 2 := by
      have h1 := he.sum_inner_products_le (∫ y, (∑ i, Ψ (y i) + cv) ∂ν) (s := Finset.univ)
      simpa only [Real.norm_eq_abs, sq_abs] using h1
    have hnorm_int : Integrable (fun y : Fin n → Euc d => ‖Ψ (y 0)‖ ^ 2) ν :=
      Integrable.of_bound (((hΨ.comp (continuous_apply 0)).norm.pow 2).aestronglyMeasurable) (r ^ 2)
        (Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          exact pow_le_pow_left₀ (norm_nonneg _) (hr _) 2)
    calc ∑ j, ∫ y, (inner ℝ (e j) (∑ i, Ψ (y i) + cv)) ^ 2 ∂ν
        ≤ ∑ j, (2 * n * ∫ y, (inner ℝ (e j) (Ψ (y 0))) ^ 2 ∂ν
          + (inner ℝ (e j) (∫ y, (∑ i, Ψ (y i) + cv) ∂ν)) ^ 2) := Finset.sum_le_sum fun j _ => hscal j
      _ = 2 * n * ∫ y, ∑ j, (inner ℝ (e j) (Ψ (y 0))) ^ 2 ∂ν
          + ∑ j, (inner ℝ (e j) (∫ y, (∑ i, Ψ (y i) + cv) ∂ν)) ^ 2 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, integral_finsetSum _ fun j _ => hint0 j]
      _ ≤ 2 * n * ∫ y, ‖Ψ (y 0)‖ ^ 2 ∂ν + ‖∫ y, (∑ i, Ψ (y i) + cv) ∂ν‖ ^ 2 := by
          have h2 : ∫ y, ∑ j, (inner ℝ (e j) (Ψ (y 0))) ^ 2 ∂ν ≤ ∫ y, ‖Ψ (y 0)‖ ^ 2 ∂ν :=
            integral_mono (integrable_finsetSum _ fun j _ => hint0 j) hnorm_int hbess0
          have h3 : (0 : ℝ) ≤ 2 * n := by positivity
          nlinarith
  exact wr11b_trace_limit ν hDc.stronglyMeasurable hDb hfin

end SecondMoment

/-! ### Pair sums -/

section PairSum

variable {d : ℕ}

theorem wr13b_filter_lt {n : ℕ} (i : Fin n) : Finset.univ.filter (fun j : Fin n => i < j) = Finset.Ioi i := by
  ext j; simp

/-- For an even kernel, `∑_{i<j} g(y_i - y_j) = ½ (∑_{a,b} g(y_a - y_b) - n g(0))`. -/
theorem wr13b_pairSum_eq {g : Euc d → ℝ} (hg : ∀ z, g (-z) = g z) {n : ℕ} (y : Fin n → Euc d) :
    wr13a_pairSum g y = (1 / 2) * (∑ a, ∑ b, g (y a - y b) - n * g 0) := by
  have h1 : ∀ i : Fin n, ∑ j, g (y i - y j)
      = g 0 + (∑ j ∈ Finset.Iio i, g (y i - y j) + ∑ j ∈ Finset.Ioi i, g (y i - y j)) := by
    intro i
    have hu : (Finset.univ : Finset (Fin n)) = {i} ∪ (Finset.Iio i ∪ Finset.Ioi i) := by
      ext j
      simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_singleton, Finset.mem_Iio,
        Finset.mem_Ioi, true_iff]
      rcases lt_trichotomy j i with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    rw [hu, Finset.sum_union, Finset.sum_union]
    · simp
    · exact Finset.disjoint_left.2 fun j hj hj' => by
        simp at hj hj'; exact absurd (hj.trans hj') (lt_irrefl _)
    · refine Finset.disjoint_left.2 fun j hj hj' => ?_
      simp only [Finset.mem_singleton, Finset.mem_union, Finset.mem_Iio, Finset.mem_Ioi] at hj hj'
      rcases hj' with h | h <;> subst hj <;> exact lt_irrefl _ h
  have h2 : ∑ i, ∑ j ∈ Finset.Iio i, g (y i - y j) = ∑ j, ∑ i ∈ Finset.Ioi j, g (y j - y i) := by
    rw [Finset.sum_comm' (s := Finset.univ) (t := fun i => Finset.Iio i) (t' := Finset.univ)
      (s' := fun j => Finset.Ioi j) (fun i j => by simp)]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [← hg (y i - y j), neg_sub]
  have h3 : wr13a_pairSum g y = ∑ i, ∑ j ∈ Finset.Ioi i, g (y i - y j) := by
    unfold wr13a_pairSum
    exact Finset.sum_congr rfl fun i _ => by rw [wr13b_filter_lt]
  simp_rw [h1, Finset.sum_add_distrib, h2]
  rw [h3]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

open HRS.External in
theorem wr13b_pairEnergy_eq {μ : Measure (Euc d)} {V : WeakPotential μ} [IsProbabilityMeasure μ]
    {q : Euc d → ℝ} (hV : ∀ a b, V.q a b = q (a - b)) {n : ℕ} (y : Fin n → Euc d) :
    HRS.External.pairEnergy V y = wr13a_pairSum q y := by
  rw [pairEnergy_eq_sum_lt]
  unfold wr13a_pairSum
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [wr13b_filter_lt]
  exact Finset.sum_congr rfl fun j _ => hV _ _

end PairSum

/-! ### The exponent identity -/

section Exponent

variable {d : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {a : ℝ} {q k g : Euc d → ℝ} {Ψ : Euc d → H}

/-- The exponent of the pole law for the kernel `gs`:
`-λ ∑_{i<j} gs(y_i - y_j) + β ∑_i (gs*μ)(y_i) - tλ ∑_i gs(x - y_i)`. -/
def wr13b_EP (gs : Euc d → ℝ) (μ : Measure (Euc d)) (n : ℕ) (lam β t : ℝ) (x : Euc d)
    (Y : Fin n → Euc d) : ℝ :=
  (-lam * wr13a_pairSum gs Y + β * ∑ i, HRS.Whole.convMeasure gs μ (Y i)) + -(t * lam) * ∑ i, gs (x - Y i)

/-- The constant in `wr13b_exponent_identity`. -/
def wr13b_C0 (μ : Measure (Euc d)) (Ψ : Euc d → H) (k : Euc d → ℝ) (β lam : ℝ) (n : ℕ) (x : Euc d)
    (Xb : H) : ℝ :=
  (lam / 2) * n * k 0 + n * inner ℝ ((-β) • Xb) (∫ w, Ψ w ∂μ)
    + (lam / 2) * ‖Ψ x - ((n : ℝ) + 1) • (∫ w, Ψ w ∂μ + Xb)‖ ^ 2

theorem wr13b_q_even (h : TransferHyp μ a q k g Ψ) (z : Euc d) : q (-z) = q z := by
  have := h.weak.symm 0 z
  simpa using this

theorem wr13b_k_even (h : TransferHyp μ a q k g Ψ) (z : Euc d) : k (-z) = k z :=
  h.feat.k_symm z

theorem wr13b_sum_sum_k (h : TransferHyp μ a q k g Ψ) {n : ℕ} (y : Fin n → Euc d) :
    ∑ a, ∑ b, k (y a - y b) = ‖∑ i, Ψ (y i)‖ ^ 2 := by
  simp_rw [← h.feat.inner_eq]
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum]

theorem wr13b_integrable_q_conv (h : TransferHyp μ a q k g Ψ) (z : Euc d) :
    Integrable (fun w => q (z - w)) μ := h.weak.wr1_integrable_row z

theorem wr13b_integrable_k_conv (h : TransferHyp μ a q k g Ψ) (z : Euc d) :
    Integrable (fun w => k (z - w)) μ := by
  have : (fun w => k (z - w)) = fun w => inner ℝ (Ψ z) (Ψ w) := by
    funext w; rw [h.feat.inner_eq]
  rw [this]
  exact (h.calFeat.integrable_Ψ (μ := μ)).const_inner (Ψ z)

theorem wr13b_conv_gs (h : TransferHyp μ a q k g Ψ) (z : Euc d) :
    HRS.Whole.convMeasure (fun w => q w + k w) μ z
      = HRS.Whole.convMeasure q μ z + inner ℝ (Ψ z) (∫ w, Ψ w ∂μ) := by
  unfold HRS.Whole.convMeasure
  rw [integral_add (wr13b_integrable_q_conv h z) (wr13b_integrable_k_conv h z)]
  congr 1
  simp_rw [← h.feat.inner_eq]
  exact (integral_inner (h.calFeat.integrable_Ψ (μ := μ)) (Ψ z))

/-- **The exponent identity** (`PoleVariance.lean:362 exponent_identity`, `c = 0`, `g_L = k`). -/
theorem wr13b_exponent_identity (h : TransferHyp μ a q k g Ψ) (β lam t : ℝ) (n : ℕ)
    (hlam : β = lam * ((n : ℝ) + 1)) (x : Euc d) (Xb : H) (y : Fin n → Euc d) :
    wr13b_EP (fun w => q w + k w) μ n lam β t x y =
      (∑ i, (β * HRS.Whole.convMeasure q μ (y i) + inner ℝ ((-β) • Xb) (Xi μ Ψ (y i))
          - t * lam * q (y i - x)) - lam * wr13a_pairSum q y)
      + (-(lam / 2) * ‖∑ i, Ψ (y i) + Ψ x - ((n : ℝ) + 1) • (∫ w, Ψ w ∂μ + Xb)‖ ^ 2)
      + (1 - t) * lam * inner ℝ (Ψ x) (∑ i, Ψ (y i))
      + wr13b_C0 μ Ψ k β lam n x Xb := by
  set S : H := ∑ i, Ψ (y i) with hS
  set m : H := ∫ w, Ψ w ∂μ with hm
  have hq_even : ∀ z, q (-z) = q z := wr13b_q_even h
  have hgeven : ∀ z, (fun w => q w + k w) (-z) = (fun w => q w + k w) z := fun z => by
    simp only [hq_even z, wr13b_k_even h z]
  have ha : wr13a_pairSum (fun w => q w + k w) y = (1 / 2) * (‖S‖ ^ 2 + ∑ a, ∑ b, q (y a - y b)
      - n * (k 0 + q 0)) := by
    rw [wr13b_pairSum_eq hgeven]
    have : ∑ a, ∑ b, (fun w => q w + k w) (y a - y b) =
        ‖S‖ ^ 2 + ∑ a, ∑ b, q (y a - y b) := by
      simp only [Finset.sum_add_distrib]
      rw [wr13b_sum_sum_k h y]
      ring
    rw [this]
    ring
  have hb : wr13a_pairSum q y = (1 / 2) * (∑ a, ∑ b, q (y a - y b) - n * q 0) :=
    wr13b_pairSum_eq hq_even y
  have hc : ∑ i, HRS.Whole.convMeasure (fun w => q w + k w) μ (y i) =
      inner ℝ S m + ∑ i, HRS.Whole.convMeasure q μ (y i) := by
    simp_rw [wr13b_conv_gs h]
    rw [Finset.sum_add_distrib, hS, sum_inner]
    ring
  have hd : ∑ i, (fun w => q w + k w) (x - y i) = inner ℝ (Ψ x) S + ∑ i, q (y i - x) := by
    have : ∀ i, (fun w => q w + k w) (x - y i) = inner ℝ (Ψ x) (Ψ (y i)) + q (y i - x) := fun i => by
      simp only
      rw [h.feat.inner_eq, ← hq_even (y i - x), neg_sub]
      ring
    simp_rw [this]
    rw [Finset.sum_add_distrib, hS, inner_sum]
  have he : ∑ i, inner ℝ ((-β) • Xb) (Xi μ Ψ (y i)) =
      inner ℝ ((-β) • Xb) S - n * inner ℝ ((-β) • Xb) m := by
    simp only [Xi]
    simp_rw [inner_sub_right]
    rw [Finset.sum_sub_distrib, hS, inner_sum]
    simp
    exact Or.inl rfl
  have hnorm : ‖S + Ψ x - ((n : ℝ) + 1) • (m + Xb)‖ ^ 2 =
      ‖S‖ ^ 2 + 2 * (inner ℝ S (Ψ x) - ((n : ℝ) + 1) * (inner ℝ S m + inner ℝ S Xb))
        + ‖Ψ x - ((n : ℝ) + 1) • (m + Xb)‖ ^ 2 := by
    have : S + Ψ x - ((n : ℝ) + 1) • (m + Xb) = S + (Ψ x - ((n : ℝ) + 1) • (m + Xb)) := by abel
    rw [this, norm_add_sq_real]
    rw [inner_sub_right, inner_smul_right, inner_add_right]
  have hτ : inner ℝ ((-β) • Xb) S = -β * inner ℝ S Xb := by
    rw [inner_smul_left, real_inner_comm]
    simp
  have hsum : ∑ i, (β * HRS.Whole.convMeasure q μ (y i) + inner ℝ ((-β) • Xb) (Xi μ Ψ (y i))
          - t * lam * q (y i - x)) = β * ∑ i, HRS.Whole.convMeasure q μ (y i)
        + (inner ℝ ((-β) • Xb) S - n * inner ℝ ((-β) • Xb) m) - t * lam * ∑ i, q (y i - x) := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, he, ← Finset.mul_sum, ← Finset.mul_sum]
  unfold wr13b_EP wr13b_C0
  rw [hsum, ha, hb, hc, hd, hnorm, hτ, real_inner_comm S (Ψ x)]
  subst hlam
  ring

end Exponent

/-! ### The pole law as a bounded tilt of the weak reference with the pole -/

section Core

variable {d : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {a : ℝ} {q k g : Euc d → ℝ} {Ψ : Euc d → H}
  (h : TransferHyp μ a q k g Ψ) {β : ℝ} (hβ : 0 < β)

/-- The coupling `λ = β / (n+1)`. -/
def wr13b_lamN (β : ℝ) (n : ℕ) : ℝ := β / ((n + 1 : ℕ) : ℝ)

/-- The weak potential of the calibrated reference `R_{n+1}`. -/
abbrev wr13b_Vp (n : ℕ)
    (ht : ∀ x, |inner ℝ (tN (wr11b_dk q) μ Ψ β (n + 1)) (Xi μ Ψ x)| ≤ 1) : WeakPotential μ :=
  weakPotE h.weak h.a_nonneg hβ.le h.calFeat (tN (wr11b_dk q) μ Ψ β (n + 1)) ht

/-- The weak reference with the pole: the field `φ - tλ q(· - x)`. -/
def wr13b_Rpole (n : ℕ)
    (ht : ∀ x, |inner ℝ (tN (wr11b_dk q) μ Ψ β (n + 1)) (Xi μ Ψ x)| ≤ 1) (x : Euc d) (t : ℝ) :
    Measure (Fin n → Euc d) :=
  fieldLaw (wr13b_Vp h hβ n ht)
    (HRS.External.PoleVar.psiPole (wr13b_Vp h hβ n ht) (wr13b_lamN β n) t x) (wr13b_lamN β n) n

/-- The log-density of the pole law with respect to the weak reference with the pole. -/
def wr13b_aPole (μ : Measure (Euc d)) (Ψ : Euc d → H) (β : ℝ) (n : ℕ)
    (x : Euc d) (t : ℝ) (Xb : H) (y : Fin n → Euc d) : ℝ :=
  -(wr13b_lamN β n / 2) * ‖∑ i, Ψ (y i) + Ψ x - ((n : ℝ) + 1) • (∫ w, Ψ w ∂μ + Xb)‖ ^ 2
    + (1 - t) * wr13b_lamN β n * inner ℝ (Ψ x) (∑ i, Ψ (y i))

theorem wr13b_lamN_mul (n : ℕ) : β = wr13b_lamN β n * ((n : ℝ) + 1) := by
  unfold wr13b_lamN
  have : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [this]
  have : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp

include hβ in
theorem wr13b_lamN_nonneg (n : ℕ) : 0 ≤ wr13b_lamN β n := div_nonneg hβ.le (Nat.cast_nonneg _)

theorem wr13b_pole_tilted_eq (n : ℕ)
    (ht : ∀ x, |inner ℝ (tN (wr11b_dk q) μ Ψ β (n + 1)) (Xi μ Ψ x)| ≤ 1) (x : Euc d) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (Measure.pi fun _ : Fin n => μ).tilted
        (wr13b_EP (fun w => q w + k w) μ n (wr13b_lamN β n) β t x)
      = (wr13b_Rpole h hβ n ht x t).tilted
          (wr13b_aPole μ Ψ β n x t (Xibar (wr11b_dk q) μ Ψ β (n + 1))) := by
  have hlam0 := wr13b_lamN_nonneg hβ n
  have hψ := HRS.External.PoleVar.isField_psiPole (wr13b_Vp h hβ n ht) hlam0 ht0 ht1 x
  have hint := wr12b_integrable_exp_field (V := wr13b_Vp h hβ n ht) hψ hlam0 n
  have hq : ∀ a b, (wr13b_Vp h hβ n ht).q a b = q (a - b) := fun a b => rfl
  have htN : tN (wr11b_dk q) μ Ψ β (n + 1) = (-β) • Xibar (wr11b_dk q) μ Ψ β (n + 1) :=
    tN_eq h.weak h.calFeat hβ (Nat.succ_pos n)
  have hfun : wr13b_EP (fun w => q w + k w) μ n (wr13b_lamN β n) β t x =
      (fun y : Fin n → Euc d => ∑ i, HRS.External.PoleVar.psiPole (wr13b_Vp h hβ n ht) (wr13b_lamN β n) t x (y i)
          - wr13b_lamN β n * HRS.External.pairEnergy (wr13b_Vp h hβ n ht) y) +
      (fun y => wr13b_aPole μ Ψ β n x t (Xibar (wr11b_dk q) μ Ψ β (n + 1)) y
          + wr13b_C0 μ Ψ k β (wr13b_lamN β n) n x (Xibar (wr11b_dk q) μ Ψ β (n + 1))) := by
    funext y
    rw [wr13b_exponent_identity h β (wr13b_lamN β n) t n (wr13b_lamN_mul (β := β) n) x
      (Xibar (wr11b_dk q) μ Ψ β (n + 1)) y]
    simp only [Pi.add_apply]
    rw [wr13b_pairEnergy_eq hq y]
    have : ∑ i, HRS.External.PoleVar.psiPole (wr13b_Vp h hβ n ht) (wr13b_lamN β n) t x (y i) =
        ∑ i, (β * HRS.Whole.convMeasure q μ (y i)
          + inner ℝ ((-β) • Xibar (wr11b_dk q) μ Ψ β (n + 1)) (Xi μ Ψ (y i))
          - t * wr13b_lamN β n * q (y i - x)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [HRS.External.PoleVar.psiPole, wr13b_Vp, weakPotE_φ, weakPotE_q]
      rw [htN]
      rfl
    rw [this]
    unfold wr13b_aPole
    ring
  rw [hfun, ← tilted_tilted hint, wr11b_tilted_add_const]
  unfold wr13b_Rpole
  rw [wr12b_fieldLaw_eq_tilted hint]

theorem wr13b_isProb_Rpole (n : ℕ)
    (ht : ∀ x, |inner ℝ (tN (wr11b_dk q) μ Ψ β (n + 1)) (Xi μ Ψ x)| ≤ 1)
    (x : Euc d) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IsProbabilityMeasure (wr13b_Rpole h hβ n ht x t) := by
  have hlam0 := wr13b_lamN_nonneg hβ n
  exact (fieldSpec (V := wr13b_Vp h hβ n ht)
    (HRS.External.PoleVar.isField_psiPole (wr13b_Vp h hβ n ht) hlam0 ht0 ht1 x) hlam0 n).isProb

include h in
theorem wr13b_continuous_aPole (n : ℕ) (x : Euc d) (t : ℝ) (Xb : H) :
    Continuous (wr13b_aPole μ Ψ β n x t Xb) := by
  have hS : Continuous fun y : Fin n → Euc d => ∑ i, Ψ (y i) :=
    continuous_finsetSum _ fun i _ => h.feat.continuous.comp (continuous_apply i)
  unfold wr13b_aPole
  exact ((((hS.add continuous_const).sub continuous_const).norm.pow 2).const_mul _).add
    ((continuous_const.inner hS).const_mul _)

include h in
theorem wr13b_measurable_aPole (n : ℕ) (x : Euc d) (t : ℝ) (Xb : H) :
    Measurable (wr13b_aPole μ Ψ β n x t Xb) :=
  (wr13b_continuous_aPole h (β := β) n x t Xb).measurable

include h in
theorem wr13b_norm_sum_Ψ_le (n : ℕ) (y : Fin n → Euc d) :
    ‖∑ i, Ψ (y i)‖ ≤ n * Real.sqrt (k 0) := by
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i, ‖Ψ (y i)‖ ≤ ∑ _i : Fin n, Real.sqrt (k 0) :=
        Finset.sum_le_sum fun i _ => (h.feat.norm_eq _).le
    _ = _ := by simp

include h hβ in
theorem wr13b_abs_pert_le (n : ℕ) (x : Euc d) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (y : Fin n → Euc d) :
    |(1 - t) * wr13b_lamN β n * inner ℝ (Ψ x) (∑ i, Ψ (y i))| ≤ wr13b_lamN β n * n * k 0 := by
  have hlam0 := wr13b_lamN_nonneg hβ n
  have hk0 := h.feat.k_zero_nonneg
  have hr : Real.sqrt (k 0) * Real.sqrt (k 0) = k 0 := Real.mul_self_sqrt hk0
  have h1 : |inner ℝ (Ψ x) (∑ i, Ψ (y i))| ≤ n * k 0 := by
    calc |inner ℝ (Ψ x) (∑ i, Ψ (y i))| ≤ ‖Ψ x‖ * ‖∑ i, Ψ (y i)‖ := abs_real_inner_le_norm _ _
      _ ≤ Real.sqrt (k 0) * (n * Real.sqrt (k 0)) :=
          mul_le_mul (h.feat.norm_eq x).le (wr13b_norm_sum_Ψ_le h n y) (norm_nonneg _) (Real.sqrt_nonneg _)
      _ = n * (Real.sqrt (k 0) * Real.sqrt (k 0)) := by ring
      _ = n * k 0 := by rw [hr]
  rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - t), abs_of_nonneg hlam0]
  calc (1 - t) * wr13b_lamN β n * |inner ℝ (Ψ x) (∑ i, Ψ (y i))| ≤ 1 * wr13b_lamN β n * (n * k 0) := by
        gcongr
        linarith
    _ = _ := by ring

include h in
/-- The vector `Wv(y) = ∑ Ψ(y_i) + Ψ x - (n+1)(m + Ξ̄)` is continuous in `y`. -/
theorem wr13b_continuous_Wv (n : ℕ) (x : Euc d) (c : H) :
    Continuous fun y : Fin n → Euc d => ∑ i, Ψ (y i) + Ψ x - ((n : ℝ) + 1) • c :=
  ((continuous_finsetSum _ fun i _ => h.feat.continuous.comp (continuous_apply i)).add
    continuous_const).sub continuous_const

include h hβ in
/-- **Bounded density of the pole law with respect to the weak reference with the pole**:
`dP/dR ≤ exp(2β k(0) + (λ/2) E_R|S + Ψ x - (n+1)(m + Ξ̄)|²)`. -/
theorem wr13b_tilted_aPole_le (n : ℕ)
    (ht : ∀ x, |inner ℝ (tN (wr11b_dk q) μ Ψ β (n + 1)) (Xi μ Ψ x)| ≤ 1)
    (x : Euc d) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {Esq : ℝ}
    (hE : ∫ y, ‖∑ i, Ψ (y i) + Ψ x - ((n : ℝ) + 1) •
          (∫ w, Ψ w ∂μ + Xibar (wr11b_dk q) μ Ψ β (n + 1))‖ ^ 2 ∂(wr13b_Rpole h hβ n ht x t) ≤ Esq) :
    (wr13b_Rpole h hβ n ht x t).tilted (wr13b_aPole μ Ψ β n x t (Xibar (wr11b_dk q) μ Ψ β (n + 1))) ≤
      ENNReal.ofReal (Real.exp (2 * β * k 0 + (wr13b_lamN β n / 2) * Esq)) • wr13b_Rpole h hβ n ht x t := by
  have := wr13b_isProb_Rpole h hβ n ht x ht0 ht1
  set Pr := wr13b_Rpole h hβ n ht x t with hPr
  set Xb := Xibar (wr11b_dk q) μ Ψ β (n + 1) with hXb
  have hlam0 := wr13b_lamN_nonneg hβ n
  have hg0 := h.feat.k_zero_nonneg
  have hlamn : wr13b_lamN β n * n ≤ β := by
    have := wr13b_lamN_mul (β := β) n
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  set Wv : (Fin n → Euc d) → H := fun y =>
    ∑ i, Ψ (y i) + Ψ x - ((n : ℝ) + 1) • (∫ w, Ψ w ∂μ + Xb) with hWv
  have hWc : Continuous fun y : Fin n → Euc d => ‖Wv y‖ ^ 2 :=
    (wr13b_continuous_Wv h n x _).norm.pow 2
  have hWm : Measurable fun y : Fin n → Euc d => ‖Wv y‖ ^ 2 := hWc.measurable
  set Cn : ℝ := n * Real.sqrt (k 0) + Real.sqrt (k 0)
    + ((n : ℝ) + 1) * (Real.sqrt (k 0) + ‖Xb‖) with hCn
  have hWb : ∀ y, ‖Wv y‖ ≤ Cn := by
    intro y
    simp only [hWv]
    calc ‖∑ i, Ψ (y i) + Ψ x - ((n : ℝ) + 1) • (∫ w, Ψ w ∂μ + Xb)‖
        ≤ ‖∑ i, Ψ (y i) + Ψ x‖ + ‖((n : ℝ) + 1) • (∫ w, Ψ w ∂μ + Xb)‖ := norm_sub_le _ _
      _ ≤ (‖∑ i, Ψ (y i)‖ + ‖Ψ x‖) + ((n : ℝ) + 1) * (‖∫ w, Ψ w ∂μ‖ + ‖Xb‖) := by
          refine add_le_add (norm_add_le _ _) ?_
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
      _ ≤ _ := by
          have h1 := wr13b_norm_sum_Ψ_le h n y
          have h2 := (h.feat.norm_eq x).le
          have h3 := h.feat.norm_integral_le μ
          have : ((n : ℝ) + 1) * (‖∫ w, Ψ w ∂μ‖ + ‖Xb‖) ≤ ((n : ℝ) + 1) * (Real.sqrt (k 0) + ‖Xb‖) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          linarith
  have hnorm0 : ∀ y, 0 ≤ ‖Wv y‖ := fun y => norm_nonneg _
  set a1 : (Fin n → Euc d) → ℝ := fun y => -(wr13b_lamN β n / 2) * ‖Wv y‖ ^ 2 with ha1
  set a2 : (Fin n → Euc d) → ℝ := fun y => (1 - t) * wr13b_lamN β n * inner ℝ (Ψ x) (∑ i, Ψ (y i)) with ha2
  have ha : wr13b_aPole μ Ψ β n x t Xb = fun y => a1 y + a2 y := rfl
  have ha1m : Measurable a1 := hWm.const_mul _
  have ha2m : Measurable a2 := by
    have hS : Continuous fun y : Fin n → Euc d => ∑ i, Ψ (y i) :=
      continuous_finsetSum _ fun i _ => h.feat.continuous.comp (continuous_apply i)
    exact ((continuous_const.inner hS).const_mul _).measurable
  have ha1b : ∀ y, |a1 y| ≤ (wr13b_lamN β n / 2) * Cn ^ 2 := by
    intro y
    simp only [ha1]
    rw [abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ wr13b_lamN β n / 2),
      abs_of_nonneg (sq_nonneg _)]
    gcongr
    exact hWb y
  have ha2b : ∀ y, |a2 y| ≤ wr13b_lamN β n * n * k 0 := fun y => wr13b_abs_pert_le h hβ n x ht0 ht1 y
  have ha1i : Integrable a1 Pr := wr11_integrable_of_abs_le ha1m _ ha1b
  have ha2i : Integrable a2 Pr := wr11_integrable_of_abs_le ha2m _ ha2b
  have hWi : Integrable (fun y : Fin n → Euc d => ‖Wv y‖ ^ 2) Pr := by
    refine wr11_integrable_of_abs_le hWm (Cn ^ 2) fun y => ?_
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (hnorm0 y) (hWb y) 2
  have hA : ∀ y, wr13b_aPole μ Ψ β n x t Xb y ≤ β * k 0 := by
    intro y
    show a1 y + a2 y ≤ _
    have h1 : a1 y ≤ 0 := by
      simp only [ha1]
      have : 0 ≤ (wr13b_lamN β n / 2) * ‖Wv y‖ ^ 2 := by positivity
      linarith
    have h2 := (le_abs_self _).trans (ha2b y)
    have h3 : wr13b_lamN β n * n * k 0 ≤ β * k 0 := mul_le_mul_of_nonneg_right hlamn hg0
    linarith
  have hB : ∀ y, |wr13b_aPole μ Ψ β n x t Xb y| ≤
      (wr13b_lamN β n / 2) * Cn ^ 2 + wr13b_lamN β n * n * k 0 := by
    intro y
    show |a1 y + a2 y| ≤ _
    exact (abs_add_le _ _).trans (add_le_add (ha1b y) (ha2b y))
  have hJ := HRS.External.PoleVar.tilted_le_smul_jensen (ν := Pr)
    (wr13b_measurable_aPole h (β := β) n x t Xb) hA hB
  refine hJ.trans ?_
  have hint1 : ∫ y, a1 y ∂Pr = -(wr13b_lamN β n / 2) * ∫ y, ‖Wv y‖ ^ 2 ∂Pr := by
    simp only [ha1]
    rw [integral_const_mul]
  have hint2 : -(wr13b_lamN β n * n * k 0) ≤ ∫ y, a2 y ∂Pr := by
    have : ∫ y, -(wr13b_lamN β n * n * k 0) ∂Pr ≤ ∫ y, a2 y ∂Pr :=
      integral_mono (integrable_const _) ha2i fun y => (abs_le.1 (ha2b y)).1
    simpa using this
  have hsplit : ∫ y, wr13b_aPole μ Ψ β n x t Xb y ∂Pr = ∫ y, a1 y ∂Pr + ∫ y, a2 y ∂Pr := by
    rw [ha]
    exact integral_add ha1i ha2i
  have hE' : -(wr13b_lamN β n / 2) * ∫ y, ‖Wv y‖ ^ 2 ∂Pr ≥ -(wr13b_lamN β n / 2) * Esq := by
    have : ∫ y, ‖Wv y‖ ^ 2 ∂Pr ≤ Esq := hE
    nlinarith
  have hlow : -(wr13b_lamN β n / 2) * Esq - β * k 0 ≤ ∫ y, wr13b_aPole μ Ψ β n x t Xb y ∂Pr := by
    rw [hsplit, hint1]
    have h3 : wr13b_lamN β n * n * k 0 ≤ β * k 0 := mul_le_mul_of_nonneg_right hlamn hg0
    linarith
  intro S
  rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
  exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by linarith))) _

end Core

end HRS.MS.Wr
