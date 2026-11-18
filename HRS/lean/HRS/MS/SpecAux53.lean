import HRS.MS.SpecAux52
import HRS.Prob.HilbertMartingale

/-!
# S8R: the deterministic diagonal covariance form `Cdet` and its square root (S8.7, packet C5)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  `s8p_dv β om τ l = 2 β⁻¹ om_l exp(-τ om_l)` (the diagonal covariance
`b_l` of S8.7).

* `s8p_Cdet`: the bounded bilinear form `(u,v) ↦ ∑' l, dv_l u_l v_l` on `ℓ²` (a `SeqL2 →L[ℝ] SeqL2 →L[ℝ] ℝ`);
* `s8p_isTraceClassCov_Cdet`, `s8p_isDetCovDensity_Cdet`;
* `s8p_sqrt_basis`: any `S` with `IsSqrtOfForm S Cdet` acts diagonally, `S b_j = √dv_j • b_j`.
* `s8p_hsCov_apply`: `hsCovForm Φ x y = ∑_k ⟪Φ_k, x⟫⟪Φ_k, y⟫` for a finite family.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace HRS.MS.Spec

open HRS.Whole
open HRS (Euc)

/-- The diagonal covariance `b_l = 2 β⁻¹ om_l exp(-τ om_l)`. -/
def s8p_dv (β : ℝ) (om : ℕ → ℝ) (τ : ℝ) (l : ℕ) : ℝ := 2 * β⁻¹ * om l * Real.exp (-τ * om l)

theorem s8p_dv_pos {β : ℝ} (hβ : 0 < β) {om : ℕ → ℝ} (hom : ∀ l, 0 < om l) (τ : ℝ) (l : ℕ) :
    0 < s8p_dv β om τ l := by
  unfold s8p_dv; have := hom l; positivity

/-- Cauchy-Schwarz for series. -/
theorem s8p_series_cs (a b : ℕ → ℝ) (ha : Summable fun l => a l ^ 2) (hb : Summable fun l => b l ^ 2) :
    Summable (fun l => a l * b l) ∧
      (∑' l, a l * b l) ^ 2 ≤ (∑' l, a l ^ 2) * ∑' l, b l ^ 2 := by
  have hab : Summable fun l => a l * b l := by
    refine Summable.of_norm_bounded ((ha.add hb).mul_left (1 / 2)) fun l => ?_
    rw [Real.norm_eq_abs]
    rw [abs_mul]
    nlinarith [sq_nonneg (|a l| - |b l|), sq_abs (a l), sq_abs (b l)]
  refine ⟨hab, ?_⟩
  have key : ∀ t : ℝ, 0 ≤ (∑' l, a l ^ 2) * (t * t) + (2 * ∑' l, a l * b l) * t + ∑' l, b l ^ 2 := by
    intro t
    have h1 : Summable fun l => t * t * a l ^ 2 := ha.mul_left _
    have h2 : Summable fun l => 2 * t * (a l * b l) := hab.mul_left _
    have e : ∑' l, (t * a l + b l) ^ 2 = (∑' l, a l ^ 2) * (t * t) + (2 * ∑' l, a l * b l) * t +
        ∑' l, b l ^ 2 := by
      have : ∀ l, (t * a l + b l) ^ 2 = t * t * a l ^ 2 + 2 * t * (a l * b l) + b l ^ 2 := fun l => by ring
      simp_rw [this]
      rw [(h1.add h2).tsum_add hb, h1.tsum_add h2, tsum_mul_left, tsum_mul_left]
      ring
    rw [← e]
    exact tsum_nonneg fun l => sq_nonneg _
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith

theorem s8p_sqrt_mul {c : ℝ} (hc : 0 ≤ c) (x y : ℝ) :
    Real.sqrt c * x * (Real.sqrt c * y) = c * x * y := by
  have h := Real.mul_self_sqrt hc
  calc Real.sqrt c * x * (Real.sqrt c * y) = (Real.sqrt c * Real.sqrt c) * x * y := by ring
    _ = c * x * y := by rw [h]

theorem s8p_coord_add (u v : SeqL2) (l : ℕ) : SeqL2.coord (u + v) l = SeqL2.coord u l + SeqL2.coord v l :=
  rfl

theorem s8p_coord_sq_summable (z : SeqL2) : Summable fun l => SeqL2.coord z l ^ 2 :=
  u11_coord_summable z

/-- Summability of `c_l u_l v_l` for `0 ≤ c ≤ K`. -/
theorem s8p_wsum_summable {c : ℕ → ℝ} (hc : ∀ l, 0 ≤ c l) {K : ℝ} (hK : ∀ l, c l ≤ K) (u v : SeqL2) :
    Summable fun l => c l * SeqL2.coord u l * SeqL2.coord v l := by
  have hsq : ∀ z : SeqL2, Summable fun l => (Real.sqrt (c l) * SeqL2.coord z l) ^ 2 := by
    intro z
    refine Summable.of_nonneg_of_le (fun l => sq_nonneg _) (fun l => ?_)
      ((s8p_coord_sq_summable z).mul_left K)
    rw [mul_pow, Real.sq_sqrt (hc l)]
    exact mul_le_mul_of_nonneg_right (hK l) (sq_nonneg _)
  have := (s8p_series_cs _ _ (hsq u) (hsq v)).1
  exact this.congr fun l => s8p_sqrt_mul (hc l) _ _

theorem s8p_wsum_sq_le {c : ℕ → ℝ} (hc : ∀ l, 0 ≤ c l) {K : ℝ} (hK : ∀ l, c l ≤ K) (u v : SeqL2) :
    (∑' l, c l * SeqL2.coord u l * SeqL2.coord v l) ^ 2 ≤ K ^ 2 * (‖u‖ ^ 2 * ‖v‖ ^ 2) := by
  have hK0 : 0 ≤ K := (hc 0).trans (hK 0)
  have hsq : ∀ z : SeqL2, Summable fun l => (Real.sqrt (c l) * SeqL2.coord z l) ^ 2 := by
    intro z
    refine Summable.of_nonneg_of_le (fun l => sq_nonneg _) (fun l => ?_)
      ((s8p_coord_sq_summable z).mul_left K)
    rw [mul_pow, Real.sq_sqrt (hc l)]
    exact mul_le_mul_of_nonneg_right (hK l) (sq_nonneg _)
  have hcs := (s8p_series_cs _ _ (hsq u) (hsq v)).2
  have e1 : ∀ l, Real.sqrt (c l) * SeqL2.coord u l * (Real.sqrt (c l) * SeqL2.coord v l) =
      c l * SeqL2.coord u l * SeqL2.coord v l := fun l => s8p_sqrt_mul (hc l) _ _
  simp_rw [e1] at hcs
  have e2 : ∀ z : SeqL2, ∑' l, (Real.sqrt (c l) * SeqL2.coord z l) ^ 2 ≤ K * ‖z‖ ^ 2 := by
    intro z
    rw [← u11_norm_sq z, ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun l => ?_) (hsq z) ((s8p_coord_sq_summable z).mul_left K)
    rw [mul_pow, Real.sq_sqrt (hc l)]
    exact mul_le_mul_of_nonneg_right (hK l) (sq_nonneg _)
  refine hcs.trans ?_
  have h0 : ∀ z : SeqL2, 0 ≤ ∑' l, (Real.sqrt (c l) * SeqL2.coord z l) ^ 2 :=
    fun z => tsum_nonneg fun l => sq_nonneg _
  calc _ ≤ (K * ‖u‖ ^ 2) * (K * ‖v‖ ^ 2) :=
        mul_le_mul (e2 u) (e2 v) (h0 v) (by positivity)
    _ = K ^ 2 * (‖u‖ ^ 2 * ‖v‖ ^ 2) := by ring

/-- The bounded bilinear form `(u,v) ↦ ∑' l, c_l u_l v_l`. -/
def s8p_wform (c : ℕ → ℝ) (hc : ∀ l, 0 ≤ c l) (K : ℝ) (hK : ∀ l, c l ≤ K) :
    SeqL2 →L[ℝ] SeqL2 →L[ℝ] ℝ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun u v => ∑' l, c l * SeqL2.coord u l * SeqL2.coord v l)
      (fun u u' v => by
        rw [← (s8p_wsum_summable hc hK u v).tsum_add (s8p_wsum_summable hc hK u' v)]
        exact tsum_congr fun l => by rw [s8p_coord_add]; ring)
      (fun a u v => by
        rw [smul_eq_mul, ← tsum_mul_left]
        exact tsum_congr fun l => by rw [s8p_coord_smul]; ring)
      (fun u v v' => by
        rw [← (s8p_wsum_summable hc hK u v).tsum_add (s8p_wsum_summable hc hK u v')]
        exact tsum_congr fun l => by rw [s8p_coord_add]; ring)
      (fun a u v => by
        rw [smul_eq_mul, ← tsum_mul_left]
        exact tsum_congr fun l => by rw [s8p_coord_smul]; ring))
    |K|
    (fun u v => by
      have h := s8p_wsum_sq_le hc hK u v
      have hK0 : 0 ≤ K := (hc 0).trans (hK 0)
      change |∑' l, c l * SeqL2.coord u l * SeqL2.coord v l| ≤ |K| * ‖u‖ * ‖v‖
      rw [abs_of_nonneg hK0]
      refine abs_le_of_sq_le_sq ?_ (by positivity)
      calc _ ≤ K ^ 2 * (‖u‖ ^ 2 * ‖v‖ ^ 2) := h
        _ = (K * ‖u‖ * ‖v‖) ^ 2 := by ring)

theorem s8p_wform_apply (c : ℕ → ℝ) (hc : ∀ l, 0 ≤ c l) (K : ℝ) (hK : ∀ l, c l ≤ K) (u v : SeqL2) :
    s8p_wform c hc K hK u v = ∑' l, c l * SeqL2.coord u l * SeqL2.coord v l := rfl

theorem s8p_dv_nonneg {β : ℝ} (hβ : 0 < β) {om : ℕ → ℝ} (hom : ∀ l, 0 < om l) (τ : ℝ) (l : ℕ) :
    0 ≤ s8p_dv β om τ l := (s8p_dv_pos hβ hom τ l).le

theorem s8p_dv_le {β : ℝ} (hβ : 0 < β) {om : ℕ → ℝ} (hom : ∀ l, 0 < om l) {τ : ℝ} (hτ : 0 < τ)
    (l : ℕ) : s8p_dv β om τ l ≤ 4 / (β * τ) := by
  unfold s8p_dv
  have h1 := s8p_mul_exp_le hτ (hom l).le
  have h2 : Real.exp (-τ * om l / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]; have := hom l; nlinarith
  have h3 : om l * Real.exp (-τ * om l) ≤ 2 / τ := by
    refine h1.trans ?_
    calc 2 / τ * Real.exp (-τ * om l / 2) ≤ 2 / τ * 1 := by gcongr
      _ = 2 / τ := mul_one _
  calc 2 * β⁻¹ * om l * Real.exp (-τ * om l) = 2 * β⁻¹ * (om l * Real.exp (-τ * om l)) := by ring
    _ ≤ 2 * β⁻¹ * (2 / τ) := by gcongr
    _ = 4 / (β * τ) := by field_simp; ring

/-- The deterministic covariance form of S8.7. -/
def s8p_Cdet {β : ℝ} (hβ : 0 < β) {om : ℕ → ℝ} (hom : ∀ l, 0 < om l) {τ : ℝ} (hτ : 0 < τ) :
    SeqL2 →L[ℝ] SeqL2 →L[ℝ] ℝ :=
  s8p_wform (s8p_dv β om τ) (s8p_dv_nonneg hβ hom τ) (4 / (β * τ)) (s8p_dv_le hβ hom hτ)

theorem s8p_Cdet_apply {β : ℝ} (hβ : 0 < β) {om : ℕ → ℝ} (hom : ∀ l, 0 < om l) {τ : ℝ} (hτ : 0 < τ)
    (u v : SeqL2) : s8p_Cdet hβ hom hτ u v =
      ∑' l, 2 * β⁻¹ * om l * Real.exp (-τ * om l) * SeqL2.coord u l * SeqL2.coord v l := rfl

theorem s8p_coord_basis (i l : ℕ) :
    SeqL2.coord (S45.s45_seqBasis i) l = if l = i then 1 else 0 := by
  rw [← s8p_inner_basis l (S45.s45_seqBasis i)]
  have := (S45.s45_seqBasis).orthonormal
  rw [orthonormal_iff_ite] at this
  rw [real_inner_comm] at *
  simpa [eq_comm] using this l i

theorem s8p_Cdet_basis {β : ℝ} (hβ : 0 < β) {om : ℕ → ℝ} (hom : ∀ l, 0 < om l) {τ : ℝ} (hτ : 0 < τ)
    (j : ℕ) (y : SeqL2) :
    s8p_Cdet hβ hom hτ (S45.s45_seqBasis j) y = s8p_dv β om τ j * SeqL2.coord y j := by
  rw [s8p_Cdet_apply]
  rw [tsum_eq_single j]
  · rw [s8p_coord_basis]; simp [s8p_dv]
  · intro l hl
    rw [s8p_coord_basis]; simp [hl]

theorem s8p_isTraceClassCov_Cdet {β : ℝ} (hβ : 0 < β) {om : ℕ → ℝ} (hom : ∀ l, 0 < om l) {τ : ℝ}
    (hτ : 0 < τ) (hsum : Summable (s8p_dv β om τ)) :
    IsTraceClassCov (s8p_Cdet hβ hom hτ) where
  symm := fun x y => by
    rw [s8p_Cdet_apply, s8p_Cdet_apply]
    exact tsum_congr fun l => by ring
  nonneg := fun x => by
    rw [s8p_Cdet_apply]
    refine tsum_nonneg fun l => ?_
    have := s8p_dv_nonneg hβ hom τ l
    unfold s8p_dv at this
    have e : 2 * β⁻¹ * om l * Real.exp (-τ * om l) * SeqL2.coord x l * SeqL2.coord x l =
        s8p_dv β om τ l * SeqL2.coord x l ^ 2 := by unfold s8p_dv; ring
    rw [e]; positivity
  trace := ⟨ℕ, S45.s45_seqBasis, by
    refine hsum.congr fun i => ?_
    rw [s8p_Cdet_basis, s8p_coord_basis]; simp⟩

theorem s8p_isDetCovDensity_Cdet {β : ℝ} (hβ : 0 < β) {om : ℕ → ℝ} (hom : ∀ l, 0 < om l) {τ : ℝ}
    (hτ : 0 < τ) (hsum : Summable (s8p_dv β om τ)) (T : ℝ) :
    IsDetCovDensity T (fun _ => s8p_Cdet hβ hom hτ) where
  meas := fun x y => measurable_const
  traceClass := fun σ _ => s8p_isTraceClassCov_Cdet hβ hom hτ hsum
  int := integrableOn_const (by simp) (by simp)

/-- A square root of `Cdet` acts diagonally. -/
theorem s8p_sqrt_basis {β : ℝ} (hβ : 0 < β) {om : ℕ → ℝ} (hom : ∀ l, 0 < om l) {τ : ℝ}
    (hτ : 0 < τ) {S : SeqL2 →L[ℝ] SeqL2} (hS : IsSqrtOfForm S (s8p_Cdet hβ hom hτ)) (j : ℕ) :
    S (S45.s45_seqBasis j) = Real.sqrt (s8p_dv β om τ j) • S45.s45_seqBasis j := by
  set b := S45.s45_seqBasis j with hb
  set d := s8p_dv β om τ j with hd
  have hd0 : 0 < d := s8p_dv_pos hβ hom τ j
  set e := Real.sqrt d with he
  have he0 : 0 < e := Real.sqrt_pos.2 hd0
  have hee : e * e = d := Real.mul_self_sqrt hd0.le
  have hSS : S (S b) = d • b := by
    refine ext_inner_right ℝ fun y => ?_
    rw [hS.symm, hS.sq, hb, s8p_Cdet_basis, inner_smul_left, S45.s45_inner_seqBasis]
    simp [hd]
  set a := S b - e • b with ha
  have hSa : S a = -e • a := by
    rw [ha, map_sub, map_smul, hSS]
    simp only [ha, smul_sub, neg_smul, neg_sub]
    rw [← hee]
    module
  have h1 := hS.nonneg a
  rw [hSa, inner_smul_left] at h1
  simp only [conj_trivial, real_inner_self_eq_norm_sq] at h1
  have h2 : ‖a‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖a‖]
  have h3 : a = 0 := by simpa using h2
  rw [ha] at h3
  exact sub_eq_zero.1 h3

/-- The covariance form of a finite family. -/
theorem s8p_hsCov_apply {κ : Type*} [Fintype κ] {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (Φ : κ → H) (x y : H) :
    hsCovForm Φ x y = ∑ k, ⟪Φ k, x⟫ * ⟪Φ k, y⟫ := by
  unfold hsCovForm
  rw [tsum_fintype]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul]

end HRS.MS.Spec
