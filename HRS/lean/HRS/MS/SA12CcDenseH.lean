import HRS.MS.SA12LimitL16A
import HRS.MS.SA12LimitL16
import HRS.MP.RdInit

/-!
# S.A.12: smooth compactly supported cutoffs converge in `H^n` for smooth functions with `L²` jets
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Limit

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd

variable {d : ℕ}

/-- The fixed bump profile. -/
def sa12cc_bump (d : ℕ) : ContDiffBump (0 : Euc d) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The dilated cutoff `ρ_a(x) = ρ(a⁻¹ x)`. -/
def sa12cc_rho (a : ℝ) (x : Euc d) : ℝ := sa12cc_bump d (a⁻¹ • x)

theorem sa12cc_rho_contDiff (a : ℝ) : ContDiff ℝ ∞ (sa12cc_rho (d := d) a) :=
  (sa12cc_bump d).contDiff.comp (contDiff_id.const_smul a⁻¹)

theorem sa12cc_rho_nonneg (a : ℝ) (x : Euc d) : 0 ≤ sa12cc_rho a x := (sa12cc_bump d).nonneg

theorem sa12cc_rho_le_one (a : ℝ) (x : Euc d) : sa12cc_rho a x ≤ 1 := (sa12cc_bump d).le_one

theorem sa12cc_rho_one {a : ℝ} (ha : 0 < a) {x : Euc d} (hx : ‖x‖ ≤ a) : sa12cc_rho a x = 1 := by
  unfold sa12cc_rho
  apply (sa12cc_bump d).one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_inv, Real.norm_of_nonneg ha.le]
  show a⁻¹ * ‖x‖ ≤ 1
  rw [inv_mul_le_iff₀ ha]; linarith

theorem sa12cc_rho_compact {a : ℝ} (ha : 0 < a) : HasCompactSupport (sa12cc_rho (d := d) a) := by
  have h := (sa12cc_bump d).hasCompactSupport
  exact h.comp_homeomorph (Homeomorph.smulOfNeZero a⁻¹ (inv_ne_zero ha.ne'))

theorem sa12cc_rho_tendsto (x : Euc d) : Tendsto (fun a : ℝ => sa12cc_rho a x) atTop (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_ge_atTop ‖x‖] with a ha hxa
  exact (sa12cc_rho_one ha hxa).symm

/-- Uniform derivative bounds for the dilated cutoffs. -/
theorem sa12cc_rho_deriv (n : ℕ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ a : ℝ, 1 ≤ a → ∀ i : ℕ, 1 ≤ i → i ≤ n →
    ∀ x : Euc d, ‖iteratedFDeriv ℝ i (sa12cc_rho a) x‖ ≤ M / a := by
  have hex : ∀ i : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Euc d,
      ‖iteratedFDeriv ℝ i (sa12cc_bump d : Euc d → ℝ) y‖ ≤ C := by
    intro i
    have hb : ContDiff ℝ i (sa12cc_bump d : Euc d → ℝ) := (sa12cc_bump d).contDiff
    have hc : HasCompactSupport (iteratedFDeriv ℝ i (sa12cc_bump d : Euc d → ℝ)) :=
      (sa12cc_bump d).hasCompactSupport.iteratedFDeriv i
    obtain ⟨C, hC⟩ := (hb.continuous_iteratedFDeriv (le_refl _)).bounded_above_of_compact_support hc
    exact ⟨max C 0, le_max_right _ _, fun y => (hC y).trans (le_max_left _ _)⟩
  choose C hC0 hC using hex
  refine ⟨∑ i ∈ Finset.range (n + 1), C i, Finset.sum_nonneg fun i _ => hC0 i, ?_⟩
  intro a ha i hi hin x
  have ha0 : 0 < a := by linarith
  have hb : ContDiff ℝ i (sa12cc_bump d : Euc d → ℝ) := (sa12cc_bump d).contDiff
  have h1 := congrFun (iteratedFDeriv_comp_const_smul (𝕜 := ℝ) (i := i) (f := (sa12cc_bump d : Euc d → ℝ))
    a⁻¹ hb) x
  have h2 : sa12cc_rho (d := d) a = fun z => (sa12cc_bump d : Euc d → ℝ) (a⁻¹ • z) := rfl
  rw [h2, h1, norm_smul, norm_pow, norm_inv, Real.norm_of_nonneg ha0.le]
  have h3 : ‖iteratedFDeriv ℝ i (sa12cc_bump d : Euc d → ℝ) (a⁻¹ • x)‖ ≤ C i := hC i _
  have h4 : (a⁻¹) ^ i ≤ a⁻¹ := by
    refine pow_le_of_le_one (inv_nonneg.2 ha0.le) (inv_le_one_of_one_le₀ ha) (by omega)
  have h5 : C i ≤ ∑ j ∈ Finset.range (n + 1), C j :=
    Finset.single_le_sum (f := C) (fun j _ => hC0 j) (Finset.mem_range.2 (Nat.lt_succ_of_le hin))
  calc (a⁻¹) ^ i * ‖iteratedFDeriv ℝ i (sa12cc_bump d : Euc d → ℝ) (a⁻¹ • x)‖
      ≤ a⁻¹ * (∑ j ∈ Finset.range (n + 1), C j) :=
        mul_le_mul h4 (h3.trans h5) (norm_nonneg _) (inv_nonneg.2 ha0.le)
    _ = (∑ j ∈ Finset.range (n + 1), C j) / a := by rw [inv_mul_eq_div]

/-- The pointwise jet bound for the difference of two dilated cutoffs times a smooth function. -/
theorem sa12cc_jet_pt (n : ℕ) {M : ℝ} (hM0 : 0 ≤ M) (hM : ∀ a : ℝ, 1 ≤ a → ∀ i : ℕ, 1 ≤ i → i ≤ n →
      ∀ x : Euc d, ‖iteratedFDeriv ℝ i (sa12cc_rho a) x‖ ≤ M / a)
    {φ : Euc d → ℝ} (hφ : ContDiff ℝ ∞ φ) {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) {j : ℕ} (hj : j ≤ n)
    (x : Euc d) :
    ‖iteratedFDeriv ℝ j (fun y => (sa12cc_rho b y - sa12cc_rho a y) * φ y) x‖ ^ 2 ≤
      ((n + 1 : ℕ) : ℝ) * 4 ^ n * ((if a ≤ ‖x‖ then ‖iteratedFDeriv ℝ j φ x‖ ^ 2 else 0) +
        (2 * M / a) ^ 2 * ∑ l ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ l φ x‖ ^ 2) := by
  have hb1 : 1 ≤ b := ha.trans hab
  have ha0 : 0 < a := by linarith
  have hθ : ContDiff ℝ j (fun y => sa12cc_rho b y - sa12cc_rho a y) :=
    ((sa12cc_rho_contDiff (d := d) b).of_le (by exact_mod_cast le_top)).sub
      ((sa12cc_rho_contDiff (d := d) a).of_le (by exact_mod_cast le_top))
  have hφj : ContDiff ℝ j φ := hφ.of_le (by exact_mod_cast le_top)
  have hle := norm_iteratedFDeriv_mul_le hθ hφj x (n := j) le_rfl
  -- bounds on the derivatives of the difference of cutoffs
  have hθ0 : ‖iteratedFDeriv ℝ 0 (fun y => sa12cc_rho b y - sa12cc_rho a y) x‖ ≤
      if a ≤ ‖x‖ then 1 else 0 := by
    rw [norm_iteratedFDeriv_zero]
    by_cases hx : a ≤ ‖x‖
    · rw [if_pos hx, Real.norm_eq_abs, abs_le]
      constructor <;> linarith [sa12cc_rho_nonneg b x, sa12cc_rho_le_one b x,
        sa12cc_rho_nonneg a x, sa12cc_rho_le_one a x]
    · rw [if_neg hx]
      push Not at hx
      have e1 := sa12cc_rho_one ha0 hx.le
      have e2 := sa12cc_rho_one (by linarith : 0 < b) (hx.le.trans hab)
      simp [e1, e2]
  have hθi : ∀ i, 1 ≤ i → i ≤ j → ‖iteratedFDeriv ℝ i (fun y => sa12cc_rho b y - sa12cc_rho a y) x‖ ≤
      2 * M / a := by
    intro i hi1 hi
    have hs : iteratedFDeriv ℝ i (fun y => sa12cc_rho b y - sa12cc_rho a y) x =
        iteratedFDeriv ℝ i (sa12cc_rho b) x - iteratedFDeriv ℝ i (sa12cc_rho a) x := by
      have := iteratedFDeriv_sub_apply (𝕜 := ℝ) (i := i) (x := x)
        ((sa12cc_rho_contDiff (d := d) b).contDiffAt.of_le (by exact_mod_cast le_top))
        ((sa12cc_rho_contDiff (d := d) a).contDiffAt.of_le (by exact_mod_cast le_top))
      exact this
    rw [hs]
    refine (norm_sub_le _ _).trans ?_
    have h1 := hM b hb1 i hi1 (hi.trans hj) x
    have h2 := hM a ha i hi1 (hi.trans hj) x
    have h3 : M / b ≤ M / a := div_le_div_of_nonneg_left hM0 ha0 hab
    calc _ ≤ M / b + M / a := add_le_add h1 h2
      _ ≤ 2 * M / a := by rw [mul_div_assoc]; linarith
  set T : ℕ → ℝ := fun i => ‖iteratedFDeriv ℝ i (fun y => sa12cc_rho b y - sa12cc_rho a y) x‖ with hT
  set P : ℕ → ℝ := fun l => ‖iteratedFDeriv ℝ l φ x‖ with hP
  have hT0 : ∀ i, 0 ≤ T i := fun i => norm_nonneg _
  have hP0 : ∀ i, 0 ≤ P i := fun i => norm_nonneg _
  have h1 : ‖iteratedFDeriv ℝ j (fun y => (sa12cc_rho b y - sa12cc_rho a y) * φ y) x‖ ^ 2 ≤
      (∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * T i * P (j - i)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hle 2
  refine h1.trans ?_
  refine (sq_sum_le_card_mul_sum_sq).trans ?_
  rw [Finset.card_range]
  have hc4 : ∀ i ∈ Finset.range (j + 1), ((j.choose i : ℝ) * T i * P (j - i)) ^ 2 ≤
      4 ^ n * (T i * P (j - i)) ^ 2 := by
    intro i hi
    have hch : (j.choose i : ℝ) ≤ 2 ^ n := by
      have := Nat.choose_le_two_pow j i
      calc (j.choose i : ℝ) ≤ 2 ^ j := by exact_mod_cast this
        _ ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hj
    have : ((j.choose i : ℝ) * T i * P (j - i)) ^ 2 = (j.choose i : ℝ) ^ 2 * (T i * P (j - i)) ^ 2 := by
      ring
    rw [this]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    calc (j.choose i : ℝ) ^ 2 ≤ (2 ^ n) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hch 2
      _ = 4 ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have hj1 : ((j + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ hj
  calc ((j + 1 : ℕ) : ℝ) * ∑ i ∈ Finset.range (j + 1), ((j.choose i : ℝ) * T i * P (j - i)) ^ 2
      ≤ ((n + 1 : ℕ) : ℝ) * ∑ i ∈ Finset.range (j + 1), 4 ^ n * (T i * P (j - i)) ^ 2 := by
        refine mul_le_mul hj1 (Finset.sum_le_sum hc4) (Finset.sum_nonneg fun i _ => sq_nonneg _)
          (Nat.cast_nonneg _)
    _ = ((n + 1 : ℕ) : ℝ) * 4 ^ n * ∑ i ∈ Finset.range (j + 1), (T i * P (j - i)) ^ 2 := by
        rw [← Finset.mul_sum]; ring
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        have hsplit : ∑ i ∈ Finset.range (j + 1), (T i * P (j - i)) ^ 2 =
            (T 0 * P j) ^ 2 + ∑ i ∈ Finset.range j, (T (i + 1) * P (j - (i + 1))) ^ 2 := by
          rw [Finset.sum_range_succ']; simp [add_comm]
        rw [hsplit]
        refine add_le_add ?_ ?_
        · -- the term i = 0
          by_cases hx : a ≤ ‖x‖
          · rw [if_pos hx]
            have : T 0 ≤ 1 := by simpa [hT, hx] using hθ0
            rw [mul_pow]
            exact mul_le_of_le_one_left (sq_nonneg _) (pow_le_one₀ (hT0 0) this)
          · rw [if_neg hx]
            have : T 0 ≤ 0 := by simpa [hT, hx] using hθ0
            have h0 : T 0 = 0 := le_antisymm this (hT0 0)
            simp [h0]
        · -- the terms i ≥ 1
          have hterm : ∀ i ∈ Finset.range j, (T (i + 1) * P (j - (i + 1))) ^ 2 ≤
              (2 * M / a) ^ 2 * P (j - (i + 1)) ^ 2 := by
            intro i hi
            have hi' : i < j := Finset.mem_range.1 hi
            have hb : T (i + 1) ≤ 2 * M / a := hθi (i + 1) (by omega) (by omega)
            rw [mul_pow]
            exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hT0 _) hb 2) (sq_nonneg _)
          refine (Finset.sum_le_sum hterm).trans ?_
          rw [← Finset.mul_sum]
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          have hrefl : ∑ i ∈ Finset.range j, P (j - (i + 1)) ^ 2 = ∑ l ∈ Finset.range j, P l ^ 2 := by
            have := Finset.sum_range_reflect (fun l => P l ^ 2) j
            have e : ∀ i, j - (i + 1) = j - 1 - i := fun i => by omega
            exact (Finset.sum_congr rfl fun i _ => by rw [e i]).trans this
          rw [hrefl]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 (by omega))
            (fun l _ _ => sq_nonneg _)

/-- The tail jet mass. -/
def sa12cc_T (φ : Euc d → ℝ) (j : ℕ) (a : ℝ) : ℝ :=
  ∫ x, (if a ≤ ‖x‖ then ‖iteratedFDeriv ℝ j φ x‖ ^ 2 else 0)

/-- The total jet mass. -/
def sa12cc_P (φ : Euc d → ℝ) (n : ℕ) : ℝ :=
  ∑ l ∈ Finset.range (n + 1), ∫ x, ‖iteratedFDeriv ℝ l φ x‖ ^ 2

theorem sa12cc_sobolev_diff (n : ℕ) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ a : ℝ, 1 ≤ a → ∀ i : ℕ, 1 ≤ i → i ≤ n →
      ∀ x : Euc d, ‖iteratedFDeriv ℝ i (sa12cc_rho a) x‖ ≤ M / a)
    {φ : Euc d → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hint : ∀ j ≤ n, Integrable (fun x => ‖iteratedFDeriv ℝ j φ x‖ ^ 2) volume)
    {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    HRS.PDE.ToolboxRd.MemSobolev (n : ℝ) (fun y => (sa12cc_rho b y - sa12cc_rho a y) * φ y) ∧
      HRS.PDE.ToolboxRd.sobolevNormSq (n : ℝ) (fun y => (sa12cc_rho b y - sa12cc_rho a y) * φ y) ≤
        (∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * (d : ℝ) ^ j) * (((n + 1 : ℕ) : ℝ) * 4 ^ n) *
          ((∑ j ∈ Finset.range (n + 1), sa12cc_T φ j a) + (2 * M / a) ^ 2 * sa12cc_P φ n) := by
  have hb0 : 0 < b := by linarith
  have ha0 : 0 < a := by linarith
  set g : Euc d → ℝ := fun y => (sa12cc_rho b y - sa12cc_rho a y) * φ y with hg
  have hgs : ContDiff ℝ n g :=
    (((sa12cc_rho_contDiff (d := d) b).sub (sa12cc_rho_contDiff (d := d) a)).mul hφ).of_le
      (by exact_mod_cast le_top)
  have hgc : HasCompactSupport g :=
    ((sa12cc_rho_compact hb0).sub (sa12cc_rho_compact ha0)).mul_right
  obtain ⟨hmem, hnorm⟩ := HRS.MP.RdInit.mri_sobolev_deriv hgs hgc
  refine ⟨hmem, ?_⟩
  rw [hnorm]
  have hms : MeasurableSet {x : Euc d | a ≤ ‖x‖} := measurableSet_le measurable_const measurable_norm
  -- the integrated bound for one jet order
  have hRint : ∀ j ≤ n, Integrable (fun x => ((n + 1 : ℕ) : ℝ) * 4 ^ n *
      ((if a ≤ ‖x‖ then ‖iteratedFDeriv ℝ j φ x‖ ^ 2 else 0) +
        (2 * M / a) ^ 2 * ∑ l ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ l φ x‖ ^ 2)) volume := by
    intro j hj
    refine Integrable.const_mul (Integrable.add ?_ (Integrable.const_mul ?_ _)) _
    · exact (hint j hj).indicator hms
        |>.congr (Filter.Eventually.of_forall fun x => by by_cases h : a ≤ ‖x‖ <;> simp [Set.indicator, h])
    · exact integrable_finsetSum _ fun l hl => hint l (Nat.lt_succ_iff.1 (Finset.mem_range.1 hl))
  have hjet : ∀ j ≤ n, ∫ x, ‖iteratedFDeriv ℝ j g x‖ ^ 2 ≤
      ((n + 1 : ℕ) : ℝ) * 4 ^ n * (sa12cc_T φ j a + (2 * M / a) ^ 2 * sa12cc_P φ n) := by
    intro j hj
    refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => sq_nonneg _) (hRint j hj)
      (Filter.Eventually.of_forall fun x => sa12cc_jet_pt n hM0 hM hφ ha hab hj x)).trans (le_of_eq ?_)
    rw [integral_const_mul]
    congr 1
    have hi1 : Integrable (fun x => (if a ≤ ‖x‖ then ‖iteratedFDeriv ℝ j φ x‖ ^ 2 else 0)) volume :=
      ((hint j hj).indicator hms).congr
        (Filter.Eventually.of_forall fun x => by by_cases h : a ≤ ‖x‖ <;> simp [Set.indicator, h])
    have hi2 : Integrable (fun x => (2 * M / a) ^ 2 *
        ∑ l ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ l φ x‖ ^ 2) volume :=
      Integrable.const_mul (integrable_finsetSum _ fun l hl =>
        hint l (Nat.lt_succ_iff.1 (Finset.mem_range.1 hl))) _
    rw [integral_add hi1 hi2, integral_const_mul, integral_finset_sum _ fun l hl =>
      hint l (Nat.lt_succ_iff.1 (Finset.mem_range.1 hl))]
    rfl
  have hTnn : ∀ j, 0 ≤ sa12cc_T φ j a := fun j =>
    integral_nonneg fun x => by split_ifs <;> positivity
  have hPnn : 0 ≤ sa12cc_P φ n := Finset.sum_nonneg fun l _ => integral_nonneg fun x => sq_nonneg _
  have hTle : ∀ j ∈ Finset.range (n + 1), sa12cc_T φ j a ≤ ∑ j ∈ Finset.range (n + 1), sa12cc_T φ j a :=
    fun j hj => Finset.single_le_sum (f := fun j => sa12cc_T φ j a) (fun j _ => hTnn j) hj
  calc ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) *
        ∑ idx : Fin j → Fin d, ∫ x, (partialDeriv idx g x) ^ 2
      ≤ ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * ((d : ℝ) ^ j *
          (((n + 1 : ℕ) : ℝ) * 4 ^ n * (sa12cc_T φ j a + (2 * M / a) ^ 2 * sa12cc_P φ n))) := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hj' : j ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        have hcard : ∑ idx : Fin j → Fin d, ∫ x, (partialDeriv idx g x) ^ 2 ≤
            ∑ _idx : Fin j → Fin d, (((n + 1 : ℕ) : ℝ) * 4 ^ n *
              (sa12cc_T φ j a + (2 * M / a) ^ 2 * sa12cc_P φ n)) := by
          refine Finset.sum_le_sum fun idx _ => ?_
          refine le_trans ?_ (hjet j hj')
          have hgj : Integrable (fun x => ‖iteratedFDeriv ℝ j g x‖ ^ 2) volume := by
            have hc : Continuous fun x => ‖iteratedFDeriv ℝ j g x‖ ^ 2 :=
              ((hgs.continuous_iteratedFDeriv (by exact_mod_cast hj')).norm).pow 2
            refine hc.integrable_of_hasCompactSupport ?_
            exact (hgc.iteratedFDeriv (𝕜 := ℝ) j).comp_left (g := fun A => ‖A‖ ^ 2) (by simp)
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => sq_nonneg _) hgj
            (Filter.Eventually.of_forall fun x => ?_)
          simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (HRS.MP.RdInit.mri_abs_partialDeriv_le idx g x) 2
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
          nsmul_eq_mul] at hcard
        simpa using hcard
    _ ≤ _ := by
        rw [Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_le_sum fun j hj => ?_
        have h1 := hTle j hj
        have : (n.choose j : ℝ) * ((d : ℝ) ^ j *
            (((n + 1 : ℕ) : ℝ) * 4 ^ n * (sa12cc_T φ j a + (2 * M / a) ^ 2 * sa12cc_P φ n))) =
            ((n.choose j : ℝ) * (d : ℝ) ^ j) * (((n + 1 : ℕ) : ℝ) * 4 ^ n) *
              (sa12cc_T φ j a + (2 * M / a) ^ 2 * sa12cc_P φ n) := by ring
        rw [this]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith

theorem sa12cc_T_tendsto {φ : Euc d → ℝ} (j : ℕ)
    (hj : Integrable (fun x => ‖iteratedFDeriv ℝ j φ x‖ ^ 2) volume) :
    Tendsto (fun a : ℝ => sa12cc_T φ j a) atTop (𝓝 0) := by
  have hms : ∀ a : ℝ, MeasurableSet {x : Euc d | a ≤ ‖x‖} := fun a =>
    measurableSet_le measurable_const measurable_norm
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := (volume : Measure (Euc d))) (l := (atTop : Filter ℝ))
    (F := fun (a : ℝ) x => if a ≤ ‖x‖ then ‖iteratedFDeriv ℝ j φ x‖ ^ 2 else 0)
    (f := fun _ => (0 : ℝ)) (bound := fun x => ‖iteratedFDeriv ℝ j φ x‖ ^ 2)
    (Filter.Eventually.of_forall fun a => by
      refine (hj.indicator (hms a)).aestronglyMeasurable.congr (Filter.Eventually.of_forall fun x => ?_)
      by_cases h : a ≤ ‖x‖ <;> simp [Set.indicator, h])
    (Filter.Eventually.of_forall fun a => Filter.Eventually.of_forall fun x => by
      by_cases h : a ≤ ‖x‖
      · simp [h]
      · simp [h])
    hj
    (Filter.Eventually.of_forall fun x => by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop ‖x‖] with a ha
      simp [not_le.2 ha])
  simpa [sa12cc_T] using h

/-- The remainder after cutting off a smooth function with `L²` jets is small in `H^n`. -/
theorem sa12cc_remainder (n : ℕ) {φ : Euc d → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hint : ∀ j ≤ n, Integrable (fun x => ‖iteratedFDeriv ℝ j φ x‖ ^ 2) volume) :
    (∀ a : ℝ, 1 ≤ a → HRS.PDE.ToolboxRd.MemSobolev (n : ℝ) (fun x => φ x - sa12cc_rho a x * φ x)) ∧
    Tendsto (fun a : ℝ => HRS.PDE.ToolboxRd.sobolevNormSq (n : ℝ)
      (fun x => φ x - sa12cc_rho a x * φ x)) atTop (𝓝 0) := by
  obtain ⟨M, hM0, hM⟩ := sa12cc_rho_deriv (d := d) n
  set K : ℝ := (∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * (d : ℝ) ^ j) *
    (((n + 1 : ℕ) : ℝ) * 4 ^ n) with hK
  have hK0 : 0 ≤ K := by positivity
  set R : ℝ → ℝ := fun a => K * ((∑ j ∈ Finset.range (n + 1), sa12cc_T φ j a) +
    (2 * M / a) ^ 2 * sa12cc_P φ n) with hR
  have hφ2 : MemLp φ 2 volume := by
    rw [memLp_two_iff_integrable_sq hφ.continuous.aestronglyMeasurable]
    simpa using hint 0 (Nat.zero_le n)
  -- the bound for every cutoff level
  have hmain : ∀ a : ℝ, 1 ≤ a →
      HRS.PDE.ToolboxRd.MemSobolev (n : ℝ) (fun x => φ x - sa12cc_rho a x * φ x) ∧
      HRS.PDE.ToolboxRd.sobolevNormSq (n : ℝ) (fun x => φ x - sa12cc_rho a x * φ x) ≤ R a := by
    intro a ha
    have ha0 : 0 < a := by linarith
    have hdiff : ∀ b : ℝ, a ≤ b →
        HRS.PDE.ToolboxRd.MemSobolev (n : ℝ) (fun y => (sa12cc_rho b y - sa12cc_rho a y) * φ y) ∧
        HRS.PDE.ToolboxRd.sobolevNormSq (n : ℝ) (fun y => (sa12cc_rho b y - sa12cc_rho a y) * φ y) ≤ R a :=
      fun b hab => sa12cc_sobolev_diff n hM0 hM hφ hint ha hab
    have hRnn : 0 ≤ R a := by
      have := (hdiff a le_rfl).2
      exact le_trans (integral_nonneg fun ξ => by
        have := HRS.PDE.ToolboxRd.FourierAux.wt_pos (d := d) ξ
        positivity) this
    have hlsc := sa12x_weak_lsc (n : ℝ) (wn := fun k : ℕ => fun y => (sa12cc_rho (a + k) y - sa12cc_rho a y) * φ y)
      (w := fun x => φ x - sa12cc_rho a x * φ x)
      (fun k => (hdiff (a + k) (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])).1.1) ?_ ?_
      (b := Real.sqrt (R a)) ?_
    · refine ⟨hlsc.1, ?_⟩
      have := hlsc.2
      rwa [Real.sq_sqrt hRnn] at this
    · refine hφ2.sub ?_
      exact (((sa12cc_rho_contDiff (d := d) a).continuous.mul hφ.continuous)).memLp_of_hasCompactSupport
        ((sa12cc_rho_compact ha0).mul_right)
    · intro ψ hψ
      have hint1 : Integrable (fun x => φ x * ψ x) volume := hφ2.integrable_mul hψ
      refine tendsto_integral_of_dominated_convergence (fun x => |φ x * ψ x|) ?_ hint1.abs ?_ ?_
      · intro k
        have hc : Continuous fun y : Euc d => (sa12cc_rho (a + k) y - sa12cc_rho a y) * φ y :=
          (((sa12cc_rho_contDiff (d := d) (a + k)).continuous.sub
            (sa12cc_rho_contDiff (d := d) a).continuous).mul hφ.continuous)
        exact (hc.aestronglyMeasurable).mul hψ.aestronglyMeasurable
      · intro k
        refine Filter.Eventually.of_forall fun x => ?_
        rw [Real.norm_eq_abs, mul_assoc, abs_mul]
        have h1 : |sa12cc_rho (a + k) x - sa12cc_rho a x| ≤ 1 := by
          rw [abs_le]
          constructor <;> linarith [sa12cc_rho_nonneg (a + k) x, sa12cc_rho_le_one (a + k) x,
            sa12cc_rho_nonneg a x, sa12cc_rho_le_one a x]
        exact mul_le_of_le_one_left (abs_nonneg _) h1
      · refine Filter.Eventually.of_forall fun x => ?_
        have h1 : Tendsto (fun k : ℕ => sa12cc_rho (a + k) x) atTop (𝓝 1) :=
          (sa12cc_rho_tendsto x).comp (tendsto_atTop_add_const_left _ a tendsto_natCast_atTop_atTop)
        have h2 := ((h1.sub_const (sa12cc_rho a x)).mul_const (φ x * ψ x))
        convert h2 using 2
        · ring
        · ring
    · refine Filter.Eventually.frequently (Filter.Eventually.of_forall fun k => ?_)
      exact ⟨(hdiff (a + k) (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])).1, by
        have := (hdiff (a + k) (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])).2
        rwa [← Real.sq_sqrt hRnn] at this⟩
  refine ⟨fun a ha => (hmain a ha).1, ?_⟩
  -- R tends to zero
  have hRt : Tendsto R atTop (𝓝 0) := by
    have h1 : Tendsto (fun a : ℝ => ∑ j ∈ Finset.range (n + 1), sa12cc_T φ j a) atTop (𝓝 0) := by
      have := tendsto_finset_sum (Finset.range (n + 1)) fun j hj =>
        sa12cc_T_tendsto (φ := φ) j (hint j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)))
      simpa using this
    have h2 : Tendsto (fun a : ℝ => (2 * M / a) ^ 2 * sa12cc_P φ n) atTop (𝓝 0) := by
      have : Tendsto (fun a : ℝ => 2 * M / a) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
      simpa using (this.pow 2).mul_const (sa12cc_P φ n)
    simpa [hR] using (h1.add h2).const_mul K
  refine squeeze_zero' ?_ ?_ hRt
  · exact Filter.Eventually.of_forall fun a => integral_nonneg fun ξ => by
      have := HRS.PDE.ToolboxRd.FourierAux.wt_pos (d := d) ξ
      positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with a ha
    exact (hmain a ha).2

end HRS.MH.AdjointRd.Phase2SA12Limit
