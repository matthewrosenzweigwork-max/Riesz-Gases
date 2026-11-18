import HRS.MS.S21K2_W09C

/-!
# S21K2 W09D -- local compactness of the test inclusion (R26-T3.W09), part 1: jet coordinates

For a smooth `f` with `tsupport f ⊆ B_L`: every ordered partial derivative `∂_i f` is smooth with compact support in `B_L`
(`s21k2_w09_pd_smooth`, `s21k2_w09_pd_cs`), its weighted `L²` integrals are finite (`s21k2_w09_term_int`, `s21k2_w09_sq_int`,
`s21k2_w09_wE_fin`), and `weightedSobolevE r q f` is bounded by `sqrt(∑_{j<=r} d^j · max(1,(1+L²)^{-q}) · η)` when every
`∫(∂_i f)² <= η` for `j <= r` (`s21k2_w09_wE_le`).  Helper prefix `s21k2_w09_`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators FourierTransform
noncomputable section
namespace HRS.MS.R26T3
open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux
variable {d : ℕ}

theorem s21k2_w09_pd_smooth {f : HRS.Euc d → ℝ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) {j : ℕ}
    (i : Fin j → Fin d) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (HRS.Whole.partialDeriv i f) := by
  unfold HRS.Whole.partialDeriv
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => HRS.Euc d) ℝ
    (fun l => EuclideanSpace.single (i l) 1)).contDiff.comp
    (hf.iteratedFDeriv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (i := j) (by simp))

theorem s21k2_w09_fderiv_pd {f : HRS.Euc d → ℝ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) {j : ℕ}
    (i : Fin j → Fin d) (k : Fin d) (x : HRS.Euc d) :
    fderiv ℝ (HRS.Whole.partialDeriv i f) x (EuclideanSpace.single k (1 : ℝ)) =
      HRS.Whole.partialDeriv (Fin.cons k i : Fin (j + 1) → Fin d) f x := by
  have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ j f) x :=
    ((hf.iteratedFDeriv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (i := j) (by simp)).differentiable (by simp)) x
  unfold HRS.Whole.partialDeriv
  rw [hdiff.iteratedFDeriv_succ_apply_left']
  rfl

theorem s21k2_w09_pd_cs {f : HRS.Euc d → ℝ} (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) {j : ℕ} (i : Fin j → Fin d)
    {L : ℝ} (hsupp : tsupport f ⊆ Metric.closedBall 0 L) : HasCompactSupport (HRS.Whole.partialDeriv i f) :=
  HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : HRS.Euc d) L)
    ((subset_tsupport _).trans (s21k2_w09_supp (r := j) (hf.of_le (by exact_mod_cast le_top)) le_rfl i hsupp))

theorem s21k2_w09_jb_cont (q : ℝ) : Continuous (fun x : HRS.Euc d => HRS.Whole.jbracket x ^ q) := by
  have hjb : Continuous (HRS.Whole.jbracket (d := d)) := by unfold HRS.Whole.jbracket; fun_prop
  exact hjb.rpow_const fun x => Or.inl (by unfold HRS.Whole.jbracket; positivity)

theorem s21k2_w09_term_int {h : HRS.Euc d → ℝ} (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h) {L : ℝ}
    (hsupp : tsupport h ⊆ Metric.closedBall 0 L) {j : ℕ} (i : Fin j → Fin d) (q : ℝ) :
    Integrable (fun x : HRS.Euc d => HRS.Whole.jbracket x ^ (-2 * q) * (HRS.Whole.partialDeriv i h x) ^ 2) := by
  have hcont : Continuous (fun x : HRS.Euc d => HRS.Whole.jbracket x ^ (-2 * q) *
      (HRS.Whole.partialDeriv i h x) ^ 2) :=
    (s21k2_w09_jb_cont _).mul ((s21k2_w09_pd_smooth hh i).continuous.pow 2)
  have hcs : HasCompactSupport (HRS.Whole.partialDeriv i h) := s21k2_w09_pd_cs hh i hsupp
  refine hcont.integrable_of_hasCompactSupport ?_
  exact (hcs.comp_left (g := fun t : ℝ => t ^ 2) (by simp)).mul_left

theorem s21k2_w09_sq_int {h : HRS.Euc d → ℝ} (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h) {L : ℝ}
    (hsupp : tsupport h ⊆ Metric.closedBall 0 L) {j : ℕ} (i : Fin j → Fin d) :
    Integrable (fun x : HRS.Euc d => (HRS.Whole.partialDeriv i h x) ^ 2) := by
  have h0 : (fun t : ℝ => t ^ 2) 0 = 0 := by norm_num
  have hcs : HasCompactSupport ((fun t : ℝ => t ^ 2) ∘ HRS.Whole.partialDeriv i h) :=
    (s21k2_w09_pd_cs hh i hsupp).comp_left h0
  exact ((s21k2_w09_pd_smooth hh i).continuous.pow 2).integrable_of_hasCompactSupport hcs

theorem s21k2_w09_wE_fin {h : HRS.Euc d → ℝ} (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h) {L : ℝ}
    (hsupp : tsupport h ⊆ Metric.closedBall 0 L) (r : ℕ) (q : ℝ) :
    HRS.Whole.weightedSobolevE r q h < ⊤ := by
  unfold HRS.Whole.weightedSobolevE
  refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ne_of_lt ?_)
  rw [ENNReal.sum_lt_top]
  intro j _
  rw [ENNReal.sum_lt_top]
  intro i _
  exact (s21k2_w09_term_int hh hsupp i q).lintegral_lt_top

theorem s21k2_w09_wE_le {h : HRS.Euc d → ℝ} (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h) {L : ℝ}
    (hsupp : tsupport h ⊆ Metric.closedBall 0 L) (r : ℕ) (q η : ℝ) (hη : 0 ≤ η)
    (hb : ∀ j ≤ r, ∀ i : Fin j → Fin d, ∫ x, (HRS.Whole.partialDeriv i h x) ^ 2 ≤ η) :
    HRS.Whole.weightedSobolevE r q h ≤ ENNReal.ofReal (Real.sqrt
      ((∑ j ∈ Finset.range (r + 1), (d : ℝ) ^ j) * (max 1 ((1 + L ^ 2) ^ (-q)) * η))) := by
  set c : ℝ := max 1 ((1 + L ^ 2) ^ (-q)) with hc
  have hc0 : 0 ≤ c := (zero_le_one).trans (le_max_left _ _)
  have hterm : ∀ j ≤ r, ∀ i : Fin j → Fin d,
      ∫⁻ x, ENNReal.ofReal (HRS.Whole.jbracket x ^ (-2 * q) * (HRS.Whole.partialDeriv i h x) ^ 2) ≤
        ENNReal.ofReal (c * η) := by
    intro j hj i
    have hint := s21k2_w09_term_int hh hsupp i q
    have hint2 : Integrable (fun x : HRS.Euc d => (HRS.Whole.partialDeriv i h x) ^ 2) :=
      s21k2_w09_sq_int hh hsupp i
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x => by
      unfold HRS.Whole.jbracket; positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : ∫ x, HRS.Whole.jbracket x ^ (-2 * q) * (HRS.Whole.partialDeriv i h x) ^ 2 ≤
        ∫ x, c * (HRS.Whole.partialDeriv i h x) ^ 2 := by
      refine integral_mono hint (hint2.const_mul c) fun x => ?_
      by_cases hx : HRS.Whole.partialDeriv i h x = 0
      · simp [hx]
      · have hxB : ‖x‖ ≤ L := by
          have := s21k2_w09_supp (r := j) (hh.of_le (by exact_mod_cast le_top)) le_rfl i hsupp
            (subset_tsupport _ (Function.mem_support.2 hx))
          simpa using this
        exact mul_le_mul_of_nonneg_right (s21k2_w09_weight_bounds q L hxB).2 (sq_nonneg _)
    rw [integral_const_mul] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left (hb j hj i) hc0)
  unfold HRS.Whole.weightedSobolevE
  have hsum : (∑ j ∈ Finset.range (r + 1), ∑ i : Fin j → Fin d,
      ∫⁻ x, ENNReal.ofReal (HRS.Whole.jbracket x ^ (-2 * q) * (HRS.Whole.partialDeriv i h x) ^ 2)) ≤
      ENNReal.ofReal ((∑ j ∈ Finset.range (r + 1), (d : ℝ) ^ j) * (c * η)) := by
    calc _ ≤ ∑ j ∈ Finset.range (r + 1), ∑ i : Fin j → Fin d, ENNReal.ofReal (c * η) :=
          Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun i _ =>
            hterm j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) i
      _ = ENNReal.ofReal ((∑ j ∈ Finset.range (r + 1), (d : ℝ) ^ j) * (c * η)) := by
          rw [Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg fun j _ => by positivity]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
            ENNReal.ofReal_mul (by positivity)]
          simp [ENNReal.ofReal_mul hc0]
  calc _ ≤ ENNReal.ofReal ((∑ j ∈ Finset.range (r + 1), (d : ℝ) ^ j) * (c * η)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow hsum (by norm_num)
    _ = _ := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), Real.sqrt_eq_rpow]

end HRS.MS.R26T3
