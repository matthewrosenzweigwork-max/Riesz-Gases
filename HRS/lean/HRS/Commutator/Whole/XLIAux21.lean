import HRS.Commutator.Whole.XLIAux20

/-!
# X-LI part 21: the synthesis estimate `‖∑ U_k‖_r ≲ ‖(∑ |U_k|²)^{1/2}‖_r`
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff Convolution Topology SchwartzMap

noncomputable section

namespace HRS.Commutator.Whole.XLI

open HRS.Commutator.Whole

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- the dual function `om = |V|^{r-2} V̄` -/
def omg (r : ℝ) (V : SchwartzMap 𝔼 ℂ) (x : 𝔼) : ℂ :=
  (((‖V x‖ ^ (r - 2) : ℝ) : ℂ)) * (starRingEnd ℂ) (V x)

lemma omg_meas (r : ℝ) (V : SchwartzMap 𝔼 ℂ) : Measurable (omg r V) := by
  have h1 : Measurable fun x => ‖V x‖ := V.continuous.norm.measurable
  exact (Complex.measurable_ofReal.comp (h1.pow_const _)).mul
    (Complex.continuous_conj.measurable.comp V.continuous.measurable)

lemma norm_omg {r : ℝ} (hr : 1 < r) (V : SchwartzMap 𝔼 ℂ) (x : 𝔼) :
    ‖omg r V x‖ = ‖V x‖ ^ (r - 1) := by
  by_cases hv : V x = 0
  · unfold omg
    simp [hv, Real.zero_rpow (show r - 1 ≠ 0 by linarith)]
  · have hpos : 0 < ‖V x‖ := norm_pos_iff.2 hv
    unfold omg
    rw [norm_mul, Complex.norm_real, Complex.norm_conj, Real.norm_of_nonneg (Real.rpow_nonneg hpos.le _)]
    rw [← Real.rpow_add_one hpos.ne']
    congr 1; ring

lemma mul_omg {r : ℝ} (hr : 1 < r) (V : SchwartzMap 𝔼 ℂ) (x : 𝔼) :
    V x * omg r V x = ((‖V x‖ ^ r : ℝ) : ℂ) := by
  by_cases hv : V x = 0
  · unfold omg
    simp [hv, Real.zero_rpow (show r ≠ 0 by linarith)]
  · have hpos : 0 < ‖V x‖ := norm_pos_iff.2 hv
    unfold omg
    have h1 : V x * ((((‖V x‖ ^ (r - 2) : ℝ) : ℂ)) * (starRingEnd ℂ) (V x)) =
        (((‖V x‖ ^ (r - 2) : ℝ) : ℂ)) * (V x * (starRingEnd ℂ) (V x)) := by ring
    rw [h1, Complex.mul_conj']
    have h2 : ‖V x‖ ^ r = ‖V x‖ ^ (r - 2) * ‖V x‖ ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hpos]
      congr 1; push_cast; ring
    rw [h2]
    push_cast
    ring

lemma rhoT_symK_even (k : ℤ) (z : 𝔼) : symK (rhoT : 𝔼 → ℂ) k (-z) = symK (rhoT : 𝔼 → ℂ) k z :=
  symK_even (fun η => by
    show rhoT (-η) = rhoT η
    exact rhoT_neg η) k z

/-- the pairing identity for one frequency piece -/
lemma pair_piece (U : SchwartzMap 𝔼 ℂ) (k : ℤ)
    (hrep : ∀ x, U x = cv (symK (rhoT : 𝔼 → ℂ) k) ⇑U x) {r : ℝ} (hr : 1 < r)
    (V : SchwartzMap 𝔼 ℂ) :
    ∫ x, U x * omg r V x = ∫ y, U y * cv (symK (rhoT : 𝔼 → ℂ) k) (omg r V) y := by
  obtain ⟨CV, hCV0, hCV⟩ := sch_bdd V
  have hB : ∀ x, ‖omg r V x‖ ≤ CV ^ (r - 1) := by
    intro x
    rw [norm_omg hr]
    exact Real.rpow_le_rpow (norm_nonneg _) (hCV x) (by linarith)
  have h1 : ∫ x, U x * omg r V x = ∫ x, cv (symK (rhoT : 𝔼 → ℂ) k) ⇑U x * omg r V x :=
    integral_congr_ae (Eventually.of_forall fun x => by beta_reduce; rw [← hrep x])
  rw [h1, adj_cv (symK_integrable rhoT_contDiff rhoT_cs k)
    (symK_continuous rhoT_contDiff rhoT_cs k).measurable U.integrable U.continuous.measurable
    (omg_meas r V) hB]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  have : (fun z => symK (rhoT : 𝔼 → ℂ) k (-z)) = symK (rhoT : 𝔼 → ℂ) k :=
    funext fun z => rhoT_symK_even k z
  rw [this]

lemma SYN (hd : 1 ≤ d) {r : ℝ} (hr : 1 < r)
    (hE : E1At (fun j => symK (rhoT : 𝔼 → ℂ) j) (r.conjExponent / 2)) :
    ∃ C : ℝ≥0, ∀ (S : Finset ℤ) (U : ℤ → SchwartzMap 𝔼 ℂ),
      (∀ k x, U k x = cv (symK (rhoT : 𝔼 → ℂ) k) ⇑(U k) x) →
      ∫⁻ x, ‖(∑ k ∈ S, U k) x‖ₑ ^ r ≤ (C : ℝ≥0∞) * ∫⁻ x, (∑ k ∈ S, ‖U k x‖ₑ ^ 2) ^ (r / 2) := by
  obtain ⟨CE, hCE⟩ := hE
  set r' : ℝ := r.conjExponent with hr'
  have hconj : r.HolderConjugate r' := Real.HolderConjugate.conjExponent hr
  have hr'1 : 1 < r' := (Real.holderConjugate_iff.1 hconj.symm).1
  have hr0 : 0 < r := by linarith
  have hrr' : (r - 1) * r' = r := by
    have h1 : r⁻¹ + r'⁻¹ = 1 := hconj.inv_add_inv_eq_one
    have hr'0 : r' ≠ 0 := by linarith
    field_simp at h1
    nlinarith
  refine ⟨CE ^ (r - 1), fun S U hrep => ?_⟩
  set V : SchwartzMap 𝔼 ℂ := ∑ k ∈ S, U k with hV
  set N : ℝ≥0∞ := ∫⁻ x, ‖V x‖ₑ ^ r with hN
  have hNeq : N = ∫⁻ x, ENNReal.ofReal (‖V x‖ ^ r) := by
    refine lintegral_congr fun x => ?_
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hr0.le]
  have hVr : Integrable (fun x => ‖V x‖ ^ r) := schwartz_rpow_integrable V hr0
  have hNtop : N ≠ ⊤ := by
    rw [hNeq]; exact hVr.lintegral_lt_top.ne
  by_cases hN0 : N = 0
  · rw [hN0]; exact zero_le
  -- the dual function
  obtain ⟨CV, hCV0, hCV⟩ := sch_bdd V
  set om : 𝔼 → ℂ := omg r V with hom
  have hB : ∀ x, ‖om x‖ ≤ CV ^ (r - 1) := by
    intro x
    rw [hom, norm_omg hr]
    exact Real.rpow_le_rpow (norm_nonneg _) (hCV x) (by linarith)
  have homi : Integrable om := by
    have h1 : Integrable (fun x => ‖V x‖ ^ (r - 1)) := schwartz_rpow_integrable V (by linarith)
    refine (integrable_norm_iff (omg_meas r V).aestronglyMeasurable).1 ?_
    refine h1.congr (Eventually.of_forall fun x => ?_)
    exact (norm_omg hr V x).symm
  have home : ∀ x, ‖om x‖ₑ ≤ ENNReal.ofReal (CV ^ (r - 1)) := by
    intro x
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hB x)
  -- `N = ‖∫ V om‖`
  have hVomint : ∀ k ∈ S, Integrable (fun x => U k x * om x) := by
    intro k _
    refine Integrable.mul_bdd (c := CV ^ (r - 1)) (U k).integrable
      (omg_meas r V).aestronglyMeasurable (Eventually.of_forall hB) |>.congr ?_
    exact Eventually.of_forall fun x => by ring
  have hI : ∫ x, V x * om x = ∑ k ∈ S, ∫ y, U k y * cv (symK (rhoT : 𝔼 → ℂ) k) om y := by
    have e1 : ∀ x, V x * om x = ∑ k ∈ S, U k x * om x := by
      intro x
      rw [hV, sum_apply_schwartz, Finset.sum_mul]
    simp_rw [e1]
    rw [integral_finsetSum _ hVomint]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact pair_piece (U k) k (hrep k) hr V
  have hNI : N = ‖∫ x, V x * om x‖ₑ := by
    have e : ∀ x, V x * om x = ((‖V x‖ ^ r : ℝ) : ℂ) := fun x => mul_omg hr V x
    simp_rw [e]
    rw [integral_complex_ofReal, ← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (integral_nonneg fun x =>
      Real.rpow_nonneg (norm_nonneg _) _), hNeq]
    exact (ofReal_integral_eq_lintegral_ofReal hVr (Eventually.of_forall fun x =>
      Real.rpow_nonneg (norm_nonneg _) _)).symm
  -- Hölder
  set A : 𝔼 → ℝ≥0∞ := fun x => (∑ k ∈ S, ‖U k x‖ₑ ^ 2) ^ (1 / 2 : ℝ) with hA
  set B' : 𝔼 → ℝ≥0∞ := fun x =>
    (sqS (fun j => cv (symK (rhoT : 𝔼 → ℂ) j) om) x) ^ (1 / 2 : ℝ) with hB'
  have hUm : ∀ k, Measurable (fun x => ‖U k x‖ₑ) := fun k => (U k).continuous.measurable.enorm
  have hAm : Measurable A :=
    (Finset.measurable_sum _ fun k _ => (hUm k).pow_const 2).pow_const _
  have hcvm : ∀ j, Measurable (cv (symK (rhoT : 𝔼 → ℂ) j) om) := fun j =>
    measurable_cv (symK_continuous rhoT_contDiff rhoT_cs j).measurable (omg_meas r V)
  have hB'm : Measurable B' := (sqS_measurable hcvm).pow_const _
  have step1 : N ≤ ∫⁻ x, A x * B' x := by
    rw [hNI]
    calc ‖∫ x, V x * om x‖ₑ = ‖∑ k ∈ S, ∫ y, U k y * cv (symK (rhoT : 𝔼 → ℂ) k) om y‖ₑ := by
          rw [hI]
      _ ≤ ∑ k ∈ S, ‖∫ y, U k y * cv (symK (rhoT : 𝔼 → ℂ) k) om y‖ₑ := enorm_sum_le _ _
      _ ≤ ∑ k ∈ S, ∫⁻ y, ‖U k y‖ₑ * ‖cv (symK (rhoT : 𝔼 → ℂ) k) om y‖ₑ := by
          refine Finset.sum_le_sum fun k _ => ?_
          refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
          refine lintegral_congr fun y => ?_
          simp [enorm_mul]
      _ = ∫⁻ y, ∑ k ∈ S, ‖U k y‖ₑ * ‖cv (symK (rhoT : 𝔼 → ℂ) k) om y‖ₑ := by
          rw [lintegral_finset_sum]
          intro k _
          exact (hUm k).mul (hcvm k).enorm
      _ ≤ ∫⁻ y, A y * B' y := by
          refine lintegral_mono fun y => ?_
          have h1 := ENNReal.inner_le_Lp_mul_Lq S (fun k => ‖U k y‖ₑ)
            (fun k => ‖cv (symK (rhoT : 𝔼 → ℂ) k) om y‖ₑ) Real.HolderConjugate.two_two
          simp only [ENNReal.rpow_two] at h1
          have h2 : (∑ k ∈ S, ‖cv (symK (rhoT : 𝔼 → ℂ) k) om y‖ₑ ^ 2) ^ (1 / 2 : ℝ) ≤ B' y :=
            ENNReal.rpow_le_rpow (ENNReal.sum_le_tsum S) (by norm_num)
          exact h1.trans (mul_le_mul_right h2 _)
  -- Hölder in `x`
  have step2 : ∫⁻ x, A x * B' x ≤ (∫⁻ x, A x ^ r) ^ (1 / r) * (∫⁻ x, B' x ^ r') ^ (1 / r') :=
    ENNReal.lintegral_mul_le_Lp_mul_Lq volume hconj hAm.aemeasurable hB'm.aemeasurable
  set I₁ : ℝ≥0∞ := ∫⁻ x, (∑ k ∈ S, ‖U k x‖ₑ ^ 2) ^ (r / 2) with hI₁
  have hA' : ∫⁻ x, A x ^ r = I₁ := by
    refine lintegral_congr fun x => ?_
    simp only [hA]
    rw [← ENNReal.rpow_mul]; congr 1; ring
  have hB'' : ∫⁻ x, B' x ^ r' ≤ CE * N := by
    have h1 : ∫⁻ x, B' x ^ r' =
        ∫⁻ x, sqS (fun j => cv (symK (rhoT : 𝔼 → ℂ) j) om) x ^ (r' / 2) := by
      refine lintegral_congr fun x => ?_
      simp only [hB']
      rw [← ENNReal.rpow_mul]; congr 1; ring
    rw [h1]
    refine (hCE om (omg_meas r V) homi (ENNReal.ofReal (CV ^ (r - 1))) ENNReal.ofReal_ne_top
      home).trans ?_
    refine mul_le_mul_right (le_of_eq ?_) _
    refine lintegral_congr fun x => ?_
    have e : ‖om x‖ₑ = ‖V x‖ₑ ^ (r - 1) := by
      rw [← ofReal_norm, hom, norm_omg hr, ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _)
        (by linarith), ofReal_norm]
    rw [e, ← ENNReal.rpow_mul]; congr 1; nlinarith [hrr']
  have hmain : N ≤ I₁ ^ (1 / r) * ((CE : ℝ≥0∞) * N) ^ (1 / r') := by
    refine step1.trans (step2.trans ?_)
    rw [hA']
    exact mul_le_mul_right (ENNReal.rpow_le_rpow hB'' (by positivity)) _
  -- solve for `N`
  have hN0' : 0 < N := pos_iff_ne_zero.2 hN0
  have hab : 1 / r + 1 / r' = 1 := by
    have := hconj.inv_add_inv_eq_one
    simpa [one_div] using this
  have ha0 : 0 < 1 / r' := by positivity
  have hb0 : 0 < 1 / r := by positivity
  have hNa0 : N ^ (1 / r') ≠ 0 := (ENNReal.rpow_pos hN0' hNtop).ne'
  have hNatop : N ^ (1 / r') ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg ha0.le hNtop
  have h1 : N ^ (1 / r) * N ^ (1 / r') ≤ (I₁ ^ (1 / r) * (CE : ℝ≥0∞) ^ (1 / r')) * N ^ (1 / r') := by
    calc N ^ (1 / r) * N ^ (1 / r') = N := by
          rw [← ENNReal.rpow_add _ _ hN0 hNtop, hab, ENNReal.rpow_one]
      _ ≤ I₁ ^ (1 / r) * ((CE : ℝ≥0∞) * N) ^ (1 / r') := hmain
      _ = (I₁ ^ (1 / r) * (CE : ℝ≥0∞) ^ (1 / r')) * N ^ (1 / r') := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ ha0.le]; ring
  have h2 : N ^ (1 / r) ≤ I₁ ^ (1 / r) * (CE : ℝ≥0∞) ^ (1 / r') :=
    (ENNReal.mul_le_mul_iff_left hNa0 hNatop).1 h1
  have hbr : 1 / r * r = 1 := by field_simp
  have har : 1 / r' * r = r - 1 := by
    have hr'0 : r' ≠ 0 := by linarith
    field_simp
    nlinarith [hrr']
  have h3 : N ≤ I₁ * (CE : ℝ≥0∞) ^ (r - 1) := by
    calc N = (N ^ (1 / r)) ^ r := by rw [← ENNReal.rpow_mul, hbr, ENNReal.rpow_one]
      _ ≤ (I₁ ^ (1 / r) * (CE : ℝ≥0∞) ^ (1 / r')) ^ r := ENNReal.rpow_le_rpow h2 hr0.le
      _ = I₁ * (CE : ℝ≥0∞) ^ (r - 1) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hr0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, hbr,
            har, ENNReal.rpow_one]
  rw [ENNReal.coe_rpow_of_nonneg _ (by linarith : (0 : ℝ) ≤ r - 1), mul_comm]
  exact h3

end HRS.Commutator.Whole.XLI
