import HRS.MS.S21K2_W09B
import HRS.Commutator.Whole.LocalAuxKR

/-!
# S21K2 W09C -- weighted jet bounds on a ball and the `H^1` bound of a jet coordinate (R26-T3.W09)

For `f` smooth with `tsupport f ⊆ B_L` and `weightedSobolevE r P f <= 1`, every ordered partial derivative of order `j <= r` has
`∫ (∂f)² <= (min 1 (1+L²)^{-P})⁻¹`; and for `u` smooth with compact support, `∫(1+4π²|ξ|²)|F u|² = ∫u² + ∑_k ∫ (∂_k u)²`.
Helper prefix `s21k2_w09_`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators FourierTransform
noncomputable section
namespace HRS.MS.R26T3
open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux
variable {d : ℕ}

theorem s21k2_w09_jb_rpow (x : HRS.Euc d) (c : ℝ) :
    HRS.Whole.jbracket x ^ c = (1 + ‖x‖ ^ 2) ^ (c / 2) := by
  unfold HRS.Whole.jbracket
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
  congr 1; ring

theorem s21k2_w09_weight_bounds (q L : ℝ) {x : HRS.Euc d} (hx : ‖x‖ ≤ L) :
    min 1 ((1 + L ^ 2) ^ (-q)) ≤ HRS.Whole.jbracket x ^ (-2 * q) ∧
    HRS.Whole.jbracket x ^ (-2 * q) ≤ max 1 ((1 + L ^ 2) ^ (-q)) := by
  rw [s21k2_w09_jb_rpow, show -2 * q / 2 = -q by ring]
  have h1 : (1 : ℝ) ≤ 1 + ‖x‖ ^ 2 := by nlinarith [sq_nonneg ‖x‖]
  have h2 : 1 + ‖x‖ ^ 2 ≤ 1 + L ^ 2 := by
    have : ‖x‖ ^ 2 ≤ L ^ 2 := by
      have := norm_nonneg x
      nlinarith
    linarith
  rcases le_total 0 (-q) with hq | hq
  · have a1 : (1 : ℝ) ^ (-q) ≤ (1 + ‖x‖ ^ 2) ^ (-q) := Real.rpow_le_rpow zero_le_one h1 hq
    have a2 : (1 + ‖x‖ ^ 2) ^ (-q) ≤ (1 + L ^ 2) ^ (-q) := Real.rpow_le_rpow (by positivity) h2 hq
    rw [Real.one_rpow] at a1
    exact ⟨(min_le_left _ _).trans a1, a2.trans (le_max_right _ _)⟩
  · have a1 : (1 + ‖x‖ ^ 2) ^ (-q) ≤ (1 : ℝ) ^ (-q) := Real.rpow_le_rpow_of_nonpos zero_lt_one h1 hq
    have a2 : (1 + L ^ 2) ^ (-q) ≤ (1 + ‖x‖ ^ 2) ^ (-q) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) h2 hq
    rw [Real.one_rpow] at a1
    exact ⟨(min_le_right _ _).trans a2, a1.trans (le_max_left _ _)⟩


theorem s21k2_w09_supp {r : ℕ} {f : HRS.Euc d → ℝ} (hf : ContDiff ℝ r f) {j : ℕ} (hj : j ≤ r)
    (idx : Fin j → Fin d) {L : ℝ} (hsupp : tsupport f ⊆ Metric.closedBall 0 L) :
    tsupport (HRS.Whole.partialDeriv idx f) ⊆ Metric.closedBall 0 L := by
  refine (closure_minimal ?_ (Metric.isClosed_closedBall)).trans le_rfl
  intro x hx
  have hne : iteratedFDeriv ℝ j f x ≠ 0 := by
    intro h0
    apply hx
    unfold HRS.Whole.partialDeriv
    rw [h0]; rfl
  exact hsupp (support_iteratedFDeriv_subset j (Function.mem_support.2 hne))

theorem s21k2_w09_l2_bound {r : ℕ} {P L : ℝ} {f : HRS.Euc d → ℝ} (hf : ContDiff ℝ r f)
    (hsupp : tsupport f ⊆ Metric.closedBall 0 L) (hE : HRS.Whole.weightedSobolevE r P f ≤ 1)
    {j : ℕ} (hj : j ≤ r) (idx : Fin j → Fin d) :
    ∫ x, (HRS.Whole.partialDeriv idx f x) ^ 2 ≤ (min 1 ((1 + L ^ 2) ^ (-P)))⁻¹ := by
  set m : ℝ := min 1 ((1 + L ^ 2) ^ (-P)) with hm
  have hm0 : 0 < m := lt_min one_pos (Real.rpow_pos_of_pos (by positivity) _)
  have hcont : Continuous (HRS.Whole.partialDeriv idx f) := s21g2_w01_pd_cont hf hj idx
  have hcs : HasCompactSupport (HRS.Whole.partialDeriv idx f) :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : HRS.Euc d) L)
      ((subset_tsupport _).trans (s21k2_w09_supp hf hj idx hsupp))
  have hint : Integrable (fun x : HRS.Euc d => (HRS.Whole.partialDeriv idx f x) ^ 2) :=
    (hcont.memLp_of_hasCompactSupport (p := 2) (μ := volume) hcs).integrable_sq
  -- lintegral bound
  have hS : ∑ j' ∈ Finset.range (r + 1), ∑ i : Fin j' → Fin d,
      ∫⁻ x, ENNReal.ofReal (HRS.Whole.jbracket x ^ (-2 * P) * (HRS.Whole.partialDeriv i f x) ^ 2) ≤ 1 := by
    by_contra hlt
    rw [not_le] at hlt
    have := ENNReal.one_lt_rpow hlt (by norm_num : (0 : ℝ) < 1 / 2)
    unfold HRS.Whole.weightedSobolevE at hE
    exact absurd hE (not_le.2 this)
  have hterm : ∫⁻ x, ENNReal.ofReal (HRS.Whole.jbracket x ^ (-2 * P) * (HRS.Whole.partialDeriv idx f x) ^ 2) ≤ 1 :=
    le_trans (le_trans (Finset.single_le_sum (f := fun i : Fin j → Fin d => ∫⁻ x, ENNReal.ofReal
      (HRS.Whole.jbracket x ^ (-2 * P) * (HRS.Whole.partialDeriv i f x) ^ 2)) (fun _ _ => zero_le)
      (Finset.mem_univ idx)) (Finset.single_le_sum (f := fun j' => ∑ i : Fin j' → Fin d, ∫⁻ x, ENNReal.ofReal
      (HRS.Whole.jbracket x ^ (-2 * P) * (HRS.Whole.partialDeriv i f x) ^ 2)) (fun _ _ => zero_le)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hj)))) hS
  have hpt : ∀ x : HRS.Euc d, m * (HRS.Whole.partialDeriv idx f x) ^ 2 ≤
      HRS.Whole.jbracket x ^ (-2 * P) * (HRS.Whole.partialDeriv idx f x) ^ 2 := fun x => by
    by_cases hx : HRS.Whole.partialDeriv idx f x = 0
    · simp [hx]
    · have hxB : ‖x‖ ≤ L := by
        have := s21k2_w09_supp hf hj idx hsupp (subset_tsupport _ (Function.mem_support.2 hx))
        simpa using this
      exact mul_le_mul_of_nonneg_right (s21k2_w09_weight_bounds P L hxB).1 (sq_nonneg _)
  have h1 : ENNReal.ofReal (m * ∫ x, (HRS.Whole.partialDeriv idx f x) ^ 2) ≤ 1 := by
    rw [← integral_const_mul, ofReal_integral_eq_lintegral_ofReal (hint.const_mul m)
      (Eventually.of_forall fun x => by positivity)]
    exact (lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hpt x)).trans hterm
  have h2 : m * ∫ x, (HRS.Whole.partialDeriv idx f x) ^ 2 ≤ 1 := by
    have := (ENNReal.ofReal_le_one).1 h1
    exact this
  calc ∫ x, (HRS.Whole.partialDeriv idx f x) ^ 2
      = m⁻¹ * (m * ∫ x, (HRS.Whole.partialDeriv idx f x) ^ 2) := by field_simp
    _ ≤ m⁻¹ * 1 := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = m⁻¹ := mul_one _


theorem s21k2_w09_F_fderiv {u : HRS.Euc d → ℝ} (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u)
    (hc : HasCompactSupport u) (k : Fin d) (ξ : HRS.Euc d) :
    s21k2_w09_F (fun x => fderiv ℝ u x (EuclideanSpace.single k (1 : ℝ))) ξ =
      (2 * Real.pi * Complex.I * (ξ k : ℂ)) * s21k2_w09_F u ξ := by
  have hcs : HasCompactSupport (fun x : HRS.Euc d => ((u x : ℝ) : ℂ)) :=
    hc.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
  have hcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : HRS.Euc d => ((u x : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hu
  set Φ : SchwartzMap (HRS.Euc d) ℂ := hcs.toSchwartzMap hcd with hΦ
  have h := HRS.Commutator.Whole.cmxMY_fourier_partial Φ k ξ
  have hcoe : (⇑Φ : HRS.Euc d → ℂ) = fun x => ((u x : ℝ) : ℂ) := rfl
  have hder : ∀ x : HRS.Euc d, fderiv ℝ Φ x (EuclideanSpace.single k (1 : ℝ)) =
      ((fderiv ℝ u x (EuclideanSpace.single k (1 : ℝ)) : ℝ) : ℂ) := fun x => by
    have hd : HasFDerivAt (fun y : HRS.Euc d => ((u y : ℝ) : ℂ))
        (Complex.ofRealCLM.comp (fderiv ℝ u x)) x :=
      Complex.ofRealCLM.hasFDerivAt.comp x ((hu.differentiable (by simp)) x).hasFDerivAt
    rw [hcoe, hd.fderiv]
    rfl
  have hfun : (fun x : HRS.Euc d => ((fderiv ℝ u x (EuclideanSpace.single k (1 : ℝ)) : ℝ) : ℂ)) =
      fun x => fderiv ℝ Φ x (EuclideanSpace.single k (1 : ℝ)) := funext fun x => (hder x).symm
  simp only [s21k2_w09_F]
  rw [hfun, ← hcoe]
  exact h

theorem s21k2_w09_F_int_sq {w : HRS.Euc d → ℝ} (hw : Continuous w) (hcw : HasCompactSupport w) :
    Integrable (fun ξ : HRS.Euc d => ‖s21k2_w09_F w ξ‖ ^ 2) := by
  have := (memLp_fourierL2 (hw.memLp_of_hasCompactSupport hcw : MemLp w 2 volume)).norm.integrable_sq
  exact this.congr ((s21k2_w09_ae hw hcw).mono fun ξ h => by
    show ‖fourierL2 w ξ‖ ^ 2 = ‖s21k2_w09_F w ξ‖ ^ 2; rw [h])

theorem s21k2_w09_sobolev {u : HRS.Euc d → ℝ} (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u)
    (hc : HasCompactSupport u) :
    HRS.PDE.ToolboxRd.MemSobolev (1 : ℝ) u ∧
    ∫ ξ, (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (1 : ℝ) * ‖fourierL2 u ξ‖ ^ 2 =
      (∫ x, u x ^ 2) + ∑ k : Fin d, ∫ x, (fderiv ℝ u x (EuclideanSpace.single k (1 : ℝ))) ^ 2 := by
  have hcu : Continuous u := hu.continuous
  have hv : ∀ k : Fin d, Continuous (fun x => fderiv ℝ u x (EuclideanSpace.single k (1 : ℝ))) := fun k =>
    ((hu.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hvc : ∀ k : Fin d, HasCompactSupport (fun x => fderiv ℝ u x (EuclideanSpace.single k (1 : ℝ))) :=
    fun k => hc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k (1 : ℝ))
  set G : HRS.Euc d → ℝ := fun ξ => ‖s21k2_w09_F u ξ‖ ^ 2 +
    ∑ k : Fin d, ‖s21k2_w09_F (fun x => fderiv ℝ u x (EuclideanSpace.single k (1 : ℝ))) ξ‖ ^ 2 with hG
  have hGint : Integrable G :=
    (s21k2_w09_F_int_sq hcu hc).add (integrable_finset_sum _ fun k _ => s21k2_w09_F_int_sq (hv k) (hvc k))
  have hpt : ∀ ξ : HRS.Euc d, (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (1 : ℝ) * ‖s21k2_w09_F u ξ‖ ^ 2 = G ξ := by
    intro ξ
    have e : ∀ k : Fin d, ‖(2 * Real.pi * Complex.I * (ξ k : ℂ))‖ ^ 2 = 4 * Real.pi ^ 2 * (ξ k) ^ 2 := fun k => by
      have hre : (2 * Real.pi * Complex.I * (ξ k : ℂ)) = ((2 * Real.pi * ξ k : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [hre, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      ring
    have e2 : ∀ k : Fin d, ‖(2 * Real.pi * Complex.I * (ξ k : ℂ)) * s21k2_w09_F u ξ‖ ^ 2 =
        (4 * Real.pi ^ 2 * (ξ k) ^ 2) * ‖s21k2_w09_F u ξ‖ ^ 2 := fun k => by
      rw [norm_mul, mul_pow, e k]
    have hn : ‖ξ‖ ^ 2 = ∑ k : Fin d, (ξ k) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp only [Real.norm_eq_abs, sq_abs]
    simp only [Real.rpow_one, hG, s21k2_w09_F_fderiv hu hc _ ξ, e2]
    rw [hn, add_mul, one_mul, Finset.mul_sum, Finset.sum_mul]
  have hae : (fun ξ => (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (1 : ℝ) * ‖fourierL2 u ξ‖ ^ 2) =ᵐ[volume] G :=
    (s21k2_w09_ae hcu hc).mono fun ξ h => by
      show (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (1 : ℝ) * ‖fourierL2 u ξ‖ ^ 2 = G ξ
      rw [h]; exact hpt ξ
  refine ⟨⟨hcu.memLp_of_hasCompactSupport hc, hGint.congr hae.symm⟩, ?_⟩
  have hs : ∑ i : Fin d, ∫ a, ‖s21k2_w09_F (fun x => fderiv ℝ u x (EuclideanSpace.single i (1 : ℝ))) a‖ ^ 2 =
      ∑ k : Fin d, ∫ x, (fderiv ℝ u x (EuclideanSpace.single k (1 : ℝ))) ^ 2 :=
    Finset.sum_congr rfl fun k _ => s21k2_w09_parseval (hv k) (hvc k)
  rw [integral_congr_ae hae, hG, integral_add (s21k2_w09_F_int_sq hcu hc)
    (integrable_finsetSum _ fun k _ => s21k2_w09_F_int_sq (hv k) (hvc k)),
    integral_finsetSum _ fun k _ => s21k2_w09_F_int_sq (hv k) (hvc k), hs, s21k2_w09_parseval hcu hc]

end HRS.MS.R26T3
