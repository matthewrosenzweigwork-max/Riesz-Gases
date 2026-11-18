import HRS.MS.UniqQAux1
import HRS.MS.UlOuSAux2
import HRS.MS.UlMildAux1

/-!
# UNIQ-Q, part 2: Gaussian smoothing of the OU semigroup with sup-norm data

(plan: `UniqQAux1`).  Class `UqCB1 g B M`: `g ∈ C¹`, `|g| ≤ B`, `‖Dg‖ ≤ M`.

* `uniqq_cb1_ouSg`: `P_τ` maps `UqCB1 g B M` into `UqCB1 (P_τ g) B (K M)`, `K ≥ ‖e^{-τQ}‖`.
* `uniqq_lip`: `|P_τ g (x) - P_τ g (x')| ≤ C_l τ^{-1/2} B |x - x'|` for `g ∈ UqCB1 g B M`, `0 < τ ≤ T₀`:
  the constant does not depend on `M` (Stein identity `ul3_avg_deriv`, preimage `ul3_S_preimage`).
* translation, linearity.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff RealInnerProductSpace Matrix MatrixOrder

namespace HRS.MS.UniqQ

open HRS HRS.Whole HRS.MS.Ul

variable {d : ℕ}

/-- `C¹` with sup bound `B` and gradient bound `M` -/
def UqCB1 (g : Euc d → ℝ) (B M : ℝ) : Prop :=
  ContDiff ℝ 1 g ∧ (∀ y, |g y| ≤ B) ∧ (∀ y, ‖fderiv ℝ g y‖ ≤ M)

theorem UqCB1.B_nonneg {g : Euc d → ℝ} {B M : ℝ} (h : UqCB1 g B M) : 0 ≤ B :=
  (abs_nonneg _).trans (h.2.1 0)

theorem UqCB1.M_nonneg {g : Euc d → ℝ} {B M : ℝ} (h : UqCB1 g B M) : 0 ≤ M :=
  (norm_nonneg _).trans (h.2.2 0)

theorem UqCB1.mono {g : Euc d → ℝ} {B M B' M' : ℝ} (h : UqCB1 g B M) (hB : B ≤ B') (hM : M ≤ M') :
    UqCB1 g B' M' :=
  ⟨h.1, fun y => (h.2.1 y).trans hB, fun y => (h.2.2 y).trans hM⟩

theorem UqCB1.lip {g : Euc d → ℝ} {B M : ℝ} (h : UqCB1 g B M) (a b : Euc d) :
    |g a - g b| ≤ M * ‖a - b‖ :=
  ul4_lip_of_cb h.1 h.2.2 a b

theorem uniqq_cb1_trans {g : Euc d → ℝ} {B M : ℝ} (h : UqCB1 g B M) (e : Euc d) :
    UqCB1 (fun y => g (y + e)) B M := by
  refine ⟨h.1.comp (contDiff_id.add contDiff_const), fun y => h.2.1 _, fun y => ?_⟩
  rw [fderiv_comp_add_right]
  exact h.2.2 _

theorem uniqq_cb1_sub {g g' : Euc d → ℝ} {B M B' M' : ℝ} (h : UqCB1 g B M) (h' : UqCB1 g' B' M') :
    UqCB1 (fun y => g y - g' y) (B + B') (M + M') := by
  refine ⟨h.1.sub h'.1, fun y => ?_, fun y => ?_⟩
  · exact (abs_sub _ _).trans (add_le_add (h.2.1 y) (h'.2.1 y))
  · have e : fderiv ℝ (fun y => g y - g' y) y = fderiv ℝ g y - fderiv ℝ g' y :=
      fderiv_sub (h.1.differentiable one_ne_zero y) (h'.1.differentiable one_ne_zero y)
    rw [e]
    exact (norm_sub_le _ _).trans (add_le_add (h.2.2 y) (h'.2.2 y))

/-- the square root of the OU covariance as a continuous linear map -/
def uniqqS (Q : Matrix (Fin d) (Fin d) ℝ) (ν τ : ℝ) : Euc d →L[ℝ] Euc d :=
  Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (ouCov Q ν τ))

/-- the Gaussian representation of `ouSg` -/
theorem uniqq_ouSg_eq {g : Euc d → ℝ} (hg : Continuous g) (Q : Matrix (Fin d) (Fin d) ℝ) (ν τ : ℝ)
    (x : Euc d) :
    ouSg Q ν τ g x = ∫ w, g (ouExp Q τ x + uniqqS Q ν τ w) ∂(stdGaussian (Euc d)) := by
  have hm : AEMeasurable (fun w : Euc d => uniqqS Q ν τ w) (stdGaussian (Euc d)) :=
    (uniqqS Q ν τ).continuous.measurable.aemeasurable
  have h := integral_map (μ := stdGaussian (Euc d)) (φ := fun w : Euc d => uniqqS Q ν τ w)
    (f := fun y => g (ouExp Q τ x + y)) hm
    (hg.comp (continuous_const.add continuous_id)).aestronglyMeasurable
  unfold ouSg
  rw [ouLaw_eq_map]
  exact h

theorem uniqq_ouSg_eq_F {g : Euc d → ℝ} (hg : Continuous g) (Q : Matrix (Fin d) (Fin d) ℝ) (ν τ : ℝ) :
    ouSg Q ν τ g = fun x => (fun y => ∫ w, g (y + uniqqS Q ν τ w) ∂(stdGaussian (Euc d)))
      (ouExp Q τ x) :=
  funext fun x => uniqq_ouSg_eq hg Q ν τ x

/-- `P_τ` preserves the class `UqCB1` -/
theorem uniqq_cb1_ouSg (Q : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) {τ K : ℝ}
    (hK : ‖ouExp Q τ‖ ≤ K) {g : Euc d → ℝ} {B M : ℝ} (hg : UqCB1 g B M) :
    UqCB1 (ouSg Q ν τ g) B (M * K) := by
  have hgc : Continuous g := hg.1.continuous
  obtain ⟨hF1, -⟩ := ul3_avg_deriv hg.1 hg.2.1 hg.2.2 (uniqqS Q ν τ)
  have hcd : ContDiff ℝ 1 (ouSg Q ν τ g) := by
    rw [uniqq_ouSg_eq_F hgc Q ν τ]
    exact hF1.comp (ouExp Q τ).contDiff
  have hbd : ∀ x, |ouSg Q ν τ g x| ≤ B := ul4_ouSg_abs_le Q ν τ hg.2.1
  have hlip : ∀ x x' : Euc d, |ouSg Q ν τ g x - ouSg Q ν τ g x'| ≤ M * K * ‖x - x'‖ := by
    intro x x'
    have hi : ∀ z : Euc d, Integrable (fun y => g (ouExp Q τ z + y)) (ouLaw Q ν τ) := fun z =>
      Integrable.of_bound (hgc.comp (continuous_const.add continuous_id)).aestronglyMeasurable B
        (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hg.2.1 _)
    have e : ouSg Q ν τ g x - ouSg Q ν τ g x' =
        ∫ y, (g (ouExp Q τ x + y) - g (ouExp Q τ x' + y)) ∂(ouLaw Q ν τ) := by
      unfold ouSg
      rw [integral_sub (hi x) (hi x')]
    rw [e, ← Real.norm_eq_abs]
    have hb := norm_integral_le_of_norm_le_const (μ := ouLaw Q ν τ)
      (f := fun y => g (ouExp Q τ x + y) - g (ouExp Q τ x' + y)) (C := M * ‖ouExp Q τ (x - x')‖)
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]
        refine (hg.lip _ _).trans (le_of_eq ?_)
        congr 2
        rw [map_sub]; abel)
    simp only [probReal_univ, mul_one] at hb
    refine hb.trans ?_
    calc M * ‖ouExp Q τ (x - x')‖ ≤ M * (K * ‖x - x'‖) :=
          mul_le_mul_of_nonneg_left (((ouExp Q τ).le_opNorm _).trans
            (mul_le_mul_of_nonneg_right hK (norm_nonneg _))) hg.M_nonneg
      _ = _ := by ring
  have hK0 : 0 ≤ M * K := mul_nonneg hg.M_nonneg ((norm_nonneg _).trans hK)
  refine ⟨hcd, hbd, fun x => ?_⟩
  have hL : LipschitzWith ⟨M * K, hK0⟩ (ouSg Q ν τ g) := by
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    rw [Real.dist_eq, dist_eq_norm]
    exact hlip a b
  exact norm_fderiv_le_of_lipschitz ℝ hL

/-- the Gaussian `L¹` constant `E‖W‖` -/
def uniqqCm (d : ℕ) : ℝ := ∫ w : Euc d, ‖w‖ ∂(stdGaussian (Euc d))

theorem uniqqCm_nonneg : 0 ≤ uniqqCm d := integral_nonneg fun _ => norm_nonneg _

theorem uniqq_wavg_bound {g : Euc d → ℝ} {B M : ℝ} (hg : UqCB1 g B M) (S : Euc d →L[ℝ] Euc d)
    (c z : Euc d) : |ul3_wavg S c g z| ≤ B * ‖c‖ * uniqqCm d := by
  have hint : Integrable (fun w : Euc d => B * (‖c‖ * ‖w‖)) (stdGaussian (Euc d)) :=
    ((IsGaussian.integrable_id (μ := stdGaussian (Euc d))).norm.const_mul ‖c‖).const_mul B
  have h := norm_integral_le_of_norm_le hint (μ := stdGaussian (Euc d))
    (f := fun w : Euc d => g (z + S w) * ⟪c, w⟫) (Filter.Eventually.of_forall fun w => by
      rw [norm_mul, Real.norm_eq_abs]
      refine mul_le_mul (hg.2.1 _) ?_ (norm_nonneg _) hg.B_nonneg
      exact (abs_real_inner_le_norm c w))
  have e : ∫ w : Euc d, B * (‖c‖ * ‖w‖) ∂(stdGaussian (Euc d)) = B * ‖c‖ * uniqqCm d := by
    rw [integral_const_mul, integral_const_mul, uniqqCm]; ring
  rw [e] at h
  simpa [ul3_wavg, Real.norm_eq_abs] using h

theorem uniqq_fderiv_F_bound {g : Euc d → ℝ} {B M : ℝ} (hg : UqCB1 g B M) (S : Euc d →L[ℝ] Euc d)
    {κ : ℝ} (hκ : 0 ≤ κ) (hpre : ∀ j : Fin d, ∃ c : Euc d, S c = EuclideanSpace.single j 1 ∧ ‖c‖ ≤ κ)
    (z : Euc d) :
    ‖fderiv ℝ (fun x => ∫ w, g (x + S w) ∂(stdGaussian (Euc d))) z‖ ≤
      d * (B * κ * uniqqCm d) := by
  obtain ⟨-, hder⟩ := ul3_avg_deriv hg.1 hg.2.1 hg.2.2 S
  choose c hcS hcn using hpre
  have hCm := uniqqCm_nonneg (d := d)
  have hB := hg.B_nonneg
  have hj : ∀ j : Fin d, |fderiv ℝ (fun x => ∫ w, g (x + S w) ∂(stdGaussian (Euc d))) z
      (EuclideanSpace.single j 1)| ≤ B * κ * uniqqCm d := by
    intro j
    rw [hder (c j) j (hcS j) z]
    refine (uniqq_wavg_bound hg S (c j) z).trans ?_
    gcongr
    exact hcn j
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  have hv : v = ∑ i : Fin d, v i • (EuclideanSpace.single i (1 : ℝ) : Euc d) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  set L := fderiv ℝ (fun x => ∫ w, g (x + S w) ∂(stdGaussian (Euc d))) z with hL
  rw [Real.norm_eq_abs]
  conv_lhs => rw [hv]
  simp only [map_sum, map_smul, smul_eq_mul]
  calc |∑ i : Fin d, v i * L (EuclideanSpace.single i 1)|
      ≤ ∑ i : Fin d, |v i * L (EuclideanSpace.single i 1)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, ‖v‖ * (B * κ * uniqqCm d) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul]
        exact mul_le_mul (by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le v i) (hj i)
          (abs_nonneg _) (norm_nonneg _)
    _ = d * (B * κ * uniqqCm d) * ‖v‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- **Lipschitz smoothing with sup-norm data**: the constant does not depend on the gradient bound `M`. -/
theorem uniqq_lip (Q : Matrix (Fin d) (Fin d) ℝ) {ν : ℝ} (hν : 0 < ν) (T0 : ℝ) :
    ∃ Cl : ℝ, 0 ≤ Cl ∧ ∀ τ : ℝ, 0 < τ → τ ≤ T0 → ∀ (g : Euc d → ℝ) (B M : ℝ), UqCB1 g B M →
      ∀ x x' : Euc d, |ouSg Q ν τ g x - ouSg Q ν τ g x'| ≤ Cl * τ ^ (-(1 / 2 : ℝ)) * B * ‖x - x'‖ := by
  obtain ⟨K, hK1, hK⟩ := ul2_exp_bound Q T0
  obtain ⟨lam, Lam, hlam, -, hb⟩ := ouCov_bounds Q hν T0
  have hCm := uniqqCm_nonneg (d := d)
  refine ⟨d * uniqqCm d * K / Real.sqrt lam, by positivity, fun τ hτ hτT g B M hg x x' => ?_⟩
  have hτI : τ ∈ Icc (0 : ℝ) T0 := ⟨hτ.le, hτT⟩
  have hpos : (ouCov Q ν τ).PosSemidef := ouCov_posSemidef Q hν.le hτ.le
  have hμ : 0 < lam * τ := by positivity
  have hpre : ∀ j : Fin d, ∃ c : Euc d, uniqqS Q ν τ c = EuclideanSpace.single j 1 ∧
      ‖c‖ ≤ 1 / Real.sqrt (lam * τ) := by
    intro j
    obtain ⟨c, hc1, hc2⟩ := ul3_S_preimage hpos hμ (fun ξ => (hb τ hτI ξ).1) (EuclideanSpace.single j (1 : ℝ))
    exact ⟨c, hc1, by simpa using hc2⟩
  set κ : ℝ := 1 / Real.sqrt (lam * τ) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  have hgc : Continuous g := hg.1.continuous
  obtain ⟨hF1, -⟩ := ul3_avg_deriv hg.1 hg.2.1 hg.2.2 (uniqqS Q ν τ)
  set F : Euc d → ℝ := fun y => ∫ w, g (y + uniqqS Q ν τ w) ∂(stdGaussian (Euc d)) with hF
  have hFl : ∀ y y' : Euc d, |F y - F y'| ≤ d * (B * κ * uniqqCm d) * ‖y - y'‖ := by
    intro y y'
    have := (convex_univ (𝕜 := ℝ) (E := Euc d)).norm_image_sub_le_of_norm_fderiv_le
      (f := F) (C := d * (B * κ * uniqqCm d)) (x := y') (y := y)
      (fun z _ => (hF1.differentiable one_ne_zero) z)
      (fun z _ => uniqq_fderiv_F_bound hg (uniqqS Q ν τ) hκ0 hpre z) (mem_univ _) (mem_univ _)
    simpa [Real.norm_eq_abs] using this
  rw [uniqq_ouSg_eq hgc, uniqq_ouSg_eq hgc]
  refine (hFl _ _).trans ?_
  have hA : ‖ouExp Q τ x - ouExp Q τ x'‖ ≤ K * ‖x - x'‖ := by
    rw [← map_sub]
    exact ((ouExp Q τ).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hK τ (by rw [abs_of_pos hτ]; exact hτT)) (norm_nonneg _))
  have hκe : κ = Real.sqrt lam⁻¹ * τ ^ (-(1 / 2 : ℝ)) := by
    rw [hκ, Real.sqrt_mul hlam.le, Real.sqrt_eq_rpow τ, Real.rpow_neg hτ.le, Real.sqrt_inv]
    field_simp
  have hB := hg.B_nonneg
  calc d * (B * κ * uniqqCm d) * ‖ouExp Q τ x - ouExp Q τ x'‖
      ≤ d * (B * κ * uniqqCm d) * (K * ‖x - x'‖) := by gcongr
    _ = _ := by
        rw [hκe]
        have : Real.sqrt lam⁻¹ = 1 / Real.sqrt lam := by
          rw [Real.sqrt_inv]; simp
        rw [this]
        field_simp

end HRS.MS.UniqQ
