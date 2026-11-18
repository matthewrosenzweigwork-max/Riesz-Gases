import HRS.MC.S7W4Aux1

/-!
# Packet `s7_W4_gaussian_quadratic_clt`: CLT for `sum a_j (g_j^2 - 1)`

Route: the characteristic function of the normalised sum is `prod_j phi(t a_j / s)` with
`phi(u) = E exp(i u (g^2 - 1))`; `|phi(u) - e^{-u^2}| <= C |u|^3` (`S7W4Aux1`), the telescoping bound for
products of numbers of modulus `<= 1` and `sum (t a_j / s)^2 = t^2/2` give the pointwise convergence of
the characteristic functions to `e^{-t^2/2}`; Levy's theorem (`Mathlib`) finishes.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.W4

lemma s7w4_phi_gauss {u : ℝ} (hu : |u| ≤ 1) :
    ‖s7w4_phi u - Complex.exp (((-u ^ 2 : ℝ) : ℂ))‖ ≤ (4 * s7w4_K + 1) * |u| ^ 3 := by
  have h1 := s7w4_phi_approx u
  have h2 : ‖Complex.exp (((-u ^ 2 : ℝ) : ℂ)) - ((1 - u ^ 2 : ℝ) : ℂ)‖ ≤ |u| ^ 3 := by
    have hx : |(-u ^ 2 : ℝ)| ≤ 1 := by
      rw [abs_neg, abs_pow]; nlinarith [abs_nonneg u]
    have := Real.abs_exp_sub_one_sub_id_le hx
    have e : Complex.exp (((-u ^ 2 : ℝ) : ℂ)) - ((1 - u ^ 2 : ℝ) : ℂ) =
        ((Real.exp (-u ^ 2) - 1 - (-u ^ 2) : ℝ) : ℂ) := by
      push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs]
    refine this.trans ?_
    have : (-u ^ 2) ^ 2 = |u| ^ 4 := by rw [neg_sq, ← sq_abs u]; ring
    rw [this]
    have h0 : 0 ≤ |u| ^ 3 := by positivity
    nlinarith [pow_le_pow_of_le_one (abs_nonneg u) hu (by norm_num : 3 ≤ 4)]
  calc _ = ‖(s7w4_phi u - ((1 - u ^ 2 : ℝ) : ℂ)) +
          (((1 - u ^ 2 : ℝ) : ℂ) - Complex.exp (((-u ^ 2 : ℝ) : ℂ)))‖ := by congr 1; ring
    _ ≤ ‖s7w4_phi u - ((1 - u ^ 2 : ℝ) : ℂ)‖ +
          ‖((1 - u ^ 2 : ℝ) : ℂ) - Complex.exp (((-u ^ 2 : ℝ) : ℂ))‖ := norm_add_le _ _
    _ ≤ 4 * s7w4_K * |u| ^ 3 + |u| ^ 3 := by
          rw [norm_sub_rev (((1 - u ^ 2 : ℝ) : ℂ))]; exact add_le_add h1 h2
    _ = _ := by ring

lemma s7w4_prod_sub {ι : Type*} (s : Finset ι) (z w : ι → ℂ) (hz : ∀ j, ‖z j‖ ≤ 1)
    (hw : ∀ j, ‖w j‖ ≤ 1) :
    ‖∏ j ∈ s, z j - ∏ j ∈ s, w j‖ ≤ ∑ j ∈ s, ‖z j - w j‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have hPw : ‖∏ j ∈ s, w j‖ ≤ 1 := by
      rw [norm_prod]; exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun j _ => hw j)
    calc ‖z a * ∏ j ∈ s, z j - w a * ∏ j ∈ s, w j‖
        = ‖z a * (∏ j ∈ s, z j - ∏ j ∈ s, w j) + (z a - w a) * ∏ j ∈ s, w j‖ := by congr 1; ring
      _ ≤ ‖z a * (∏ j ∈ s, z j - ∏ j ∈ s, w j)‖ + ‖(z a - w a) * ∏ j ∈ s, w j‖ := norm_add_le _ _
      _ ≤ 1 * ‖∏ j ∈ s, z j - ∏ j ∈ s, w j‖ + ‖z a - w a‖ * 1 := by
          rw [norm_mul, norm_mul]
          gcongr
          exact hz a
      _ ≤ _ := by linarith

/-- characteristic function of the normalised quadratic form: a product of scalar ones -/
lemma s7w4_charFun {ι : Type} [Fintype ι] (a : ι → ℝ) {s : ℝ} (t : ℝ) :
    charFun ((Measure.pi fun _ : ι => s7w4_γ).map
        (fun x : ι → ℝ => (∑ j, a j * (x j ^ 2 - 1)) / s)) t
      = ∏ j, s7w4_phi (t * a j / s) := by
  have hm : Measurable (fun x : ι → ℝ => (∑ j, a j * (x j ^ 2 - 1)) / s) := by fun_prop
  rw [charFun_apply_real, integral_map hm.aemeasurable (by fun_prop)]
  have : ∀ x : ι → ℝ, Complex.exp (((t : ℂ) * (((∑ j, a j * (x j ^ 2 - 1)) / s : ℝ) : ℂ)) * Complex.I) =
      ∏ j, Complex.exp (((t * a j / s * (x j ^ 2 - 1) : ℝ) : ℂ) * Complex.I) := by
    intro x
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.sum_div, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  simp_rw [this]
  rw [integral_fintype_prod_eq_prod (f := fun j (y : ℝ) =>
    Complex.exp (((t * a j / s * (y ^ 2 - 1) : ℝ) : ℂ) * Complex.I))]
  rfl

/-- pointwise convergence of the characteristic functions -/
lemma s7w4_tendsto_charFun {ι : ℕ → Type} [∀ n, Fintype (ι n)] (a : ∀ n, ι n → ℝ)
    (hσ : ∀ n, 0 < ∑ j, a n j ^ 2)
    (hmax : Tendsto (fun n => (⨆ j, |a n j|) / Real.sqrt (∑ j, a n j ^ 2)) atTop (𝓝 0)) (t : ℝ) :
    Tendsto (fun n => charFun ((Measure.pi fun _ : ι n => s7w4_γ).map
        (fun x : ι n → ℝ => (∑ j, a n j * (x j ^ 2 - 1)) / Real.sqrt (2 * ∑ j, a n j ^ 2))) t)
      atTop (𝓝 (Complex.exp (((-(t ^ 2 / 2) : ℝ) : ℂ)))) := by
  set S : ℕ → ℝ := fun n => ∑ j, a n j ^ 2 with hS
  set sg : ℕ → ℝ := fun n => Real.sqrt (2 * S n) with hsg
  have hSpos : ∀ n, 0 < S n := hσ
  have hsg_pos : ∀ n, 0 < sg n := fun n => Real.sqrt_pos.2 (by linarith [hSpos n])
  have hsg_sq : ∀ n, sg n ^ 2 = 2 * S n := fun n => Real.sq_sqrt (by linarith [hSpos n])
  set r : ℕ → ℝ := fun n => (⨆ j, |a n j|) / Real.sqrt (S n) with hr
  have hr' : Tendsto r atTop (𝓝 0) := hmax
  set δ : ℕ → ℝ := fun n => |t| * r n with hδ
  have hδ0 : Tendsto δ atTop (𝓝 0) := by simpa using hr'.const_mul |t|
  -- bounds on the individual arguments
  have hu : ∀ n j, |t * a n j / sg n| ≤ δ n := by
    intro n j
    have h1 : |a n j| ≤ ⨆ j, |a n j| := le_ciSup (f := fun j => |a n j|) (Set.finite_range _).bddAbove j
    have h2 : Real.sqrt (S n) ≤ sg n := Real.sqrt_le_sqrt (by linarith [hSpos n])
    have h3 : 0 < Real.sqrt (S n) := Real.sqrt_pos.2 (hSpos n)
    rw [abs_div, abs_mul, abs_of_pos (hsg_pos n)]
    simp only [hδ, hr]
    calc |t| * |a n j| / sg n ≤ |t| * |a n j| / Real.sqrt (S n) :=
          div_le_div_of_nonneg_left (by positivity) h3 h2
      _ ≤ |t| * (⨆ j, |a n j|) / Real.sqrt (S n) := by gcongr
      _ = _ := by ring
  have hsumu : ∀ n, ∑ j, (t * a n j / sg n) ^ 2 = t ^ 2 / 2 := by
    intro n
    have : ∑ j, (t * a n j / sg n) ^ 2 = t ^ 2 * S n / sg n ^ 2 := by
      simp only [hS, div_pow, mul_pow, ← Finset.sum_div, ← Finset.mul_sum]
    rw [this, hsg_sq]; have := hSpos n; field_simp
  have hprodexp : ∀ n, ∏ j, Complex.exp (((-(t * a n j / sg n) ^ 2 : ℝ) : ℂ)) =
      Complex.exp (((-(t ^ 2 / 2) : ℝ) : ℂ)) := by
    intro n
    rw [← Complex.exp_sum, ← Complex.ofReal_sum, Finset.sum_neg_distrib, hsumu]
  have hbound : ∀ᶠ n in atTop, ‖∏ j, s7w4_phi (t * a n j / sg n) - Complex.exp (((-(t ^ 2 / 2) : ℝ) : ℂ))‖
      ≤ (4 * s7w4_K + 1) * δ n * (t ^ 2 / 2) := by
    filter_upwards [hδ0.eventually (Iic_mem_nhds (zero_lt_one : (0:ℝ) < 1))] with n hn
    have hn1 : δ n ≤ 1 := hn
    rw [← hprodexp n]
    refine (s7w4_prod_sub Finset.univ _ _ (fun j => s7w4_phi_norm _)
      (fun j => ?_)).trans ?_
    · rw [Complex.norm_exp]; simp only [Complex.ofReal_re]
      rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg (t * a n j / sg n)]
    · calc ∑ j, ‖s7w4_phi (t * a n j / sg n) - Complex.exp (((-(t * a n j / sg n) ^ 2 : ℝ) : ℂ))‖
          ≤ ∑ j, (4 * s7w4_K + 1) * (δ n * (t * a n j / sg n) ^ 2) := by
            refine Finset.sum_le_sum fun j _ => ?_
            have hj : |t * a n j / sg n| ≤ 1 := (hu n j).trans hn1
            refine (s7w4_phi_gauss hj).trans ?_
            have : |t * a n j / sg n| ^ 3 ≤ δ n * (t * a n j / sg n) ^ 2 := by
              have h0 := abs_nonneg (t * a n j / sg n)
              calc |t * a n j / sg n| ^ 3 = |t * a n j / sg n| * (t * a n j / sg n) ^ 2 := by
                    rw [← sq_abs (t * a n j / sg n)]; ring
                _ ≤ δ n * (t * a n j / sg n) ^ 2 := by
                    gcongr; exact hu n j
            have hK := s7w4_K_nonneg
            nlinarith
        _ = (4 * s7w4_K + 1) * δ n * (t ^ 2 / 2) := by
            rw [← Finset.mul_sum, ← Finset.mul_sum, hsumu]; ring
  have hlim : Tendsto (fun n => (4 * s7w4_K + 1) * δ n * (t ^ 2 / 2)) atTop (𝓝 0) := by
    simpa using (hδ0.const_mul (4 * s7w4_K + 1)).mul_const (t ^ 2 / 2)
  have h0 : Tendsto (fun n => ∏ j, s7w4_phi (t * a n j / sg n) -
      Complex.exp (((-(t ^ 2 / 2) : ℝ) : ℂ))) atTop (𝓝 0) :=
    squeeze_zero_norm' hbound hlim
  have := (tendsto_sub_nhds_zero_iff.1 h0)
  refine this.congr fun n => ?_
  rw [s7w4_charFun]

theorem s7_W4_gaussian_quadratic_clt_proof {ι : ℕ → Type} [∀ n, Fintype (ι n)] (a : ∀ n, ι n → ℝ)
    (hσ : ∀ n, 0 < ∑ j, a n j ^ 2)
    (hmax : Tendsto (fun n => (⨆ j, |a n j|) / Real.sqrt (∑ j, a n j ^ 2)) atTop (𝓝 0)) :
    ∀ F : ℝ → ℝ, Continuous F → (∃ M, ∀ x, |F x| ≤ M) →
      Tendsto (fun n => ∫ x : ι n → ℝ,
          F ((∑ j, a n j * (x j ^ 2 - 1)) / Real.sqrt (2 * ∑ j, a n j ^ 2))
            ∂(Measure.pi fun _ : ι n => gaussianReal 0 1))
        atTop (𝓝 (∫ y, F y ∂(gaussianReal 0 1))) := by
  intro F hF ⟨M, hM⟩
  have hX : ∀ n, AEMeasurable (fun x : ι n → ℝ =>
      (∑ j, a n j * (x j ^ 2 - 1)) / Real.sqrt (2 * ∑ j, a n j ^ 2))
      (Measure.pi fun _ : ι n => gaussianReal 0 1) := fun n => by
    have : Measurable (fun x : ι n → ℝ =>
      (∑ j, a n j * (x j ^ 2 - 1)) / Real.sqrt (2 * ∑ j, a n j ^ 2)) := by fun_prop
    exact this.aemeasurable
  have hZ : AEMeasurable (id : ℝ → ℝ) (gaussianReal 0 1) := aemeasurable_id
  have hd : TendstoInDistribution (fun n (x : ι n → ℝ) =>
      (∑ j, a n j * (x j ^ 2 - 1)) / Real.sqrt (2 * ∑ j, a n j ^ 2)) atTop id
      (fun n => Measure.pi fun _ : ι n => gaussianReal 0 1) (gaussianReal 0 1) := by
    refine TendstoInDistribution.of_tendsto_charFun hX hZ fun t => ?_
    rw [Measure.map_id]
    have h := s7w4_tendsto_charFun a hσ hmax t
    convert h using 2
    rw [charFun_gaussianReal]
    congr 1
    push_cast; ring
  let f : BoundedContinuousFunction ℝ ℝ := BoundedContinuousFunction.mkOfBound ⟨F, hF⟩ (2 * M) (fun x y => by
    simp only [ContinuousMap.coe_mk, Real.dist_eq]
    calc |F x - F y| ≤ |F x| + |F y| := abs_sub _ _
      _ ≤ 2 * M := by linarith [hM x, hM y])
  have := (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ hX hZ).1 hd f
  simpa [f] using this

end HRS.MC.Sec7.W4
