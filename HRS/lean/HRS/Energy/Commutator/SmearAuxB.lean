import HRS.Energy.Commutator.SmearAux

/-!
# Auxiliary lemmas for `Smear.lean` (packet CM-S2), part B: Gaussian test functions

The Gaussian `gφ d s z` is an admissible test function (`TF`) for the radial Green identity of
`SmearAux.lean`; its Laplacian is the heat operator `∂_s`.  Facts on the Yukawa profile used to
feed `core_weak`.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators Pointwise
noncomputable section
namespace HRS.Commutator.SmearAux
variable {d : ℕ}

theorem integrable_pow_gauss (hd : 1 ≤ d) {b : ℝ} (hb : 0 < b) (k : ℕ) :
    Integrable (fun w : Euc d => (1 + ‖w‖) ^ k * Real.exp (-b * ‖w‖ ^ 2)) := by
  have : Nontrivial (Euc d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hfr : Module.finrank ℝ (Euc d) = d := by simp
  rw [integrable_fun_norm_addHaar (volume : Measure (Euc d)) (f := fun r : ℝ => (1 + r) ^ k * Real.exp (-b * r ^ 2))]
  rw [hfr]
  have h1 := integrableOn_rpow_mul_exp_neg_mul_sq (b := b) hb (s := ((d - 1 : ℕ) : ℝ)) (by
    have : (0:ℝ) ≤ ((d - 1 : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith)
  have h2 := integrableOn_rpow_mul_exp_neg_mul_sq (b := b) hb (s := ((d - 1 + k : ℕ) : ℝ)) (by
    have : (0:ℝ) ≤ ((d - 1 + k : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith)
  have h3 := (h1.add h2).const_mul (2 ^ k)
  refine Integrable.mono' h3 ?_ ?_
  · refine (Measurable.aestronglyMeasurable ?_)
    fun_prop
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun r hr => ?_)
    have hr' : (0:ℝ) < r := hr
    simp only [smul_eq_mul, Real.rpow_natCast, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity)]
    have hk : (1 + r) ^ k ≤ 2 ^ k * (1 + r ^ k) := by
      rcases le_total r 1 with h | h
      · calc (1 + r) ^ k ≤ 2 ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
          _ ≤ 2 ^ k * (1 + r ^ k) := by nlinarith [pow_nonneg hr'.le k, pow_pos (by norm_num : (0:ℝ) < 2) k]
      · calc (1 + r) ^ k ≤ (2 * r) ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
          _ = 2 ^ k * r ^ k := by rw [mul_pow]
          _ ≤ 2 ^ k * (1 + r ^ k) := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) k]
    have hE := Real.exp_pos (-b * r ^ 2)
    calc r ^ (d - 1) * ((1 + r) ^ k * Real.exp (-b * r ^ 2))
        ≤ r ^ (d - 1) * (2 ^ k * (1 + r ^ k) * Real.exp (-b * r ^ 2)) := by gcongr
      _ = 2 ^ k * (r ^ (d - 1) * Real.exp (-b * r ^ 2) + r ^ (d - 1 + k) * Real.exp (-b * r ^ 2)) := by
          rw [pow_add]; ring

theorem integrable_pow_gauss_shift (hd : 1 ≤ d) {b : ℝ} (hb : 0 < b) (k : ℕ) (z : Euc d) :
    Integrable (fun y : Euc d => (1 + ‖y‖) ^ k * Real.exp (-b * ‖y - z‖ ^ 2)) := by
  have h := (integrable_pow_gauss hd hb k).comp_sub_right z
  have h2 := h.const_mul ((1 + ‖z‖) ^ k)
  refine Integrable.mono' h2 ?_ (Eventually.of_forall fun y => ?_)
  · exact (by fun_prop : Continuous fun y : Euc d => (1 + ‖y‖) ^ k * Real.exp (-b * ‖y - z‖ ^ 2)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have : (1 + ‖y‖) ≤ (1 + ‖z‖) * (1 + ‖y - z‖) := by
      have := norm_le_insert' y z
      nlinarith [norm_nonneg z, norm_nonneg (y - z), norm_nonneg y]
    calc (1 + ‖y‖) ^ k * Real.exp (-b * ‖y - z‖ ^ 2)
        ≤ ((1 + ‖z‖) * (1 + ‖y - z‖)) ^ k * Real.exp (-b * ‖y - z‖ ^ 2) := by gcongr
      _ = (1 + ‖z‖) ^ k * ((1 + ‖y - z‖) ^ k * Real.exp (-b * ‖y - z‖ ^ 2)) := by rw [mul_pow]; ring

theorem integral_gauss_one (hd : 1 ≤ d) {s : ℝ} (hs : 0 < s) (z : Euc d) :
    ∫ y : Euc d, (4 * Real.pi * s) ^ (-(d : ℝ) / 2) * Real.exp (-‖y - z‖ ^ 2 / (4 * s)) = 1 := by
  have : Nontrivial (Euc d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hfr : Module.finrank ℝ (Euc d) = d := by simp
  rw [integral_const_mul]
  have h := integral_sub_right_eq_self (μ := (volume : Measure (Euc d)))
    (fun v : Euc d => Real.exp (-(1 / (4 * s)) * ‖v‖ ^ 2)) z
  have e : ∀ y : Euc d, Real.exp (-‖y - z‖ ^ 2 / (4 * s)) = Real.exp (-(1 / (4 * s)) * ‖y - z‖ ^ 2) := by
    intro y; congr 1; ring
  simp_rw [e]
  rw [h, GaussianFourier.integral_rexp_neg_mul_sq_norm (by positivity), hfr]
  have h1 : Real.pi / (1 / (4 * s)) = 4 * Real.pi * s := by field_simp
  rw [h1, ← Real.rpow_add (by positivity)]
  have h0 : -(d : ℝ) / 2 + (d : ℝ) / 2 = 0 := by ring
  rw [h0, Real.rpow_zero]

/-- the Gaussian (heat kernel) test function centred at `z` with variance parameter `s`. -/
def gφ (d : ℕ) (s : ℝ) (z : Euc d) (y : Euc d) : ℝ :=
  (4 * Real.pi * s) ^ (-(d : ℝ) / 2) * Real.exp (-‖y - z‖ ^ 2 / (4 * s))

theorem gφ_eq (d : ℕ) (s : ℝ) (z y : Euc d) : gφ d s z y = SliceAux.gprof d s ‖y - z‖ := rfl

theorem gφ_pos (d : ℕ) {s : ℝ} (hs : 0 < s) (z y : Euc d) : 0 < gφ d s z y := by
  unfold gφ; positivity

theorem gφ_eq' (d : ℕ) (s : ℝ) (z : Euc d) :
    gφ d s z = fun y => (4 * Real.pi * s) ^ (-(d : ℝ) / 2) * Real.exp (-(1 / (4 * s)) * ‖y - z‖ ^ 2) := by
  funext y; unfold gφ; congr 2; ring

theorem hasFDerivAt_gφ {s : ℝ} (hs : 0 < s) (z y : Euc d) :
    HasFDerivAt (gφ d s z) ((-(gφ d s z y / (2 * s))) • innerSL ℝ (y - z)) y := by
  have h1 : HasFDerivAt (fun y : Euc d => ‖y - z‖ ^ 2) (2 • innerSL ℝ (y - z)) y := by
    have := (hasStrictFDerivAt_norm_sq (y - z)).hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const z)
    refine (show HasFDerivAt (fun y : Euc d => ‖y - z‖ ^ 2) _ y from this).congr_fderiv ?_
    ext v; simp
  have h2 := (((h1.const_mul (-(1 / (4 * s)))).exp).const_mul ((4 * Real.pi * s) ^ (-(d : ℝ) / 2)))
  rw [← gφ_eq'] at h2
  refine h2.congr_fderiv ?_
  ext v
  have : Real.exp (-(1 / (4 * s)) * ‖y - z‖ ^ 2) = Real.exp (-‖y - z‖ ^ 2 / (4 * s)) := by
    congr 1; ring
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, nsmul_eq_mul, smul_eq_mul, gφ,
    this]
  field_simp
  push_cast
  ring


theorem fderiv_gφ_ei {s : ℝ} (hs : 0 < s) (z y : Euc d) (i : Fin d) :
    fderiv ℝ (gφ d s z) y (ei i) = -(gφ d s z y / (2 * s)) * (y i - z i) := by
  rw [(hasFDerivAt_gφ hs z y).fderiv]
  simp [ei, EuclideanSpace.inner_single_right]

theorem dd_gφ {s : ℝ} (hs : 0 < s) (z y : Euc d) (i : Fin d) :
    dd (gφ d s z) i y = gφ d s z y * ((y i - z i) ^ 2 / (4 * s ^ 2) - 1 / (2 * s)) := by
  unfold dd
  have e : (fun x => fderiv ℝ (gφ d s z) x (ei i)) =
      fun x => (-(1 / (2 * s)) * gφ d s z x) * (x i - z i) :=
    funext fun x => by rw [fderiv_gφ_ei hs z x i]; ring
  rw [e]
  have hp : HasFDerivAt (fun x : Euc d => x i - z i) (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ) y :=
    ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).hasFDerivAt).sub_const (z i)
  have h := (((hasFDerivAt_gφ hs z y).const_mul (-(1 / (2 * s)))).mul hp)
  have h' : HasFDerivAt (fun x : Euc d => (-(1 / (2 * s)) * gφ d s z x) * (x i - z i)) _ y := h
  rw [h'.fderiv]
  simp [ei, EuclideanSpace.inner_single_right]
  field_simp
  ring

theorem lap_gφ {s : ℝ} (hs : 0 < s) (z y : Euc d) :
    lap (gφ d s z) y = gφ d s z y * (‖y - z‖ ^ 2 / (4 * s ^ 2) - (d : ℝ) / (2 * s)) := by
  unfold lap
  simp_rw [dd_gφ hs]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_div]
  have h1 : ∑ i, (y i - z i) ^ 2 = ‖y - z‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Real.norm_eq_abs, sq_abs]
  rw [h1]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  congr 2
  ring

theorem contDiff_gφ (s : ℝ) (z : Euc d) : ContDiff ℝ 2 (gφ d s z) := by
  rw [gφ_eq']
  refine contDiff_const.mul (Real.contDiff_exp.comp (contDiff_const.mul ?_))
  exact (contDiff_id.sub contDiff_const).norm_sq ℝ


theorem gφ_eq'' (d : ℕ) (s : ℝ) (z y : Euc d) :
    gφ d s z y = (4 * Real.pi * s) ^ (-(d : ℝ) / 2) * Real.exp (-(1 / (4 * s)) * ‖y - z‖ ^ 2) := by
  rw [gφ_eq']

theorem norm_fderiv_gφ {s : ℝ} (hs : 0 < s) (z y : Euc d) :
    ‖fderiv ℝ (gφ d s z) y‖ = gφ d s z y / (2 * s) * ‖y - z‖ := by
  rw [(hasFDerivAt_gφ hs z y).fderiv, norm_smul, innerSL_apply_norm, norm_neg, Real.norm_eq_abs,
    abs_of_pos (div_pos (gφ_pos d hs z y) (by positivity))]

theorem TF_gφ (hd : 1 ≤ d) {s : ℝ} (hs : 0 < s) (z : Euc d) : TF (gφ d s z) := by
  have hb : 0 < 1 / (4 * s) := by positivity
  set c : ℝ := (4 * Real.pi * s) ^ (-(d : ℝ) / 2) with hc
  have hc0 : 0 < c := by rw [hc]; positivity
  have hcont : Continuous (gφ d s z) := (contDiff_gφ s z).continuous
  have hG : ∀ k : ℕ, Integrable (fun y : Euc d => (1 + ‖y‖) ^ k * gφ d s z y) := by
    intro k
    have := (integrable_pow_gauss_shift hd hb k z).const_mul c
    refine this.congr (Eventually.of_forall fun y => ?_)
    simp only [gφ_eq'']; ring
  have hz1 : (0:ℝ) ≤ ‖z‖ := norm_nonneg z
  have hyz : ∀ y : Euc d, ‖y - z‖ ≤ (1 + ‖z‖) * (1 + ‖y‖) := fun y => by
    have := norm_sub_le y z
    nlinarith [norm_nonneg y]
  refine ⟨contDiff_gφ s z, ?_, ?_, ?_, ?_⟩
  · have := hG 1
    refine this.congr (Eventually.of_forall fun y => ?_)
    simp only [pow_one, abs_of_pos (gφ_pos d hs z y)]
  · -- first derivative
    have := (hG 2).const_mul ((1 + ‖z‖) / (2 * s))
    refine Integrable.mono' this ?_ (Eventually.of_forall fun y => ?_)
    · exact (Continuous.aestronglyMeasurable (by
        have h1 : Continuous fun y : Euc d => fderiv ℝ (gφ d s z) y := (contDiff_gφ s z).continuous_fderiv (by norm_num)
        exact (continuous_const.add continuous_norm).mul h1.norm))
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (norm_nonneg _)),
        norm_fderiv_gφ hs]
      have hg := gφ_pos d hs z y
      calc (1 + ‖y‖) * (gφ d s z y / (2 * s) * ‖y - z‖)
          ≤ (1 + ‖y‖) * (gφ d s z y / (2 * s) * ((1 + ‖z‖) * (1 + ‖y‖))) := by gcongr; exact hyz y
        _ = (1 + ‖z‖) / (2 * s) * ((1 + ‖y‖) ^ 2 * gφ d s z y) := by ring
  · intro i
    have := (hG 3).const_mul (((1 + ‖z‖) ^ 2 / (4 * s ^ 2) + 1 / (2 * s)))
    have hdd : dd (gφ d s z) i = fun y => gφ d s z y * ((y i - z i) ^ 2 / (4 * s ^ 2) - 1 / (2 * s)) :=
      funext fun y => dd_gφ hs z y i
    refine Integrable.mono' this ?_ (Eventually.of_forall fun y => ?_)
    · rw [hdd]
      refine Continuous.aestronglyMeasurable ?_
      refine (continuous_const.add continuous_norm).mul (Continuous.abs (hcont.mul ?_))
      exact (((EuclideanSpace.proj i).continuous.sub continuous_const).pow 2).div_const _ |>.sub continuous_const
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) (abs_nonneg _)), hdd]
      show (1 + ‖y‖) * |gφ d s z y * ((y i - z i) ^ 2 / (4 * s ^ 2) - 1 / (2 * s))| ≤ _
      have hg := gφ_pos d hs z y
      have h1 : (y i - z i) ^ 2 ≤ ‖y - z‖ ^ 2 := by
        have := abs_apply_le_norm (y - z) i
        have h2 : |y i - z i| ≤ ‖y - z‖ := by simpa using this
        nlinarith [sq_abs (y i - z i), abs_nonneg (y i - z i)]
      have h3 : ‖y - z‖ ^ 2 ≤ ((1 + ‖z‖) * (1 + ‖y‖)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (hyz y) 2
      have h4 : |(y i - z i) ^ 2 / (4 * s ^ 2) - 1 / (2 * s)| ≤
          (1 + ‖z‖) ^ 2 * (1 + ‖y‖) ^ 2 / (4 * s ^ 2) + 1 / (2 * s) := by
        have h5 : 0 ≤ (y i - z i) ^ 2 / (4 * s ^ 2) := by positivity
        have h6 : (y i - z i) ^ 2 / (4 * s ^ 2) ≤ (1 + ‖z‖) ^ 2 * (1 + ‖y‖) ^ 2 / (4 * s ^ 2) := by
          gcongr
          calc (y i - z i) ^ 2 ≤ ‖y - z‖ ^ 2 := h1
            _ ≤ ((1 + ‖z‖) * (1 + ‖y‖)) ^ 2 := h3
            _ = _ := by ring
        have h7 : 0 < 1 / (2 * s) := by positivity
        rw [abs_le]; constructor <;> nlinarith
      have h8 : (1 + ‖y‖) ≤ (1 + ‖y‖) ^ 3 := by
        have : (1:ℝ) ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
        nlinarith [pow_nonneg (by linarith : (0:ℝ) ≤ 1 + ‖y‖) 2]
      rw [abs_mul, abs_of_pos hg]
      have h9 : (1 + ‖z‖) ^ 2 * (1 + ‖y‖) ^ 2 / (4 * s ^ 2) + 1 / (2 * s) ≤
          ((1 + ‖z‖) ^ 2 / (4 * s ^ 2) + 1 / (2 * s)) * (1 + ‖y‖) ^ 2 := by
        have : (1:ℝ) ≤ (1 + ‖y‖) ^ 2 := by nlinarith [norm_nonneg y]
        have h10 : 0 < 1 / (2 * s) := by positivity
        calc (1 + ‖z‖) ^ 2 * (1 + ‖y‖) ^ 2 / (4 * s ^ 2) + 1 / (2 * s)
            ≤ (1 + ‖z‖) ^ 2 * (1 + ‖y‖) ^ 2 / (4 * s ^ 2) + 1 / (2 * s) * (1 + ‖y‖) ^ 2 := by nlinarith
          _ = _ := by ring
      calc (1 + ‖y‖) * (gφ d s z y * |(y i - z i) ^ 2 / (4 * s ^ 2) - 1 / (2 * s)|)
          ≤ (1 + ‖y‖) * (gφ d s z y * (((1 + ‖z‖) ^ 2 / (4 * s ^ 2) + 1 / (2 * s)) * (1 + ‖y‖) ^ 2)) := by
            gcongr
            exact h4.trans h9
        _ = ((1 + ‖z‖) ^ 2 / (4 * s ^ 2) + 1 / (2 * s)) * ((1 + ‖y‖) ^ 3 * gφ d s z y) := by ring
  · -- bounded gradient
    refine ⟨c / (2 * s) * ((1 + 1 / (1 / (4 * s))) / 2), fun y => ?_⟩
    rw [norm_fderiv_gφ hs, gφ_eq'']
    set r := ‖y - z‖ with hr
    have hr0 : 0 ≤ r := norm_nonneg _
    have hE : (1 + (1 / (4 * s)) * r ^ 2) * Real.exp (-(1 / (4 * s)) * r ^ 2) ≤ 1 := by
      have := Real.add_one_le_exp ((1 / (4 * s)) * r ^ 2)
      have h2 : Real.exp (-(1 / (4 * s)) * r ^ 2) = (Real.exp ((1 / (4 * s)) * r ^ 2))⁻¹ := by
        rw [← Real.exp_neg]; congr 1; ring
      rw [h2, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
      linarith
    have hE2 : r * Real.exp (-(1 / (4 * s)) * r ^ 2) ≤ (1 + 1 / (1 / (4 * s))) / 2 := by
      have h3 : r ≤ (1 + r ^ 2) / 2 := by nlinarith [sq_nonneg (r - 1)]
      have h4 : 1 + r ^ 2 ≤ (1 + 1 / (1 / (4 * s))) * (1 + (1 / (4 * s)) * r ^ 2) := by
        have : (1:ℝ) / (1 / (4 * s)) = 4 * s := by field_simp
        rw [this]
        have h5 : 0 ≤ 1 / (4 * s) * r ^ 2 := by positivity
        have h6 : 4 * s * (1 / (4 * s) * r ^ 2) = r ^ 2 := by field_simp
        nlinarith [sq_nonneg r]
      have he := Real.exp_pos (-(1 / (4 * s)) * r ^ 2)
      calc r * Real.exp (-(1 / (4 * s)) * r ^ 2) ≤ (1 + r ^ 2) / 2 * Real.exp (-(1 / (4 * s)) * r ^ 2) := by gcongr
        _ ≤ (1 + 1 / (1 / (4 * s))) * (1 + (1 / (4 * s)) * r ^ 2) / 2 * Real.exp (-(1 / (4 * s)) * r ^ 2) := by gcongr
        _ = (1 + 1 / (1 / (4 * s))) / 2 * ((1 + (1 / (4 * s)) * r ^ 2) * Real.exp (-(1 / (4 * s)) * r ^ 2)) := by ring
        _ ≤ (1 + 1 / (1 / (4 * s))) / 2 * 1 := by gcongr
        _ = _ := by ring
    calc c * Real.exp (-(1 / (4 * s)) * r ^ 2) / (2 * s) * r
        = c / (2 * s) * (r * Real.exp (-(1 / (4 * s)) * r ^ 2)) := by ring
      _ ≤ _ := by gcongr


/-! ### Facts on the Yukawa profile -/

theorem hasDerivAt_yukawa (hd : 1 ≤ d) {l : ℝ} (hl : 0 < l) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (yukawa d l) (deriv (yukawa d l) r) r := by
  have := (SliceAux.hasDerivAt_yk hd hl hr).2
  have h : yukawa d l = fun r => ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * SliceAux.gprof d t r := rfl
  rw [h]
  exact this.differentiableAt.hasDerivAt

theorem deriv_yukawa_neg (hd : 1 ≤ d) {l : ℝ} (hl : 0 < l) {r : ℝ} (hr : 0 < r) :
    deriv (yukawa d l) r < 0 := by
  have h := (SliceAux.hasDerivAt_yk hd hl hr).2.deriv
  have h2 : yukawa d l = fun r => ∫ t in Ioi (0 : ℝ), Real.exp (-l * t) * SliceAux.gprof d t r := rfl
  rw [h2, h]
  exact SliceAux.yk_deriv_neg hd hl hr

theorem hasDerivAt_flux (hd : 1 ≤ d) {l : ℝ} (hl : 0 < l) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun r => r ^ (d - 1) * deriv (yukawa d l) r) (l * r ^ (d - 1) * yukawa d l r) r := by
  have h := (yukawa_ode hd hl).2.2.1 r hr
  have hpos : 0 < l * r ^ (d - 1) * yukawa d l r :=
    mul_pos (mul_pos hl (pow_pos hr _)) ((yukawa_ode hd hl).1 r hr)
  have hne : deriv (fun r => r ^ (d - 1) * deriv (yukawa d l) r) r ≠ 0 := by rw [h]; exact hpos.ne'
  have := (differentiableAt_of_deriv_ne_zero hne).hasDerivAt
  rwa [h] at this

theorem bound_deriv_yukawa (hd : 1 ≤ d) {l η : ℝ} (hl : 0 < l) (hη : 0 < η) :
    ∃ C : ℝ, ∀ s, η ≤ s → |deriv (yukawa d l) s| ≤ C := by
  set q : ℝ → ℝ := fun r => r ^ (d - 1) * deriv (yukawa d l) r with hq
  have hqd : ∀ r, 0 < r → HasDerivAt q (l * r ^ (d - 1) * yukawa d l r) r :=
    fun r hr => hasDerivAt_flux hd hl hr
  have hmono : MonotoneOn q (Ici η) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici η) ?_ ?_ ?_
    · intro r hr; exact (hqd r (lt_of_lt_of_le hη hr)).continuousAt.continuousWithinAt
    · intro r hr; exact (hqd r (lt_of_lt_of_le hη (interior_subset hr))).differentiableAt.differentiableWithinAt
    · intro r hr
      have hr' : η < r := by simpa using hr
      have hr0 : 0 < r := lt_trans hη hr'
      rw [(hqd r hr0).deriv]
      exact (mul_pos (mul_pos hl (pow_pos hr0 _)) ((yukawa_ode hd hl).1 r hr0)).le
  refine ⟨|q η| / η ^ (d - 1), fun s hs => ?_⟩
  have hs0 : 0 < s := lt_of_lt_of_le hη hs
  have h1 : q η ≤ q s := hmono (mem_Ici.2 le_rfl) (mem_Ici.2 hs) hs
  have h2 : q s ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (pow_pos hs0 _).le (deriv_yukawa_neg hd hl hs0).le
  have h3 : |q s| ≤ |q η| := by
    rw [abs_of_nonpos h2]; rw [abs_of_nonpos (h1.trans h2)]; linarith
  have h4 : |deriv (yukawa d l) s| = |q s| / s ^ (d - 1) := by
    rw [hq]; simp only []
    rw [abs_mul, abs_of_pos (pow_pos hs0 _)]
    field_simp
  rw [h4]
  have h5 : η ^ (d - 1) ≤ s ^ (d - 1) := pow_le_pow_left₀ hη.le hs _
  calc |q s| / s ^ (d - 1) ≤ |q η| / s ^ (d - 1) := by gcongr
    _ ≤ |q η| / η ^ (d - 1) := by
        apply div_le_div_of_nonneg_left (abs_nonneg _) (pow_pos hη _) h5


/-- negation on the unit sphere -/
def negS (d : ℕ) (ω : sphere (0 : Euc d) 1) : sphere (0 : Euc d) 1 := ⟨-(ω : Euc d), by simp⟩

theorem continuous_negS : Continuous (negS d) :=
  Continuous.subtype_mk (continuous_neg.comp continuous_subtype_val) _

theorem negS_negS (ω : sphere (0 : Euc d) 1) : negS d (negS d ω) = ω := by
  ext; simp [negS]

theorem toSphere_neg : (sphMeas d).map (negS d) = sphMeas d := by
  ext s hs
  rw [Measure.map_apply continuous_negS.measurable hs]
  have hs' : MeasurableSet (negS d ⁻¹' s) := continuous_negS.measurable hs
  rw [Measure.toSphere_apply' _ hs', Measure.toSphere_apply' _ hs]
  congr 1
  have : Ioo (0:ℝ) 1 • (Subtype.val '' (negS d ⁻¹' s)) = -(Ioo (0:ℝ) 1 • (Subtype.val '' s) : Set (Euc d)) := by
    ext x
    rw [Set.mem_neg]
    constructor
    · rintro ⟨t, ht, y, ⟨ω, hω, rfl⟩, hx⟩
      refine ⟨t, ht, ((negS d ω : sphere (0 : Euc d) 1) : Euc d), ⟨negS d ω, hω, rfl⟩, ?_⟩
      rw [← hx]; simp [negS]
    · rintro ⟨t, ht, y, ⟨ω, hω, rfl⟩, hx⟩
      refine ⟨t, ht, ((negS d ω : sphere (0 : Euc d) 1) : Euc d), ⟨negS d ω, ?_, rfl⟩, ?_⟩
      · simpa [negS_negS] using hω
      · have hx' : t • (ω : Euc d) = -x := hx
        have : x = -(t • (ω : Euc d)) := by rw [hx']; simp
        show t • _ = x
        rw [this]; simp [negS]
  rw [this, Measure.measure_neg]



theorem real_volume_ball_one (hd : 1 ≤ d) :
    (volume : Measure (Euc d)).real (ball 0 1) = Real.sqrt Real.pi ^ d / Real.Gamma ((d : ℝ) / 2 + 1) := by
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  rw [measureReal_def, EuclideanSpace.volume_ball]
  simp only [ENNReal.ofReal_one, one_pow, one_mul, Fintype.card_fin]
  rw [ENNReal.toReal_ofReal]
  have := Real.Gamma_pos_of_pos (show (0:ℝ) < (d : ℝ) / 2 + 1 by positivity)
  positivity

theorem sphere_mass_mul_flux (hd : 1 ≤ d) :
    (volume : Measure (Euc d)).toSphere.real univ *
      (Real.Gamma ((d : ℝ) / 2) / (2 * Real.pi ^ ((d : ℝ) / 2))) = 1 := by
  have : Nontrivial (Euc d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hfr : Module.finrank ℝ (Euc d) = d := by simp
  rw [Measure.toSphere_real_apply_univ, hfr, real_volume_ball_one hd]
  have hd0 : (0:ℝ) < d := by exact_mod_cast hd
  have hG : Real.Gamma ((d : ℝ) / 2 + 1) = (d : ℝ) / 2 * Real.Gamma ((d : ℝ) / 2) :=
    Real.Gamma_add_one (by positivity)
  have hGp : 0 < Real.Gamma ((d : ℝ) / 2) := Real.Gamma_pos_of_pos (by positivity)
  have hs : Real.sqrt Real.pi ^ d = Real.pi ^ ((d : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le]
    congr 1; ring
  rw [hG, hs]
  have hp : 0 < Real.pi ^ ((d : ℝ) / 2) := by positivity
  field_simp


theorem int_flux (hd : 1 ≤ d) {l η : ℝ} (hl : 0 < l) (hη : 0 < η) :
    IntegrableOn (fun r : ℝ => r ^ (d - 1) * yukawa d l r) (Ioc 0 η) ∧
    l * ∫ r in Ioc 0 η, r ^ (d - 1) * yukawa d l r =
      η ^ (d - 1) * deriv (yukawa d l) η + Real.Gamma ((d : ℝ) / 2) / (2 * Real.pi ^ ((d : ℝ) / 2)) := by
  set κ : ℝ := Real.Gamma ((d : ℝ) / 2) / (2 * Real.pi ^ ((d : ℝ) / 2)) with hκ
  set q : ℝ → ℝ := fun r => r ^ (d - 1) * deriv (yukawa d l) r with hq
  set Q : ℝ → ℝ := Function.update q 0 (-κ) with hQ
  have hqd : ∀ r, 0 < r → HasDerivAt q (l * r ^ (d - 1) * yukawa d l r) r :=
    fun r hr => hasDerivAt_flux hd hl hr
  have hlim : Tendsto q (𝓝[>] 0) (𝓝 (-κ)) := by
    have := ((yukawa_ode hd hl).2.2.2).neg
    simpa [hq] using this
  have hQd : ∀ r, 0 < r → HasDerivAt Q (l * r ^ (d - 1) * yukawa d l r) r := by
    intro r hr
    refine (hqd r hr).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hr] with s hs
    exact Function.update_of_ne (ne_of_gt hs) _ _
  have hQc : ContinuousOn Q (Icc 0 η) := by
    intro r hr
    rcases eq_or_lt_of_le hr.1 with h0 | hpos
    · subst h0
      have : ContinuousWithinAt Q (Ioi 0) 0 := by
        rw [ContinuousWithinAt, hQ, Function.update_self]
        refine hlim.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with s hs
        exact (Function.update_of_ne (ne_of_gt hs) _ _).symm
      exact (continuousWithinAt_Ioi_iff_Ici.1 this).mono Icc_subset_Ici_self
    · exact (hQd r hpos).continuousAt.continuousWithinAt
  have hint : IntegrableOn (fun r : ℝ => l * r ^ (d - 1) * yukawa d l r) (Ioc 0 η) :=
    intervalIntegral.integrableOn_deriv_of_nonneg hQc (fun r hr => hQd r hr.1)
      (fun r hr => (mul_pos (mul_pos hl (pow_pos hr.1 _)) ((yukawa_ode hd hl).1 r hr.1)).le)
  have hint' : IntegrableOn (fun r : ℝ => r ^ (d - 1) * yukawa d l r) (Ioc 0 η) := by
    have : IntegrableOn (fun r : ℝ => 1 / l * (l * r ^ (d - 1) * yukawa d l r)) (Ioc 0 η) := hint.const_mul (1 / l)
    refine this.congr_fun (fun r _ => ?_) measurableSet_Ioc
    field_simp
  refine ⟨hint', ?_⟩
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hη.le hQc (fun r hr => hQd r hr.1)
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hη.le).2 hint)
  rw [intervalIntegral.integral_of_le hη.le] at h
  have e : ∫ r in Ioc 0 η, l * r ^ (d - 1) * yukawa d l r = l * ∫ r in Ioc 0 η, r ^ (d - 1) * yukawa d l r := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioc fun r _ => by ring
  rw [e] at h
  rw [h, hQ, Function.update_self, Function.update_of_ne hη.ne']
  ring


theorem integral_torus_radial (hd : 1 ≤ d) {η : ℝ} (hη2 : η < 1 / 2) (Fm : ℝ → ℝ)
    (hF : ∀ r, η ≤ r → Fm r = 0) :
    ∫ z : Torus d, Fm ‖KernelGrad.centeredRep z‖ =
      (volume : Measure (Euc d)).toSphere.real univ * ∫ r in Ioi (0 : ℝ), r ^ (d - 1) * Fm r := by
  have : Nontrivial (Euc d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hfr : Module.finrank ℝ (Euc d) = d := by simp
  rw [KernelAux.integral_torus_box]
  have hmp := PiLp.volume_preserving_ofLp (Fin d)
  have hemb : MeasurableEmbedding (@WithLp.ofLp 2 (Fin d → ℝ)) :=
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm.measurableEmbedding
  have h1 : ∫ y in KernelAux.Box d, Fm ‖KernelGrad.centeredRep (KernelAux.boxPt y)‖ =
      ∫ y in KernelAux.Box d, Fm ‖(WithLp.toLp 2 y : Euc d)‖ := by
    refine setIntegral_congr_fun (KernelAux.measurableSet_Box d) fun y hy => ?_
    simp only []
    rw [HRS.CoercAux.centeredRep_boxPt (fun i => KernelAux.Box_abs_le hy i)]
  rw [h1]
  have h2 := hmp.setIntegral_preimage_emb hemb (fun y : Fin d → ℝ => Fm ‖(WithLp.toLp 2 y : Euc d)‖)
    (KernelAux.Box d)
  rw [← h2]
  simp only [WithLp.toLp_ofLp]
  have h3 : ∫ w in (@WithLp.ofLp 2 (Fin d → ℝ)) ⁻¹' (KernelAux.Box d), Fm ‖w‖ = ∫ w : Euc d, Fm ‖w‖ := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun w hw => hF _ ?_
    by_contra hlt
    push_neg at hlt
    apply hw
    show (w : Fin d → ℝ) ∈ KernelAux.Box d
    intro i
    have := abs_apply_le_norm w i
    have h4 := abs_le.1 (this.trans hlt.le)
    simp only [mem_Ioc]
    constructor <;> linarith [h4.1, h4.2]
  rw [h3, integral_fun_norm_addHaar (volume : Measure (Euc d)) Fm, hfr, Measure.toSphere_real_apply_univ, hfr]
  simp only [nsmul_eq_mul, smul_eq_mul]
  ring


end HRS.Commutator.SmearAux
