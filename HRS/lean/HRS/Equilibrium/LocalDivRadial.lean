import HRS.Equilibrium.LocalDivAux
import HRS.Equilibrium.LocalDivTaylor
open MeasureTheory Set Metric
noncomputable section
namespace HRS.LocalDivAux
variable {d : ℕ}

/-- `d · vol(B₁)`: the total mass of the radial measure. -/
def ballConst (d : ℕ) : ℝ := d * (volume : Measure (EuclideanSpace ℝ (Fin d))).real (ball 0 1)

theorem ballConst_nonneg : 0 ≤ ballConst d := by
  unfold ballConst
  exact mul_nonneg (Nat.cast_nonneg d) measureReal_nonneg

theorem integral_radial (hd : 1 ≤ d) (g : ℝ → ℝ) :
    ∫ w : EuclideanSpace ℝ (Fin d), g ‖w‖ =
      ballConst d * ∫ r in Ioi (0 : ℝ), r ^ (d - 1) * g r := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have := integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin d))) g
  rw [finrank_euclideanSpace_fin] at this
  simp only [ballConst]
  rw [this]
  simp [smul_eq_mul, nsmul_eq_mul, mul_assoc]

theorem Ioc_pow_integral (n : ℕ) (a : ℝ) {ε δ : ℝ} (hε : 0 < ε) (hεδ : ε ≤ δ) :
    ∫ r in Ioi (0 : ℝ), r ^ n * (Ioc ε δ).indicator (fun r => r ^ (-a)) r =
      ∫ r in ε..δ, r ^ ((n : ℝ) - a) := by
  have h1 : ∀ r : ℝ, r ^ n * (Ioc ε δ).indicator (fun r => r ^ (-a)) r =
      (Ioc ε δ).indicator (fun r => r ^ ((n : ℝ) - a)) r := by
    intro r
    by_cases hr : r ∈ Ioc ε δ
    · have hr0 : 0 < r := hε.trans hr.1
      rw [indicator_of_mem hr, indicator_of_mem hr, ← Real.rpow_natCast, ← Real.rpow_add hr0]
      congr 1
    · simp [indicator_of_notMem hr]
  simp_rw [h1]
  rw [intervalIntegral.integral_of_le hεδ, setIntegral_indicator measurableSet_Ioc]
  have e : Ioi (0 : ℝ) ∩ Ioc ε δ = Ioc ε δ := by
    ext r
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨hε.trans h.1, h⟩
  rw [e]


theorem integrable_of_bdd {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : Measurable f) {C R : ℝ}
    (hb : ∀ w, |f w| ≤ C) (hs : ∀ w, R < ‖w‖ → f w = 0) : Integrable f := by
  have h1 : IntegrableOn f (closedBall (0 : EuclideanSpace ℝ (Fin d)) R) := by
    refine Measure.integrableOn_of_bounded (M := C) (measure_closedBall_lt_top).ne
      hf.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun w => by simpa using hb w
  have h2 : f = (closedBall (0 : EuclideanSpace ℝ (Fin d)) R).indicator f := by
    ext w
    by_cases hw : w ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) R
    · rw [indicator_of_mem hw]
    · rw [indicator_of_notMem hw]
      apply hs
      simpa using hw
  rw [h2]
  exact (integrable_indicator_iff measurableSet_closedBall).2 h1


theorem near_pointwise (s t hx q ρ0 ρx D C1 Lρ ρmax : ℝ) (hs : 0 < s) (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hD : 0 ≤ D) (hq : |q| ≤ D * t ^ 2) (hh : |hx + s * t ^ (-s - 2) * q| ≤ C1 * t ^ (1 - s))
    (hC1 : 0 ≤ C1) (hρ0 : 0 ≤ ρ0) (hρ0m : ρ0 ≤ ρmax) (hρx : 0 ≤ ρx) (hρxm : ρx ≤ ρmax)
    (hρ : |ρx - ρ0| ≤ Lρ * t) (hL : 0 ≤ Lρ) :
    |ρ0 * ρx * hx ^ 2 - ρ0 ^ 2 * (s ^ 2 * t ^ (-2 * s - 4) * q ^ 2)| ≤
      ρmax * (ρmax * (2 * s * D * C1 + C1 ^ 2) + Lρ * (s * D) ^ 2) * t ^ (1 - 2 * s) := by
  set a : ℝ := s * t ^ (-s - 2) with ha
  set u : ℝ := t ^ (-s) with hu
  set v : ℝ := t ^ (1 - s) with hv
  set w : ℝ := t ^ (1 - 2 * s) with hw
  have hu0 : 0 < u := Real.rpow_pos_of_pos ht0 _
  have hv0 : 0 < v := Real.rpow_pos_of_pos ht0 _
  have hw0 : 0 < w := Real.rpow_pos_of_pos ht0 _
  have e1 : t ^ (-s - 2) * t ^ 2 = u := by
    rw [← Real.rpow_natCast t 2, ← Real.rpow_add ht0]; congr 1; push_cast; ring
  have e2 : (t ^ (-s - 2)) ^ 2 = t ^ (-2 * s - 4) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]; congr 1; push_cast; ring
  have e3 : v * u = w := by
    rw [hv, hu, ← Real.rpow_add ht0]; congr 1; ring
  have e4 : v * v ≤ w := by
    have : v * v = t ^ (2 - 2 * s) := by
      rw [hv, ← Real.rpow_add ht0]; congr 1; ring
    rw [this]
    exact Real.rpow_le_rpow_of_exponent_ge ht0 ht1 (by linarith)
  have e5 : t * (u * u) = w := by
    calc t * (u * u) = t ^ (1 : ℝ) * t ^ (-s) * t ^ (-s) := by rw [Real.rpow_one]; ring
      _ = t ^ ((1 : ℝ) + -s + -s) := by rw [Real.rpow_add ht0, Real.rpow_add ht0]
      _ = w := by rw [hw]; congr 1; ring
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have haq : |a * q| ≤ s * D * u := by
    rw [abs_mul, abs_of_nonneg ha0]
    calc a * |q| ≤ a * (D * t ^ 2) := mul_le_mul_of_nonneg_left hq ha0
      _ = D * (s * (t ^ (-s - 2) * t ^ 2)) := by rw [ha]; ring
      _ = s * D * u := by rw [e1]; ring
  have hRm : |hx + a * q| ≤ C1 * v := hh
  have e6 : s ^ 2 * t ^ (-2 * s - 4) * q ^ 2 = (a * q) ^ 2 := by
    rw [mul_pow, ha, mul_pow, e2]
  rw [e6]
  have h1 : |hx ^ 2 - (a * q) ^ 2| ≤ C1 * v * (C1 * v + 2 * (s * D * u)) := by
    have : hx ^ 2 - (a * q) ^ 2 = (hx + a * q) * ((hx + a * q) - 2 * (a * q)) := by ring
    rw [this, abs_mul]
    refine mul_le_mul hRm ?_ (abs_nonneg _) (by positivity)
    calc |(hx + a * q) - 2 * (a * q)| ≤ |hx + a * q| + |2 * (a * q)| := abs_sub _ _
      _ ≤ C1 * v + 2 * (s * D * u) := by
          rw [abs_mul, abs_two]; linarith
  have h2 : ρ0 * ρx * hx ^ 2 - ρ0 ^ 2 * (a * q) ^ 2 =
      ρ0 * ρx * (hx ^ 2 - (a * q) ^ 2) + ρ0 * (ρx - ρ0) * (a * q) ^ 2 := by ring
  rw [h2]
  have hρm0 : 0 ≤ ρmax := hρ0.trans hρ0m
  have hρρ : 0 ≤ ρ0 * ρx := mul_nonneg hρ0 hρx
  have hρρm : ρ0 * ρx ≤ ρmax * ρmax := mul_le_mul hρ0m hρxm hρx (hρ0.trans hρ0m)
  have t1 : |ρ0 * ρx * (hx ^ 2 - (a * q) ^ 2)| ≤ ρmax * ρmax * (C1 * v * (C1 * v + 2 * (s * D * u))) := by
    rw [abs_mul, abs_of_nonneg hρρ]
    exact mul_le_mul hρρm h1 (abs_nonneg _) (mul_nonneg hρm0 hρm0)
  have t2 : |ρ0 * (ρx - ρ0) * (a * q) ^ 2| ≤ ρmax * (Lρ * t) * (s * D * u) ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg hρ0, abs_pow]
    have : |a * q| ^ 2 ≤ (s * D * u) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) haq 2
    refine mul_le_mul (mul_le_mul hρ0m hρ (abs_nonneg _) hρm0) this (by positivity) (by positivity)
  have t3 : ρmax * ρmax * (C1 * v * (C1 * v + 2 * (s * D * u))) + ρmax * (Lρ * t) * (s * D * u) ^ 2 ≤
      ρmax * (ρmax * (2 * s * D * C1 + C1 ^ 2) + Lρ * (s * D) ^ 2) * w := by
    have : ρmax * ρmax * (C1 * v * (C1 * v + 2 * (s * D * u))) + ρmax * (Lρ * t) * (s * D * u) ^ 2 =
        ρmax * (ρmax * (2 * s * D * C1 * (v * u) + C1 ^ 2 * (v * v)) + Lρ * (s * D) ^ 2 * (t * (u * u))) := by
      ring
    rw [this, e3, e5]
    have : C1 ^ 2 * (v * v) ≤ C1 ^ 2 * w := mul_le_mul_of_nonneg_left e4 (sq_nonneg _)
    nlinarith [mul_nonneg hρm0 hρm0, mul_nonneg hρm0 hL, mul_nonneg (mul_nonneg hρm0 hρm0) (sq_nonneg C1),
      hw0, sq_nonneg (s * D)]
  calc _ ≤ |ρ0 * ρx * (hx ^ 2 - (a * q) ^ 2)| + |ρ0 * (ρx - ρ0) * (a * q) ^ 2| := abs_add_le _ _
    _ ≤ _ := (add_le_add t1 t2).trans t3


theorem volume_cube : (volume : Measure (EuclideanSpace ℝ (Fin d))) (cube d) = 1 := by
  have h := (mk_measurePreserving (d := d)).measure_preimage (s := Set.univ) MeasurableSet.univ.nullMeasurableSet
  simp only [preimage_univ, Measure.restrict_apply MeasurableSet.univ, univ_inter, measure_univ] at h
  exact h

theorem cube_norm_le {w : EuclideanSpace ℝ (Fin d)} (hw : w ∈ cube d) : ‖w‖ ≤ d :=
  norm_le_dim fun i => by
    have := hw i
    rw [abs_le]
    constructor <;> linarith [this.1, this.2]

theorem closedBall_subset_cube {δ : ℝ} (hδ : δ ≤ 1 / 4) :
    closedBall (0 : EuclideanSpace ℝ (Fin d)) δ ⊆ cube d := by
  intro w hw i
  have h1 : |w i| ≤ ‖w‖ := by
    have := PiLp.norm_apply_le w i
    simpa [Real.norm_eq_abs] using this
  have h2 : ‖w‖ ≤ δ := by simpa using hw
  have := abs_le.1 (h1.trans (h2.trans hδ |>.trans (by norm_num : (1:ℝ)/4 ≤ 1/4)))
  constructor <;> linarith [this.1, this.2]


theorem coord_le_norm (w : EuclideanSpace ℝ (Fin d)) (i : Fin d) : |w i| ≤ ‖w‖ := by
  have := PiLp.norm_apply_le w i
  simpa [Real.norm_eq_abs] using this

theorem quad_le {BH : ℝ} (hBH : 0 ≤ BH) (H : Matrix (Fin d) (Fin d) ℝ) (hH : ∀ i j, |H i j| ≤ BH)
    (w : EuclideanSpace ℝ (Fin d)) : |quadForm H w| ≤ (d : ℝ) ^ 2 * BH * ‖w‖ ^ 2 := by
  unfold quadForm
  calc |∑ i, ∑ j, H i j * w i * w j| ≤ ∑ i, |∑ j, H i j * w i * w j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin d, ∑ j : Fin d, BH * ‖w‖ ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [abs_mul, abs_mul]
        have h1 := hH i j
        have h2 := coord_le_norm w i
        have h3 := coord_le_norm w j
        calc |H i j| * |w i| * |w j| ≤ BH * ‖w‖ * ‖w‖ := by gcongr
          _ = BH * ‖w‖ ^ 2 := by ring
    _ = (d : ℝ) ^ 2 * BH * ‖w‖ ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

theorem measurable_quadForm (H : Matrix (Fin d) (Fin d) ℝ) : Measurable (quadForm H) := by
  unfold quadForm
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
  have hi : Measurable fun w : EuclideanSpace ℝ (Fin d) => w i := (EuclideanSpace.proj i).continuous.measurable
  have hj : Measurable fun w : EuclideanSpace ℝ (Fin d) => w j := (EuclideanSpace.proj j).continuous.measurable
  exact (measurable_const.mul hi).mul hj


theorem integrableOn_cube_bdd {P : EuclideanSpace ℝ (Fin d) → ℝ} (hP : Measurable P) {C : ℝ}
    (h : ∀ w ∈ cube d, |P w| ≤ C) : IntegrableOn P (cube d) := by
  refine Measure.integrableOn_of_bounded (M := C) ?_ hP.aestronglyMeasurable ?_
  · rw [volume_cube]; exact ENNReal.one_ne_top
  · exact (ae_restrict_iff' measurableSet_cube).2
      (Filter.Eventually.of_forall fun w hw => by simpa using h w hw)

theorem cube_of_norm_le {δ : ℝ} (hδ4 : δ ≤ 1 / 4) {w : EuclideanSpace ℝ (Fin d)} (hw : ‖w‖ ≤ δ) :
    w ∈ cube d := closedBall_subset_cube hδ4 (by simpa using hw)

theorem rpow_neg_mono {t ε a : ℝ} (hε : 0 < ε) (h : ε ≤ t) (ha : 0 ≤ a) :
    t ^ (-a) ≤ ε ^ (-a) := Real.rpow_le_rpow_of_nonpos hε h (by linarith)

theorem sq_rpow_bound {s B hx t : ℝ} (ht : 0 < t) (h : |hx| ≤ B * t ^ (-s)) :
    hx ^ 2 ≤ B ^ 2 * t ^ (-(2 * s)) := by
  have h1 : hx ^ 2 = |hx| ^ 2 := (sq_abs hx).symm
  rw [h1]
  calc |hx| ^ 2 ≤ (B * t ^ (-s)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = B ^ 2 * t ^ (-(2 * s)) := by
      rw [mul_pow, ← Real.rpow_natCast (t ^ (-s)) 2, ← Real.rpow_mul ht.le]
      congr 2; push_cast; ring


theorem local_estimate (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 < s) {BH C1 B Lρ ρmax δ : ℝ}
    (hBH : 0 ≤ BH) (hC1 : 0 ≤ C1) (hB : 0 ≤ B) (hLρ : 0 ≤ Lρ) (hρmax : 0 ≤ ρmax)
    (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) :
    ∃ K1 K2 : ℝ, 0 ≤ K1 ∧ 0 ≤ K2 ∧ ∀ (H : Matrix (Fin d) (Fin d) ℝ), H.IsHermitian →
      (∀ i j, |H i j| ≤ BH) → ∀ (hx ρx : EuclideanSpace ℝ (Fin d) → ℝ), Measurable hx →
      Measurable ρx → ∀ ρ0 : ℝ,
      (∀ w : EuclideanSpace ℝ (Fin d), 0 < ‖w‖ → ‖w‖ ≤ δ →
        |hx w + s * ‖w‖ ^ (-s - 2) * quadForm H w| ≤ C1 * ‖w‖ ^ (1 - s)) →
      (∀ w ∈ cube d, 0 < ‖w‖ → |hx w| ≤ B * ‖w‖ ^ (-s)) →
      (∀ w ∈ cube d, 0 ≤ ρx w ∧ ρx w ≤ ρmax) → (0 ≤ ρ0 ∧ ρ0 ≤ ρmax) →
      (∀ w : EuclideanSpace ℝ (Fin d), ‖w‖ ≤ δ → |ρx w - ρ0| ≤ Lρ * ‖w‖) →
      ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      |(∫ w in cube d, if ε < ‖w‖ then ρ0 * ρx w * hx w ^ 2 else 0) -
        ρ0 ^ 2 * s ^ 2 * (HRS.sphereArea d / (d * (d + 2)) *
          (H.trace ^ 2 + 2 * ∑ i, ∑ j, H i j ^ 2)) * ∫ r in ε..δ, r ^ ((d : ℝ) - 1 - 2 * s)| ≤
      K1 + K2 * ∫ r in ε..δ, r ^ ((d : ℝ) - 2 * s) := by
  set D : ℝ := (d : ℝ) ^ 2 * BH with hD
  set Kerr : ℝ := ρmax * (ρmax * (2 * s * D * C1 + C1 ^ 2) + Lρ * (s * D) ^ 2) with hKerr
  have hD0 : 0 ≤ D := by positivity
  have hKerr0 : 0 ≤ Kerr := by positivity
  refine ⟨ρmax ^ 2 * B ^ 2 * δ ^ (-(2 * s)), Kerr * ballConst d, by positivity,
    mul_nonneg hKerr0 ballConst_nonneg, ?_⟩
  intro H hH hBHH hx ρx hxm hρm ρ0 hexp hbd hρ hρ0 hρL ε hε hεδ
  set g : EuclideanSpace ℝ (Fin d) → ℝ := fun w => ρ0 * ρx w * hx w ^ 2 with hg
  have hgm : Measurable g := (measurable_const.mul hρm).mul (hxm.pow_const 2)
  have hgb : ∀ w ∈ cube d, 0 < ‖w‖ → |g w| ≤ ρmax ^ 2 * B ^ 2 * ‖w‖ ^ (-(2 * s)) := by
    intro w hw hw0
    have h1 := sq_rpow_bound hw0 (hbd w hw hw0)
    have h2 := hρ w hw
    have h3 : 0 ≤ ρ0 * ρx w := mul_nonneg hρ0.1 h2.1
    have h4 : ρ0 * ρx w ≤ ρmax ^ 2 := by
      rw [sq]; exact mul_le_mul hρ0.2 h2.2 h2.1 hρmax
    simp only [hg]
    rw [abs_of_nonneg (mul_nonneg h3 (sq_nonneg _))]
    calc ρ0 * ρx w * hx w ^ 2 ≤ ρmax ^ 2 * (B ^ 2 * ‖w‖ ^ (-(2 * s))) :=
          mul_le_mul h4 h1 (sq_nonneg _) (sq_nonneg _)
      _ = _ := by ring
  have hgbε : ∀ w ∈ cube d, ε < ‖w‖ → |g w| ≤ ρmax ^ 2 * B ^ 2 * ε ^ (-(2 * s)) := by
    intro w hw hεw
    refine (hgb w hw (hε.trans hεw)).trans ?_
    have := rpow_neg_mono (a := 2 * s) hε hεw.le (by linarith)
    have h0 : 0 ≤ ρmax ^ 2 * B ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left this h0
  have hgbδ : ∀ w ∈ cube d, δ < ‖w‖ → |g w| ≤ ρmax ^ 2 * B ^ 2 * δ ^ (-(2 * s)) := by
    intro w hw hδw
    refine (hgb w hw (hδ.trans hδw)).trans ?_
    have := rpow_neg_mono (a := 2 * s) hδ hδw.le (by linarith)
    have h0 : 0 ≤ ρmax ^ 2 * B ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left this h0
  set Fn : EuclideanSpace ℝ (Fin d) → ℝ := fun w => if ε < ‖w‖ ∧ ‖w‖ ≤ δ then g w else 0 with hFn
  set Ff : EuclideanSpace ℝ (Fin d) → ℝ := fun w => if δ < ‖w‖ then g w else 0 with hFf
  have hsplit : ∀ w : EuclideanSpace ℝ (Fin d),
      (if ε < ‖w‖ then ρ0 * ρx w * hx w ^ 2 else 0) = Fn w + Ff w := by
    intro w
    simp only [hFn, hFf, hg]
    by_cases h1 : ε < ‖w‖
    · by_cases h2 : ‖w‖ ≤ δ
      · have h3 : ¬ δ < ‖w‖ := not_lt.2 h2
        simp [h1, h2, h3]
      · have h3 : δ < ‖w‖ := not_le.1 h2
        simp [h1, h2, h3]
    · have h3 : ¬ δ < ‖w‖ := fun h => h1 (lt_of_le_of_lt hεδ h)
      simp [h1, h3]
  have hnormm : Measurable fun w : EuclideanSpace ℝ (Fin d) => ‖w‖ := measurable_norm
  have hFnm : Measurable Fn :=
    Measurable.ite ((measurableSet_lt measurable_const hnormm).inter
      (measurableSet_le hnormm measurable_const)) hgm measurable_const
  have hFfm : Measurable Ff :=
    Measurable.ite (measurableSet_lt measurable_const hnormm) hgm measurable_const
  have hFnI : IntegrableOn Fn (cube d) := by
    refine integrableOn_cube_bdd hFnm (C := ρmax ^ 2 * B ^ 2 * ε ^ (-(2 * s))) fun w hw => ?_
    simp only [hFn]
    split_ifs with h
    · exact hgbε w hw h.1
    · simp only [abs_zero]; positivity
  have hFfI : IntegrableOn Ff (cube d) := by
    refine integrableOn_cube_bdd hFfm (C := ρmax ^ 2 * B ^ 2 * ε ^ (-(2 * s))) fun w hw => ?_
    simp only [hFf]
    split_ifs with h
    · exact hgbε w hw (lt_of_le_of_lt hεδ h)
    · simp only [abs_zero]; positivity
  -- far part
  haveI : IsFiniteMeasure ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict (cube d)) :=
    ⟨by rw [Measure.restrict_apply_univ, volume_cube]; exact ENNReal.one_lt_top⟩
  have hfar : |∫ w in cube d, Ff w| ≤ ρmax ^ 2 * B ^ 2 * δ ^ (-(2 * s)) := by
    have h := norm_integral_le_of_norm_le_const
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))).restrict (cube d)) (f := Ff)
      (C := ρmax ^ 2 * B ^ 2 * δ ^ (-(2 * s))) ?_
    · have h1 : ((volume : Measure (EuclideanSpace ℝ (Fin d))).restrict (cube d)).real univ = 1 := by
        simp [Measure.real, Measure.restrict_apply_univ, volume_cube]
      rw [h1, mul_one, Real.norm_eq_abs] at h
      exact h
    · refine (ae_restrict_iff' measurableSet_cube).2 (Filter.Eventually.of_forall fun w hw => ?_)
      simp only [hFf, Real.norm_eq_abs]
      split_ifs with h
      · exact hgbδ w hw h
      · simp only [abs_zero]; positivity
  -- model
  set f1 : ℝ → ℝ := (Ioc ε δ).indicator (fun r => r ^ (-(2 * s + 4))) with hf1
  set M : EuclideanSpace ℝ (Fin d) → ℝ :=
    fun w => ρ0 ^ 2 * s ^ 2 * (quadForm H w ^ 2 * f1 ‖w‖) with hM
  have hMeq : ∀ w : EuclideanSpace ℝ (Fin d), M w =
      if ε < ‖w‖ ∧ ‖w‖ ≤ δ then ρ0 ^ 2 * (s ^ 2 * ‖w‖ ^ (-2 * s - 4) * quadForm H w ^ 2) else 0 := by
    intro w
    simp only [hM, hf1]
    by_cases h : ε < ‖w‖ ∧ ‖w‖ ≤ δ
    · rw [if_pos h, indicator_of_mem (show ‖w‖ ∈ Ioc ε δ from h)]
      have : -2 * s - 4 = -(2 * s + 4) := by ring
      rw [this]; ring
    · rw [if_neg h, indicator_of_notMem (show ‖w‖ ∉ Ioc ε δ from h)]; ring
  have hMint : ∫ w, M w = ρ0 ^ 2 * s ^ 2 * (HRS.sphereArea d / (d * (d + 2)) *
          (H.trace ^ 2 + 2 * ∑ i, ∑ j, H i j ^ 2)) * ∫ r in ε..δ, r ^ ((d : ℝ) - 1 - 2 * s) := by
    simp only [hM]
    rw [integral_const_mul, integral_quad_radial hd H hH f1, hf1,
      Ioc_pow_integral (d + 3) (2 * s + 4) hε hεδ]
    have e : ((d + 3 : ℕ) : ℝ) - (2 * s + 4) = (d : ℝ) - 1 - 2 * s := by push_cast; ring
    rw [e]; ring
  -- error bound
  set f2 : ℝ → ℝ := (Ioc ε δ).indicator (fun r => r ^ (-(2 * s - 1))) with hf2
  set bnd : EuclideanSpace ℝ (Fin d) → ℝ := fun w => Kerr * f2 ‖w‖ with hbnd
  have hf2m : Measurable f2 := (measurable_id.pow_const _).indicator measurableSet_Ioc
  have hbndm : Measurable bnd := measurable_const.mul (hf2m.comp hnormm)
  have hbnd0 : ∀ w, 0 ≤ bnd w := by
    intro w
    simp only [hbnd, hf2, indicator]
    split_ifs with h
    · exact mul_nonneg hKerr0 (Real.rpow_nonneg (hε.le.trans h.1.le) _)
    · simp
  have hbndsupp : ∀ w, δ < ‖w‖ → bnd w = 0 := by
    intro w hw
    simp only [hbnd, hf2]
    rw [indicator_of_notMem (show ‖w‖ ∉ Ioc ε δ from fun h => absurd h.2 (not_le.2 hw))]
    simp
  have hbndI : Integrable bnd := by
    obtain ⟨C0, hC0⟩ := (isCompact_Icc (a := ε) (b := δ)).exists_bound_of_continuousOn
      (f := fun r : ℝ => r ^ (-(2 * s - 1)))
      (ContinuousOn.rpow_const continuousOn_id
        (fun x hx => Or.inl (ne_of_gt (lt_of_lt_of_le hε hx.1))))
    refine integrable_of_bdd hbndm (C := Kerr * |C0|) (R := δ) (fun w => ?_) (fun w hw => hbndsupp w hw)
    simp only [hbnd, hf2]
    by_cases h : ‖w‖ ∈ Ioc ε δ
    · rw [indicator_of_mem h, abs_mul, abs_of_nonneg hKerr0]
      have := hC0 ‖w‖ ⟨h.1.le, h.2⟩
      rw [Real.norm_eq_abs] at this
      exact mul_le_mul_of_nonneg_left (this.trans (le_abs_self _)) hKerr0
    · rw [indicator_of_notMem h]; simp; positivity
  have hbndint : ∫ w, bnd w = Kerr * ballConst d * ∫ r in ε..δ, r ^ ((d : ℝ) - 2 * s) := by
    simp only [hbnd]
    rw [integral_const_mul, integral_radial hd f2, hf2, Ioc_pow_integral (d - 1) (2 * s - 1) hε hεδ]
    have e : ((d - 1 : ℕ) : ℝ) - (2 * s - 1) = (d : ℝ) - 2 * s := by
      rw [Nat.cast_sub hd]; push_cast; ring
    rw [e]; ring
  have hnear : ∀ w, |Fn w - M w| ≤ bnd w := by
    intro w
    rw [hMeq w]
    simp only [hFn, hbnd, hf2]
    by_cases h : ε < ‖w‖ ∧ ‖w‖ ≤ δ
    · rw [if_pos h, if_pos h, indicator_of_mem (show ‖w‖ ∈ Ioc ε δ from h)]
      have hw0 : 0 < ‖w‖ := hε.trans h.1
      have hwc : w ∈ cube d := cube_of_norm_le hδ4 h.2
      have key := near_pointwise s ‖w‖ (hx w) (quadForm H w) ρ0 (ρx w) D C1 Lρ ρmax hs0 hw0
        (h.2.trans (hδ4.trans (by norm_num))) hD0
        (quad_le hBH H hBHH w) (hexp w hw0 h.2) hC1 hρ0.1 hρ0.2 (hρ w hwc).1 (hρ w hwc).2
        (hρL w h.2) hLρ
      have e : ‖w‖ ^ (-(2 * s - 1)) = ‖w‖ ^ (1 - 2 * s) := by congr 1; ring
      rw [e]
      simpa only [hg] using key
    · rw [if_neg h, if_neg h, indicator_of_notMem (show ‖w‖ ∉ Ioc ε δ from h)]
      simp
  have hFnE : Integrable Fn := by
    rw [← integrableOn_iff_integrable_of_support_subset (s := cube d)]
    · exact hFnI
    · intro w hw
      by_contra hc
      apply hw
      simp only [hFn]
      rw [if_neg]
      rintro ⟨_, h2⟩
      exact hc (cube_of_norm_le hδ4 h2)
  have hMm : Measurable M :=
    measurable_const.mul (((measurable_quadForm H).pow_const 2).mul
      (((measurable_id.pow_const _).indicator measurableSet_Ioc).comp hnormm))
  have hMI : Integrable M := by
    refine Integrable.mono' (hFnE.norm.add hbndI) hMm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun w => ?_)
    have h1 := hnear w
    rw [Real.norm_eq_abs]
    have : |M w| ≤ |Fn w| + |Fn w - M w| := by
      have := abs_sub_abs_le_abs_sub (Fn w) (Fn w - M w)
      calc |M w| = |Fn w - (Fn w - M w)| := by ring_nf
        _ ≤ |Fn w| + |Fn w - M w| := abs_sub _ _
    simp only [Pi.add_apply, Real.norm_eq_abs]
    linarith
  have hMsupp : ∀ w, w ∉ cube d → M w = 0 := by
    intro w hw
    rw [hMeq w, if_neg]
    rintro ⟨_, h2⟩
    exact hw (cube_of_norm_le hδ4 h2)
  have hbsupp : ∀ w, w ∉ cube d → bnd w = 0 := by
    intro w hw
    apply hbndsupp
    by_contra h
    exact hw (cube_of_norm_le hδ4 (not_lt.1 h))
  have hMcube : ∫ w in cube d, M w = ∫ w, M w :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hMsupp
  have hbcube : ∫ w in cube d, bnd w = ∫ w, bnd w :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hbsupp
  have hnearint : |(∫ w in cube d, Fn w) - ∫ w, M w| ≤ Kerr * ballConst d * ∫ r in ε..δ, r ^ ((d : ℝ) - 2 * s) := by
    rw [← hMcube, ← integral_sub hFnI hMI.integrableOn, ← Real.norm_eq_abs]
    calc ‖∫ w in cube d, (Fn w - M w)‖ ≤ ∫ w in cube d, bnd w :=
          norm_integral_le_of_norm_le hbndI.integrableOn
            (Filter.Eventually.of_forall fun w => by rw [Real.norm_eq_abs]; exact hnear w)
      _ = _ := by rw [hbcube, hbndint]
  have hFsum : (∫ w in cube d, if ε < ‖w‖ then ρ0 * ρx w * hx w ^ 2 else 0) =
      (∫ w in cube d, Fn w) + ∫ w in cube d, Ff w := by
    rw [← integral_add hFnI hFfI]
    exact setIntegral_congr_fun measurableSet_cube fun w _ => hsplit w
  rw [hFsum, ← hMint]
  have : (∫ w in cube d, Fn w) + (∫ w in cube d, Ff w) - ∫ w, M w =
      ((∫ w in cube d, Fn w) - ∫ w, M w) + ∫ w in cube d, Ff w := by ring
  rw [this]
  calc _ ≤ |(∫ w in cube d, Fn w) - ∫ w, M w| + |∫ w in cube d, Ff w| := abs_add_le _ _
    _ ≤ _ := by linarith


end HRS.LocalDivAux
