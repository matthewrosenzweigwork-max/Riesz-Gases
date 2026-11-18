import HRS.MS.MovForceAux5

/-!
# MOV-B2 (3): the split of the force and the pointwise bounds (S6.1, steps 4(a), 5)

Namespace `HRS.MS.MovForce`, helper prefix `movb2_`, output prefix `mv1_`.

For a `C^1` profile `u` with Gaussian amplitude bound `movb2_GA 1 c E u` and `F = movForce d s u`:

* `movb2_force_split`: `F_i = g_loc * ∂_i u + (∂_i g_far) * u` (local part: derivative on the profile; far part:
  derivative on the kernel, by integration by parts);
* `mv1_loc_cb` (step 5): `‖D^k (g_loc * ∂_i u)(x)‖ ≤ ‖g_loc‖_{L¹} sup ‖D^{k+1} u‖`, and the `x`-weighted version;
* `mv1_far_direct` (step 4(a)): `(1+‖x‖)^{s+1} ‖D^k (∂_i g_far * u)(x)‖` is bounded by `C` times a weighted
  `L¹` norm of `D^k u`;
* `mv1_force_deriv_bound`: `‖D^k F(x)‖ + ‖x‖ ‖D^k F(x)‖ ≤ C E` with `C` independent of `u` and `E`.

Statement adjustment relative to the sketch of step 4(a): the derivatives `D^k` are carried by the profile `u` (not
by the kernel), which gives the decay `(1+‖x‖)^{-(s+1)}` for every `k` (the sketch has `-(s+1+k)`); this is all that
the force theorem and `mov_force_tail_thermal` need.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovForce

open HRS.Whole

variable {d : ℕ} {s : ℝ}

lemma movb2_partial_data {c E : ℝ} {u : Euc d → ℝ} (hu : ContDiff ℝ 1 u) (hga : movb2_GA 1 c E u)
    (e : Euc d) :
    Continuous (fun y => fderiv ℝ u y e) ∧
      ∀ y, |fderiv ℝ u y e| ≤ (E * ‖e‖) * Real.exp (-c * ‖y‖ ^ 2) := by
  refine ⟨(hu.continuous_fderiv one_ne_zero).clm_apply continuous_const, fun y => ?_⟩
  have hu1 : ContDiff ℝ ((0 + 1 : ℕ) : WithTop ℕ∞) u := by simpa using hu
  have hw := movb2_GA_partial hu1 (by simpa using hga) e
  have := hw 0 le_rfl y
  rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this

section Split

variable (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
include hd hs0 hsd

/-- **Split of the force.**  `(∇g * u)_i = g_loc * ∂_i u + (∂_i g_far) * u`. -/
theorem movb2_force_split {c E : ℝ} (hc : 0 < c) {u : Euc d → ℝ} (hu : ContDiff ℝ 1 u)
    (hga : movb2_GA 1 c E u) (i : Fin d) (x : Euc d) :
    (movForce d s u x) i =
      movb2_T (movb2_gloc d s) (fun y => fderiv ℝ u y (EuclideanSpace.single i 1)) x +
        movb2_T (movb2_kfar d s i) u x := by
  have hE := movb2_GA_nonneg hga
  obtain ⟨h0, h1⟩ := movb2_GA_01 hga
  obtain ⟨hwc, hw0⟩ := movb2_partial_data hu hga (EuclideanSpace.single i (1 : ℝ))
  have hn : ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖ = 1 := by simp
  rw [hn, mul_one] at hw0
  rw [mv1_force_eq_conv_grad hd hs0 hsd hc hE hu h0 h1 x i, mv1_convFun_eq]
  have hl := movb2_T_integrable hd hs0 hsd (movb2_gloc_ker hd hs0 hsd) hc hE hwc hw0 x
  have hf := movb2_T_integrable hd hs0 hsd (movb2_gfar_ker hd hs0 hsd) hc hE hwc hw0 x
  have hsplit : ∀ z, rieszKernel d s z * fderiv ℝ u (x - z) (EuclideanSpace.single i 1) =
      movb2_gloc d s z * fderiv ℝ u (x - z) (EuclideanSpace.single i 1) +
        movb2_gfar d s z * fderiv ℝ u (x - z) (EuclideanSpace.single i 1) := fun z => by
    rw [← add_mul, movb2_gloc_add_gfar]
  simp_rw [hsplit]
  rw [integral_add hl hf, ← movb2_ibp hd hs0 hsd hc hu hga i x]
  rfl

end Split

/-! ### Pointwise bounds for `κ * w` -/

lemma movb2_r_exp_le {c : ℝ} (hc : 0 < c) {r : ℝ} (hr : 0 ≤ r) :
    r * Real.exp (-c * r ^ 2) ≤ 1 + 1 / c := by
  have hinv : 0 < 1 / c := one_div_pos.2 hc
  have hexp : 1 + c * r ^ 2 ≤ Real.exp (c * r ^ 2) := by linarith [Real.add_one_le_exp (c * r ^ 2)]
  have hr1 : r ≤ (1 + 1 / c) * (1 + c * r ^ 2) := by
    have : (1 + 1 / c) * (1 + c * r ^ 2) = 1 + c * r ^ 2 + 1 / c + r ^ 2 := by field_simp; ring
    rw [this]
    nlinarith [sq_nonneg (r - 1), mul_nonneg hc.le (sq_nonneg r)]
  have h3 : Real.exp (-c * r ^ 2) * (1 + c * r ^ 2) ≤ 1 := by
    have : Real.exp (-c * r ^ 2) * Real.exp (c * r ^ 2) = 1 := by
      rw [← Real.exp_add]; simp
    calc Real.exp (-c * r ^ 2) * (1 + c * r ^ 2) ≤ Real.exp (-c * r ^ 2) * Real.exp (c * r ^ 2) :=
          mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le
      _ = 1 := this
  calc r * Real.exp (-c * r ^ 2) ≤ ((1 + 1 / c) * (1 + c * r ^ 2)) * Real.exp (-c * r ^ 2) :=
        mul_le_mul_of_nonneg_right hr1 (Real.exp_pos _).le
    _ = (1 + 1 / c) * (Real.exp (-c * r ^ 2) * (1 + c * r ^ 2)) := by ring
    _ ≤ (1 + 1 / c) * 1 := mul_le_mul_of_nonneg_left h3 (by linarith)
    _ = 1 + 1 / c := mul_one _

lemma movb2_exp_le_one {c : ℝ} (hc : 0 < c) (r : ℝ) : Real.exp (-c * r ^ 2) ≤ 1 := by
  rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg r]

/-- Bounds for the local part (kernel in `L¹` with first moment). -/
theorem movb2_loc_bound (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {E : ℝ} {w : Euc d → ℝ}, 0 ≤ E →
      (∀ y, |w y| ≤ E * Real.exp (-c * ‖y‖ ^ 2)) → ∀ x : Euc d,
        |movb2_T (movb2_gloc d s) w x| ≤ C * E ∧ ‖x‖ * |movb2_T (movb2_gloc d s) w x| ≤ C * E := by
  obtain ⟨hI0, hI1⟩ := mv1_gloc_integrable hd hs0 hsd
  have hI0' : Integrable (fun z => |movb2_gloc d s z|) volume := hI0.abs
  have hI1' : Integrable (fun z => ‖z‖ * |movb2_gloc d s z|) volume :=
    hI1.norm.congr (Filter.Eventually.of_forall fun z => by simp [norm_mul])
  set L0 : ℝ := ∫ z, |movb2_gloc d s z| with hL0
  set L1 : ℝ := ∫ z, ‖z‖ * |movb2_gloc d s z| with hL1
  have hn0 : 0 ≤ L0 := integral_nonneg fun z => abs_nonneg _
  have hn1 : 0 ≤ L1 := integral_nonneg fun z => mul_nonneg (norm_nonneg _) (abs_nonneg _)
  refine ⟨L0 + L1 + (1 + 1 / c) * L0, by positivity, fun {E w} hE hw x => ?_⟩
  have hc1 : 0 ≤ (1 + 1 / c) := by positivity
  have hpt : ∀ z, |movb2_gloc d s z * w (x - z)| ≤ |movb2_gloc d s z| * E := fun z => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((hw _).trans (mul_le_of_le_one_right hE (movb2_exp_le_one hc _)))
      (abs_nonneg _)
  have h1 : |movb2_T (movb2_gloc d s) w x| ≤ L0 * E := by
    have := norm_integral_le_of_norm_le (hI0'.mul_const E)
      (Filter.Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hpt z)
      (f := fun z => movb2_gloc d s z * w (x - z))
    rw [integral_mul_const] at this
    simpa [movb2_T, Real.norm_eq_abs] using this
  refine ⟨h1.trans (by nlinarith [mul_nonneg (add_nonneg hn1 (mul_nonneg hc1 hn0)) hE]), ?_⟩
  have hΦ : Integrable (fun z => ‖z‖ * |movb2_gloc d s z| * E + (1 + 1 / c) * |movb2_gloc d s z| * E)
      volume := (hI1'.mul_const E).add ((hI0'.const_mul (1 + 1 / c)).mul_const E)
  have h2 : ‖x‖ * |movb2_T (movb2_gloc d s) w x| ≤ L1 * E + (1 + 1 / c) * L0 * E := by
    have hb : ∀ z, ‖(‖x‖ * (movb2_gloc d s z * w (x - z)))‖ ≤
        ‖z‖ * |movb2_gloc d s z| * E + (1 + 1 / c) * |movb2_gloc d s z| * E := fun z => by
      rw [norm_mul, norm_norm, Real.norm_eq_abs, abs_mul]
      have hxz : ‖x‖ ≤ ‖z‖ + ‖x - z‖ := by
        calc ‖x‖ = ‖z + (x - z)‖ := by simp
          _ ≤ _ := norm_add_le _ _
      have hw1 := hw (x - z)
      have hr := movb2_r_exp_le hc (norm_nonneg (x - z))
      have hexp1 := movb2_exp_le_one hc ‖x - z‖
      have hA : 0 ≤ |movb2_gloc d s z| := abs_nonneg _
      have hwz : |w (x - z)| ≤ E * Real.exp (-c * ‖x - z‖ ^ 2) := hw1
      calc ‖x‖ * (|movb2_gloc d s z| * |w (x - z)|)
          ≤ (‖z‖ + ‖x - z‖) * (|movb2_gloc d s z| * (E * Real.exp (-c * ‖x - z‖ ^ 2))) := by
            apply mul_le_mul hxz (mul_le_mul_of_nonneg_left hwz hA) (by positivity) (by positivity)
        _ = ‖z‖ * |movb2_gloc d s z| * (E * Real.exp (-c * ‖x - z‖ ^ 2)) +
              |movb2_gloc d s z| * E * (‖x - z‖ * Real.exp (-c * ‖x - z‖ ^ 2)) := by ring
        _ ≤ ‖z‖ * |movb2_gloc d s z| * (E * 1) + |movb2_gloc d s z| * E * (1 + 1 / c) := by
            gcongr
        _ = _ := by ring
    have := norm_integral_le_of_norm_le hΦ (Filter.Eventually.of_forall hb)
      (f := fun z => ‖x‖ * (movb2_gloc d s z * w (x - z)))
    rw [integral_const_mul, integral_add (hI1'.mul_const E) ((hI0'.const_mul (1 + 1 / c)).mul_const E),
      integral_mul_const, integral_mul_const, integral_const_mul, Real.norm_eq_abs] at this
    have h3 : |‖x‖ * movb2_T (movb2_gloc d s) w x| = ‖x‖ * |movb2_T (movb2_gloc d s) w x| := by
      rw [abs_mul, abs_norm]
    rw [← h3]
    simpa [movb2_T] using this
  refine h2.trans ?_
  nlinarith [mul_nonneg hn0 hE, mul_nonneg hn1 hE, mul_nonneg hc1 (mul_nonneg hn0 hE)]

/-- The weighted Gaussian integral `∫ (1+‖y‖) e^{-c‖y‖²}`. -/
def movb2_A1 (d : ℕ) (c : ℝ) : ℝ := ∫ y : Euc d, (1 + ‖y‖) * Real.exp (-c * ‖y‖ ^ 2)

lemma movb2_A1_integrable (hd : 1 ≤ d) {c : ℝ} (hc : 0 < c) :
    Integrable (fun y : Euc d => (1 + ‖y‖) * Real.exp (-c * ‖y‖ ^ 2)) volume := by
  have h0 := movtr_integrable_rpow_gauss (d := d) hd (α := 0) (c := c) (by
    have : (0:ℝ) ≤ d := Nat.cast_nonneg d
    have : (1:ℝ) ≤ d := by exact_mod_cast hd
    linarith) hc
  have h1 := movtr_integrable_rpow_gauss (d := d) hd (α := 1) (c := c) (by
    have : (0:ℝ) ≤ d := Nat.cast_nonneg d
    linarith) hc
  simp only [Real.rpow_one, Real.rpow_zero, one_mul] at h0 h1
  refine (h0.add h1).congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [Pi.add_apply]; ring

lemma movb2_A1_nonneg {c : ℝ} (hc : 0 < c) : 0 ≤ movb2_A1 d c :=
  integral_nonneg fun y => by positivity

/-- Bounds for a kernel with `|κ z| (1 + ‖z‖) ≤ K` (far part). -/
theorem movb2_far_bound (hd : 1 ≤ d) {c K : ℝ} (hc : 0 < c) {κ : Euc d → ℝ}
    (hκ : ∀ z, |κ z| * (1 + ‖z‖) ≤ K) {E : ℝ} {w : Euc d → ℝ} (hE : 0 ≤ E)
    (hw : ∀ y, |w y| ≤ E * Real.exp (-c * ‖y‖ ^ 2)) (x : Euc d) :
    |movb2_T κ w x| ≤ K * movb2_A1 d c * E ∧ ‖x‖ * |movb2_T κ w x| ≤ K * movb2_A1 d c * E := by
  have hK : 0 ≤ K := (mul_nonneg (abs_nonneg _) (by positivity)).trans (hκ 0)
  set G : Euc d → ℝ := fun y => (1 + ‖y‖) * Real.exp (-c * ‖y‖ ^ 2) with hG
  have hGi : Integrable G volume := movb2_A1_integrable hd hc
  have hΦ : Integrable (fun z => K * E * G (x - z)) volume := (hGi.comp_sub_left x).const_mul (K * E)
  have hint : ∫ z, K * E * G (x - z) = K * movb2_A1 d c * E := by
    rw [integral_const_mul, integral_sub_left_eq_self (fun y => G y) volume x]
    simp only [movb2_A1, hG]; ring
  have hG1 : ∀ y, Real.exp (-c * ‖y‖ ^ 2) ≤ G y := fun y => by
    simp only [hG]
    exact le_mul_of_one_le_left (Real.exp_pos _).le (by linarith [norm_nonneg y])
  have hG0 : ∀ y, 0 ≤ G y := fun y => by positivity
  have hk1 : ∀ z, |κ z| ≤ K := fun z =>
    ((le_mul_of_one_le_right (abs_nonneg _) (by linarith [norm_nonneg z])).trans (hκ z))
  constructor
  · have hb : ∀ z, ‖κ z * w (x - z)‖ ≤ K * E * G (x - z) := fun z => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      calc |κ z| * |w (x - z)| ≤ K * (E * G (x - z)) :=
            mul_le_mul (hk1 z) ((hw _).trans (mul_le_mul_of_nonneg_left (hG1 _) hE)) (abs_nonneg _) hK
        _ = _ := by ring
    have := norm_integral_le_of_norm_le hΦ (Filter.Eventually.of_forall hb)
      (f := fun z => κ z * w (x - z))
    rw [hint] at this
    simpa [movb2_T, Real.norm_eq_abs] using this
  · have hb : ∀ z, ‖‖x‖ * (κ z * w (x - z))‖ ≤ K * E * G (x - z) := fun z => by
      rw [norm_mul, norm_norm, Real.norm_eq_abs, abs_mul]
      have hxz : ‖x‖ ≤ (1 + ‖z‖) * (1 + ‖x - z‖) := by
        have : ‖x‖ ≤ ‖z‖ + ‖x - z‖ := by
          calc ‖x‖ = ‖z + (x - z)‖ := by simp
            _ ≤ _ := norm_add_le _ _
        nlinarith [norm_nonneg z, norm_nonneg (x - z), mul_nonneg (norm_nonneg z) (norm_nonneg (x - z))]
      have hwz := hw (x - z)
      calc ‖x‖ * (|κ z| * |w (x - z)|)
          ≤ ((1 + ‖z‖) * (1 + ‖x - z‖)) * (|κ z| * (E * Real.exp (-c * ‖x - z‖ ^ 2))) :=
            mul_le_mul hxz (mul_le_mul_of_nonneg_left hwz (abs_nonneg _)) (by positivity) (by positivity)
        _ = (|κ z| * (1 + ‖z‖)) * (E * G (x - z)) := by simp only [hG]; ring
        _ ≤ K * (E * G (x - z)) :=
            mul_le_mul_of_nonneg_right (hκ z) (mul_nonneg hE (hG0 _))
        _ = _ := by ring
    have := norm_integral_le_of_norm_le hΦ (Filter.Eventually.of_forall hb)
      (f := fun z => ‖x‖ * (κ z * w (x - z)))
    rw [hint, integral_const_mul] at this
    have h3 : |‖x‖ * movb2_T κ w x| = ‖x‖ * |movb2_T κ w x| := by rw [abs_mul, abs_norm]
    rw [← h3]
    simpa [movb2_T, Real.norm_eq_abs] using this

section Deriv

variable (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
include hd hs0 hsd

/-- **Derivative bounds for the components of the force** (steps 4(a), 5, combined). -/
theorem movb2_forceComp {c : ℝ} (hc : 0 < c) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {E : ℝ} {u : Euc d → ℝ}, ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) u →
      movb2_GA (k + 1) c E u → ∀ i : Fin d,
        ContDiff ℝ (k : WithTop ℕ∞) (fun y => (movForce d s u y) i) ∧
        ∀ x : Euc d, ‖iteratedFDeriv ℝ k (fun y => (movForce d s u y) i) x‖ ≤ C * E ∧
          ‖x‖ * ‖iteratedFDeriv ℝ k (fun y => (movForce d s u y) i) x‖ ≤ C * E := by
  obtain ⟨Cl, hCl0, hCl⟩ := movb2_loc_bound hd hs0 hsd hc
  obtain ⟨K, hK0, hK⟩ := movb2_kfar_bound (d := d) (s := s) hs0
  refine ⟨Cl + K * movb2_A1 d c, add_nonneg hCl0 (mul_nonneg hK0 (movb2_A1_nonneg hc)),
    fun {E u} hu hga i => ?_⟩
  have hE := movb2_GA_nonneg hga
  have hk1 : k ≤ k + 1 := Nat.le_succ k
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by exact_mod_cast Nat.le_add_left 1 k)
  have hga1 : movb2_GA 1 c E u := movb2_GA_mono (by omega) hga
  set e : Euc d := EuclideanSpace.single i (1 : ℝ) with he
  have hen : ‖e‖ = 1 := by simp [he]
  have hF : (fun y => (movForce d s u y) i) = fun y =>
      movb2_T (movb2_gloc d s) (fun y => fderiv ℝ u y e) y + movb2_T (movb2_kfar d s i) u y :=
    funext fun y => movb2_force_split hd hs0 hsd hc hu1 hga1 i y
  have hwi : ContDiff ℝ (k : WithTop ℕ∞) (fun y => fderiv ℝ u y e) := movb2_partial_contDiff hu e
  have hgai : movb2_GA k c (E * ‖e‖) (fun y => fderiv ℝ u y e) := movb2_GA_partial hu hga e
  have hu0 : ContDiff ℝ (k : WithTop ℕ∞) u := hu.of_le (by exact_mod_cast hk1)
  have hga0 : movb2_GA k c E u := movb2_GA_mono hk1 hga
  have hker1 := movb2_gloc_ker hd hs0 hsd
  have hker2 := movb2_kfar_ker (d := d) (s := s) hs0 i
  have hS1 := movb2_T_contDiff hd hs0 hsd hker1 hc k hwi hgai
  have hS2 := movb2_T_contDiff hd hs0 hsd hker2 hc k hu0 hga0
  refine ⟨by rw [hF]; exact hS1.add hS2, fun x => ?_⟩
  have hit : iteratedFDeriv ℝ k (fun y => (movForce d s u y) i) x =
      iteratedFDeriv ℝ k (movb2_T (movb2_gloc d s) (fun y => fderiv ℝ u y e)) x +
        iteratedFDeriv ℝ k (movb2_T (movb2_kfar d s i) u) x := by
    rw [hF]; exact iteratedFDeriv_add_apply hS1.contDiffAt hS2.contDiffAt
  have hmain : ∀ m : Fin k → Euc d,
      |iteratedFDeriv ℝ k (fun y => (movForce d s u y) i) x m| ≤
        ((Cl + K * movb2_A1 d c) * E) * ∏ j, ‖m j‖ ∧
      ‖x‖ * |iteratedFDeriv ℝ k (fun y => (movForce d s u y) i) x m| ≤
        ((Cl + K * movb2_A1 d c) * E) * ∏ j, ‖m j‖ := by
    intro m
    set P : ℝ := ∏ j, ‖m j‖ with hP
    have hP0 : 0 ≤ P := Finset.prod_nonneg fun j _ => norm_nonneg _
    have hw1 : ∀ y, |iteratedFDeriv ℝ k (fun y => fderiv ℝ u y e) y m| ≤
        (E * P) * Real.exp (-c * ‖y‖ ^ 2) := fun y => by
      have h1 := (iteratedFDeriv ℝ k (fun y => fderiv ℝ u y e) y).le_opNorm m
      have h2 := hgai k le_rfl y
      rw [hen, mul_one] at h2
      rw [Real.norm_eq_abs] at h1
      calc _ ≤ ‖iteratedFDeriv ℝ k (fun y => fderiv ℝ u y e) y‖ * P := h1
        _ ≤ (E * Real.exp (-c * ‖y‖ ^ 2)) * P := mul_le_mul_of_nonneg_right h2 hP0
        _ = _ := by ring
    have hw2 : ∀ y, |iteratedFDeriv ℝ k u y m| ≤ (E * P) * Real.exp (-c * ‖y‖ ^ 2) := fun y => by
      have h1 := (iteratedFDeriv ℝ k u y).le_opNorm m
      have h2 := hga0 k le_rfl y
      rw [Real.norm_eq_abs] at h1
      calc _ ≤ ‖iteratedFDeriv ℝ k u y‖ * P := h1
        _ ≤ (E * Real.exp (-c * ‖y‖ ^ 2)) * P := mul_le_mul_of_nonneg_right h2 hP0
        _ = _ := by ring
    have hEP : 0 ≤ E * P := mul_nonneg hE hP0
    obtain ⟨a1, a2⟩ := hCl hEP hw1 x
    obtain ⟨b1, b2⟩ := movb2_far_bound hd hc (hK i) hEP hw2 x
    have hsum : iteratedFDeriv ℝ k (fun y => (movForce d s u y) i) x m =
        movb2_T (movb2_gloc d s) (fun y => iteratedFDeriv ℝ k (fun y => fderiv ℝ u y e) y m) x +
          movb2_T (movb2_kfar d s i) (fun y => iteratedFDeriv ℝ k u y m) x := by
      rw [hit, ContinuousMultilinearMap.add_apply,
        movb2_T_iter hd hs0 hsd hker1 hc k hwi hgai x m, movb2_T_iter hd hs0 hsd hker2 hc k hu0 hga0 x m]
    rw [hsum]
    set A := movb2_T (movb2_gloc d s) (fun y => iteratedFDeriv ℝ k (fun y => fderiv ℝ u y e) y m) x
    set B := movb2_T (movb2_kfar d s i) (fun y => iteratedFDeriv ℝ k u y m) x
    have hx0 : 0 ≤ ‖x‖ := norm_nonneg x
    constructor
    · calc |A + B| ≤ |A| + |B| := abs_add_le _ _
        _ ≤ Cl * (E * P) + K * movb2_A1 d c * (E * P) := add_le_add a1 b1
        _ = _ := by ring
    · calc ‖x‖ * |A + B| ≤ ‖x‖ * (|A| + |B|) := mul_le_mul_of_nonneg_left (abs_add_le _ _) hx0
        _ = ‖x‖ * |A| + ‖x‖ * |B| := by ring
        _ ≤ Cl * (E * P) + K * movb2_A1 d c * (E * P) := add_le_add a2 b2
        _ = _ := by ring
  have hM0 : 0 ≤ (Cl + K * movb2_A1 d c) * E :=
    mul_nonneg (add_nonneg hCl0 (mul_nonneg hK0 (movb2_A1_nonneg hc))) hE
  constructor
  · refine ContinuousMultilinearMap.opNorm_le_bound hM0 fun m => ?_
    rw [Real.norm_eq_abs]; exact (hmain m).1
  · have := ContinuousMultilinearMap.opNorm_le_bound (f := ‖x‖ • iteratedFDeriv ℝ k
      (fun y => (movForce d s u y) i) x) hM0 fun m => by
      rw [ContinuousMultilinearMap.smul_apply, norm_smul, norm_norm, Real.norm_eq_abs]
      exact (hmain m).2
    rwa [norm_smul, norm_norm] at this

omit hd hs0 hsd in
lemma movb2_vec_eq_sum (v : Euc d) : v = ∑ i, v i • (EuclideanSpace.single i (1 : ℝ) : Euc d) := by
  have := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr v
  simpa using this.symm

/-- **Derivative bounds for the force** (vector form): for `u ∈ C^{k+1}` with Gaussian amplitude `E` up to order
`k+1`, `F = ∇g * u` is `C^k` and `‖D^k F(x)‖ + ‖x‖ ‖D^k F(x)‖ ≤ 2 C E`, `C` independent of `u, E`. -/
theorem mv1_force_deriv_bound {c : ℝ} (hc : 0 < c) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {E : ℝ} {u : Euc d → ℝ}, ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) u →
      movb2_GA (k + 1) c E u →
        ContDiff ℝ (k : WithTop ℕ∞) (movForce d s u) ∧ ∀ x : Euc d,
          ‖iteratedFDeriv ℝ k (movForce d s u) x‖ ≤ C * E ∧
            ‖x‖ * ‖iteratedFDeriv ℝ k (movForce d s u) x‖ ≤ C * E := by
  obtain ⟨C0, hC0, hC⟩ := movb2_forceComp hd hs0 hsd hc k
  refine ⟨d * C0, mul_nonneg (Nat.cast_nonneg d) hC0, fun {E u} hu hga => ?_⟩
  have hE := movb2_GA_nonneg hga
  have hFeq : movForce d s u = fun y => ∑ i, (movForce d s u y) i • (EuclideanSpace.single i (1 : ℝ) : Euc d) :=
    funext fun y => movb2_vec_eq_sum _
  have hcomp := fun i => hC hu hga i
  refine ⟨contDiff_euclidean.2 fun i => (hcomp i).1, fun x => ?_⟩
  have hnorm : ‖iteratedFDeriv ℝ k (movForce d s u) x‖ ≤
      ∑ i : Fin d, ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖ *
        ‖iteratedFDeriv ℝ k (fun y => (movForce d s u y) i) x‖ := by
    conv_lhs => rw [hFeq]
    exact movb2_norm_iter_sum (fun i => (EuclideanSpace.single i (1 : ℝ) : Euc d))
      (f := fun i y => (movForce d s u y) i) (N := (k : WithTop ℕ∞)) (x := x)
      (fun i => (hcomp i).1.contDiffAt) k le_rfl
  have hn1 : ∀ i : Fin d, ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖ = 1 := fun i => by simp
  simp only [hn1, one_mul] at hnorm
  constructor
  · calc _ ≤ ∑ i : Fin d, ‖iteratedFDeriv ℝ k (fun y => (movForce d s u y) i) x‖ := hnorm
      _ ≤ ∑ _i : Fin d, C0 * E := Finset.sum_le_sum fun i _ => ((hcomp i).2 x).1
      _ = d * C0 * E := by simp; ring
  · calc ‖x‖ * ‖iteratedFDeriv ℝ k (movForce d s u) x‖
        ≤ ‖x‖ * ∑ i : Fin d, ‖iteratedFDeriv ℝ k (fun y => (movForce d s u y) i) x‖ :=
          mul_le_mul_of_nonneg_left hnorm (norm_nonneg _)
      _ = ∑ i : Fin d, ‖x‖ * ‖iteratedFDeriv ℝ k (fun y => (movForce d s u y) i) x‖ := Finset.mul_sum _ _ _
      _ ≤ ∑ _i : Fin d, C0 * E := Finset.sum_le_sum fun i _ => ((hcomp i).2 x).2
      _ = d * C0 * E := by simp; ring

omit hd hs0 hsd in
/-- `‖D^k(∂_e w)‖ ≤ ‖e‖ ‖D^{k+1} w‖`. -/
lemma movb2_norm_iter_partial {k : ℕ} {w : Euc d → ℝ} (hw : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) w)
    (e : Euc d) (y : Euc d) :
    ‖iteratedFDeriv ℝ k (fun z => fderiv ℝ w z e) y‖ ≤ ‖e‖ * ‖iteratedFDeriv ℝ (k + 1) w y‖ := by
  have hfd : ContDiff ℝ (k : WithTop ℕ∞) (fderiv ℝ w) := hw.fderiv_right (m := k) (by rw [Nat.cast_succ])
  have h1 := norm_iteratedFDeriv_clm_apply_const (𝕜 := ℝ) (f := fderiv ℝ w) (c := e) (x := y) (n := k)
    (N := (k : WithTop ℕ∞)) hfd.contDiffAt le_rfl
  rwa [norm_iteratedFDeriv_fderiv] at h1

/-- **`mv1_loc_cb`** (step 5): the local part of the `C_b^k` norm of `∂_i (g * u)` is controlled by
`‖g_loc‖_{L¹}` times the sup of `D^{k+1} u` (no singular integral estimate is needed):
`‖D^k (g_loc * ∂_i u)(x)‖ ≤ (∫ |g_loc|) S` whenever `‖D^{k+1}u‖ ≤ S`. -/
theorem mv1_loc_cb {c E : ℝ} (hc : 0 < c) (k : ℕ) {u : Euc d → ℝ}
    (hu : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) u) (hga : movb2_GA (k + 1) c E u) {S : ℝ} (hS0 : 0 ≤ S)
    (hS : ∀ y, ‖iteratedFDeriv ℝ (k + 1) u y‖ ≤ S) (i : Fin d) (x : Euc d) :
    ‖iteratedFDeriv ℝ k (movb2_T (movb2_gloc d s)
        (fun y => fderiv ℝ u y (EuclideanSpace.single i 1))) x‖ ≤ (∫ z, |movb2_gloc d s z|) * S := by
  set e : Euc d := EuclideanSpace.single i (1 : ℝ) with he
  have hen : ‖e‖ = 1 := by simp [he]
  have hwi : ContDiff ℝ (k : WithTop ℕ∞) (fun y => fderiv ℝ u y e) := movb2_partial_contDiff hu e
  have hgai : movb2_GA k c (E * ‖e‖) (fun y => fderiv ℝ u y e) := movb2_GA_partial hu hga e
  have hI0 : Integrable (fun z => |movb2_gloc d s z|) volume := (mv1_gloc_integrable hd hs0 hsd).1.abs
  have hL0 : 0 ≤ ∫ z, |movb2_gloc d s z| := integral_nonneg fun z => abs_nonneg _
  refine ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg hL0 hS0) fun m => ?_
  set P : ℝ := ∏ j, ‖m j‖ with hP
  have hP0 : 0 ≤ P := Finset.prod_nonneg fun j _ => norm_nonneg _
  rw [movb2_T_iter hd hs0 hsd (movb2_gloc_ker hd hs0 hsd) hc k hwi hgai x m]
  have hw : ∀ y, |iteratedFDeriv ℝ k (fun y => fderiv ℝ u y e) y m| ≤ S * P := fun y => by
    have h1 := (iteratedFDeriv ℝ k (fun y => fderiv ℝ u y e) y).le_opNorm m
    rw [Real.norm_eq_abs] at h1
    have h2 := movb2_norm_iter_partial hu e y
    rw [hen, one_mul] at h2
    calc _ ≤ ‖iteratedFDeriv ℝ k (fun y => fderiv ℝ u y e) y‖ * P := h1
      _ ≤ S * P := mul_le_mul_of_nonneg_right (h2.trans (hS y)) hP0
  have hb : ∀ z, ‖movb2_gloc d s z * iteratedFDeriv ℝ k (fun y => fderiv ℝ u y e) (x - z) m‖ ≤
      |movb2_gloc d s z| * (S * P) := fun z => by
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hw _) (abs_nonneg _)
  have := norm_integral_le_of_norm_le (hI0.mul_const (S * P)) (Filter.Eventually.of_forall hb)
  rw [integral_mul_const] at this
  rw [Real.norm_eq_abs]
  simpa [movb2_T, Real.norm_eq_abs, mul_assoc, mul_comm, mul_left_comm] using this

/-- **`mv1_far_direct`** (step 4(a)): the far part of the force decays like `(1+‖x‖)^{-(s+1)}`, with a weighted
`L¹` norm of the profile (valid for `s = 0`; the weight exponent is `s+1`, the derivatives `D^k` fall on the
profile):
`(1+‖x‖)^{s+1} ‖D^k (∂_i g_far * u)(x)‖ ≤ C ∫ (1+‖y‖)^{s+1} ‖D^k u(y)‖ dy`. -/
theorem mv1_far_direct :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : Fin d) {c E : ℝ}, 0 < c → ∀ (k : ℕ) {u : Euc d → ℝ},
      ContDiff ℝ (k : WithTop ℕ∞) u → movb2_GA k c E u →
      Integrable (fun y => (1 + ‖y‖) ^ (s + 1) * ‖iteratedFDeriv ℝ k u y‖) volume →
      ∀ x : Euc d, (1 + ‖x‖) ^ (s + 1) *
          ‖iteratedFDeriv ℝ k (movb2_T (movb2_kfar d s i) u) x‖ ≤
        C * ∫ y, (1 + ‖y‖) ^ (s + 1) * ‖iteratedFDeriv ℝ k u y‖ := by
  obtain ⟨C1, hC10, hC1⟩ := mv1_gfar_bound (d := d) hs0 1 le_rfl
  refine ⟨C1, hC10, fun i {c E} hc k {u} hu hga hint x => ?_⟩
  set p : ℝ := s + 1 with hp
  have hp0 : 0 ≤ p := by rw [hp]; linarith
  set W : Euc d → ℝ := fun y => (1 + ‖y‖) ^ p * ‖iteratedFDeriv ℝ k u y‖ with hW
  have hI : 0 ≤ ∫ y, W y := integral_nonneg fun y => by positivity
  have hker := movb2_kfar_ker (d := d) (s := s) hs0 i
  have hkb : ∀ z, |movb2_kfar d s i z| ≤ C1 * (1 + ‖z‖) ^ (-p) := fun z => by
    have h1 : |movb2_kfar d s i z| ≤ ‖iteratedFDeriv ℝ 1 (movb2_gfar d s) z‖ := by
      rw [norm_iteratedFDeriv_one]
      have := (fderiv ℝ (movb2_gfar d s) z).le_opNorm (EuclideanSpace.single i (1 : ℝ))
      simpa [movb2_kfar, Real.norm_eq_abs] using this
    have h2 := hC1 z
    have : (-s - ((1 : ℕ) : ℝ)) = -p := by rw [hp]; push_cast; ring
    rw [this] at h2
    exact h1.trans h2
  have hweight : ∀ z, (1 + ‖x‖) ^ p ≤ (1 + ‖z‖) ^ p * (1 + ‖x - z‖) ^ p := fun z => by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    refine Real.rpow_le_rpow (by positivity) ?_ hp0
    have : ‖x‖ ≤ ‖z‖ + ‖x - z‖ := by
      calc ‖x‖ = ‖z + (x - z)‖ := by simp
        _ ≤ _ := norm_add_le _ _
    nlinarith [norm_nonneg z, norm_nonneg (x - z), mul_nonneg (norm_nonneg z) (norm_nonneg (x - z))]
  have hM0 : 0 ≤ C1 * ∫ y, W y := mul_nonneg hC10 hI
  have key : ‖(1 + ‖x‖) ^ p • iteratedFDeriv ℝ k (movb2_T (movb2_kfar d s i) u) x‖ ≤
      C1 * ∫ y, W y := by
    refine ContinuousMultilinearMap.opNorm_le_bound hM0 fun m => ?_
    set P : ℝ := ∏ j, ‖m j‖ with hP
    have hP0 : 0 ≤ P := Finset.prod_nonneg fun j _ => norm_nonneg _
    rw [ContinuousMultilinearMap.smul_apply, movb2_T_iter hd hs0 hsd hker hc k hu hga x m]
    have hb : ∀ z, ‖(1 + ‖x‖) ^ p • (movb2_kfar d s i z * iteratedFDeriv ℝ k u (x - z) m)‖ ≤
        C1 * P * W (x - z) := fun z => by
      rw [norm_smul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 + ‖x‖) ^ p)]
      have h1 : |iteratedFDeriv ℝ k u (x - z) m| ≤ ‖iteratedFDeriv ℝ k u (x - z)‖ * P := by
        have := (iteratedFDeriv ℝ k u (x - z)).le_opNorm m
        rwa [Real.norm_eq_abs] at this
      have hz : (1 + ‖z‖) ^ p * (1 + ‖z‖) ^ (-p) = 1 := by
        rw [← Real.rpow_add (by positivity)]; simp
      calc (1 + ‖x‖) ^ p * (|movb2_kfar d s i z| * |iteratedFDeriv ℝ k u (x - z) m|)
          ≤ ((1 + ‖z‖) ^ p * (1 + ‖x - z‖) ^ p) *
              ((C1 * (1 + ‖z‖) ^ (-p)) * (‖iteratedFDeriv ℝ k u (x - z)‖ * P)) :=
            mul_le_mul (hweight z) (mul_le_mul (hkb z) h1 (abs_nonneg _) (by positivity))
              (by positivity) (by positivity)
        _ = C1 * P * W (x - z) := by
            simp only [hW]
            have : (1 + ‖z‖) ^ p * (1 + ‖z‖) ^ (-p) = 1 := hz
            calc _ = ((1 + ‖z‖) ^ p * (1 + ‖z‖) ^ (-p)) * (C1 * P *
                  ((1 + ‖x - z‖) ^ p * ‖iteratedFDeriv ℝ k u (x - z)‖)) := by ring
              _ = _ := by rw [this, one_mul]
    have hΦ : Integrable (fun z => C1 * P * W (x - z)) volume :=
      ((hint.comp_sub_left x).const_mul (C1 * P))
    have h3 : movb2_T (movb2_kfar d s i) (fun y => iteratedFDeriv ℝ k u y m) x =
        ∫ z, movb2_kfar d s i z * iteratedFDeriv ℝ k u (x - z) m := rfl
    rw [h3]
    calc ‖(1 + ‖x‖) ^ p • ∫ z, movb2_kfar d s i z * iteratedFDeriv ℝ k u (x - z) m‖
        = ‖∫ z, (1 + ‖x‖) ^ p • (movb2_kfar d s i z * iteratedFDeriv ℝ k u (x - z) m)‖ := by
          rw [integral_smul]
      _ ≤ ∫ z, C1 * P * W (x - z) :=
          norm_integral_le_of_norm_le hΦ (Filter.Eventually.of_forall hb)
      _ = C1 * P * ∫ y, W y := by
          rw [integral_const_mul, integral_sub_left_eq_self (fun y => W y) volume x]
      _ = (C1 * ∫ y, W y) * P := by ring
  rwa [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ (1 + ‖x‖) ^ p)] at key

end Deriv

end HRS.MS.MovForce

end
