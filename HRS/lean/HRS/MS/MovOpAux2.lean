import HRS.MS.MovOpAux1

/-!
# MOV-C1 (2): the far field of `P`, pairing form (S6.1, step 4(b))

Namespace `HRS.MS.MovC1`, helper prefix `movc1_`.  Infrastructure for S6.1; not manuscript rows.

For `κ` with all derivatives bounded (`MovcB κ`), `ω` of Gaussian class (`MovcG ω`) and a Schwartz function `v`,
the far convolution `Θ(x) = ∫ κ(z) ω(x-z) v(x-z) dz` (`movb2_T κ (ω v)`) satisfies, for **every real** `r`,
* `movc1_far0`: `|Θ(x)| ≤ C A ‖v‖_{Σ^r}` uniformly in `x`, `A` bounding the derivatives of `κ` up to order `⌈|r|⌉`
  (`Θ(x) = ⟨v, ω κ(x-·)⟩`, `mo_dual_le`, and `mo_mult_cb` for the `C_b^N` multiplier `κ(x-·)` acting on `ω ∈ Σ^{-r}`);
* `movc1_farK`: the same for the coordinate-iterated derivatives of `Θ` up to order `K` (`mova3b2_Q`), by
  integration by parts onto the kernel (`movc1_ibp`, `movc1_Dj_T`: `∂_j (κ * w) = (∂_j κ) * w`);
* `movc1_T_tg`: `Θ` has temperate growth (all derivatives bounded);
* `movc1_far_term`: `‖Θ ψ'‖_{Σ^σ} ≤ C ‖v‖_{Σ^r}` for Gaussian `ψ'` (B3, `mo_mult_cb`), all real `r, σ`;
* kernels: `MovcK κ` (derivatives bounded with an extra factor `(1+‖z‖)⁻¹`) holds for `∂_i g_far`
  (`movc1_kfar_K`, from `mv1_gfar_bound`), is stable under `∂_j` and gives `MovcB` for `z_i κ`.

Statement adjustment relative to the plan: the weighted factor `‖x‖` of 4(b) is not proved as a separate bound; it
is absorbed by the identity `x_i (κ*h) = (z_i κ)*h + κ*(y_i h)` (`movc1_xT`), both terms being of the same type.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovC1

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.Mov0 HRS.MS.MovForce

variable {d : ℕ}

/-! ### Kernels with bounded derivatives -/

/-- `κ` is smooth with all derivatives bounded. -/
def MovcB (κ : Euc d → ℝ) : Prop :=
  ContDiff ℝ ∞ κ ∧ ∀ k : ℕ, ∃ A : ℝ, ∀ z : Euc d, ‖iteratedFDeriv ℝ k κ z‖ ≤ A

/-- Quantitative form: derivatives up to order `N` are bounded by `A`. -/
def MovcBd (N : ℕ) (A : ℝ) (κ : Euc d → ℝ) : Prop :=
  ∀ k ≤ N, ∀ z : Euc d, ‖iteratedFDeriv ℝ k κ z‖ ≤ A

lemma movc1_Bd_Dj {N : ℕ} {A : ℝ} {κ : Euc d → ℝ} (hκ : ContDiff ℝ ∞ κ) (h : MovcBd (N + 1) A κ) (j : Fin d) :
    MovcBd N A (mova3b1_Dj j κ) := by
  intro k hk z
  have h1 := movb2_norm_iter_partial (hκ.of_le (by exact_mod_cast le_top) : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) κ)
    (EuclideanSpace.single j (1 : ℝ)) z
  have h2 : ‖(EuclideanSpace.single j (1 : ℝ) : Euc d)‖ = 1 := by simp
  rw [h2, one_mul] at h1
  exact h1.trans (h (k + 1) (by omega) z)

lemma movc1_B_Dj {κ : Euc d → ℝ} (hκ : MovcB κ) (j : Fin d) : MovcB (mova3b1_Dj j κ) := by
  refine ⟨mova3b2_contDiff_Dj j hκ.1, fun k => ?_⟩
  obtain ⟨A, hA⟩ := hκ.2 (k + 1)
  refine ⟨A, fun z => ?_⟩
  have h1 := movb2_norm_iter_partial (hκ.1.of_le (by exact_mod_cast le_top) : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) κ)
    (EuclideanSpace.single j (1 : ℝ)) z
  have h2 : ‖(EuclideanSpace.single j (1 : ℝ) : Euc d)‖ = 1 := by simp
  rw [h2, one_mul] at h1
  exact h1.trans (hA z)

lemma movc1_Bd_mono {N N' : ℕ} {A : ℝ} {κ : Euc d → ℝ} (h : MovcBd N' A κ) (hN : N ≤ N') : MovcBd N A κ :=
  fun k hk z => h k (hk.trans hN) z

lemma movc1_Bd_abs {A : ℝ} {κ : Euc d → ℝ} (h : MovcBd 0 A κ) (z : Euc d) : |κ z| ≤ A := by
  have := h 0 le_rfl z
  rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this

/-- A bounded continuous kernel is a `MovKer`. -/
lemma movc1_ker {s : ℝ} {κ : Euc d → ℝ} (hc : Continuous κ) {A : ℝ} (hA : ∀ z, |κ z| ≤ A) :
    MovKer d s κ := by
  refine ⟨hc.aestronglyMeasurable, max A 0, le_max_right _ _, Filter.Eventually.of_forall fun z => ?_⟩
  calc |κ z| ≤ max A 0 := (hA z).trans (le_max_left _ _)
    _ = max A 0 * 1 := (mul_one _).symm
    _ ≤ max A 0 * movb2_Bs d s z := mul_le_mul_of_nonneg_left (movb2_Bs_ge_one z) (le_max_right _ _)

/-- Reflection `y ↦ κ(x - y)` preserves the derivative norms. -/
lemma movc1_norm_iter_refl (κ : Euc d → ℝ) (x : Euc d) (k : ℕ) (y : Euc d) :
    ‖iteratedFDeriv ℝ k (fun y => κ (x - y)) y‖ = ‖iteratedFDeriv ℝ k κ (x - y)‖ := by
  have e1 : (fun y => κ (x - y)) = (fun y => κ (y + x)) ∘ (LinearIsometryEquiv.neg ℝ (E := Euc d)) := by
    funext y; simp [sub_eq_add_neg, add_comm]
  rw [e1, LinearIsometryEquiv.norm_iteratedFDeriv_comp_right, iteratedFDeriv_comp_add_right]
  simp [sub_eq_add_neg, add_comm]

section TT

variable {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
include hd hs0 hsd

/-- Integration by parts for a bounded smooth kernel with bounded derivative. -/
theorem movc1_ibp {κ : Euc d → ℝ} (hκ : ContDiff ℝ ∞ κ) {A : ℝ} (hA : MovcBd 1 A κ) {c E : ℝ} (hc : 0 < c)
    {u : Euc d → ℝ} (hu : ContDiff ℝ 1 u) (hga : movb2_GA 1 c E u) (i : Fin d) (x : Euc d) :
    movb2_T κ (fun y => fderiv ℝ u y (EuclideanSpace.single i 1)) x =
      movb2_T (mova3b1_Dj i κ) u x := by
  have hE := movb2_GA_nonneg hga
  obtain ⟨h0, -⟩ := movb2_GA_01 hga
  set v : Euc d := EuclideanSpace.single i 1 with hv
  have hu1 : ContDiff ℝ ((0 + 1 : ℕ) : WithTop ℕ∞) u := by simpa using hu
  have hw := movb2_GA_partial hu1 (movb2_GA_mono le_rfl (by simpa using hga)) v
  have hw0 : ∀ y, |fderiv ℝ u y v| ≤ E * ‖v‖ * Real.exp (-c * ‖y‖ ^ 2) := fun y => by
    have := hw 0 le_rfl y
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hwc : Continuous (fun y => fderiv ℝ u y v) :=
    (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have huc : Continuous u := hu.continuous
  have hgdiff : ∀ z, HasFDerivAt (fun z : Euc d => u (x - z)) (-(fderiv ℝ u (x - z))) z := by
    intro z
    have h1 : HasFDerivAt (fun z : Euc d => x - z) (-(ContinuousLinearMap.id ℝ (Euc d))) z :=
      (hasFDerivAt_id z).const_sub x
    have := ((hu.differentiable one_ne_zero) (x - z)).hasFDerivAt.comp z h1
    exact this.congr_fderiv (by ext w; simp)
  have hκc : Continuous κ := hκ.continuous
  have hDκ : MovcBd 0 A (mova3b1_Dj i κ) := movc1_Bd_Dj hκ hA i
  have hDκc : Continuous (mova3b1_Dj i κ) := (mova3b2_contDiff_Dj i hκ).continuous
  have hker := movc1_ker (s := s) hκc (movc1_Bd_abs (movc1_Bd_mono hA (by norm_num)))
  have hkker := movc1_ker (s := s) hDκc (movc1_Bd_abs hDκ)
  have hk1 := movb2_T_integrable hd hs0 hsd hker hc hE huc h0 x
  have hk2 := movb2_T_integrable hd hs0 hsd hker hc (mul_nonneg hE (norm_nonneg v)) hwc hw0 x
  have hk3 := movb2_T_integrable hd hs0 hsd hkker hc hE huc h0 x
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure (Euc d)))
    (f := κ) (g := fun z => u (x - z)) (v := v)
    (by
      refine hk3.congr (Filter.Eventually.of_forall fun z => ?_)
      rfl)
    (by
      refine hk2.neg.congr (Filter.Eventually.of_forall fun z => ?_)
      simp [(hgdiff z).fderiv])
    hk1
    (fun z _ => (hκ.differentiable (by simp)) z)
    (fun z _ => (hgdiff z).differentiableAt)
  simp only [(hgdiff _).fderiv, neg_apply, mul_neg, integral_neg, neg_inj] at key
  simpa [movb2_T, mova3b1_Dj] using key

/-- Differentiation of `κ * w` in the direction `e_j` falls on the kernel. -/
theorem movc1_Dj_T {κ : Euc d → ℝ} (hκ : ContDiff ℝ ∞ κ) {A : ℝ} (hA : MovcBd 1 A κ) {c E : ℝ} (hc : 0 < c)
    {w : Euc d → ℝ} (hw : ContDiff ℝ 1 w) (hga : movb2_GA 1 c E w) (j : Fin d) :
    mova3b1_Dj j (movb2_T κ w) = movb2_T (mova3b1_Dj j κ) w := by
  funext x
  have hker := movc1_ker (s := s) hκ.continuous (movc1_Bd_abs (movc1_Bd_mono hA (by norm_num)))
  obtain ⟨hF, hL⟩ := movb2_T_fderiv hd hs0 hsd hker hc hw hga x
  simp only [mova3b1_Dj]
  rw [hF.fderiv, hL, movc1_ibp hd hs0 hsd hκ hA hc hw hga j x]

end TT

lemma movc1_G_GA {w : Euc d → ℝ} (hw : MovcG w) (k : ℕ) :
    ∃ c E : ℝ, 0 < c ∧ 0 ≤ E ∧ movb2_GA k c E w := by
  obtain ⟨-, c, hc, hk⟩ := hw
  choose C hC using hk
  have hC0 : ∀ i, 0 ≤ C i := fun i => movc1_G_nonneg (hC i)
  refine ⟨c, ∑ i ∈ Finset.range (k + 1), C i, hc, Finset.sum_nonneg fun i _ => hC0 i, fun i hi y => ?_⟩
  refine (hC i y).trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
  exact Finset.single_le_sum (f := C) (fun i _ => hC0 i) (Finset.mem_range.2 (by omega))

lemma movc1_gauss_integrable (hd : 1 ≤ d) {c : ℝ} (hc : 0 < c) :
    Integrable (fun y : Euc d => Real.exp (-c * ‖y‖ ^ 2)) volume := by
  have := movtr_integrable_rpow_gauss (d := d) hd (α := 0) (c := c) (by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith) hc
  simpa using this

lemma movc1_T_bdd (hd : 1 ≤ d) {c E A : ℝ} (hc : 0 < c) {κ w : Euc d → ℝ}
    (hκ : ∀ z, |κ z| ≤ A) (hw : ∀ y, |w y| ≤ E * Real.exp (-c * ‖y‖ ^ 2)) (x : Euc d) :
    |movb2_T κ w x| ≤ A * (E * ∫ y : Euc d, Real.exp (-c * ‖y‖ ^ 2)) := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hκ 0)
  have hG := movc1_gauss_integrable hd hc
  have hbd : Integrable (fun z : Euc d => A * (E * Real.exp (-c * ‖x - z‖ ^ 2))) volume :=
    (((hG.comp_sub_left x)).const_mul E).const_mul A
  have hint : ∫ z : Euc d, A * (E * Real.exp (-c * ‖x - z‖ ^ 2)) = A * (E * ∫ y : Euc d, Real.exp (-c * ‖y‖ ^ 2)) := by
    rw [integral_const_mul, integral_const_mul]
    congr 2
    exact integral_sub_left_eq_self (fun y : Euc d => Real.exp (-c * ‖y‖ ^ 2)) volume x
  rw [← hint]
  unfold movb2_T
  refine (abs_integral_le_integral_abs).trans ?_
  refine integral_mono_of_nonneg (Eventually.of_forall fun z => abs_nonneg _) hbd
    (Eventually.of_forall fun z => ?_)
  beta_reduce
  rw [abs_mul]
  exact mul_le_mul (hκ z) (hw (x - z)) (abs_nonneg _) hA0

section TG

variable {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
include hd hs0 hsd

/-- `κ * w` has temperate growth (all derivatives bounded) for `κ ∈ C_b^∞` and `w` of Gaussian class. -/
theorem movc1_T_tg {κ : Euc d → ℝ} (hκ : MovcB κ) {w : Euc d → ℝ} (hw : MovcG w) :
    Function.HasTemperateGrowth (movb2_T κ w) := by
  obtain ⟨hκs, hκb⟩ := hκ
  have hA : ∃ A : ℝ, ∀ z, |κ z| ≤ A := by
    obtain ⟨A, hA⟩ := hκb 0
    exact ⟨A, fun z => by simpa using hA z⟩
  obtain ⟨A, hA⟩ := hA
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  have hker := movc1_ker (s := s) hκs.continuous hA
  have hcd : ∀ k : ℕ, ContDiff ℝ (k : WithTop ℕ∞) (movb2_T κ w) := by
    intro k
    obtain ⟨c, E, hc, hE, hga⟩ := movc1_G_GA hw k
    exact movb2_T_contDiff hd hs0 hsd hker hc k (hw.1.of_le (by exact_mod_cast le_top)) hga
  refine ⟨contDiff_infty.2 hcd, fun n => ⟨0, ?_⟩⟩
  obtain ⟨c, E, hc, hE, hga⟩ := movc1_G_GA hw n
  have hwn : ContDiff ℝ (n : WithTop ℕ∞) w := hw.1.of_le (by exact_mod_cast le_top)
  set G : ℝ := ∫ y : Euc d, Real.exp (-c * ‖y‖ ^ 2) with hG
  have hG0 : 0 ≤ G := integral_nonneg fun y => (Real.exp_pos _).le
  refine ⟨A * (E * G), fun x => ?_⟩
  rw [pow_zero, mul_one]
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) (fun m => ?_)
  rw [movb2_T_iter hd hs0 hsd hker hc n hwn hga x m]
  have hP : 0 ≤ ∏ i, ‖m i‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
  have := movc1_T_bdd hd hc (κ := κ) (w := fun y => iteratedFDeriv ℝ n w y m) (E := E * ∏ i, ‖m i‖) hA
    (fun y => by
      calc |iteratedFDeriv ℝ n w y m| ≤ ‖iteratedFDeriv ℝ n w y‖ * ∏ i, ‖m i‖ := by
            rw [← Real.norm_eq_abs]; exact (iteratedFDeriv ℝ n w y).le_opNorm m
        _ ≤ (E * Real.exp (-c * ‖y‖ ^ 2)) * ∏ i, ‖m i‖ :=
            mul_le_mul_of_nonneg_right (hga n le_rfl y) hP
        _ = E * (∏ i, ‖m i‖) * Real.exp (-c * ‖y‖ ^ 2) := by ring) x
  rw [Real.norm_eq_abs]
  calc _ ≤ A * (E * (∏ i, ‖m i‖) * G) := this
    _ = A * (E * G) * ∏ i, ‖m i‖ := by ring

end TG

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

lemma movc1_schwartz_G_mul {om : Euc d → ℝ} (hom : MovcG om) (v : 𝓢R) :
    MovcG (fun y => om y * v y) := by
  have hG : MovcG (fun x => v x * om x) := by
    refine movc1_G_mul hom (v.smooth ⊤) (fun k => ?_)
    obtain ⟨M, hM⟩ := (⟨SchwartzMap.seminorm ℝ 0 k v, fun x => SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ v k x⟩ :
      ∃ M : ℝ, ∀ x, ‖iteratedFDeriv ℝ k v x‖ ≤ M)
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
    exact ⟨M, hM0, fun x => (hM x).trans (by nlinarith [norm_nonneg x])⟩
  have e : (fun y => om y * v y) = fun x => v x * om x := by funext y; ring
  rw [e]; exact hG

lemma movc1_refl_tg {κ : Euc d → ℝ} (hκ : MovcB κ) (x : Euc d) :
    Function.HasTemperateGrowth (fun y => κ (x - y)) := by
  refine ⟨hκ.1.comp (contDiff_const.sub contDiff_id), fun n => ?_⟩
  obtain ⟨A, hA⟩ := hκ.2 n
  exact ⟨0, A, fun y => by rw [movc1_norm_iter_refl, pow_zero, mul_one]; exact hA _⟩

lemma movc1_T_eq_pair (κ w : Euc d → ℝ) (x : Euc d) :
    movb2_T κ w x = ∫ y, κ (x - y) * w y := by
  unfold movb2_T
  rw [← integral_sub_left_eq_self (fun z => κ z * w (x - z)) volume x]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [sub_sub_cancel]

/-- **Far pairing** (step 4(b), basic form): for every real `r`, `|∫ κ(x-y) ω(y) v(y) dy| ≤ C A ‖v‖_{Σ^r}`
uniformly in `x`, for kernels with derivatives bounded by `A` up to order `⌈|r|⌉`. -/
theorem movc1_far0 {om : Euc d → ℝ} (hom : MovcG om) (r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {A : ℝ} {κ : Euc d → ℝ}, 0 ≤ A → MovcB κ → MovcBd ⌈|r|⌉₊ A κ →
      ∀ (v : 𝓢R) (x : Euc d), |movb2_T κ (fun y => om y * v y) x| ≤ C * A * oscNorm r v := by
  set N : ℕ := ⌈|r|⌉₊ with hN
  have hrN : |-r| ≤ (N : ℝ) := by rw [abs_neg]; exact Nat.le_ceil _
  obtain ⟨C3, hC3, hmult⟩ := mo_mult_cb (d := d) (-r) N hrN
  obtain ⟨φ, hφ⟩ := movc1_G_schwartz hom
  have hom' : MemOsc (-r) om := by rw [← hφ]; exact memOsc_schwartz (-r) φ
  refine ⟨C3 * oscNorm (-r) om, mul_nonneg hC3 (Real.sqrt_nonneg _), fun {A κ} hA hκ hbd v x => ?_⟩
  have hθ : mova3b2_Q N 0 A (fun y => κ (x - y)) := by
    refine mova3b2_Q_of_iter (hκ.1.comp (contDiff_const.sub contDiff_id)) (fun k hk y => ?_)
    rw [movc1_norm_iter_refl, pow_zero, mul_one]
    exact hbd k hk _
  obtain ⟨hm, hn⟩ := hmult A hA _ (movc1_refl_tg hκ x) hθ om hom'
  have hv : MemOsc (-(-r)) (⇑v) := by rw [neg_neg]; exact memOsc_schwartz r v
  have hd := mo_dual_le (-r) hv hm
  rw [neg_neg] at hd
  rw [movc1_T_eq_pair]
  have e : (fun y => κ (x - y) * (om y * v y)) = fun y => v y * (κ (x - y) * om y) := by
    funext y; ring
  rw [e]
  calc |∫ y, v y * (κ (x - y) * om y)| ≤ oscNorm r (⇑v) * oscNorm (-r) (fun y => κ (x - y) * om y) := hd
    _ ≤ oscNorm r (⇑v) * (C3 * A * oscNorm (-r) om) := mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg _)
    _ = _ := by ring

/-- Derivative version of `movc1_far0`: the coordinate-iterated derivatives of `x ↦ ∫ κ(x-y) ω v` up to order `K`
are bounded by `C A ‖v‖_{Σ^r}` (in the form `mova3b2_Q`), if the derivatives of `κ` are bounded up to order
`⌈|r|⌉ + K`. -/
theorem movc1_farK (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {om : Euc d → ℝ} (hom : MovcG om) (r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (K : ℕ) {A : ℝ} {κ : Euc d → ℝ}, 0 ≤ A → MovcB κ → MovcBd (⌈|r|⌉₊ + K) A κ →
      ∀ v : 𝓢R, mova3b2_Q K 0 (C * A * oscNorm r v) (movb2_T κ (fun y => om y * v y)) := by
  obtain ⟨C, hC, hf0⟩ := movc1_far0 hom r
  refine ⟨C, hC, fun K => ?_⟩
  induction K with
  | zero =>
    intro A κ hA hκ hbd v x
    have := hf0 hA hκ (by simpa using hbd) v x
    simpa using this
  | succ K ih =>
    intro A κ hA hκ hbd v
    have hw := movc1_schwartz_G_mul hom v
    obtain ⟨c, E, hc, hE, hga⟩ := movc1_G_GA hw 1
    refine ⟨fun x => ?_, fun j => ?_⟩
    · have := hf0 hA hκ (movc1_Bd_mono hbd (by omega)) v x
      simpa using this
    · have hAκ : MovcBd 1 A κ := movc1_Bd_mono hbd (by omega)
      have e := movc1_Dj_T hd hs0 hsd hκ.1 hAκ hc (hw.1.of_le (by exact_mod_cast le_top)) hga j
      rw [e]
      exact ih hA (movc1_B_Dj hκ j) (movc1_Bd_Dj hκ.1 hbd j) v

/-! ### The far kernels -/

/-- Derivatives bounded with an extra decay factor `(1+‖z‖)⁻¹`. -/
def MovcK (κ : Euc d → ℝ) : Prop :=
  ContDiff ℝ ∞ κ ∧ ∀ k : ℕ, ∃ M : ℝ, ∀ z : Euc d, (1 + ‖z‖) * ‖iteratedFDeriv ℝ k κ z‖ ≤ M

lemma movc1_K_B {κ : Euc d → ℝ} (hκ : MovcK κ) : MovcB κ := by
  refine ⟨hκ.1, fun k => ?_⟩
  obtain ⟨M, hM⟩ := hκ.2 k
  refine ⟨M, fun z => ?_⟩
  have h1 : ‖iteratedFDeriv ℝ k κ z‖ ≤ (1 + ‖z‖) * ‖iteratedFDeriv ℝ k κ z‖ :=
    le_mul_of_one_le_left (norm_nonneg _) (by linarith [norm_nonneg z])
  exact h1.trans (hM z)

lemma movc1_K_Dj {κ : Euc d → ℝ} (hκ : MovcK κ) (j : Fin d) : MovcK (mova3b1_Dj j κ) := by
  refine ⟨mova3b2_contDiff_Dj j hκ.1, fun k => ?_⟩
  obtain ⟨M, hM⟩ := hκ.2 (k + 1)
  refine ⟨M, fun z => ?_⟩
  have h1 := movb2_norm_iter_partial (hκ.1.of_le (by exact_mod_cast le_top) : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) κ)
    (EuclideanSpace.single j (1 : ℝ)) z
  have h2 : ‖(EuclideanSpace.single j (1 : ℝ) : Euc d)‖ = 1 := by simp
  rw [h2, one_mul] at h1
  exact (mul_le_mul_of_nonneg_left h1 (by positivity)).trans (hM z)

lemma movc1_kfar_eq (s : ℝ) (i : Fin d) : movb2_kfar d s i = mova3b1_Dj i (movb2_gfar d s) := rfl

lemma movc1_kfar_K {s : ℝ} (hs0 : 0 ≤ s) (i : Fin d) : MovcK (movb2_kfar d s i) := by
  rw [movc1_kfar_eq]
  refine ⟨mova3b2_contDiff_Dj i (mv1_gfar_smooth s), fun k => ?_⟩
  obtain ⟨C, hC0, hC⟩ := mv1_gfar_bound (d := d) hs0 (k + 1) (by omega)
  refine ⟨C, fun z => ?_⟩
  have h1 := movb2_norm_iter_partial ((mv1_gfar_smooth (d := d) s).of_le (by exact_mod_cast le_top) :
    ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (movb2_gfar d s)) (EuclideanSpace.single i (1 : ℝ)) z
  have h2 : ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖ = 1 := by simp
  rw [h2, one_mul] at h1
  have hr : 0 < 1 + ‖z‖ := by positivity
  have h3 : (1 + ‖z‖) * (1 + ‖z‖) ^ (-s - ((k + 1 : ℕ) : ℝ)) ≤ 1 := by
    have e : (1 + ‖z‖) * (1 + ‖z‖) ^ (-s - ((k + 1 : ℕ) : ℝ)) = (1 + ‖z‖) ^ (1 + (-s - ((k + 1 : ℕ) : ℝ))) := by
      rw [Real.rpow_add hr, Real.rpow_one]
    rw [e]
    refine Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg z]) ?_
    push_cast; linarith
  calc (1 + ‖z‖) * ‖iteratedFDeriv ℝ k (mova3b1_Dj i (movb2_gfar d s)) z‖
      ≤ (1 + ‖z‖) * (C * (1 + ‖z‖) ^ (-s - ((k + 1 : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left (h1.trans (hC z)) hr.le
    _ = C * ((1 + ‖z‖) * (1 + ‖z‖) ^ (-s - ((k + 1 : ℕ) : ℝ))) := by ring
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left h3 hC0
    _ = C := mul_one _

lemma movc1_coord_iter_le (i : Fin d) (k : ℕ) (z : Euc d) :
    ‖iteratedFDeriv ℝ k (fun z : Euc d => z i) z‖ ≤ 1 + ‖z‖ := by
  set ℓ : Euc d →L[ℝ] ℝ := EuclideanSpace.proj i with hℓ
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · subst h0
    rw [norm_iteratedFDeriv_zero]
    have : |z i| ≤ ‖z‖ := by simpa using (PiLp.norm_apply_le z i)
    rw [Real.norm_eq_abs]; linarith
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have := mov0_clm_iter ℓ k' z
    have hn : ‖ℓ‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => ?_
      have : ‖ℓ w‖ ≤ ‖w‖ := by simpa [hℓ] using PiLp.norm_apply_le w i
      simpa using this
    calc _ ≤ ‖ℓ‖ := this
      _ ≤ 1 := hn
      _ ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]

/-- Multiplying a weighted-class kernel by a coordinate gives a bounded-derivative kernel. -/
lemma movc1_coord_B {κ : Euc d → ℝ} (hκ : MovcK κ) (i : Fin d) : MovcB (fun z => z i * κ z) := by
  set ℓ : Euc d →L[ℝ] ℝ := EuclideanSpace.proj i with hℓ
  have hℓs : ContDiff ℝ ∞ (fun z : Euc d => z i) := ℓ.contDiff
  refine ⟨hℓs.mul hκ.1, fun n => ?_⟩
  choose M hM using hκ.2
  refine ⟨∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * M (n - k), fun z => ?_⟩
  have h1 := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (N := (n : WithTop ℕ∞))
    (hℓs.of_le (by exact_mod_cast le_top)) (hκ.1.of_le (by exact_mod_cast le_top)) z (n := n) le_rfl
  refine h1.trans (Finset.sum_le_sum fun k hk => ?_)
  have hk' : k ≤ n := by simpa [Nat.lt_succ_iff] using hk
  have hℓk := movc1_coord_iter_le i k z
  have hch : (0 : ℝ) ≤ n.choose k := Nat.cast_nonneg _
  calc (n.choose k : ℝ) * ‖iteratedFDeriv ℝ k (fun z : Euc d => z i) z‖ * ‖iteratedFDeriv ℝ (n - k) κ z‖
      ≤ (n.choose k : ℝ) * (1 + ‖z‖) * ‖iteratedFDeriv ℝ (n - k) κ z‖ := by
        gcongr
    _ = (n.choose k : ℝ) * ((1 + ‖z‖) * ‖iteratedFDeriv ℝ (n - k) κ z‖) := by ring
    _ ≤ (n.choose k : ℝ) * M (n - k) := mul_le_mul_of_nonneg_left (hM (n - k) z) hch

lemma movc1_B_Bd {κ : Euc d → ℝ} (hκ : MovcB κ) (N : ℕ) : ∃ A : ℝ, 0 ≤ A ∧ MovcBd N A κ := by
  choose M hM using hκ.2
  refine ⟨∑ k ∈ Finset.range (N + 1), |M k|, Finset.sum_nonneg fun _ _ => abs_nonneg _, fun k hk z => ?_⟩
  refine (hM k z).trans ((le_abs_self _).trans ?_)
  exact Finset.single_le_sum (f := fun k => |M k|) (fun _ _ => abs_nonneg _)
    (Finset.mem_range.2 (by omega))

/-! ### Far terms: `Σ^r → Σ^σ` -/

lemma movc1_osc_nonneg (m : ℝ) (f : Euc d → ℝ) : 0 ≤ oscNorm m f := Real.sqrt_nonneg _

lemma movc1_B_tg {κ : Euc d → ℝ} (hκ : MovcB κ) : Function.HasTemperateGrowth κ :=
  ⟨hκ.1, fun n => by obtain ⟨A, hA⟩ := hκ.2 n; exact ⟨0, A, fun x => by simpa using hA x⟩⟩

lemma movc1_G_coord {om : Euc d → ℝ} (hom : MovcG om) (i : Fin d) : MovcG (fun y => y i * om y) :=
  movc1_G_mul hom (ContinuousLinearMap.contDiff (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ))
    (fun k => ⟨1, zero_le_one, fun x => by simpa using movc1_coord_iter_le i k x⟩)

/-- Multiplication by a `C_b^∞` function on `Σ^σ` (B3, packaged for `MovcB`). -/
theorem movc1_mult_B {b : Euc d → ℝ} (hb : MovcB b) (σ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Euc d → ℝ, MemOsc σ f →
      MemOsc σ (fun x => b x * f x) ∧ oscNorm σ (fun x => b x * f x) ≤ C * oscNorm σ f := by
  set N : ℕ := ⌈|σ|⌉₊ with hN
  have hσN : |σ| ≤ (N : ℝ) := Nat.le_ceil _
  obtain ⟨C3, hC3, hmult⟩ := mo_mult_cb (d := d) σ N hσN
  obtain ⟨A, hA0, hA⟩ := movc1_B_Bd hb N
  have hQ : mova3b2_Q N 0 A b := mova3b2_Q_of_iter hb.1 (fun k hk x => by
    rw [pow_zero, mul_one]; exact hA k hk x)
  exact ⟨C3 * A, mul_nonneg hC3 hA0, fun f hf => by
    obtain ⟨h1, h2⟩ := hmult A hA0 b (movc1_B_tg hb) hQ f hf
    exact ⟨h1, h2⟩⟩

section FarTerm

variable {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
include hd hs0 hsd

/-- **Far term** (step 4(b) + B3): for a `C_b^∞` kernel `κ`, a Gaussian-class `ω` and `ψ'` and all real `r, σ`:
`‖(κ * (ω v)) ψ'‖_{Σ^σ} ≤ C ‖v‖_{Σ^r}` for Schwartz `v`. -/
theorem movc1_far_term {om ps : Euc d → ℝ} (hom : MovcG om) (hps : MovcG ps) {κ : Euc d → ℝ}
    (hκ : MovcB κ) (r σ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : 𝓢R,
      MemOsc σ (fun x => movb2_T κ (fun y => om y * v y) x * ps x) ∧
        oscNorm σ (fun x => movb2_T κ (fun y => om y * v y) x * ps x) ≤ C * oscNorm r v := by
  set N' : ℕ := ⌈|σ|⌉₊ with hN'
  have hσN : |σ| ≤ (N' : ℝ) := Nat.le_ceil _
  obtain ⟨C1, hC1, hfar⟩ := movc1_farK hd hs0 hsd hom r
  obtain ⟨C3, hC3, hmult⟩ := mo_mult_cb (d := d) σ N' hσN
  obtain ⟨A, hA0, hA⟩ := movc1_B_Bd hκ (⌈|r|⌉₊ + N')
  obtain ⟨φ, hφ⟩ := movc1_G_schwartz hps
  have hps' : MemOsc σ ps := by rw [← hφ]; exact memOsc_schwartz σ φ
  refine ⟨C3 * (C1 * A) * oscNorm σ ps, mul_nonneg (mul_nonneg hC3 (mul_nonneg hC1 hA0)) (movc1_osc_nonneg _ _), fun v => ?_⟩
  have hQ := hfar N' hA0 hκ hA v
  have htg := movc1_T_tg hd hs0 hsd hκ (movc1_schwartz_G_mul hom v)
  have hC1A : 0 ≤ C1 * A * oscNorm r v := mul_nonneg (mul_nonneg hC1 hA0) (movc1_osc_nonneg _ _)
  obtain ⟨h1, h2⟩ := hmult (C1 * A * oscNorm r v) hC1A _ htg hQ ps hps'
  refine ⟨h1, h2.trans ?_⟩
  exact le_of_eq (by ring)

end FarTerm

/-! ### The weight `x_i` -/

section Weight

variable {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
include hd hs0 hsd

/-- `x_i (κ * w)(x) = ((z_i κ) * w)(x) + (κ * (y_i w))(x)`. -/
lemma movc1_xT {κ : Euc d → ℝ} (i : Fin d) (hκ : MovcB κ) (hκ' : MovcB (fun z => z i * κ z)) {w : Euc d → ℝ}
    (hw : MovcG w) (x : Euc d) :
    x i * movb2_T κ w x = movb2_T (fun z => z i * κ z) w x + movb2_T κ (fun y => y i * w y) x := by
  obtain ⟨A, hA⟩ := (movc1_B_Bd hκ 0).imp fun A h => h.2
  obtain ⟨A', hA'⟩ := (movc1_B_Bd hκ' 0).imp fun A h => h.2
  have hker := movc1_ker (s := s) hκ.1.continuous (movc1_Bd_abs hA)
  have hker' := movc1_ker (s := s) hκ'.1.continuous (movc1_Bd_abs hA')
  obtain ⟨c, E, hc, hE, hga⟩ := movc1_G_GA hw 1
  obtain ⟨h0, -⟩ := movb2_GA_01 hga
  have hw2 := movc1_G_coord hw i
  obtain ⟨c2, E2, hc2, hE2, hga2⟩ := movc1_G_GA hw2 1
  obtain ⟨h02, -⟩ := movb2_GA_01 hga2
  have hI1 := movb2_T_integrable hd hs0 hsd hker' hc hE hw.1.continuous h0 x
  have hI2 := movb2_T_integrable hd hs0 hsd hker hc2 hE2 hw2.1.continuous h02 x
  unfold movb2_T at hI1 hI2 ⊢
  rw [← integral_add hI1 hI2, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [PiLp.sub_apply]
  ring

end Weight

end HRS.MS.MovC1
