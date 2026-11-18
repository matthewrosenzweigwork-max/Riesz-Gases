import HRS.MS.MovForceAux4

/-!
# MOV-B2 (2): convolution calculus for the split kernels (S6.1, steps 4(a), 5)

Namespace `HRS.MS.MovForce`, helper prefix `movb2_`.

Generic in a kernel `κ` dominated by a multiple of the universal majorant `2‖z‖^{-sp s} + ‖z‖ + 1`
(`MovKer`), and a profile `w` with Gaussian amplitude bounds `movb2_GA k c E w`
(`‖D^i w(y)‖ ≤ E e^{-c‖y‖²}` for `i ≤ k`), with `movb2_T κ w (x) = ∫ κ(z) w(x - z) dz`:

* `movb2_T_fderiv`: `D(κ * w)(x) e = (κ * ∂_e w)(x)`;
* `movb2_T_contDiff`: `κ * w ∈ C^k` for `w ∈ C^k`;
* `movb2_T_iter`: `D^k(κ * w)(x)(m) = (κ * D^k w(·)(m))(x)` (derivatives fall on the profile).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovForce

open HRS.Whole

variable {d : ℕ} {s : ℝ}

/-- The universal singular majorant of the kernels. -/
def movb2_Bs (d : ℕ) (s : ℝ) (z : Euc d) : ℝ := 2 * ‖z‖ ^ (-movtr_sp s) + ‖z‖ + 1

/-- Kernels dominated by a multiple of the universal majorant. -/
def MovKer (d : ℕ) (s : ℝ) (κ : Euc d → ℝ) : Prop :=
  AEStronglyMeasurable κ volume ∧ ∃ A : ℝ, 0 ≤ A ∧ ∀ᵐ z : Euc d, |κ z| ≤ A * movb2_Bs d s z

/-- Gaussian amplitude bound on the first `k` derivatives. -/
def movb2_GA (k : ℕ) (c E : ℝ) (w : Euc d → ℝ) : Prop :=
  ∀ i ≤ k, ∀ y, ‖iteratedFDeriv ℝ i w y‖ ≤ E * Real.exp (-c * ‖y‖ ^ 2)

/-- The convolution `κ * w`, in the form `∫ κ(z) w(x - z) dz`. -/
def movb2_T (κ w : Euc d → ℝ) (x : Euc d) : ℝ := ∫ z, κ z * w (x - z)

lemma movb2_GA_mono {k k' : ℕ} (h : k' ≤ k) {c E : ℝ} {w : Euc d → ℝ} (hw : movb2_GA k c E w) :
    movb2_GA k' c E w := fun i hi => hw i (hi.trans h)

lemma movb2_GA_01 {c E : ℝ} {w : Euc d → ℝ} (hw : movb2_GA 1 c E w) :
    (∀ y, |w y| ≤ E * Real.exp (-c * ‖y‖ ^ 2)) ∧
      (∀ y, ‖fderiv ℝ w y‖ ≤ E * Real.exp (-c * ‖y‖ ^ 2)) := by
  refine ⟨fun y => ?_, fun y => ?_⟩
  · have := hw 0 (by norm_num) y
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  · have := hw 1 le_rfl y
    rwa [norm_iteratedFDeriv_one] at this

lemma movb2_GA_nonneg {k : ℕ} {c E : ℝ} {w : Euc d → ℝ} (hw : movb2_GA k c E w) : 0 ≤ E := by
  have := hw 0 (Nat.zero_le _) 0
  simp only [norm_zero, mul_zero, zero_pow two_ne_zero, Real.exp_zero, mul_one] at this
  exact (norm_nonneg _).trans this

/-- `∂_e w` has Gaussian amplitude `E ‖e‖`, one order lower. -/
lemma movb2_GA_partial {k : ℕ} {c E : ℝ} {w : Euc d → ℝ} (hw : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) w)
    (hga : movb2_GA (k + 1) c E w) (e : Euc d) :
    movb2_GA k c (E * ‖e‖) (fun y => fderiv ℝ w y e) := by
  intro i hi y
  have hfd : ContDiff ℝ (k : WithTop ℕ∞) (fderiv ℝ w) := hw.fderiv_right (m := k) (by rw [Nat.cast_succ])
  have h1 := norm_iteratedFDeriv_clm_apply_const (𝕜 := ℝ) (f := fderiv ℝ w) (c := e) (x := y) (n := i)
    (N := (k : WithTop ℕ∞)) hfd.contDiffAt (by exact_mod_cast hi)
  rw [norm_iteratedFDeriv_fderiv] at h1
  refine h1.trans ?_
  have := hga (i + 1) (by omega) y
  calc ‖e‖ * ‖iteratedFDeriv ℝ (i + 1) w y‖ ≤ ‖e‖ * (E * Real.exp (-c * ‖y‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left this (norm_nonneg _)
    _ = _ := by ring

lemma movb2_partial_contDiff {k : ℕ} {w : Euc d → ℝ} (hw : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) w) (e : Euc d) :
    ContDiff ℝ (k : WithTop ℕ∞) (fun y => fderiv ℝ w y e) :=
  (hw.fderiv_right (m := k) (by rw [Nat.cast_succ])).clm_apply contDiff_const

section Gen

variable (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
include hd hs0 hsd

lemma movb2_ker_data {κ : Euc d → ℝ} (hκ : MovKer d s κ) {c : ℝ} (hc : 0 < c) :
    ∃ B : Euc d → ℝ, (∀ᵐ z : Euc d, |κ z| ≤ B z) ∧
      Integrable (fun z => B z * Real.exp (-(c / 2) * ‖z‖ ^ 2)) := by
  obtain ⟨-, A, hA, hb⟩ := hκ
  obtain ⟨-, -, hBint⟩ := mv1_g_data (d := d) hd hs0 hsd hc
  refine ⟨fun z => A * movb2_Bs d s z, hb, ?_⟩
  refine (hBint.const_mul A).congr (Filter.Eventually.of_forall fun z => ?_)
  simp only [movb2_Bs]; ring

/-- Differentiation of `κ * w` (derivative on the profile). -/
theorem movb2_T_fderiv {κ : Euc d → ℝ} (hκ : MovKer d s κ) {c E : ℝ} (hc : 0 < c) {w : Euc d → ℝ}
    (hw : ContDiff ℝ 1 w) (hga : movb2_GA 1 c E w) (x : Euc d) :
    HasFDerivAt (movb2_T κ w) (∫ z, κ z • fderiv ℝ w (x - z)) x ∧
      ∀ e, (∫ z, κ z • fderiv ℝ w (x - z)) e = movb2_T κ (fun y => fderiv ℝ w y e) x := by
  obtain ⟨B, hB, hBint⟩ := movb2_ker_data hd hs0 hsd hκ hc
  obtain ⟨h0, h1⟩ := movb2_GA_01 hga
  have hE := movb2_GA_nonneg hga
  obtain ⟨hF, hint⟩ := mv1_hasFDerivAt_conv hc hκ.1 hB hBint hE hw h0 h1 x
  refine ⟨hF, fun e => ?_⟩
  rw [ContinuousLinearMap.integral_apply hint]
  simp [movb2_T]

theorem movb2_T_continuous {κ : Euc d → ℝ} (hκ : MovKer d s κ) {c E : ℝ} (hc : 0 < c) {w : Euc d → ℝ}
    (hw : Continuous w) (h0 : ∀ y, |w y| ≤ E * Real.exp (-c * ‖y‖ ^ 2)) (hE : 0 ≤ E) :
    Continuous (movb2_T κ w) := by
  obtain ⟨B, hB, hBint⟩ := movb2_ker_data hd hs0 hsd hκ hc
  exact mv1_continuous_conv hc hκ.1 hB hBint hE hw h0

/-- `κ * w ∈ C^k`. -/
theorem movb2_T_contDiff {κ : Euc d → ℝ} (hκ : MovKer d s κ) {c : ℝ} (hc : 0 < c) :
    ∀ (k : ℕ) {E : ℝ} {w : Euc d → ℝ}, ContDiff ℝ (k : WithTop ℕ∞) w → movb2_GA k c E w →
      ContDiff ℝ (k : WithTop ℕ∞) (movb2_T κ w) := by
  intro k
  induction k with
  | zero =>
    intro E w hw hga
    have hw' : Continuous w := by simpa using hw
    have h0 : ∀ y, |w y| ≤ E * Real.exp (-c * ‖y‖ ^ 2) := fun y => by
      have := hga 0 le_rfl y
      rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    have := movb2_T_continuous hd hs0 hsd hκ hc hw' h0 (movb2_GA_nonneg hga)
    simpa using this
  | succ k ih =>
    intro E w hw hga
    have hw1 : ContDiff ℝ 1 w := hw.of_le (by exact_mod_cast Nat.le_add_left 1 k)
    have hga1 : movb2_GA 1 c E w := movb2_GA_mono (by omega) hga
    have hL : ∀ x, ∃ L : Euc d →L[ℝ] ℝ, HasFDerivAt (movb2_T κ w) L x ∧
        L = ∑ i, movb2_T κ (fun y => fderiv ℝ w y (EuclideanSpace.single i 1)) x •
          (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ) := by
      intro x
      obtain ⟨hF, hLe⟩ := movb2_T_fderiv hd hs0 hsd hκ hc hw1 hga1 x
      refine ⟨_, hF, ?_⟩
      rw [mv1_clm_eq_sum (∫ z, κ z • fderiv ℝ w (x - z))]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hLe]
    have hder : Differentiable ℝ (movb2_T κ w) := fun x => (hL x).elim fun _ h => h.1.differentiableAt
    have hfd : fderiv ℝ (movb2_T κ w) = fun x =>
        ∑ i, movb2_T κ (fun y => fderiv ℝ w y (EuclideanSpace.single i 1)) x •
          (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ) := by
      funext x
      obtain ⟨L, hL', hLe⟩ := hL x
      rw [hL'.fderiv, hLe]
    rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
    refine ⟨hder, fun h => absurd h (by simp), ?_⟩
    rw [hfd]
    refine ContDiff.sum fun i _ => ?_
    exact (ih (movb2_partial_contDiff hw _) (movb2_GA_partial hw hga _)).smul
      (contDiff_const (c := (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)))

/-- **Derivatives fall on the profile**: `D^k(κ * w)(x)(m) = (κ * D^k w(·)(m))(x)`. -/
theorem movb2_T_iter {κ : Euc d → ℝ} (hκ : MovKer d s κ) {c : ℝ} (hc : 0 < c) :
    ∀ (k : ℕ) {E : ℝ} {w : Euc d → ℝ}, ContDiff ℝ (k : WithTop ℕ∞) w → movb2_GA k c E w →
      ∀ (x : Euc d) (m : Fin k → Euc d),
        iteratedFDeriv ℝ k (movb2_T κ w) x m = movb2_T κ (fun y => iteratedFDeriv ℝ k w y m) x := by
  intro k
  induction k with
  | zero =>
    intro E w hw hga x m
    simp [movb2_T]
  | succ k ih =>
    intro E w hw hga x m
    have hw1 : ContDiff ℝ 1 w := hw.of_le (by exact_mod_cast Nat.le_add_left 1 k)
    have hga1 : movb2_GA 1 c E w := movb2_GA_mono (by omega) hga
    have hTk : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (movb2_T κ w) :=
      movb2_T_contDiff hd hs0 hsd hκ hc (k + 1) hw hga
    have hfdT : ContDiff ℝ (k : WithTop ℕ∞) (fderiv ℝ (movb2_T κ w)) :=
      hTk.fderiv_right (m := k) (by rw [Nat.cast_succ])
    have hfdw : ContDiff ℝ (k : WithTop ℕ∞) (fderiv ℝ w) :=
      hw.fderiv_right (m := k) (by rw [Nat.cast_succ])
    set e : Euc d := m (Fin.last k) with he
    -- the derivative of `κ * w` in direction `e` is `κ * ∂_e w`
    have hfun : (fun y => fderiv ℝ (movb2_T κ w) y e) = movb2_T κ (fun y => fderiv ℝ w y e) := by
      funext y
      obtain ⟨hF, hLe⟩ := movb2_T_fderiv hd hs0 hsd hκ hc hw1 hga1 y
      rw [hF.fderiv, hLe]
    rw [iteratedFDeriv_succ_apply_right]
    have h1 := iteratedFDeriv_clm_apply_const_apply (𝕜 := ℝ) (c := fderiv ℝ (movb2_T κ w)) (n := k)
      hfdT (i := k) le_rfl (x := x) (u := e) (m := Fin.init m)
    rw [← h1, hfun, ih (movb2_partial_contDiff hw e) (movb2_GA_partial hw hga e) x (Fin.init m)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    have h2 := iteratedFDeriv_clm_apply_const_apply (𝕜 := ℝ) (c := fderiv ℝ w) (n := k)
      hfdw (i := k) le_rfl (x := x - z) (u := e) (m := Fin.init m)
    have h3 : (iteratedFDeriv ℝ (k + 1) w (x - z)) m =
        ((iteratedFDeriv ℝ k (fderiv ℝ w) (x - z)) (Fin.init m)) e := iteratedFDeriv_succ_apply_right m
    beta_reduce
    rw [h3, ← h2]

lemma movb2_T_integrable {κ : Euc d → ℝ} (hκ : MovKer d s κ) {c E : ℝ} (hc : 0 < c) (hE : 0 ≤ E)
    {w : Euc d → ℝ} (hwc : Continuous w) (h0 : ∀ y, |w y| ≤ E * Real.exp (-c * ‖y‖ ^ 2)) (x : Euc d) :
    Integrable (fun z => κ z * w (x - z)) volume := by
  obtain ⟨B, hB, hBint⟩ := movb2_ker_data hd hs0 hsd hκ hc
  exact movtr_integrable_of_gauss_bound hc hκ.1 hB hBint hE hwc (R := ‖x‖) le_rfl h0

/-- The local kernel is a `MovKer`. -/
lemma movb2_gloc_ker : MovKer d s (movb2_gloc d s) := by
  refine ⟨movb2_gloc_aesm hd hs0 hsd, 1, zero_le_one, ?_⟩
  filter_upwards [(mv1_g_data (d := d) hd hs0 hsd (c := 1) one_pos).2.1] with z hz
  rw [one_mul]
  exact (movb2_abs_gloc_le s z).trans hz

/-- The far kernel is a `MovKer`. -/
lemma movb2_gfar_ker : MovKer d s (movb2_gfar d s) := by
  refine ⟨movb2_gfar_aesm hd hs0 hsd, 1, zero_le_one, ?_⟩
  filter_upwards [(mv1_g_data (d := d) hd hs0 hsd (c := 1) one_pos).2.1] with z hz
  rw [one_mul]
  exact (movb2_abs_gfar_le s z).trans hz

end Gen

/-- The `i`-th component of the gradient of the far kernel. -/
def movb2_kfar (d : ℕ) (s : ℝ) (i : Fin d) (z : Euc d) : ℝ :=
  fderiv ℝ (movb2_gfar d s) z (EuclideanSpace.single i 1)

lemma movb2_Bs_ge_one (z : Euc d) : 1 ≤ movb2_Bs d s z := by
  unfold movb2_Bs
  have h1 : 0 ≤ ‖z‖ ^ (-movtr_sp s) := Real.rpow_nonneg (norm_nonneg _) _
  linarith [norm_nonneg z]

/-- `|∂_i g_far (z)| (1 + ‖z‖) ≤ K`. -/
lemma movb2_kfar_bound (hs0 : 0 ≤ s) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (i : Fin d) (z : Euc d), |movb2_kfar d s i z| * (1 + ‖z‖) ≤ K := by
  obtain ⟨C, hC0, hC⟩ := mv1_gfar_bound (d := d) hs0 1 le_rfl
  refine ⟨C, hC0, fun i z => ?_⟩
  have hpos : 0 < 1 + ‖z‖ := by positivity
  have h1 : |movb2_kfar d s i z| ≤ ‖iteratedFDeriv ℝ 1 (movb2_gfar d s) z‖ := by
    rw [norm_iteratedFDeriv_one]
    have := (fderiv ℝ (movb2_gfar d s) z).le_opNorm (EuclideanSpace.single i (1 : ℝ))
    simpa [movb2_kfar, Real.norm_eq_abs] using this
  have h2 : (1 + ‖z‖) ^ (-s - ((1 : ℕ) : ℝ)) * (1 + ‖z‖) ≤ 1 := by
    rw [← Real.rpow_add_one hpos.ne']
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg z]) (by push_cast; linarith)
  calc |movb2_kfar d s i z| * (1 + ‖z‖) ≤ (C * (1 + ‖z‖) ^ (-s - ((1 : ℕ) : ℝ))) * (1 + ‖z‖) :=
        mul_le_mul_of_nonneg_right (h1.trans (hC z)) hpos.le
    _ = C * ((1 + ‖z‖) ^ (-s - ((1 : ℕ) : ℝ)) * (1 + ‖z‖)) := by ring
    _ ≤ C * 1 := mul_le_mul_of_nonneg_left h2 hC0
    _ = C := mul_one C

lemma movb2_kfar_ker (hs0 : 0 ≤ s) (i : Fin d) : MovKer d s (movb2_kfar d s i) := by
  obtain ⟨K, hK0, hK⟩ := movb2_kfar_bound (d := d) (s := s) hs0
  refine ⟨?_, K, hK0, Filter.Eventually.of_forall fun z => ?_⟩
  · exact (((mv1_gfar_smooth (d := d) s).continuous_fderiv (by simp)).clm_apply
      continuous_const).aestronglyMeasurable
  · have h1 := hK i z
    have h2 : |movb2_kfar d s i z| ≤ K := by
      calc |movb2_kfar d s i z| = |movb2_kfar d s i z| * 1 := (mul_one _).symm
        _ ≤ |movb2_kfar d s i z| * (1 + ‖z‖) :=
          mul_le_mul_of_nonneg_left (by linarith [norm_nonneg z]) (abs_nonneg _)
        _ ≤ K := h1
    exact h2.trans (le_mul_of_one_le_right hK0 (movb2_Bs_ge_one z))

section Split

variable (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
include hd hs0 hsd

/-- Integration by parts moving the derivative from the profile onto the far kernel. -/
theorem movb2_ibp {c E : ℝ} (hc : 0 < c) {u : Euc d → ℝ} (hu : ContDiff ℝ 1 u)
    (hga : movb2_GA 1 c E u) (i : Fin d) (x : Euc d) :
    movb2_T (movb2_gfar d s) (fun y => fderiv ℝ u y (EuclideanSpace.single i 1)) x =
      movb2_T (movb2_kfar d s i) u x := by
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
  have hker := movb2_gfar_ker (d := d) (s := s) hd hs0 hsd
  have hkker := movb2_kfar_ker (d := d) (s := s) hs0 i
  have hk1 := movb2_T_integrable hd hs0 hsd hker hc hE huc h0 x
  have hk2 := movb2_T_integrable hd hs0 hsd hker hc (mul_nonneg hE (norm_nonneg v)) hwc hw0 x
  have hk3 := movb2_T_integrable hd hs0 hsd hkker hc hE huc h0 x
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure (Euc d)))
    (f := movb2_gfar d s) (g := fun z => u (x - z)) (v := v)
    (by
      refine hk3.congr (Filter.Eventually.of_forall fun z => ?_)
      rfl)
    (by
      refine hk2.neg.congr (Filter.Eventually.of_forall fun z => ?_)
      simp [(hgdiff z).fderiv])
    hk1
    (fun z _ => ((mv1_gfar_smooth (d := d) s).differentiable (by simp)) z)
    (fun z _ => (hgdiff z).differentiableAt)
  simp only [(hgdiff _).fderiv, neg_apply, mul_neg, integral_neg, neg_inj] at key
  simpa [movb2_T, movb2_kfar] using key

end Split

end HRS.MS.MovForce

end
