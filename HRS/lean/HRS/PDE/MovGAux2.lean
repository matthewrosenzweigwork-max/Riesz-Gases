import HRS.PDE.MovGAux1

/-!
# MOVG Aux2: integration by parts on the torus against the slice weight `wt(x) = ∏_k Ga(x - Y_k) e^{b(x)}`

`movg_slice_ibp`: for `a > 0`, points `Y_1..Y_n`, `b ∈ C¹`, `V ∈ C¹` vector field:
`∫ ∑_j (∂_jV_j wt + V_j wt (-a ∑_k ∂_jg(x-Y_k) + ∂_jb)) = 0`  (from `movf_libp`, MovFAux16).
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

def movg_wt (d : ℕ) (s a : ℝ) {n : ℕ} (Y : Fin n → Torus d) (b : Torus d → ℝ) (x : Torus d) : ℝ :=
  (∏ k, movg_Ga d s a (x - Y k)) * Real.exp (b x)

def movg_H (d : ℕ) (s a : ℝ) {n : ℕ} (Y : Fin n → Torus d) (b : Torus d → ℝ) (y : Euc d) : ℝ :=
  -a * ∑ k, Torus.lift (periodicRiesz d s) (y - Torus.rep (Y k)) + Torus.lift b y

variable {s a : ℝ} {n : ℕ} {Y : Fin n → Torus d} {b : Torus d → ℝ}

theorem movg_wt_lift_eq {y : Euc d} (hy : ∀ k, Torus.mk y ≠ Y k) :
    ∀ᶠ y' in 𝓝 y, Torus.lift (movg_wt d s a Y b) y' = Real.exp (movg_H d s a Y b y') := by
  have hopen : ∀ᶠ y' in 𝓝 y, ∀ k, Torus.mk y' ≠ Y k := by
    rw [Filter.eventually_all]
    intro k
    exact (Torus.continuous_mk.continuousAt (x := y)).eventually (isOpen_ne.mem_nhds (hy k))
  filter_upwards [hopen] with y' hy'
  unfold movg_wt movg_H Torus.lift
  simp only [Function.comp]
  have h1 : ∀ k, movg_Ga d s a (Torus.mk y' - Y k) = Real.exp (-a * periodicRiesz d s (Torus.mk (y' - Torus.rep (Y k)))) := by
    intro k
    rw [movg_Ga_of_ne (sub_ne_zero.2 (hy' k)), movg_mk_sub, Torus.mk_rep]
  simp_rw [h1]
  rw [← Real.exp_sum, ← Real.exp_add, Finset.mul_sum]

theorem movg_lift_g_contDiffAt (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {y : Euc d} {c : Euc d}
    (hy : Torus.mk (y - c) ≠ 0) :
    ContDiffAt ℝ 1 (fun y' => Torus.lift (periodicRiesz d s) (y' - c)) y := by
  have h : ContDiffAt ℝ 1 (Torus.lift (periodicRiesz d s)) ((fun y' : Euc d => y' - c) y) :=
    (b15c_contDiffAt_lift_periodicRiesz hd hs0 hsd hy).of_le (by norm_cast)
  exact ContDiffAt.comp (g := Torus.lift (periodicRiesz d s)) (f := fun y' : Euc d => y' - c) y h
    (contDiffAt_id.sub contDiffAt_const)

theorem movg_H_contDiffAt (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hb : Torus.IsCk 1 b) {y : Euc d}
    (hy : ∀ k, Torus.mk y ≠ Y k) : ContDiffAt ℝ 1 (movg_H d s a Y b) y := by
  unfold movg_H
  refine ContDiffAt.add (ContDiffAt.mul contDiffAt_const (ContDiffAt.sum fun k _ => ?_)) hb.contDiffAt
  refine movg_lift_g_contDiffAt hd hs0 hsd ?_
  rw [movg_mk_sub, Torus.mk_rep]
  exact sub_ne_zero.2 (hy k)

theorem movg_wt_contDiffAt (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hb : Torus.IsCk 1 b) {y : Euc d}
    (hy : ∀ k, Torus.mk y ≠ Y k) : ContDiffAt ℝ 1 (Torus.lift (movg_wt d s a Y b)) y := by
  have h := (Real.contDiff_exp.contDiffAt (x := movg_H d s a Y b y)).comp y (movg_H_contDiffAt hd hs0 hsd hb hy)
  exact h.congr_of_eventuallyEq (movg_wt_lift_eq hy)

theorem movg_wt_partialDeriv (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hb : Torus.IsCk 1 b) (j : Fin d)
    {x : Torus d} (hx : ∀ k, x ≠ Y k) :
    Torus.partialDeriv j (movg_wt d s a Y b) x =
      movg_wt d s a Y b x * (-a * ∑ k, (periodicRieszGrad d s (x - Y k)).ofLp j + Torus.partialDeriv j b x) := by
  set y := Torus.rep x with hydef
  have hmk : Torus.mk y = x := Torus.mk_rep x
  have hyk : ∀ k, Torus.mk y ≠ Y k := fun k => by rw [hmk]; exact hx k
  have hev := movg_wt_lift_eq (s := s) (a := a) (b := b) hyk
  have hwt : movg_wt d s a Y b x = Real.exp (movg_H d s a Y b y) := by
    have := hev.self_of_nhds
    simpa [Torus.lift, hmk] using this
  -- derivative of `H`
  have hg : ∀ k, HasFDerivAt (fun y' : Euc d => Torus.lift (periodicRiesz d s) (y' - Torus.rep (Y k)))
      (fderiv ℝ (Torus.lift (periodicRiesz d s)) (y - Torus.rep (Y k))) y := by
    intro k
    have hne : Torus.mk (y - Torus.rep (Y k)) ≠ 0 := by
      rw [movg_mk_sub, Torus.mk_rep (Y k)]; exact sub_ne_zero.2 (hyk k)
    have hd1 : DifferentiableAt ℝ (Torus.lift (periodicRiesz d s)) (y - Torus.rep (Y k)) :=
      (b15c_contDiffAt_lift_periodicRiesz hd hs0 hsd hne).differentiableAt (by simp)
    have := hd1.hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const (Torus.rep (Y k)))
    convert this using 1
    · rfl
    · simp
  have hbd : HasFDerivAt (Torus.lift b) (fderiv ℝ (Torus.lift b) y) y :=
    (hb.differentiable (by norm_num) y).hasFDerivAt
  have hH : HasFDerivAt (movg_H d s a Y b)
      ((-a) • ∑ k, fderiv ℝ (Torus.lift (periodicRiesz d s)) (y - Torus.rep (Y k)) + fderiv ℝ (Torus.lift b) y) y := by
    unfold movg_H
    refine HasFDerivAt.add (HasFDerivAt.const_mul (HasFDerivAt.fun_sum fun k _ => hg k) (-a)) hbd
  have hE := (Real.hasDerivAt_exp (movg_H d s a Y b y)).comp_hasFDerivAt y hH
  have hfd : fderiv ℝ (Torus.lift (movg_wt d s a Y b)) y =
      Real.exp (movg_H d s a Y b y) • ((-a) • ∑ k, fderiv ℝ (Torus.lift (periodicRiesz d s)) (y - Torus.rep (Y k)) +
        fderiv ℝ (Torus.lift b) y) := by
    have h1 : fderiv ℝ (Torus.lift (movg_wt d s a Y b)) y = fderiv ℝ (fun y' => Real.exp (movg_H d s a Y b y')) y :=
      Filter.EventuallyEq.fderiv_eq hev
    rw [h1]
    exact hE.fderiv
  have hLk : ∀ k, fderiv ℝ (Torus.lift (periodicRiesz d s)) (y - Torus.rep (Y k)) (EuclideanSpace.single j 1) =
      (periodicRieszGrad d s (x - Y k)).ofLp j := by
    intro k
    have hz : x - Y k ≠ 0 := sub_ne_zero.2 (hx k)
    calc _ = Torus.partialDeriv j (periodicRiesz d s) (Torus.mk (y - Torus.rep (Y k))) :=
          (movg_partialDeriv_mk j _ _).symm
      _ = Torus.partialDeriv j (periodicRiesz d s) (x - Y k) := by
          rw [movg_mk_sub, hmk, Torus.mk_rep (Y k)]
      _ = (Torus.grad (periodicRiesz d s) (x - Y k)).ofLp j := (mova_grad_apply _ _ _).symm
      _ = _ := by rw [b15c_periodicRieszGrad_eq_grad hd hs0 hsd hz]
  unfold Torus.partialDeriv
  rw [← hydef, hfd, ← hwt]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
    smul_eq_mul, hLk]

theorem movg_ae_ne (hd : 1 ≤ d) (p : Torus d) : ∀ᵐ x : Torus d, x ≠ p := by
  rw [ae_iff]
  simpa using volume_singleton_torus hd p

theorem movg_ae_notMem (hd : 1 ≤ d) (Y : Fin n → Torus d) : ∀ᵐ x : Torus d, ∀ k, x ≠ Y k := by
  rw [ae_all_iff]
  exact fun k => movg_ae_ne hd (Y k)

theorem movg_wt_continuous (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (ha : 0 < a) (hb : Continuous b) :
    Continuous (movg_wt d s a Y b) :=
  (continuous_finset_prod _ fun k _ => (movg_Ga_continuous hd hs0 hsd ha).comp
    (continuous_id.sub continuous_const)).mul (Real.continuous_exp.comp hb)

theorem movg_wt_nonneg (x : Torus d) : 0 ≤ movg_wt d s a Y b x :=
  mul_nonneg (Finset.prod_nonneg fun k _ => movg_Ga_nonneg s a _) (Real.exp_pos _).le

theorem movg_wt_eq_zero (k : Fin n) : movg_wt d s a Y b (Y k) = 0 := by
  unfold movg_wt
  rw [Finset.prod_eq_zero (Finset.mem_univ k) (by rw [sub_self, movg_Ga_zero]), zero_mul]

theorem movg_wt_pos {x : Torus d} (hx : ∀ k, x ≠ Y k) : 0 < movg_wt d s a Y b x :=
  mul_pos (Finset.prod_pos fun k _ => movg_Ga_pos (sub_ne_zero.2 (hx k))) (Real.exp_pos _)

theorem movg_wt_le (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (ha : 0 < a) {Cb : ℝ}
    (hCb : ∀ x, Real.exp (b x) ≤ Cb) (k : Fin n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Torus d, movg_wt d s a Y b x ≤ C * movg_Ga d s a (x - Y k) := by
  obtain ⟨B, hB⟩ := periodicRiesz_ge_of_one_le (d := d) hd hs0 hsd
  set CG := Real.exp (a * B) with hCG
  have hCG0 : 0 ≤ CG := (Real.exp_pos _).le
  have hCb0 : 0 ≤ Cb := (Real.exp_pos _).le.trans (hCb 0)
  refine ⟨CG ^ (Finset.univ.erase k).card * Cb, by positivity, fun x => ?_⟩
  unfold movg_wt
  rw [← Finset.mul_prod_erase Finset.univ (fun l => movg_Ga d s a (x - Y l)) (Finset.mem_univ k)]
  have h1 : ∏ l ∈ Finset.univ.erase k, movg_Ga d s a (x - Y l) ≤ CG ^ (Finset.univ.erase k).card := by
    calc _ ≤ ∏ l ∈ Finset.univ.erase k, CG := Finset.prod_le_prod₀ (fun l _ => movg_Ga_nonneg s a _)
          (fun l _ => movg_Ga_le ha.le hB _)
      _ = _ := by rw [Finset.prod_const]
  have h2 := hCb x
  have hG0 := movg_Ga_nonneg s a (x - Y k)
  have hP0 : 0 ≤ ∏ l ∈ Finset.univ.erase k, movg_Ga d s a (x - Y l) :=
    Finset.prod_nonneg fun l _ => movg_Ga_nonneg s a _
  calc movg_Ga d s a (x - Y k) * (∏ l ∈ Finset.univ.erase k, movg_Ga d s a (x - Y l)) * Real.exp (b x)
      ≤ movg_Ga d s a (x - Y k) * CG ^ (Finset.univ.erase k).card * Cb := by
        gcongr
    _ = _ := by ring

theorem movg_wt_G_integrable (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (ha : 0 < a) (hb : Torus.IsCk 1 b)
    (k : Fin n) (j : Fin d) :
    Integrable (fun x => movg_wt d s a Y b x * (periodicRieszGrad d s (x - Y k)).ofLp j) := by
  have hbc : Continuous b := mova_continuous_of_isCk hb
  obtain ⟨Cb, -, hCb0⟩ := mova_bound_of_continuous (Real.continuous_exp.comp hbc)
  have hCb : ∀ x, Real.exp (b x) ≤ Cb := fun x => (le_abs_self _).trans (hCb0 x)
  obtain ⟨C, hC0, hC⟩ := movg_wt_le (Y := Y) hd hs0 hsd ha hCb k
  have hdom : Integrable (fun x : Torus d => C * (movg_Ga d s a (x - Y k) * ‖periodicRieszGrad d s (x - Y k)‖)) :=
    ((movg_Ga_grad_integrable hd hs0 hsd ha).comp_sub_right (Y k)).const_mul C
  have hGm : Measurable (periodicRieszGrad d s : Torus d → Euc d) := KernelGrad.measurable_periodicRieszGrad hsd
  have hwm : Measurable (movg_wt d s a Y b) := (movg_wt_continuous hd hs0 hsd ha hbc).measurable
  refine hdom.mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (hwm.mul (((measurable_pi_apply j).comp (WithLp.measurable_ofLp (p := 2) (X := Fin d → ℝ))).comp
      (hGm.comp (measurable_id.sub measurable_const)))).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (movg_wt_nonneg x)]
    calc movg_wt d s a Y b x * |(periodicRieszGrad d s (x - Y k)).ofLp j|
        ≤ (C * movg_Ga d s a (x - Y k)) * ‖periodicRieszGrad d s (x - Y k)‖ :=
          mul_le_mul (hC x) (by simpa using PiLp.norm_apply_le (periodicRieszGrad d s (x - Y k)) j)
            (abs_nonneg _) (mul_nonneg hC0 (movg_Ga_nonneg s a _))
      _ = _ := by ring

theorem movg_force_integrable (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (ha : 0 < a) (hb : Torus.IsCk 1 b)
    (j : Fin d) :
    Integrable (fun x => movg_wt d s a Y b x *
        (-a * ∑ k, (periodicRieszGrad d s (x - Y k)).ofLp j + Torus.partialDeriv j b x)) := by
  have hbc : Continuous b := mova_continuous_of_isCk hb
  have e : (fun x => movg_wt d s a Y b x *
      (-a * ∑ k, (periodicRieszGrad d s (x - Y k)).ofLp j + Torus.partialDeriv j b x)) =
      fun x => ∑ k, (-a) * (movg_wt d s a Y b x * (periodicRieszGrad d s (x - Y k)).ofLp j) +
        movg_wt d s a Y b x * Torus.partialDeriv j b x := by
    funext x
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e]
  refine (integrable_finsetSum _ fun k _ => (movg_wt_G_integrable hd hs0 hsd ha hb k j).const_mul (-a)).add ?_
  exact mova_int_cont ((movg_wt_continuous hd hs0 hsd ha hbc).mul (mova_continuous_partialDeriv hb j))

theorem movg_slice_ibp (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (ha : 0 < a) (hb : Torus.IsCk 1 b)
    {V : Fin d → Torus d → ℝ} (hV : ∀ j, Torus.IsCk 1 (V j)) :
    ∫ x, ∑ j, (Torus.partialDeriv j (V j) x * movg_wt d s a Y b x +
        V j x * (movg_wt d s a Y b x * (-a * ∑ k, (periodicRieszGrad d s (x - Y k)).ofLp j +
          Torus.partialDeriv j b x))) = 0 := by
  classical
  have hbc : Continuous b := mova_continuous_of_isCk hb
  set S : Finset (Torus d) := Finset.univ.image Y with hS
  have hSmem : ∀ x, x ∉ S ↔ ∀ k, x ≠ Y k := by
    intro x; simp only [hS, Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    exact forall_congr' fun k => ⟨fun h h' => h h'.symm, fun h h' => h h'.symm⟩
  have hint : ∀ j, Integrable (Torus.partialDeriv j (movg_wt d s a Y b)) := by
    intro j
    refine (movg_force_integrable (Y := Y) hd hs0 hsd ha hb j).congr ?_
    filter_upwards [movg_ae_notMem hd Y] with x hx
    exact (movg_wt_partialDeriv hd hs0 hsd hb j hx).symm
  have h0 := movf_libp (S := S) (Y := V) hd (movg_wt_continuous hd hs0 hsd ha hbc)
    (fun x => movg_wt_nonneg x)
    (fun x hx => by
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hx
      exact movg_wt_eq_zero k)
    (fun x hx => movg_wt_pos ((hSmem x).1 hx))
    (fun y hy => movg_wt_contDiffAt hd hs0 hsd hb ((hSmem _).1 hy)) hV hint
  rw [← h0]
  refine integral_congr_ae ?_
  filter_upwards [movg_ae_notMem hd Y] with x hx
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [movg_wt_partialDeriv hd hs0 hsd hb j hx]

/-- The same identity in the form used for the configuration slices:
`∫ wt · div V = ∫ wt ∑_j V_j (a ∑_k ∂_jg(x - Y_k) - ∂_jb)`. -/
theorem movg_slice_ibp' (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (ha : 0 < a) (hb : Torus.IsCk 1 b)
    {V : Fin d → Torus d → ℝ} (hV : ∀ j, Torus.IsCk 1 (V j)) :
    ∫ x, (∑ j, Torus.partialDeriv j (V j) x) * movg_wt d s a Y b x =
      ∫ x, movg_wt d s a Y b x * ∑ j, V j x * (a * ∑ k, (periodicRieszGrad d s (x - Y k)).ofLp j -
        Torus.partialDeriv j b x) := by
  have h0 := movg_slice_ibp (Y := Y) hd hs0 hsd ha hb hV
  have hVc : ∀ j, Continuous (V j) := fun j => mova_continuous_of_isCk (hV j)
  have hdVc : ∀ j, Continuous (Torus.partialDeriv j (V j)) := fun j => mova_continuous_partialDeriv (hV j) j
  have hwc := movg_wt_continuous (Y := Y) hd hs0 hsd ha (mova_continuous_of_isCk hb)
  have hA : Integrable (fun x => ∑ j, Torus.partialDeriv j (V j) x * movg_wt d s a Y b x) :=
    mova_int_cont (continuous_finsetSum _ fun j _ => (hdVc j).mul hwc)
  have hB : Integrable (fun x => ∑ j, V j x * (movg_wt d s a Y b x * (-a * ∑ k,
      (periodicRieszGrad d s (x - Y k)).ofLp j + Torus.partialDeriv j b x))) := by
    refine integrable_finsetSum _ fun j _ => ?_
    obtain ⟨C, -, hC⟩ := mova_bound_of_continuous (hVc j)
    exact (movg_force_integrable hd hs0 hsd ha hb j).bdd_mul (hVc j).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simpa using hC x)
  have h1 : (∫ x, ∑ j, Torus.partialDeriv j (V j) x * movg_wt d s a Y b x) +
      ∫ x, ∑ j, V j x * (movg_wt d s a Y b x * (-a * ∑ k,
        (periodicRieszGrad d s (x - Y k)).ofLp j + Torus.partialDeriv j b x)) = 0 := by
    rw [← integral_add hA hB, ← h0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Finset.sum_add_distrib]
  have h2 : ∫ x, movg_wt d s a Y b x * ∑ j, V j x * (a * ∑ k, (periodicRieszGrad d s (x - Y k)).ofLp j -
        Torus.partialDeriv j b x) = -∫ x, ∑ j, V j x * (movg_wt d s a Y b x * (-a * ∑ k,
          (periodicRieszGrad d s (x - Y k)).ofLp j + Torus.partialDeriv j b x)) := by
    rw [← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h3 : ∫ x, (∑ j, Torus.partialDeriv j (V j) x) * movg_wt d s a Y b x =
      ∫ x, ∑ j, Torus.partialDeriv j (V j) x * movg_wt d s a Y b x := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Finset.sum_mul]
  rw [h2, h3]
  linarith

end HRS
