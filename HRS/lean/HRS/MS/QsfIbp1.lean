import HRS.Whole.MovtrAux2
import HRS.MS.ThCorrDriftAux1
import HRS.MP.SelfSimP4Gibbs
import HRS.MS.ThmLogAux1

/-!
# S4.5 packet B2, part 1: the regularised Gibbs weight, its derivative, Gaussian domination

Namespace `S45`.  `g_ε` is the smoothed kernel `movtr_gEps` (`ε = 0` is the true kernel,
`movtr_gEps_zero`); `H_ε = ∑ V(x_i) + N⁻¹ ∑_{i<j} g_ε(x_i - x_j)`, `w_ε = e^{-β H_ε}`.  For `ε ≠ 0` the weight is
`C^∞` on `ℝ^{dN}`; its Fréchet derivative is `-β w_ε dH_ε` with the explicit pairing `s45_dH`.
Uniform in `ε ∈ (0,1]` the weight is dominated by `C e^{-(βa/4)‖X‖²}` (sup norm on `(ℝ^d)^N`).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace S45

open HRS.Whole
open HRS (Euc)

variable {d N : ℕ}

/-! ### Definitions -/

/-- `H_ε(X) = ∑_i a|x_i|²/2 + N⁻¹ ∑_{i<j} g_ε(x_i - x_j)`. -/
def s45_H (s a ε : ℝ) (X : EucConfig d N) : ℝ :=
  ∑ i, confinement a (X i) + (1 / (N : ℝ)) *
    ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), movtr_gEps d s ε (X i - X j)

theorem s45_H_zero (s a : ℝ) (X : EucConfig d N) :
    s45_H s a 0 X = canonicalHamiltonian (rieszKernel d s) (confinement a) X := by
  unfold s45_H canonicalHamiltonian
  rw [movtr_gEps_zero]

/-- The weight `w_ε = e^{-β H_ε}`. -/
def s45_w (s a β ε : ℝ) (X : EucConfig d N) : ℝ := Real.exp (-β * s45_H s a ε X)

theorem s45_w_zero (s a β : ℝ) (X : EucConfig d N) :
    s45_w s a β 0 X = Real.exp (-β * canonicalHamiltonian (rieszKernel d s) (confinement a) X) := by
  unfold s45_w
  rw [s45_H_zero]

theorem s45_w_pos (s a β ε : ℝ) (X : EucConfig d N) : 0 < s45_w s a β ε X := Real.exp_pos _

/-- The smoothed force `∇g_ε(z) = -(σ (|z|²+ε²)^{-s/2-1}) z`. -/
def s45_F (s ε : ℝ) (z : Euc d) : Euc d :=
  (-(movtr_sigma s * (‖z‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 1))) • z

/-- The derivative `dH_ε(X) : (ℝ^d)^N →L ℝ`. -/
def s45_dH (s a ε : ℝ) (X : EucConfig d N) : EucConfig d N →L[ℝ] ℝ :=
  (∑ i, (a • (innerSL ℝ (X i)).comp (ContinuousLinearMap.proj i : EucConfig d N →L[ℝ] Euc d))) +
    (1 / (N : ℝ)) • ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
      (innerSL ℝ (s45_F s ε (X i - X j))).comp
        ((ContinuousLinearMap.proj i : EucConfig d N →L[ℝ] Euc d) -
          (ContinuousLinearMap.proj j : EucConfig d N →L[ℝ] Euc d))

theorem s45_hasFDerivAt_gEps (s : ℝ) {ε : ℝ} (hε : ε ≠ 0) (z : Euc d) :
    HasFDerivAt (movtr_gEps d s ε) (innerSL ℝ (s45_F s ε z)) z := by
  have hu : 0 < ‖z‖ ^ 2 + ε ^ 2 := by positivity
  have h := movtr_gEps_hasFDerivAt (d := d) s ε z hu
  have e : innerSL ℝ (s45_F s ε z) =
      (-(movtr_sigma s * (‖z‖ ^ 2 + ε ^ 2) ^ (-s / 2 - 1))) • innerSL ℝ z := by
    unfold s45_F
    ext w
    simp
  rw [e]
  exact h

theorem s45_hasFDerivAt_H (s a : ℝ) {ε : ℝ} (hε : ε ≠ 0) (X : EucConfig d N) :
    HasFDerivAt (s45_H s a ε) (s45_dH s a ε X) X := by
  unfold s45_H s45_dH
  refine HasFDerivAt.add ?_ ?_
  · refine HasFDerivAt.fun_sum fun i _ => ?_
    have h := (HRS.MS.Tc1.tc1_hasFDeriv_conf a (X i)).comp X
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i).hasFDerivAt
    exact h
  · refine HasFDerivAt.const_mul ?_ _
    refine HasFDerivAt.fun_sum fun i _ => HasFDerivAt.fun_sum fun j _ => ?_
    have hL : HasFDerivAt (fun y : EucConfig d N => y i - y j)
        ((ContinuousLinearMap.proj i : EucConfig d N →L[ℝ] Euc d) -
          (ContinuousLinearMap.proj j : EucConfig d N →L[ℝ] Euc d)) X :=
      ((ContinuousLinearMap.proj i : EucConfig d N →L[ℝ] Euc d) -
          (ContinuousLinearMap.proj j : EucConfig d N →L[ℝ] Euc d)).hasFDerivAt
    exact (s45_hasFDerivAt_gEps s hε (X i - X j)).comp X hL

theorem s45_hasFDerivAt_w (s a β : ℝ) {ε : ℝ} (hε : ε ≠ 0) (X : EucConfig d N) :
    HasFDerivAt (s45_w s a β ε) ((-β * s45_w s a β ε X) • s45_dH s a ε X) X := by
  have h := ((s45_hasFDerivAt_H s a hε X).const_mul (-β)).exp
  have e : (-β * s45_w s a β ε X) • s45_dH s a ε X =
      Real.exp (-β * s45_H s a ε X) • (-β) • s45_dH s a ε X := by
    unfold s45_w
    rw [smul_smul]
    congr 1
    ring
  rw [e]
  exact h

theorem s45_differentiable_w (s a β : ℝ) {ε : ℝ} (hε : ε ≠ 0) :
    Differentiable ℝ (s45_w s a β ε : EucConfig d N → ℝ) :=
  fun X => (s45_hasFDerivAt_w s a β hε X).differentiableAt

theorem s45_fderiv_w (s a β : ℝ) {ε : ℝ} (hε : ε ≠ 0) (X : EucConfig d N) :
    fderiv ℝ (s45_w s a β ε) X = (-β * s45_w s a β ε X) • s45_dH s a ε X :=
  (s45_hasFDerivAt_w s a β hε X).fderiv

theorem s45_fderiv_H (s a : ℝ) {ε : ℝ} (hε : ε ≠ 0) (X : EucConfig d N) :
    fderiv ℝ (s45_H s a ε) X = s45_dH s a ε X :=
  (s45_hasFDerivAt_H s a hε X).fderiv

theorem s45_measurable_dH_apply (s a : ℝ) {ε : ℝ} (hε : ε ≠ 0) (e : EucConfig d N) :
    Measurable fun X : EucConfig d N => s45_dH s a ε X e := by
  have h : Measurable fun X : EucConfig d N => fderiv ℝ (s45_H s a ε) X e :=
    measurable_fderiv_apply_const ℝ (s45_H s a ε : EucConfig d N → ℝ) e
  have e' : (fun X : EucConfig d N => s45_dH s a ε X e) =
      fun X => fderiv ℝ (s45_H s a ε) X e := by
    funext X
    rw [s45_fderiv_H s a hε]
  rw [e']
  exact h

theorem s45_measurable_w (s a β ε : ℝ) : Measurable (s45_w s a β ε : EucConfig d N → ℝ) := by
  unfold s45_w s45_H
  refine Real.measurable_exp.comp (measurable_const.mul ?_)
  refine Finset.measurable_sum _ (fun i _ => ?_) |>.add (measurable_const.mul ?_)
  · unfold confinement
    exact ((measurable_norm.comp (measurable_pi_apply i)).pow_const 2).const_mul a |>.div_const 2
  · refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
    unfold movtr_gEps
    by_cases hs : s = 0
    · simp only [hs, ite_true]
      exact (Real.measurable_log.comp (((measurable_norm.comp
        ((measurable_pi_apply i).sub (measurable_pi_apply j))).pow_const 2).add_const _)).const_mul _
    · simp only [hs, ite_false]
      exact (((measurable_norm.comp
        ((measurable_pi_apply i).sub (measurable_pi_apply j))).pow_const 2).add_const _).pow_const _

/-! ### The sup norm bound and the lower bound of `H_ε` -/

theorem s45_norm_sq_le_sum (X : EucConfig d N) : ‖X‖ ^ 2 ≤ ∑ i, ‖X i‖ ^ 2 := by
  have h0 : 0 ≤ ∑ i, ‖X i‖ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have : ‖X‖ ≤ Real.sqrt (∑ i, ‖X i‖ ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
    refine Real.le_sqrt_of_sq_le ?_
    exact Finset.single_le_sum (f := fun i => ‖X i‖ ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ i)
  calc ‖X‖ ^ 2 ≤ Real.sqrt (∑ i, ‖X i‖ ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
    _ = ∑ i, ‖X i‖ ^ 2 := Real.sq_sqrt h0

theorem s45_card_pairs_le (N : ℕ) :
    ∑ i : Fin N, ((Finset.univ.filter fun j : Fin N => i < j).card : ℝ) ≤ (N : ℝ) * N := by
  have : ∀ i : Fin N, ((Finset.univ.filter fun j : Fin N => i < j).card : ℝ) ≤ N := by
    intro i
    exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
  calc _ ≤ ∑ _i : Fin N, (N : ℝ) := Finset.sum_le_sum fun i _ => this i
    _ = (N : ℝ) * N := by simp

theorem s45_H_lower {s : ℝ} {a : ℝ} (ha : 0 < a) (hN : 1 ≤ N) :
    ∃ c0 : ℝ, 0 ≤ c0 ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ X : EucConfig d N,
      (a / 4) * ‖X‖ ^ 2 - c0 ≤ s45_H s a ε X := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set δ : ℝ := a / (8 * N) with hδ
  have hδ0 : 0 < δ := by positivity
  set cδ : ℝ := δ - 1 - Real.log δ with hcδ
  have hcδ0 : 0 ≤ cδ := by
    have := Real.log_le_sub_one_of_pos hδ0
    linarith
  refine ⟨N * cδ / 2, by positivity, fun ε hε hε1 X => ?_⟩
  have hconf : (a / 2) * ‖X‖ ^ 2 ≤ ∑ i, confinement a (X i) := by
    unfold confinement
    calc (a / 2) * ‖X‖ ^ 2 ≤ (a / 2) * ∑ i, ‖X i‖ ^ 2 :=
          mul_le_mul_of_nonneg_left (s45_norm_sq_le_sum X) (by positivity)
      _ = ∑ i, a * ‖X i‖ ^ 2 / 2 := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; ring
  have hpair : -(N * cδ / 2) - (a / 4) * ‖X‖ ^ 2 ≤ (1 / (N : ℝ)) *
      ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), movtr_gEps d s ε (X i - X j) := by
    set m : ℝ := (1 / 2) * (4 * δ * ‖X‖ ^ 2 + cδ) with hm
    have hm0 : 0 ≤ m := by positivity
    have hterm : ∀ i j : Fin N, -m ≤ movtr_gEps d s ε (X i - X j) := by
      intro i j
      by_cases hs : s = 0
      · unfold movtr_gEps
        simp only [hs, ite_true]
        have hz : ‖X i - X j‖ ≤ 2 * ‖X‖ := by
          calc ‖X i - X j‖ ≤ ‖X i‖ + ‖X j‖ := norm_sub_le _ _
            _ ≤ ‖X‖ + ‖X‖ := add_le_add (norm_le_pi_norm X i) (norm_le_pi_norm X j)
            _ = 2 * ‖X‖ := by ring
        have h1 : Real.log (‖X i - X j‖ ^ 2 + ε ^ 2) ≤ Real.log (1 + ‖X i - X j‖ ^ 2) :=
          Real.log_le_log (by positivity) (by nlinarith)
        have h2 : Real.log (1 + ‖X i - X j‖ ^ 2) ≤ δ * ‖X i - X j‖ ^ 2 + cδ :=
          HRS.MS.Thm.t67l_le hδ0 (X i - X j)
        have h3 : ‖X i - X j‖ ^ 2 ≤ 4 * ‖X‖ ^ 2 := by
          nlinarith [norm_nonneg (X i - X j), norm_nonneg X]
        have h4 : δ * ‖X i - X j‖ ^ 2 ≤ δ * (4 * ‖X‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h3 hδ0.le
        rw [hm]
        nlinarith
      · unfold movtr_gEps
        simp only [hs, ite_false]
        have : 0 ≤ (‖X i - X j‖ ^ 2 + ε ^ 2) ^ (-s / 2) := Real.rpow_nonneg (by positivity) _
        linarith
    have hsum : -(m * ((N : ℝ) * N)) ≤ ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j),
        movtr_gEps d s ε (X i - X j) := by
      calc -(m * ((N : ℝ) * N)) ≤ -(m * ∑ i : Fin N, ((Finset.univ.filter fun j : Fin N => i < j).card : ℝ)) := by
            have := s45_card_pairs_le N
            nlinarith
        _ = ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), (-m) := by
            rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
            refine Finset.sum_congr rfl fun i _ => ?_
            simp [mul_comm]
        _ ≤ _ := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    have : (1 / (N : ℝ)) * (-(m * ((N : ℝ) * N))) ≤ (1 / (N : ℝ)) *
        ∑ i, ∑ j ∈ Finset.univ.filter (fun j => i < j), movtr_gEps d s ε (X i - X j) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    refine le_trans ?_ this
    have e : (1 / (N : ℝ)) * (-(m * ((N : ℝ) * N))) = -(N * m) := by field_simp
    rw [e, hm]
    have e2 : (N : ℝ) * ((1 / 2) * (4 * δ * ‖X‖ ^ 2 + cδ)) =
        (a / 4) * ‖X‖ ^ 2 + N * cδ / 2 := by
      rw [hδ]; field_simp; ring
    rw [e2]; linarith
  unfold s45_H
  linarith

theorem s45_w_le {s : ℝ} {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) (hN : 1 ≤ N) :
    ∃ Cw : ℝ, 0 ≤ Cw ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ X : EucConfig d N,
      s45_w s a β ε X ≤ Cw * Real.exp (-((β * a / 4) * ‖X‖ ^ 2)) := by
  obtain ⟨c0, hc0, h⟩ := s45_H_lower (d := d) (N := N) (s := s) ha hN
  refine ⟨Real.exp (β * c0), (Real.exp_pos _).le, fun ε hε hε1 X => ?_⟩
  unfold s45_w
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have := h ε hε hε1 X
  nlinarith

end S45

end
