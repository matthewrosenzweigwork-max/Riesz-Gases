import HRS.MS.MfeConfAux18

/-!
# S.B.1 (alternative (ii)): the quadratic potential `V = ½⟨x,Qx⟩ + ⟨b,x⟩ + c`

* `sb1_pot_quad`: `V ∈ C³` (indeed `C^∞`) with constant second derivative, i.e. `Sb1Pot V B` for some `B`;
* `sb1_quad_lower`: `⟨x,Qx⟩ ≥ q‖x‖²` for `Q - qI ⪰ 0`;
* `sb1_quad_confining`: hence `V ≥ (q/4)‖x‖² - (‖b‖²/q - c)`, the confinement used by the second moment (`sb1_init_moment`).
So the classical regularity (`sb1_traj_classical`), the regularised flow and the initial moment apply to the sub row verbatim.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d : ℕ}

theorem sb1_pot_quad (Q : Matrix (Fin d) (Fin d) ℝ) (b : Euc d) (c : ℝ) {V : Euc d → ℝ}
    (hV : ∀ x, V x = (1 / 2) * inner ℝ x (Torus.matVec Q x) + inner ℝ b x + c) :
    ∃ B : ℝ, Sb1Pot V B := by
  set T : Euc d →L[ℝ] Euc d := LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin Q) with hT
  have hTx : ∀ x, Torus.matVec Q x = T x := fun x => rfl
  have hV' : V = fun x => (1 / 2) * inner ℝ x (T x) + inner ℝ b x + c := funext fun x => by
    rw [hV x, hTx]
  set A : Euc d →L[ℝ] (Euc d →L[ℝ] ℝ) := (1 / 2 : ℝ) • ((innerSL ℝ).comp T +
    ((ContinuousLinearMap.compL ℝ (Euc d) (Euc d) ℝ).flip T).comp (innerSL ℝ)) with hA
  have hAx : ∀ x, A x = (1 / 2 : ℝ) • (innerSL ℝ (T x) + (innerSL ℝ x).comp T) := fun x => by
    simp [hA]
  have hder : ∀ x, HasFDerivAt V (A x + innerSL ℝ b) x := by
    intro x
    have h1 : HasFDerivAt (fun y : Euc d => inner ℝ y (T y))
        (innerSL ℝ (T x) + (innerSL ℝ x).comp T) x := by
      have := (hasFDerivAt_id x).inner ℝ (T.hasFDerivAt (x := x))
      refine this.congr_fderiv ?_
      ext v
      simp [fderivInnerCLM_apply, real_inner_comm]; ring
    have h2 : HasFDerivAt (fun y : Euc d => inner ℝ b y) (innerSL ℝ b) x := by
      simpa using (innerSL ℝ b).hasFDerivAt (x := x)
    rw [hV']
    have h3 := ((h1.const_mul (1 / 2 : ℝ)).add h2).add_const c
    refine h3.congr_fderiv ?_
    rw [hAx]
  have hfd : fderiv ℝ V = fun x => A x + innerSL ℝ b := funext fun x => (hder x).fderiv
  have hfdd : ∀ x, fderiv ℝ (fderiv ℝ V) x = A := fun x => by
    rw [hfd]
    exact (A.hasFDerivAt.add_const (innerSL ℝ b)).fderiv
  refine ⟨‖A‖, ?_, fun x => ?_⟩
  · rw [hV']
    have hT' : ContDiff ℝ 3 T := T.contDiff
    exact (((contDiff_const.mul (contDiff_id.inner ℝ (T.contDiff))).add
      (contDiff_const.inner ℝ contDiff_id)).add contDiff_const)
  · rw [← sb1_norm_fderiv_fderiv, hfdd]

theorem sb1_quad_lower (Q : Matrix (Fin d) (Fin d) ℝ) {q : ℝ}
    (hQq : (Q - q • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef) (x : Euc d) :
    q * ‖x‖ ^ 2 ≤ inner ℝ x (Torus.matVec Q x) := by
  have h := hQq.dotProduct_mulVec_nonneg x.ofLp
  have e : inner ℝ x (Torus.matVec Q x) = dotProduct x.ofLp (Q.mulVec x.ofLp) := by
    simp [Torus.matVec, Matrix.toEuclideanLin, Matrix.mulVec, PiLp.inner_apply, dotProduct, mul_comm]
  have e2 : ‖x‖ ^ 2 = dotProduct x.ofLp x.ofLp := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [dotProduct, sq]
  rw [e, e2]
  simp [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec] at h
  linarith

theorem sb1_quad_confining (Q : Matrix (Fin d) (Fin d) ℝ) (b : Euc d) (c : ℝ) {q : ℝ} (hq : 0 < q)
    (hQq : (Q - q • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef) {V : Euc d → ℝ}
    (hV : ∀ x, V x = (1 / 2) * inner ℝ x (Torus.matVec Q x) + inner ℝ b x + c) :
    ∃ cV CV : ℝ, 0 < cV ∧ ∀ x, cV * ‖x‖ ^ 2 - CV ≤ V x := by
  refine ⟨q / 4, ‖b‖ ^ 2 / q - c, by positivity, fun x => ?_⟩
  have h1 := sb1_quad_lower Q hQq x
  have h2 : -(‖b‖ * ‖x‖) ≤ inner ℝ b x := by
    have := abs_real_inner_le_norm b x
    linarith [neg_abs_le (inner ℝ b x)]
  have h3 : ‖b‖ * ‖x‖ ≤ q / 4 * ‖x‖ ^ 2 + ‖b‖ ^ 2 / q := by
    have : 0 ≤ (q * ‖x‖ - 2 * ‖b‖) ^ 2 / (4 * q) := by positivity
    have e : (q * ‖x‖ - 2 * ‖b‖) ^ 2 / (4 * q) = q / 4 * ‖x‖ ^ 2 + ‖b‖ ^ 2 / q - ‖b‖ * ‖x‖ := by
      field_simp; ring
    linarith
  rw [hV x]
  nlinarith

end HRS.MS.MfeConf
