import HRS.MS.SA12Z3NearN4C
import HRS.MS.UniqN0b
import HRS.MS.UniqN3cB

/-!
# S.A.12 N4 (SA12Z3), part D: the difference identity at fixed smoothing

`Q_ε v = ∫ D_ε(x-y) v(y) dy` is `C¹` with `∂_l Q_ε v = Q_ε ∂_l v` for `v ∈ C¹_c`; and for `Z ∈ C²_c`, `a ∈ C¹`:
`S_ε(∂_lZ a, ∂_jZ) - S_ε(∂_jZ a, ∂_lZ) = S_ε(Z ∂_ja, ∂_lZ) - S_ε(Z ∂_la, ∂_jZ)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqT3

variable {d : ℕ}

/-- `Q_ε v (x) = ∫ D_ε(x-y) v(y) dy`. -/
def sa12z3_Q (d : ℕ) (s : ℝ) (i : Fin d) (ε : ℝ) (v : Euc d → ℝ) (x : Euc d) : ℝ :=
  ∫ y, movtr_dEps d s ε (EuclideanSpace.single i (1 : ℝ)) (x - y) * v y

theorem sa12z3_S_eq_int (s : ℝ) (i : Fin d) {ε : ℝ} (hε : 0 < ε) {u v : Euc d → ℝ} (hu : Continuous u)
    (huc : HasCompactSupport u) (hv : Continuous v) (hvc : HasCompactSupport v) :
    sa12z3_S d s i ε u v = ∫ x, u x * sa12z3_Q d s i ε v x := by
  have hI := sa12z3_prod_integrable s i hε hu huc hv hvc
  unfold sa12z3_S
  refine (integral_prod _ hI).trans ?_
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [sa12z3_Q]
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [mul_assoc]

theorem sa12z3_Q_conv (s : ℝ) (i : Fin d) (ε : ℝ) (v : Euc d → ℝ) :
    sa12z3_Q d s i ε v = (fun z => movtr_dEps d s ε (EuclideanSpace.single i (1 : ℝ)) z) ⋆[
      ContinuousLinearMap.mul ℝ ℝ, volume] v := by
  funext x
  have h := integral_sub_left_eq_self (μ := volume)
    (fun t => movtr_dEps d s ε (EuclideanSpace.single i (1 : ℝ)) t * v (x - t)) x
  simp only [sub_sub_cancel] at h
  simpa [convolution_def, sa12z3_Q] using h

theorem sa12z3_Q_contDiff (s : ℝ) (i : Fin d) {ε : ℝ} (hε : 0 < ε) {v : Euc d → ℝ}
    (hv : ContDiff ℝ 1 v) (hvc : HasCompactSupport v) : ContDiff ℝ 1 (sa12z3_Q d s i ε v) := by
  rw [sa12z3_Q_conv]
  exact hvc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    (sa12z2_dEps_cont (d := d) s hε i).locallyIntegrable hv

theorem sa12z3_Q_deriv (s : ℝ) (i : Fin d) {ε : ℝ} (hε : 0 < ε) {v : Euc d → ℝ}
    (hv : ContDiff ℝ 1 v) (hvc : HasCompactSupport v) (l : Fin d) (x : Euc d) :
    D1 l (sa12z3_Q d s i ε v) x = sa12z3_Q d s i ε (D1 l v) x := by
  have hK := (sa12z2_dEps_cont (d := d) s hε i).locallyIntegrable
    (μ := (volume : Measure (Euc d)))
  have hconv := hvc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hK hv x
  have hint : Integrable (fun t => (ContinuousLinearMap.mul ℝ ℝ).precompR (Euc d)
      (movtr_dEps d s ε (EuclideanSpace.single i (1 : ℝ)) t) (fderiv ℝ v (x - t))) := by
    have := (hvc.fderiv ℝ).convolutionExists_right ((ContinuousLinearMap.mul ℝ ℝ).precompR (Euc d))
      hK (hv.continuous_fderiv (by norm_num)) x
    exact this
  unfold D1
  rw [sa12z3_Q_conv, hconv.fderiv, convolution_def]
  show (∫ t, (ContinuousLinearMap.mul ℝ ℝ).precompR (Euc d)
      (movtr_dEps d s ε (EuclideanSpace.single i (1 : ℝ)) t)
      (fderiv ℝ v (x - t)) ∂volume) (EuclideanSpace.single l (1 : ℝ)) = _
  rw [ContinuousLinearMap.integral_apply hint]
  have key : ∀ t, (ContinuousLinearMap.mul ℝ ℝ).precompR (Euc d)
      (movtr_dEps d s ε (EuclideanSpace.single i (1 : ℝ)) t) (fderiv ℝ v (x - t))
        (EuclideanSpace.single l (1 : ℝ)) =
      movtr_dEps d s ε (EuclideanSpace.single i (1 : ℝ)) t * D1 l v (x - t) := by
    intro t
    simp [ContinuousLinearMap.precompR, D1]
  simp_rw [key]
  unfold sa12z3_Q
  have h := integral_sub_left_eq_self (μ := volume)
    (fun t => movtr_dEps d s ε (EuclideanSpace.single i (1 : ℝ)) t * D1 l v (x - t)) x
  simp only [sub_sub_cancel] at h
  exact h.symm

theorem sa12z3_diff_eps (s : ℝ) (i : Fin d) {ε : ℝ} (hε : 0 < ε) {Z a : Euc d → ℝ}
    (hZ : ContDiff ℝ 2 Z) (hZc : HasCompactSupport Z) (ha : ContDiff ℝ 1 a) (l j : Fin d) :
    sa12z3_S d s i ε (fun x => D1 l Z x * a x) (D1 j Z) -
        sa12z3_S d s i ε (fun x => D1 j Z x * a x) (D1 l Z) =
      sa12z3_S d s i ε (fun x => Z x * D1 j a x) (D1 l Z) -
        sa12z3_S d s i ε (fun x => Z x * D1 l a x) (D1 j Z) := by
  have hf : ∀ k, ContDiff ℝ 1 (D1 k Z) := fun k => D1_contDiff hZ k
  have hfc : ∀ k, HasCompactSupport (D1 k Z) := fun k => D1_supp hZc k
  have hQ : ∀ k, ContDiff ℝ 1 (sa12z3_Q d s i ε (D1 k Z)) := fun k =>
    sa12z3_Q_contDiff s i hε (hf k) (hfc k)
  have ha2 : ∀ k, Continuous (D1 k a) := fun k => (ha.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hac := ha.continuous
  have hDQ : ∀ k k', Continuous (D1 k (sa12z3_Q d s i ε (D1 k' Z))) := fun k k' =>
    ((hQ k').continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hint : ∀ {G : Euc d → ℝ}, Continuous G → Integrable (fun t => G t * Z t) volume :=
    fun {G} hG => Continuous.integrable_of_hasCompactSupport (f := fun t => G t * Z t)
      (hG.mul hZ.continuous) hZc.mul_left
  have hcQ : ∀ k, Continuous (sa12z3_Q d s i ε (D1 k Z)) := fun k => (hQ k).continuous
  -- integration by parts
  have hibp : ∀ k k' : Fin d, ∫ t, (D1 k Z t * a t) * sa12z3_Q d s i ε (D1 k' Z) t =
      -((∫ t, (D1 k a t * sa12z3_Q d s i ε (D1 k' Z) t) * Z t) +
        ∫ t, (a t * D1 k (sa12z3_Q d s i ε (D1 k' Z)) t) * Z t) := by
    intro k k'
    have h1 := HRS.MS.UniqN0.n0_ibp (F := Z) (k := fun t => a t * sa12z3_Q d s i ε (D1 k' Z) t)
      (hZ.of_le (by norm_num)) hZc (fun t _ => (ha.mul (hQ k')).contDiffAt) (EuclideanSpace.single k (1 : ℝ))
    have e1 : ∀ t, (D1 k Z t * a t) * sa12z3_Q d s i ε (D1 k' Z) t =
        (a t * sa12z3_Q d s i ε (D1 k' Z) t) * fderiv ℝ Z t (EuclideanSpace.single k (1 : ℝ)) := by
      intro t; unfold D1; ring
    simp_rw [e1]
    rw [h1]
    have e2 : ∀ t, fderiv ℝ (fun t => a t * sa12z3_Q d s i ε (D1 k' Z) t) t (EuclideanSpace.single k (1 : ℝ)) =
        D1 k a t * sa12z3_Q d s i ε (D1 k' Z) t + a t * D1 k (sa12z3_Q d s i ε (D1 k' Z)) t := by
      intro t
      rw [fderiv_fun_mul (ha.differentiable one_ne_zero t) ((hQ k').differentiable one_ne_zero t)]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, D1]
      ring
    simp_rw [e2]
    have hI1 : Integrable (fun t => D1 k a t * sa12z3_Q d s i ε (D1 k' Z) t * Z t) volume :=
      hint (G := fun t => D1 k a t * sa12z3_Q d s i ε (D1 k' Z) t) ((ha2 k).mul (hcQ k'))
    have hI2 : Integrable (fun t => a t * D1 k (sa12z3_Q d s i ε (D1 k' Z)) t * Z t) volume :=
      hint (G := fun t => a t * D1 k (sa12z3_Q d s i ε (D1 k' Z)) t) (hac.mul (hDQ k k'))
    rw [neg_inj, ← integral_add hI1 hI2]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    ring
  -- symmetry of the second derivative
  have hsym : ∀ t, D1 l (sa12z3_Q d s i ε (D1 j Z)) t = D1 j (sa12z3_Q d s i ε (D1 l Z)) t := by
    intro t
    rw [sa12z3_Q_deriv s i hε (hf j) (hfc j) l t, sa12z3_Q_deriv s i hε (hf l) (hfc l) j t]
    have : D1 l (D1 j Z) = D1 j (D1 l Z) := funext fun x => HRS.MS.UniqN3c.n3c_hess_symm hZ l j x |>.symm
    rw [this]
  rw [sa12z3_S_eq_int s i hε (u := fun x => D1 l Z x * a x) ((hf l).continuous.mul hac)
      ((hfc l).mul_right) (hf j).continuous (hfc j),
    sa12z3_S_eq_int s i hε (u := fun x => D1 j Z x * a x) ((hf j).continuous.mul hac)
      ((hfc j).mul_right) (hf l).continuous (hfc l),
    sa12z3_S_eq_int s i hε (u := fun x => Z x * D1 j a x) (hZ.continuous.mul (ha2 j))
      (hZc.mul_right) (hf l).continuous (hfc l),
    sa12z3_S_eq_int s i hε (u := fun x => Z x * D1 l a x) (hZ.continuous.mul (ha2 l))
      (hZc.mul_right) (hf j).continuous (hfc j),
    hibp l j, hibp j l]
  have e3 : ∫ t, (a t * D1 l (sa12z3_Q d s i ε (D1 j Z)) t) * Z t =
      ∫ t, (a t * D1 j (sa12z3_Q d s i ε (D1 l Z)) t) * Z t :=
    integral_congr_ae (Eventually.of_forall fun t => by simp only [hsym t])
  have e4 : ∫ t, Z t * D1 j a t * sa12z3_Q d s i ε (D1 l Z) t =
      ∫ t, (D1 j a t * sa12z3_Q d s i ε (D1 l Z) t) * Z t :=
    integral_congr_ae (Eventually.of_forall fun t => by ring)
  have e5 : ∫ t, Z t * D1 l a t * sa12z3_Q d s i ε (D1 j Z) t =
      ∫ t, (D1 l a t * sa12z3_Q d s i ε (D1 j Z) t) * Z t :=
    integral_congr_ae (Eventually.of_forall fun t => by ring)
  rw [e3, e4, e5]
  ring

end HRS.MH.AdjointRd.Phase2SA12Near
