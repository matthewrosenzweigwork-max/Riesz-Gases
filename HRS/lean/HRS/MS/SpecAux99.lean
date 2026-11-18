import HRS.MS.SpecAux98
import HRS.MS.SpecAux85

/-!
# S8M: translation of the spectral data to the hypotheses of `s8p_gradL4` (S8.7, R3)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  In the standard orthonormal basis `bb` of `Euc d` and `W = -log ρ`:
`L_W f = weightedLaplacian ρ f` (`s8p_Lw_eq_wlap`), the pointwise eigen-equation `L_W e = ω w` (`s8p_Lw_eig`),
and the differentiated inequality `Σ ∂_i e ∂_i(L_W e) ≤ λ N + λ √N ‖∇U‖` with `λ = ω β` (`s8p_hLe_pt`).
-/

noncomputable section

open MeasureTheory
open scoped ENNReal RealInnerProductSpace ContDiff

namespace HRS.MS.Spec

open HRS HRS.Whole HRS.MS.MovDec

variable {d : ℕ} {s : ℝ} {ρ : Euc d → ℝ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

/-- The standard orthonormal basis. -/
abbrev s8p_bb (d : ℕ) : OrthonormalBasis (Fin d) ℝ (Euc d) := EuclideanSpace.basisFun (Fin d) ℝ

theorem s8p_lap_eq (f : Euc d → ℝ) (x : Euc d) :
    s8p_lap (s8p_bb d) f x = Laplacian.laplacian f x := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f (s8p_bb d)]
  simp [s8p_lap, iteratedFDeriv_two_apply]

theorem s8p_Lw_eq_wlap (hρ : Mov2eRho d ρ) (e : Euc d → ℝ) (x : Euc d) :
    s8p_Lw (s8p_bb d) (fun y => -Real.log (ρ y)) e x = weightedLaplacian ρ e x := by
  unfold s8p_Lw weightedLaplacian
  rw [s8p_lap_eq]
  have hlog : DifferentiableAt ℝ (fun y => Real.log (ρ y)) x :=
    ((hρ.data.smooth.log fun y => (hρ.pos y).ne').differentiable (by simp)) x
  have h1 : ∀ j, fderiv ℝ (fun y => -Real.log (ρ y)) x (s8p_bb d j) = -inner ℝ (s8p_lgr ρ x) (s8p_bb d j) := by
    intro j
    rw [fderiv_fun_neg]
    simp only [ContinuousLinearMap.neg_apply]
    rw [s8p_fderiv_apply_grad]; rfl
  have h2 : ∀ j, fderiv ℝ e x (s8p_bb d j) = inner ℝ (gradient e x) (s8p_bb d j) := fun j =>
    s8p_fderiv_apply_grad e x _
  simp_rw [h1, h2]
  have h3 : ∑ j, -inner ℝ (s8p_lgr ρ x) (s8p_bb d j) * inner ℝ (gradient e x) (s8p_bb d j) =
      -inner ℝ (gradient (fun y => Real.log (ρ y)) x) (gradient e x) := by
    have := (s8p_bb d).sum_inner_mul_inner (gradient (fun y => Real.log (ρ y)) x) (gradient e x)
    simp only [neg_mul, Finset.sum_neg_distrib]
    rw [neg_inj]
    unfold s8p_lgr
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [real_inner_comm (gradient e x)]
  rw [h3]
  ring

theorem s8p_Lw_cont {e W : Euc d → ℝ} (he : ContDiff ℝ 2 e) (hW : ContDiff ℝ 2 W) :
    Continuous (s8p_Lw (s8p_bb d) W e) := by
  unfold s8p_Lw s8p_lap
  have h1 : Continuous (fderiv ℝ (fderiv ℝ e)) :=
    (he.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  have h2 : Continuous (fderiv ℝ W) := hW.continuous_fderiv (by norm_num)
  have h3 : Continuous (fderiv ℝ e) := he.continuous_fderiv (by norm_num)
  refine (continuous_finset_sum _ fun j _ => ((h1.clm_apply continuous_const).clm_apply continuous_const)).neg.add
    (continuous_finset_sum _ fun j _ => (h2.clm_apply continuous_const).mul (h3.clm_apply continuous_const))

theorem s8p_Lw_eig (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : Mov2eRho d ρ) (hE : Mov2eEll d ρ)
    (β : ℝ) (φ : 𝓢R) (om : ℝ)
    (hS : ∀ᵐ x ∂(volume : Measure (Euc d)), movS d s β ρ φ x = om * φ x) (x : Euc d) :
    s8p_Lw (s8p_bb d) (fun y => -Real.log (ρ y)) (s8p_E d s β ρ φ) x = om * s8p_ws ρ φ x := by
  obtain ⟨κ, hκ0, hW, -, -⟩ := s8p_W_data hρ hE
  have hc1 : Continuous (s8p_Lw (s8p_bb d) (fun y => -Real.log (ρ y)) (s8p_E d s β ρ φ)) :=
    s8p_Lw_cont ((s8p_E_smooth hd hs0 hsd hρ hE β φ).of_le (by simp))
      (hW.of_le (by simp))
  have hc2 : Continuous (fun x => om * s8p_ws ρ φ x) := continuous_const.mul (s8p_ws_smooth hρ φ).continuous
  have hae : (s8p_Lw (s8p_bb d) (fun y => -Real.log (ρ y)) (s8p_E d s β ρ φ)) =ᵐ[volume]
      fun x => om * s8p_ws ρ φ x := by
    filter_upwards [hS] with x hx
    rw [s8p_Lw_eq_wlap hρ, s8p_E_wlap hd hs0 hsd hρ hE β φ x, hx]
    unfold s8p_ws
    ring
  exact congrFun ((Continuous.ae_eq_iff_eq volume hc1 hc2).1 hae) x

theorem s8p_hLe_pt (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : Mov2eRho d ρ) (hE : Mov2eEll d ρ)
    {β : ℝ} (hβ : 0 < β) (φ : 𝓢R) {om : ℝ} (hom : 0 ≤ om)
    (hLw : ∀ x, s8p_Lw (s8p_bb d) (fun y => -Real.log (ρ y)) (s8p_E d s β ρ φ) x = om * s8p_ws ρ φ x)
    (x : Euc d) :
    ∑ i, s8p_g (s8p_E d s β ρ φ) (s8p_bb d i) x *
        fderiv ℝ (s8p_Lw (s8p_bb d) (fun y => -Real.log (ρ y)) (s8p_E d s β ρ φ)) x (s8p_bb d i) ≤
      (om * β) * s8p_N (s8p_bb d) (s8p_E d s β ρ φ) x +
        (om * β) * Real.sqrt (s8p_N (s8p_bb d) (s8p_E d s β ρ φ) x) * ‖fderiv ℝ (s8p_U d s ρ φ) x‖ := by
  set e := s8p_E d s β ρ φ with he
  have hfun : s8p_Lw (s8p_bb d) (fun y => -Real.log (ρ y)) e = fun x => om * s8p_ws ρ φ x := funext hLw
  have hwd : DifferentiableAt ℝ (s8p_ws ρ φ) x := ((s8p_ws_smooth hρ φ).differentiable (by simp)) x
  have hder : ∀ i, fderiv ℝ (s8p_Lw (s8p_bb d) (fun y => -Real.log (ρ y)) e) x (s8p_bb d i) =
      om * β * (fderiv ℝ e x (s8p_bb d i) - fderiv ℝ (s8p_U d s ρ φ) x (s8p_bb d i)) := by
    intro i
    rw [hfun, fderiv_const_mul hwd, s8p_fderiv_ws_eq hd hs0 hsd hρ hE hβ φ x]
    simp only [smul_apply, sub_apply, smul_eq_mul]
    ring
  simp_rw [hder]
  set N := s8p_N (s8p_bb d) e x with hN
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hNU : ∑ i, fderiv ℝ (s8p_U d s ρ φ) x (s8p_bb d i) ^ 2 = ‖fderiv ℝ (s8p_U d s ρ φ) x‖ ^ 2 :=
    s8p_N_eq (s8p_bb d) (s8p_U d s ρ φ) x
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => s8p_g e (s8p_bb d i) x)
    (fun i => fderiv ℝ (s8p_U d s ρ φ) x (s8p_bb d i))
  rw [hNU] at hCS
  have hb0 : 0 ≤ Real.sqrt N * ‖fderiv ℝ (s8p_U d s ρ φ) x‖ := by positivity
  have hb2 : (Real.sqrt N * ‖fderiv ℝ (s8p_U d s ρ φ) x‖) ^ 2 = N * ‖fderiv ℝ (s8p_U d s ρ φ) x‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hN0]
  have hCS' : -(Real.sqrt N * ‖fderiv ℝ (s8p_U d s ρ φ) x‖) ≤
      ∑ i, s8p_g e (s8p_bb d i) x * fderiv ℝ (s8p_U d s ρ φ) x (s8p_bb d i) := by
    refine (abs_le_of_sq_le_sq' ?_ hb0).1
    rw [hb2]; exact hCS
  have hexp : ∑ i, s8p_g e (s8p_bb d i) x * (om * β * (fderiv ℝ e x (s8p_bb d i) -
      fderiv ℝ (s8p_U d s ρ φ) x (s8p_bb d i))) = om * β * (N -
      ∑ i, s8p_g e (s8p_bb d i) x * fderiv ℝ (s8p_U d s ρ φ) x (s8p_bb d i)) := by
    rw [hN]; unfold s8p_N
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold s8p_g
    ring
  rw [hexp]
  have homb : 0 ≤ om * β := mul_nonneg hom hβ.le
  nlinarith [mul_le_mul_of_nonneg_left hCS' homb]

end HRS.MS.Spec
