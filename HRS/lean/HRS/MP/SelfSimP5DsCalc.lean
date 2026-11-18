import HRS.MP.SelfSimP5DsFish

/-!
# P5 dissipation on `Fin N`: calculus along `e` (derivatives of `h ∘ e`, test functions, generator)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.SelfSimP4 HRS.MP.SelfSimP5
  HRS.MP.SelfSimP5Core
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MP.SelfSimP5Ds

theorem p5d_fderiv_comp {N : ℕ} (h : EucConfig 1 N → ℝ) (z : EuclideanSpace ℝ (Fin N)) :
    fderiv ℝ (fun w => h (p5d_e N w)) z =
      (fderiv ℝ h (p5d_e N z)).comp (p5d_e N : EuclideanSpace ℝ (Fin N) →L[ℝ] EucConfig 1 N) :=
  (p5d_e N).comp_right_fderiv (f := h)

theorem p5d_D2 {N : ℕ} {h : EucConfig 1 N → ℝ} (hh : ContDiff ℝ 2 h) (z v w : EuclideanSpace ℝ (Fin N)) :
    fderiv ℝ (fderiv ℝ (fun w => h (p5d_e N w))) z v w =
      fderiv ℝ (fderiv ℝ h) (p5d_e N z) (p5d_e N v) (p5d_e N w) := by
  have hfd : Differentiable ℝ (fderiv ℝ h) :=
    (hh.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  set P : (EucConfig 1 N →L[ℝ] ℝ) →L[ℝ] (EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin N)) (EucConfig 1 N) ℝ).flip
      (p5d_e N : EuclideanSpace ℝ (Fin N) →L[ℝ] EucConfig 1 N) with hP
  have hfun : fderiv ℝ (fun w => h (p5d_e N w)) = fun z => P (fderiv ℝ h (p5d_e N z)) := by
    funext z
    rw [p5d_fderiv_comp]
    rfl
  have hder : HasFDerivAt (fun z => P (fderiv ℝ h (p5d_e N z)))
      (P.comp ((fderiv ℝ (fderiv ℝ h) (p5d_e N z)).comp
        (p5d_e N : EuclideanSpace ℝ (Fin N) →L[ℝ] EucConfig 1 N))) z := by
    have h1 : HasFDerivAt (fderiv ℝ h) (fderiv ℝ (fderiv ℝ h) (p5d_e N z)) (p5d_e N z) :=
      (hfd _).hasFDerivAt
    have h2 := h1.comp z (p5d_e N).hasFDerivAt
    exact P.hasFDerivAt.comp z h2
  rw [hfun, hder.fderiv]
  rfl

theorem p5d_e_single {N : ℕ} (k : Fin N) :
    p5d_e N (EuclideanSpace.single k (1 : ℝ)) = configBasis 1 N (k, 0) := by
  funext i
  ext j
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  rw [p5d_e_apply]
  by_cases hk : i = k
  · subst hk
    simp [configBasis]
  · simp [configBasis, Pi.single_apply, hk, PiLp.single_apply]

theorem p5d_opNorm_e_le {N : ℕ} :
    ‖(p5d_e N : EuclideanSpace ℝ (Fin N) →L[ℝ] EucConfig 1 N)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
    simpa using p5d_norm_e_le v

theorem p5d_test {N : ℕ} {h : EucConfig 1 N → ℝ} (hh : P4Test h) :
    ss5_Test (fun w : EuclideanSpace ℝ (Fin N) => h (p5d_e N w)) := by
  refine ⟨hh.smooth.comp (p5d_e N).contDiff, ?_⟩
  obtain ⟨C₀, hC₀⟩ := hh.bdd
  have hC0 : 0 ≤ C₀ := le_trans (abs_nonneg _) (hC₀ 0).1
  have hs : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  refine ⟨(1 + Real.sqrt N) * C₀, fun z => ⟨?_, ?_, ?_⟩⟩
  · calc |h (p5d_e N z)| ≤ C₀ := (hC₀ _).1
      _ ≤ (1 + Real.sqrt N) * C₀ := by nlinarith
  · rw [p5d_fderiv_comp]
    have h1 : ‖(fderiv ℝ h (p5d_e N z)).comp
        (p5d_e N : EuclideanSpace ℝ (Fin N) →L[ℝ] EucConfig 1 N)‖ ≤ ‖fderiv ℝ h (p5d_e N z)‖ :=
      (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_of_le_one_right (norm_nonneg _) p5d_opNorm_e_le)
    have h2 : 1 + ‖z‖ ≤ (1 + Real.sqrt N) * (1 + ‖p5d_e N z‖) := by
      have := p5d_norm_le_sqrt z
      nlinarith [norm_nonneg (p5d_e N z)]
    calc ‖(fderiv ℝ h (p5d_e N z)).comp
          (p5d_e N : EuclideanSpace ℝ (Fin N) →L[ℝ] EucConfig 1 N)‖ * (1 + ‖z‖)
        ≤ ‖fderiv ℝ h (p5d_e N z)‖ * ((1 + Real.sqrt N) * (1 + ‖p5d_e N z‖)) :=
          mul_le_mul h1 h2 (by positivity) (norm_nonneg _)
      _ = (1 + Real.sqrt N) * (‖fderiv ℝ h (p5d_e N z)‖ * (1 + ‖p5d_e N z‖)) := by ring
      _ ≤ (1 + Real.sqrt N) * C₀ := mul_le_mul_of_nonneg_left (hC₀ _).2.1 (by positivity)
  · have hb := (hC₀ (p5d_e N z)).2.2
    have hle : ‖fderiv ℝ (fderiv ℝ (fun w => h (p5d_e N w))) z‖ ≤ C₀ := by
      refine ContinuousLinearMap.opNorm_le_bound _ hC0 fun v => ?_
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
      rw [p5d_D2 hh.smooth]
      calc ‖fderiv ℝ (fderiv ℝ h) (p5d_e N z) (p5d_e N v) (p5d_e N w)‖
          ≤ ‖fderiv ℝ (fderiv ℝ h) (p5d_e N z)‖ * ‖p5d_e N v‖ * ‖p5d_e N w‖ :=
            ContinuousLinearMap.le_opNorm₂ _ _ _
        _ ≤ C₀ * ‖v‖ * ‖w‖ := by
            have := p5d_norm_e_le v
            have := p5d_norm_e_le w
            gcongr
    calc _ ≤ C₀ := hle
      _ ≤ (1 + Real.sqrt N) * C₀ := by nlinarith

/-- The transported drift `b x = e (-∇U (e⁻¹ x))`. -/
def p5d_b {N : ℕ} (U : EuclideanSpace ℝ (Fin N) → ℝ) : EucConfig 1 N → EucConfig 1 N :=
  fun x => p5d_e N (-(gradient U ((p5d_e N).symm x)))

theorem p5d_inner_gradient {N : ℕ} (f : EuclideanSpace ℝ (Fin N) → ℝ) (z w : EuclideanSpace ℝ (Fin N)) :
    inner ℝ (gradient f z) w = fderiv ℝ f z w := by
  unfold gradient
  rw [InnerProductSpace.toDual_symm_apply]

theorem p5d_gen {N : ℕ} {θ : ℝ} {U : EuclideanSpace ℝ (Fin N) → ℝ} {h : EucConfig 1 N → ℝ}
    (hh : ContDiff ℝ 2 h) (r : ℝ) (z : EuclideanSpace ℝ (Fin N)) :
    p4Gen θ (fun _ => p5d_b U) r h (p5d_e N z) =
      ss5_gen θ U (fun w => h (p5d_e N w)) z := by
  unfold p4Gen ss5_gen ss5_lap
  have hlap : ∑ k : Fin N × Fin 1, fderiv ℝ (fderiv ℝ h) (p5d_e N z) (configBasis 1 N k) (configBasis 1 N k) =
      ∑ k : Fin N, fderiv ℝ (fderiv ℝ (fun w => h (p5d_e N w))) z
        (EuclideanSpace.single k 1) (EuclideanSpace.single k 1) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Fin.sum_univ_one, p5d_D2 hh, p5d_e_single]
  have hdr : fderiv ℝ h (p5d_e N z) (p5d_b U (p5d_e N z)) =
      -inner ℝ (gradient U z) (gradient (fun w => h (p5d_e N w)) z) := by
    have : inner ℝ (gradient U z) (gradient (fun w => h (p5d_e N w)) z) =
        fderiv ℝ h (p5d_e N z) (p5d_e N (gradient U z)) := by
      rw [real_inner_comm, p5d_inner_gradient, p5d_fderiv_comp]
      rfl
    rw [this]
    simp [p5d_b]
  rw [hlap, hdr]
  ring

end HRS.MP.SelfSimP5Ds
