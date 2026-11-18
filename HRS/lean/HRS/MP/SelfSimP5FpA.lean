import HRS.MP.SelfSimP5Spec
import HRS.MP.SelfSimP4Flow

/-!
# MPP5FP, part A: the transport `EuclideanSpace ℝ (Fin N) ≃ EucConfig 1 N` and deterministic identities

Namespace `HRS.MP.SelfSimP5Fp`, helpers `p5f_`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.SelfSim HRS.MP.SelfSimP4 HRS.MP.SelfSimP5
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MP.SelfSimP5Fp

variable {N : ℕ}

/-- The linear equivalence `(e z) k = single 0 (z k)`. -/
def p5f_eL (N : ℕ) : EuclideanSpace ℝ (Fin N) ≃ₗ[ℝ] EucConfig 1 N where
  toFun z := fun k => EuclideanSpace.single (0 : Fin 1) (z k)
  map_add' x y := by ext k j; simp; split_ifs <;> simp
  map_smul' c x := by ext k j; simp
  invFun x := WithLp.toLp 2 fun k => x k 0
  left_inv z := by ext k; simp
  right_inv x := by
    ext k j
    have : j = 0 := Subsingleton.elim _ _
    subst this; simp

/-- The continuous linear equivalence. -/
def p5f_e (N : ℕ) : EuclideanSpace ℝ (Fin N) ≃L[ℝ] EucConfig 1 N :=
  (p5f_eL N).toContinuousLinearEquiv

theorem p5f_e_apply (z : EuclideanSpace ℝ (Fin N)) (k : Fin N) :
    p5f_e N z k = EuclideanSpace.single (0 : Fin 1) (z k) := rfl

theorem p5f_e_symm_apply (x : EucConfig 1 N) (k : Fin N) : (p5f_e N).symm x k = x k 0 := rfl

theorem p5f_norm_e_le (z : EuclideanSpace ℝ (Fin N)) : ‖p5f_e N z‖ ≤ ‖z‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg z)).2 fun k => ?_
  rw [p5f_e_apply, EuclideanSpace.norm_single]
  simpa using PiLp.norm_apply_le z k

theorem p5f_norm_sq_le (z : EuclideanSpace ℝ (Fin N)) : ‖z‖ ^ 2 ≤ N * ‖p5f_e N z‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  calc ∑ k, ‖z k‖ ^ 2 ≤ ∑ _k : Fin N, ‖p5f_e N z‖ ^ 2 := by
        refine Finset.sum_le_sum fun k _ => ?_
        have h1 : ‖p5f_e N z k‖ ≤ ‖p5f_e N z‖ := norm_le_pi_norm (p5f_e N z) k
        rw [p5f_e_apply, EuclideanSpace.norm_single] at h1
        exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = N * ‖p5f_e N z‖ ^ 2 := by simp

/-! ### Derivatives along the transport -/

/-- `g` transported to `EucConfig 1 N`. -/
def p5f_tr (g : EuclideanSpace ℝ (Fin N) → ℝ) : EucConfig 1 N → ℝ := fun x => g ((p5f_e N).symm x)

theorem p5f_fderiv_tr (g : EuclideanSpace ℝ (Fin N) → ℝ) (x : EucConfig 1 N) :
    fderiv ℝ (p5f_tr g) x =
      (fderiv ℝ g ((p5f_e N).symm x)).comp ((p5f_e N).symm : EucConfig 1 N →L[ℝ] EuclideanSpace ℝ (Fin N)) :=
  ContinuousLinearEquiv.comp_right_fderiv (p5f_e N).symm

theorem p5f_fderiv_tr_apply (g : EuclideanSpace ℝ (Fin N) → ℝ) (x v : EucConfig 1 N) :
    fderiv ℝ (p5f_tr g) x v = fderiv ℝ g ((p5f_e N).symm x) ((p5f_e N).symm v) := by
  rw [p5f_fderiv_tr]; rfl

theorem p5f_fderiv2_tr_apply {g : EuclideanSpace ℝ (Fin N) → ℝ} (hg : ContDiff ℝ 2 g) (x v w : EucConfig 1 N) :
    fderiv ℝ (fderiv ℝ (p5f_tr g)) x v w =
      fderiv ℝ (fderiv ℝ g) ((p5f_e N).symm x) ((p5f_e N).symm v) ((p5f_e N).symm w) := by
  set L : EucConfig 1 N →L[ℝ] EuclideanSpace ℝ (Fin N) := ((p5f_e N).symm : EucConfig 1 N →L[ℝ] EuclideanSpace ℝ (Fin N))
  have hfun : fderiv ℝ (p5f_tr g) = fun x => ((ContinuousLinearMap.compL ℝ (EucConfig 1 N) (EuclideanSpace ℝ (Fin N)) ℝ).flip L)
      (fderiv ℝ g (L x)) := by
    funext y; rw [p5f_fderiv_tr]; rfl
  have hd : Differentiable ℝ (fderiv ℝ g) := by
    have := hg.fderiv_right (m := 1) (by norm_num)
    exact this.differentiable (by norm_num)
  have h1 : HasFDerivAt (fun y => fderiv ℝ g (L y)) ((fderiv ℝ (fderiv ℝ g) (L x)).comp L) x :=
    (hd (L x)).hasFDerivAt.comp x L.hasFDerivAt
  have h2 := ((ContinuousLinearMap.compL ℝ (EucConfig 1 N) (EuclideanSpace ℝ (Fin N)) ℝ).flip L).hasFDerivAt.comp x h1
  rw [hfun]
  have h3 := h2.fderiv
  simp only [Function.comp_def] at h3
  rw [h3]
  rfl

/-! ### Test functions -/

theorem p5f_norm_symm_le (x : EucConfig 1 N) : ‖x‖ ≤ ‖(p5f_e N).symm x‖ := by
  simpa using p5f_norm_e_le ((p5f_e N).symm x)

theorem p5f_test_tr {g : EuclideanSpace ℝ (Fin N) → ℝ} (hg : ss5_Test g) : P4Test (p5f_tr g) := by
  refine ⟨hg.smooth.comp (p5f_e N).symm.contDiff, ?_⟩
  obtain ⟨C, hC⟩ := hg.bdd
  set L : EucConfig 1 N →L[ℝ] EuclideanSpace ℝ (Fin N) :=
    ((p5f_e N).symm : EucConfig 1 N →L[ℝ] EuclideanSpace ℝ (Fin N)) with hL
  set c : ℝ := ‖L‖ with hc
  have hc0 : 0 ≤ c := norm_nonneg _
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0).1
  refine ⟨C * (1 + c + c ^ 2), fun x => ⟨?_, ?_, ?_⟩⟩
  · calc |p5f_tr g x| ≤ C := (hC _).1
      _ ≤ C * (1 + c + c ^ 2) := by nlinarith [mul_nonneg hC0 hc0, mul_nonneg hC0 (sq_nonneg c)]
  · have h1 : ‖fderiv ℝ (p5f_tr g) x‖ ≤ ‖fderiv ℝ g (L x)‖ * c := by
      rw [p5f_fderiv_tr]; exact ContinuousLinearMap.opNorm_comp_le _ _
    have h2 : (1 + ‖x‖) ≤ 1 + ‖L x‖ := add_le_add_right (p5f_norm_symm_le x) 1
    calc ‖fderiv ℝ (p5f_tr g) x‖ * (1 + ‖x‖)
        ≤ (‖fderiv ℝ g (L x)‖ * c) * (1 + ‖L x‖) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = (‖fderiv ℝ g (L x)‖ * (1 + ‖L x‖)) * c := by ring
      _ ≤ C * c := mul_le_mul_of_nonneg_right (hC _).2.1 hc0
      _ ≤ C * (1 + c + c ^ 2) := by nlinarith [mul_nonneg hC0 hc0, mul_nonneg hC0 (sq_nonneg c)]
  · have h1 : ‖fderiv ℝ (fderiv ℝ (p5f_tr g)) x‖ ≤ ‖fderiv ℝ (fderiv ℝ g) (L x)‖ * c * c := by
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
      have hh := p5f_fderiv2_tr_apply hg.smooth x v w
      rw [hh]
      have e1 : ‖fderiv ℝ (fderiv ℝ g) (L x) (L v) (L w)‖ ≤
          ‖fderiv ℝ (fderiv ℝ g) (L x)‖ * ‖L v‖ * ‖L w‖ := ContinuousLinearMap.le_opNorm₂ _ _ _
      have e2 : ‖L v‖ ≤ c * ‖v‖ := L.le_opNorm v
      have e3 : ‖L w‖ ≤ c * ‖w‖ := L.le_opNorm w
      have e4 := (hC (L x)).2.2
      calc _ ≤ ‖fderiv ℝ (fderiv ℝ g) (L x)‖ * ‖L v‖ * ‖L w‖ := e1
        _ ≤ ‖fderiv ℝ (fderiv ℝ g) (L x)‖ * (c * ‖v‖) * (c * ‖w‖) := by
          gcongr
        _ = ‖fderiv ℝ (fderiv ℝ g) (L x)‖ * c * c * ‖v‖ * ‖w‖ := by ring
    calc ‖fderiv ℝ (fderiv ℝ (p5f_tr g)) x‖ ≤ ‖fderiv ℝ (fderiv ℝ g) (L x)‖ * c * c := h1
      _ ≤ C * c * c := by gcongr; exact (hC _).2.2
      _ ≤ C * (1 + c + c ^ 2) := by nlinarith [mul_nonneg hC0 hc0, mul_nonneg hC0 (sq_nonneg c)]

/-! ### The drift and the generator -/

/-- The transported drift `b r x = e (-(∇U (e⁻¹ x)))` (time independent). -/
def p5f_b (U : EuclideanSpace ℝ (Fin N) → ℝ) : ℝ → EucConfig 1 N → EucConfig 1 N :=
  fun _ x => p5f_e N (-(gradient U ((p5f_e N).symm x)))

theorem p5f_symm_configBasis (k : Fin N × Fin 1) :
    (p5f_e N).symm (configBasis 1 N k) = EuclideanSpace.single k.1 (1 : ℝ) := by
  ext j
  rw [p5f_e_symm_apply]
  simp only [configBasis, EuclideanSpace.single_apply]
  by_cases h : j = k.1
  · subst h
    have : k.2 = 0 := Subsingleton.elim _ _
    simp [this]
  · simp [h, Pi.single_apply]

theorem p5f_gen_eq {g : EuclideanSpace ℝ (Fin N) → ℝ} (hg : ContDiff ℝ 2 g) (θ : ℝ)
    (U : EuclideanSpace ℝ (Fin N) → ℝ) (r : ℝ) (z : EuclideanSpace ℝ (Fin N)) :
    p4Gen θ (p5f_b U) r (p5f_tr g) (p5f_e N z) = ss5_gen θ U g z := by
  unfold p4Gen ss5_gen ss5_lap
  have hsym : (p5f_e N).symm (p5f_e N z) = z := (p5f_e N).symm_apply_apply z
  congr 1
  · congr 1
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Fin.sum_univ_one, p5f_fderiv2_tr_apply hg, hsym]
    have := p5f_symm_configBasis (N := N) (k, 0)
    simp only at this
    rw [this]
  · rw [p5f_fderiv_tr_apply, p5f_b]
    simp only [hsym, ContinuousLinearEquiv.symm_apply_apply]
    have key : inner ℝ (gradient U z) (gradient g z) = fderiv ℝ g z (gradient U z) := by
      rw [real_inner_comm]; exact InnerProductSpace.toDual_symm_apply
    rw [key, map_neg]

end HRS.MP.SelfSimP5Fp
