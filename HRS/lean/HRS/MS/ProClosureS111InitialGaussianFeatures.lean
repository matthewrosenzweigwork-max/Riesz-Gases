import HRS.MS.ProClosureS111InitialTests
import HRS.MS.ProClosureS111PhysicalJets
import HRS.Prob.HilbertMartingale
import HRS.MS.S111X2Aux15

/-!
The actual initial Gaussian feature sqrt(R_theta) P_mu U(0,t) phi.
The accepted bounded positive operator square root applies to the actual
resolvent. Its Gram form is exactly susceptibilityCov, and contraction
retains the physical oscillator envelope. At theta=0 the same construction
and proof apply, without division by the preparation parameter.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.Whole.Q34 HRS.MS.S111X1 HRS.MS.S111X2 HRS.MS.R2WinOrb

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {K : E →L[ℝ] E} {Mg theta : ℝ}

def responseSqrt (hK : PosOp K Mg) (htheta : 0 ≤ theta) : E →L[ℝ] E :=
  HRS.sqrtOp 1 (s111x2_Rm hK htheta)

theorem responseSqrt_spec (hK : PosOp K Mg) (htheta : 0 ≤ theta) :
    HRS.HilbertCLTAux.IsPSDOp (responseSqrt hK htheta) ∧
      responseSqrt hK htheta * responseSqrt hK htheta = s111x2_Rm hK htheta := by
  have hR : HRS.HilbertCLTAux.IsPSDOp (s111x2_Rm hK htheta) := by
    refine ⟨fun x y => s111x2_Res_symm hK htheta x y, fun x => ?_⟩
    have hden : 0 < 1 + theta * Mg := by
      have := hK.nonneg
      positivity
    have hlow := (s111x2_Res_bounds hK htheta x).1
    have hnonneg : 0 ≤ ‖x‖ ^ 2 / (1 + theta * Mg) :=
      div_nonneg (sq_nonneg _) hden.le
    simpa only [s111x2_Rm_apply, real_inner_comm] using hnonneg.trans hlow
  exact HRS.sqrtOp_spec hR one_pos (fun x => by
    simpa only [s111x2_Rm_apply, real_inner_comm, one_mul] using
      (s111x2_Res_bounds hK htheta x).2.1)

theorem responseSqrt_inner (hK : PosOp K Mg) (htheta : 0 ≤ theta) (x y : E) :
    inner ℝ (responseSqrt hK htheta x) (responseSqrt hK htheta y) =
      inner ℝ x (s111x2_Rm hK htheta y) := by
  obtain ⟨hS, hSS⟩ := responseSqrt_spec hK htheta
  rw [hS.symm]
  have he : responseSqrt hK htheta (responseSqrt hK htheta y) =
      s111x2_Rm hK htheta y := congrArg (fun A : E →L[ℝ] E => A y) hSS
  rw [he]

theorem responseSqrt_norm_le (hK : PosOp K Mg) (htheta : 0 ≤ theta) (x : E) :
    ‖responseSqrt hK htheta x‖ ≤ ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1
  rw [← real_inner_self_eq_norm_sq, responseSqrt_inner]
  exact (s111x2_Res_bounds hK htheta x).2.1

end Hilbert

section Initial
variable {d : ℕ} {mu : Measure (Euc d)} [IsProbabilityMeasure mu]
variable {g : Euc d → ℝ} {K : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu} {Mg theta : ℝ}

def initialGaussianFeature (hK : KRep g mu K Mg) (htheta : 0 ≤ theta)
    (C : WholeCoeff d) (t : ℝ) (phi : Euc d → ℝ) : Lp ℝ 2 mu :=
  responseSqrt hK.posOp htheta (Pc mu (s111x2_toLp mu (propagatorW C 0 t phi)))

theorem initialGaussianFeature_inner (hK : KRep g mu K Mg) (htheta : 0 ≤ theta)
    (C : WholeCoeff d) (t v : ℝ) (phi psi : Euc d → ℝ)
    (hf : MemLp (propagatorW C 0 t phi) 2 mu)
    (hg : MemLp (propagatorW C 0 v psi) 2 mu) :
    inner ℝ (initialGaussianFeature hK htheta C t phi)
      (initialGaussianFeature hK htheta C v psi) =
      HRS.Whole.susceptibilityCov g mu theta (propagatorW C 0 t phi) (propagatorW C 0 v psi) := by
  rw [initialGaussianFeature, initialGaussianFeature, responseSqrt_inner]
  exact (s111x2_susc_eq_inner hK htheta hf hg).symm

theorem initialGaussianFeature_norm_le (hK : KRep g mu K Mg) (htheta : 0 ≤ theta)
    (C : WholeCoeff d) (t : ℝ) (phi : Euc d → ℝ) :
    ‖initialGaussianFeature hK htheta C t phi‖ ≤
      ‖s111x2_toLp mu (propagatorW C 0 t phi)‖ :=
  (responseSqrt_norm_le hK.posOp htheta _).trans (Pc_norm_le _)

theorem initialGaussianFeature_sub_norm_le (hK : KRep g mu K Mg) (htheta : 0 ≤ theta)
    (C : WholeCoeff d) (t v : ℝ) (phi : Euc d → ℝ) :
    ‖initialGaussianFeature hK htheta C t phi - initialGaussianFeature hK htheta C v phi‖ ≤
      ‖s111x2_toLp mu (propagatorW C 0 t phi) - s111x2_toLp mu (propagatorW C 0 v phi)‖ := by
  simp only [initialGaussianFeature, ← map_sub]
  exact (responseSqrt_norm_le hK.posOp htheta _).trans (Pc_norm_le _)

end Initial

section Linear
variable {d : ℕ} {s a beta theta : ℝ} {rho : Euc d → ℝ}
variable [IsProbabilityMeasure (HRS.Whole.withDensityReal rho)]
variable {g : Euc d → ℝ}
variable {K : Lp ℝ 2 (HRS.Whole.withDensityReal rho) →L[ℝ] Lp ℝ 2 (HRS.Whole.withDensityReal rho)} {Mg : ℝ}
variable (hX : X1Input d s a beta 0 rho)
variable (hK : KRep g (HRS.Whole.withDensityReal rho) K Mg) (htheta : 0 ≤ theta)

/-- The actual centered propagated class, obtained from the already
constructed screening map at preparation zero. -/
def centeredPropLinear {t : ℝ} (ht : 0 ≤ t) :
    oscSub d (wholeSpaceIndex d) →ₗ[ℝ] Lp ℝ 2 (HRS.Whole.withDensityReal rho) :=
  initialScreenedLinear hX hK (le_refl (0 : ℝ)) ht

theorem centeredPropLinear_eq {t : ℝ} (ht : 0 ≤ t)
    (phi : oscSub d (wholeSpaceIndex d)) :
    centeredPropLinear hX hK ht phi = Pc (HRS.Whole.withDensityReal rho)
      (s111x2_toLp (HRS.Whole.withDensityReal rho)
        (propagatorW (x1C d s a beta rho) 0 t (phi : Euc d → ℝ))) := by
  change s111x2_Res hK.posOp (le_refl (0 : ℝ))
    (s111x2_cl (initialProp_memLp hX ht phi)) = _
  have he := s111x2_Res_spec hK.posOp (le_refl (0 : ℝ))
    (s111x2_cl (initialProp_memLp hX ht phi))
  simpa only [zero_smul, add_zero, s111x2_cl_eq_Pc] using he

def initialGaussianLinear {t : ℝ} (ht : 0 ≤ t) :
    oscSub d (wholeSpaceIndex d) →ₗ[ℝ] Lp ℝ 2 (HRS.Whole.withDensityReal rho) :=
  (responseSqrt hK.posOp htheta).toLinearMap.comp (centeredPropLinear hX hK ht)

theorem initialGaussianLinear_apply {t : ℝ} (ht : 0 ≤ t)
    (phi : oscSub d (wholeSpaceIndex d)) :
    initialGaussianLinear hX hK htheta ht phi =
      initialGaussianFeature hK htheta (x1C d s a beta rho) t (phi : Euc d → ℝ) := by
  change responseSqrt hK.posOp htheta (centeredPropLinear hX hK ht phi) = _
  rw [centeredPropLinear_eq]
  rfl

end Linear

#print axioms responseSqrt_spec
#print axioms initialGaussianFeature_inner

end HRS.MS.ProClosureS111
