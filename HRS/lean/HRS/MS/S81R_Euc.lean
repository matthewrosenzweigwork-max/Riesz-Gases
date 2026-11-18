import HRS.MS.MfeConfAux62
import HRS.MS.PoisFlowAux1

/-!
# S81R, packet R7a: the identification `EucConfig d N ≃ Euc (N*d)` and the rescaling `Φ = √β · enc`

`enc z = (z_i^j)_{(i,j) ↦ finProdFinEquiv (i,j)}` preserves the Euclidean pairing `∑ᵢ ⟨zᵢ, wᵢ⟩`; `Φ = √β enc`, `Ψ = Φ⁻¹`.
`s81r_Phi_sigma`: the noise directions `√(2β⁻¹) e_{ij}` are sent to the Pois noise directions `√2 e_{(ij)}`.
-/

noncomputable section

open MeasureTheory
open HRS HRS.MS.PoisFlow HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Impl HRS.MS.MfeConf

namespace HRS.MS.S81R

variable {d N : ℕ}

/-- encoding of a configuration as a vector of `Euc (N*d)` -/
def s81r_encFun (z : Whole.EucConfig d N) : Euc (N * d) :=
  WithLp.toLp 2 (fun k => z (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2)

/-- decoding -/
def s81r_decFun (y : Euc (N * d)) : Whole.EucConfig d N :=
  fun i => WithLp.toLp 2 (fun j => y (finProdFinEquiv (i, j)))

theorem s81r_dec_enc (z : Whole.EucConfig d N) : s81r_decFun (s81r_encFun z) = z := by
  funext i
  ext j
  show (z (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1).ofLp
    (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2 = (z i).ofLp j
  rw [Equiv.symm_apply_apply]

theorem s81r_enc_dec (y : Euc (N * d)) : s81r_encFun (s81r_decFun y) = y := by
  ext k
  show y.ofLp (finProdFinEquiv ((finProdFinEquiv.symm k).1, (finProdFinEquiv.symm k).2)) = y.ofLp k
  rw [Prod.mk.eta, Equiv.apply_symm_apply]

theorem s81r_encFun_smul (c : ℝ) (w : Whole.EucConfig d N) :
    s81r_encFun (c • w) = c • s81r_encFun w := by
  ext k
  simp [s81r_encFun]

theorem s81r_decFun_smul (c : ℝ) (y : Euc (N * d)) :
    s81r_decFun (c • y) = c • s81r_decFun y := by
  funext i
  ext j
  simp [s81r_decFun]

/-- the linear map `enc` -/
def s81r_encL (d N : ℕ) : Whole.EucConfig d N →ₗ[ℝ] Euc (N * d) where
  toFun := s81r_encFun
  map_add' z w := by
    ext k
    simp [s81r_encFun]
  map_smul' c z := by
    ext k
    simp [s81r_encFun]

/-- the linear map `dec` -/
def s81r_decL (d N : ℕ) : Euc (N * d) →ₗ[ℝ] Whole.EucConfig d N where
  toFun := s81r_decFun
  map_add' y y' := by
    funext i
    ext j
    simp [s81r_decFun]
  map_smul' c y := by
    funext i
    ext j
    simp [s81r_decFun]

/-- continuous linear map `enc` -/
def s81r_enc (d N : ℕ) : Whole.EucConfig d N →L[ℝ] Euc (N * d) :=
  LinearMap.toContinuousLinearMap (s81r_encL d N)

/-- continuous linear map `dec` -/
def s81r_dec (d N : ℕ) : Euc (N * d) →L[ℝ] Whole.EucConfig d N :=
  LinearMap.toContinuousLinearMap (s81r_decL d N)

@[simp] theorem s81r_enc_apply (z : Whole.EucConfig d N) : s81r_enc d N z = s81r_encFun z := rfl
@[simp] theorem s81r_dec_apply (y : Euc (N * d)) : s81r_dec d N y = s81r_decFun y := rfl

theorem s81r_enc_inner (z w : Whole.EucConfig d N) :
    inner ℝ (s81r_encFun z) (s81r_encFun w) = ∑ i, inner ℝ (z i) (w i) := by
  have h := Equiv.sum_comp (finProdFinEquiv : Fin N × Fin d ≃ Fin (N * d))
    (fun k => inner ℝ (s81r_encFun z k) (s81r_encFun w k))
  rw [PiLp.inner_apply, ← h, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  show inner ℝ ((z (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1).ofLp
      (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2)
    ((w (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1).ofLp
      (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2) = _
  rw [Equiv.symm_apply_apply]

theorem s81r_enc_norm_sq (z : Whole.EucConfig d N) : ‖s81r_encFun z‖ ^ 2 = ∑ i, ‖z i‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, s81r_enc_inner]
  exact Finset.sum_congr rfl fun i _ => real_inner_self_eq_norm_sq _

/-- `Φ = √β · enc` -/
def s81r_Phi (β : ℝ) (d N : ℕ) : Whole.EucConfig d N →L[ℝ] Euc (N * d) :=
  Real.sqrt β • s81r_enc d N

/-- `Ψ = Φ⁻¹ = (√β)⁻¹ · dec` -/
def s81r_Psi (β : ℝ) (d N : ℕ) : Euc (N * d) →L[ℝ] Whole.EucConfig d N :=
  (Real.sqrt β)⁻¹ • s81r_dec d N

theorem s81r_Psi_apply (β : ℝ) (y : Euc (N * d)) :
    s81r_Psi β d N y = (Real.sqrt β)⁻¹ • s81r_decFun y := rfl

theorem s81r_Phi_apply (β : ℝ) (z : Whole.EucConfig d N) :
    s81r_Phi β d N z = Real.sqrt β • s81r_encFun z := rfl

theorem s81r_enc_Psi (β : ℝ) (y : Euc (N * d)) :
    s81r_encFun (s81r_Psi β d N y) = (Real.sqrt β)⁻¹ • y := by
  rw [s81r_Psi_apply, s81r_encFun_smul, s81r_enc_dec]

theorem s81r_Psi_Phi {β : ℝ} (hβ : 0 < β) (z : Whole.EucConfig d N) :
    s81r_Psi β d N (s81r_Phi β d N z) = z := by
  have h : Real.sqrt β ≠ 0 := (Real.sqrt_pos.2 hβ).ne'
  rw [s81r_Phi_apply, s81r_Psi_apply, s81r_decFun_smul, s81r_dec_enc, smul_smul,
    inv_mul_cancel₀ h, one_smul]

theorem s81r_Phi_Psi {β : ℝ} (hβ : 0 < β) (y : Euc (N * d)) :
    s81r_Phi β d N (s81r_Psi β d N y) = y := by
  have h : Real.sqrt β ≠ 0 := (Real.sqrt_pos.2 hβ).ne'
  rw [s81r_Phi_apply, s81r_enc_Psi, smul_smul, mul_inv_cancel₀ h, one_smul]

/-- the continuous linear equivalence `Φ` -/
def s81r_PhiE {β : ℝ} (hβ : 0 < β) (d N : ℕ) : Whole.EucConfig d N ≃L[ℝ] Euc (N * d) :=
  ContinuousLinearEquiv.equivOfInverse (s81r_Phi β d N) (s81r_Psi β d N)
    (s81r_Psi_Phi hβ) (s81r_Phi_Psi hβ)

theorem s81r_PhiE_apply {β : ℝ} (hβ : 0 < β) (z : Whole.EucConfig d N) :
    s81r_PhiE hβ d N z = s81r_Phi β d N z := rfl

theorem s81r_PhiE_symm_apply {β : ℝ} (hβ : 0 < β) (y : Euc (N * d)) :
    (s81r_PhiE hβ d N).symm y = s81r_Psi β d N y := rfl

/-- the encoded basis vector -/
theorem s81r_enc_basis (i : Fin N) (j : Fin d) :
    s81r_encFun (configBasis d N (i, j)) = EuclideanSpace.single (finProdFinEquiv (i, j)) 1 := by
  ext k
  obtain ⟨⟨i', j'⟩, rfl⟩ := finProdFinEquiv.surjective k
  show (configBasis d N (i, j) (finProdFinEquiv.symm (finProdFinEquiv (i', j'))).1).ofLp
    (finProdFinEquiv.symm (finProdFinEquiv (i', j'))).2 = _
  rw [Equiv.symm_apply_apply]
  by_cases h : (i', j') = (i, j)
  · rw [h]
    simp [configBasis]
  · have hne : finProdFinEquiv (i', j') ≠ finProdFinEquiv (i, j) := fun h' =>
      h (finProdFinEquiv.injective h')
    rw [EuclideanSpace.single_apply, if_neg hne]
    by_cases h1 : i' = i
    · subst h1
      have h2 : j' ≠ j := fun h2 => h (by rw [h2])
      simp [configBasis, EuclideanSpace.single_apply, h2]
    · simp [configBasis, h1]

/-- the noise directions are sent to the Pois noise directions -/
theorem s81r_Phi_sigma {β : ℝ} (hβ : 0 < β) (i : Fin N) (j : Fin d) :
    s81r_Phi β d N (p4r_sigma d N β⁻¹ (i, j)) = pfSigma (N * d) (finProdFinEquiv (i, j)) := by
  have e : Real.sqrt (2 * β⁻¹) * Real.sqrt β = Real.sqrt 2 := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  simp only [s81r_Phi, p4r_sigma, ContinuousLinearMap.smul_apply, s81r_enc_apply, map_smul]
  rw [s81r_enc_basis i j, ← smul_assoc, smul_eq_mul, e]
  rfl

end HRS.MS.S81R
