import HRS.MC.S7E0b

/-!
# Packet `s7_E1_variance_sandwich`, file 1: the operator bounds `c <= C <= 1`

The response operator `R = (I + beta T)^{-1}` on `L^2(mu)` (`T = K P` self-adjoint, nonnegative) satisfies
`c ||u||^2 <= <R u, u> <= ||u||^2` with `c = (1 + beta ||T||)^{-1}`; hence every finite section of the
covariance matrix `C_ij = susceptibilityCov (e_i) (e_j)` satisfies `c I <= C_n <= I`.  The Kronecker
square then gives `c^2 sum a_ij^2 <= sum a_ij a_kl C_ik C_jl <= sum a_ij^2`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace Matrix Kronecker

noncomputable section

namespace HRS.MC.Sec7.E1Aux1

open HRS HRS.Sec7 HRS.StaticLimitAux Torus

variable {d : ℕ}

/-! ### Abstract Hilbert space facts -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem e1a_cs (T : E →L[ℝ] E) (hs : ∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫) (hp : ∀ x, 0 ≤ ⟪T x, x⟫) (u : E) :
    ‖T u‖ ^ 2 ≤ ‖T‖ * ⟪T u, u⟫ := by
  set a := T u with ha
  have hm : ⟪T a, u⟫ = ‖a‖ ^ 2 := by
    rw [hs, ← ha, real_inner_self_eq_norm_sq]
  have hq : ∀ t : ℝ, 0 ≤ ⟪T u, u⟫ * (t * t) + (2 * ‖a‖ ^ 2) * t + ⟪T a, a⟫ := by
    intro t
    have := hp (a + t • u)
    rw [map_add, map_smul, ← ha, inner_add_left, inner_add_right, inner_add_right,
      real_inner_smul_left, real_inner_smul_left, real_inner_smul_right, real_inner_smul_right,
      hm, real_inner_self_eq_norm_sq] at this
    nlinarith [this]
  have hd := discrim_le_zero hq
  unfold discrim at hd
  have hpa : ⟪T a, a⟫ ≤ ‖T‖ * ‖a‖ ^ 2 := by
    calc ⟪T a, a⟫ ≤ ‖T a‖ * ‖a‖ := real_inner_le_norm _ _
      _ ≤ (‖T‖ * ‖a‖) * ‖a‖ := mul_le_mul_of_nonneg_right (T.le_opNorm a) (norm_nonneg _)
      _ = _ := by ring
  have hr := hp u
  have hk := norm_nonneg T
  by_cases h0 : ‖a‖ = 0
  · rw [h0]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]; positivity
  · have hpos : 0 < ‖a‖ ^ 2 := by positivity
    have h1 : (‖a‖ ^ 2) ^ 2 ≤ ⟪T u, u⟫ * (‖T‖ * ‖a‖ ^ 2) := by
      nlinarith [mul_le_mul_of_nonneg_left hpa hr]
    nlinarith

/-- `A = I + beta T` with `T` symmetric nonnegative and `R A = A R = I`: `c <= R <= 1`. -/
theorem e1a_resolvent (T : E →L[ℝ] E) (hs : ∀ x y, ⟪T x, y⟫ = ⟪x, T y⟫) (hp : ∀ x, 0 ≤ ⟪T x, x⟫)
    {β : ℝ} (hβ : 0 ≤ β) (R : E →L[ℝ] E) (hR : ∀ y, R y + β • T (R y) = y)
    (hRs : ∀ x y, ⟪R x, y⟫ = ⟪x, R y⟫) (u : E) :
    ⟪R u, u⟫ ≤ ‖u‖ ^ 2 ∧ ‖u‖ ^ 2 ≤ (1 + β * ‖T‖) * ⟪R u, u⟫ := by
  set h := R u with hh
  have hu : u = h + β • T h := (hR u).symm
  have e1 : ⟪R u, u⟫ = ‖h‖ ^ 2 + β * ⟪T h, h⟫ := by
    conv_lhs => rw [← hh]
    conv_lhs => rw [hu]
    rw [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq, real_inner_comm]
  have e2 : ‖u‖ ^ 2 = ‖h‖ ^ 2 + 2 * β * ⟪T h, h⟫ + β ^ 2 * ‖T h‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    conv_lhs => rw [hu]
    rw [inner_add_left, inner_add_right, inner_add_right, real_inner_smul_left, real_inner_smul_left,
      real_inner_smul_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq, real_inner_comm h (T h)]
    ring
  have b1 : 0 ≤ ⟪T h, h⟫ := hp h
  have b2 := e1a_cs T hs hp h
  have b3 : ⟪T h, h⟫ ≤ ‖T‖ * ‖h‖ ^ 2 := by
    calc ⟪T h, h⟫ ≤ ‖T h‖ * ‖h‖ := real_inner_le_norm _ _
      _ ≤ (‖T‖ * ‖h‖) * ‖h‖ := mul_le_mul_of_nonneg_right (T.le_opNorm h) (norm_nonneg _)
      _ = _ := by ring
  have hk := norm_nonneg T
  rw [e1, e2]
  constructor
  · nlinarith [mul_nonneg hβ b1, mul_nonneg (sq_nonneg β) (sq_nonneg ‖T h‖)]
  · nlinarith [mul_nonneg hβ (sub_nonneg.2 b3), mul_nonneg (sq_nonneg β) (sub_nonneg.2 b2),
      mul_nonneg hβ hk, mul_nonneg hβ b1]

end Abstract

/-! ### The response operator with the two-sided bounds -/

section Concrete

variable {ρ : Torus d → ℝ}

theorem e1a_resp (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    (hρ : SmoothPosDensity ρ) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧
    ∃ R : Lp ℝ 2 (withDensityReal ρ) →L[ℝ] Lp ℝ 2 (withDensityReal ρ),
      (∀ x y, ⟪R x, y⟫ = ⟪x, R y⟫) ∧ (∀ u, ⟪R u, u⟫ ≤ ‖u‖ ^ 2) ∧ (∀ u, c * ‖u‖ ^ 2 ≤ ⟪R u, u⟫) ∧
      ∀ {φ ψ : Torus d → ℝ} (hφ : MemLp φ 2 (withDensityReal ρ)) (hψ : MemLp ψ 2 (withDensityReal ρ)),
        ∫ x, φ x ∂(withDensityReal ρ) = 0 → ∫ x, ψ x ∂(withDensityReal ρ) = 0 →
        susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β φ ψ =
          ⟪hφ.toLp φ, R (hψ.toLp ψ)⟫ := by
  have hd1 : 1 ≤ d := by omega
  have hρc : Continuous ρ := continuous_of_smooth hρ.smooth
  obtain ⟨Λ, hΛ⟩ := isCompact_univ.exists_bound_of_continuousOn hρc.continuousOn
  have H : PDE.MFLinear.KS (periodicRiesz d s) ρ Λ :=
    ⟨PDE.MFOneLe.integrable_periodicRiesz hd1 s hs0 hsd, fun x => periodicRiesz_neg x, hρ.density,
      fun x => (le_abs_self _).trans (hΛ x (Set.mem_univ x))⟩
  have hP : IsProbabilityMeasure (withDensityReal ρ) := H.isProb
  obtain ⟨R, hRl, hRr, hRsym, hRpos⟩ := PDE.MFLinear.exists_inverse hd1 s hs0 hsd H hρc β hβ.le
  have hTs := PDE.MFLinear.TLp_symm hd1 s hs0 hsd H hρc
  have hTp := PDE.MFLinear.TLp_inner_nonneg hd1 s hs0 hsd H hρc
  have hres : ∀ u, ⟪R u, u⟫ ≤ ‖u‖ ^ 2 ∧ ‖u‖ ^ 2 ≤ (1 + β * ‖PDE.MFLinear.TLp H‖) * ⟪R u, u⟫ :=
    fun u => e1a_resolvent (PDE.MFLinear.TLp H) hTs hTp hβ.le R (fun y => hRr y) hRsym u
  have hk := norm_nonneg (PDE.MFLinear.TLp H)
  have hpos : 0 < 1 + β * ‖PDE.MFLinear.TLp H‖ := by positivity
  refine ⟨(1 + β * ‖PDE.MFLinear.TLp H‖)⁻¹, inv_pos.2 hpos,
    inv_le_one_of_one_le₀ (by nlinarith [mul_nonneg hβ.le hk]), R, hRsym, fun u => (hres u).1,
    fun u => ?_, fun {φ ψ} hφ hψ hφ0 hψ0 => ?_⟩
  · rw [inv_mul_le_iff₀ hpos]; exact (hres u).2
  have hy1 : ⇑(hφ.toLp φ) =ᵐ[withDensityReal ρ] projMean (withDensityReal ρ) φ := by
    have : projMean (withDensityReal ρ) φ = φ := PDE.MFLinear.projMean_of_pair_zero hφ0
    rw [this]; exact MemLp.coeFn_toLp hφ
  have hy2 : ⇑(hψ.toLp ψ) =ᵐ[withDensityReal ρ] projMean (withDensityReal ρ) ψ := by
    have : projMean (withDensityReal ρ) ψ = ψ := PDE.MFLinear.projMean_of_pair_zero hψ0
    rw [this]; exact MemLp.coeFn_toLp hψ
  have hresp : IsResponse (periodicRiesz d s) (withDensityReal ρ) β ψ ⇑(R (hψ.toLp ψ)) :=
    PDE.MFLinear.isResponse_of_A H β ψ _ (by rw [hRr]; exact hy2)
  have hex : ∃ h, IsResponse (periodicRiesz d s) (withDensityReal ρ) β ψ h := ⟨_, hresp⟩
  obtain ⟨h0, -, huniq⟩ := PDE.MFLinear.exists_unique_response_of_one_le hd1 s hs0 hsd ρ hρ.density
    hρc β hβ.le ψ hψ
  have hch : responseInverse (periodicRiesz d s) (withDensityReal ρ) β ψ =ᵐ[withDensityReal ρ] ⇑(R (hψ.toLp ψ)) := by
    unfold responseInverse
    simp only [hex, dite_true]
    exact (huniq _ hex.choose_spec).trans (huniq _ hresp).symm
  unfold susceptibilityCov
  rw [PDE.MFLinear.innerLp_eq_l2Inner]
  exact (PDE.MFLinear.l2Inner_congr_ae (Filter.EventuallyEq.refl _ _) hch).trans
    (PDE.MFLinear.l2Inner_congr_ae hy1.symm (Filter.EventuallyEq.refl _ _))

/-- Gram form of the covariance along the basis, for the bounded response operator `R`. -/
theorem e1a_gram (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    (hρ : SmoothPosDensity ρ) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ {e : ℕ → Torus d → ℝ}, IsONBL2Zero (withDensityReal ρ) e →
    ∃ (u : ℕ → Lp ℝ 2 (withDensityReal ρ)) (R : Lp ℝ 2 (withDensityReal ρ) →L[ℝ] Lp ℝ 2 (withDensityReal ρ)),
      Orthonormal ℝ u ∧ (∀ x y, ⟪R x, y⟫ = ⟪x, R y⟫) ∧ (∀ u, ⟪R u, u⟫ ≤ ‖u‖ ^ 2) ∧
      (∀ u, c * ‖u‖ ^ 2 ≤ ⟪R u, u⟫) ∧
      ∀ i j, susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j) =
        ⟪u i, R (u j)⟫ := by
  obtain ⟨c, hc0, hc1, R, h1, h2, h3, h4⟩ := e1a_resp hd hs0 hsd hβ hρ
  refine ⟨c, hc0, hc1, fun {e} he => ⟨fun i => (he.memLp i).toLp (e i), R, ?_, h1, h2, h3,
    fun i j => h4 (he.memLp i) (he.memLp j) (he.centered i) (he.centered j)⟩⟩
  have := isProb_withDensityReal hρ.density
  rw [orthonormal_iff_ite]
  intro i j
  rw [PDE.MFLinear.innerLp_eq_l2Inner]
  have := he.orthonormal i j
  unfold l2Inner at this ⊢
  rw [← this]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (he.memLp i), MemLp.coeFn_toLp (he.memLp j)] with x h1 h2
  rw [h1, h2]

theorem e1a_norm_sum {u : ℕ → Lp ℝ 2 (withDensityReal ρ)} (hu : Orthonormal ℝ u) (n : ℕ)
    (x : Fin n → ℝ) : ‖∑ i : Fin n, x i • u i‖ ^ 2 = x ⬝ᵥ x := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
  have := (orthonormal_iff_ite.1 hu)
  simp only [dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [this]; simp [sq]
  · intro j _ hji
    have hne : (j : ℕ) ≠ (i : ℕ) := fun h => hji (Fin.ext h)
    rw [this]; simp [hne]
  · simp

/-- `c I <= C_n <= I` for every finite section of the covariance matrix. -/
theorem e1a_cov_bounds (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    (hρ : SmoothPosDensity ρ) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ {e : ℕ → Torus d → ℝ}, IsONBL2Zero (withDensityReal ρ) e →
    ∀ n : ℕ,
      (((1 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) - Matrix.of fun i j : Fin n =>
        susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j)).PosSemidef ∧
      ((Matrix.of fun i j : Fin n =>
        susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j)) -
        c • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef := by
  obtain ⟨c, hc0, hc1, hall⟩ := e1a_gram hd hs0 hsd hβ hρ
  refine ⟨c, hc0, hc1, fun {e} he n => ?_⟩
  obtain ⟨u, R, hu, hsym, hup, hlow, hC⟩ := hall he
  have hCh : (Matrix.of fun i j : Fin n =>
      susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j)).IsHermitian := by
    refine Matrix.IsHermitian.ext fun i j => ?_
    simp only [Matrix.of_apply, star_trivial, hC]
    exact (hsym _ _).symm.trans (real_inner_comm _ _)
  have h1 : ∀ r : ℝ, (r • (1 : Matrix (Fin n) (Fin n) ℝ)).IsHermitian := fun r => by
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.one_apply, eq_comm]
  have hq : ∀ x : Fin n → ℝ, star x ⬝ᵥ (Matrix.of fun i j : Fin n =>
      susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j)) *ᵥ x =
      ⟪R (∑ i : Fin n, x i • u i), ∑ i : Fin n, x i • u i⟫ := fun x => by
    have key := E0a.s7e_quad u R hsym n x
    simp only [← hC] at key
    exact key
  constructor
  · rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨(h1 1).sub hCh, fun x => ?_⟩
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, hq]
    have := hup (∑ i : Fin n, x i • u i)
    rw [e1a_norm_sum hu] at this
    simp only [star_trivial, smul_eq_mul]
    linarith
  · rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨hCh.sub (h1 c), fun x => ?_⟩
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, hq]
    have := hlow (∑ i : Fin n, x i • u i)
    rw [e1a_norm_sum hu] at this
    simp only [star_trivial, smul_eq_mul]
    linarith

end Concrete

/-! ### Kronecker square bounds -/

section Kron

variable {N : ℕ}

theorem e1a_kron_ge {C : Matrix (Fin N) (Fin N) ℝ} (hC : C.PosSemidef) {c : ℝ} (hc : 0 ≤ c)
    (hD : (C - c • (1 : Matrix (Fin N) (Fin N) ℝ)).PosSemidef) (a : Fin N → Fin N → ℝ) :
    c ^ 2 * ∑ i, ∑ j, a i j ^ 2 ≤ ∑ i, ∑ j, ∑ k, ∑ l, a i j * a k l * (C i k * C j l) := by
  set D : Matrix (Fin N) (Fin N) ℝ := C - c • (1 : Matrix (Fin N) (Fin N) ℝ) with hDdef
  have e : C ⊗ₖ C - (c ^ 2) • (1 : Matrix (Fin N × Fin N) (Fin N × Fin N) ℝ) =
      D ⊗ₖ C + c • ((1 : Matrix (Fin N) (Fin N) ℝ) ⊗ₖ D) := by
    rw [← Matrix.one_kronecker_one]
    ext ⟨i, j⟩ ⟨k, l⟩
    simp only [hDdef, Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply,
      Matrix.kroneckerMap_apply, smul_eq_mul]
    ring
  have hM : (C ⊗ₖ C - (c ^ 2) • (1 : Matrix (Fin N × Fin N) (Fin N × Fin N) ℝ)).PosSemidef := by
    rw [e]
    exact (hD.kronecker hC).add ((Matrix.PosSemidef.one.kronecker hD).smul hc)
  have h0 := hM.dotProduct_mulVec_nonneg (fun p : Fin N × Fin N => a p.1 p.2)
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul,
    E0b.e0b_kron_quad] at h0
  have h1 : star (fun p : Fin N × Fin N => a p.1 p.2) ⬝ᵥ (fun p : Fin N × Fin N => a p.1 p.2) =
      ∑ i, ∑ j, a i j ^ 2 := by
    simp only [dotProduct, star_trivial, Fintype.sum_prod_type, sq]
  rw [h1] at h0
  simp only [smul_eq_mul] at h0
  linarith

end Kron

end HRS.MC.Sec7.E1Aux1

end
