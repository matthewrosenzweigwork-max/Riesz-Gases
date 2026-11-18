import HRS.MS.QsfAux1
import HRS.Prob.HilbertCLT

/-!
# S4.5 packet A2: the abstract resolvent `(I + βK)⁻¹`, uniqueness of responses, covariance form

Namespace `S45`, helper prefix `s45_`.  For a probability measure `ν`, a kernel `g` and a bounded operator `K` on
`L²(ν)` with `IsKData ν g K` (symmetric, nonnegative, centered range, representing `Kop g ν` on centered classes):

* `s45_Rr`: the Lax-Milgram inverse of `I + βK` as a continuous linear equivalence of `L²(ν)`; `s45_Rr_eq`
  `R z + β K R z = z`; `‖R z‖ ≤ ‖z‖`; `R` preserves centered classes;
* `s45_response_iff`: a function `h` is a response of `ψ ∈ L²(ν)` iff `h =ᵐ R P_ν ψ`;
* `s45_susceptibilityCov_eq`: `susceptibilityCov g ν β φ ψ = ⟪P φ, R P ψ⟫`;
* `s45_exists_gaussian`: for a Hilbert basis `b` of a separable Hilbert space `H` and a family `U_i` of centered
  classes with `∑ ‖U_i‖ < ∞` there is a centered Gaussian `γ` on `H` with
  `E[⟨b_i,Z⟩⟨b_j,Z⟩] = ⟪U_i, R U_j⟫`.
-/

open MeasureTheory Filter Topology Set Metric InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace S45

open HRS.Whole HRS.Whole.Q34 HRS.MS.Thm HRS.MS.TcR
open HRS (Euc cbNorm MemCb smoothDist law IsCenteredGaussian)

variable {d : ℕ}

section Resolvent

set_option linter.unusedSectionVars false

variable {ν : Measure (Euc d)} [IsProbabilityMeasure ν] {g : Euc d → ℝ}
  {K : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν}

/-- The bilinear form `B(f,k) = ⟪f,k⟫ + β ⟪K f, k⟫`. -/
def s45_B (K : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) (β : ℝ) : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν →L[ℝ] ℝ :=
  innerSL ℝ + β • (innerSL ℝ : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν →L[ℝ] ℝ).bilinearComp K
    (ContinuousLinearMap.id ℝ _)

theorem s45_B_apply (K : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) (β : ℝ) (f k : Lp ℝ 2 ν) :
    s45_B K β f k = ⟪f, k⟫ + β * ⟪K f, k⟫ := by
  simp [s45_B]
  rfl

theorem s45_B_coercive (hK : IsKData ν g K) {β : ℝ} (hβ : 0 ≤ β) : IsCoercive (s45_B K β) := by
  refine ⟨1, one_pos, fun u => ?_⟩
  rw [s45_B_apply, one_mul, ← real_inner_self_eq_norm_mul_norm]
  have : 0 ≤ β * ⟪K u, u⟫ := mul_nonneg hβ (hK.pos u)
  linarith

/-- The resolvent `(I + βK)⁻¹` on `L²(ν)` (Lax-Milgram inverse). -/
def s45_Rr (hK : IsKData ν g K) {β : ℝ} (hβ : 0 ≤ β) : Lp ℝ 2 ν ≃L[ℝ] Lp ℝ 2 ν :=
  (s45_B_coercive hK hβ).continuousLinearEquivOfBilin.symm

theorem s45_Rr_spec (hK : IsKData ν g K) {β : ℝ} (hβ : 0 ≤ β) (z k : Lp ℝ 2 ν) :
    ⟪z, k⟫ = s45_B K β (s45_Rr hK hβ z) k := by
  have := (s45_B_coercive hK hβ).continuousLinearEquivOfBilin_apply
    ((s45_B_coercive hK hβ).continuousLinearEquivOfBilin.symm z) k
  simpa [s45_Rr] using this

theorem s45_Rr_eq (hK : IsKData ν g K) {β : ℝ} (hβ : 0 ≤ β) (z : Lp ℝ 2 ν) :
    s45_Rr hK hβ z + β • K (s45_Rr hK hβ z) = z := by
  refine (ext_inner_right ℝ fun k => ?_).symm
  rw [s45_Rr_spec hK hβ z k, s45_B_apply, inner_add_left, inner_smul_left]
  simp

theorem s45_Rr_symm_apply (hK : IsKData ν g K) {β : ℝ} (hβ : 0 ≤ β) (w : Lp ℝ 2 ν) :
    (s45_Rr hK hβ).symm w = w + β • K w := by
  have h := s45_Rr_eq hK hβ ((s45_Rr hK hβ).symm w)
  simp only [ContinuousLinearEquiv.apply_symm_apply] at h
  exact h.symm

theorem s45_Rr_norm_le (hK : IsKData ν g K) {β : ℝ} (hβ : 0 ≤ β) (z : Lp ℝ 2 ν) :
    ‖s45_Rr hK hβ z‖ ≤ ‖z‖ := by
  set h := s45_Rr hK hβ z with hh
  have h1 := s45_Rr_spec hK hβ z h
  rw [s45_B_apply] at h1
  have h2 : 0 ≤ β * ⟪K h, h⟫ := mul_nonneg hβ (hK.pos h)
  have h3 : ‖h‖ * ‖h‖ ≤ ⟪z, h⟫ := by
    rw [h1, real_inner_self_eq_norm_mul_norm]; linarith
  have h4 : ⟪z, h⟫ ≤ ‖z‖ * ‖h‖ := real_inner_le_norm z h
  by_cases h0 : ‖h‖ = 0
  · rw [h0]; exact norm_nonneg _
  · have hpos : 0 < ‖h‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    nlinarith

theorem s45_Rr_centered (hK : IsKData ν g K) {β : ℝ} (hβ : 0 ≤ β) {z : Lp ℝ 2 ν}
    (hz : Pc ν z = z) : Pc ν (s45_Rr hK hβ z) = s45_Rr hK hβ z := by
  have h1 := congrArg (Pc ν) (s45_Rr_eq hK hβ z)
  rw [map_add, map_smul, hK.PK, hz] at h1
  have h2 := s45_Rr_eq hK hβ z
  have h3 : Pc ν (s45_Rr hK hβ z) + β • K (s45_Rr hK hβ z) =
      s45_Rr hK hβ z + β • K (s45_Rr hK hβ z) := h1.trans h2.symm
  exact add_right_cancel h3

/-- `⟪z, R w⟫ = B(R z, R w)`: symmetric in `z, w`. -/
theorem s45_inner_Rr_eq_B (hK : IsKData ν g K) {β : ℝ} (hβ : 0 ≤ β) (z w : Lp ℝ 2 ν) :
    ⟪z, s45_Rr hK hβ w⟫ = s45_B K β (s45_Rr hK hβ z) (s45_Rr hK hβ w) :=
  s45_Rr_spec hK hβ z _

theorem s45_inner_Rr_comm (hK : IsKData ν g K) {β : ℝ} (hβ : 0 ≤ β) (z w : Lp ℝ 2 ν) :
    ⟪z, s45_Rr hK hβ w⟫ = ⟪w, s45_Rr hK hβ z⟫ := by
  rw [s45_inner_Rr_eq_B hK hβ, s45_inner_Rr_eq_B hK hβ, s45_B_apply, s45_B_apply]
  have e1 : ⟪s45_Rr hK hβ w, s45_Rr hK hβ z⟫ = ⟪s45_Rr hK hβ z, s45_Rr hK hβ w⟫ :=
    real_inner_comm _ _
  have e2 : ⟪K (s45_Rr hK hβ w), s45_Rr hK hβ z⟫ = ⟪K (s45_Rr hK hβ z), s45_Rr hK hβ w⟫ := by
    rw [hK.symm, real_inner_comm]
  rw [e1, e2]

theorem s45_inner_Rr_nonneg (hK : IsKData ν g K) {β : ℝ} (hβ : 0 ≤ β) (z : Lp ℝ 2 ν) :
    0 ≤ ⟪z, s45_Rr hK hβ z⟫ := by
  rw [s45_inner_Rr_eq_B hK hβ, s45_B_apply]
  exact add_nonneg real_inner_self_nonneg (mul_nonneg hβ (hK.pos _))

theorem s45_inner_Rr_le (hK : IsKData ν g K) {β : ℝ} (hβ : 0 ≤ β) (z : Lp ℝ 2 ν) :
    ⟪z, s45_Rr hK hβ z⟫ ≤ ‖z‖ ^ 2 := by
  calc ⟪z, s45_Rr hK hβ z⟫ ≤ ‖z‖ * ‖s45_Rr hK hβ z‖ := real_inner_le_norm _ _
    _ ≤ ‖z‖ * ‖z‖ := mul_le_mul_of_nonneg_left (s45_Rr_norm_le hK hβ z) (norm_nonneg _)
    _ = ‖z‖ ^ 2 := by ring

end Resolvent

section Response

variable {ν : Measure (Euc d)} [IsProbabilityMeasure ν] {g : Euc d → ℝ}
  {K : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν}

theorem s45_memLp_projMean {ψ : Euc d → ℝ} (hψ : MemLp ψ 2 ν) : MemLp (projMean ν ψ) 2 ν := by
  unfold projMean
  exact hψ.sub (memLp_const _)

/-- The centered class `P_ν ψ ∈ L²(ν)`. -/
def s45_U (ψ : Euc d → ℝ) (hψ : MemLp ψ 2 ν) : Lp ℝ 2 ν :=
  (s45_memLp_projMean hψ).toLp (projMean ν ψ)

theorem s45_U_ae {ψ : Euc d → ℝ} (hψ : MemLp ψ 2 ν) :
    (s45_U ψ hψ : Euc d → ℝ) =ᵐ[ν] projMean ν ψ :=
  MemLp.coeFn_toLp _

theorem s45_centered_iff (F : Lp ℝ 2 ν) : Pc ν F = F ↔ ∫ x, F x ∂ν = 0 := by
  rw [← inner_one2]
  constructor
  · intro h
    have := inner_one2_Pc (ν := ν) F
    rwa [h] at this
  · intro h
    rw [Pc_apply, h]
    simp

theorem s45_U_centered {ψ : Euc d → ℝ} (hψ : MemLp ψ 2 ν) : Pc ν (s45_U ψ hψ) = s45_U ψ hψ := by
  rw [s45_centered_iff, integral_congr_ae (s45_U_ae hψ)]
  have hi : Integrable ψ ν := hψ.integrable (by norm_num)
  simp only [projMean, pair]
  rw [integral_sub hi (integrable_const _), integral_const]
  simp

/-- A function is a response of `ψ ∈ L²(ν)` iff it is a.e. `R P_ν ψ`. -/
theorem s45_response_iff (hK : IsKData ν g K) {β : ℝ} (hβ : 0 < β) {ψ : Euc d → ℝ}
    (hψ : MemLp ψ 2 ν) (h : Euc d → ℝ) :
    IsResponse g ν β ψ h ↔ h =ᵐ[ν] (s45_Rr hK hβ.le (s45_U ψ hψ) : Euc d → ℝ) := by
  set U := s45_U ψ hψ with hU
  have hUc : Pc ν U = U := s45_U_centered hψ
  constructor
  · rintro ⟨hh, heq⟩
    obtain ⟨F, hF, hPF⟩ := exists_class hh
    have hkF : Kop g ν h = Kop g ν (F : Euc d → ℝ) := tc2_kop_congr_ae hF
    have h1 : Kop g ν (F : Euc d → ℝ) =ᵐ[ν] (K F : Euc d → ℝ) := hK.kop F hPF
    have h2 : F + β • K F = U := by
      refine Lp.ext ?_
      filter_upwards [Lp.coeFn_add F (β • K F), Lp.coeFn_smul β (K F), hF, h1, heq, s45_U_ae hψ]
        with x e1 e2 e3 e4 e5 e6
      rw [e1, Pi.add_apply, e2, Pi.smul_apply, smul_eq_mul, ← e4, ← e3, e6, ← e5, hkF]
    have h3 : F = s45_Rr hK hβ.le U := by
      rw [← ContinuousLinearEquiv.symm_apply_eq, s45_Rr_symm_apply]
      exact h2
    filter_upwards [hF] with x hx
    rw [hx, h3]
  · intro hh
    have hPR : Pc ν (s45_Rr hK hβ.le U) = s45_Rr hK hβ.le U := s45_Rr_centered hK hβ.le hUc
    have hkF : Kop g ν h = Kop g ν (s45_Rr hK hβ.le U : Euc d → ℝ) := tc2_kop_congr_ae hh
    have h1 := hK.kop (s45_Rr hK hβ.le U) hPR
    refine ⟨⟨(Lp.memLp (s45_Rr hK hβ.le U)).ae_eq hh.symm, ?_⟩, ?_⟩
    · rw [integral_congr_ae hh]
      exact (s45_centered_iff _).1 hPR
    · have hE := s45_Rr_eq hK hβ.le U
      filter_upwards [hh, h1, Lp.coeFn_add (s45_Rr hK hβ.le U) (β • K (s45_Rr hK hβ.le U)),
        Lp.coeFn_smul β (K (s45_Rr hK hβ.le U)), s45_U_ae hψ] with x e1 e2 e3 e4 e5
      have e6 := congrFun (congrArg (fun F : Lp ℝ 2 ν => (F : Euc d → ℝ)) hE) x
      rw [e3, Pi.add_apply, e4, Pi.smul_apply, smul_eq_mul, e5] at e6
      rw [e1, hkF, e2, e6]

theorem s45_exists_response (hK : IsKData ν g K) {β : ℝ} (hβ : 0 < β) {ψ : Euc d → ℝ}
    (hψ : MemLp ψ 2 ν) : ∃ h, IsResponse g ν β ψ h :=
  ⟨_, (s45_response_iff hK hβ hψ _).2 (Filter.EventuallyEq.refl _ _)⟩

theorem s45_responseInverse_ae (hK : IsKData ν g K) {β : ℝ} (hβ : 0 < β) {ψ : Euc d → ℝ}
    (hψ : MemLp ψ 2 ν) :
    responseInverse g ν β ψ =ᵐ[ν] (s45_Rr hK hβ.le (s45_U ψ hψ) : Euc d → ℝ) := by
  have hex := s45_exists_response hK hβ hψ
  unfold responseInverse
  rw [dif_pos hex]
  exact (s45_response_iff hK hβ hψ _).1 hex.choose_spec

theorem s45_susceptibilityCov_eq (hK : IsKData ν g K) {β : ℝ} (hβ : 0 < β) {φ ψ : Euc d → ℝ}
    (hφ : MemLp φ 2 ν) (hψ : MemLp ψ 2 ν) :
    susceptibilityCov g ν β φ ψ = ⟪s45_U φ hφ, s45_Rr hK hβ.le (s45_U ψ hψ)⟫ := by
  unfold susceptibilityCov
  exact l2Inner_eq (s45_U_ae hφ).symm (s45_responseInverse_ae hK hβ hψ)

end Response

section Gauss

variable {ν : Measure (Euc d)} [IsProbabilityMeasure ν] {g : Euc d → ℝ}
  {K : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν} {ι : Type} {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H]

theorem s45_abs_inner_le (b : HilbertBasis ι ℝ H) (i : ι) (x : H) : |⟪b i, x⟫| ≤ ‖x‖ := by
  have := abs_real_inner_le_norm (b i) x
  rwa [b.orthonormal.1 i, one_mul] at this

theorem s45_summable_T (b : HilbertBasis ι ℝ H) {U : ι → Lp ℝ 2 ν}
    (hU : Summable fun i => ‖U i‖) (x : H) : Summable fun i => ⟪b i, x⟫ • U i := by
  refine Summable.of_norm_bounded (hU.mul_left ‖x‖) fun i => ?_
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (s45_abs_inner_le b i x) (norm_nonneg _)

/-- `T x = ∑_i ⟪b_i, x⟫ U_i`. -/
def s45_T (b : HilbertBasis ι ℝ H) {U : ι → Lp ℝ 2 ν} (hU : Summable fun i => ‖U i‖) :
    H →L[ℝ] Lp ℝ 2 ν :=
  LinearMap.mkContinuous
    { toFun := fun x => ∑' i, ⟪b i, x⟫ • U i
      map_add' := fun x y => by
        simp only [inner_add_right, add_smul]
        exact (s45_summable_T b hU x).tsum_add (s45_summable_T b hU y)
      map_smul' := fun c x => by
        simp only [inner_smul_right, smul_eq_mul, mul_smul, RingHom.id_apply]
        exact (s45_summable_T b hU x).tsum_const_smul c }
    (∑' i, ‖U i‖) (fun x => by
      show ‖∑' i, ⟪b i, x⟫ • U i‖ ≤ (∑' i, ‖U i‖) * ‖x‖
      have hs : Summable fun i => ‖⟪b i, x⟫ • U i‖ := by
        refine Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => ?_) (hU.mul_left ‖x‖)
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (s45_abs_inner_le b i x) (norm_nonneg _)
      refine (norm_tsum_le_tsum_norm hs).trans ?_
      rw [mul_comm, ← tsum_mul_left]
      refine Summable.tsum_le_tsum (fun i => ?_) hs (hU.mul_left ‖x‖)
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (s45_abs_inner_le b i x) (norm_nonneg _))

theorem s45_T_apply (b : HilbertBasis ι ℝ H) {U : ι → Lp ℝ 2 ν} (hU : Summable fun i => ‖U i‖)
    (x : H) : s45_T b hU x = ∑' i, ⟪b i, x⟫ • U i := rfl

theorem s45_T_basis (b : HilbertBasis ι ℝ H) {U : ι → Lp ℝ 2 ν} (hU : Summable fun i => ‖U i‖)
    (j : ι) : s45_T b hU (b j) = U j := by
  classical
  rw [s45_T_apply]
  rw [tsum_eq_single j]
  · rw [real_inner_self_eq_norm_sq, b.orthonormal.1 j]; simp
  · intro i hij
    have := b.orthonormal.2 hij
    rw [this, zero_smul]

/-- The covariance form `C(x,y) = ⟪T x, R T y⟫`. -/
def s45_C (hK : IsKData ν g K) {β : ℝ} (hβ : 0 ≤ β) (b : HilbertBasis ι ℝ H)
    {U : ι → Lp ℝ 2 ν} (hU : Summable fun i => ‖U i‖) : H →L[ℝ] H →L[ℝ] ℝ :=
  (innerSL ℝ : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν →L[ℝ] ℝ).bilinearComp (s45_T b hU)
    ((s45_Rr hK hβ : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν).comp (s45_T b hU))

theorem s45_C_apply (hK : IsKData ν g K) {β : ℝ} (hβ : 0 ≤ β) (b : HilbertBasis ι ℝ H)
    {U : ι → Lp ℝ 2 ν} (hU : Summable fun i => ‖U i‖) (x y : H) :
    s45_C hK hβ b hU x y = ⟪s45_T b hU x, s45_Rr hK hβ (s45_T b hU y)⟫ := by
  simp [s45_C]

theorem s45_C_basis (hK : IsKData ν g K) {β : ℝ} (hβ : 0 ≤ β) (b : HilbertBasis ι ℝ H)
    {U : ι → Lp ℝ 2 ν} (hU : Summable fun i => ‖U i‖) (i j : ι) :
    s45_C hK hβ b hU (b i) (b j) = ⟪U i, s45_Rr hK hβ (U j)⟫ := by
  rw [s45_C_apply, s45_T_basis, s45_T_basis]

theorem s45_summable_sq {a : ι → ℝ} (ha0 : ∀ i, 0 ≤ a i) (ha : Summable a) :
    Summable fun i => a i ^ 2 := by
  obtain ⟨B, hB⟩ := ha.tendsto_cofinite_zero.bddAbove_range_of_cofinite
  refine Summable.of_nonneg_of_le (fun i => sq_nonneg _) (fun i => ?_) (ha.mul_left B)
  have : a i ≤ B := hB ⟨i, rfl⟩
  nlinarith [ha0 i]

theorem s45_isTraceClassCov (hK : IsKData ν g K) {β : ℝ} (hβ : 0 ≤ β) (b : HilbertBasis ι ℝ H)
    {U : ι → Lp ℝ 2 ν} (hU : Summable fun i => ‖U i‖) :
    HRS.IsTraceClassCov (s45_C hK hβ b hU) where
  symm x y := by
    rw [s45_C_apply, s45_C_apply]
    exact s45_inner_Rr_comm hK hβ _ _
  nonneg x := by
    rw [s45_C_apply]
    exact s45_inner_Rr_nonneg hK hβ _
  trace := by
    refine ⟨ι, b, ?_⟩
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_)
      (s45_summable_sq (fun i => norm_nonneg (U i)) hU)
    · rw [s45_C_basis]
      exact s45_inner_Rr_nonneg hK hβ _
    · rw [s45_C_basis]
      exact s45_inner_Rr_le hK hβ _

/-- **Gaussian existence.**  On a separable Hilbert space `H` with Hilbert basis `b`, a summable family `U_i` in
`L²(ν)` gives a centered Gaussian `γ` with `E[⟨b_i,Z⟩⟨b_j,Z⟩] = ⟪U_i, R U_j⟫`. -/
theorem s45_exists_gaussian [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (hK : IsKData ν g K) {β : ℝ} (hβ : 0 ≤ β) (b : HilbertBasis ι ℝ H)
    {U : ι → Lp ℝ 2 ν} (hU : Summable fun i => ‖U i‖) :
    ∃ γ : Measure H, IsProbabilityMeasure γ ∧ IsCenteredGaussian γ ∧ ∀ i j,
      Integrable (fun z => ⟪b i, z⟫ * ⟪b j, z⟫) γ ∧
        ∫ z, ⟪b i, z⟫ * ⟪b j, z⟫ ∂γ = ⟪U i, s45_Rr hK hβ (U j)⟫ := by
  obtain ⟨γ, hp, hg, hcov⟩ := HRS.exists_centeredGaussian_of_traceClass (s45_C hK hβ b hU)
    (s45_isTraceClassCov hK hβ b hU)
  refine ⟨γ, hp, hg, fun i j => ?_⟩
  have := hg.1
  have hmem : MemLp id 2 γ := ProbabilityTheory.IsGaussian.memLp_two_id
  have hL : ∀ x : H, MemLp (fun z => ⟪x, z⟫) 2 γ := fun x => (innerSL ℝ x).comp_memLp' hmem
  refine ⟨(hL (b i)).integrable_mul (hL (b j)), ?_⟩
  have h := ProbabilityTheory.covarianceBilin_apply hmem (b i) (b j)
  rw [hcov, HRS.HilbertCLTAux.gaussian_mean_zero hg, s45_C_basis] at h
  rw [h]
  simp

end Gauss

end S45

end
