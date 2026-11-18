import HRS.MC.Sec7Vocab
import HRS.PDE.MeanFieldLinearResponse
import HRS.Prob.HilbertCLT
import HRS.Energy.StaticLimitGauss

/-!
# Packet `s7_E0a_gauss_exists`: the Gaussian data of Proposition 7.18 exist

Route.  The response operator `R = (I + beta K P)^{-1}` on `L^2(mu)` of `PDE/MeanFieldLinearResponse`
is bounded, self-adjoint and nonnegative, and `susceptibilityCov (e i) (e j) = <e_i, R e_j>` for the
centred `L^2` functions `e_i`.  Hence every finite section of the covariance matrix is positive
semidefinite (`s7e_cov_psd`, also used by the Isserlis packet).  Existence: with weights `w_i = 2^{-i}`
the weighted analysis operator `L^2(mu) -> l^2`, its adjoint `A` (`A delta_i = w_i e_i`, Hilbert-Schmidt),
the form `B(x,y) = <A x, R A y>` is trace class on `l^2`, so `exists_centeredGaussian_of_traceClass`
gives a centred Gaussian `Z` on `l^2`; `G_i = Z_i / w_i`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace Matrix

noncomputable section

namespace HRS.MC.Sec7.E0a

open HRS HRS.Sec7 HRS.StaticLimitAux Torus

variable {d : ℕ}

/-! ### The response operator and the covariance as an inner product -/

theorem s7e_resp_op (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) :
    ∃ R : Lp ℝ 2 (withDensityReal ρ) →L[ℝ] Lp ℝ 2 (withDensityReal ρ),
      (∀ x y, ⟪R x, y⟫ = ⟪x, R y⟫) ∧ (∀ y, 0 ≤ ⟪R y, y⟫) ∧
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
  refine ⟨R, hRsym, hRpos, fun {φ ψ} hφ hψ hφ0 hψ0 => ?_⟩
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


theorem s7e_cov_gram (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {e : ℕ → Torus d → ℝ}
    (he : IsONBL2Zero (withDensityReal ρ) e) :
    ∃ (u : ℕ → Lp ℝ 2 (withDensityReal ρ)) (R : Lp ℝ 2 (withDensityReal ρ) →L[ℝ] Lp ℝ 2 (withDensityReal ρ)),
      Orthonormal ℝ u ∧ (∀ x y, ⟪R x, y⟫ = ⟪x, R y⟫) ∧ (∀ y, 0 ≤ ⟪R y, y⟫) ∧
      ∀ i j, susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j) =
        ⟪u i, R (u j)⟫ := by
  obtain ⟨R, h1, h2, h3⟩ := s7e_resp_op hd hs0 hsd hβ hρ
  refine ⟨fun i => (he.memLp i).toLp (e i), R, ?_, h1, h2,
    fun i j => h3 (he.memLp i) (he.memLp j) (he.centered i) (he.centered j)⟩
  rw [orthonormal_iff_ite]
  intro i j
  rw [PDE.MFLinear.innerLp_eq_l2Inner]
  have := he.orthonormal i j
  unfold l2Inner at this ⊢
  rw [← this]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (he.memLp i), MemLp.coeFn_toLp (he.memLp j)] with x h1 h2
  rw [h1, h2]

theorem s7e_quad {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (u : ℕ → E)
    (R : E →L[ℝ] E) (hsym : ∀ x y, ⟪R x, y⟫ = ⟪x, R y⟫) (n : ℕ) (x : Fin n → ℝ) :
    star x ⬝ᵥ (Matrix.of fun i j : Fin n => ⟪u i, R (u j)⟫) *ᵥ x =
      ⟪R (∑ i : Fin n, x i • u i), ∑ i : Fin n, x i • u i⟫ := by
  have hh : ∀ a b : E, ⟪R a, b⟫ = ⟪R b, a⟫ := fun a b =>
    (hsym _ _).trans (real_inner_comm _ _).symm
  simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, star_trivial, map_sum, map_smul,
    sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← real_inner_comm (u j) (R (u i)), hh (u i) (u j)]; ring

theorem s7e_cov_psd (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {e : ℕ → Torus d → ℝ}
    (he : IsONBL2Zero (withDensityReal ρ) e) (n : ℕ) :
    (Matrix.of fun i j : Fin n =>
      susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j)).PosSemidef := by
  obtain ⟨u, R, -, hsym, hpos, hC⟩ := s7e_cov_gram hd hs0 hsd hβ hρ he
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨Matrix.IsHermitian.ext fun i j => ?_, fun x => ?_⟩
  · simp only [Matrix.of_apply, star_trivial, hC]
    exact (hsym _ _).symm.trans (real_inner_comm _ _)
  · have key := s7e_quad u R hsym n x
    simp only [← hC] at key
    rw [key]; exact hpos _

/-- the covariance matrices are bounded by `lam = ||R||` -/
theorem s7e_cov_bdd (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {e : ℕ → Torus d → ℝ}
    (he : IsONBL2Zero (withDensityReal ρ) e) :
    ∃ lam : ℝ, 0 ≤ lam ∧ ∀ n : ℕ, ((lam • (1 : Matrix (Fin n) (Fin n) ℝ)) -
      Matrix.of fun i j : Fin n =>
        susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β (e i) (e j)).PosSemidef := by
  obtain ⟨u, R, hu, hsym, hpos, hC⟩ := s7e_cov_gram hd hs0 hsd hβ hρ he
  refine ⟨‖R‖, norm_nonneg _, fun n => ?_⟩
  have hCh := (s7e_cov_psd hd hs0 hsd hβ hρ he n).isHermitian
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · refine Matrix.IsHermitian.sub ?_ hCh
    ext i j
    simp [Matrix.conjTranspose_apply, Matrix.one_apply, eq_comm]
  · have key := s7e_quad u R hsym n x
    simp only [← hC] at key
    set v : Lp ℝ 2 (withDensityReal ρ) := ∑ i : Fin n, x i • u i with hv
    have hnorm : ‖v‖ ^ 2 = x ⬝ᵥ x := by
      rw [← real_inner_self_eq_norm_sq, hv]
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
    have hle : ⟪R v, v⟫ ≤ ‖R‖ * (x ⬝ᵥ x) := by
      calc ⟪R v, v⟫ ≤ ‖R v‖ * ‖v‖ := real_inner_le_norm _ _
        _ ≤ (‖R‖ * ‖v‖) * ‖v‖ :=
            mul_le_mul_of_nonneg_right (R.le_opNorm v) (norm_nonneg _)
        _ = ‖R‖ * ‖v‖ ^ 2 := by ring
        _ = _ := by rw [hnorm]
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, key]
    simp only [star_trivial, smul_eq_mul]
    linarith

/-! ### The Hilbert space `l^2(N)` and the weighted analysis operator -/

/-- `l^2(N)` as a type synonym (so that the Borel structure can be declared). -/
abbrev L2N : Type := lp (fun _ : ℕ => ℝ) 2

instance : MeasurableSpace L2N := borel _
instance : BorelSpace L2N := ⟨rfl⟩
instance : SecondCountableTopology L2N := by
  have : TopologicalSpace.SeparableSpace (lp (fun _ : ℕ => ℝ) 2) := separable_lp
  exact UniformSpace.secondCountable_of_separable (lp (fun _ : ℕ => ℝ) 2)

/-- the unit vector `delta_i` of `l^2(N)` -/
def e0Delta (i : ℕ) : L2N := (lp.single (E := fun _ : ℕ => ℝ) 2 i (1 : ℝ) : lp (fun _ : ℕ => ℝ) 2)

/-- the weights `2^{-i}` -/
def e0w (i : ℕ) : ℝ := (1 / 2 : ℝ) ^ i

theorem e0w_pos (i : ℕ) : 0 < e0w i := by unfold e0w; positivity

theorem e0w_le_one (i : ℕ) : e0w i ≤ 1 := by
  unfold e0w; exact pow_le_one₀ (by norm_num) (by norm_num)

theorem summable_e0w_sq : Summable fun i => e0w i ^ 2 := by
  have : (fun i => e0w i ^ 2) = fun i => (1 / 4 : ℝ) ^ i := by
    funext i; unfold e0w; rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [this]; exact summable_geometric_of_lt_one (by norm_num) (by norm_num)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem e0_memℓp {u : ℕ → E} (hu : Orthonormal ℝ u) (x : E) :
    Memℓp (fun i => e0w i * ⟪u i, x⟫) 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) (hu.inner_products_summable x)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, norm_mul, mul_pow]
  have h1 : ‖e0w i‖ ^ 2 ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (e0w_pos i)]
    nlinarith [e0w_pos i, e0w_le_one i]
  calc ‖e0w i‖ ^ 2 * ‖⟪u i, x⟫‖ ^ 2 ≤ 1 * ‖⟪u i, x⟫‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = _ := one_mul _


/-- the weighted analysis operator `x |-> (w_i <u_i, x>)_i : E -> l^2` -/
def e0An {u : ℕ → E} (hu : Orthonormal ℝ u) : E →L[ℝ] L2N :=
  LinearMap.mkContinuous
    { toFun := fun x => (⟨fun i => e0w i * ⟪u i, x⟫, e0_memℓp hu x⟩ : lp (fun _ : ℕ => ℝ) 2)
      map_add' := fun x y => by
        refine Subtype.ext (funext fun i => ?_)
        show e0w i * ⟪u i, x + y⟫ = e0w i * ⟪u i, x⟫ + e0w i * ⟪u i, y⟫
        rw [inner_add_right, mul_add]
      map_smul' := fun c x => by
        refine Subtype.ext (funext fun i => ?_)
        simp [lp.coeFn_smul, inner_smul_right]; ring } 1 (fun x => by
    have h2 : ‖(⟨fun i => e0w i * ⟪u i, x⟫, e0_memℓp hu x⟩ : lp (fun _ : ℕ => ℝ) 2)‖ ^ 2 ≤ ‖x‖ ^ 2 := by
      have := lp.norm_rpow_eq_tsum (p := 2) (by norm_num)
        (⟨fun i => e0w i * ⟪u i, x⟫, e0_memℓp hu x⟩ : lp (fun _ : ℕ => ℝ) 2)
      simp only [ENNReal.toReal_ofNat, Real.rpow_two] at this
      rw [this]
      refine le_trans (Summable.tsum_le_tsum (fun i => ?_) ?_ (hu.inner_products_summable x))
        (hu.tsum_inner_products_le x)
      · simp only [norm_mul, mul_pow]
        have h1 : ‖e0w i‖ ^ 2 ≤ 1 := by
          rw [Real.norm_eq_abs, abs_of_pos (e0w_pos i)]
          nlinarith [e0w_pos i, e0w_le_one i]
        calc ‖e0w i‖ ^ 2 * ‖⟪u i, x⟫‖ ^ 2 ≤ 1 * ‖⟪u i, x⟫‖ ^ 2 :=
              mul_le_mul_of_nonneg_right h1 (by positivity)
          _ = _ := one_mul _
      · have := (memℓp_gen_iff (p := 2) (by norm_num)).1 (e0_memℓp hu x)
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using this
    rw [one_mul]
    exact le_of_sq_le_sq (by simpa using h2) (norm_nonneg _))

theorem e0An_apply {u : ℕ → E} (hu : Orthonormal ℝ u) (x : E) (i : ℕ) :
    ((e0An hu x : L2N) : lp (fun _ : ℕ => ℝ) 2) i = e0w i * ⟪u i, x⟫ := rfl

/-- the synthesis operator `A = (analysis)^*`, `A delta_i = w_i u_i` -/
def e0Syn {u : ℕ → E} (hu : Orthonormal ℝ u) : L2N →L[ℝ] E := ContinuousLinearMap.adjoint (e0An hu)

theorem e0Syn_delta {u : ℕ → E} (hu : Orthonormal ℝ u) (i : ℕ) :
    e0Syn hu (e0Delta i) = e0w i • u i := by
  refine ext_inner_right ℝ fun x => ?_
  rw [e0Syn, ContinuousLinearMap.adjoint_inner_left, real_inner_smul_left]
  unfold e0Delta
  rw [lp.inner_single_left]
  simp [e0An_apply]


/-- the covariance form `B(x,y) = <A x, R A y>` on `l^2` -/
def e0B {u : ℕ → E} (hu : Orthonormal ℝ u) (R : E →L[ℝ] E) : L2N →L[ℝ] L2N →L[ℝ] ℝ :=
  (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).bilinearComp (e0Syn hu) (R ∘L e0Syn hu)

theorem e0B_apply {u : ℕ → E} (hu : Orthonormal ℝ u) (R : E →L[ℝ] E) (x y : L2N) :
    e0B hu R x y = ⟪e0Syn hu x, R (e0Syn hu y)⟫ := by
  simp [e0B]

theorem e0_traceClass {u : ℕ → E} (hu : Orthonormal ℝ u) (R : E →L[ℝ] E)
    (hsym : ∀ x y, ⟪R x, y⟫ = ⟪x, R y⟫) (hpos : ∀ y, 0 ≤ ⟪R y, y⟫) :
    IsTraceClassCov (e0B hu R) where
  symm := fun x y => by
    rw [e0B_apply, e0B_apply, real_inner_comm, hsym]
  nonneg := fun x => by
    rw [e0B_apply, real_inner_comm]; exact hpos _
  trace := by
    refine ⟨ℕ, HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℝ L2N), ?_⟩
    have hb : ∀ i, (HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℝ L2N) : HilbertBasis ℕ ℝ L2N) i
        = e0Delta i := fun i => by
      classical
      rw [← HilbertBasis.repr_symm_single]; rfl
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_)
      ((summable_e0w_sq).mul_left ‖R‖)
    · rw [hb, e0B_apply, real_inner_comm]; exact hpos _
    · rw [hb, e0B_apply, e0Syn_delta, map_smul, real_inner_smul_left, real_inner_smul_right]
      have h1 : ⟪u i, R (u i)⟫ ≤ ‖R‖ := by
        calc ⟪u i, R (u i)⟫ ≤ ‖u i‖ * ‖R (u i)‖ := real_inner_le_norm _ _
          _ ≤ ‖u i‖ * (‖R‖ * ‖u i‖) :=
              mul_le_mul_of_nonneg_left (R.le_opNorm _) (norm_nonneg _)
          _ = ‖R‖ := by rw [hu.1 i]; ring
      calc e0w i * (e0w i * ⟪u i, R (u i)⟫) = e0w i ^ 2 * ⟪u i, R (u i)⟫ := by ring
        _ ≤ e0w i ^ 2 * ‖R‖ := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
        _ = ‖R‖ * e0w i ^ 2 := by ring


/-- the coordinate map `z |-> (z_i / w_i)_{i<n}` -/
def e0F (n : ℕ) : L2N →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun i : Fin n => (e0w i)⁻¹ • innerSL ℝ (e0Delta i)

theorem e0F_apply (n : ℕ) (z : L2N) (i : Fin n) : e0F n z i = (e0w i)⁻¹ * ⟪e0Delta i, z⟫ := by
  simp [e0F]

theorem e0F_adjoint (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    ContinuousLinearMap.adjoint (e0F n) x = ∑ i : Fin n, (x i * (e0w i)⁻¹) • e0Delta i := by
  refine ext_inner_right ℝ fun z => ?_
  rw [ContinuousLinearMap.adjoint_inner_left, PiLp.inner_apply, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_left, e0F_apply]
  simp only [RCLike.inner_apply, conj_trivial]
  ring

theorem e0F_syn {u : ℕ → E} (hu : Orthonormal ℝ u) (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    e0Syn hu (ContinuousLinearMap.adjoint (e0F n) x) = ∑ i : Fin n, x i • u i := by
  rw [e0F_adjoint, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, e0Syn_delta, smul_smul]
  have := (e0w_pos i).ne'
  rw [mul_assoc, inv_mul_cancel₀ this, mul_one]


/-! ### The packet -/

theorem s7_E0a_gauss_exists_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (e : ℕ → Torus d → ℝ)
    (he : IsONBL2Zero (withDensityReal ρ) e) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P) (G : ℕ → Ω → ℝ),
      s7_GaussData d s β ρ e P G := by
  obtain ⟨u, R, hu, hsym, hpos, hC⟩ := s7e_cov_gram hd hs0 hsd hβ hρ he
  obtain ⟨γ, hp, hg, hcov⟩ := exists_centeredGaussian_of_traceClass (e0B hu R)
    (e0_traceClass hu R hsym hpos)
  refine ⟨L2N, inferInstance, γ, hp, fun i z => (e0w i)⁻¹ * ⟪e0Delta i, z⟫, fun i => ?_, fun n => ?_⟩
  · exact (continuous_const.mul (continuous_const.inner continuous_id)).measurable
  · have hG := hg.1
    have hfun : (fun ω : L2N => (WithLp.toLp 2 fun i : Fin n => (e0w i)⁻¹ * ⟪e0Delta i, ω⟫ :
        EuclideanSpace ℝ (Fin n))) = ⇑(e0F n) := by
      funext ω; ext i; rw [e0F_apply]
    show γ.map _ = _
    rw [hfun]
    apply IsGaussian.ext
    · simp only [id_eq]
      rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id, integral_id_multivariateGaussian]
      have := HilbertCLTAux.gaussian_mean_zero hg
      simp only [id] at this
      rw [this, map_zero]
    · refine ContinuousLinearMap.ext fun x => ContinuousLinearMap.ext fun y => ?_
      rw [covarianceBilin_map IsGaussian.memLp_two_id, hcov, e0B_apply, e0F_syn, e0F_syn,
        covarianceBilin_multivariateGaussian (s7e_cov_psd hd hs0 hsd hβ hρ he n)]
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, hC, map_sum, map_smul,
        sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring

end HRS.MC.Sec7.E0a
