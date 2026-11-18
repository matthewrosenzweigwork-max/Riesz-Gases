import HRS.MC.SEdgeVocab

/-!
# Packet B8a: second-order Gaussian integration by parts (semidefinite covariance)

Relocated proof of `HRS.MC.SEdge.sed_B8a_gauss_ibp2`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators MatrixOrder

noncomputable section

namespace HRS.MC.SEdge.B8a

open HRS HRS.Q66 HRS.Sec7

variable {m p : ℕ}

/-- The linear functional `x ↦ ∑ k, u k * x k`. -/
def b8a_ell (u : Fin (m + 1) → ℝ) : EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] ℝ :=
  ∑ k, u k • EuclideanSpace.proj k

lemma b8a_ell_apply (u : Fin (m + 1) → ℝ) (x : EuclideanSpace ℝ (Fin (m + 1))) :
    b8a_ell u x = ∑ k, u k * x k := by
  simp [b8a_ell]

/-- first-order Gaussian IBP in an arbitrary direction -/
lemma b8a_ibp1 (u : Fin (m + 1) → ℝ) {h : EuclideanSpace ℝ (Fin (m + 1)) → ℝ}
    (hh : ContDiff ℝ 1 h) (K : ℝ) (hK : ∀ x, |h x| ≤ K * (1 + ‖x‖))
    (hK' : ∀ x, ‖fderiv ℝ h x‖ ≤ K * (1 + ‖x‖)) :
    ∫ x, (∑ k, u k * x k) * h x ∂(stdGaussian (EuclideanSpace ℝ (Fin (m + 1)))) =
      ∫ x, fderiv ℝ h x (WithLp.toLp 2 u) ∂(stdGaussian (EuclideanSpace ℝ (Fin (m + 1)))) := by
  set γ := stdGaussian (EuclideanSpace ℝ (Fin (m + 1))) with hγ
  have hhc : Continuous h := hh.continuous
  have hdc : ∀ k : Fin (m + 1), Continuous (fun x => fderiv ℝ h x (EuclideanSpace.single k 1)) :=
    fun k => (hh.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdK : ∀ k : Fin (m + 1), ∀ x, |fderiv ℝ h x (EuclideanSpace.single k 1)| ≤ K * (1 + ‖x‖) := by
    intro k x
    refine le_trans ?_ (hK' x)
    have := (fderiv ℝ h x).le_opNorm (EuclideanSpace.single k 1)
    simpa [Real.norm_eq_abs] using this
  have e1 : ∀ x, (∑ k, u k * x k) * h x = ∑ k, u k * (x k * h x) := by
    intro x; rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun k _ => by ring
  have hvec : (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin (m + 1))) =
      ∑ k, u k • EuclideanSpace.single k (1 : ℝ) := by
    ext k; simp [Finset.sum_apply, Pi.single_apply]
  have e2 : ∀ x, fderiv ℝ h x (WithLp.toLp 2 u) =
      ∑ k, u k * fderiv ℝ h x (EuclideanSpace.single k 1) := by
    intro x; rw [hvec, map_sum]; simp
  simp_rw [e1, e2]
  rw [integral_finsetSum _ (fun k _ => ?_), integral_finsetSum _ (fun k _ => ?_)]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul, integral_const_mul]
    congr 1
    exact q66_stdGaussian_ibp k hh K hK hK'
  · exact (q66_std_integrable_of_growth (hdc k) K (hdK k)).const_mul _
  · exact (q66_stdGaussian_integrable_growth hhc.aestronglyMeasurable K hK k).const_mul _


/-- first-order Gaussian IBP for a function with bounded value and derivative -/
lemma b8a_ibp1_bdd (u : Fin (m + 1) → ℝ) {h : EuclideanSpace ℝ (Fin (m + 1)) → ℝ}
    (hh : ContDiff ℝ 1 h) (A A' : ℝ) (hA : ∀ x, |h x| ≤ A) (hA' : ∀ x, ‖fderiv ℝ h x‖ ≤ A') :
    ∫ x, (∑ k, u k * x k) * h x ∂(stdGaussian (EuclideanSpace ℝ (Fin (m + 1)))) =
      ∫ x, fderiv ℝ h x (WithLp.toLp 2 u) ∂(stdGaussian (EuclideanSpace ℝ (Fin (m + 1)))) := by
  refine b8a_ibp1 u hh (|A| + |A'|) (fun x => ?_) (fun x => ?_)
  · have h1 := hA x
    have h2 := le_abs_self A
    have h3 : 0 ≤ ‖x‖ := norm_nonneg _
    nlinarith [abs_nonneg A, abs_nonneg A', mul_nonneg (add_nonneg (abs_nonneg A) (abs_nonneg A')) h3]
  · have h1 := hA' x
    have h2 := le_abs_self A'
    have h3 : 0 ≤ ‖x‖ := norm_nonneg _
    nlinarith [abs_nonneg A, abs_nonneg A', mul_nonneg (add_nonneg (abs_nonneg A) (abs_nonneg A')) h3]

/-- uniform bounds for a `C_b^2` function -/
lemma b8a_bounds {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {ψ : F → ℝ}
    (hψ : MemCb 2 ψ) :
    ∃ B : ℝ, 0 ≤ B ∧ (∀ y, |ψ y| ≤ B) ∧ (∀ y, ‖fderiv ℝ ψ y‖ ≤ B) ∧
      (∀ y, ‖fderiv ℝ (fderiv ℝ ψ) y‖ ≤ B) := by
  obtain ⟨_, hb⟩ := hψ
  obtain ⟨B0, h0⟩ := hb 0 (by norm_num)
  obtain ⟨B1, h1⟩ := hb 1 (by norm_num)
  obtain ⟨B2, h2⟩ := hb 2 (by norm_num)
  have e0 : ∀ y, ‖ψ y‖ ≤ B0 := fun y => by
    have := h0 ⟨y, rfl⟩
    simpa [norm_iteratedFDeriv_zero] using this
  have e1 : ∀ y, ‖fderiv ℝ ψ y‖ ≤ B1 := fun y => by
    have := h1 ⟨y, rfl⟩
    simpa [← norm_iteratedFDeriv_fderiv (n := 0), norm_iteratedFDeriv_zero] using this
  have e2 : ∀ y, ‖fderiv ℝ (fderiv ℝ ψ) y‖ ≤ B2 := fun y => by
    have := h2 ⟨y, rfl⟩
    have h3 : ‖iteratedFDeriv ℝ 2 ψ y‖ = ‖fderiv ℝ (fderiv ℝ ψ) y‖ := by
      have := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := ψ) (x := y) (n := 1)
      rw [norm_iteratedFDeriv_one] at this
      exact this.symm
    simpa [h3] using this
  have hB0 : 0 ≤ B0 := (norm_nonneg (ψ 0)).trans (e0 0)
  have hB1 : 0 ≤ B1 := (norm_nonneg (fderiv ℝ ψ 0)).trans (e1 0)
  have hB2 : 0 ≤ B2 := (norm_nonneg (fderiv ℝ (fderiv ℝ ψ) 0)).trans (e2 0)
  refine ⟨B0 + B1 + B2, by positivity, fun y => ?_, fun y => ?_, fun y => ?_⟩
  · have := e0 y; rw [Real.norm_eq_abs] at this; linarith
  · linarith [e1 y]
  · linarith [e2 y]


/-- second-order (Hermite) Gaussian IBP for the standard Gaussian -/
lemma b8a_ibp2 (u v : Fin (m + 1) → ℝ) (T : EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin p))
    {ψ : EuclideanSpace ℝ (Fin p) → ℝ} (hψ : MemCb 2 ψ) :
    ∫ x, (∑ k, v k * x k) * ((∑ k, u k * x k) * ψ (T x))
        ∂(stdGaussian (EuclideanSpace ℝ (Fin (m + 1)))) =
      (∑ k, u k * v k) * ∫ x, ψ (T x) ∂(stdGaussian (EuclideanSpace ℝ (Fin (m + 1)))) +
      ∫ x, iteratedFDeriv ℝ 2 ψ (T x) ![T (WithLp.toLp 2 u), T (WithLp.toLp 2 v)]
        ∂(stdGaussian (EuclideanSpace ℝ (Fin (m + 1)))) := by
  set γ := stdGaussian (EuclideanSpace ℝ (Fin (m + 1))) with hγ
  obtain ⟨B, hB0, hB, hB1, hB2⟩ := b8a_bounds hψ
  have hψ1 : ContDiff ℝ 1 ψ := hψ.1.of_le (by norm_num)
  have hfd : ContDiff ℝ 1 (fderiv ℝ ψ) := hψ.1.fderiv_right (by norm_num)
  have hψd : Differentiable ℝ ψ := hψ.1.differentiable (by norm_num)
  have hfdd : Differentiable ℝ (fderiv ℝ ψ) := hfd.differentiable one_ne_zero
  set ℓ := b8a_ell u with hℓ
  -- the function `h = ℓ_u * ψ ∘ T`
  have hh : ContDiff ℝ 1 (fun x => ℓ x * ψ (T x)) :=
    ℓ.contDiff.mul (hψ1.comp T.contDiff)
  have hhd : ∀ x, HasFDerivAt (fun x => ℓ x * ψ (T x))
      (ℓ x • (fderiv ℝ ψ (T x)).comp T + ψ (T x) • ℓ) x := by
    intro x
    exact ℓ.hasFDerivAt.mul ((hψd (T x)).hasFDerivAt.comp x T.hasFDerivAt)
  have hhv : ∀ x, fderiv ℝ (fun x => ℓ x * ψ (T x)) x (WithLp.toLp 2 v) =
      ℓ x * fderiv ℝ ψ (T x) (T (WithLp.toLp 2 v)) + ψ (T x) * ∑ k, u k * v k := by
    intro x
    rw [(hhd x).fderiv]
    simp [hℓ, b8a_ell_apply]
  have hlx : ∀ x, |ℓ x| ≤ ‖ℓ‖ * ‖x‖ := fun x => by
    simpa [Real.norm_eq_abs] using ℓ.le_opNorm x
  have hTn : ∀ x, ‖T x‖ ≤ ‖T‖ * ‖x‖ := fun x => T.le_opNorm x
  have hℓ0 : 0 ≤ ‖ℓ‖ := norm_nonneg _
  have hT0 : 0 ≤ ‖T‖ := norm_nonneg _
  -- step 1
  have step1 := b8a_ibp1 v hh (‖ℓ‖ * B * (1 + ‖T‖)) (fun x => ?_) (fun x => ?_)
  rotate_left
  · have h1 : |ℓ x * ψ (T x)| ≤ ‖ℓ‖ * ‖x‖ * B := by
      rw [abs_mul]
      exact mul_le_mul (hlx x) (hB _) (abs_nonneg _) (by positivity)
    have h3 : 0 ≤ ‖x‖ := norm_nonneg _
    refine h1.trans ?_
    nlinarith [mul_nonneg (mul_nonneg hℓ0 hB0) (mul_nonneg hT0 h3), mul_nonneg hℓ0 hB0,
      mul_nonneg (mul_nonneg hℓ0 hB0) h3]
  · rw [(hhd x).fderiv]
    have h3 : 0 ≤ ‖x‖ := norm_nonneg _
    have h4 : ‖ℓ x • (fderiv ℝ ψ (T x)).comp T + ψ (T x) • ℓ‖ ≤
        ‖ℓ‖ * ‖x‖ * (B * ‖T‖) + B * ‖ℓ‖ := by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, Real.norm_eq_abs]
        refine mul_le_mul (hlx x) ?_ (norm_nonneg _) (by positivity)
        exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_right (hB1 _) hT0)
      · rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul (hB _) le_rfl hℓ0 hB0
    refine h4.trans ?_
    nlinarith [mul_nonneg (mul_nonneg hℓ0 hB0) (mul_nonneg hT0 h3), mul_nonneg hℓ0 hB0,
      mul_nonneg (mul_nonneg hℓ0 hB0) h3]
  have hℓx : ∀ x, ℓ x = ∑ k, u k * x k := b8a_ell_apply u
  simp_rw [hℓx] at step1
  -- step 2
  set w : EuclideanSpace ℝ (Fin p) := T (WithLp.toLp 2 v) with hw
  have hχ : ∀ y, HasFDerivAt (fun y => fderiv ℝ ψ y w) ((fderiv ℝ (fderiv ℝ ψ) y).flip w) y := by
    intro y
    simpa using (hfdd y).hasFDerivAt.clm_apply (hasFDerivAt_const w y)
  have hχT : ∀ x, HasFDerivAt (fun x => fderiv ℝ ψ (T x) w)
      (((fderiv ℝ (fderiv ℝ ψ) (T x)).flip w).comp T) x := fun x =>
    (hχ (T x)).comp x T.hasFDerivAt
  have hχcd : ContDiff ℝ 1 (fun x => fderiv ℝ ψ (T x) w) :=
    (hfd.comp T.contDiff).clm_apply contDiff_const
  have hw0 : 0 ≤ ‖w‖ := norm_nonneg _
  have step2 := b8a_ibp1_bdd u hχcd (B * ‖w‖) (B * ‖w‖ * ‖T‖) (fun x => ?_) (fun x => ?_)
  rotate_left
  · exact ((fderiv ℝ ψ (T x)).le_opNorm w).trans (mul_le_mul_of_nonneg_right (hB1 _) hw0)
  · rw [(hχT x).fderiv]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right ?_ hT0)
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun z => ?_
    simp only [ContinuousLinearMap.flip_apply]
    calc ‖(fderiv ℝ (fderiv ℝ ψ) (T x) z) w‖ ≤ ‖fderiv ℝ (fderiv ℝ ψ) (T x) z‖ * ‖w‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖fderiv ℝ (fderiv ℝ ψ) (T x)‖ * ‖z‖) * ‖w‖ :=
          mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) hw0
      _ ≤ (B * ‖z‖) * ‖w‖ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hB2 _) (norm_nonneg _)) hw0
      _ = B * ‖w‖ * ‖z‖ := by ring
  -- integrability
  have hcont1 : Continuous (fun x => ℓ x * fderiv ℝ ψ (T x) w) :=
    ℓ.continuous.mul (hχcd.continuous)
  have hint1 : Integrable (fun x => ℓ x * fderiv ℝ ψ (T x) w) γ := by
    refine q66_std_integrable_of_growth hcont1 (‖ℓ‖ * B * ‖w‖) fun x => ?_
    have h1 : |ℓ x * fderiv ℝ ψ (T x) w| ≤ ‖ℓ‖ * ‖x‖ * (B * ‖w‖) := by
      rw [abs_mul]
      refine mul_le_mul (hlx x) ?_ (abs_nonneg _) (by positivity)
      have := (fderiv ℝ ψ (T x)).le_opNorm w
      rw [← Real.norm_eq_abs]
      exact this.trans (mul_le_mul_of_nonneg_right (hB1 _) hw0)
    have h3 : 0 ≤ ‖x‖ := norm_nonneg _
    nlinarith [mul_nonneg (mul_nonneg hℓ0 hB0) (mul_nonneg hw0 h3), mul_nonneg hℓ0 hB0]
  have hint2 : Integrable (fun x => ψ (T x) * ∑ k, u k * v k) γ := by
    refine Integrable.of_bound (((hψ1.continuous.comp T.continuous).mul continuous_const)
      |>.aestronglyMeasurable) (B * |∑ k, u k * v k|) (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hB _) (abs_nonneg _)
  have hint3 : Integrable (fun x => ψ (T x)) γ :=
    Integrable.of_bound ((hψ1.continuous.comp T.continuous).aestronglyMeasurable) B
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hB _)
  -- assemble
  have e3 : ∀ x, fderiv ℝ (fun x => fderiv ℝ ψ (T x) w) x (WithLp.toLp 2 u) =
      iteratedFDeriv ℝ 2 ψ (T x) ![T (WithLp.toLp 2 u), T (WithLp.toLp 2 v)] := by
    intro x
    rw [(hχT x).fderiv, iteratedFDeriv_two_apply]
    simp [hw]
  simp_rw [e3] at step2
  simp_rw [hℓx] at hhv hint1 hint2
  have step1' : ∫ x, (∑ k, v k * x k) * ((∑ k, u k * x k) * ψ (T x)) ∂γ =
      ∫ x, ((∑ k, u k * x k) * fderiv ℝ ψ (T x) w + ψ (T x) * ∑ k, u k * v k) ∂γ := by
    rw [step1]
    exact integral_congr_ae (ae_of_all _ fun x => hhv x)
  rw [step1', integral_add hint1 hint2, step2, integral_mul_const]
  rw [hw]; ring


/-- the linear map with matrix `M` -/
def b8a_T {n p : ℕ} (M : Matrix (Fin p) (Fin n) ℝ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p) :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)

lemma b8a_T_apply {n p : ℕ} (M : Matrix (Fin p) (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) (b : Fin p) :
    b8a_T M x b = ∑ l, M b l * x l := by
  simp [b8a_T, Matrix.mulVec, dotProduct]


lemma b8a_integrable_quad {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Continuous f) (K : ℝ)
    (hfK : ∀ x, |f x| ≤ K * (1 + ‖x‖ ^ 2)) :
    Integrable f (stdGaussian (EuclideanSpace ℝ (Fin n))) := by
  have h2 : MemLp (id : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) 2
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := IsGaussian.memLp_two_id
  have i2 : Integrable (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2)
      (stdGaussian (EuclideanSpace ℝ (Fin n))) := h2.integrable_norm_pow (by norm_num)
  refine Integrable.mono' (((integrable_const (1 : ℝ)).add i2).const_mul |K|) hf.aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  exact (hfK x).trans (mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity))

lemma b8a_expand {p : ℕ} {ψ : EuclideanSpace ℝ (Fin p) → ℝ} (y a c : EuclideanSpace ℝ (Fin p)) :
    iteratedFDeriv ℝ 2 ψ y ![a, c] =
      ∑ b, ∑ e, a b * c e * iteratedFDeriv ℝ 2 ψ y ![stdVec b, stdVec e] := by
  have hv : ∀ z : EuclideanSpace ℝ (Fin p), z = ∑ b, z b • stdVec b := by
    intro z; ext k; simp [stdVec, Finset.sum_apply, Pi.single_apply]
  rw [iteratedFDeriv_two_apply]
  conv_lhs => rw [hv a, hv c]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one, map_sum,
    map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, Finset.mul_sum,
    smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun e _ => by ring


lemma b8a_iter_facts {p : ℕ} {ψ : EuclideanSpace ℝ (Fin p) → ℝ} (hψ : MemCb 2 ψ)
    (a c : EuclideanSpace ℝ (Fin p)) :
    Continuous (fun y => iteratedFDeriv ℝ 2 ψ y ![a, c]) ∧
      ∃ C : ℝ, ∀ y, |iteratedFDeriv ℝ 2 ψ y ![a, c]| ≤ C := by
  obtain ⟨B, hB0, hB, hB1, hB2⟩ := b8a_bounds hψ
  have hfd : ContDiff ℝ 1 (fderiv ℝ ψ) := hψ.1.fderiv_right (by norm_num)
  have e : (fun y => iteratedFDeriv ℝ 2 ψ y ![a, c]) =
      fun y => fderiv ℝ (fderiv ℝ ψ) y a c := by
    funext y; rw [iteratedFDeriv_two_apply]; rfl
  rw [e]
  refine ⟨((hfd.continuous_fderiv one_ne_zero).clm_apply continuous_const).clm_apply continuous_const,
    B * ‖a‖ * ‖c‖, fun y => ?_⟩
  rw [← Real.norm_eq_abs, iteratedFDeriv_two_apply]
  show ‖fderiv ℝ (fderiv ℝ ψ) y a c‖ ≤ _
  calc ‖fderiv ℝ (fderiv ℝ ψ) y a c‖ ≤ ‖fderiv ℝ (fderiv ℝ ψ) y a‖ * ‖c‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ (‖fderiv ℝ (fderiv ℝ ψ) y‖ * ‖a‖) * ‖c‖ :=
        mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
    _ ≤ B * ‖a‖ * ‖c‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hB2 _) (norm_nonneg _))
          (norm_nonneg _)


theorem sed_B8a_gauss_ibp2_proof {n p : ℕ} (Sg : Matrix (Fin n) (Fin n) ℝ) (hSg : Sg.PosSemidef)
    (coef : Fin p → Fin n → ℝ) (i j : Fin n) {ψ : EuclideanSpace ℝ (Fin p) → ℝ}
    (hψ : MemCb 2 ψ) :
    ∫ g : EuclideanSpace ℝ (Fin n), (g i * g j - Sg i j) *
        ψ (WithLp.toLp 2 fun b => ∑ k, coef b k * g k) ∂(multivariateGaussian 0 Sg) =
      ∑ b, ∑ c, (∑ k, coef b k * Sg k i) * (∑ l, coef c l * Sg l j) *
        ∫ g : EuclideanSpace ℝ (Fin n),
          iteratedFDeriv ℝ 2 ψ (WithLp.toLp 2 fun a => ∑ k, coef a k * g k) ![stdVec b, stdVec c]
          ∂(multivariateGaussian 0 Sg) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := i.pos; omega⟩
  set γ := stdGaussian (EuclideanSpace ℝ (Fin (m + 1))) with hγ
  set R := CFC.sqrt Sg with hR
  have hRR : R * R = Sg := CFC.sqrt_mul_sqrt_self Sg hSg.nonneg
  have hRh : R.IsHermitian := (CFC.sqrt_nonneg Sg).isSelfAdjoint
  have hsym : ∀ k l, R k l = R l k := fun k l => by simpa using hRh.apply l k
  have hSgR : ∀ k l, Sg k l = ∑ s, R k s * R l s := by
    intro k l
    rw [← hRR, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun s _ => by rw [hsym l s]
  have hψc : Continuous ψ := hψ.1.continuous
  have hRx : ∀ (x : EuclideanSpace ℝ (Fin (m + 1))) k,
      (0 + Matrix.toEuclideanCLM (𝕜 := ℝ) R x) k = ∑ l, R k l * x l := by
    intro x k
    have := Matrix.toEuclideanCLM_toLp (𝕜 := ℝ) R x.ofLp
    rw [WithLp.toLp_ofLp] at this
    simp [this, Matrix.mulVec, dotProduct]
  let Mmat : Matrix (Fin p) (Fin (m + 1)) ℝ := Matrix.of fun b l => ∑ k, coef b k * R k l
  let T := b8a_T Mmat
  have hT : ∀ x : EuclideanSpace ℝ (Fin (m + 1)),
      T x = WithLp.toLp 2 fun b => ∑ k, coef b k * (0 + Matrix.toEuclideanCLM (𝕜 := ℝ) R x) k := by
    intro x
    ext b
    simp only [T, b8a_T_apply, hRx, Mmat, Matrix.of_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  have hcontlin : Continuous (fun g : EuclideanSpace ℝ (Fin (m + 1)) =>
      (WithLp.toLp 2 fun b => ∑ k, coef b k * g k : EuclideanSpace ℝ (Fin p))) := by
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun b => ?_)
    exact continuous_finsetSum _ fun k _ => continuous_const.mul (PiLp.continuous_apply 2 _ k)
  have hmap : ∀ f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ, Continuous f →
      ∫ g, f g ∂(multivariateGaussian 0 Sg) =
        ∫ x, f (0 + Matrix.toEuclideanCLM (𝕜 := ℝ) R x) ∂γ := by
    intro f hf
    unfold multivariateGaussian
    exact integral_map (by fun_prop) hf.aestronglyMeasurable
  obtain ⟨B, hB0, hB, -, -⟩ := b8a_bounds hψ
  have hTc : Continuous (fun x : EuclideanSpace ℝ (Fin (m + 1)) => ψ (T x)) :=
    hψc.comp T.continuous
  -- coefficient identities
  have hTu : ∀ (r : Fin (m + 1)) (b : Fin p),
      T (WithLp.toLp 2 fun l => R r l) b = ∑ k, coef b k * Sg k r := by
    intro r b
    simp only [T, b8a_T_apply, Mmat, Matrix.of_apply, WithLp.ofLp_toLp]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hSgR k r, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  -- step L1
  have hfc : Continuous (fun g : EuclideanSpace ℝ (Fin (m + 1)) =>
      (g i * g j - Sg i j) * ψ (WithLp.toLp 2 fun b => ∑ k, coef b k * g k)) :=
    (((PiLp.continuous_apply 2 _ i).mul (PiLp.continuous_apply 2 _ j)).sub continuous_const).mul
      (hψc.comp hcontlin)
  have L1 : ∫ g : EuclideanSpace ℝ (Fin (m + 1)), (g i * g j - Sg i j) *
        ψ (WithLp.toLp 2 fun b => ∑ k, coef b k * g k) ∂(multivariateGaussian 0 Sg) =
      ∫ x, ((∑ l, R j l * x l) * ((∑ l, R i l * x l) * ψ (T x)) - Sg i j * ψ (T x)) ∂γ := by
    rw [hmap _ hfc]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only
    rw [← hT x, hRx x i, hRx x j]
    ring
  have hint_a : Integrable (fun x : EuclideanSpace ℝ (Fin (m + 1)) =>
      (∑ l, R j l * x l) * ((∑ l, R i l * x l) * ψ (T x))) γ := by
    have hc : Continuous (fun x : EuclideanSpace ℝ (Fin (m + 1)) =>
        (∑ l, R j l * x l) * ((∑ l, R i l * x l) * ψ (T x))) := by
      simp_rw [← b8a_ell_apply]
      exact (b8a_ell _).continuous.mul ((b8a_ell _).continuous.mul hTc)
    refine b8a_integrable_quad hc (‖b8a_ell fun l => R j l‖ * ‖b8a_ell fun l => R i l‖ * B)
      fun x => ?_
    simp_rw [← b8a_ell_apply]
    have h1 := (b8a_ell fun l => R j l).le_opNorm x
    have h2 := (b8a_ell fun l => R i l).le_opNorm x
    rw [Real.norm_eq_abs] at h1 h2
    rw [abs_mul, abs_mul]
    have h3 := hB (T x)
    have e1 := norm_nonneg (b8a_ell fun l => R j l)
    have e2 := norm_nonneg (b8a_ell fun l => R i l)
    have e3 := norm_nonneg x
    calc |(b8a_ell fun l => R j l) x| * (|(b8a_ell fun l => R i l) x| * |ψ (T x)|)
        ≤ (‖b8a_ell fun l => R j l‖ * ‖x‖) * ((‖b8a_ell fun l => R i l‖ * ‖x‖) * B) :=
          mul_le_mul h1 (mul_le_mul h2 h3 (abs_nonneg _) (by positivity)) (by positivity)
            (by positivity)
      _ = (‖b8a_ell fun l => R j l‖ * ‖b8a_ell fun l => R i l‖ * B) * ‖x‖ ^ 2 := by ring
      _ ≤ (‖b8a_ell fun l => R j l‖ * ‖b8a_ell fun l => R i l‖ * B) * (1 + ‖x‖ ^ 2) := by
          refine mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hint_b : Integrable (fun x : EuclideanSpace ℝ (Fin (m + 1)) => Sg i j * ψ (T x)) γ :=
    (Integrable.of_bound hTc.aestronglyMeasurable B
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hB _)).const_mul _
  have key : ∫ g : EuclideanSpace ℝ (Fin (m + 1)), (g i * g j - Sg i j) *
        ψ (WithLp.toLp 2 fun b => ∑ k, coef b k * g k) ∂(multivariateGaussian 0 Sg) =
      ∫ x, iteratedFDeriv ℝ 2 ψ (T x) ![T (WithLp.toLp 2 fun l => R i l),
        T (WithLp.toLp 2 fun l => R j l)] ∂γ := by
    rw [L1, integral_sub hint_a hint_b, integral_const_mul,
      b8a_ibp2 (fun l => R i l) (fun l => R j l) T hψ, ← hSgR i j]
    ring
  -- expansion
  have hbc : ∀ b c : Fin p, Continuous (fun x : EuclideanSpace ℝ (Fin (m + 1)) =>
      iteratedFDeriv ℝ 2 ψ (T x) ![stdVec b, stdVec c]) := fun b c =>
    (b8a_iter_facts hψ (stdVec b) (stdVec c)).1.comp T.continuous
  have hbcI : ∀ b c : Fin p, Integrable (fun x : EuclideanSpace ℝ (Fin (m + 1)) =>
      iteratedFDeriv ℝ 2 ψ (T x) ![stdVec b, stdVec c]) γ := by
    intro b c
    obtain ⟨C, hC⟩ := (b8a_iter_facts hψ (stdVec b) (stdVec c)).2
    exact Integrable.of_bound (hbc b c).aestronglyMeasurable C
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hC _)
  have expand : ∫ x, iteratedFDeriv ℝ 2 ψ (T x) ![T (WithLp.toLp 2 fun l => R i l),
        T (WithLp.toLp 2 fun l => R j l)] ∂γ =
      ∑ b, ∑ c, (T (WithLp.toLp 2 fun l => R i l) b * T (WithLp.toLp 2 fun l => R j l) c) *
        ∫ x, iteratedFDeriv ℝ 2 ψ (T x) ![stdVec b, stdVec c] ∂γ := by
    rw [integral_congr_ae (ae_of_all _ fun x => b8a_expand (ψ := ψ) (T x) _ _)]
    rw [integral_finsetSum _ (fun b _ => integrable_finset_sum _ fun c _ =>
      (hbcI b c).const_mul _)]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_finsetSum _ (fun c _ => (hbcI b c).const_mul _)]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [integral_const_mul]
  have rhs : ∀ b c : Fin p, ∫ g : EuclideanSpace ℝ (Fin (m + 1)),
      iteratedFDeriv ℝ 2 ψ (WithLp.toLp 2 fun a => ∑ k, coef a k * g k) ![stdVec b, stdVec c]
        ∂(multivariateGaussian 0 Sg) =
      ∫ x, iteratedFDeriv ℝ 2 ψ (T x) ![stdVec b, stdVec c] ∂γ := by
    intro b c
    have hcf : Continuous (fun g : EuclideanSpace ℝ (Fin (m + 1)) =>
        iteratedFDeriv ℝ 2 ψ (WithLp.toLp 2 fun a => ∑ k, coef a k * g k) ![stdVec b, stdVec c]) :=
      (b8a_iter_facts hψ (stdVec b) (stdVec c)).1.comp hcontlin
    rw [hmap _ hcf]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only
    rw [← hT x]
  rw [key, expand]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  rw [rhs, hTu i b, hTu j c]


end HRS.MC.SEdge.B8a
