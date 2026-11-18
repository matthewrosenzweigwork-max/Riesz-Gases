import Mathlib
import HRS.MS.SuppU5Aux6
import HRS.MP.RdPropKernel

/-!
# Packet U5 (aux 7): the feature map of the transported initial field
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace Matrix

noncomputable section

namespace HRS.U5

open HRS HRS.Whole HRS.MP.RdProp HRS.MP.HNegInfra

variable {d : ℕ}

/-! ### Bounds from the `C_b^1` norm -/

lemma u5_cb_sup {f : Euc d → ℝ} (hf : MemCb 1 f) (x : Euc d) : |f x| ≤ cbNorm 1 f := by
  have h0 : BddAbove (Set.range fun z => ‖iteratedFDeriv ℝ 0 f z‖) := hf.2 0 (by norm_num)
  have h1 : ‖f x‖ ≤ ⨆ z, ‖iteratedFDeriv ℝ 0 f z‖ := by
    have := le_ciSup h0 x
    simpa using this
  unfold cbNorm
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have : 0 ≤ ⨆ z, ‖iteratedFDeriv ℝ 1 f z‖ := Real.iSup_nonneg fun _ => norm_nonneg _
  rw [← Real.norm_eq_abs]
  linarith

lemma u5_cb_fderiv {f : Euc d → ℝ} (hf : MemCb 1 f) (x : Euc d) : ‖fderiv ℝ f x‖ ≤ cbNorm 1 f := by
  have h1 : BddAbove (Set.range fun z => ‖iteratedFDeriv ℝ 1 f z‖) := hf.2 1 le_rfl
  have h : ‖fderiv ℝ f x‖ ≤ ⨆ z, ‖iteratedFDeriv ℝ 1 f z‖ := by
    have := le_ciSup h1 x
    simpa using this
  unfold cbNorm
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  have : 0 ≤ ⨆ z, ‖iteratedFDeriv ℝ 0 f z‖ := Real.iSup_nonneg fun _ => norm_nonneg _
  linarith

lemma u5_cb_lip {f : Euc d → ℝ} (hf : MemCb 1 f) (x y : Euc d) :
    |f x - f y| ≤ cbNorm 1 f * ‖x - y‖ := by
  have hd : Differentiable ℝ f := hf.1.differentiable (by norm_num)
  have := (convex_univ : Convex ℝ (Set.univ : Set (Euc d))).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => hd z) (fun z _ => u5_cb_fderiv hf z) (Set.mem_univ y) (Set.mem_univ x)
  rw [← Real.norm_eq_abs]
  simpa [norm_sub_rev] using this

lemma u5_cb_nonneg (f : Euc d → ℝ) : 0 ≤ cbNorm 1 f :=
  Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _

lemma u5_cb_integrable {f : Euc d → ℝ} (hf : MemCb 1 f) (μ : Measure (Euc d))
    [IsProbabilityMeasure μ] : Integrable f μ :=
  Integrable.of_bound hf.1.continuous.measurable.aestronglyMeasurable (cbNorm 1 f)
    (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using u5_cb_sup hf x)

lemma u5_pair_abs_le {f : Euc d → ℝ} (hf : MemCb 1 f) (μ : Measure (Euc d)) [IsProbabilityMeasure μ] :
    |HRS.Whole.pair μ f| ≤ cbNorm 1 f := by
  unfold HRS.Whole.pair
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := f) (C := cbNorm 1 f)
    (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using u5_cb_sup hf x)
  simpa [Real.norm_eq_abs] using this

/-- The Riesz representative feature map `J(x) ∈ H^{-Γ}` of `B:eq:iid-feature-map`. -/
lemma u5_feature (Γ : ℝ) (K A : ℝ) (hA : 0 ≤ A) (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    (ψ : (Euc d → ℝ) → (Euc d → ℝ))
    (hψ : ∀ φ, IsSobolevTest Γ φ → MemCb 1 (ψ φ) ∧ cbNorm 1 (ψ φ) ≤ K * HRS.Whole.sobolevNorm Γ φ)
    (hlin : ∀ (φ₁ φ₂ : Euc d → ℝ) (c : ℝ), IsSobolevTest Γ φ₁ → IsSobolevTest Γ φ₂ → ψ (φ₁ + c • φ₂) = ψ φ₁ + c • ψ φ₂) :
    ∃ J : Euc d → HNeg d Γ,
      (∀ x φ, IsSobolevTest Γ φ → HNeg.pairing φ (J x) = A * (ψ φ x - HRS.Whole.pair μ (ψ φ))) ∧
      (∀ x, ‖J x‖ ≤ 2 * A * max K 0) ∧
      (∀ x y, ‖J x - J y‖ ≤ A * max K 0 * ‖x - y‖) := by
  have hsn : ∀ φ : Euc d → ℝ, 0 ≤ HRS.Whole.sobolevNorm Γ φ := fun φ => Real.sqrt_nonneg _
  have hKK : ∀ φ, IsSobolevTest Γ φ → cbNorm 1 (ψ φ) ≤ max K 0 * HRS.Whole.sobolevNorm Γ φ := fun φ hφ =>
    (hψ φ hφ).2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hsn φ))
  have hex : ∀ x : Euc d, ∃ k : HNeg d Γ, ∀ φ, IsSobolevTest Γ φ →
      HNeg.pairing φ k = A * (ψ φ x - HRS.Whole.pair μ (ψ φ)) := fun x => by
    refine rpk_exists_rep (fun φ => A * (ψ φ x - HRS.Whole.pair μ (ψ φ))) (2 * A * max K 0) ?_ ?_
    · intro φ φ' c hφ hφ'
      have h := hlin φ' φ c hφ' hφ
      rw [add_comm] at h
      show A * (ψ (c • φ + φ') x - HRS.Whole.pair μ (ψ (c • φ + φ'))) =
        c * (A * (ψ φ x - HRS.Whole.pair μ (ψ φ))) + A * (ψ φ' x - HRS.Whole.pair μ (ψ φ'))
      rw [h]
      have i1 := u5_cb_integrable (hψ φ hφ).1 μ
      have i2 := u5_cb_integrable (hψ φ' hφ').1 μ
      have : HRS.Whole.pair μ (ψ φ' + c • ψ φ) = c * HRS.Whole.pair μ (ψ φ) + HRS.Whole.pair μ (ψ φ') := by
        unfold HRS.Whole.pair
        have e : (fun x => (ψ φ' + c • ψ φ) x) = fun x => ψ φ' x + c * ψ φ x := by ext; simp
        rw [e, integral_add i2 (i1.const_mul c), integral_const_mul]; ring
      rw [this]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · intro φ hφ
      have h1 := u5_cb_sup (hψ φ hφ).1 x
      have h2 := u5_pair_abs_le (hψ φ hφ).1 μ
      have h3 := hKK φ hφ
      rw [abs_mul, abs_of_nonneg hA]
      calc A * |ψ φ x - HRS.Whole.pair μ (ψ φ)| ≤ A * (2 * (max K 0 * HRS.Whole.sobolevNorm Γ φ)) := by
            refine mul_le_mul_of_nonneg_left ?_ hA
            calc |ψ φ x - HRS.Whole.pair μ (ψ φ)| ≤ |ψ φ x| + |HRS.Whole.pair μ (ψ φ)| := abs_sub _ _
              _ ≤ 2 * (max K 0 * HRS.Whole.sobolevNorm Γ φ) := by linarith
        _ = 2 * A * max K 0 * HRS.Whole.sobolevNorm Γ φ := by ring
  choose J hJ using hex
  refine ⟨J, hJ, fun x => ?_, fun x y => ?_⟩
  · refine hneg_norm_le_of_pairing _ _ (by positivity) fun φ hφ => ?_
    rw [hJ x φ hφ]
    have h1 := u5_cb_sup (hψ φ hφ).1 x
    have h2 := u5_pair_abs_le (hψ φ hφ).1 μ
    have h3 := hKK φ hφ
    rw [abs_mul, abs_of_nonneg hA]
    calc A * |ψ φ x - HRS.Whole.pair μ (ψ φ)| ≤ A * (2 * (max K 0 * HRS.Whole.sobolevNorm Γ φ)) := by
          refine mul_le_mul_of_nonneg_left ?_ hA
          calc |ψ φ x - HRS.Whole.pair μ (ψ φ)| ≤ |ψ φ x| + |HRS.Whole.pair μ (ψ φ)| := abs_sub _ _
            _ ≤ 2 * (max K 0 * HRS.Whole.sobolevNorm Γ φ) := by linarith
      _ = 2 * A * max K 0 * HRS.Whole.sobolevNorm Γ φ := by ring
  · refine hneg_norm_le_of_pairing _ _ (by positivity) fun φ hφ => ?_
    rw [mhn_pairing_sub hφ, hJ x φ hφ, hJ y φ hφ]
    have h1 := u5_cb_lip (hψ φ hφ).1 x y
    have h3 := hKK φ hφ
    have : A * (ψ φ x - HRS.Whole.pair μ (ψ φ)) - A * (ψ φ y - HRS.Whole.pair μ (ψ φ)) =
        A * (ψ φ x - ψ φ y) := by ring
    rw [this, abs_mul, abs_of_nonneg hA]
    calc A * |ψ φ x - ψ φ y| ≤ A * (cbNorm 1 (ψ φ) * ‖x - y‖) := mul_le_mul_of_nonneg_left h1 hA
      _ ≤ A * (max K 0 * HRS.Whole.sobolevNorm Γ φ * ‖x - y‖) := by
          gcongr
      _ = A * max K 0 * ‖x - y‖ * HRS.Whole.sobolevNorm Γ φ := by ring

/-! ### The Gaussian bridge: coordinates -/

lemma u5_prod_integrable {f g : Euc d → ℝ} (hf : MemCb 1 f) (hg : MemCb 1 g) (μ : Measure (Euc d))
    [IsProbabilityMeasure μ] : Integrable (fun x => f x * g x) μ :=
  Integrable.of_bound (hf.1.continuous.mul hg.1.continuous).measurable.aestronglyMeasurable
    (cbNorm 1 f * cbNorm 1 g) (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (u5_cb_sup hf x) (u5_cb_sup hg x) (abs_nonneg _) (u5_cb_nonneg f))

lemma u5_cov_eq {f g : Euc d → ℝ} (hf : MemCb 1 f) (hg : MemCb 1 g) (μ : Measure (Euc d))
    [IsProbabilityMeasure μ] :
    ∫ x, (f x - HRS.Whole.pair μ f) * (g x - HRS.Whole.pair μ g) ∂μ = iidCovW μ f g := by
  have hfL : MemLp f 2 μ := MemLp.of_bound hf.1.continuous.measurable.aestronglyMeasurable (cbNorm 1 f)
    (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using u5_cb_sup hf x)
  have hgL : MemLp g 2 μ := MemLp.of_bound hg.1.continuous.measurable.aestronglyMeasurable (cbNorm 1 g)
    (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using u5_cb_sup hg x)
  have := covariance_eq_sub hfL hgL
  unfold iidCovW HRS.Whole.pair
  exact this

/-- Positive semidefiniteness of the Gaussian-bridge covariance matrix. -/
lemma u5_cov_psd {q : ℕ} (ψ : Fin q → Euc d → ℝ) (hψ : ∀ j, MemCb 1 (ψ j)) (μ : Measure (Euc d))
    [IsProbabilityMeasure μ] :
    (Matrix.of fun a b => iidCovW μ (ψ a) (ψ b)).PosSemidef := by
  set F : Euc d → Ek q := fun x => WithLp.toLp 2 fun j => ψ j x - HRS.Whole.pair μ (ψ j) with hF
  have hFm : Measurable F := by
    refine (MeasurableEquiv.toLp 2 (Fin q → ℝ)).measurable.comp (measurable_pi_iff.2 fun j => ?_)
    exact ((hψ j).1.continuous.measurable).sub measurable_const
  have hcoord : ∀ j, Integrable (fun x => (ψ j x - HRS.Whole.pair μ (ψ j)) ^ 2) μ := fun j =>
    Integrable.of_bound ((((hψ j).1.continuous.measurable).sub measurable_const).pow_const 2).aestronglyMeasurable
      ((cbNorm 1 (ψ j) + cbNorm 1 (ψ j)) ^ 2) (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_pow]
        refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
        exact (abs_sub _ _).trans (add_le_add (u5_cb_sup (hψ j) x) (u5_pair_abs_le (hψ j) μ)))
  have h2 : Integrable (fun y : Ek q => ‖y‖ ^ 2) (μ.map F) := by
    rw [integrable_map_measure (measurable_norm.pow_const 2).aestronglyMeasurable hFm.aemeasurable]
    have : (fun x => ‖F x‖ ^ 2) = fun x => ∑ j, (ψ j x - HRS.Whole.pair μ (ψ j)) ^ 2 := by
      ext x
      simp [hF, EuclideanSpace.real_norm_sq_eq]
    show Integrable (fun x => ‖F x‖ ^ 2) μ
    rw [this]
    exact integrable_finsetSum _ fun j _ => hcoord j
  have e : (Matrix.of fun a b => iidCovW μ (ψ a) (ψ b)) = Yurinskii.momentMatrix (μ.map F) := by
    ext a b
    simp only [Matrix.of_apply, Yurinskii.momentMatrix]
    rw [integral_map hFm.aemeasurable (by fun_prop : Measurable fun y : Ek q => y a * y b).aestronglyMeasurable]
    exact (u5_cov_eq (hψ a) (hψ b) μ).symm
  rw [e]
  exact Yurinskii.momentMatrix_posSemidef _ h2

/-- The linear map `y ↦ M y` on Euclidean spaces. -/
def u5_lin {k q : ℕ} (M : Matrix (Fin k) (Fin q) ℝ) : Ek q →L[ℝ] Ek k :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => WithLp.toLp 2 (fun c => ∑ j, M c j * y j)
      map_add' := fun x y => by ext c; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun r x => by ext c; simp [Finset.mul_sum, mul_left_comm] }

lemma u5_lin_apply {k q : ℕ} (M : Matrix (Fin k) (Fin q) ℝ) (y : Ek q) (c : Fin k) :
    (u5_lin M y) c = ∑ j, M c j * y j := rfl

lemma u5_lin_adjoint {k q : ℕ} (M : Matrix (Fin k) (Fin q) ℝ) (u : Ek k) :
    ((u5_lin M).adjoint u).ofLp = Mᵀ *ᵥ u.ofLp := by
  ext j
  have h := ContinuousLinearMap.adjoint_inner_right (u5_lin M) (EuclideanSpace.single j (1 : ℝ)) u
  rw [EuclideanSpace.inner_single_left] at h
  rw [Matrix.mulVec, dotProduct]
  simp only [conj_trivial, one_mul] at h
  rw [h]
  simp [u5_lin_apply, PiLp.inner_apply, EuclideanSpace.single_apply, Matrix.transpose_apply, mul_comm]

lemma u5_bridge_vec {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (μ : Measure (Euc d)) [IsProbabilityMeasure μ] (η : Ω' → (Euc d → ℝ) → ℝ)
    (hη : ∀ (p : ℕ) (ψ : Fin p → Euc d → ℝ), (∀ a, MemCb 1 (ψ a)) →
      P'.map (fun ζ => (WithLp.toLp 2 fun a => η ζ (ψ a) : Ek p)) =
        multivariateGaussian 0 (Matrix.of fun a b => iidCovW μ (ψ a) (ψ b)))
    (hηm : ∀ ψ : Euc d → ℝ, MemCb 1 ψ → Measurable fun ζ => η ζ ψ)
    {q k : ℕ} (ψ : Fin q → Euc d → ℝ) (hψ : ∀ j, MemCb 1 (ψ j)) (M : Matrix (Fin k) (Fin q) ℝ) :
    P'.map (fun ζ => (WithLp.toLp 2 fun c : Fin k => ∑ j, M c j * η ζ (ψ j) : Ek k)) =
      multivariateGaussian 0 (M * Matrix.of (fun a b => iidCovW μ (ψ a) (ψ b)) * Mᵀ) := by
  have hGm : Measurable (fun ζ => (WithLp.toLp 2 fun a => η ζ (ψ a) : Ek q)) :=
    (MeasurableEquiv.toLp 2 (Fin q → ℝ)).measurable.comp
      (measurable_pi_iff.2 fun j => hηm _ (hψ j))
  have e : (fun ζ => (WithLp.toLp 2 fun c : Fin k => ∑ j, M c j * η ζ (ψ j) : Ek k)) =
      (u5_lin M) ∘ (fun ζ => (WithLp.toLp 2 fun a => η ζ (ψ a) : Ek q)) := by
    ext ζ c; rfl
  rw [e, ← Measure.map_map (u5_lin M).continuous.measurable hGm, hη q ψ hψ]
  have hpsd := u5_cov_psd ψ hψ μ
  refine u5_gauss_map (hpsd.mul_mul_conjTranspose_same M) (u5_lin M) (fun u v => ?_) hpsd
  rw [u5_lin_adjoint, u5_lin_adjoint, Matrix.mul_assoc, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec]
  conv_rhs => rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  simp [Matrix.conjTranspose_eq_transpose_of_trivial]

/-! ### The empirical field and the coordinates of the Gaussian field -/

lemma u5_pair_empirical {N : ℕ} (X : EucConfig d N) {f : Euc d → ℝ} (hf : Continuous f) :
    HRS.Whole.pair (HRS.Whole.empirical X) f = (N : ℝ)⁻¹ * ∑ i, f (X i) := by
  unfold HRS.Whole.pair HRS.Whole.empirical
  rw [integral_smul_measure, integral_finset_sum_measure]
  · simp [integral_dirac' _ _ hf.measurable.stronglyMeasurable]
  · intro i _
    exact integrable_dirac enorm_lt_top

/-- The pairing of a test with `S₀(X) = N^{-1/2} ∑ J(x_i)` is the transported empirical fluctuation. -/
lemma u5_pairing_sum {Γ : ℝ} {N : ℕ} (hN : 1 ≤ N) (A : ℝ) (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    (ψ : (Euc d → ℝ) → (Euc d → ℝ)) (J : Euc d → HNeg d Γ)
    (hψc : ∀ φ, IsSobolevTest Γ φ → MemCb 1 (ψ φ))
    (hJ : ∀ x φ, IsSobolevTest Γ φ → HNeg.pairing φ (J x) = A * (ψ φ x - HRS.Whole.pair μ (ψ φ)))
    (X : EucConfig d N) (φ : Euc d → ℝ) (hφ : IsSobolevTest Γ φ) :
    HNeg.pairing φ ((Real.sqrt N)⁻¹ • ∑ i, J (X i)) =
      A * Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical X) (ψ φ) - HRS.Whole.pair μ (ψ φ)) := by
  have hinner : ∀ F : HNeg d Γ, HNeg.pairing φ F = inner ℝ (rpk_J Γ ⟨φ, hφ⟩) F := fun F =>
    (rpk_J_inner (⟨φ, hφ⟩ : rpk_Tst d Γ) F).symm
  rw [hinner, inner_smul_right, inner_sum]
  simp_rw [← hinner, hJ _ φ hφ]
  rw [u5_pair_empirical X (hψc φ hφ).1.continuous]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hNpos.le
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.2 hNpos
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  rw [Real.sq_sqrt hNpos.le]; ring

/-- Two measurable `H^{-Γ}`-valued maps with the same pairings against every test a.e. agree a.e. -/
lemma u5_ae_eq_of_pairing {Γ : ℝ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F G : Ω → HNeg d Γ)
    (h : ∀ φ : Euc d → ℝ, IsSobolevTest Γ φ → ∀ᵐ ζ ∂P, HNeg.pairing φ (F ζ) = HNeg.pairing φ (G ζ)) :
    F =ᵐ[P] G := by
  obtain ⟨φ, hφ, -, hnorm⟩ := hneg_norming d Γ
  have h' : ∀ᵐ ζ ∂P, ∀ n, HNeg.pairing (φ n) (F ζ) = HNeg.pairing (φ n) (G ζ) :=
    ae_all_iff.2 fun n => h _ (hφ n)
  filter_upwards [h'] with ζ hζ
  have : ‖F ζ - G ζ‖ = 0 := by
    rw [hnorm]
    have : ∀ n, |HNeg.pairing (φ n) (F ζ - G ζ)| = 0 := fun n => by
      rw [mhn_pairing_sub (hφ n), hζ n, sub_self]; simp
    simp [this]
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

/-- The law of the coordinates of the Gaussian field along tests. -/
lemma u5_coords_law {Γ : ℝ} (K A : ℝ) (hA : 0 ≤ A) (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    (ψ : (Euc d → ℝ) → (Euc d → ℝ))
    (hψc : ∀ φ, IsSobolevTest Γ φ → MemCb 1 (ψ φ))
    (J : Euc d → HNeg d Γ)
    (hJ : ∀ x φ, IsSobolevTest Γ φ → HNeg.pairing φ (J x) = A * (ψ φ x - HRS.Whole.pair μ (ψ φ)))
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (η : Ω' → (Euc d → ℝ) → ℝ)
    (hηm : ∀ ψ : Euc d → ℝ, MemCb 1 ψ → Measurable fun ζ => η ζ ψ)
    (hη : ∀ (p : ℕ) (ψ : Fin p → Euc d → ℝ), (∀ a, MemCb 1 (ψ a)) →
      P'.map (fun ζ => (WithLp.toLp 2 fun a => η ζ (ψ a) : Ek p)) =
        multivariateGaussian 0 (Matrix.of fun a b => iidCovW μ (ψ a) (ψ b)))
    (I : Ω' → HNeg d Γ) (hI : ∀ φ, IsSobolevTest Γ φ → ∀ᵐ ζ ∂P', HNeg.pairing φ (I ζ) = A * η ζ (ψ φ))
    (L : ℕ) (w : Fin L → HNeg d Γ) (hw : ∀ a, w a ∈ LinearMap.range (rpk_J Γ)) :
    P'.map (fun ζ => (WithLp.toLp 2 fun a : Fin L => inner ℝ (w a) (I ζ) : Ek L)) =
      multivariateGaussian 0 (Matrix.of fun a b => ∫ x, inner ℝ (w a) (J x) * inner ℝ (w b) (J x) ∂μ) := by
  choose φ hφ using fun a => LinearMap.mem_range.1 (hw a)
  have hφt : ∀ a, IsSobolevTest Γ (φ a).1 := fun a => (φ a).2
  have hin : ∀ (a : Fin L) (F : HNeg d Γ), inner ℝ (w a) F = HNeg.pairing (φ a).1 F := fun a F => by
    rw [← hφ a]; exact rpk_J_inner (φ a) F
  set ψa : Fin L → Euc d → ℝ := fun a => ψ (φ a).1 with hψa
  have hψm : ∀ a, MemCb 1 (ψa a) := fun a => hψc _ (hφt a)
  -- replace the coordinates by `A η(ψ_a)` a.e.
  have hae : ∀ᵐ ζ ∂P', ∀ a : Fin L, inner ℝ (w a) (I ζ) = A * η ζ (ψa a) := by
    rw [ae_all_iff]
    intro a
    filter_upwards [hI _ (hφt a)] with ζ hζ
    rw [hin]; exact hζ
  have hmeasY : AEMeasurable (fun ζ => (WithLp.toLp 2 fun a : Fin L => A * η ζ (ψa a) : Ek L)) P' :=
    ((MeasurableEquiv.toLp 2 (Fin L → ℝ)).measurable.comp (measurable_pi_iff.2 fun a =>
      (hηm _ (hψm a)).const_mul A)).aemeasurable
  rw [Measure.map_congr (g := fun ζ => (WithLp.toLp 2 fun a : Fin L => ∑ j, ((A • (1 : Matrix (Fin L) (Fin L) ℝ)) a j) * η ζ (ψa j) : Ek L))
    (by
      filter_upwards [hae] with ζ hζ
      ext a
      simp [Matrix.smul_apply, Matrix.one_apply, hζ a])]
  rw [u5_bridge_vec P' μ η hη hηm ψa hψm (A • 1)]
  congr 1
  have hmat : ((A • (1 : Matrix (Fin L) (Fin L) ℝ)) * Matrix.of (fun a b => iidCovW μ (ψa a) (ψa b)) *
      (A • (1 : Matrix (Fin L) (Fin L) ℝ))ᵀ) =
      (A ^ 2) • Matrix.of (fun a b => iidCovW μ (ψa a) (ψa b)) := by
    simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.transpose_smul, Matrix.transpose_one,
      Matrix.mul_smul, Matrix.mul_one, smul_smul]
    rw [sq]
  rw [hmat]
  ext a b
  simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, hin, hJ _ _ (hφt _)]
  have : ∀ x, (A * (ψ (φ a).1 x - HRS.Whole.pair μ (ψ (φ a).1))) *
      (A * (ψ (φ b).1 x - HRS.Whole.pair μ (ψ (φ b).1))) =
      A ^ 2 * ((ψ (φ a).1 x - HRS.Whole.pair μ (ψ (φ a).1)) *
        (ψ (φ b).1 x - HRS.Whole.pair μ (ψ (φ b).1))) := fun x => by ring
  simp_rw [this]
  rw [integral_const_mul]
  exact congrArg (A ^ 2 * ·) (u5_cov_eq (hψm a) (hψm b) μ).symm ▸ rfl

end HRS.U5
