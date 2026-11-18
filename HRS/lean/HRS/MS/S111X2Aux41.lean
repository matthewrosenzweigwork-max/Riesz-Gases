import HRS.MS.S111X2Aux38
import HRS.MS.S111X2Aux25

/-!
# S11.1 X2, packet H02 (part 3): positivity of the `2 × 2` covariance matrices of the Gaussian evolution

The covariance matrix of two observations of `IsLinearGaussianEvolutionW`,
`S_{ab} = C₀(U_{t_a}φ_a, U_{t_b}φ_b) + noiseCov(t_a,t_b;φ_a,φ_b)`, is positive semidefinite: the initial part is a Gram form
of the positive resolvent (E01) and the noise part is a Gram form of the gradients of the classical solutions (E03).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111X2

open HRS (Euc)
open HRS.Whole HRS.Whole.Q34
open HRS.MS.TcR (tc2_integral_nu)

variable {d : ℕ}

/-- The noise covariance in terms of classical solutions. -/
theorem s111x2_noise_eq (hd : 2 ≤ d) {s a β : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (ha : 0 < a) (hβ : 0 < β)
    {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ) {t₁ t₂ : ℝ} (h1 : 0 ≤ t₁) (h2 : 0 ≤ t₂)
    {φ ψ : Euc d → ℝ} {f g : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) t₁ φ f)
    (hg : IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) t₂ ψ g) :
    noiseCovW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) β⁻¹ t₁ t₂ φ ψ = 2 * β⁻¹ *
      ∫ r in Icc 0 (min t₁ t₂), s111x2_dirichlet (HRS.Whole.withDensityReal ρ) (f r) (g r) := by
  obtain ⟨M, T⟩ := s111x2_td_of_thermal hd hs0 hs ha hβ hρ
  set C := (quadraticGradientDyn d s a β).coeff (fun _ => ρ) with hC
  unfold noiseCovW
  congr 1
  refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
  have p1 : propagatorW C r t₁ φ = f r :=
    s111x2_prop_eq hd hs0 hs ha hβ hρ h1 hf ⟨hr.1, hr.2.trans (min_le_left _ _)⟩
  have p2 : propagatorW C r t₂ ψ = g r :=
    s111x2_prop_eq hd hs0 hs ha hβ hρ h2 hg ⟨hr.1, hr.2.trans (min_le_right _ _)⟩
  beta_reduce
  rw [p1, p2]
  unfold s111x2_dirichlet
  rw [tc2_integral_nu T.prob]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  beta_reduce
  rw [mul_comm]
  rfl

theorem s111x2_noise_symm {C : WholeCoeff d} (q t t' : ℝ) (φ ψ : Euc d → ℝ) :
    noiseCovW C q t t' φ ψ = noiseCovW C q t' t ψ φ := by
  unfold noiseCovW
  rw [min_comm t t']
  congr 1
  refine setIntegral_congr_fun (measurableSet_Icc : MeasurableSet (Icc (0 : ℝ) (min t' t))) fun r _ => ?_
  beta_reduce
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  beta_reduce
  rw [real_inner_comm]

/-- Positivity of the Gram form of the response. -/
theorem s111x2_gram_psd {g : Euc d → ℝ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]
    {K : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ} {Mg : ℝ} (hK : KRep g μ K Mg) {θ : ℝ} (hθ : 0 ≤ θ)
    {u v : Euc d → ℝ} (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) (x₀ x₁ : ℝ) :
    0 ≤ x₀ * x₀ * HRS.Whole.susceptibilityCov g μ θ u u + x₀ * x₁ * HRS.Whole.susceptibilityCov g μ θ u v +
      x₁ * x₀ * HRS.Whole.susceptibilityCov g μ θ v u + x₁ * x₁ * HRS.Whole.susceptibilityCov g μ θ v v := by
  rw [s111x2_susc_eq hK hθ hu hu, s111x2_susc_eq hK hθ hu hv, s111x2_susc_eq hK hθ hv hu,
    s111x2_susc_eq hK hθ hv hv]
  set R := s111x2_Res hK.posOp hθ with hR
  set cu := s111x2_cl hu
  set cv := s111x2_cl hv
  have hRl : R (x₀ • cu + x₁ • cv) = x₀ • R cu + x₁ • R cv := by
    rw [hR, s111x2_Res_add, s111x2_Res_smul, s111x2_Res_smul]
  have hb := (s111x2_Res_bounds hK.posOp hθ (x₀ • cu + x₁ • cv)).1
  have hn : 0 ≤ ‖x₀ • cu + x₁ • cv‖ ^ 2 / (1 + θ * Mg) := by
    have := hK.nonneg
    positivity
  have h0 := hn.trans hb
  rw [← hR, hRl] at h0
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right] at h0
  linarith

theorem s111x2_dir_quad {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {f g : Euc d → ℝ} {B1 B2 : ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (h1 : ∀ x, ‖fderiv ℝ f x‖ ≤ B1) (h2 : ∀ x, ‖fderiv ℝ g x‖ ≤ B2)
    (x₀ x₁ : ℝ) :
    0 ≤ x₀ * x₀ * s111x2_dirichlet μ f f + 2 * x₀ * x₁ * s111x2_dirichlet μ f g +
      x₁ * x₁ * s111x2_dirichlet μ g g := by
  have hB1 : 0 ≤ B1 := (norm_nonneg _).trans (h1 0)
  have hB2 : 0 ≤ B2 := (norm_nonneg _).trans (h2 0)
  have gf := s111x2_gradient_continuous hf
  have gg := s111x2_gradient_continuous hg
  have bf : ∀ x, ‖gradient f x‖ ≤ B1 := fun x => by rw [s111x2_norm_gradient]; exact h1 x
  have bg : ∀ x, ‖gradient g x‖ ≤ B2 := fun x => by rw [s111x2_norm_gradient]; exact h2 x
  have iint : ∀ (u v : Euc d → ℝ) (Bu Bv : ℝ), Continuous (gradient u) → Continuous (gradient v) →
      (∀ x, ‖gradient u x‖ ≤ Bu) → (∀ x, ‖gradient v x‖ ≤ Bv) →
      Integrable (fun x => inner ℝ (gradient u x) (gradient v x)) μ := by
    intro u v Bu Bv cu cv hu hv
    refine (integrable_const (Bu * Bv)).mono' (cu.inner cv).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul (hu x) (hv x) (norm_nonneg _)
      ((norm_nonneg _).trans (hu x)))
  have i11 := iint f f B1 B1 gf gf bf bf
  have i12 := iint f g B1 B2 gf gg bf bg
  have i22 := iint g g B2 B2 gg gg bg bg
  unfold s111x2_dirichlet
  have iS : Integrable (fun x => x₀ * x₀ * inner ℝ (gradient f x) (gradient f x) +
      2 * x₀ * x₁ * inner ℝ (gradient f x) (gradient g x)) μ := (i11.const_mul _).add (i12.const_mul _)
  rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul, ← integral_add (i11.const_mul _) (i12.const_mul _),
    ← integral_add iS (i22.const_mul _)]
  refine integral_nonneg fun x => ?_
  have : x₀ * x₀ * inner ℝ (gradient f x) (gradient f x) + 2 * x₀ * x₁ * inner ℝ (gradient f x) (gradient g x) +
      x₁ * x₁ * inner ℝ (gradient g x) (gradient g x) =
      inner ℝ (x₀ • gradient f x + x₁ • gradient g x) (x₀ • gradient f x + x₁ • gradient g x) := by
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, real_inner_comm]
    ring
  simp only [Pi.add_apply]
  rw [this]
  exact real_inner_self_nonneg

/-- The noise form is positive semidefinite (`t₁ ≤ t₂`). -/
theorem s111x2_noise_psd (hd : 2 ≤ d) {s a β : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (ha : 0 < a) (hβ : 0 < β)
    {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ) {t₁ t₂ : ℝ} (h1 : 0 ≤ t₁) (h12 : t₁ ≤ t₂)
    {φ ψ : Euc d → ℝ} {f g : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) t₁ φ f)
    (hg : IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) t₂ ψ g) (x₀ x₁ : ℝ) :
    0 ≤ x₀ * x₀ * noiseCovW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) β⁻¹ t₁ t₁ φ φ +
      2 * x₀ * x₁ * noiseCovW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) β⁻¹ t₁ t₂ φ ψ +
      x₁ * x₁ * noiseCovW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) β⁻¹ t₂ t₂ ψ ψ := by
  have h2 : 0 ≤ t₂ := h1.trans h12
  obtain ⟨M, T⟩ := s111x2_td_of_thermal hd hs0 hs ha hβ hρ
  haveI := isProbabilityMeasure_nu T.prob
  set μ := HRS.Whole.withDensityReal ρ with hμ
  set C := (quadraticGradientDyn d s a β).coeff (fun _ => ρ) with hC
  have hν : 0 < 2 * β⁻¹ := by positivity
  have n11 := s111x2_noise_eq hd hs0 hs ha hβ hρ h1 h1 hf hf
  have n12 := s111x2_noise_eq hd hs0 hs ha hβ hρ h1 h2 hf hg
  have n22 := s111x2_noise_eq hd hs0 hs ha hβ hρ h2 h2 hg hg
  rw [min_self] at n11 n22
  rw [min_eq_left h12] at n12
  rw [n11, n12, n22]
  obtain ⟨Bf0, Bf1, Bf2, hBf0, hBf1, hBf2, hfB⟩ := HRS.MS.S111X1.classical_bounds hf
  obtain ⟨Bg0, Bg1, Bg2, hBg0, hBg1, hBg2, hgB⟩ := HRS.MS.S111X1.classical_bounds hg
  have hDgg : ∀ r ∈ Icc (0 : ℝ) t₂, 0 ≤ s111x2_dirichlet μ (g r) (g r) := fun r _ =>
    integral_nonneg fun x => real_inner_self_nonneg
  rcases h1.eq_or_lt with h0 | hpos
  · subst h0
    simp only [Icc_self, setIntegral_measure_zero _ (by simp : volume ({0} : Set ℝ) = 0), mul_zero,
      add_zero, zero_add]
    have : 0 ≤ ∫ r in Icc 0 t₂, s111x2_dirichlet μ (g r) (g r) :=
      setIntegral_nonneg measurableSet_Icc hDgg
    have : 0 ≤ x₁ * x₁ * (2 * β⁻¹ * ∫ r in Icc 0 t₂, s111x2_dirichlet μ (g r) (g r)) :=
      mul_nonneg (mul_self_nonneg x₁) (mul_nonneg hν.le this)
    simpa using this
  · have hf' := s111x2_cls_restrict hg h1 h12
    have iff_ := (s111x2_classical_fd hd hs0 hs ha hβ hpos hρ hf hf).2.2.1
    have ifg := (s111x2_classical_fd hd hs0 hs ha hβ hpos hρ hf hf').2.2.1
    have igg := (s111x2_classical_fd hd hs0 hs ha hβ (hpos.trans_le h12) hρ hg hg).2.2.1
    have igg1 : IntegrableOn (fun r => s111x2_dirichlet μ (g r) (g r)) (Icc 0 t₁) :=
      igg.mono_set (Icc_subset_Icc le_rfl h12)
    have igg2 : IntegrableOn (fun r => s111x2_dirichlet μ (g r) (g r)) (Ioc t₁ t₂) :=
      igg.mono_set (fun r hr => ⟨(h1.trans hr.1.le), hr.2⟩)
    have hsplit : ∫ r in Icc 0 t₂, s111x2_dirichlet μ (g r) (g r) =
        (∫ r in Icc 0 t₁, s111x2_dirichlet μ (g r) (g r)) + ∫ r in Ioc t₁ t₂, s111x2_dirichlet μ (g r) (g r) := by
      rw [← Icc_union_Ioc_eq_Icc h1 h12]
      exact setIntegral_union (Set.disjoint_left.2 fun r hr1 hr2 => absurd hr1.2 (not_le.2 hr2.1))
        measurableSet_Ioc igg1 igg2
    have hQ : ∫ r in Icc 0 t₁, (x₀ * x₀ * s111x2_dirichlet μ (f r) (f r) +
        2 * x₀ * x₁ * s111x2_dirichlet μ (f r) (g r) + x₁ * x₁ * s111x2_dirichlet μ (g r) (g r)) =
        x₀ * x₀ * (∫ r in Icc 0 t₁, s111x2_dirichlet μ (f r) (f r)) +
        2 * x₀ * x₁ * (∫ r in Icc 0 t₁, s111x2_dirichlet μ (f r) (g r)) +
        x₁ * x₁ * ∫ r in Icc 0 t₁, s111x2_dirichlet μ (g r) (g r) := by
      have iS : IntegrableOn (fun r => x₀ * x₀ * s111x2_dirichlet μ (f r) (f r) +
          2 * x₀ * x₁ * s111x2_dirichlet μ (f r) (g r)) (Icc 0 t₁) := (iff_.const_mul _).add (ifg.const_mul _)
      rw [integral_add iS (igg1.const_mul _),
        integral_add (iff_.const_mul _) (ifg.const_mul _), integral_const_mul, integral_const_mul,
        integral_const_mul]
    have hQnn : 0 ≤ ∫ r in Icc 0 t₁, (x₀ * x₀ * s111x2_dirichlet μ (f r) (f r) +
        2 * x₀ * x₁ * s111x2_dirichlet μ (f r) (g r) + x₁ * x₁ * s111x2_dirichlet μ (g r) (g r)) := by
      refine setIntegral_nonneg measurableSet_Icc fun r hr => ?_
      have hrg : r ∈ Icc (0 : ℝ) t₂ := ⟨hr.1, hr.2.trans h12⟩
      exact s111x2_dir_quad (hf.c2 r hr |>.of_le (by norm_num)) (hg.c2 r hrg |>.of_le (by norm_num))
        (fun x => (hfB r hr x).2.1) (fun x => (hgB r hrg x).2.1) x₀ x₁
    have h22 : 0 ≤ ∫ r in Ioc t₁ t₂, s111x2_dirichlet μ (g r) (g r) :=
      setIntegral_nonneg measurableSet_Ioc fun r hr => hDgg r ⟨h1.trans hr.1.le, hr.2⟩
    rw [hsplit]
    have : 0 ≤ 2 * β⁻¹ * (x₀ * x₀ * (∫ r in Icc 0 t₁, s111x2_dirichlet μ (f r) (f r)) +
        2 * x₀ * x₁ * (∫ r in Icc 0 t₁, s111x2_dirichlet μ (f r) (g r)) +
        x₁ * x₁ * ∫ r in Icc 0 t₁, s111x2_dirichlet μ (g r) (g r)) +
        2 * β⁻¹ * (x₁ * x₁ * ∫ r in Ioc t₁ t₂, s111x2_dirichlet μ (g r) (g r)) := by
      rw [← hQ]
      have := mul_nonneg hν.le hQnn
      have := mul_nonneg hν.le (mul_nonneg (mul_self_nonneg x₁) h22)
      linarith
    nlinarith [this]

theorem s111x2_pos2 {a b c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hb : b ^ 2 ≤ a * c) (x y : ℝ) :
    0 ≤ a * x ^ 2 + 2 * b * x * y + c * y ^ 2 := by
  rcases ha.eq_or_lt with h0 | hpos
  · subst h0
    have : b = 0 := by nlinarith [sq_nonneg b]
    subst this
    nlinarith [mul_nonneg hc (sq_nonneg y)]
  · nlinarith [sq_nonneg (a * x + b * y), sq_nonneg y, mul_nonneg hpos.le (mul_nonneg hc (sq_nonneg y))]

/-- The covariance matrix of two observations of the linear Gaussian evolution is positive semidefinite. -/
theorem s111x2_cov_psd2 (hd : 2 ≤ d) {s a β : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (ha : 0 < a) (hβ : 0 < β)
    {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ) {θ : ℝ} (hθ : 0 ≤ θ)
    (ts : Fin 2 → ℝ) (hts : ∀ i, 0 ≤ ts i) (φ : Fin 2 → Euc d → ℝ) (f : Fin 2 → ℝ → Euc d → ℝ)
    (hf : ∀ i, IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) (ts i) (φ i) (f i))
    (hmem : ∀ i, MemLp (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 (ts i) (φ i)) 2
      (HRS.Whole.withDensityReal ρ)) :
    (Matrix.of fun i j : Fin 2 =>
      HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) θ
        (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 (ts i) (φ i))
        (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 (ts j) (φ j)) +
      noiseCovW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) β⁻¹ (ts i) (ts j) (φ i) (φ j)).PosSemidef := by
  obtain ⟨M, T⟩ := s111x2_td_of_thermal hd hs0 hs ha hβ hρ
  haveI := isProbabilityMeasure_nu T.prob
  have hdr : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < d := by linarith
  obtain ⟨M₀, c, S, hc, hTc⟩ := HRS.MS.TransOp.s611_tcref_of_thermal hd hs0 hsd ha hβ hρ
  obtain ⟨Mg, K, hK⟩ := s111x2_krep_of_tcref (by omega) hs0 hsd hc hTc
  have hRF := s111x2_responseForm hK hθ (le_refl θ)
  set μ := HRS.Whole.withDensityReal ρ with hμ
  set C := (quadraticGradientDyn d s a β).coeff (fun _ => ρ) with hC
  have hsym : ∀ i j : Fin 2, HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) μ θ
      (propagatorW C 0 (ts i) (φ i)) (propagatorW C 0 (ts j) (φ j)) +
      noiseCovW C β⁻¹ (ts i) (ts j) (φ i) (φ j) =
      HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) μ θ
        (propagatorW C 0 (ts j) (φ j)) (propagatorW C 0 (ts i) (φ i)) +
      noiseCovW C β⁻¹ (ts j) (ts i) (φ j) (φ i) := fun i j => by
    rw [hRF.symmetry _ _ (hmem i) (hmem j), s111x2_noise_symm]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    ext i j
    rw [Matrix.transpose_apply]
    simp only [Matrix.of_apply]
    exact (hsym i j).symm
  · simp only [dotProduct, Matrix.mulVec, star_trivial, Matrix.of_apply, Fin.sum_univ_two]
    -- the Gram part and the noise part
    have hG := s111x2_gram_psd hK hθ (hmem 0) (hmem 1) (x 0) (x 1)
    have hN : 0 ≤ x 0 * x 0 * noiseCovW C β⁻¹ (ts 0) (ts 0) (φ 0) (φ 0) +
        2 * x 0 * x 1 * noiseCovW C β⁻¹ (ts 0) (ts 1) (φ 0) (φ 1) +
        x 1 * x 1 * noiseCovW C β⁻¹ (ts 1) (ts 1) (φ 1) (φ 1) := by
      rcases le_total (ts 0) (ts 1) with h01 | h10
      · exact s111x2_noise_psd hd hs0 hs ha hβ hρ (hts 0) h01 (hf 0) (hf 1) (x 0) (x 1)
      · have := s111x2_noise_psd hd hs0 hs ha hβ hρ (hts 1) h10 (hf 1) (hf 0) (x 1) (x 0)
        rw [s111x2_noise_symm (C := C) β⁻¹ (ts 1) (ts 0) (φ 1) (φ 0)] at this
        linarith
    have e10 : noiseCovW C β⁻¹ (ts 1) (ts 0) (φ 1) (φ 0) = noiseCovW C β⁻¹ (ts 0) (ts 1) (φ 0) (φ 1) :=
      (s111x2_noise_symm β⁻¹ _ _ _ _).symm
    simp only [mul_add, Fin.sum_univ_two] at *
    rw [e10]
    nlinarith [hG, hN]

end HRS.MS.S111X2
