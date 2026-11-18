import HRS.MS.S82WN1
import HRS.MS.S82WK6

/-!
# S8.2 A04 (S82W), part 10: the Gibbs weight, integration by parts and mean zero of the generator
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.S82W
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82U

section wt
variable {d N : ℕ}

lemma w_int_zero_of {a beta : ℝ} {g : EucConfig d N → ℝ}
    (h : ∫ X, u4w d N a beta X * g X ∂(volume : Measure (EucConfig d N)) = 0) :
    ∫ X, g X ∂(canonicalP d N a beta) = 0 := by
  unfold canonicalP HRS.Whole.canonicalGibbs
  rw [integral_smul_measure]
  have hm : Measurable (fun X : EucConfig d N => ENNReal.ofReal (u4w d N a beta X)) :=
    ENNReal.measurable_ofReal.comp (u4_w_meas d N a beta)
  have := integral_withDensity_eq_integral_toReal_smul (μ := (volume : Measure (EucConfig d N)))
    (f := fun X => ENNReal.ofReal (Real.exp (-beta *
      HRS.Whole.canonicalHamiltonian (rieszKernel d (criticalS d)) (confinement a) X))) hm
    (Eventually.of_forall fun X => ENNReal.ofReal_lt_top) g
  rw [this]
  simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
  have e : ∫ X, Real.exp (-beta * HRS.Whole.canonicalHamiltonian (rieszKernel d (criticalS d))
      (confinement a) X) * g X ∂(volume : Measure (EucConfig d N)) = 0 := h
  rw [e]; simp

lemma w_w_hasFDerivAt (hd : 2 ≤ d) (a beta : ℝ) {X : EucConfig d N} (hX : X ∉ eucCollisionSet d N) :
    ∃ Wd : EucConfig d N →L[ℝ] ℝ, HasFDerivAt (u4w d N a beta) Wd X ∧
      ∀ (i : Fin N) (v : Euc d), Wd (u4L d N i v) =
        beta * u4w d N a beta X *
          inner ℝ (particleDriftW (quadraticGradientDyn d (criticalS d) a beta) X i) v := by
  obtain ⟨Hd, hHd, hev⟩ := w_Hs_hasFDerivAt hd a hX
  refine ⟨Real.exp (-beta * HRS.Whole.canonicalHamiltonian (rieszKernel d (criticalS d)) (confinement a) X) •
    ((-beta) • Hd), ?_, ?_⟩
  · exact (hHd.const_mul (-beta)).exp
  · intro i v
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, hev, u4_drift_eq, smul_eq_mul, smul_eq_mul]
    simp only [u4w]
    rw [inner_sub_left, inner_neg_left, real_inner_smul_left, real_inner_smul_left, inner_add_left,
      real_inner_smul_left, real_inner_smul_left]
    ring

lemma w_fderiv_w_dir (hd : 2 ≤ d) (a beta : ℝ) {X : EucConfig d N} (hX : X ∉ eucCollisionSet d N)
    (i : Fin N) (v : Euc d) :
    fderiv ℝ (u4w d N a beta) X (u4L d N i v) = beta * u4w d N a beta X *
      inner ℝ (particleDriftW (quadraticGradientDyn d (criticalS d) a beta) X i) v := by
  obtain ⟨Wd, hW, hv⟩ := w_w_hasFDerivAt hd a beta hX
  rw [hW.fderiv, hv]

lemma w_gen_eq_dirs (hd : 2 ≤ d) {a beta : ℝ} (hbeta : 0 < beta) {φ : EucConfig d N → ℝ}
    (hφ : ContDiffOn ℝ 2 φ (eucCollisionSet d N)ᶜ) {X : EucConfig d N} (hX : X ∉ eucCollisionSet d N) :
    u4w d N a beta X * particleGenerator (quadraticGradientDyn d (criticalS d) a beta) φ X =
      beta⁻¹ * ∑ i : Fin N, ∑ k : Fin (Module.finrank ℝ (Euc d)),
        (u4w d N a beta X * fderiv ℝ (fderiv ℝ φ) X (u4L d N i ((stdOrthonormalBasis ℝ (Euc d)) k))
            (u4L d N i ((stdOrthonormalBasis ℝ (Euc d)) k)) +
          fderiv ℝ (u4w d N a beta) X (u4L d N i ((stdOrthonormalBasis ℝ (Euc d)) k)) *
            fderiv ℝ φ X (u4L d N i ((stdOrthonormalBasis ℝ (Euc d)) k))) := by
  have hgrad : ∀ i : Fin N, inner ℝ (particleDriftW (quadraticGradientDyn d (criticalS d) a beta) X i)
      (Phase2S82.configGrad φ X i) =
      ∑ k, inner ℝ ((stdOrthonormalBasis ℝ (Euc d)) k)
        (particleDriftW (quadraticGradientDyn d (criticalS d) a beta) X i) *
        fderiv ℝ φ X (u4L d N i ((stdOrthonormalBasis ℝ (Euc d)) k)) := by
    intro i
    rw [u4_configGrad_eq hφ hX i, real_inner_comm, InnerProductSpace.toDual_symm_apply,
      ContinuousLinearMap.comp_apply]
    set dr := particleDriftW (quadraticGradientDyn d (criticalS d) a beta) X i
    conv_lhs => rw [← (stdOrthonormalBasis ℝ (Euc d)).sum_repr' dr]
    simp only [map_sum, map_smul, smul_eq_mul]
  have hfw : ∀ (i : Fin N) (k : Fin (Module.finrank ℝ (Euc d))),
      fderiv ℝ (u4w d N a beta) X (u4L d N i ((stdOrthonormalBasis ℝ (Euc d)) k)) =
        beta * u4w d N a beta X * inner ℝ (particleDriftW (quadraticGradientDyn d (criticalS d) a beta) X i)
          ((stdOrthonormalBasis ℝ (Euc d)) k) := fun i k => w_fderiv_w_dir hd a beta hX i _
  have hgen : particleGenerator (quadraticGradientDyn d (criticalS d) a beta) φ X =
      beta⁻¹ * ∑ i, Laplacian.laplacian (fun y => φ (Function.update X i y)) (X i) +
        ∑ i, inner ℝ (particleDriftW (quadraticGradientDyn d (criticalS d) a beta) X i)
          (Phase2S82.configGrad φ X i) := rfl
  rw [hgen]
  simp_rw [hgrad, u4_laplacian_eq hφ hX, hfw]
  have hb : beta ≠ 0 := hbeta.ne'
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, mul_add]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  rw [real_inner_comm]
  field_simp

lemma w_integrable_of_supp {F : EucConfig d N → ℝ} {K : Set (EucConfig d N)} (hK : IsCompact K)
    (hKD : K ⊆ (eucCollisionSet d N)ᶜ) (hF : ContinuousOn F (eucCollisionSet d N)ᶜ)
    (hz : ∀ x ∉ K, F x = 0) : Integrable F (volume : Measure (EucConfig d N)) := by
  have h1 : IntegrableOn F K volume := (hF.mono hKD).integrableOn_compact hK
  refine (integrableOn_iff_integrable_of_support_subset (s := K) ?_).1 h1
  intro x hx
  by_contra hxK
  exact hx (hz x hxK)

lemma w_w_contOn (hd : 2 ≤ d) (a beta : ℝ) :
    ContinuousOn (u4w d N a beta) (eucCollisionSet d N)ᶜ := fun X hX => by
  obtain ⟨Wd, hW, -⟩ := w_w_hasFDerivAt hd a beta hX
  exact hW.continuousAt.continuousWithinAt

lemma w_dir_cont (hd : 2 ≤ d) (a beta : ℝ) (i : Fin N) (v : Euc d) :
    ContinuousOn (fun X => fderiv ℝ (u4w d N a beta) X (u4L d N i v)) (eucCollisionSet d N)ᶜ := by
  have : ContinuousOn (fun X : EucConfig d N => beta * u4w d N a beta X *
      inner ℝ (particleDriftW (quadraticGradientDyn d (criticalS d) a beta) X i) v) (eucCollisionSet d N)ᶜ :=
    (continuousOn_const.mul (w_w_contOn hd a beta)).mul ((u4_drift_cont hd a beta i).inner continuousOn_const)
  exact this.congr fun X hX => w_fderiv_w_dir hd a beta hX i v

lemma w_ibp_dir (hd : 2 ≤ d) (a beta : ℝ) {φ : EucConfig d N → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hc : HasCompactSupport φ) (hts : tsupport φ ⊆ (eucCollisionSet d N)ᶜ) (i : Fin N) (v : Euc d) :
    Integrable (fun X => u4w d N a beta X * fderiv ℝ (fderiv ℝ φ) X (u4L d N i v) (u4L d N i v) +
      fderiv ℝ (u4w d N a beta) X (u4L d N i v) * fderiv ℝ φ X (u4L d N i v))
      (volume : Measure (EucConfig d N)) ∧
    ∫ X, (u4w d N a beta X * fderiv ℝ (fderiv ℝ φ) X (u4L d N i v) (u4L d N i v) +
      fderiv ℝ (u4w d N a beta) X (u4L d N i v) * fderiv ℝ φ X (u4L d N i v))
      ∂(volume : Measure (EucConfig d N)) = 0 := by
  set e := u4L d N i v with he
  have hK : IsCompact (tsupport φ) := hc
  have hφ1 : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hdφ : ContDiff ℝ 1 (fderiv ℝ φ) := by
    have : ContDiff ℝ (1 + 1) φ := by rwa [show ((1 : WithTop ℕ∞) + 1) = 2 by norm_num]
    exact (contDiff_succ_iff_fderiv.1 this).2.2
  have hd2 : Differentiable ℝ (fderiv ℝ φ) := hdφ.differentiable one_ne_zero
  have hc1 : Continuous (fderiv ℝ φ) := hdφ.continuous
  have hc2 : Continuous (fderiv ℝ (fderiv ℝ φ)) := hdφ.continuous_fderiv one_ne_zero
  -- the function g = ∂_e φ
  set g : EucConfig d N → ℝ := fun X => fderiv ℝ φ X e with hg
  have hgd : ∀ X, HasFDerivAt g ((fderiv ℝ (fderiv ℝ φ) X).flip e) X := fun X => by
    have := (hd2 X).hasFDerivAt.clm_apply (hasFDerivAt_const e X)
    simpa using this
  have hgder : ∀ X, fderiv ℝ g X e = fderiv ℝ (fderiv ℝ φ) X e e := fun X => by
    rw [(hgd X).fderiv]; rfl
  -- vanishing outside the support
  have hzero : ∀ x ∉ tsupport φ, fderiv ℝ φ x = 0 ∧ fderiv ℝ (fderiv ℝ φ) x = 0 := by
    intro x hx
    refine w_jets_zero ?_
    filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hx] with y hy
    exact image_eq_zero_of_notMem_tsupport hy
  have hgts : tsupport g ⊆ tsupport φ := by
    refine closure_minimal ?_ (isClosed_tsupport φ)
    intro x hx
    by_contra hxn
    exact hx (by simp [hg, (hzero x hxn).1])
  -- integrability
  have hI1 : Integrable (fun X => u4w d N a beta X * g X) (volume : Measure (EucConfig d N)) := by
    refine w_integrable_of_supp hK hts ((w_w_contOn hd a beta).mul (hc1.clm_apply continuous_const).continuousOn) ?_
    intro x hx
    simp [hg, (hzero x hx).1]
  have hI2 : Integrable (fun X => fderiv ℝ (u4w d N a beta) X e * g X) (volume : Measure (EucConfig d N)) := by
    refine w_integrable_of_supp hK hts ((w_dir_cont hd a beta i v).mul
      (hc1.clm_apply continuous_const).continuousOn) ?_
    intro x hx
    simp [hg, (hzero x hx).1]
  have hI3 : Integrable (fun X => u4w d N a beta X * fderiv ℝ g X e) (volume : Measure (EucConfig d N)) := by
    simp_rw [hgder]
    refine w_integrable_of_supp hK hts ((w_w_contOn hd a beta).mul
      ((hc2.clm_apply continuous_const).clm_apply continuous_const).continuousOn) ?_
    intro x hx
    simp [(hzero x hx).2]
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure (EucConfig d N)))
    (f := u4w d N a beta) (g := g) (v := e) hI2 hI3 hI1 ?_ ?_
  · simp_rw [hgder] at hibp hI3
    refine ⟨hI3.add hI2, ?_⟩
    rw [integral_add hI3 hI2, hibp]
    simp [hg]
  · intro x hx
    have hxD : x ∈ (eucCollisionSet d N)ᶜ := hts (hgts hx)
    obtain ⟨Wd, hW, -⟩ := w_w_hasFDerivAt hd a beta hxD
    exact hW.differentiableAt
  · intro x _
    exact (hgd x).differentiableAt

theorem w_mean_zero_smooth (hd : 2 ≤ d) {a beta : ℝ} (hbeta : 0 < beta) {φ : EucConfig d N → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ) (hts : tsupport φ ⊆ (eucCollisionSet d N)ᶜ) :
    ∫ X, particleGenerator (quadraticGradientDyn d (criticalS d) a beta) φ X
      ∂(canonicalP d N a beta) = 0 := by
  refine w_int_zero_of ?_
  have hae : ∀ᵐ X ∂(volume : Measure (EucConfig d N)), X ∉ eucCollisionSet d N := by
    rw [ae_iff]; simpa using u4_coll_null (by omega) N
  have hcd : ContDiffOn ℝ 2 φ (eucCollisionSet d N)ᶜ := hφ.contDiffOn
  have h1 : ∫ X, u4w d N a beta X * particleGenerator (quadraticGradientDyn d (criticalS d) a beta) φ X
        ∂(volume : Measure (EucConfig d N)) =
      ∫ X, beta⁻¹ * ∑ i : Fin N, ∑ k : Fin (Module.finrank ℝ (Euc d)),
        (u4w d N a beta X * fderiv ℝ (fderiv ℝ φ) X (u4L d N i ((stdOrthonormalBasis ℝ (Euc d)) k))
            (u4L d N i ((stdOrthonormalBasis ℝ (Euc d)) k)) +
          fderiv ℝ (u4w d N a beta) X (u4L d N i ((stdOrthonormalBasis ℝ (Euc d)) k)) *
            fderiv ℝ φ X (u4L d N i ((stdOrthonormalBasis ℝ (Euc d)) k)))
        ∂(volume : Measure (EucConfig d N)) := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with X hX
    exact w_gen_eq_dirs hd hbeta hcd hX
  rw [h1, integral_const_mul]
  have h2 : ∀ i : Fin N, ∫ X, ∑ k : Fin (Module.finrank ℝ (Euc d)),
        (u4w d N a beta X * fderiv ℝ (fderiv ℝ φ) X (u4L d N i ((stdOrthonormalBasis ℝ (Euc d)) k))
            (u4L d N i ((stdOrthonormalBasis ℝ (Euc d)) k)) +
          fderiv ℝ (u4w d N a beta) X (u4L d N i ((stdOrthonormalBasis ℝ (Euc d)) k)) *
            fderiv ℝ φ X (u4L d N i ((stdOrthonormalBasis ℝ (Euc d)) k)))
        ∂(volume : Measure (EucConfig d N)) = 0 := by
    intro i
    rw [integral_finset_sum _ (fun k _ => (w_ibp_dir hd a beta hφ hc hts i _).1)]
    exact Finset.sum_eq_zero fun k _ => (w_ibp_dir hd a beta hφ hc hts i _).2
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun k _ => (w_ibp_dir hd a beta hφ hc hts i _).1))]
  simp [h2]

end wt

end HRS.MS.S82W
