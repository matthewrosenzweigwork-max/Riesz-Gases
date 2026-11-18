import HRS.Whole.SteinAux2
import HRS.Prob.HilbertMartingale

/-!
# Packet STEIN, auxiliary file 3: the Stein bound for `C_b^5` test functions

`stein_core`: for `Φ ∈ C_b^5` and the Stein solution `u` of `Φ`, insert `f_i = ∂_i u` in the
Stein-type identity and use trace duality.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ContDiff

namespace HRS.Whole.Stein
variable {n : ℕ}

lemma vec_expand (v : EuclideanSpace ℝ (Fin n)) :
    v = ∑ a, v a • (EuclideanSpace.single a (1 : ℝ) : EuclideanSpace ℝ (Fin n)) := by
  ext i; simp [Pi.single_apply]

lemma clm_expand (L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (w : EuclideanSpace ℝ (Fin n)) :
    L w = ∑ b, w b * L (EuclideanSpace.single b (1 : ℝ)) := by
  conv_lhs => rw [vec_expand w]
  simp [map_sum]

lemma ell_expand (ℓ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (v w : EuclideanSpace ℝ (Fin n)) :
    ℓ v w = ∑ a, ∑ b, v a * w b *
      ℓ (EuclideanSpace.single a (1 : ℝ)) (EuclideanSpace.single b (1 : ℝ)) := by
  have h1 : ℓ v = ∑ a, v a • ℓ (EuclideanSpace.single a (1 : ℝ)) := by
    conv_lhs => rw [vec_expand v]
    simp [map_sum]
  have h2 : ∀ L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ,
      L w = ∑ b, w b * L (EuclideanSpace.single b (1 : ℝ)) := by
    intro L
    conv_lhs => rw [vec_expand w]
    simp [map_sum]
  rw [h1, sum_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_apply, h2, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

lemma trace_dual_ell (ℓ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (β : ℝ) (hβ : ‖ℓ‖ ≤ β) (Q : Matrix (Fin n) (Fin n) ℝ) :
    |∑ a, ∑ b, ℓ (EuclideanSpace.single b (1 : ℝ)) (EuclideanSpace.single a (1 : ℝ)) * Q a b|
      ≤ β * traceNormMatrix Q := by
  have hβ0 : 0 ≤ β := le_trans (norm_nonneg ℓ) hβ
  refine HRS.LindebergAux.trace_dual
    (Matrix.of fun a b => ℓ (EuclideanSpace.single b (1 : ℝ)) (EuclideanSpace.single a (1 : ℝ))) Q β hβ0 ?_
  intro u v
  have hnorm : ∀ z : Fin n → ℝ, ‖(WithLp.toLp 2 z : EuclideanSpace ℝ (Fin n))‖ = Real.sqrt (z ⬝ᵥ z) := by
    intro z
    rw [EuclideanSpace.norm_eq]
    congr 1
    simp only [dotProduct, Real.norm_eq_abs, sq, abs_mul_abs_self]
  have e : u ⬝ᵥ ((Matrix.of fun a b => ℓ (EuclideanSpace.single b (1 : ℝ))
      (EuclideanSpace.single a (1 : ℝ))).mulVec v) =
      ℓ (WithLp.toLp 2 v) (WithLp.toLp 2 u) := by
    rw [ell_expand]
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [e]
  calc |ℓ (WithLp.toLp 2 v) (WithLp.toLp 2 u)|
      = ‖ℓ (WithLp.toLp 2 v) (WithLp.toLp 2 u)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖ℓ‖ * ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ * ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ :=
        ContinuousLinearMap.le_opNorm₂ ℓ _ _
    _ ≤ β * Real.sqrt (v ⬝ᵥ v) * Real.sqrt (u ⬝ᵥ u) := by
        rw [hnorm, hnorm]
        gcongr
    _ = β * Real.sqrt (u ⬝ᵥ u) * Real.sqrt (v ⬝ᵥ v) := by ring

section Core

variable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]

lemma int_comp_bdd {n : ℕ} {X : Ω → EuclideanSpace ℝ (Fin n)} (hXm : AEStronglyMeasurable X P)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : Continuous g) (K : ℝ) (hK : ∀ x, |g x| ≤ K) :
    Integrable (fun w => g (X w)) P :=
  (integrable_const K).mono' (hg.comp_aestronglyMeasurable hXm)
    (Eventually.of_forall fun w => by rw [Real.norm_eq_abs]; exact hK _)

lemma int_mul_comp_bdd {n : ℕ} {X : Ω → EuclideanSpace ℝ (Fin n)} (hXm : AEStronglyMeasurable X P)
    {f : Ω → ℝ} (hf : Integrable f P)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : Continuous g) (K : ℝ) (hK : ∀ x, |g x| ≤ K) :
    Integrable (fun w => f w * g (X w)) P :=
  hf.mul_bdd (c := K) (hg.comp_aestronglyMeasurable hXm)
    (Eventually.of_forall fun w => by rw [Real.norm_eq_abs]; exact hK _)

lemma gauss_sq_integrable (G : Ω → EuclideanSpace ℝ (Fin n)) (hG : AEMeasurable G P)
    (hGauss : IsCenteredGaussian (law P G)) (a b : Fin n) :
    Integrable (fun w => G w a * G w b) P := by
  have := hGauss.1
  have : IsProbabilityMeasure (law P G) := by
    unfold law; exact (Measure.isProbabilityMeasure_map_iff hG).2 inferInstance
  have h := gaussian_sqnorm_integrable (γ := law P G) hGauss
  have h2 : Integrable (fun w => ‖G w‖ ^ 2) P := by
    have := (integrable_map_measure (μ := P) (f := G) (g := fun y : EuclideanSpace ℝ (Fin n) => ‖y‖ ^ 2)
      (h.aestronglyMeasurable) hG).1 h
    exact this
  refine h2.mono' ?_ (Eventually.of_forall fun w => ?_)
  · have ha : Measurable (fun y : EuclideanSpace ℝ (Fin n) => y a) :=
      (EuclideanSpace.proj a : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).continuous.measurable
    have hb : Measurable (fun y : EuclideanSpace ℝ (Fin n) => y b) :=
      (EuclideanSpace.proj b : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ).continuous.measurable
    exact ((ha.mul hb).comp_aemeasurable hG).aestronglyMeasurable
  · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have h1 : |G w a| ≤ ‖G w‖ := by
      simpa using PiLp.norm_apply_le (G w) a
    have h2 : |G w b| ≤ ‖G w‖ := by
      simpa using PiLp.norm_apply_le (G w) b
    calc |G w a| * |G w b| ≤ ‖G w‖ * ‖G w‖ := mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
      _ = ‖G w‖ ^ 2 := by ring

lemma cc_eq (G : Ω → EuclideanSpace ℝ (Fin n)) (C : Matrix (Fin n) (Fin n) ℝ)
    (hC : ∀ i j, C i j = ∫ w, G w i * G w j ∂P)
    (hGsq : ∀ a b, Integrable (fun w => G w a * G w b) P)
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    ∫ w, iteratedFDeriv ℝ 2 u x ![G w, G w] ∂P =
      ∑ a, ∑ b, C a b * fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single b (1 : ℝ))
        (EuclideanSpace.single a (1 : ℝ)) := by
  have h1 : ∀ w, iteratedFDeriv ℝ 2 u x ![G w, G w] = ∑ a, ∑ b, G w a * G w b *
      fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single a (1 : ℝ)) (EuclideanSpace.single b (1 : ℝ)) := by
    intro w
    rw [iteratedFDeriv_two_apply]
    simpa using ell_expand (fderiv ℝ (fderiv ℝ u) x) (G w) (G w)
  simp_rw [h1]
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ fun b _ => (hGsq a b).mul_const _)]
  have h3 : ∀ a, ∫ w, ∑ b, G w a * G w b *
      fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single a (1 : ℝ)) (EuclideanSpace.single b (1 : ℝ)) ∂P =
      ∑ b, C a b * fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single a (1 : ℝ)) (EuclideanSpace.single b (1 : ℝ)) := by
    intro a
    rw [integral_finsetSum _ (fun b _ => (hGsq a b).mul_const _)]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_mul_const, hC]
  simp_rw [h3]
  have hsymm : ∀ a b, C a b = C b a := by
    intro a b; rw [hC, hC]; simp_rw [mul_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hsymm]

lemma tn_integrable (T : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hTm : ∀ i j, AEStronglyMeasurable (fun w => T w i j) P)
    (hT : Integrable (fun w => traceNormMatrix (T w)) P) (C : Matrix (Fin n) (Fin n) ℝ) :
    Integrable (fun w => traceNormMatrix (T w - C)) P := by
  obtain ⟨T', hT'⟩ : ∃ T' : Ω → Matrix (Fin n) (Fin n) ℝ,
      T' = fun w i j => (hTm i j).mk _ w := ⟨_, rfl⟩
  have hmeas' : ∀ i j, Measurable (fun w => T' w i j) := by
    intro i j; rw [hT']; exact (hTm i j).stronglyMeasurable_mk.measurable
  have hm : Measurable (fun w => traceNormMatrix (T' w - C)) :=
    HRS.measurable_traceNormMatrix (fun w => T' w - C)
      (fun i j => by simpa using (hmeas' i j).sub_const (C i j))
  have hae : ∀ᵐ w ∂P, ∀ i j, T w i j = T' w i j := by
    refine ae_all_iff.2 fun i => ae_all_iff.2 fun j => ?_
    rw [hT']; exact (hTm i j).ae_eq_mk
  have hmeas : AEStronglyMeasurable (fun w => traceNormMatrix (T w - C)) P := by
    refine hm.aestronglyMeasurable.congr ?_
    filter_upwards [hae] with w hw
    have : T w = T' w := by ext i j; exact hw i j
    rw [this]
  refine (hT.add (integrable_const (traceNormMatrix (-C)))).mono' hmeas
    (Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (traceNormMatrix_nonneg _), sub_eq_add_neg]
  exact HRS.LindebergAux.traceNormMatrix_add_le _ _

theorem stein_core_u (X R : Ω → EuclideanSpace ℝ (Fin n)) (T : Ω → Matrix (Fin n) (Fin n) ℝ)
    (hX : Integrable X P) (hR : Integrable R P)
    (hTm : ∀ i j, AEStronglyMeasurable (fun w => T w i j) P)
    (hT : Integrable (fun w => traceNormMatrix (T w)) P) (hid : SId P X R T)
    (G : Ω → EuclideanSpace ℝ (Fin n)) (hG : AEMeasurable G P)
    (hGauss : IsCenteredGaussian (law P G)) (C : Matrix (Fin n) (Fin n) ℝ)
    (hC : ∀ i j, C i j = ∫ w, G w i * G w j ∂P)
    (Φ : EuclideanSpace ℝ (Fin n) → ℝ) (hΦc : Continuous Φ) (K : ℝ) (hΦK : ∀ x, |Φ x| ≤ K)
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (hu : ContDiff ℝ 5 u)
    (a b : ℝ) (ha : ∀ x, ‖fderiv ℝ u x‖ ≤ a) (hb : ∀ x, ‖fderiv ℝ (fderiv ℝ u) x‖ ≤ b)
    (C3 : ℝ) (h3 : ∀ x, ‖iteratedFDeriv ℝ 3 u x‖ ≤ C3)
    (hseq : ∀ x, ∫ w, iteratedFDeriv ℝ 2 u x ![G w, G w] ∂P - fderiv ℝ u x x =
        Φ x - ∫ w, Φ (G w) ∂P) :
    |∫ w, Φ (X w) ∂P - ∫ w, Φ (G w) ∂P| ≤
      a * ∫ w, ‖R w‖ ∂P + b * ∫ w, traceNormMatrix (T w - C) ∂P := by
  have hXm : AEStronglyMeasurable X P := hX.aestronglyMeasurable
  have hdu : ContDiff ℝ 4 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have hℓc : Continuous (fderiv ℝ (fderiv ℝ u)) := (hdu.fderiv_right (m := 3) (by norm_num)).continuous
  have hfc : Continuous (fderiv ℝ u) := hdu.continuous
  have ha0 : 0 ≤ a := le_trans (norm_nonneg (fderiv ℝ u 0)) (ha 0)
  have hb0 : 0 ≤ b := le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ u) 0)) (hb 0)
  have hone : ∀ i : Fin n, ‖(EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin n))‖ = 1 :=
    fun i => norm_single_one i
  -- derivative of the test functions
  have hfi_der : ∀ (i : Fin n) x v, fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.single i (1 : ℝ))) x v =
      fderiv ℝ (fderiv ℝ u) x v (EuclideanSpace.single i (1 : ℝ)) := by
    intro i x v
    have hd : DifferentiableAt ℝ (fderiv ℝ u) x := (hdu.differentiable (by norm_num)) x
    rw [fderiv_clm_apply hd (differentiableAt_const _)]
    simp
  have hfi_cd : ∀ i : Fin n, ContDiff ℝ 2 (fun y => fderiv ℝ u y (EuclideanSpace.single i (1 : ℝ))) :=
    fun i => (hdu.of_le (by norm_num)).clm_apply contDiff_const
  have hfi_b0 : ∀ (i : Fin n) x, |fderiv ℝ u x (EuclideanSpace.single i (1 : ℝ))| ≤ a := by
    intro i x
    rw [← Real.norm_eq_abs]
    calc ‖fderiv ℝ u x (EuclideanSpace.single i (1 : ℝ))‖
        ≤ ‖fderiv ℝ u x‖ * ‖(EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin n))‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ a * 1 := by rw [hone]; exact mul_le_mul_of_nonneg_right (ha x) zero_le_one
      _ = a := mul_one a
  have hfi_b1 : ∀ (i : Fin n) x, ‖fderiv ℝ (fun y => fderiv ℝ u y (EuclideanSpace.single i (1 : ℝ))) x‖ ≤ b := by
    intro i x
    refine ContinuousLinearMap.opNorm_le_bound _ hb0 fun v => ?_
    rw [hfi_der]
    calc ‖fderiv ℝ (fderiv ℝ u) x v (EuclideanSpace.single i (1 : ℝ))‖
        ≤ ‖fderiv ℝ (fderiv ℝ u) x v‖ * ‖(EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin n))‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖fderiv ℝ (fderiv ℝ u) x‖ * ‖v‖) * 1 := by
          rw [hone]
          exact mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) zero_le_one
      _ ≤ b * ‖v‖ := by
          rw [mul_one]; exact mul_le_mul_of_nonneg_right (hb x) (norm_nonneg _)
  have hfi_b2 : ∀ (i : Fin n) x, ‖iteratedFDeriv ℝ 2 (fun y => fderiv ℝ u y (EuclideanSpace.single i (1 : ℝ))) x‖ ≤ C3 := by
    intro i x
    set L : (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) →L[ℝ] ℝ :=
      ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ)) with hL
    have hLn : ‖L‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun g => ?_
      rw [hL, ContinuousLinearMap.apply_apply, one_mul]
      calc ‖g (EuclideanSpace.single i (1 : ℝ))‖
          ≤ ‖g‖ * ‖(EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin n))‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ = ‖g‖ := by rw [hone, mul_one]
    have h1 := ContinuousLinearMap.norm_iteratedFDeriv_comp_left L (f := fderiv ℝ u) (x := x)
      (N := 4) (n := 2) hdu.contDiffAt (by norm_num)
    have h2 : ‖iteratedFDeriv ℝ 2 (fderiv ℝ u) x‖ = ‖iteratedFDeriv ℝ 3 u x‖ :=
      norm_iteratedFDeriv_fderiv (n := 2)
    have h4 : (⇑L ∘ fderiv ℝ u) = fun y => fderiv ℝ u y (EuclideanSpace.single i (1 : ℝ)) := rfl
    rw [h4] at h1
    refine h1.trans ?_
    rw [h2]
    calc ‖L‖ * ‖iteratedFDeriv ℝ 3 u x‖ ≤ 1 * ‖iteratedFDeriv ℝ 3 u x‖ :=
          mul_le_mul_of_nonneg_right hLn (norm_nonneg _)
      _ ≤ C3 := by rw [one_mul]; exact h3 x
  have hidi := fun i : Fin n => sid_ext P X R T hX hR hTm hT hid
    (fun y => fderiv ℝ u y (EuclideanSpace.single i (1 : ℝ))) (hfi_cd i) a (hfi_b0 i) b (hfi_b1 i)
    C3 (hfi_b2 i) i
  simp_rw [hfi_der] at hidi
  have hHc : ∀ p q : Fin n, Continuous (fun x => fderiv ℝ (fderiv ℝ u) x
      (EuclideanSpace.single q (1 : ℝ)) (EuclideanSpace.single p (1 : ℝ))) :=
    fun p q => (hℓc.clm_apply continuous_const).clm_apply continuous_const
  have hHb : ∀ (p q : Fin n) x, |fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single q (1 : ℝ))
      (EuclideanSpace.single p (1 : ℝ))| ≤ b := by
    intro p q x
    rw [← Real.norm_eq_abs]
    calc ‖fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single q (1 : ℝ)) (EuclideanSpace.single p (1 : ℝ))‖
        ≤ ‖fderiv ℝ (fderiv ℝ u) x (EuclideanSpace.single q (1 : ℝ))‖ *
            ‖(EuclideanSpace.single p (1 : ℝ) : EuclideanSpace ℝ (Fin n))‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖fderiv ℝ (fderiv ℝ u) x‖ * ‖(EuclideanSpace.single q (1 : ℝ) : EuclideanSpace ℝ (Fin n))‖) * 1 := by
          rw [hone p]
          exact mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) zero_le_one
      _ ≤ b := by
          rw [hone q, mul_one, mul_one]; exact hb x
  have hXi := integrable_coord P hX
  have hRi := integrable_coord P hR
  have hfcont : ∀ i : Fin n, Continuous (fun y => fderiv ℝ u y (EuclideanSpace.single i (1 : ℝ))) :=
    fun i => hfc.clm_apply continuous_const
  have hΦXi : Integrable (fun w => Φ (X w)) P := int_comp_bdd P hXm Φ hΦc K hΦK
  have hAi : Integrable (fun w => ∑ p, ∑ q, C p q * fderiv ℝ (fderiv ℝ u) (X w)
      (EuclideanSpace.single q (1 : ℝ)) (EuclideanSpace.single p (1 : ℝ))) P :=
    integrable_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ =>
      (int_comp_bdd P hXm _ (hHc p q) b (hHb p q)).const_mul (C p q)
  have hBi : ∀ i : Fin n, Integrable (fun w => X w i *
      fderiv ℝ u (X w) (EuclideanSpace.single i (1 : ℝ))) P := fun i =>
    int_mul_comp_bdd P hXm (hXi i) _ (hfcont i) a (hfi_b0 i)
  have hI2i : ∀ i : Fin n, Integrable (fun w => R w i *
      fderiv ℝ u (X w) (EuclideanSpace.single i (1 : ℝ))) P := fun i =>
    int_mul_comp_bdd P hXm (hRi i) _ (hfcont i) a (hfi_b0 i)
  have hτi : ∀ p q : Fin n, Integrable (fun w => T w p q * fderiv ℝ (fderiv ℝ u) (X w)
      (EuclideanSpace.single q (1 : ℝ)) (EuclideanSpace.single p (1 : ℝ))) P := fun p q =>
    int_mul_comp_bdd P hXm (integrable_entry P hTm hT p q) _ (hHc p q) b (hHb p q)
  have hpt : ∀ w, Φ (X w) - ∫ w', Φ (G w') ∂P =
      (∑ p, ∑ q, C p q * fderiv ℝ (fderiv ℝ u) (X w)
        (EuclideanSpace.single q (1 : ℝ)) (EuclideanSpace.single p (1 : ℝ))) -
      ∑ i, X w i * fderiv ℝ u (X w) (EuclideanSpace.single i (1 : ℝ)) := by
    intro w
    have h1 := hseq (X w)
    rw [cc_eq P G C hC (gauss_sq_integrable P G hG hGauss) u (X w)] at h1
    have h2 : fderiv ℝ u (X w) (X w) =
        ∑ i, X w i * fderiv ℝ u (X w) (EuclideanSpace.single i (1 : ℝ)) := by
      exact clm_expand (fderiv ℝ u (X w)) (X w)
    rw [h2] at h1
    linarith
  have E1 : ∫ w, Φ (X w) ∂P - ∫ w, Φ (G w) ∂P =
      ∫ w, (∑ p, ∑ q, C p q * fderiv ℝ (fderiv ℝ u) (X w)
        (EuclideanSpace.single q (1 : ℝ)) (EuclideanSpace.single p (1 : ℝ))) ∂P -
      ∫ w, ∑ i, X w i * fderiv ℝ u (X w) (EuclideanSpace.single i (1 : ℝ)) ∂P := by
    have h := integral_congr_ae (μ := P) (Eventually.of_forall hpt)
    rw [integral_sub hΦXi (integrable_const _),
      integral_sub hAi (integrable_finsetSum _ fun i _ => hBi i)] at h
    simpa using h
  have E2 : ∫ w, ∑ i, X w i * fderiv ℝ u (X w) (EuclideanSpace.single i (1 : ℝ)) ∂P =
      ∫ w, ∑ i, R w i * fderiv ℝ u (X w) (EuclideanSpace.single i (1 : ℝ)) ∂P +
      ∫ w, ∑ p, ∑ q, T w p q * fderiv ℝ (fderiv ℝ u) (X w)
        (EuclideanSpace.single q (1 : ℝ)) (EuclideanSpace.single p (1 : ℝ)) ∂P := by
    rw [integral_finsetSum _ (fun i _ => hBi i), integral_finsetSum _ (fun i _ => hI2i i),
      integral_finsetSum _ (fun p _ => integrable_finsetSum _ fun q _ => hτi p q)]
    have : ∀ p, ∫ w, ∑ q, T w p q * fderiv ℝ (fderiv ℝ u) (X w)
        (EuclideanSpace.single q (1 : ℝ)) (EuclideanSpace.single p (1 : ℝ)) ∂P =
        ∑ q, ∫ w, T w p q * fderiv ℝ (fderiv ℝ u) (X w)
        (EuclideanSpace.single q (1 : ℝ)) (EuclideanSpace.single p (1 : ℝ)) ∂P :=
      fun p => integral_finsetSum _ (fun q _ => hτi p q)
    simp_rw [this]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => hidi i
  have hτAi : Integrable (fun w => (∑ p, ∑ q, T w p q * fderiv ℝ (fderiv ℝ u) (X w)
        (EuclideanSpace.single q (1 : ℝ)) (EuclideanSpace.single p (1 : ℝ))) -
      ∑ p, ∑ q, C p q * fderiv ℝ (fderiv ℝ u) (X w)
        (EuclideanSpace.single q (1 : ℝ)) (EuclideanSpace.single p (1 : ℝ))) P :=
    (integrable_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ => hτi p q).sub hAi
  have hI2tot : Integrable (fun w => ∑ i, R w i *
      fderiv ℝ u (X w) (EuclideanSpace.single i (1 : ℝ))) P :=
    integrable_finsetSum _ fun i _ => hI2i i
  have hmain : ∫ w, Φ (X w) ∂P - ∫ w, Φ (G w) ∂P =
      -(∫ w, ((∑ p, ∑ q, T w p q * fderiv ℝ (fderiv ℝ u) (X w)
        (EuclideanSpace.single q (1 : ℝ)) (EuclideanSpace.single p (1 : ℝ))) -
      ∑ p, ∑ q, C p q * fderiv ℝ (fderiv ℝ u) (X w)
        (EuclideanSpace.single q (1 : ℝ)) (EuclideanSpace.single p (1 : ℝ))) ∂P) -
      ∫ w, ∑ i, R w i * fderiv ℝ u (X w) (EuclideanSpace.single i (1 : ℝ)) ∂P := by
    rw [E1, E2, integral_sub (integrable_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ => hτi p q) hAi]
    ring
  -- pointwise bounds
  have hτA : ∀ w, ‖(∑ p, ∑ q, T w p q * fderiv ℝ (fderiv ℝ u) (X w)
        (EuclideanSpace.single q (1 : ℝ)) (EuclideanSpace.single p (1 : ℝ))) -
      ∑ p, ∑ q, C p q * fderiv ℝ (fderiv ℝ u) (X w)
        (EuclideanSpace.single q (1 : ℝ)) (EuclideanSpace.single p (1 : ℝ))‖ ≤
      b * traceNormMatrix (T w - C) := by
    intro w
    have e : (∑ p, ∑ q, T w p q * fderiv ℝ (fderiv ℝ u) (X w)
        (EuclideanSpace.single q (1 : ℝ)) (EuclideanSpace.single p (1 : ℝ))) -
      ∑ p, ∑ q, C p q * fderiv ℝ (fderiv ℝ u) (X w)
        (EuclideanSpace.single q (1 : ℝ)) (EuclideanSpace.single p (1 : ℝ)) =
        ∑ p, ∑ q, fderiv ℝ (fderiv ℝ u) (X w) (EuclideanSpace.single q (1 : ℝ))
          (EuclideanSpace.single p (1 : ℝ)) * (T w - C) p q := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_
      simp only [Matrix.sub_apply]; ring
    rw [e, Real.norm_eq_abs]
    exact trace_dual_ell (fderiv ℝ (fderiv ℝ u) (X w)) b (hb _) (T w - C)
  have hI2b : ∀ w, ‖∑ i, R w i * fderiv ℝ u (X w) (EuclideanSpace.single i (1 : ℝ))‖ ≤ a * ‖R w‖ := by
    intro w
    have e : ∑ i, R w i * fderiv ℝ u (X w) (EuclideanSpace.single i (1 : ℝ)) =
        fderiv ℝ u (X w) (R w) := by
      exact (clm_expand (fderiv ℝ u (X w)) (R w)).symm
    rw [e]
    calc ‖fderiv ℝ u (X w) (R w)‖ ≤ ‖fderiv ℝ u (X w)‖ * ‖R w‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ a * ‖R w‖ := mul_le_mul_of_nonneg_right (ha _) (norm_nonneg _)
  have htn := tn_integrable P T hTm hT C
  have hb1 : ‖∫ w, ((∑ p, ∑ q, T w p q * fderiv ℝ (fderiv ℝ u) (X w)
        (EuclideanSpace.single q (1 : ℝ)) (EuclideanSpace.single p (1 : ℝ))) -
      ∑ p, ∑ q, C p q * fderiv ℝ (fderiv ℝ u) (X w)
        (EuclideanSpace.single q (1 : ℝ)) (EuclideanSpace.single p (1 : ℝ))) ∂P‖ ≤
      b * ∫ w, traceNormMatrix (T w - C) ∂P := by
    have := norm_integral_le_of_norm_le (htn.const_mul b) (Eventually.of_forall hτA)
    rwa [integral_const_mul] at this
  have hb2 : ‖∫ w, ∑ i, R w i * fderiv ℝ u (X w) (EuclideanSpace.single i (1 : ℝ)) ∂P‖ ≤
      a * ∫ w, ‖R w‖ ∂P := by
    have := norm_integral_le_of_norm_le (hR.norm.const_mul a) (Eventually.of_forall hI2b)
    rwa [integral_const_mul] at this
  rw [hmain, ← Real.norm_eq_abs]
  calc ‖-(∫ w, _ ∂P) - ∫ w, ∑ i, R w i * fderiv ℝ u (X w) (EuclideanSpace.single i (1 : ℝ)) ∂P‖
      ≤ ‖-(∫ w, _ ∂P)‖ + ‖∫ w, ∑ i, R w i * fderiv ℝ u (X w) (EuclideanSpace.single i (1 : ℝ)) ∂P‖ :=
        norm_sub_le _ _
    _ ≤ _ := by rw [norm_neg]; linarith

end Core

end HRS.Whole.Stein
