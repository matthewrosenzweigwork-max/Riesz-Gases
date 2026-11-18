import HRS.MS.R2SeAux34

/-!
# S9.9 `r2_static_edgeworth`, packet 35: Fubini for the potential pairing and integration by parts

Worker S99, namespace `S99`.

* `s99_swap`: `∫ r (g * D) = ∫ D (g * r)` for Gaussian-bounded continuous `r, D` (`g` the even Riesz kernel);
* `s99_sum_basis`: `∑_b w_b L(e_b) = L w`;
* `s99_ibp_div`: `∫ D_r H = - ∫ r DH[v]` (integration by parts for `div (r v)` against a bounded `C¹` function `H`).
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S99

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

theorem s99_sum_basis (L : Euc d →L[ℝ] ℝ) (w : Euc d) :
    ∑ b : Fin d, w b * L (EuclideanSpace.single b (1 : ℝ)) = L w := by
  have h := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr w
  simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] at h
  conv_rhs => rw [← h]
  simp [map_sum, map_smul]

section PotE

variable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β C c BU : ℝ} (hT : ThermalData d s a β C c BU)

include hd hs0 hsd hT

theorem s99_swap {r D : Euc d → ℝ} (hr : Continuous r) {K1 : ℝ} (hK1 : 0 ≤ K1)
    (hrb : ∀ y, |r y| ≤ K1 * Real.exp (-c * ‖y‖ ^ 2)) (hD : Continuous D) {K2 : ℝ} (hK2 : 0 ≤ K2)
    (hDb : ∀ y, |D y| ≤ K2 * Real.exp (-c * ‖y‖ ^ 2)) :
    (∫ x, r x * ∫ y, rieszKernel d s (x - y) * D y = ∫ y, D y * ∫ x, rieszKernel d s (y - x) * r x) ∧
      Integrable (fun x => r x * ∫ y, rieszKernel d s (x - y) * D y) := by
  have hgm : Measurable (rieszKernel d s) := by
    rw [← movtr_gEps_zero d s]; exact movtr_gEps_measurable s 0
  have hkB : ∀ z : Euc d, z ≠ 0 → |rieszKernel d s z| ≤ 2 * ‖z‖ ^ (-movtr_sp s) + ‖z‖ + 1 := fun z hz => by
    have := movtr_gEps_abs_le (d := d) hs0 (ε := 0) le_rfl zero_le_one hz
    rw [movtr_gEps_zero d s] at this
    simpa using this
  set Fxy : Euc d × Euc d → ℝ := fun p => r p.1 * (rieszKernel d s (p.1 - p.2) * D p.2) with hFxy
  have hM : Integrable (fun z : Euc d => (2 * ‖z‖ ^ (-movtr_sp s) + ‖z‖ + 1) * Real.exp (-(c / 4) * ‖z‖ ^ 2)) :=
    movtr_majorant_integrable (by omega) hs0 hsd (c := c / 4) (by have := hT.hc; positivity)
  have hw : Integrable (fun y : Euc d => Real.exp (-(c / 2) * ‖y‖ ^ 2)) := by
    have := HRS.MP.SelfSimP4Impl.p4g_integrable_gauss d (b := c / 2) (by have := hT.hc; positivity)
    simpa [neg_mul] using this
  have hconv := Integrable.convolution_integrand (μ := (volume : Measure (Euc d))) (ν := volume)
    (ContinuousLinearMap.mul ℝ ℝ) hw hM
  have hFint : Integrable Fxy ((volume : Measure (Euc d)).prod volume) := by
    refine Integrable.mono' (hconv.const_mul (K1 * K2)) ?_ ?_
    · exact (hr.comp continuous_fst).aestronglyMeasurable.mul
        ((hgm.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable.mul
          (hD.comp continuous_snd).aestronglyMeasurable)
    · have hne : ∀ᵐ p : Euc d × Euc d ∂((volume : Measure (Euc d)).prod volume), p.1 - p.2 ≠ 0 := by
        have h1 : ∀ᵐ z : Euc d ∂(volume : Measure (Euc d)), z ≠ 0 := movtr_ae_ne_zero (d := d) (by omega)
        exact (MeasureTheory.quasiMeasurePreserving_sub_of_right_invariant (volume : Measure (Euc d))
          (volume : Measure (Euc d))).ae h1
      filter_upwards [hne] with p hp
      simp only [hFxy, ContinuousLinearMap.mul_apply']
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      have e1 := hrb p.1
      have e2 := hDb p.2
      have e3 := hkB _ hp
      have hexp1 := Real.exp_pos (-c * ‖p.1‖ ^ 2)
      have hexp2 := Real.exp_pos (-c * ‖p.2‖ ^ 2)
      have hexp : Real.exp (-c * ‖p.1‖ ^ 2) * Real.exp (-c * ‖p.2‖ ^ 2) ≤
          Real.exp (-(c / 4) * ‖p.1 - p.2‖ ^ 2) * Real.exp (-(c / 2) * ‖p.2‖ ^ 2) := by
        rw [← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.2
        have h1 : ‖p.1 - p.2‖ ^ 2 ≤ 2 * ‖p.1‖ ^ 2 + 2 * ‖p.2‖ ^ 2 := by
          have h2 : ‖p.1 - p.2‖ ^ 2 ≤ (‖p.1‖ + ‖p.2‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le p.1 p.2) 2
          nlinarith [sq_nonneg (‖p.1‖ - ‖p.2‖)]
        have hc := hT.hc
        nlinarith [sq_nonneg ‖p.1‖, sq_nonneg ‖p.2‖]
      have hB0 : 0 ≤ 2 * ‖p.1 - p.2‖ ^ (-movtr_sp s) + ‖p.1 - p.2‖ + 1 := by
        have := Real.rpow_nonneg (norm_nonneg (p.1 - p.2)) (-movtr_sp s)
        have := norm_nonneg (p.1 - p.2)
        linarith
      calc |r p.1| * (|rieszKernel d s (p.1 - p.2)| * |D p.2|)
          ≤ (K1 * Real.exp (-c * ‖p.1‖ ^ 2)) * ((2 * ‖p.1 - p.2‖ ^ (-movtr_sp s) + ‖p.1 - p.2‖ + 1) *
              (K2 * Real.exp (-c * ‖p.2‖ ^ 2))) :=
            mul_le_mul e1 (mul_le_mul e3 e2 (abs_nonneg _) hB0) (by positivity) (by positivity)
        _ = (K1 * K2) * ((2 * ‖p.1 - p.2‖ ^ (-movtr_sp s) + ‖p.1 - p.2‖ + 1) *
              (Real.exp (-c * ‖p.1‖ ^ 2) * Real.exp (-c * ‖p.2‖ ^ 2))) := by ring
        _ ≤ (K1 * K2) * ((2 * ‖p.1 - p.2‖ ^ (-movtr_sp s) + ‖p.1 - p.2‖ + 1) *
              (Real.exp (-(c / 4) * ‖p.1 - p.2‖ ^ 2) * Real.exp (-(c / 2) * ‖p.2‖ ^ 2))) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp hB0) (by positivity)
        _ = K1 * K2 * (Real.exp (-(c / 2) * ‖p.2‖ ^ 2) * ((2 * ‖p.1 - p.2‖ ^ (-movtr_sp s) + ‖p.1 - p.2‖ + 1) *
              Real.exp (-(c / 4) * ‖p.1 - p.2‖ ^ 2))) := by ring
  have hswap := integral_integral_swap (f := fun x y => Fxy (x, y)) hFint
  have hg_even : ∀ x y : Euc d, rieszKernel d s (y - x) = rieszKernel d s (x - y) := fun x y => by
    unfold rieszKernel
    rw [← norm_neg (y - x), neg_sub]
  have e1 : ∀ x, r x * ∫ y, rieszKernel d s (x - y) * D y = ∫ y, Fxy (x, y) := fun x => by
    rw [← integral_const_mul]
  have e2 : ∀ y, D y * ∫ x, rieszKernel d s (y - x) * r x = ∫ x, Fxy (x, y) := fun y => by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hFxy, hg_even x y]; ring
  have hint_x : Integrable (fun x => r x * ∫ y, rieszKernel d s (x - y) * D y) :=
    (hFint.integral_prod_left).congr (Filter.Eventually.of_forall fun x => (e1 x).symm)
  refine ⟨?_, hint_x⟩
  simp_rw [e1, e2]
  exact hswap

theorem s99_ibp_div {r : Euc d → ℝ} (hr1 : ContDiff ℝ 1 r) {K : ℝ} (hK : 0 ≤ K)
    (hr0 : ∀ y, |r y| ≤ K * Real.exp (-c * ‖y‖ ^ 2))
    (hr1' : ∀ y, ‖fderiv ℝ r y‖ ≤ K * Real.exp (-c * ‖y‖ ^ 2)) {v : Euc d → Euc d}
    (hv : ContDiff ℝ 1 v) {B1 B2 : ℝ} (hB1 : ∀ x, ‖v x‖ ≤ B1) (hB2 : ∀ x, ‖fderiv ℝ v x‖ ≤ B2)
    {H : Euc d → ℝ} (hH : ContDiff ℝ 1 H) {MH DH : ℝ} (hHb : ∀ y, |H y| ≤ MH)
    (hHd : ∀ y, ‖fderiv ℝ H y‖ ≤ DH) :
    ∫ y, Dd r v y * H y = -∫ y, r y * fderiv ℝ H y (v y) := by
  have hB10 : 0 ≤ B1 := (norm_nonneg _).trans (hB1 0)
  have hB20 : 0 ≤ B2 := (norm_nonneg _).trans (hB2 0)
  have hMH0 : 0 ≤ MH := (abs_nonneg _).trans (hHb 0)
  have hDH0 : 0 ≤ DH := (norm_nonneg _).trans (hHd 0)
  have hrd : Differentiable ℝ r := hr1.differentiable one_ne_zero
  have hvd : Differentiable ℝ v := hv.differentiable one_ne_zero
  have hHd' : Differentiable ℝ H := hH.differentiable one_ne_zero
  have hexp := fun y : Euc d => (Real.exp_pos (-c * ‖y‖ ^ 2)).le
  have hrc : Continuous (fderiv ℝ r) := hr1.continuous_fderiv one_ne_zero
  have hvc : Continuous (fderiv ℝ v) := hv.continuous_fderiv one_ne_zero
  have hHc : Continuous (fderiv ℝ H) := hH.continuous_fderiv one_ne_zero
  set e : Fin d → Euc d := fun b => EuclideanSpace.single b (1 : ℝ) with he
  have he1 : ∀ b, ‖e b‖ ≤ 1 := fun b => movtr_norm_single b
  -- the coordinate fields
  set Fb : Fin d → Euc d → ℝ := fun b y => r y * v y b with hFb
  set Ph : Fin d → Euc d → ℝ := fun b y => r y * (fderiv ℝ v y (e b)) b + v y b * fderiv ℝ r y (e b) with hPh
  have hFd : ∀ b y, HasFDerivAt (Fb b) (r y • ((EuclideanSpace.proj b : Euc d →L[ℝ] ℝ).comp (fderiv ℝ v y)) +
      v y b • fderiv ℝ r y) y := by
    intro b y
    have h1 : HasFDerivAt (fun y => v y b) ((EuclideanSpace.proj b : Euc d →L[ℝ] ℝ).comp (fderiv ℝ v y)) y :=
      (EuclideanSpace.proj b : Euc d →L[ℝ] ℝ).hasFDerivAt.comp y (hvd y).hasFDerivAt
    exact (hrd y).hasFDerivAt.mul h1 |>.congr_fderiv (by ext z; simp [add_comm])
  have hFd' : ∀ b y, fderiv ℝ (Fb b) y (e b) = Ph b y := by
    intro b y
    rw [(hFd b y).fderiv]
    simp [hPh, add_comm]
  have hPhc : ∀ b, Continuous (Ph b) := fun b => by
    simp only [hPh]
    refine (hr1.continuous.mul ?_).add ((( EuclideanSpace.proj b : Euc d →L[ℝ] ℝ).continuous.comp hv.continuous).mul
      (hrc.clm_apply continuous_const))
    exact (EuclideanSpace.proj b : Euc d →L[ℝ] ℝ).continuous.comp (hvc.clm_apply continuous_const)
  have hFbc : ∀ b, Continuous (Fb b) := fun b =>
    hr1.continuous.mul ((EuclideanSpace.proj b : Euc d →L[ℝ] ℝ).continuous.comp hv.continuous)
  have hFbb : ∀ b y, |Fb b y| ≤ K * B1 * Real.exp (-c * ‖y‖ ^ 2) := fun b y => by
    simp only [hFb]; rw [abs_mul]
    calc |r y| * |v y b| ≤ (K * Real.exp (-c * ‖y‖ ^ 2)) * B1 :=
          mul_le_mul (hr0 y) ((s45_abs_coord_le _ _).trans (hB1 y)) (abs_nonneg _) (by have := hexp y; positivity)
      _ = K * B1 * Real.exp (-c * ‖y‖ ^ 2) := by ring
  have hPhb : ∀ b y, |Ph b y| ≤ K * (B2 + B1) * Real.exp (-c * ‖y‖ ^ 2) := fun b y => by
    simp only [hPh]
    have e1 : |r y * (fderiv ℝ v y (e b)) b| ≤ (K * Real.exp (-c * ‖y‖ ^ 2)) * B2 := by
      rw [abs_mul]
      refine mul_le_mul (hr0 y) ?_ (abs_nonneg _) (by have := hexp y; positivity)
      refine (s45_abs_coord_le _ _).trans ?_
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      calc ‖fderiv ℝ v y‖ * ‖e b‖ ≤ B2 * 1 := mul_le_mul (hB2 y) (he1 b) (norm_nonneg _) hB20
        _ = B2 := mul_one _
    have e2 : |v y b * fderiv ℝ r y (e b)| ≤ B1 * (K * Real.exp (-c * ‖y‖ ^ 2)) := by
      rw [abs_mul]
      refine mul_le_mul ((s45_abs_coord_le _ _).trans (hB1 y)) ?_ (abs_nonneg _) hB10
      rw [← Real.norm_eq_abs]
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      calc ‖fderiv ℝ r y‖ * ‖e b‖ ≤ (K * Real.exp (-c * ‖y‖ ^ 2)) * 1 :=
            mul_le_mul (hr1' y) (he1 b) (norm_nonneg _) (by have := hexp y; positivity)
        _ = _ := mul_one _
    refine (abs_add_le _ _).trans ((add_le_add e1 e2).trans (le_of_eq ?_))
    ring
  have hint : ∀ b, Integrable (fun y => Ph b y * H y) := fun b =>
    s99_gauss_int hd hs0 hsd hT ((hPhc b).mul hH.continuous) (K := K * (B2 + B1) * MH) (fun y => by
      rw [abs_mul]
      calc |Ph b y| * |H y| ≤ (K * (B2 + B1) * Real.exp (-c * ‖y‖ ^ 2)) * MH :=
            mul_le_mul (hPhb b y) (hHb y) (abs_nonneg _) (by have := hexp y; positivity)
        _ = _ := by ring)
  -- integration by parts in each coordinate
  have hcoord : ∀ b, ∫ y, Fb b y * fderiv ℝ H y (e b) = -∫ y, Ph b y * H y := by
    intro b
    have hI1 : Integrable (fun y => fderiv ℝ (Fb b) y (e b) * H y) :=
      (hint b).congr (Filter.Eventually.of_forall fun y => by simp only [hFd' b y])
    have hI2 : Integrable (fun y => Fb b y * fderiv ℝ H y (e b)) := by
      refine s99_gauss_int hd hs0 hsd hT ((hFbc b).mul (hHc.clm_apply continuous_const)) (K := K * B1 * DH)
        (fun y => ?_)
      rw [abs_mul]
      have : |fderiv ℝ H y (e b)| ≤ DH := by
        rw [← Real.norm_eq_abs]
        refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
        calc ‖fderiv ℝ H y‖ * ‖e b‖ ≤ DH * 1 := mul_le_mul (hHd y) (he1 b) (norm_nonneg _) hDH0
          _ = DH := mul_one _
      calc |Fb b y| * |fderiv ℝ H y (e b)| ≤ (K * B1 * Real.exp (-c * ‖y‖ ^ 2)) * DH :=
            mul_le_mul (hFbb b y) this (abs_nonneg _) (by have := hexp y; positivity)
        _ = _ := by ring
    have hI3 : Integrable (fun y => Fb b y * H y) := by
      refine s99_gauss_int hd hs0 hsd hT ((hFbc b).mul hH.continuous) (K := K * B1 * MH) (fun y => ?_)
      rw [abs_mul]
      calc |Fb b y| * |H y| ≤ (K * B1 * Real.exp (-c * ‖y‖ ^ 2)) * MH :=
            mul_le_mul (hFbb b y) (hHb y) (abs_nonneg _) (by have := hexp y; positivity)
        _ = _ := by ring
    have := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure (Euc d)))
      (f := Fb b) (g := H) (v := e b) hI1 hI2 hI3 (fun x _ => ((hrd x).mul
        (((EuclideanSpace.proj b : Euc d →L[ℝ] ℝ).differentiableAt).comp x (hvd x)))) (fun x _ => hHd' x)
    rw [this]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hFd' b y]
  -- sum over coordinates
  have hDsum : ∀ y, Dd r v y = ∑ b, Ph b y := by
    intro y
    unfold Dd s45_div
    simp only [hPh, Finset.sum_add_distrib, ← Finset.mul_sum]
    have h1 : ∑ b : Fin d, v y b * fderiv ℝ r y (e b) = ⟪gradient r y, v y⟫ := by
      rw [s99_sum_basis (fderiv ℝ r y) (v y), real_inner_comm]
      exact (HRS.MS.PoisKolm.kl_inner_gradient r y (v y)).symm
    rw [h1]; ring
  have hint2 : ∀ b, Integrable (fun y => Fb b y * fderiv ℝ H y (e b)) := fun b => by
    refine s99_gauss_int hd hs0 hsd hT ((hFbc b).mul (hHc.clm_apply continuous_const)) (K := K * B1 * DH)
      (fun y => ?_)
    rw [abs_mul]
    have : |fderiv ℝ H y (e b)| ≤ DH := by
      rw [← Real.norm_eq_abs]
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      calc ‖fderiv ℝ H y‖ * ‖e b‖ ≤ DH * 1 := mul_le_mul (hHd y) (he1 b) (norm_nonneg _) hDH0
        _ = DH := mul_one _
    calc |Fb b y| * |fderiv ℝ H y (e b)| ≤ (K * B1 * Real.exp (-c * ‖y‖ ^ 2)) * DH :=
          mul_le_mul (hFbb b y) this (abs_nonneg _) (by have := hexp y; positivity)
      _ = _ := by ring
  have e1 : ∫ y, Dd r v y * H y = ∑ b, ∫ y, Ph b y * H y := by
    have : (fun y => Dd r v y * H y) = fun y => ∑ b, Ph b y * H y := funext fun y => by
      rw [hDsum y, Finset.sum_mul]
    rw [this, integral_finsetSum _ fun b _ => hint b]
  have e2 : ∫ y, r y * fderiv ℝ H y (v y) = ∑ b, ∫ y, Fb b y * fderiv ℝ H y (e b) := by
    have : (fun y => r y * fderiv ℝ H y (v y)) = fun y => ∑ b, Fb b y * fderiv ℝ H y (e b) := funext fun y => by
      simp only [hFb, mul_assoc, ← Finset.mul_sum]
      rw [s99_sum_basis (fderiv ℝ H y) (v y)]
    rw [this, integral_finsetSum _ fun b _ => hint2 b]
  rw [e1, e2, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun b _ => by have := hcoord b; linarith

end PotE

end S99

end
