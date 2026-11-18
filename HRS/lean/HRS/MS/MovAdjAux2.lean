import HRS.MS.MovAdjAux1
import HRS.MS.Mov63CAux2
import HRS.MH.DualityRdC1b
import HRS.MH.DualityRdB1Aux

/-!
# S6.7 (packet P1, part 1): integration by parts for decaying functions, antisymmetry of the cancellation convolution

Namespace `HRS.MS.MovAdj`, helpers `s67_`.  Infrastructure for the supplement row `S:W:lem:r2mov-global-adjoint`; not a manuscript row.

* `s67_ibp_dir`: `∫ f ∂_v g = -∫ ∂_v f g` for `f ∈ C¹` bounded with bounded `∂_v f`, `g ∈ C¹` integrable with integrable `∂_v g`.
* `s67_ibp_div`: `∫ div Y ψ = -∫ ⟨Y, ∇ψ⟩` for such `ψ` and a `C¹` field `Y` with integrable components and divergence terms.
* `s67_lap_*`: the Laplacian of a `C_b²` function is continuous and bounded.
* `s67_antisym`: `∫ f (∇g ⋆ h)_j = -∫ h (∇g ⋆ f)_j` for `f, h` of the `RgW` class (from `dc1b_antisym`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovAdj

open HRS HRS.Whole HRS.MH.DualityRd HRS.MS.Mov63

variable {d : ℕ}

/-! ### Integration by parts -/

theorem s67_ibp_dir {f g : Euc d → ℝ} (v : Euc d) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    {Bf Bf' : ℝ} (hfb : ∀ x, |f x| ≤ Bf) (hfd : ∀ x, |fderiv ℝ f x v| ≤ Bf')
    (hgi : Integrable g) (hgd : Integrable (fun x => fderiv ℝ g x v)) :
    ∫ x, f x * fderiv ℝ g x v = -∫ x, fderiv ℝ f x v * g x := by
  have hfc : Continuous f := hf.continuous
  have hdf : Continuous fun x => fderiv ℝ f x v :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have h1 : Integrable (fun x => fderiv ℝ f x v * g x) :=
    hgi.bdd_mul (f := fun x => fderiv ℝ f x v) (c := Bf') hdf.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hfd x)
  have h2 : Integrable (fun x => f x * fderiv ℝ g x v) :=
    hgd.bdd_mul (f := f) (c := Bf) hfc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hfb x)
  have h3 : Integrable (fun x => f x * g x) :=
    hgi.bdd_mul (f := f) (c := Bf) hfc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hfb x)
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure (Euc d))) h1 h2 h3
    (fun x _ => hf.differentiable one_ne_zero x) (fun x _ => hg.differentiable one_ne_zero x)

theorem s67_ibp_div {Y : Euc d → Euc d} {ψ : Euc d → ℝ} (hY : ContDiff ℝ 1 Y) (hψ : ContDiff ℝ 1 ψ)
    {B B' : ℝ} (hψb : ∀ x, |ψ x| ≤ B) (hψd : ∀ x, ‖fderiv ℝ ψ x‖ ≤ B')
    (hYi : ∀ i : Fin d, Integrable (fun x => Y x i))
    (hdY : ∀ i : Fin d, Integrable (fun x => fderiv ℝ Y x (EuclideanSpace.single i 1) i)) :
    ∫ x, movDiv Y x * ψ x = -∫ x, inner ℝ (Y x) (gradient ψ x) := by
  have hYd : Differentiable ℝ Y := hY.differentiable (by norm_num)
  have hYc : ∀ i : Fin d, ContDiff ℝ 1 (fun y => Y y i) := fun i => contDiff_euclidean.1 hY i
  have hterm : ∀ i : Fin d, ∫ x, (fderiv ℝ Y x (EuclideanSpace.single i 1)) i * ψ x =
      -∫ x, (Y x i) * (gradient ψ x) i := by
    intro i
    set e : Euc d := EuclideanSpace.single i 1 with he
    have h1 : ∀ x, (fderiv ℝ Y x e) i = fderiv ℝ (fun y => Y y i) x e :=
      fun x => mnc_comp_fderiv_apply Y hYd x e i
    have hnorm : ‖e‖ = 1 := by simp [he]
    have key := s67_ibp_dir (f := ψ) (g := fun y => Y y i) e hψ (hYc i) hψb
      (Bf' := B') (fun x => by
        have := (fderiv ℝ ψ x).le_opNorm e
        rw [hnorm, mul_one] at this
        exact (Real.norm_eq_abs _ ▸ this).trans (hψd x))
      (hYi i) ((hdY i).congr (Filter.Eventually.of_forall fun x => h1 x))
    simp_rw [h1, mnc_gradient_apply]
    calc ∫ x, fderiv ℝ (fun y => Y y i) x e * ψ x = ∫ x, ψ x * fderiv ℝ (fun y => Y y i) x e :=
          integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
      _ = -∫ x, fderiv ℝ ψ x e * Y x i := key
      _ = -∫ x, Y x i * fderiv ℝ ψ x e := by
          congr 1
          exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
  have hI1 : ∀ i : Fin d, Integrable (fun x => fderiv ℝ (fun y => Y y i) x (EuclideanSpace.single i 1) * ψ x) := by
    intro i
    have h1 : ∀ x, fderiv ℝ (fun y => Y y i) x (EuclideanSpace.single i 1) =
        (fderiv ℝ Y x (EuclideanSpace.single i 1)) i := fun x => (mnc_comp_fderiv_apply Y hYd x _ i).symm
    simp_rw [h1]
    exact (hdY i).mul_bdd (g := ψ) (c := B) hψ.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hψb x)
  have hI2 : ∀ i : Fin d, Integrable (fun x => fderiv ℝ ψ x (EuclideanSpace.single i 1) * Y x i) := by
    intro i
    have hnorm : ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖ = 1 := by simp
    exact (hYi i).bdd_mul (f := fun x => fderiv ℝ ψ x (EuclideanSpace.single i 1)) (c := B')
      (((hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => by
        have := (fderiv ℝ ψ x).le_opNorm (EuclideanSpace.single i (1 : ℝ) : Euc d)
        rw [hnorm, mul_one] at this
        exact this.trans (hψd x))
  have hlhs : ∀ x, movDiv Y x * ψ x =
      ∑ i, fderiv ℝ (fun y => Y y i) x (EuclideanSpace.single i 1) * ψ x := by
    intro x
    unfold movDiv
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mnc_comp_fderiv_apply Y hYd x _ i]
  have hrhs : ∀ x, inner ℝ (Y x) (gradient ψ x) =
      ∑ i, fderiv ℝ ψ x (EuclideanSpace.single i 1) * Y x i := by
    intro x
    rw [mnc_inner_eq_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mnc_gradient_apply, mul_comm]
  simp_rw [hlhs, hrhs]
  rw [integral_finsetSum _ (fun i _ => hI1 i), integral_finsetSum _ (fun i _ => hI2 i),
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := hterm i
  have h1 : ∀ x, fderiv ℝ (fun y => Y y i) x (EuclideanSpace.single i 1) =
      (fderiv ℝ Y x (EuclideanSpace.single i 1)) i := fun x => (mnc_comp_fderiv_apply Y hYd x _ i).symm
  simp_rw [h1]
  rw [this]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show (Y x) i * (gradient ψ x) i = _
  rw [mnc_gradient_apply, mul_comm]

/-! ### The Laplacian of a `C_b²` function -/

theorem s67_lap_cont {u : Euc d → ℝ} (hu : ContDiff ℝ 2 u) : Continuous (Laplacian.laplacian u) :=
  db1_laplacian_continuous hu

theorem s67_lap_bound {u : Euc d → ℝ} {B : ℝ} (hB : ∀ x, ‖iteratedFDeriv ℝ 2 u x‖ ≤ B) (x : Euc d) :
    |Laplacian.laplacian u x| ≤ d * B := by
  rw [mnb_lap_formula]
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB x)
  calc |∑ i, iteratedFDeriv ℝ 2 u x ![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)]|
      ≤ ∑ i : Fin d, |iteratedFDeriv ℝ 2 u x ![EuclideanSpace.single i (1 : ℝ),
        EuclideanSpace.single i (1 : ℝ)]| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin d, B := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h1 := (iteratedFDeriv ℝ 2 u x).le_opNorm ![EuclideanSpace.single i (1 : ℝ),
          EuclideanSpace.single i (1 : ℝ)]
        have h2 : ∏ k : Fin 2, ‖(![EuclideanSpace.single i (1 : ℝ), EuclideanSpace.single i (1 : ℝ)] :
            Fin 2 → Euc d) k‖ = 1 := by
          simp [Fin.prod_univ_two]
        rw [h2, mul_one] at h1
        exact (Real.norm_eq_abs _ ▸ h1).trans (hB x)
    _ = d * B := by simp

/-! ### Antisymmetry of the cancellation convolution -/

/-- `∫ f (∇g ⋆ h)_j = -∫ h (∇g ⋆ f)_j` for `f, h` in the `RgW` class. -/
theorem s67_antisym {s : ℝ} (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (j : Fin d) {f h : Euc d → ℝ}
    {cf ch : ℝ} (hcf : 0 ≤ cf) (hch : 0 ≤ ch)
    (hf : HRS.MP.RdGen.RgW (fun y : Euc d => (1 + ‖y‖) ^ (-((d : ℝ) + 1))) 1 cf f)
    (hh : HRS.MP.RdGen.RgW (fun y : Euc d => (1 + ‖y‖) ^ (-((d : ℝ) + 1))) 1 ch h) :
    ∫ x, f x * (convGradConvW (rieszKernelGrad d s) h x) j =
      -∫ x, h x * (convGradConvW (rieszKernelGrad d s) f x) j := by
  have hκ : HRS.MP.RdGen.RgKer d s (movtr_sigma s) (fun z => rieszKernelGrad d s z j) :=
    HRS.MP.RdGen.rgKerComp_ok hs0 j
  have hκodd : ∀ z : Euc d, rieszKernelGrad d s (-z) j = -(rieszKernelGrad d s z j) := by
    intro z
    rw [HRS.Whole.Q09B.q09b_rkg_neg]
    simp
  have e1 : ∀ x, (convGradConvW (rieszKernelGrad d s) h x) j =
      ∫ z, rieszKernelGrad d s z j * movtr_R h x z := fun x => dc1a_force_eq hd hs0 hsd hch hh x j
  have e2 : ∀ x, (convGradConvW (rieszKernelGrad d s) f x) j =
      ∫ z, rieszKernelGrad d s z j * movtr_R f x z := fun x => dc1a_force_eq hd hs0 hsd hcf hf x j
  simp_rw [e1, e2]
  exact dc1b_antisym hd hs0 hsd hκ hκodd hcf hch hf hh

end HRS.MS.MovAdj
