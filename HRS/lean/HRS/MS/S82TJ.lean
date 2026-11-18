import HRS.MS.S82P2Grad3

/-!
# S8.2 (S82T): a measurable symmetric model of `pairJ`
`pairJ C mu Q x y` is built from `oneJ` (gradients and cancellation convolutions with junk values on the
diagonal).  For `x ≠ y` it equals the explicit jointly measurable kernel
`s82t_Jt C mu gt x y = T(x,y) + T(y,x)`, `T(x,y) = J1(x,y) - int J1(x',y) dmu(x')`, where `gt = s82p2_gt Q` is
the measurable gradient model and `J1(x,y) = - sum_j (convGradConvW G (w -> rho(w) (M^T gt(w,y))_j) x)_j`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82T
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82P2

/-- Explicit model of `oneJ C (fun w => Q w y) x` (`gt w y` models the gradient of `w -> Q w y`). -/
def s82t_J1 {d : ℕ} (C : WholeCoeff d) (gt : Euc d → Euc d → Euc d) (x y : Euc d) : ℝ :=
  -∑ j : Fin d, convGradConvW (rieszKernelGrad d C.s)
    (fun w => C.ρ 0 w * (Torus.matVec C.M.transpose (gt w y)) j) x j

def s82t_T {d : ℕ} (C : WholeCoeff d) (mu : Measure (Euc d)) (gt : Euc d → Euc d → Euc d)
    (x y : Euc d) : ℝ :=
  s82t_J1 C gt x y - ∫ x', s82t_J1 C gt x' y ∂mu

def s82t_Jt {d : ℕ} (C : WholeCoeff d) (mu : Measure (Euc d)) (gt : Euc d → Euc d → Euc d)
    (x y : Euc d) : ℝ :=
  s82t_T C mu gt x y + s82t_T C mu gt y x

lemma s82t_conv_congr {d : ℕ} (G : Euc d → Euc d) (φ ψ : Euc d → ℝ) (x : Euc d) (hx : φ x = ψ x)
    (hae : ∀ᵐ w ∂(volume : Measure (Euc d)), φ w = ψ w) :
    convGradConvW G φ x = convGradConvW G ψ x := by
  unfold convGradConvW
  refine integral_congr_ae ?_
  filter_upwards [hae] with w hw
  simp only [hw, hx]

lemma s82t_oneJ_eq_J1 {d : ℕ} (hd : 2 ≤ d) (C : WholeCoeff d) (Q : Euc d → Euc d → ℝ)
    (gt : Euc d → Euc d → Euc d)
    (hgt : ∀ x y : Euc d, x ≠ y → gradient (fun w => Q w y) x = gt x y) (x y : Euc d)
    (hxy : x ≠ y) : oneJ C (fun w => Q w y) x = s82t_J1 C gt x y := by
  haveI : Nontrivial (Euc d) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    simp; omega
  have hae : ∀ᵐ w ∂(volume : Measure (Euc d)), w ≠ y :=
    compl_mem_ae_iff.mpr (measure_singleton y)
  have key : ∀ j : Fin d, convGradConvW (rieszKernelGrad d C.s)
      (fun w => C.ρ 0 w * (Torus.matVec C.M.transpose (gradient (fun w => Q w y) w)) j) x =
      convGradConvW (rieszKernelGrad d C.s)
        (fun w => C.ρ 0 w * (Torus.matVec C.M.transpose (gt w y)) j) x := by
    intro j
    refine s82t_conv_congr _ _ _ x (by simp only [hgt x y hxy]) (hae.mono fun w hw => ?_)
    simp only [hgt w y hw]
  unfold oneJ generatorW s82t_J1
  simp only [key]
  ring

lemma s82t_J1_measurable {d : ℕ} (C : WholeCoeff d) (hρ : Measurable (C.ρ 0))
    {gt : Euc d → Euc d → Euc d} (hg : Measurable (Function.uncurry gt)) :
    Measurable (Function.uncurry (s82t_J1 C gt)) := by
  change Measurable (fun p : Euc d × Euc d => -∑ j : Fin d, convGradConvW (rieszKernelGrad d C.s)
    (fun w => C.ρ 0 w * (Torus.matVec C.M.transpose (gt w p.2)) j) p.1 j)
  refine Measurable.neg (Finset.measurable_sum _ fun j _ => ?_)
  have hG := HRS.Whole.movtr_rieszKernelGrad_measurable (d := d) C.s
  have hmv : Measurable (fun v : Euc d => (Torus.matVec C.M.transpose v) j) := by
    have : Continuous (fun v : Euc d => (Torus.matVec C.M.transpose v) j) :=
      (EuclideanSpace.proj j).continuous.comp
        (Matrix.toEuclideanLin C.M.transpose).continuous_of_finiteDimensional
    exact this.measurable
  -- phi (w, y) = rho w * (M^T gt w y)_j
  have hφ : Measurable (fun u : Euc d × Euc d => C.ρ 0 u.1 * (Torus.matVec C.M.transpose (gt u.1 u.2)) j) :=
    (hρ.comp measurable_fst).mul (hmv.comp hg)
  have hsub : Measurable (fun r : (Euc d × Euc d) × Euc d => r.1.1 - r.2) :=
    (measurable_fst.comp measurable_fst).sub measurable_snd
  have hF : Measurable (fun r : (Euc d × Euc d) × Euc d =>
      if ‖r.1.1 - r.2‖ ≤ 1 / 4 then
        (C.ρ 0 r.2 * (Torus.matVec C.M.transpose (gt r.2 r.1.2)) j -
          C.ρ 0 r.1.1 * (Torus.matVec C.M.transpose (gt r.1.1 r.1.2)) j) •
            rieszKernelGrad d C.s (r.1.1 - r.2)
      else (C.ρ 0 r.2 * (Torus.matVec C.M.transpose (gt r.2 r.1.2)) j) •
            rieszKernelGrad d C.s (r.1.1 - r.2)) := by
    have hm1 : Measurable (fun r : (Euc d × Euc d) × Euc d => (r.2, r.1.2)) :=
      measurable_snd.prodMk (measurable_snd.comp measurable_fst)
    have hm2 : Measurable (fun r : (Euc d × Euc d) × Euc d => (r.1.1, r.1.2)) :=
      (measurable_fst.comp measurable_fst).prodMk (measurable_snd.comp measurable_fst)
    have hA1 : Measurable (fun r : (Euc d × Euc d) × Euc d =>
        C.ρ 0 r.2 * (Torus.matVec C.M.transpose (gt r.2 r.1.2)) j) := hφ.comp hm1
    have hA2 : Measurable (fun r : (Euc d × Euc d) × Euc d =>
        C.ρ 0 r.1.1 * (Torus.matVec C.M.transpose (gt r.1.1 r.1.2)) j) := hφ.comp hm2
    have hGs : Measurable (fun r : (Euc d × Euc d) × Euc d => rieszKernelGrad d C.s (r.1.1 - r.2)) :=
      hG.comp hsub
    refine Measurable.ite (measurableSet_le (measurable_norm.comp hsub) measurable_const) ?_ ?_
    · exact (hA1.sub hA2).smul hGs
    · exact hA1.smul hGs
  have hI := (hF.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
  exact (EuclideanSpace.proj j).continuous.measurable.comp hI

lemma s82t_Jt_measurable {d : ℕ} (C : WholeCoeff d) (mu : Measure (Euc d)) [SFinite mu]
    (hρ : Measurable (C.ρ 0)) {gt : Euc d → Euc d → Euc d} (hg : Measurable (Function.uncurry gt)) :
    Measurable (Function.uncurry (s82t_Jt C mu gt)) := by
  have hJ : Measurable (fun p : Euc d × Euc d => s82t_J1 C gt p.1 p.2) :=
    s82t_J1_measurable C hρ hg
  have hm1 : Measurable (fun r : (Euc d × Euc d) × Euc d => (r.2, r.1.2)) :=
    measurable_snd.prodMk (measurable_snd.comp measurable_fst)
  have hf : Measurable (fun r : (Euc d × Euc d) × Euc d => s82t_J1 C gt r.2 r.1.2) := by
    have h1 := hJ.comp hm1
    exact h1
  have hI : Measurable (fun p : Euc d × Euc d => ∫ x', s82t_J1 C gt x' p.2 ∂mu) :=
    (hf.stronglyMeasurable.integral_prod_right' (ν := mu)).measurable
  have hT : Measurable (fun p : Euc d × Euc d => s82t_T C mu gt p.1 p.2) := hJ.sub hI
  have hsw : Measurable (fun p : Euc d × Euc d => (p.2, p.1)) := measurable_snd.prodMk measurable_fst
  have hTs : Measurable (fun p : Euc d × Euc d => s82t_T C mu gt p.2 p.1) := by
    have h1 := hT.comp hsw
    exact h1
  have e : Function.uncurry (s82t_Jt C mu gt) =
      fun p : Euc d × Euc d => s82t_T C mu gt p.1 p.2 + s82t_T C mu gt p.2 p.1 := by
    funext p; rfl
  rw [e]
  exact hT.add hTs

lemma s82t_Jt_symm {d : ℕ} (C : WholeCoeff d) (mu : Measure (Euc d)) (gt : Euc d → Euc d → Euc d)
    (x y : Euc d) : s82t_Jt C mu gt x y = s82t_Jt C mu gt y x := by
  unfold s82t_Jt; ring

lemma s82t_mu_ae_ne {d : ℕ} (hd : 2 ≤ d) (rho : Euc d → ℝ) (y : Euc d) :
    ∀ᵐ z ∂HRS.Whole.withDensityReal rho, z ≠ y := by
  have := s82p2_mu_singleton hd rho y
  rw [ae_iff]
  simpa using this

/-- `pairJ` equals the explicit model off the diagonal. -/
lemma s82t_pairJ_eq {d : ℕ} (hd : 2 ≤ d) {a beta M A : ℝ} {rho : Euc d → ℝ} {f : Euc d → ℝ}
    {Q : Euc d → Euc d → ℝ} (hQ : PairCorrector a beta rho M A f Q) (x y : Euc d) (hxy : x ≠ y) :
    pairJ (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) Q x y =
      s82t_Jt (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) (s82p2_gt Q) x y := by
  set C := critCoeff d a beta rho with hC
  set mu := HRS.Whole.withDensityReal rho with hmu
  have hgt : ∀ x y : Euc d, x ≠ y → gradient (fun w => Q w y) x = s82p2_gt Q x y :=
    fun x y hxy => (s82p2_gt_eq hQ x y hxy).symm
  have hQx : Q x = fun w => Q w x := funext fun w => hQ.symmetric x w
  have e1 : ∫ x', oneJ C (fun w => Q w y) x' ∂mu = ∫ x', s82t_J1 C (s82p2_gt Q) x' y ∂mu :=
    integral_congr_ae ((s82t_mu_ae_ne hd rho y).mono fun x' hx' =>
      s82t_oneJ_eq_J1 hd C Q (s82p2_gt Q) hgt x' y hx')
  have e2 : ∫ y', oneJ C (Q x) y' ∂mu = ∫ y', s82t_J1 C (s82p2_gt Q) y' x ∂mu := by
    rw [hQx]
    exact integral_congr_ae ((s82t_mu_ae_ne hd rho x).mono fun y' hy' =>
      s82t_oneJ_eq_J1 hd C Q (s82p2_gt Q) hgt y' x hy')
  unfold pairJ s82t_Jt s82t_T HRS.Whole.projMean HRS.Whole.pair
  beta_reduce
  rw [e1, e2, s82t_oneJ_eq_J1 hd C Q (s82p2_gt Q) hgt x y hxy]
  rw [hQx, s82t_oneJ_eq_J1 hd C Q (s82p2_gt Q) hgt y x hxy.symm]

end HRS.MS.S82T
