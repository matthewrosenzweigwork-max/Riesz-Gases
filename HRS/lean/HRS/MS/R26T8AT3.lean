import HRS.MS.R26T8AT2

/-!
# S8.2 T8A T3: linearity of `pairA` on conormal pair functions
`r26t8a_T3_pairA_lin`: `pairA (F1 + c F2) x y = pairA F1 x y + c pairA F2 x y` for `x ≠ y` and `F1, F2` of class `Conormal 2 1 M (σ-2)`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_T3_gradient_smul {g : Euc d → ℝ} {u : Euc d} (hg : DifferentiableAt ℝ g u) (c : ℝ) :
    gradient (fun w => c * g w) u = c • gradient g u := by
  unfold gradient
  rw [fderiv_const_mul hg c, map_smul]

theorem r26t8a_T3_generatorW_smul (hd : 2 ≤ d) (C : WholeCoeff d) {g : Euc d → ℝ} {y0 : Euc d}
    (hg : ∀ u, u ≠ y0 → ContDiffAt ℝ 2 g u) (c : ℝ) {x : Euc d} (hx : x ≠ y0) :
    generatorW C 0 (fun w => c * g w) x = c * generatorW C 0 g x := by
  haveI := r26t8a_nontrivial hd
  have hae : ∀ᵐ u : Euc d ∂volume, u ≠ y0 := compl_mem_ae_iff.mpr (measure_singleton y0)
  have hgrad : ∀ u, u ≠ y0 → gradient (fun w => c * g w) u = c • gradient g u := fun u hu =>
    r26t8a_T3_gradient_smul ((hg u hu).differentiableAt (by norm_num)) c
  have hlap : Laplacian.laplacian (fun w => c * g w) x = c * Laplacian.laplacian g x :=
    InnerProductSpace.laplacian_smul c (hg x hx)
  have hmv : ∀ v : Euc d, Torus.matVec C.M.transpose (c • v) = c • Torus.matVec C.M.transpose v := fun v => by
    simp [Torus.matVec]
  have hconv : ∀ j : Fin d, convGradConvW (rieszKernelGrad d C.s)
      (fun y => C.ρ 0 y * (Torus.matVec C.M.transpose (gradient (fun w => c * g w) y)) j) x =
      c • convGradConvW (rieszKernelGrad d C.s)
      (fun y => C.ρ 0 y * (Torus.matVec C.M.transpose (gradient g y)) j) x := by
    intro j
    unfold convGradConvW
    rw [← integral_smul]
    refine integral_congr_ae ?_
    filter_upwards [hae] with u hu
    simp only [hgrad u hu, hgrad x hx, hmv, PiLp.smul_apply, smul_eq_mul]
    by_cases hb : ‖x - u‖ ≤ 1 / 4
    · simp only [hb, if_true, smul_smul]
      congr 1; ring
    · simp only [hb, if_false, smul_smul]
      congr 1; ring
  unfold generatorW
  rw [hlap, hgrad x hx]
  simp only [hconv, PiLp.smul_apply, smul_eq_mul, inner_smul_right, ← Finset.mul_sum]
  ring

theorem r26t8a_T3_pairA_smul (hd : 2 ≤ d) (C : WholeCoeff d) (rho : Euc d → ℝ) {b : ℕ} {M σ A : ℝ} {G : Euc d → Euc d → ℝ}
    (hG : Conormal 2 b M σ A G) (c : ℝ) {x y : Euc d} (hxy : x ≠ y) :
    pairA C (HRS.Whole.withDensityReal rho) (fun x y => c * G x y) x y =
      c * pairA C (HRS.Whole.withDensityReal rho) G x y := by
  haveI := r26t8a_nontrivial hd
  have hmu : HRS.Whole.withDensityReal rho ≪ (volume : Measure (Euc d)) := withDensity_absolutelyContinuous _ _
  have hae : ∀ p : Euc d, ∀ᵐ u ∂(HRS.Whole.withDensityReal rho), u ≠ p :=
    fun p => hmu.ae_le (compl_mem_ae_iff.mpr (measure_singleton p))
  have hproj : ∀ {g : Euc d → ℝ} {y0 : Euc d}, (∀ u, u ≠ y0 → ContDiffAt ℝ 2 g u) → ∀ {x : Euc d}, x ≠ y0 →
      HRS.Whole.projGeneratorW C (HRS.Whole.withDensityReal rho) 0 (fun w => c * g w) x =
        c * HRS.Whole.projGeneratorW C (HRS.Whole.withDensityReal rho) 0 g x := by
    intro g y0 hg x hx
    unfold HRS.Whole.projGeneratorW
    rw [r26t8a_T3_generatorW_smul hd C hg c hx]
    have : ∫ u, generatorW C 0 (fun w => c * g w) u ∂(HRS.Whole.withDensityReal rho) =
        c * ∫ u, generatorW C 0 g u ∂(HRS.Whole.withDensityReal rho) := by
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [hae y0] with u hu using r26t8a_T3_generatorW_smul hd C hg c hu
    rw [this]; ring
  unfold pairA
  have h1 := hproj (g := fun x' => G x' y) (y0 := y) (fun u hu => r26t8a_V1_slice1 hG hu) hxy
  have h2 := hproj (g := G x) (y0 := x) (fun u hu => r26t8a_V1_slice2 hG (Ne.symm hu)) (Ne.symm hxy)
  beta_reduce
  linarith [h1, h2]

theorem r26t8a_T3_pairA_lin (hd : 2 ≤ d) (a beta M sigma : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M)
    (hsd : sigma < d) (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {G1 G2 : Euc d → Euc d → ℝ} {A1 A2 : ℝ}
    (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2) (h1 : Conormal 2 1 M (sigma - 2) A1 G1) (h2 : Conormal 2 1 M (sigma - 2) A2 G2)
    (c : ℝ) {x y : Euc d} (hxy : x ≠ y) :
    pairA (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) (fun x y => G1 x y + c * G2 x y) x y =
      pairA (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) G1 x y +
        c * pairA (critCoeff d a beta rho) (HRS.Whole.withDensityReal rho) G2 x y := by
  have hc2 := r26t8a_conormal_const_mul hchi hA2 c h2
  rw [r26t8a_V2_pairA_add hd a beta M sigma ha hbeta hM hsd rho hrho hchi hA1
    (by positivity : 0 ≤ 2 ^ 2 * (((2 : ℕ) + 1 : ℝ) ^ 2 * |c| * A2)) h1 hc2 hxy,
    r26t8a_T3_pairA_smul hd _ rho h2 c hxy]

end HRS.MS.R26T8A
