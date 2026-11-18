import HRS.MS.R26T8AV3

/-!
# S8.2 T8A U1: the diagonal is invisible to `CanonicalPair`, `generatorW` and `pairA`
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_U1_canonical_congr (hd : 2 ≤ d) (rho : Euc d → ℝ) {G H : Euc d → Euc d → ℝ}
    (h : ∀ x y, x ≠ y → G x y = H x y) (hH : CanonicalPair (HRS.Whole.withDensityReal rho) H) :
    CanonicalPair (HRS.Whole.withDensityReal rho) G := by
  haveI := r26t8a_nontrivial hd
  have hmu : HRS.Whole.withDensityReal rho ≪ (volume : Measure (Euc d)) := withDensity_absolutelyContinuous _ _
  have hae : ∀ p : Euc d, ∀ᵐ u ∂(HRS.Whole.withDensityReal rho), u ≠ p :=
    fun p => hmu.ae_le (compl_mem_ae_iff.mpr (measure_singleton p))
  have h1 : ∀ y, (fun x => G x y) =ᵐ[HRS.Whole.withDensityReal rho] fun x => H x y := fun y => by
    filter_upwards [hae y] with x hx using h x y hx
  have h2 : ∀ x, G x =ᵐ[HRS.Whole.withDensityReal rho] H x := fun x => by
    filter_upwards [hae x] with y hy using h x y (Ne.symm hy)
  refine ⟨fun y => (hH.1 y).congr (h1 y).symm, fun x => (hH.2.1 x).congr (h2 x).symm, fun y => ?_, fun x => ?_⟩
  · rw [integral_congr_ae (h1 y)]; exact hH.2.2.1 y
  · rw [integral_congr_ae (h2 x)]; exact hH.2.2.2 x

theorem r26t8a_U1_generatorW_congr (hd : 2 ≤ d) (C : WholeCoeff d) {g1 g2 : Euc d → ℝ} {y0 : Euc d}
    (h : ∀ u, u ≠ y0 → g1 u = g2 u) {x : Euc d} (hx : x ≠ y0) :
    generatorW C 0 g1 x = generatorW C 0 g2 x := by
  haveI := r26t8a_nontrivial hd
  have hev : ∀ u, u ≠ y0 → g1 =ᶠ[𝓝 u] g2 := fun u hu => by
    filter_upwards [(isOpen_compl_singleton (x := y0)).mem_nhds hu] with w hw using h w hw
  have hgrad : ∀ u, u ≠ y0 → gradient g1 u = gradient g2 u := fun u hu => by
    unfold gradient; rw [(hev u hu).fderiv_eq]
  have hlap : Laplacian.laplacian g1 x = Laplacian.laplacian g2 x :=
    (InnerProductSpace.laplacian_congr_nhds (hev x hx)).self_of_nhds
  have hae : ∀ᵐ u : Euc d ∂volume, u ≠ y0 := compl_mem_ae_iff.mpr (measure_singleton y0)
  have hconv : ∀ j : Fin d, convGradConvW (rieszKernelGrad d C.s)
      (fun y => C.ρ 0 y * (Torus.matVec C.M.transpose (gradient g1 y)) j) x =
      convGradConvW (rieszKernelGrad d C.s)
      (fun y => C.ρ 0 y * (Torus.matVec C.M.transpose (gradient g2 y)) j) x := by
    intro j
    unfold convGradConvW
    refine integral_congr_ae ?_
    filter_upwards [hae] with u hu
    simp only [hgrad u hu, hgrad x hx]
  unfold generatorW
  rw [hlap, hgrad x hx]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hconv j]

theorem r26t8a_U1_pairA_congr (hd : 2 ≤ d) (C : WholeCoeff d) (rho : Euc d → ℝ) {G H : Euc d → Euc d → ℝ}
    (h : ∀ x y, x ≠ y → G x y = H x y) {x y : Euc d} (hxy : x ≠ y) :
    pairA C (HRS.Whole.withDensityReal rho) G x y = pairA C (HRS.Whole.withDensityReal rho) H x y := by
  haveI := r26t8a_nontrivial hd
  have hmu : HRS.Whole.withDensityReal rho ≪ (volume : Measure (Euc d)) := withDensity_absolutelyContinuous _ _
  have hae : ∀ p : Euc d, ∀ᵐ u ∂(HRS.Whole.withDensityReal rho), u ≠ p :=
    fun p => hmu.ae_le (compl_mem_ae_iff.mpr (measure_singleton p))
  have hproj : ∀ {g1 g2 : Euc d → ℝ} {y0 : Euc d}, (∀ u, u ≠ y0 → g1 u = g2 u) → ∀ {x : Euc d}, x ≠ y0 →
      HRS.Whole.projGeneratorW C (HRS.Whole.withDensityReal rho) 0 g1 x =
        HRS.Whole.projGeneratorW C (HRS.Whole.withDensityReal rho) 0 g2 x := by
    intro g1 g2 y0 hg x hx
    unfold HRS.Whole.projGeneratorW
    rw [r26t8a_U1_generatorW_congr hd C hg hx]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hae y0] with u hu using r26t8a_U1_generatorW_congr hd C hg hu
  unfold pairA
  rw [hproj (g1 := fun x' => G x' y) (g2 := fun x' => H x' y) (y0 := y) (fun u hu => h u y hu) hxy,
    hproj (g1 := G x) (g2 := H x) (y0 := x) (fun u hu => h x u (Ne.symm hu)) (Ne.symm hxy)]

end HRS.MS.R26T8A
