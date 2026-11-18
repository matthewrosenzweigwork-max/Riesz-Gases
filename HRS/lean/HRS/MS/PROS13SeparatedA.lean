import HRS.MS.S21T4ProdW
import HRS.MS.SuppU1Aux3
import HRS.MS.SuppU1Aux9

/-!
# S13: symmetric separated finite-rank approximation for arbitrary probability measures

Preliminary support estimate for compactly supported smooth kernels on Euclidean
product spaces. No non-atomicity or density hypothesis is imposed.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.Whole.U1
variable {d : ℕ}

private theorem pro_s13_support_bound
    (g : Euc d × Euc d → ℝ) (hg : HasCompactSupport g) :
    ∃ R : ℝ, ∀ p : Euc d × Euc d,
      g p ≠ 0 → ‖p.1‖ ≤ R ∧ ‖p.2‖ ≤ R := by
  obtain ⟨R, hR⟩ :=
    (Metric.isBounded_iff_subset_closedBall
      (0 : Euc d × Euc d)).mp hg.isBounded
  refine ⟨R, fun p hp => ?_⟩
  have hps : p ∈ tsupport g :=
    subset_closure (show p ∈ Function.support g from hp)
  have hpR : ‖p‖ ≤ R := by
    simpa [mem_closedBall, dist_zero_right] using hR hps
  exact ⟨(norm_fst_le p).trans hpR, (norm_snd_le p).trans hpR⟩


/--
Every symmetric square-integrable pair kernel under an arbitrary Borel
probability admits a symmetric finite-rank approximation with smooth compactly
supported separated factors. This includes finite atomic measures.
-/
theorem pro_s13_generic_separated_approx
    (μ : Measure (Euc d)) [IsProbabilityMeasure μ]
    (h : Euc d → Euc d → ℝ)
    (hh : MemLp (fun p : Euc d × Euc d => h p.1 p.2) 2 (μ.prod μ))
    (hs : ∀ x y, h x y = h y x)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (m : ℕ) (c : Fin m → Fin m → ℝ) (u : Fin m → Euc d → ℝ),
      IsR2FiniteRankData c u ∧
      eLpNorm
        (fun p : Euc d × Euc d =>
          r2FiniteRankKernel c u p.1 p.2 - h p.1 p.2)
        2 (μ.prod μ) ≤ ENNReal.ofReal ε := by
  let P := μ.prod μ
  have hε2 : 0 < ε / 2 := by positivity
  obtain ⟨g, hgc, hgs, hgap⟩ :=
    s21t4_product_kernel_smooth_dense μ
      (fun p : Euc d × Euc d => h p.1 p.2) hh (ε / 2) hε2
  let G : Euc d × Euc d → ℝ := fun p => (g p + g p.swap) / 2
  have hgc' : Continuous g := hgs.continuous
  have hGcont : Continuous G :=
    (hgc'.add (hgc'.comp continuous_swap)).div_const 2
  have hGsym : ∀ x y : Euc d, G (x, y) = G (y, x) := by
    intro x y
    simp only [G, Prod.swap_prod_mk]
    rw [add_comm]
  obtain ⟨R, hR⟩ := pro_s13_support_bound g hgc
  have hGsupport : ∀ x y : Euc d,
      G (x, y) ≠ 0 → ‖x‖ ≤ R ∧ ‖y‖ ≤ R := by
    intro x y hxy
    by_cases hx : g (x,y) = 0
    · have hy : g (y,x) ≠ 0 := by
        intro hzero
        apply hxy
        simp [G, hx, hzero]
      obtain ⟨hyb, hxb⟩ := hR (y,x) hy
      exact ⟨hxb, hyb⟩
    · exact hR (x,y) hx
  obtain ⟨m, c, u, hcs, hum, huc, hk⟩ :=
    u1_finiteRank_of_continuous G hGcont hGsym R (ε / 2) hε2 hGsupport
  have hdata : IsR2FiniteRankData c u := ⟨hcs, hum, huc⟩
  have hKcont : Continuous
      (fun p : Euc d × Euc d => r2FiniteRankKernel c u p.1 p.2) := by
    unfold r2FiniteRankKernel
    refine continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_
    exact (continuous_const.mul ((hum a).continuous.comp continuous_fst)).mul
      ((hum b).continuous.comp continuous_snd)
  have h1 : eLpNorm
      (fun p : Euc d × Euc d =>
        r2FiniteRankKernel c u p.1 p.2 - G p) 2 P
      ≤ ENNReal.ofReal (ε / 2) := by
    have hbd : ∀ p : Euc d × Euc d,
        ‖r2FiniteRankKernel c u p.1 p.2 - G p‖ ≤ ε / 2 := by
      intro p
      rw [Real.norm_eq_abs, abs_sub_comm]
      exact hk p.1 p.2
    have h := eLpNorm_le_of_ae_bound (p := (2 : ℝ≥0∞))
      (μ := P) (hKcont.sub hGcont).aestronglyMeasurable (ae_of_all _ hbd)
    have hfun :
        (fun p : Euc d × Euc d =>
          r2FiniteRankKernel c u p.1 p.2 - G p) =
        ((fun p : Euc d × Euc d =>
          r2FiniteRankKernel c u p.1 p.2) - G) := by
      funext p
      rfl
    rw [hfun]
    simpa [P] using h
  have h2 : eLpNorm
      (fun p : Euc d × Euc d => G p - h p.1 p.2) 2 P
      ≤ ENNReal.ofReal (ε / 2) := by
    have hswap : MeasurePreserving Prod.swap P P :=
      Measure.measurePreserving_swap (μ := μ) (ν := μ)
    have hgSym : ∀ p : Euc d × Euc d,
      (fun p : Euc d × Euc d => h p.1 p.2) p.swap =
        (fun p : Euc d × Euc d => h p.1 p.2) p := by
      intro p
      simpa only [Prod.swap, Prod.fst_swap, Prod.snd_swap] using hs p.2 p.1
    have hsymm :=
      u1_symm_Lr P hswap (by norm_num : (1:ℝ) ≤ 2)
        g (fun p : Euc d × Euc d => h p.1 p.2)
        hgc'.aestronglyMeasurable hh.aestronglyMeasurable hgSym
    have hsymm' : eLpNorm (fun p => G p - h p.1 p.2) 2 P ≤
      eLpNorm (fun p => g p - h p.1 p.2) 2 P := by
      simpa only [G, ENNReal.ofReal_ofNat] using hsymm
    have hgapp : eLpNorm
        (g - (fun p : Euc d × Euc d => h p.1 p.2)) 2 P
        ≤ ENNReal.ofReal (ε / 2) := by
      rw [eLpNorm_sub_comm]
      exact hgap
    have hfun :
        (fun p : Euc d × Euc d => g p - h p.1 p.2) =
        (g - (fun p : Euc d × Euc d => h p.1 p.2)) := by
      funext p
      rfl
    exact hsymm'.trans (by
      rw [hfun]
      exact hgapp)
  refine ⟨m, c, u, hdata, ?_⟩
  calc
    eLpNorm
        (fun p : Euc d × Euc d =>
          r2FiniteRankKernel c u p.1 p.2 - h p.1 p.2) 2 P
      ≤ eLpNorm (fun p => r2FiniteRankKernel c u p.1 p.2 - G p) 2 P +
        eLpNorm (fun p => G p - h p.1 p.2) 2 P :=
          u1_tri P (by norm_num) _ _ _
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
      add_le_add h1 h2
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add hε2.le hε2.le]
      congr 1
      ring

end HRS.MS.R26T3
