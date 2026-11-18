import HRS.MS.R26T8AW5
import HRS.MS.R26T8AP10a
import HRS.MS.R26T8AP15h

/-!
# S8.2 T8A V1: pointwise additivity of the local operator, the divergence source and `oneJ` on conormal pair functions
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_V1_gradient_add {f g : Euc d → ℝ} {x : Euc d} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x) :
    gradient (fun w => f w + g w) x = gradient f x + gradient g x := by
  unfold gradient
  rw [show (fun w => f w + g w) = f + g from rfl, fderiv_add hf hg, map_add]

theorem r26t8a_V1_Lop_add (C : WholeCoeff d) {f g : Euc d → ℝ} {x : Euc d} (hf : ContDiffAt ℝ 2 f x)
    (hg : ContDiffAt ℝ 2 g x) :
    r26t8a_Lop C (fun w => f w + g w) x = r26t8a_Lop C f x + r26t8a_Lop C g x := by
  unfold r26t8a_Lop
  have h1 : Laplacian.laplacian (fun w => f w + g w) x = Laplacian.laplacian f x + Laplacian.laplacian g x :=
    hf.laplacian_add hg
  have hfd : DifferentiableAt ℝ f x := hf.differentiableAt (by norm_num)
  have hgd : DifferentiableAt ℝ g x := hg.differentiableAt (by norm_num)
  rw [h1, r26t8a_V1_gradient_add hfd hgd, inner_add_right]
  ring

theorem r26t8a_V1_slice1 {b : ℕ} {M σ A : ℝ} {Q : Euc d → Euc d → ℝ} (hQ : Conormal 2 b M σ A Q) {x y : Euc d}
    (hxy : x ≠ y) : ContDiffAt ℝ 2 (fun v => Q v y) x := by
  have hopen : IsOpen {p : Euc d × Euc d | p.1 ≠ p.2} := isOpen_ne_fun continuous_fst continuous_snd
  have h1 : ContDiffAt ℝ 2 (Function.uncurry Q) (x, y) := by
    have := hQ.1.contDiffAt (hopen.mem_nhds (show (x, y) ∈ {p : Euc d × Euc d | p.1 ≠ p.2} from hxy))
    exact_mod_cast this
  exact h1.comp x (contDiffAt_id.prodMk contDiffAt_const)

theorem r26t8a_V1_slice2 {b : ℕ} {M σ A : ℝ} {Q : Euc d → Euc d → ℝ} (hQ : Conormal 2 b M σ A Q) {x y : Euc d}
    (hxy : x ≠ y) : ContDiffAt ℝ 2 (Q x) y := by
  have hopen : IsOpen {p : Euc d × Euc d | p.1 ≠ p.2} := isOpen_ne_fun continuous_fst continuous_snd
  have h1 : ContDiffAt ℝ 2 (Function.uncurry Q) (x, y) := by
    have := hQ.1.contDiffAt (hopen.mem_nhds (show (x, y) ∈ {p : Euc d × Euc d | p.1 ≠ p.2} from hxy))
    exact_mod_cast this
  exact h1.comp y (contDiffAt_const.prodMk contDiffAt_id)

theorem r26t8a_V1_divSource_add (rho : Euc d → ℝ) {G1 G2 : Euc d → Euc d → ℝ} {u y : Euc d}
    (h1 : ContDiffAt ℝ 2 (fun v => G1 v y) u) (h2 : ContDiffAt ℝ 2 (fun v => G2 v y) u) :
    r26t8a_divSource rho (fun x y => G1 x y + G2 x y) u y =
      r26t8a_divSource rho G1 u y + r26t8a_divSource rho G2 u y := by
  unfold r26t8a_divSource pairGradX
  have hl : Laplacian.laplacian (fun w => G1 w y + G2 w y) u =
      Laplacian.laplacian (fun w => G1 w y) u + Laplacian.laplacian (fun w => G2 w y) u := h1.laplacian_add h2
  rw [hl, r26t8a_V1_gradient_add (h1.differentiableAt (by norm_num)) (h2.differentiableAt (by norm_num)),
    inner_add_right]
  ring

theorem r26t8a_V1_oneJ_add (hd : 2 ≤ d) (a beta M sigma : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M)
    (hsd : sigma < d) (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    {G1 G2 : Euc d → Euc d → ℝ} {A1 A2 : ℝ} (hA1 : 0 ≤ A1) (hA2 : 0 ≤ A2) {chi : Euc d → ℝ}
    (hchi : NewtonCutoff chi)
    (h1 : Conormal 2 1 M (sigma - 2) A1 G1) (h2 : Conormal 2 1 M (sigma - 2) A2 G2)
    {x y : Euc d} (hxy : x ≠ y) :
    oneJ (critCoeff d a beta rho) (fun w => G1 w y + G2 w y) x =
      oneJ (critCoeff d a beta rho) (fun w => G1 w y) x + oneJ (critCoeff d a beta rho) (fun w => G2 w y) x := by
  haveI : Nontrivial (Euc d) := r26t8a_nontrivial hd
  have h12 : Conormal 2 1 M (sigma - 2) (A1 + A2) (fun x y => G1 x y + G2 x y) :=
    r26t8a_conormal_add hchi h1 h2
  obtain ⟨i1, e1⟩ := r26t8a_conormal_potential_ibp d hd 0 1 a beta M sigma ha hbeta hM hsd rho hrho G1 A1 hA1 h1 x y hxy
  obtain ⟨i2, e2⟩ := r26t8a_conormal_potential_ibp d hd 0 1 a beta M sigma ha hbeta hM hsd rho hrho G2 A2 hA2 h2 x y hxy
  obtain ⟨-, e12⟩ := r26t8a_conormal_potential_ibp d hd 0 1 a beta M sigma ha hbeta hM hsd rho hrho
    (fun x y => G1 x y + G2 x y) (A1 + A2) (by positivity) h12 x y hxy
  have hae : ∀ᵐ u : Euc d ∂volume, u ≠ y := compl_mem_ae_iff.mpr (measure_singleton y)
  show oneJ (critCoeff d a beta rho) (fun u => (fun x y => G1 x y + G2 x y) u y) x = _
  rw [e12, e1, e2, ← integral_add i1 i2]
  refine integral_congr_ae ?_
  filter_upwards [hae] with u hu
  rw [r26t8a_V1_divSource_add rho (r26t8a_V1_slice1 h1 hu) (r26t8a_V1_slice1 h2 hu), mul_add]

end HRS.MS.R26T8A
