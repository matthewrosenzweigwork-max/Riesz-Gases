import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MP.RdGenSob
import HRS.MS.S67NlBD08
import HRS.MS.S67NlBD14B
import HRS.MS.S67NlBD21

/-!
# S6.7 nonlinear breakdown, packet 43: local Cb force estimate from L1 and Sobolev source data

Namespace `HRS.MS.BreakdownS67`, helper prefix `s67bd_`. TeX S:4751-4763 area, nonlinear part of
`S:W:lem:r2mov-global-adjoint`. No owned definitions.
Route: (A) the physical local potential `s67bd_local d s h i = (D_i h) * g_loc` is `C^j` (convolution of
the locally integrable compactly supported kernel with a `C^{j+1}` function, localized by a bump);
(B) packet 21 puts it in `H^t`, `t = k - (movA - 1) > j + d/2`, with the stated norm bound;
(C) a Sobolev embedding for `C^l` functions (the proof of `rg_sobolev_embedding` copied with
`C^l` regularity instead of `C^infty`: continuity and `L^2` give pointwise Fourier inversion, `C^l`
identifies the derivative) bounds `D^l`, `l <= j`, by the `H^t` norm; constants are combined.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace FourierTransform

namespace HRS.MS.BreakdownS67

open HRS HRS.Whole HRS.MS.MovLin HRS.MS.MovOsc HRS.MS.MovAdj
open HRS.MS.Mov63 HRS.MS.MovForce HRS.MS.MovC2
open HRS.MS.PoisFlow HRS.MS.PoisSg HRS.MS.PoisKolm HRS.MS.PoisHigh

variable {d : ℕ} {s β q : ℝ} {ρ₀ : Euc d → ℝ}

/-- Sobolev embedding for functions of class `C^j` only (no smoothness beyond `j`). -/
lemma s67bd43_embed (j : ℕ) {q : ℝ} (hq : (j : ℝ) + d / 2 < q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : Euc d → ℝ, ContDiff ℝ (j : WithTop ℕ∞) φ → HRS.PDE.ToolboxRd.MemSobolev q φ →
      ∀ x : Euc d, ‖iteratedFDeriv ℝ j φ x‖ ≤ C * HRS.Whole.sobolevNorm q φ := by
  obtain ⟨Cj, hCj0, hCj⟩ := HRS.MP.RdGen.rg_moment_bound (d := d) j hq
  refine ⟨(2 * Real.pi) ^ j * Cj, by positivity, fun φ hφ hmem x => ?_⟩
  have hF := HRS.PDE.ToolboxRd.FourierAux.aestronglyMeasurable_fourierL2 hmem.1
  have hmom : ∀ n : ℕ, n ≤ j → Integrable (fun ξ : Euc d => ‖ξ‖ ^ n * ‖HRS.PDE.ToolboxRd.fourierL2 φ ξ‖) := by
    intro n hn
    have hnq : (n : ℝ) + d / 2 < q := by
      have : (n : ℝ) ≤ j := by exact_mod_cast hn
      linarith
    obtain ⟨Cn, -, hCn⟩ := HRS.MP.RdGen.rg_moment_bound (d := d) n hnq
    exact (hCn φ hmem).1
  set F' : Euc d → ℂ := fun ξ => HRS.PDE.ToolboxRd.fourierL2 φ (-ξ) with hF'
  have hF'm : AEStronglyMeasurable F' volume :=
    hF.comp_quasiMeasurePreserving (Measure.measurePreserving_neg (volume : Measure (Euc d))).quasiMeasurePreserving
  have hF'int : ∀ n : ℕ, n ≤ j → Integrable (fun ξ : Euc d => ‖ξ‖ ^ n * ‖F' ξ‖) := by
    intro n hn
    have := (hmom n hn).comp_neg
    refine this.congr (Eventually.of_forall fun ξ => ?_)
    simp [hF']
  have hcont : Continuous φ := hφ.continuous
  have hF1 : Integrable F' := by
    have := hF'int 0 (Nat.zero_le _)
    simp only [pow_zero, one_mul] at this
    exact (integrable_norm_iff hF'm).1 this
  have hinv : (fun y : Euc d => ((φ y : ℝ) : ℂ)) = 𝓕 F' := by
    funext y
    exact (HRS.MP.RdGen.rg_inversion hmem.1 hcont hF1 y).symm
  have e1 : ‖iteratedFDeriv ℝ j φ x‖ = ‖iteratedFDeriv ℝ j (fun y : Euc d => ((φ y : ℝ) : ℂ)) x‖ := by
    have := LinearIsometry.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) Complex.ofRealLI
      (hφ.contDiffAt (x := x)) (i := j) le_rfl
    exact this.symm
  rw [e1, hinv]
  refine (HRS.MP.RdGen.rg_norm_iteratedFDeriv_fourier_le hF'int hF'm x).trans ?_
  have e2 : ∫ v : Euc d, ‖v‖ ^ j * ‖F' v‖ = ∫ v : Euc d, ‖v‖ ^ j * ‖HRS.PDE.ToolboxRd.fourierL2 φ v‖ := by
    have := integral_neg_eq_self (fun ξ : Euc d => ‖ξ‖ ^ j * ‖HRS.PDE.ToolboxRd.fourierL2 φ ξ‖) (volume : Measure (Euc d))
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp [hF']
  rw [e2]
  have := (hCj φ hmem).2
  calc (2 * Real.pi) ^ j * ∫ v : Euc d, ‖v‖ ^ j * ‖HRS.PDE.ToolboxRd.fourierL2 φ v‖
      ≤ (2 * Real.pi) ^ j * (Cj * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq q φ)) := by gcongr
    _ = _ := by unfold HRS.Whole.sobolevNorm; ring

lemma s67bd43_embed_all (j : ℕ) {q : ℝ} (hq : (j : ℝ) + d / 2 < q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : Euc d → ℝ, ContDiff ℝ (j : WithTop ℕ∞) φ →
      HRS.PDE.ToolboxRd.MemSobolev q φ → ∀ l ≤ j, ∀ x : Euc d,
        ‖iteratedFDeriv ℝ l φ x‖ ≤ C * HRS.Whole.sobolevNorm q φ := by
  have h1 : ∀ l : Fin (j + 1), ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : Euc d → ℝ,
      ContDiff ℝ ((l : ℕ) : WithTop ℕ∞) φ → HRS.PDE.ToolboxRd.MemSobolev q φ →
      ∀ x : Euc d, ‖iteratedFDeriv ℝ (l : ℕ) φ x‖ ≤ C * HRS.Whole.sobolevNorm q φ := by
    intro l
    refine s67bd43_embed (l : ℕ) ?_
    have : ((l : ℕ) : ℝ) ≤ j := by exact_mod_cast Nat.lt_succ_iff.1 l.2
    linarith
  choose C hC0 hC using h1
  refine ⟨∑ l, C l, Finset.sum_nonneg (fun l _ => hC0 l), fun φ hφ hmem l hl x => ?_⟩
  have h2 := hC ⟨l, Nat.lt_succ_of_le hl⟩ φ (hφ.of_le (by exact_mod_cast hl)) hmem x
  refine h2.trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
  exact Finset.single_le_sum (f := C) (fun l _ => hC0 l) (Finset.mem_univ _)

/-- the physical local potential of a `C^{j+2}` source is `C^j` -/
lemma s67bd43_local_contDiff (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (j : ℕ)
    (h : Euc d → ℝ) (hh : ContDiff ℝ ((j + 2 : ℕ) : WithTop ℕ∞) h) (i : Fin d) :
    ContDiff ℝ (j : WithTop ℕ∞) (s67bd_local d s h i) := by
  have hd1 : 1 ≤ d := by omega
  have hg : ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) (s67bd_D i h) := by
    unfold s67bd_D
    exact (hh.fderiv_right (m := ((j + 1 : ℕ) : WithTop ℕ∞)) (by push_cast; exact le_rfl)).clm_apply
      contDiff_const
  have hloc : LocallyIntegrable (movb2_gloc d s) volume :=
    (mv1_gloc_integrable hd1 hs0 hsd).1.locallyIntegrable
  rw [contDiff_iff_contDiffAt]
  intro x0
  let χ : ContDiffBump (0 : Euc d) := ⟨‖x0‖ + 3, ‖x0‖ + 4, by positivity, by linarith⟩
  have hχg : ContDiff ℝ ((j : ℕ∞) : WithTop ℕ∞) (fun y => χ y * s67bd_D i h y) :=
    χ.contDiff.mul (hg.of_le (by exact_mod_cast Nat.le_succ j))
  have hχs : HasCompactSupport (fun y => χ y * s67bd_D i h y) := χ.hasCompactSupport.mul_right
  have hconv := hχs.contDiff_convolution_left (ContinuousLinearMap.mul ℝ ℝ) hχg hloc
  refine (hconv.contDiffAt (x := x0)).congr_of_eventuallyEq ?_
  filter_upwards [Metric.ball_mem_nhds x0 one_pos] with x hx
  have hxn : ‖x‖ ≤ ‖x0‖ + 1 := by
    have := norm_le_norm_add_norm_sub' x x0
    rw [Metric.mem_ball, dist_eq_norm] at hx
    linarith [norm_sub_rev x x0]
  unfold s67bd_local
  rw [convolution_def]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [ContinuousLinearMap.mul_apply']
  by_cases hy : 2 ≤ ‖x - y‖
  · rw [movb2_gloc_eq_zero hy]; simp
  · push Not at hy
    have hyn : ‖y‖ ≤ ‖x0‖ + 3 := by
      have := norm_le_norm_add_norm_sub' y x
      rw [norm_sub_rev] at this
      linarith
    have hχ1 : χ y = 1 := χ.one_of_mem_closedBall (by simpa using hyn)
    rw [hχ1]; ring

theorem s67bd_force_local_cb (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    (k j : ℕ) (hkj : (k : ℝ) - (movA d s - 1) > j + (d : ℝ) / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : Euc d → ℝ,
      ContDiff ℝ ((j + 2 : ℕ) : WithTop ℕ∞) h → Integrable h volume →
      HRS.PDE.ToolboxRd.MemSobolev (k : ℝ) h → ∀ i : Fin d,
      ContDiff ℝ (j : WithTop ℕ∞) (s67bd_local d s h i) ∧
      ∀ l ≤ j, ∀ x, ‖iteratedFDeriv ℝ l (s67bd_local d s h i) x‖ ≤
        C * ((∫ x, |h x|) + s67bd_Hnorm (k : ℝ) h) := by
  have ha1 : 1 ≤ movA d s := le_max_left _ _
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hd0 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hk1 : (1 : ℝ) ≤ k := by linarith
  obtain ⟨C2, hC2, hmul⟩ := s67bd_local_multiplier hd hs0 hsd (k : ℝ) hk1
  obtain ⟨C3, hC3, hemb⟩ := s67bd43_embed_all (d := d) j
    (q := (k : ℝ) - (movA d s - 1)) hkj
  refine ⟨C3 * C2, mul_nonneg hC3 hC2, fun h hh hI hH i => ?_⟩
  have hh1 : ContDiff ℝ 1 h := hh.of_le (by exact_mod_cast (by omega : 1 ≤ j + 2))
  obtain ⟨hmem, hnorm⟩ := hmul h hh1 hI hH i
  have hLc := s67bd43_local_contDiff hd hs0 hsd j h hh i
  refine ⟨hLc, fun l hl x => ?_⟩
  calc ‖iteratedFDeriv ℝ l (s67bd_local d s h i) x‖
      ≤ C3 * HRS.Whole.sobolevNorm ((k : ℝ) - (movA d s - 1)) (s67bd_local d s h i) :=
        hemb _ hLc hmem l hl x
    _ ≤ C3 * (C2 * (s67bd_Hnorm (k : ℝ) h + ∫ x, |h x|)) :=
        mul_le_mul_of_nonneg_left hnorm hC3
    _ = C3 * C2 * ((∫ x, |h x|) + s67bd_Hnorm (k : ℝ) h) := by ring

end HRS.MS.BreakdownS67
