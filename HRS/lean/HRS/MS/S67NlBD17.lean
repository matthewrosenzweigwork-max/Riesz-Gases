import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.MovOpAux6
import HRS.MS.MovOscAux5
import HRS.MS.S67NlBD04
import HRS.MS.S67NlBD14B

/-!
# S6.7 nonlinear breakdown, packet 17: smooth far-force coefficients and coordinate-weighted bounds

`s67bd_far_force_coefficients`: `h = √ρ₀ v` satisfies the Gaussian-times-`L²` moment bound
`∫ (1+|y|)|h| ≤ C ‖v‖_{Σ^m}` (Cauchy–Schwarz), so `movc2_conv_far` applied to the far kernel `∂_i g_far`
(bounded derivatives with weight `(1+|z|)`) gives the `C^∞` convolution with weighted jet bounds; the
coordinate-multiplied jets follow from Leibniz and the `(1+|x|)` weight.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.BreakdownS67

open HRS HRS.Whole HRS.MS.MovLin HRS.MS.MovOsc HRS.MS.MovAdj
open HRS.MS.Mov63 HRS.MS.MovForce HRS.MS.MovC2
open HRS.MS.PoisFlow HRS.MS.PoisSg HRS.MS.PoisKolm HRS.MS.PoisHigh

variable {d : ℕ} {s β q : ℝ} {ρ₀ : Euc d → ℝ}

/-- Cauchy–Schwarz for the weighted moment: `∫ G |v| ≤ ‖G‖₂ ‖v‖₂`. -/
theorem s67bd_moment_cs {G v : Euc d → ℝ} (hG : MemLp G 2 (volume : Measure (Euc d)))
    (hv : MemLp v 2 (volume : Measure (Euc d))) :
    Integrable (fun y => G y * |v y|) volume ∧
      ∫ y, G y * |v y| ≤ (eLpNorm G 2 (volume : Measure (Euc d))).toReal *
        (eLpNorm v 2 (volume : Measure (Euc d))).toReal := by
  have hvn : MemLp (fun y => |v y|) 2 (volume : Measure (Euc d)) := by
    simpa [Real.norm_eq_abs] using hv.norm
  refine ⟨hG.integrable_mul hvn, ?_⟩
  have h1 := OscDual.inner_toLp_mul G (fun y => |v y|) hG hvn
  have h2 := real_inner_le_norm (hG.toLp G) (hvn.toLp fun y => |v y|)
  rw [h1, Lp.norm_toLp, Lp.norm_toLp] at h2
  refine h2.trans (le_of_eq ?_)
  congr 2
  have : (fun y => |v y|) = fun y => ‖v y‖ := by funext y; simp
  rw [this]
  exact eLpNorm_norm v hv.aestronglyMeasurable

theorem s67bd_far_force_coefficients (H : Mov2dTh d s β q ρ₀) (m N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : Euc d → ℝ, MemOsc (m : ℝ) v → ∀ i : Fin d,
      ContDiff ℝ ∞ (s67bd_far d s (fun y => Real.sqrt (ρ₀ y) * v y) i) ∧
      (∀ k ≤ N, ∀ x, ‖iteratedFDeriv ℝ k
        (s67bd_far d s (fun y => Real.sqrt (ρ₀ y) * v y) i) x‖ ≤
          C * oscNorm (m : ℝ) v) ∧
      ∀ l : Fin d, ∀ k ≤ N, ∀ x, ‖iteratedFDeriv ℝ k
        (fun z => z l * s67bd_far d s (fun y => Real.sqrt (ρ₀ y) * v y) i z) x‖ ≤
          C * oscNorm (m : ℝ) v := by
  obtain ⟨B, -, hR, -⟩ := HRS.MS.Mov0.mv0_gapref H.hd H.hs0 H.hsd H.hq H.hβ H.hρ
  obtain ⟨hsm, -, c, hc, hk⟩ := HRS.MS.Mov0.mv0_sqrt_gauss (mul_pos H.hβ H.hq) hR
  obtain ⟨Cψ, hCψ⟩ := hk 0
  have hCψ0 : 0 ≤ Cψ := (abs_nonneg _).trans (by simpa using hCψ 0)
  obtain ⟨CG, hCG0, hCG⟩ := s67bd_gaussian_L2 d 1 c hc
  set G : Euc d → ℝ := fun y => (1 + ‖y‖) * Real.sqrt (ρ₀ y) with hGdef
  have hG0 : ∀ y, 0 ≤ G y := fun y => mul_nonneg (by positivity) (Real.sqrt_nonneg _)
  have hGc : Continuous G := (continuous_const.add continuous_norm).mul hsm.continuous
  have hGL2 := hCG Cψ hCψ0 G hGc.aestronglyMeasurable (fun x => by
    have h1 := hCψ x
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h1
    rw [abs_of_nonneg (hG0 x), hGdef]
    simp only
    rw [pow_one]
    calc (1 + ‖x‖) * Real.sqrt (ρ₀ x) ≤ (1 + ‖x‖) * (Cψ * Real.exp (-c * ‖x‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left ((le_abs_self _).trans h1) (by positivity)
      _ = Cψ * (1 + ‖x‖) * Real.exp (-c * ‖x‖ ^ 2) := by ring)
  obtain ⟨K, hK0, hK⟩ := movc2_kfar_iter (d := d) H.hs0 N
  refine ⟨(2 ^ N + 1) * K * (CG * Cψ), by positivity, fun v hv i => ?_⟩
  set h : Euc d → ℝ := fun y => Real.sqrt (ρ₀ y) * v y with hh
  have hhm : AEStronglyMeasurable h volume :=
    hsm.continuous.aestronglyMeasurable.mul hv.1.aestronglyMeasurable
  -- the moment bound
  have hmom : Integrable (fun y => (1 + ‖y‖) * |h y|) volume ∧
      ∫ y, (1 + ‖y‖) * |h y| ≤ CG * Cψ * oscNorm (m : ℝ) v := by
    obtain ⟨hi, hle⟩ := s67bd_moment_cs hGL2.1 hv.1
    have e : (fun y => (1 + ‖y‖) * |h y|) = fun y => G y * |v y| := by
      funext y
      simp only [hh, hGdef, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      ring
    rw [e]
    refine ⟨hi, hle.trans ?_⟩
    have hv0 : (eLpNorm v 2 (volume : Measure (Euc d))).toReal = oscNorm 0 v := by
      rw [mova2_eLpNorm_two hv.1, ENNReal.toReal_ofReal (by unfold oscNorm; exact Real.sqrt_nonneg _)]
    have hvm : oscNorm 0 v ≤ oscNorm (m : ℝ) v := (mo_mono (Nat.cast_nonneg m) hv).2
    rw [hv0]
    calc (eLpNorm G 2 (volume : Measure (Euc d))).toReal * oscNorm 0 v
        ≤ (CG * Cψ) * oscNorm (m : ℝ) v :=
          mul_le_mul hGL2.2 hvm (by unfold oscNorm; exact Real.sqrt_nonneg _)
            (mul_nonneg hCG0 hCψ0)
      _ = _ := rfl
  have hfar : s67bd_far d s h i = fun x => ∫ y, h y • movb2_kfar d s i (x - y) := by
    funext x
    unfold s67bd_far
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp [mul_comm]
  have hκ : ∀ n : ℕ, ContDiff ℝ (n : WithTop ℕ∞) (movb2_kfar d s i) := fun n =>
    (movc2_kfar_smooth (d := d) (s := s) i).of_le (by exact_mod_cast le_top)
  -- smoothness of all orders
  have hsmooth : ContDiff ℝ ∞ (s67bd_far d s h i) := by
    rw [contDiff_infty]
    intro n
    obtain ⟨Kn, -, hKn⟩ := movc2_kfar_iter (d := d) H.hs0 n
    rw [hfar]
    exact (movc2_conv_far n ℝ (movb2_kfar d s i) Kn h (hκ n)
      (fun k hk z => hKn i k hk z) hhm hmom.1).1
  -- weighted bounds up to order `N`
  obtain ⟨hcN, hbN⟩ := movc2_conv_far (d := d) N ℝ (movb2_kfar d s i) K h (hκ N)
    (fun k hk z => hK i k hk z) hhm hmom.1
  rw [← hfar] at hcN hbN
  set I : ℝ := ∫ y, (1 + ‖y‖) * |h y| with hI
  have hI0 : 0 ≤ I := integral_nonneg fun y => mul_nonneg (by positivity) (abs_nonneg _)
  have hW : K * I ≤ K * (CG * Cψ * oscNorm (m : ℝ) v) := mul_le_mul_of_nonneg_left hmom.2 hK0
  have ho : 0 ≤ oscNorm (m : ℝ) v := by unfold oscNorm; exact Real.sqrt_nonneg _
  have hW0 : 0 ≤ K * (CG * Cψ * oscNorm (m : ℝ) v) :=
    mul_nonneg hK0 (mul_nonneg (mul_nonneg hCG0 hCψ0) ho)
  -- unweighted bound
  have hb1 : ∀ k ≤ N, ∀ x, ‖iteratedFDeriv ℝ k (s67bd_far d s h i) x‖ ≤
      K * (CG * Cψ * oscNorm (m : ℝ) v) := by
    intro k hk x
    have := hbN k hk x
    have h1 : ‖iteratedFDeriv ℝ k (s67bd_far d s h i) x‖ ≤
        ‖iteratedFDeriv ℝ k (s67bd_far d s h i) x‖ * (1 + ‖x‖) :=
      le_mul_of_one_le_right (norm_nonneg _) (by linarith [norm_nonneg x])
    exact h1.trans (this.trans hW)
  refine ⟨hsmooth, fun k hk x => ?_, fun l k hk x => ?_⟩
  · refine (hb1 k hk x).trans ?_
    have : K * (CG * Cψ * oscNorm (m : ℝ) v) ≤
        (2 ^ N + 1) * K * (CG * Cψ) * oscNorm (m : ℝ) v := by
      have h2 : (1 : ℝ) ≤ 2 ^ N + 1 := by
        have : (0 : ℝ) ≤ 2 ^ N := by positivity
        linarith
      have h3 : 0 ≤ K * (CG * Cψ) * oscNorm (m : ℝ) v := by
        exact mul_nonneg (mul_nonneg hK0 (mul_nonneg hCG0 hCψ0)) ho
      nlinarith [mul_le_mul_of_nonneg_right h2 h3]
    exact this
  · -- coordinate-weighted jets
    set Wb : ℝ := K * (CG * Cψ * oscNorm (m : ℝ) v) with hWb
    have hlin : ContDiff ℝ (N : WithTop ℕ∞) (fun z : Euc d => z l) :=
      (EuclideanSpace.proj (𝕜 := ℝ) l : Euc d →L[ℝ] ℝ).contDiff
    have hmul := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (f := fun z : Euc d => z l)
      (g := s67bd_far d s h i) (N := (N : WithTop ℕ∞)) hlin hcN x (n := k) (by exact_mod_cast hk)
    refine hmul.trans ?_
    have hterm : ∀ j ∈ Finset.range (k + 1),
        (k.choose j : ℝ) * ‖iteratedFDeriv ℝ j (fun z : Euc d => z l) x‖ *
          ‖iteratedFDeriv ℝ (k - j) (s67bd_far d s h i) x‖ ≤ (k.choose j : ℝ) * Wb := by
      intro j hj
      have hj' : j ≤ k := by simpa [Nat.lt_succ_iff] using Finset.mem_range.1 hj
      have hFb := hbN (k - j) (by omega) x
      have hxp : (0 : ℝ) < 1 + ‖x‖ := by positivity
      have ha : ‖iteratedFDeriv ℝ j (fun z : Euc d => z l) x‖ ≤ 1 + ‖x‖ := by
        rcases j with _ | j
        · rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
          have := PiLp.norm_apply_le x l
          rw [Real.norm_eq_abs] at this
          linarith
        · have h1 := HRS.MS.Mov0.mov0_clm_iter (EuclideanSpace.proj (𝕜 := ℝ) l : Euc d →L[ℝ] ℝ) j x
          have h2 : ‖(EuclideanSpace.proj (𝕜 := ℝ) l : Euc d →L[ℝ] ℝ)‖ ≤ 1 :=
            ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by
              simpa using PiLp.norm_apply_le w l
          have := h1.trans h2
          have h3 : ‖iteratedFDeriv ℝ (j + 1) (fun z : Euc d => z l) x‖ ≤ 1 := this
          linarith [norm_nonneg x]
      have hFb' : ‖iteratedFDeriv ℝ (k - j) (s67bd_far d s h i) x‖ * (1 + ‖x‖) ≤ Wb :=
        hFb.trans hW
      calc (k.choose j : ℝ) * ‖iteratedFDeriv ℝ j (fun z : Euc d => z l) x‖ *
            ‖iteratedFDeriv ℝ (k - j) (s67bd_far d s h i) x‖
          ≤ (k.choose j : ℝ) * (1 + ‖x‖) * ‖iteratedFDeriv ℝ (k - j) (s67bd_far d s h i) x‖ := by
            gcongr
        _ = (k.choose j : ℝ) * (‖iteratedFDeriv ℝ (k - j) (s67bd_far d s h i) x‖ * (1 + ‖x‖)) := by
            ring
        _ ≤ (k.choose j : ℝ) * Wb := mul_le_mul_of_nonneg_left hFb' (Nat.cast_nonneg _)
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.sum_mul]
    have hs : ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) = 2 ^ k := by
      exact_mod_cast Nat.sum_range_choose k
    rw [hs]
    have h2k : (2 : ℝ) ^ k ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hk
    have hWb0 : 0 ≤ Wb := hW0
    have : 2 ^ k * Wb ≤ (2 ^ N + 1) * K * (CG * Cψ) * oscNorm (m : ℝ) v := by
      rw [hWb]
      nlinarith [mul_le_mul_of_nonneg_right h2k hWb0, hW0]
    exact this

end HRS.MS.BreakdownS67
