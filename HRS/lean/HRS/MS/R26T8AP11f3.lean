import HRS.MS.R26T8AP10a14

/-!
# S8.2 T8A P11f (part 3): joint jets of `uncurry Q` from the conormal bounds
`r26t8a_p11f_joint_jet`: for `Conormal K b M σ A Q`, `j ≤ K`, `x ≠ y`:
`‖D^j (uncurry Q) (x,y)‖ ≤ 2^j ∑_{q ≤ j} C(j,q) A w(x,y) (1 + s^(-(σ+q)) (1+|log s|)^b)`, `s = min 1 |x-y|`.
Same route as `r26t8a_p10a_slice_jet`: `Q(x,y) = Ψ(L(x,y))`, `L(x,y) = ((x+y)/2, x-y)` (`‖L‖ ≤ 2`), `Ψ` the cutoff of `midPair Q`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_p11f_joint_jet {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {K b : ℕ} {M σ A : ℝ}
    (hA : 0 ≤ A) {Q : Euc d → Euc d → ℝ} (hQ : Conormal K b M σ A Q) {j : ℕ} (hj : j ≤ K)
    {x y : Euc d} (hxy : x ≠ y) :
    ‖iteratedFDeriv ℝ j (Function.uncurry Q) (x, y)‖ ≤
      2 ^ j * ∑ q ∈ Finset.range (j + 1), (j.choose q : ℝ) * (A * pairWeight M x y *
        (1 + (min 1 ‖x - y‖) ^ (-(σ + q)) * (1 + |Real.log (min 1 ‖x - y‖)|) ^ b)) := by
  set X : Euc d := (1 / 2 : ℝ) • (x + y) with hX
  set z : Euc d := x - y with hz
  have hz0 : z ≠ 0 := sub_ne_zero.2 hxy
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hx1 : X + (1 / 2 : ℝ) • z = x := by rw [hX, hz]; module
  have hy1 : X - (1 / 2 : ℝ) • z = y := by rw [hX, hz]; module
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = 2 * ‖z‖ := ⟨_, rfl⟩
  have hR : 0 < R := by rw [hRdef]; positivity
  have hl : R / 4 < ‖z‖ := by rw [hRdef]; linarith
  set Ψ : Euc d × Euc d → ℝ := fun Yw => r26t8a_psiCut chi R Yw.2 * midPair Q Yw.1 Yw.2 with hΨdef
  have hΨ : ContDiff ℝ (j : WithTop ℕ∞) Ψ :=
    (r26t8a_gtilde_contDiff hchi hR hQ.1).of_le (by exact_mod_cast hj)
  set L : (Euc d × Euc d) →L[ℝ] (Euc d × Euc d) :=
    (((1 / 2 : ℝ) • ContinuousLinearMap.fst ℝ (Euc d) (Euc d) + (1 / 2 : ℝ) • ContinuousLinearMap.snd ℝ (Euc d) (Euc d))).prod
      (ContinuousLinearMap.fst ℝ (Euc d) (Euc d) - ContinuousLinearMap.snd ℝ (Euc d) (Euc d)) with hL
  have hLw : ∀ w : Euc d × Euc d, L w = ((1 / 2 : ℝ) • (w.1 + w.2), w.1 - w.2) := by
    intro w; ext <;> simp [hL] <;> module
  have hLn : ‖L‖ ≤ 2 := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun w => ?_
    have h1 : ‖w.1‖ ≤ ‖w‖ := norm_fst_le w
    have h2 : ‖w.2‖ ≤ ‖w‖ := norm_snd_le w
    have h3 := le_max_left ‖w.1‖ ‖w.2‖
    have h4 := le_max_right ‖w.1‖ ‖w.2‖
    have h5 : 0 ≤ max ‖w.1‖ ‖w.2‖ := le_max_of_le_left (norm_nonneg _)
    have h6 := norm_nonneg w
    rw [hLw, Prod.norm_def]
    refine max_le ?_ ?_
    · rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
      have := norm_add_le w.1 w.2
      linarith
    · have := norm_sub_le w.1 w.2
      linarith
  have hopen : IsOpen {w : Euc d × Euc d | R / 4 < ‖w.1 - w.2‖} :=
    isOpen_lt continuous_const (continuous_norm.comp (continuous_fst.sub continuous_snd))
  have hev : Function.uncurry Q =ᶠ[𝓝 (x, y)] fun w => Ψ (L w) := by
    filter_upwards [hopen.mem_nhds (show R / 4 < ‖(x, y).1 - (x, y).2‖ from hl)] with w hw
    simp only [hLw, hΨdef, r26t8a_psiCut_one hchi hR (le_of_lt (show R / 4 < ‖w.1 - w.2‖ from hw)), one_mul,
      midPair, Function.uncurry]
    congr 1
    · module
    · module
  have hfe : iteratedFDeriv ℝ j (Function.uncurry Q) (x, y) =
      iteratedFDeriv ℝ j (fun w => Ψ (L w)) (x, y) := (hev.iteratedFDeriv ℝ j).self_of_nhds
  have hcomp := L.iteratedFDeriv_comp_right (n := (j : WithTop ℕ∞)) hΨ (x, y) (i := j) le_rfl
  have hLx : L (x, y) = (X, z) := by rw [hLw]
  have h1 : ‖iteratedFDeriv ℝ j (Function.uncurry Q) (x, y)‖ ≤ 2 ^ j * ‖iteratedFDeriv ℝ j Ψ (X, z)‖ := by
    rw [hfe]
    change ‖iteratedFDeriv ℝ j (Ψ ∘ L) (x, y)‖ ≤ _
    rw [hcomp, hLx]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    have : ∏ _i : Fin j, ‖L‖ ≤ 2 ^ j := by
      calc ∏ _i : Fin j, ‖L‖ = ‖L‖ ^ j := by simp
        _ ≤ 2 ^ j := pow_le_pow_left₀ (norm_nonneg _) hLn _
    calc ‖iteratedFDeriv ℝ j Ψ (X, z)‖ * ∏ _i : Fin j, ‖L‖ ≤ ‖iteratedFDeriv ℝ j Ψ (X, z)‖ * 2 ^ j :=
          mul_le_mul_of_nonneg_left this (norm_nonneg _)
      _ = _ := mul_comm _ _
  refine h1.trans (mul_le_mul_of_nonneg_left ((r26t8a_joint_le_nest j Ψ X z hΨ).trans ?_) (by positivity))
  refine Finset.sum_le_sum fun q hq => ?_
  have hq' : q ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hq)
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  rw [r26t8a_nest_gtilde hchi hR (F := Q) (j - q) q X z hl]
  have hb := hQ.2 (j - q) q (by omega) X z hz0
  rw [hx1, hy1] at hb
  exact hb

end HRS.MS.R26T8A
