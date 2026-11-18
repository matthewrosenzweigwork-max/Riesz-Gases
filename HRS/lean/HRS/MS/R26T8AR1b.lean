import HRS.MS.R26T8AR1a

/-!
# S8.2 T8A R1b: jets of the slice `u ↦ Q(x,u)` and of the pair function in terms of the mixed jets
`r26t8a_R1_yslice`, `r26t8a_R1_full`: `‖D^j (Q(x,·)) (y)‖`, `‖D^j (uncurry Q) (x,y)‖ ≤ 2^j ∑_q C(j,q) ‖mixedJet (j-q) q Q X z‖`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_R1_yslice {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {j : ℕ}
    {Q : Euc d → Euc d → ℝ} (hQ : ContDiffOn ℝ j (Function.uncurry Q) {p : Euc d × Euc d | p.1 ≠ p.2})
    {x y : Euc d} (hxy : x ≠ y) :
    ‖iteratedFDeriv ℝ j (Q x) y‖ ≤
      ∑ q ∈ Finset.range (j + 1), (j.choose q : ℝ) *
        ‖mixedJet (j - q) q Q ((1 / 2 : ℝ) • (x + y)) (x - y)‖ := by
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
    (r26t8a_gtilde_contDiff hchi hR hQ)
  -- the slice as a composition
  set L : Euc d →L[ℝ] Euc d × Euc d :=
    ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ (Euc d)).prod (-ContinuousLinearMap.id ℝ (Euc d)) with hL
  set c : Euc d × Euc d := ((1 / 2 : ℝ) • x, x) with hc
  have hLu : ∀ u : Euc d, L u + c = ((1 / 2 : ℝ) • (x + u), x - u) := by
    intro u; ext <;> simp [hL, hc] <;> try module
  have hLn : ‖L‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
    simp only [hL, ContinuousLinearMap.prod_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, one_mul, Prod.norm_def]
    refine max_le ?_ ?_
    · rw [norm_smul]
      have : ‖(1 / 2 : ℝ)‖ ≤ 1 := by norm_num
      nlinarith [norm_nonneg v]
    · simp
  have hopen : IsOpen {u : Euc d | R / 4 < ‖x - u‖} :=
    isOpen_lt continuous_const (continuous_norm.comp (continuous_const.sub continuous_id))
  have hev : (Q x) =ᶠ[𝓝 y] fun u => (fun w => Ψ (w + c)) (L u) := by
    filter_upwards [hopen.mem_nhds (show R / 4 < ‖x - y‖ from hl)] with u hu
    simp only [hLu, hΨdef, r26t8a_psiCut_one hchi hR (le_of_lt hu : R / 4 ≤ ‖x - u‖), one_mul, midPair]
    congr 1
    · module
    · module
  have hfe : iteratedFDeriv ℝ j (Q x) y =
      iteratedFDeriv ℝ j (fun u => (fun w => Ψ (w + c)) (L u)) y := (hev.iteratedFDeriv ℝ j).self_of_nhds
  have hsh : ContDiff ℝ (j : WithTop ℕ∞) (fun w => Ψ (w + c)) := hΨ.comp (contDiff_id.add contDiff_const)
  have hcomp := L.iteratedFDeriv_comp_right (n := (j : WithTop ℕ∞)) hsh y (i := j) le_rfl
  have hLx : L y + c = (X, z) := by rw [hLu y]
  have h1 : ‖iteratedFDeriv ℝ j (Q x) y‖ ≤ ‖iteratedFDeriv ℝ j Ψ (X, z)‖ := by
    rw [hfe]
    change ‖iteratedFDeriv ℝ j ((fun w => Ψ (w + c)) ∘ L) y‖ ≤ _
    rw [hcomp, iteratedFDeriv_comp_add_right, hLx]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    have : ∏ _i : Fin j, ‖L‖ ≤ 1 := by simpa using pow_le_one₀ (norm_nonneg L) hLn
    calc ‖iteratedFDeriv ℝ j Ψ (X, z)‖ * ∏ _i : Fin j, ‖L‖ ≤ ‖iteratedFDeriv ℝ j Ψ (X, z)‖ * 1 :=
          mul_le_mul_of_nonneg_left this (norm_nonneg _)
      _ = _ := mul_one _
  refine h1.trans ((r26t8a_joint_le_nest j Ψ X z hΨ).trans ?_)
  refine Finset.sum_le_sum fun q hq => ?_
  have hq' : q ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hq)
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  rw [r26t8a_nest_gtilde hchi hR (F := Q) (j - q) q X z hl]

theorem r26t8a_R1_full {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {j : ℕ}
    {Q : Euc d → Euc d → ℝ} (hQ : ContDiffOn ℝ j (Function.uncurry Q) {p : Euc d × Euc d | p.1 ≠ p.2})
    {x y : Euc d} (hxy : x ≠ y) :
    ‖iteratedFDeriv ℝ j (Function.uncurry Q) (x, y)‖ ≤ 2 ^ j *
      ∑ q ∈ Finset.range (j + 1), (j.choose q : ℝ) *
        ‖mixedJet (j - q) q Q ((1 / 2 : ℝ) • (x + y)) (x - y)‖ := by
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
    (r26t8a_gtilde_contDiff hchi hR hQ)
  set T : (Euc d × Euc d) →L[ℝ] (Euc d × Euc d) :=
    ((1 / 2 : ℝ) • (ContinuousLinearMap.fst ℝ (Euc d) (Euc d) + ContinuousLinearMap.snd ℝ (Euc d) (Euc d))).prod
      (ContinuousLinearMap.fst ℝ (Euc d) (Euc d) - ContinuousLinearMap.snd ℝ (Euc d) (Euc d)) with hT
  have hTu : ∀ p : Euc d × Euc d, T p = ((1 / 2 : ℝ) • (p.1 + p.2), p.1 - p.2) := fun p => by
    simp [hT]
  have hTn : ‖T‖ ≤ 2 := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun v => ?_
    rw [hTu, Prod.norm_def]
    have h1 : ‖v.1‖ ≤ ‖v‖ := by rw [Prod.norm_def]; exact le_max_left _ _
    have h2 : ‖v.2‖ ≤ ‖v‖ := by rw [Prod.norm_def]; exact le_max_right _ _
    refine max_le ?_ ?_
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      have := norm_add_le v.1 v.2
      nlinarith [norm_nonneg v]
    · have := norm_sub_le v.1 v.2
      nlinarith
  have hopen : IsOpen {p : Euc d × Euc d | R / 4 < ‖p.1 - p.2‖} :=
    isOpen_lt continuous_const (continuous_norm.comp (continuous_fst.sub continuous_snd))
  have hev : Function.uncurry Q =ᶠ[𝓝 (x, y)] fun p => Ψ (T p) := by
    filter_upwards [hopen.mem_nhds (show R / 4 < ‖(x, y).1 - (x, y).2‖ from hl)] with p hp
    have hp' : R / 4 ≤ ‖p.1 - p.2‖ := le_of_lt hp
    have e : (T p).2 = p.1 - p.2 := by rw [hTu]
    simp only [hΨdef, e, r26t8a_psiCut_one hchi hR hp', one_mul, hTu, midPair, Function.uncurry]
    congr 1
    · module
    · module
  have hfe : iteratedFDeriv ℝ j (Function.uncurry Q) (x, y) = iteratedFDeriv ℝ j (fun p => Ψ (T p)) (x, y) :=
    (hev.iteratedFDeriv ℝ j).self_of_nhds
  have hcomp := T.iteratedFDeriv_comp_right (n := (j : WithTop ℕ∞)) hΨ (x, y) (i := j) le_rfl
  have hTx : T (x, y) = (X, z) := by rw [hTu]
  have h1 : ‖iteratedFDeriv ℝ j (Function.uncurry Q) (x, y)‖ ≤ 2 ^ j * ‖iteratedFDeriv ℝ j Ψ (X, z)‖ := by
    rw [hfe]
    change ‖iteratedFDeriv ℝ j (Ψ ∘ T) (x, y)‖ ≤ _
    rw [hcomp, hTx]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    have : ∏ _i : Fin j, ‖T‖ ≤ 2 ^ j := by
      simpa using pow_le_pow_left₀ (norm_nonneg T) hTn j
    calc ‖iteratedFDeriv ℝ j Ψ (X, z)‖ * ∏ _i : Fin j, ‖T‖ ≤ ‖iteratedFDeriv ℝ j Ψ (X, z)‖ * 2 ^ j :=
          mul_le_mul_of_nonneg_left this (norm_nonneg _)
      _ = _ := mul_comm _ _
  refine h1.trans (mul_le_mul_of_nonneg_left ((r26t8a_joint_le_nest j Ψ X z hΨ).trans ?_) (by positivity))
  refine Finset.sum_le_sum fun q hq => ?_
  have hq' : q ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hq)
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  rw [r26t8a_nest_gtilde hchi hR (F := Q) (j - q) q X z hl]

end HRS.MS.R26T8A
