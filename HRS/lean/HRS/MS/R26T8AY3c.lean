import HRS.MS.R26T8AY3b0
import HRS.MS.R26T8AZ5a3
import HRS.MS.R26T8AP06d7

/-!
# S8.2 T8A Y3c: the fixed-`y` slices of a `Conormal 1` function of negative order, supported in `|x-y| ≤ 1/2`
`r26t8a_Y3c_slice`: for such `P` and every `y`, `v ↦ P(y+v,y)` is bounded and its derivative is `≤ c1 |v|^{-1}` (`c0, c1` depend on `P, y`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

set_option maxHeartbeats 3200000 in
theorem r26t8a_Y3c_slice {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (b : ℕ) (M σ : ℝ) (hM : 0 ≤ M) (hσ : σ < 0)
    {A : ℝ} (hA : 0 ≤ A) {P : Euc d → Euc d → ℝ} (hP : Conormal 1 b M σ A P)
    (hsupp : ∀ x y : Euc d, 1 / 2 ≤ ‖x - y‖ → P x y = 0) (y : Euc d) :
    ∃ c0 c1 : ℝ, (∀ v : Euc d, v ≠ 0 → |P (y + v) y| ≤ c0) ∧
      (∀ v : Euc d, v ≠ 0 → ‖fderiv ℝ (fun v => P (y + v) y) v‖ ≤ c1 * ‖v‖ ^ (-(1 : ℝ))) := by
  obtain ⟨c, hc0, hc⟩ := r26t8a_Z5a1_log_bound (a := -σ) (by linarith) b
  have hcont : Continuous (fun v : Euc d => HRS.MS.Phase2S82.pairWeight M (y + v) y) := by
    unfold HRS.MS.Phase2S82.pairWeight
    exact (((r26t8a_jbracket_continuous (d := d)).comp (continuous_const.add continuous_id)).rpow_const
      (fun x => Or.inr hM)).mul continuous_const
  obtain ⟨W, hW⟩ := (isCompact_closedBall (0 : Euc d) (1 / 2)).exists_bound_of_continuousOn hcont.continuousOn
  have hpw0 : ∀ v : Euc d, 0 ≤ HRS.MS.Phase2S82.pairWeight M (y + v) y := fun v =>
    mul_nonneg (Real.rpow_nonneg (s83_jb_pos _).le _) (Real.rpow_nonneg (s83_jb_pos _).le _)
  have hW0 : 0 ≤ W := (norm_nonneg _).trans (hW 0 (by simp))
  have hj : ∀ p q : ℕ, p + q ≤ 1 → ∀ v : Euc d, v ≠ 0 → ‖v‖ ≤ 1 / 2 →
      ‖mixedJet p q P (y + (1 / 2 : ℝ) • v) v‖ ≤ A * W * ((1 + c) * ‖v‖ ^ (-(q : ℝ))) := by
    intro p q hpq v hv hv2
    have hvn : 0 < ‖v‖ := norm_pos_iff.2 hv
    have hb := hP.2 p q hpq (y + (1 / 2 : ℝ) • v) v hv
    have hmin : min 1 ‖v‖ = ‖v‖ := min_eq_right (by linarith)
    have e1 : y + (1 / 2 : ℝ) • v + (1 / 2 : ℝ) • v = y + v := by module
    have e2 : y + (1 / 2 : ℝ) • v - (1 / 2 : ℝ) • v = y := by module
    rw [hmin, e1, e2] at hb
    have hWv : HRS.MS.Phase2S82.pairWeight M (y + v) y ≤ W := by
      have := hW v (by simpa using hv2)
      exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs, abs_of_nonneg (hpw0 v)] using this)
    have hcc := hc ‖v‖ hvn (by linarith)
    have hsplit : ‖v‖ ^ (-(σ + (q : ℝ))) = ‖v‖ ^ (-σ) * ‖v‖ ^ (-(q : ℝ)) := by
      rw [← Real.rpow_add hvn]; congr 1; ring
    have hr1 : 1 ≤ ‖v‖ ^ (-(q : ℝ)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hvn (by linarith) (by simp)
    have hr0 : 0 ≤ ‖v‖ ^ (-(q : ℝ)) := by linarith
    have h1 : 1 + ‖v‖ ^ (-(σ + (q : ℝ))) * (1 + |Real.log ‖v‖|) ^ b ≤ (1 + c) * ‖v‖ ^ (-(q : ℝ)) := by
      rw [hsplit]
      have : ‖v‖ ^ (-σ) * (1 + |Real.log ‖v‖|) ^ b ≤ c := hcc
      nlinarith [mul_le_mul_of_nonneg_right this hr0]
    refine hb.trans ?_
    have h1' : 0 ≤ 1 + ‖v‖ ^ (-(σ + (q : ℝ))) * (1 + |Real.log ‖v‖|) ^ b := by positivity
    exact mul_le_mul (mul_le_mul_of_nonneg_left hWv hA) h1 h1' (mul_nonneg hA hW0)
  refine ⟨A * W * (1 + c), d * (2 * (A * W * (1 + c))), fun v hv => ?_, fun v hv => ?_⟩
  · by_cases hv2 : ‖v‖ ≤ 1 / 2
    · have h := hj 0 0 (by norm_num) v hv hv2
      have e0 : ‖mixedJet 0 0 P (y + (1 / 2 : ℝ) • v) v‖ = |P (y + v) y| := by
        unfold mixedJet; simp [norm_iteratedFDeriv_zero, midPair]
        congr 2 <;> module
      rw [e0] at h
      simpa using h
    · push Not at hv2
      rw [hsupp (y + v) y (by simp; linarith), abs_zero]
      positivity
  · by_cases hv2 : ‖v‖ ≤ 1 / 2
    · have hvn : 0 < ‖v‖ := norm_pos_iff.2 hv
      have hyv : y + v ≠ y := by intro h; apply hv; simpa using h
      have hF1 : ContDiffOn ℝ ((0 + 1 : ℕ) : WithTop ℕ∞) (Function.uncurry P) {p : Euc d × Euc d | p.1 ≠ p.2} := by
        simpa using hP.1
      have hopen : IsOpen {p : Euc d × Euc d | p.1 ≠ p.2} := isOpen_ne_fun continuous_fst continuous_snd
      have hdiff : DifferentiableAt ℝ (fun x' => P x' y) (y + v) := by
        have h1 : DifferentiableAt ℝ (Function.uncurry P) (y + v, y) :=
          ((hP.1.contDiffAt (hopen.mem_nhds hyv))).differentiableAt (by norm_num)
        have h2 : DifferentiableAt ℝ (fun x' : Euc d => (x', y)) (y + v) :=
          differentiableAt_id.prodMk (differentiableAt_const y)
        exact DifferentiableAt.comp (g := Function.uncurry P) (f := fun x' : Euc d => (x', y)) (y + v) h1 h2
      have hfd : fderiv ℝ (fun v => P (y + v) y) v = fderiv ℝ (fun x' => P x' y) (y + v) := by
        rw [show (fun v => P (y + v) y) = (fun x' => P x' y) ∘ (fun v => y + v) from rfl]
        have := hdiff.hasFDerivAt.comp v ((hasFDerivAt_id v).const_add y)
        rw [this.fderiv]; simp
      rw [hfd]
      set T := fderiv ℝ (fun x' => P x' y) (y + v) with hT
      have hTn : ‖T‖ ≤ ∑ i : Fin d, ‖T (r26t8a_e d i)‖ := by
        conv_lhs => rw [r26t8a_Z5c_clm_expand T]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => r26t8a_Z5c_L_norm i _ |>.trans le_rfl)
      have hTi : ∀ i : Fin d, ‖T (r26t8a_e d i)‖ ≤ 2 * (A * W * (1 + c)) * ‖v‖ ^ (-(1 : ℝ)) := by
        intro i
        have hsplit := r26t8a_Y3b0_dx_split hF1 i hyv
        have hTe : T (r26t8a_e d i) = r26t8a_dx i P (y + v) y := rfl
        rw [hTe, hsplit]
        set X := y + (1 / 2 : ℝ) • v with hX
        have eq1 : ∀ G : Euc d → Euc d → ℝ, ‖mixedJet 0 0 G X v‖ = |G (y + v) y| := by
          intro G
          unfold mixedJet; simp [norm_iteratedFDeriv_zero, midPair, hX]
          congr 2 <;> module
        have hG := r26t8a_pdir_jet_Z hchi hF1 (r26t8a_e d i) (le_of_eq (r26t8a_e_norm i)) 0 0 (le_refl _) X v hv
        have hH := r26t8a_pdir_jet_X hchi hF1 ((1 / 2 : ℝ) • r26t8a_e d i) (by
          rw [norm_smul, r26t8a_e_norm]; norm_num) 0 0 (le_refl _) X v hv
        rw [eq1] at hG hH
        have j01 := hj 0 1 (by norm_num) v hv hv2
        have j10 := hj 1 0 (by norm_num) v hv hv2
        have hr1 : 1 ≤ ‖v‖ ^ (-(1 : ℝ)) :=
          Real.one_le_rpow_of_pos_of_le_one_of_nonpos hvn (by linarith) (by norm_num)
        have hAWc : 0 ≤ A * W * (1 + c) := by positivity
        have j01' : ‖mixedJet 0 1 P X v‖ ≤ A * W * (1 + c) * ‖v‖ ^ (-(1 : ℝ)) := by
          have := j01; simp only [Nat.cast_one] at this; linarith
        have j10' : ‖mixedJet 1 0 P X v‖ ≤ A * W * (1 + c) * ‖v‖ ^ (-(1 : ℝ)) := by
          have e0 : ‖v‖ ^ (-((0 : ℕ) : ℝ)) = 1 := by simp
          have h10 : ‖mixedJet 1 0 P X v‖ ≤ A * W * ((1 + c) * ‖v‖ ^ (-((0 : ℕ) : ℝ))) := j10
          rw [e0] at h10
          have h11 := mul_le_mul_of_nonneg_left hr1 hAWc
          calc ‖mixedJet 1 0 P X v‖ ≤ A * W * ((1 + c) * 1) := h10
            _ = A * W * (1 + c) * 1 := by ring
            _ ≤ _ := h11
        calc |r26t8a_pdir (0, r26t8a_e d i) P (y + v) y + r26t8a_pdir ((1 / 2 : ℝ) • r26t8a_e d i, 0) P (y + v) y|
            ≤ |r26t8a_pdir (0, r26t8a_e d i) P (y + v) y| + |r26t8a_pdir ((1 / 2 : ℝ) • r26t8a_e d i, 0) P (y + v) y| :=
              abs_add_le _ _
          _ ≤ A * W * (1 + c) * ‖v‖ ^ (-(1 : ℝ)) + A * W * (1 + c) * ‖v‖ ^ (-(1 : ℝ)) :=
              add_le_add (hG.trans (by simpa using j01')) (hH.trans (by exact j10'))
          _ = _ := by ring
      calc ‖T‖ ≤ ∑ i : Fin d, ‖T (r26t8a_e d i)‖ := hTn
        _ ≤ ∑ _i : Fin d, 2 * (A * W * (1 + c)) * ‖v‖ ^ (-(1 : ℝ)) := Finset.sum_le_sum fun i _ => hTi i
        _ = _ := by simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring
    · push Not at hv2
      have : (fun v => P (y + v) y) =ᶠ[𝓝 v] fun _ => 0 := by
        have hopen : IsOpen {u : Euc d | 1 / 2 < ‖u‖} := isOpen_lt continuous_const continuous_norm
        filter_upwards [hopen.mem_nhds hv2] with u hu
        exact hsupp (y + u) y (by simp only [add_sub_cancel_left]; exact hu.le)
      rw [this.fderiv_eq, fderiv_const_apply, norm_zero]
      have : 0 ≤ ‖v‖ ^ (-(1 : ℝ)) := Real.rpow_nonneg (norm_nonneg _) _
      positivity

end HRS.MS.R26T8A
