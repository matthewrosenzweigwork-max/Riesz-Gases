import HRS.MS.R26T8AZ4b
import HRS.MS.R26T8AP15j
import HRS.MS.R26T8AP11lb
import HRS.MS.R26T8AP06b

/-!
# S8.2 T8A Z5c: mixed jets of order `q+1` from the jets of the partial derivatives
`r26t8a_Z5c_jets`: if for `0 < |w| < 1` the slice `w ↦ midPair R0 X w` is differentiable with `∂_{e_i}` equal to `midPair (Ri i) X w`, then for
`0 < |z| < 1/2`: `‖mixedJet p (q+1) R0 X z‖ ≤ Σ_i ‖mixedJet p q (Ri i) X z‖` (`p + q ≤ k'`, `R0` is `C^{k'+1}`, `Ri` are `C^{k'}` off the diagonal).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_Z5c_nest_congr_ball {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (p q : ℕ)
    (Φ Φ' : Euc d × Euc d → V) {ρ : ℝ} (hρ : 0 < ρ) (X z : Euc d)
    (hΦ : ∀ Y w : Euc d, ‖w - z‖ < ρ → Φ (Y, w) = Φ' (Y, w)) :
    r26t8a_nest p q Φ X z = r26t8a_nest p q Φ' X z := by
  unfold r26t8a_nest
  have h : ∀ Y : Euc d, iteratedFDeriv ℝ q (fun w => Φ (Y, w)) z = iteratedFDeriv ℝ q (fun w => Φ' (Y, w)) z := by
    intro Y
    have hev : (fun w => Φ (Y, w)) =ᶠ[𝓝 z] fun w => Φ' (Y, w) := by
      filter_upwards [ball_mem_nhds z hρ] with w hw
      exact hΦ Y w (by simpa [dist_eq_norm] using hw)
    exact (hev.iteratedFDeriv ℝ q).self_of_nhds
  simp only [h]

/-- `c ↦ c • proj_i`. -/
def r26t8a_Z5c_L (d : ℕ) (i : Fin d) : ℝ →L[ℝ] (Euc d →L[ℝ] ℝ) :=
  ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)

theorem r26t8a_Z5c_L_norm (i : Fin d) (c : ℝ) : ‖r26t8a_Z5c_L d i c‖ ≤ ‖c‖ := by
  unfold r26t8a_Z5c_L
  rw [ContinuousLinearMap.toSpanSingleton_apply, norm_smul]
  have h2 : ‖(EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
    show ‖v i‖ ≤ 1 * ‖v‖
    rw [one_mul, Real.norm_eq_abs]; exact r26t8a_abs_coord_le v i
  calc ‖c‖ * ‖(EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)‖ ≤ ‖c‖ * 1 := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = ‖c‖ := mul_one _

theorem r26t8a_Z5c_clm_expand (T : Euc d →L[ℝ] ℝ) :
    T = ∑ i : Fin d, r26t8a_Z5c_L d i (T (r26t8a_e d i)) := by
  ext u
  rw [r26t8a_clm_expand T u]
  simp [r26t8a_Z5c_L, ContinuousLinearMap.sum_apply, mul_comm]

theorem r26t8a_Z5c_sum_bound (p q : ℕ) (X z : Euc d) (Θ : Fin d → Euc d × Euc d → ℝ)
    (hΘ : ∀ i, ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (Θ i)) (s : Finset (Fin d)) :
    ‖r26t8a_nest p q (fun Yw => ∑ i ∈ s, r26t8a_Z5c_L d i (Θ i Yw)) X z‖ ≤
      ∑ i ∈ s, ‖r26t8a_nest p q (Θ i) X z‖ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have : r26t8a_nest p q (fun Yw : Euc d × Euc d => ∑ i ∈ (∅ : Finset (Fin d)), r26t8a_Z5c_L d i (Θ i Yw)) X z = 0 := by
      unfold r26t8a_nest
      simp [iteratedFDeriv_fun_zero]
    rw [this]; simp
  | insert j s hj ih =>
    have e : (fun Yw : Euc d × Euc d => ∑ i ∈ insert j s, r26t8a_Z5c_L d i (Θ i Yw)) =
        fun Yw => r26t8a_Z5c_L d j (Θ j Yw) + ∑ i ∈ s, r26t8a_Z5c_L d i (Θ i Yw) := by
      funext Yw; rw [Finset.sum_insert hj]
    have h1 : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (fun Yw => r26t8a_Z5c_L d j (Θ j Yw)) :=
      (r26t8a_Z5c_L d j).contDiff.comp (hΘ j)
    have h2 : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (fun Yw => ∑ i ∈ s, r26t8a_Z5c_L d i (Θ i Yw)) :=
      ContDiff.sum fun i _ => (r26t8a_Z5c_L d i).contDiff.comp (hΘ i)
    rw [e, r26t8a_nest_add p q z X h1 h2, Finset.sum_insert hj]
    refine (norm_add_le _ _).trans (add_le_add ?_ ih)
    exact (r26t8a_nest_clm' (r26t8a_Z5c_L d j) (r26t8a_Z5c_L_norm j) p q (Θ j) X z (hΘ j))

theorem r26t8a_Z5c_jets {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {k' : ℕ} {R0 : Euc d → Euc d → ℝ}
    (Ri : Fin d → Euc d → Euc d → ℝ)
    (hR0 : ContDiffOn ℝ ((k' + 1 : ℕ) : WithTop ℕ∞) (Function.uncurry R0) {p : Euc d × Euc d | p.1 ≠ p.2})
    (hRi : ∀ i, ContDiffOn ℝ (k' : WithTop ℕ∞) (Function.uncurry (Ri i)) {p : Euc d × Euc d | p.1 ≠ p.2})
    (hder : ∀ X w : Euc d, w ≠ 0 → ‖w‖ < 1 → DifferentiableAt ℝ (fun w' => midPair R0 X w') w ∧
      ∀ i, fderiv ℝ (fun w' => midPair R0 X w') w (r26t8a_e d i) = midPair (Ri i) X w)
    (p q : ℕ) (hpq : p + q ≤ k') (X z : Euc d) (hz : z ≠ 0) (hz1 : ‖z‖ < 1 / 2) :
    ‖mixedJet p (q + 1) R0 X z‖ ≤ ∑ i : Fin d, ‖mixedJet p q (Ri i) X z‖ := by
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
  set R : ℝ := 2 * ‖z‖ with hR
  have hRp : 0 < R := by rw [hR]; positivity
  have hlt : R / 4 < ‖z‖ := by rw [hR]; linarith
  set Φ0 : Euc d × Euc d → ℝ := fun Yw => r26t8a_psiCut chi R Yw.2 * midPair R0 Yw.1 Yw.2 with hΦ0
  have hΦ0c : ContDiff ℝ ((k' + 1 : ℕ) : WithTop ℕ∞) Φ0 := r26t8a_gtilde_contDiff hchi hRp hR0
  set Θ : Fin d → Euc d × Euc d → ℝ := fun i Yw => r26t8a_psiCut chi R Yw.2 * midPair (Ri i) Yw.1 Yw.2 with hΘ
  have hΘc : ∀ i, ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (Θ i) := fun i =>
    (r26t8a_gtilde_contDiff hchi hRp (hRi i)).of_le (by exact_mod_cast hpq)
  have h1 : mixedJet p (q + 1) R0 X z = r26t8a_nest p (q + 1) Φ0 X z :=
    (r26t8a_nest_gtilde hchi hRp (F := R0) p (q + 1) X z hlt).symm
  have h2 : ∀ i, mixedJet p q (Ri i) X z = r26t8a_nest p q (Θ i) X z := fun i =>
    (r26t8a_nest_gtilde hchi hRp (F := Ri i) p q X z hlt).symm
  rw [h1, r26t8a_nest_succ p q Φ0 X z]
  have hcongr : r26t8a_nest p q (r26t8a_dw Φ0) X z =
      r26t8a_nest p q (fun Yw => ∑ i : Fin d, r26t8a_Z5c_L d i (Θ i Yw)) X z := by
    refine r26t8a_Z5c_nest_congr_ball p q _ _ (ρ := ‖z‖ / 4) (by positivity) X z (fun Y w hw => ?_)
    have hwn : 3 * ‖z‖ / 4 < ‖w‖ := by
      have := norm_sub_norm_le z w
      rw [norm_sub_rev] at this
      linarith
    have hwn1 : ‖w‖ < 1 := by
      have := norm_le_norm_add_norm_sub' w z
      linarith
    have hw0 : w ≠ 0 := by
      intro h; rw [h, norm_zero] at hwn; linarith
    have hψ : ∀ w' : Euc d, R / 4 ≤ ‖w'‖ → r26t8a_psiCut chi R w' = 1 := fun w' hw' =>
      r26t8a_psiCut_one hchi hRp hw'
    have hev : (fun w' : Euc d => Φ0 (Y, w')) =ᶠ[𝓝 w] fun w' => midPair R0 Y w' := by
      filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds
        (show R / 4 < ‖w‖ by rw [hR]; linarith)] with w' hw'
      simp only [hΦ0, hψ w' hw'.le, one_mul]
    obtain ⟨-, hder2⟩ := hder Y w hw0 hwn1
    have hdw : r26t8a_dw Φ0 (Y, w) = fderiv ℝ (fun w' => midPair R0 Y w') w := by
      unfold r26t8a_dw
      exact hev.fderiv_eq
    rw [hdw]
    conv_lhs => rw [r26t8a_Z5c_clm_expand (fderiv ℝ (fun w' => midPair R0 Y w') w)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hder2 i]
    simp only [hΘ, hψ w (by rw [hR]; linarith), one_mul]
  rw [hcongr]
  refine (r26t8a_Z5c_sum_bound p q X z Θ hΘc Finset.univ).trans (le_of_eq ?_)
  exact Finset.sum_congr rfl fun i _ => by rw [h2 i]

end HRS.MS.R26T8A
