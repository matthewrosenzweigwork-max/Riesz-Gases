import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.MovOpAux6
import HRS.MS.S67NlBD14B

/-!
# S6.7 nonlinear breakdown, packet 44: far `C_b` force estimate from honest `L¹` domination

`s67bd_force_far_cb`: for a kernel with bounded derivatives, `κ * h` (`h ∈ L¹`) is `C^n` with
`‖D^k (κ * h)‖ ≤ K ‖h‖₁`: differentiation under the integral by induction on `n`, mirroring the weighted
`movc2_conv_far` but with the unweighted bounds `‖D^k κ‖ ≤ K` only.
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

/-- Convolution of an `L¹` function with a `C^n` kernel with bounded derivatives. -/
theorem s67bd_conv_cb (n : ℕ) : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (κ : Euc d → E) (K : ℝ) (h : Euc d → ℝ), ContDiff ℝ (n : WithTop ℕ∞) κ →
    (∀ k ≤ n, ∀ z, ‖iteratedFDeriv ℝ k κ z‖ ≤ K) → Integrable h volume →
    ContDiff ℝ (n : WithTop ℕ∞) (fun x => ∫ y, h y • κ (x - y)) ∧ ∀ k ≤ n, ∀ x,
      ‖iteratedFDeriv ℝ k (fun x => ∫ y, h y • κ (x - y)) x‖ ≤ K * ∫ y, |h y| := by
  induction n with
  | zero =>
    intro E _ _ κ K h hκ hb hI
    have hb0 : ∀ z, ‖κ z‖ ≤ K := fun z => by simpa using hb 0 le_rfl z
    have hκc : Continuous κ := by simpa using hκ.continuous
    have hK : 0 ≤ K := (norm_nonneg _).trans (hb0 0)
    have hI0 : Integrable (fun y => |h y|) volume := by simpa [Real.norm_eq_abs] using hI.norm
    have hh := hI.aestronglyMeasurable
    have hbd : ∀ x y, ‖h y • κ (x - y)‖ ≤ K * |h y| := fun x y => by
      rw [norm_smul, Real.norm_eq_abs, mul_comm]
      exact mul_le_mul_of_nonneg_right (hb0 _) (abs_nonneg _)
    refine ⟨?_, fun k hk x => ?_⟩
    · have hc : Continuous (fun x => ∫ y, h y • κ (x - y)) := by
        refine continuous_of_dominated (bound := fun y => K * |h y|) (fun x => ?_) (fun x => ?_)
          (hI0.const_mul K) (Eventually.of_forall fun y => ?_)
        · exact hh.smul (hκc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
        · exact Eventually.of_forall fun y => hbd x y
        · exact continuous_const.smul (hκc.comp (continuous_id.sub continuous_const))
      exact_mod_cast contDiff_zero.2 hc
    · have hk0 : k = 0 := by omega
      subst hk0
      rw [norm_iteratedFDeriv_zero]
      calc ‖∫ y, h y • κ (x - y)‖ ≤ ∫ y, K * |h y| :=
            norm_integral_le_of_norm_le (hI0.const_mul K) (Eventually.of_forall (hbd x))
        _ = K * ∫ y, |h y| := integral_const_mul _ _
  | succ n ih =>
    intro E _ _ κ K h hκ hb hI
    have hb0 : ∀ z, ‖κ z‖ ≤ K := fun z => by simpa using hb 0 (Nat.zero_le _) z
    have hκ1 : ContDiff ℝ 1 κ := hκ.of_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
    have hκc : Continuous κ := hκ1.continuous
    have hκd : Differentiable ℝ κ := hκ1.differentiable one_ne_zero
    have hfd : ContDiff ℝ (n : WithTop ℕ∞) (fderiv ℝ κ) := by
      have := hκ.fderiv_right (m := (n : WithTop ℕ∞)) (by push_cast; exact le_rfl)
      exact this
    have hb' : ∀ k ≤ n, ∀ z, ‖iteratedFDeriv ℝ k (fderiv ℝ κ) z‖ ≤ K := fun k hk z => by
      rw [norm_iteratedFDeriv_fderiv]
      exact hb (k + 1) (by omega) z
    have hb1 : ∀ z, ‖fderiv ℝ κ z‖ ≤ K := fun z => by
      simpa using hb' 0 (Nat.zero_le _) z
    have hfc : Continuous (fderiv ℝ κ) := by simpa using hfd.continuous
    obtain ⟨ih1, ih2⟩ := ih (Euc d →L[ℝ] E) (fderiv ℝ κ) K h hfd hb' hI
    have hK : 0 ≤ K := (norm_nonneg _).trans (hb0 0)
    have hI0 : Integrable (fun y => |h y|) volume := by simpa [Real.norm_eq_abs] using hI.norm
    have hh := hI.aestronglyMeasurable
    have hbd : ∀ x y, ‖h y • κ (x - y)‖ ≤ K * |h y| := fun x y => by
      rw [norm_smul, Real.norm_eq_abs, mul_comm]
      exact mul_le_mul_of_nonneg_right (hb0 _) (abs_nonneg _)
    -- the derivative of the convolution
    have hD : ∀ x, HasFDerivAt (fun x => ∫ y, h y • κ (x - y)) (∫ y, h y • fderiv ℝ κ (x - y)) x := by
      intro x₀
      refine hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun x y => h y • κ (x - y))
        (F' := fun x y => h y • fderiv ℝ κ (x - y)) (bound := fun y => K * |h y|) Filter.univ_mem
        (Eventually.of_forall fun x => hh.smul (hκc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
        ((hI0.const_mul K).mono'
          (hh.smul (hκc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
          (Eventually.of_forall fun y => hbd x₀ y))
        (hh.smul (hfc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
        (Eventually.of_forall fun y x _ => ?_) (hI0.const_mul K) (Eventually.of_forall fun y x _ => ?_)
      · rw [norm_smul, Real.norm_eq_abs, mul_comm]
        exact mul_le_mul_of_nonneg_right (hb1 _) (abs_nonneg _)
      · have h1 : HasFDerivAt (fun x : Euc d => x - y) (ContinuousLinearMap.id ℝ (Euc d)) x :=
          (hasFDerivAt_id x).sub_const y
        have h2 := ((hκd (x - y)).hasFDerivAt).comp x h1
        have h3 := h2.const_smul (h y)
        simp only [ContinuousLinearMap.comp_id] at h3
        exact h3
    have hfun : fderiv ℝ (fun x => ∫ y, h y • κ (x - y)) = fun x => ∫ y, h y • fderiv ℝ κ (x - y) :=
      funext fun x => (hD x).fderiv
    refine ⟨?_, fun k hk x => ?_⟩
    · have : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (fun x => ∫ y, h y • κ (x - y)) := by
        rw [Nat.cast_succ, contDiff_succ_iff_hasFDerivAt]
        exact ⟨fun x => ∫ y, h y • fderiv ℝ κ (x - y), ih1, hD⟩
      exact this
    · rcases k with _ | k
      · rw [norm_iteratedFDeriv_zero]
        calc ‖∫ y, h y • κ (x - y)‖ ≤ ∫ y, K * |h y| :=
              norm_integral_le_of_norm_le (hI0.const_mul K) (Eventually.of_forall (hbd x))
          _ = K * ∫ y, |h y| := integral_const_mul _ _
      · rw [← norm_iteratedFDeriv_fderiv, hfun]
        exact ih2 k (by omega) x

theorem s67bd_force_far_cb (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : Euc d → ℝ, Integrable h volume → ∀ i : Fin d,
      ContDiff ℝ (j : WithTop ℕ∞) (s67bd_far d s h i) ∧
      ∀ l ≤ j, ∀ x, ‖iteratedFDeriv ℝ l (s67bd_far d s h i) x‖ ≤ C * ∫ x, |h x| := by
  obtain ⟨K, hK0, hK⟩ := movc2_kfar_iter (d := d) hs0 j
  refine ⟨K, hK0, fun h hI i => ?_⟩
  have hfar : s67bd_far d s h i = fun x => ∫ y, h y • movb2_kfar d s i (x - y) := by
    funext x
    unfold s67bd_far
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp [mul_comm]
  have hκ : ContDiff ℝ (j : WithTop ℕ∞) (movb2_kfar d s i) :=
    (movc2_kfar_smooth (d := d) (s := s) i).of_le (by exact_mod_cast le_top)
  have hb : ∀ k ≤ j, ∀ z, ‖iteratedFDeriv ℝ k (movb2_kfar d s i) z‖ ≤ K := fun k hk z =>
    le_trans (le_mul_of_one_le_right (norm_nonneg _) (by linarith [norm_nonneg z])) (hK i k hk z)
  rw [hfar]
  exact s67bd_conv_cb j ℝ (movb2_kfar d s i) K h hκ hb hI

end HRS.MS.BreakdownS67
