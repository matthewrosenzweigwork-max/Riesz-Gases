import HRS.MS.SA16V1
import HRS.MS.SA16AsmA1
import HRS.MS.SA12LimitL16
import HRS.MS.UniqM1

/-!
# S.A.16 A2, part 2: a smooth function supported in a ball of radius `2` has `H^1` norm controlled by the
`L^p` norm of its first-order jet

`sa16v_sob_bound`: if `v ∈ C^∞`, `tsupport v ⊆ B(z,2)` and `‖(‖wJet 1 v‖)‖_{L^p} ≤ b` then
`‖v‖_{H^1} ≤ √(1+d³) K₁ b`, with `K₁ = |B(0,2)|^{1/2-1/p}` (Hölder from `L^p` to `L²` on a ball).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16V
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16

section Part2
variable {d : ℕ}

/-- Hölder constant from `L^p` to `L²` on a ball of radius `2` -/
def sa16v_K1 (d : ℕ) (p : ℝ) : ℝ := ((volume (Metric.ball (0 : Euc d) 2)).toReal) ^ (1 / 2 - 1 / p)

lemma sa16v_K1_nonneg (d : ℕ) (p : ℝ) : 0 ≤ sa16v_K1 d p :=
  Real.rpow_nonneg ENNReal.toReal_nonneg _

lemma sa16v_vanish {v : Euc d → ℝ} {z : Euc d} (hsupp : tsupport v ⊆ Metric.ball z 2) (m : ℕ)
    {x : Euc d} (hx : x ∉ Metric.ball z 2) : ‖wJet m v x‖ = 0 := by
  have hx' : x ∉ tsupport v := fun h => hx (hsupp h)
  have : wJet m v x = 0 := by
    funext τ
    have h0 : iteratedFDeriv ℝ (τ.1 : ℕ) v x = 0 := by
      by_contra hne
      exact hx' (support_iteratedFDeriv_subset (𝕜 := ℝ) (τ.1 : ℕ) hne)
    simp [wJet, partialDeriv, h0]
  rw [this]; simp

/-- pointwise bounds by the first-order jet norm -/
lemma sa16v_jet_bounds {v : Euc d → ℝ} (hv : ContDiff ℝ ∞ v) (x : Euc d) :
    |v x| ≤ ‖wJet 1 v x‖ ∧ sa16v_grad v x ≤ (d : ℝ) * ‖wJet 1 v x‖ := by
  refine ⟨?_, ?_⟩
  · have h := norm_le_pi_norm (wJet 1 v x) (wZero d 1)
    simpa [wJet, wZero, sa16j_pd_zero] using h
  · have hpd : ∀ i : Fin d, |fderiv ℝ v x (EuclideanSpace.single i (1 : ℝ))| ≤ ‖wJet 1 v x‖ := by
      intro i
      have h := norm_le_pi_norm (wJet 1 v x) (⟨⟨1, by omega⟩, fun _ => i⟩ : WIndex d 1)
      have e : wJet 1 v x (⟨⟨1, by omega⟩, fun _ => i⟩ : WIndex d 1) =
          fderiv ℝ v x (EuclideanSpace.single i (1 : ℝ)) := by
        have := congrFun (sa16y_pd1_eq v hv i) x
        simpa [wJet] using this
      rw [e] at h
      simpa [Real.norm_eq_abs] using h
    unfold sa16v_grad
    calc ∑ i : Fin d, |fderiv ℝ v x (EuclideanSpace.single i (1 : ℝ))| ≤ ∑ i : Fin d, ‖wJet 1 v x‖ :=
          Finset.sum_le_sum fun i _ => hpd i
      _ = (d : ℝ) * ‖wJet 1 v x‖ := by simp

/-- Hölder from `L^p` to `L²` on the ball for a function vanishing off the ball -/
lemma sa16v_L2_bound (p : ℝ) [Fact (2 ≤ p)] {F : Euc d → ℝ} (hFc : Continuous F) {z : Euc d}
    (hF0 : ∀ x, x ∉ Metric.ball z 2 → F x = 0) {b : ℝ} (hb0 : 0 ≤ b)
    (hF : eLpNorm F (ENNReal.ofReal p) volume ≤ ENNReal.ofReal b) :
    ∫ x, F x ^ 2 ≤ (sa16v_K1 d p * b) ^ 2 := by
  have hp2 : (2 : ℝ) ≤ p := Fact.out
  have hmeasF : AEStronglyMeasurable F volume := hFc.aestronglyMeasurable
  have hcl : IsCompact (Metric.closedBall z 2) := isCompact_closedBall z 2
  have hFcs : HasCompactSupport F :=
    HasCompactSupport.intro hcl (fun x hx => hF0 x (fun h => hx (Metric.ball_subset_closedBall h)))
  have hF2c : Continuous (fun x => F x ^ 2) := hFc.pow 2
  set ν : Measure (Euc d) := volume.restrict (Metric.ball z 2) with hν
  have hsuppF : F.support ⊆ Metric.ball z 2 := fun x hx => by
    by_contra h; exact hx (hF0 x h)
  have hres : ∀ q : ℝ≥0∞, eLpNorm F q ν = eLpNorm F q volume := fun q =>
    eLpNorm_restrict_eq_of_support_subset hmeasF hsuppF
  have hVfin : volume (Metric.ball z 2) < ⊤ := measure_ball_lt_top
  have hball : volume (Metric.ball z 2) = volume (Metric.ball (0 : Euc d) 2) :=
    Measure.addHaar_ball_center _ _ _
  have hholder : eLpNorm F 2 volume ≤ ENNReal.ofReal (sa16v_K1 d p * b) := by
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := ν) (p := 2) (q := ENNReal.ofReal p)
      (by simpa using ENNReal.ofReal_le_ofReal hp2) hmeasF.restrict
    rw [hres, hres] at h
    refine h.trans ?_
    have hν1 : ν Set.univ = volume (Metric.ball (0 : Euc d) 2) := by
      rw [hν, Measure.restrict_apply_univ, hball]
    rw [hν1]
    have hexp : 0 ≤ 1 / (2 : ℝ≥0∞).toReal - 1 / (ENNReal.ofReal p).toReal := by
      rw [ENNReal.toReal_ofReal (by linarith)]
      simp only [ENNReal.toReal_ofNat]
      have : 1 / p ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
      linarith
    have hV2 : volume (Metric.ball (0 : Euc d) 2) ≠ ⊤ := by
      rw [← hball]; exact hVfin.ne
    have hK : volume (Metric.ball (0 : Euc d) 2) ^ (1 / (2 : ℝ≥0∞).toReal - 1 / (ENNReal.ofReal p).toReal) =
        ENNReal.ofReal (sa16v_K1 d p) := by
      rw [sa16v_K1, ← ENNReal.ofReal_toReal hV2, ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hexp]
      simp only [ENNReal.toReal_ofNat, ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ p), ENNReal.ofReal_toReal hV2]
    rw [hK, mul_comm (sa16v_K1 d p) b, ENNReal.ofReal_mul hb0]
    exact mul_le_mul' hF le_rfl
  have hlin : ∫⁻ x, ENNReal.ofReal (F x ^ 2) = eLpNorm F 2 volume ^ 2 := by
    rw [HRS.MS.UniqM1.sq_eLpNorm_two hmeasF]
    refine lintegral_congr fun x => ?_
    rw [← ofReal_norm, Real.norm_eq_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  have hEl : ∫ x, F x ^ 2 = (∫⁻ x, ENNReal.ofReal (F x ^ 2)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x => sq_nonneg _)
      hF2c.aestronglyMeasurable
  rw [hEl, hlin]
  have hbd : eLpNorm F 2 volume ^ 2 ≤ ENNReal.ofReal ((sa16v_K1 d p * b) ^ 2) := by
    rw [ENNReal.ofReal_pow (mul_nonneg (sa16v_K1_nonneg d p) hb0)]
    exact pow_le_pow_left' hholder 2
  exact ENNReal.toReal_le_of_le_ofReal (sq_nonneg _) hbd

lemma sa16v_sob_bound (p : ℝ) [Fact (2 ≤ p)] {v : Euc d → ℝ} (hv : ContDiff ℝ ∞ v) {z : Euc d}
    (hsupp : tsupport v ⊆ Metric.ball z 2) {b : ℝ} (hb0 : 0 ≤ b)
    (hF : eLpNorm (fun x => ‖wJet 1 v x‖) (ENNReal.ofReal p) volume ≤ ENNReal.ofReal b) :
    sobolevNormE 1 v ≤ ENNReal.ofReal (Real.sqrt (1 + (d : ℝ) ^ 3) * sa16v_K1 d p * b) := by
  set F : Euc d → ℝ := fun x => ‖wJet 1 v x‖ with hFdef
  have hv1 : ContDiff ℝ 1 v := hv.of_le (by exact_mod_cast le_top)
  have hFc : Continuous F := (sa16j_jet_cont hv 1).norm
  have hcl : IsCompact (Metric.closedBall z 2) := isCompact_closedBall z 2
  have hc : HasCompactSupport v :=
    IsCompact.of_isClosed_subset hcl (isClosed_tsupport v) (hsupp.trans Metric.ball_subset_closedBall)
  have hF0 : ∀ x, x ∉ Metric.ball z 2 → F x = 0 := fun x hx => sa16v_vanish hsupp 1 hx
  have hFcs : HasCompactSupport F :=
    HasCompactSupport.intro hcl (fun x hx => hF0 x (fun h => hx (Metric.ball_subset_closedBall h)))
  have hF2c : Continuous (fun x => F x ^ 2) := hFc.pow 2
  have hF2cs : HasCompactSupport (fun x => F x ^ 2) := hFcs.comp_left (g := fun r : ℝ => r ^ 2) (by simp)
  have hF2i : Integrable (fun x => F x ^ 2) volume := hF2c.integrable_of_hasCompactSupport hF2cs
  have hgrad : ∀ x, sa16v_grad v x ^ 2 ≤ ((d : ℝ) ^ 2) * F x ^ 2 := by
    intro x
    have h1 := (sa16v_jet_bounds hv x).2
    calc sa16v_grad v x ^ 2 ≤ ((d : ℝ) * F x) ^ 2 :=
          pow_le_pow_left₀ (sa16v_grad_nonneg v x) h1 2
      _ = ((d : ℝ) ^ 2) * F x ^ 2 := by ring
  obtain ⟨hmem, hnorm⟩ := sa16v_h1 hv1 hc
  have hvc2 : Integrable (fun x => v x ^ 2) volume := by
    have : MemLp v 2 volume := hv1.continuous.memLp_of_hasCompactSupport hc
    exact this.integrable_sq
  have hgs2 : HasCompactSupport (fun y => sa16v_grad v y ^ 2) :=
    (sa16v_grad_support hc).comp_left (g := fun r : ℝ => r ^ 2) (by simp)
  have hg2i : Integrable (fun y => sa16v_grad v y ^ 2) volume :=
    ((sa16v_grad_cont hv1).pow 2).integrable_of_hasCompactSupport hgs2
  set E : ℝ := ∫ x, F x ^ 2 with hE
  have h1 : ∫ x, v x ^ 2 ≤ E :=
    integral_mono hvc2 hF2i fun x => by
      have := (sa16v_jet_bounds hv x).1
      calc v x ^ 2 = |v x| ^ 2 := (sq_abs _).symm
        _ ≤ F x ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
  have h2 : ∫ y, sa16v_grad v y ^ 2 ≤ (d : ℝ) ^ 2 * E := by
    rw [hE, ← integral_const_mul]
    exact integral_mono hg2i (hF2i.const_mul _) hgrad
  have hsq : HRS.PDE.ToolboxRd.sobolevNormSq 1 v ≤ (1 + (d : ℝ) ^ 3) * E := by
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    nlinarith [hnorm, h1, h2, mul_le_mul_of_nonneg_left h2 hd0]
  have hE' : E ≤ (sa16v_K1 d p * b) ^ 2 := sa16v_L2_bound p hFc hF0 hb0 hF
  have hdd : (0 : ℝ) ≤ 1 + (d : ℝ) ^ 3 := by positivity
  have hfin : HRS.PDE.ToolboxRd.sobolevNormSq 1 v ≤
      (Real.sqrt (1 + (d : ℝ) ^ 3) * sa16v_K1 d p * b) ^ 2 := by
    have e : (Real.sqrt (1 + (d : ℝ) ^ 3) * sa16v_K1 d p * b) ^ 2 = (1 + (d : ℝ) ^ 3) * (sa16v_K1 d p * b) ^ 2 := by
      rw [mul_assoc, mul_pow, Real.sq_sqrt hdd]
    rw [e]
    exact hsq.trans (mul_le_mul_of_nonneg_left hE' hdd)
  exact HRS.MH.AdjointRd.Phase2SA12Limit.sa12x_sobE_of_le
    (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (sa16v_K1_nonneg d p)) hb0) hmem hfin

end Part2

end HRS.Whole.AppendixA.Phase2SA16V
