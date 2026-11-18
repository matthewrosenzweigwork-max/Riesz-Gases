import HRS.MS.MfeConfAux52

/-!
# S.B.1, packet F6 (part 15): the initial Jensen bound for a non-confining reference

`sb1_init_jensen`: for a reference `q = exp(-U/θ)` of mass one with `∇U = -b₀` (`b₀` Lipschitz) and `U` bounded below, a
probability law `μ` with a finite second moment and `klDiv μ (q dx) ≠ ⊤`:
`∫ (u log u + u U/θ) ≤ (klDiv μ (q dx)).toReal + e(v)`, `u = G_v * μ`, `e(v) → 0` (transplant of `p4_initial_jensen_proof`
without the Gaussian majorant of the reference).
-/

open MeasureTheory Filter Topology InformationTheory
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Mol HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MS.MfeConf

variable {d N : ℕ}

theorem sb1_descent {U : EucConfig d N → ℝ} {b0 : EucConfig d N → EucConfig d N} {K : ℝ≥0}
    (hU : ∀ x, HasFDerivAt U (-(p4InnerL (b0 x))) x) (hb : LipschitzWith K b0) (x w : EucConfig d N) :
    |U (x + w) - U x + p4InnerL (b0 x) w| ≤ N * K * p4j_Phi w := by
  set g : ℝ → ℝ := fun s => U (x + s • w) with hg
  set g' : ℝ → ℝ := fun s => -(p4InnerL (b0 (x + s • w)) w) with hg'
  have hd : ∀ s : ℝ, HasDerivAt g (g' s) s := by
    intro s
    have h1 : HasDerivAt (fun s : ℝ => x + s • w) w s := by
      simpa using ((hasDerivAt_id s).smul_const w).const_add x
    have := (hU (x + s • w)).comp_hasDerivAt s h1
    simp only [hg, hg']
    exact this
  have hc : Continuous g' := by
    have h1 : Continuous fun s : ℝ => b0 (x + s • w) :=
      hb.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))
    simp only [hg']
    exact ((p4j_innerL_continuous w).comp h1).neg
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    (hc.intervalIntegrable 0 1)
  have hg1 : g 1 = U (x + w) := by simp [hg]
  have hg0 : g 0 = U x := by simp [hg]
  have hdiff : U (x + w) - U x + p4InnerL (b0 x) w =
      ∫ s in (0 : ℝ)..1, (g' s + p4InnerL (b0 x) w) := by
    rw [intervalIntegral.integral_add (hc.intervalIntegrable 0 1) intervalIntegrable_const, hftc, hg1, hg0]
    simp
  rw [hdiff]
  have hbd : ∀ s ∈ Set.Ioc (0 : ℝ) 1, ‖g' s + p4InnerL (b0 x) w‖ ≤ N * K * ‖w‖ ^ 2 * s := by
    intro s hs
    have e : g' s + p4InnerL (b0 x) w = p4InnerL (b0 x - b0 (x + s • w)) w := by
      rw [p4j_innerL_sub]; simp only [hg']; ring
    rw [e, Real.norm_eq_abs]
    refine (p4j_innerL_bound _ _).trans ?_
    have hl : ‖b0 x - b0 (x + s • w)‖ ≤ K * (s * ‖w‖) := by
      have := hb.dist_le_mul x (x + s • w)
      rw [dist_eq_norm, dist_eq_norm] at this
      have e2 : ‖x - (x + s • w)‖ = s * ‖w‖ := by
        rw [sub_add_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hs.1]
      rwa [e2] at this
    calc (N : ℝ) * ‖b0 x - b0 (x + s • w)‖ * ‖w‖ ≤ N * (K * (s * ‖w‖)) * ‖w‖ := by gcongr
      _ = N * K * ‖w‖ ^ 2 * s := by ring
  have hint : IntervalIntegrable (fun s : ℝ => (N : ℝ) * K * ‖w‖ ^ 2 * s) volume 0 1 :=
    (continuous_const.mul continuous_id).intervalIntegrable 0 1
  have h1 := intervalIntegral.norm_integral_le_of_norm_le zero_le_one
    (Eventually.of_forall hbd) hint
  have h2 : ∫ s in (0 : ℝ)..1, (N : ℝ) * K * ‖w‖ ^ 2 * s = N * K * ‖w‖ ^ 2 / 2 := by
    rw [intervalIntegral.integral_const_mul, integral_id]; ring
  rw [h2] at h1
  rw [← Real.norm_eq_abs]
  refine h1.trans ?_
  have := p4j_norm_sq_le_Phi w
  have hNK : 0 ≤ (N : ℝ) * K := by positivity
  nlinarith [mul_le_mul_of_nonneg_left this hNK]

theorem sb1_quad_growth {U : EucConfig d N → ℝ} {b0 : EucConfig d N → EucConfig d N} {K : ℝ≥0}
    (hU : ∀ x, HasFDerivAt U (-(p4InnerL (b0 x))) x) (hb : LipschitzWith K b0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |U x| ≤ C * (1 + p4j_Phi x) := by
  set B : ℝ := N * ‖b0 0‖ with hB
  refine ⟨|U 0| + N * K + B, by positivity, fun x => ?_⟩
  have h := sb1_descent hU hb 0 x
  rw [zero_add] at h
  have hI : |p4InnerL (b0 0) x| ≤ B * (1 + p4j_Phi x) := by
    refine (p4j_innerL_bound _ _).trans ?_
    have h1 : ‖x‖ ≤ 1 + p4j_Phi x := by
      have := p4j_norm_sq_le_Phi x
      nlinarith [sq_nonneg (‖x‖ - 1), norm_nonneg x]
    calc (N : ℝ) * ‖b0 0‖ * ‖x‖ ≤ N * ‖b0 0‖ * (1 + p4j_Phi x) := by gcongr
      _ = B * (1 + p4j_Phi x) := by rw [hB]
  have hP := p4j_Phi_nonneg x
  have h2 : |U x - U 0| ≤ |U x - U 0 + p4InnerL (b0 0) x| + |p4InnerL (b0 0) x| := by
    have := abs_sub (U x - U 0 + p4InnerL (b0 0) x) (p4InnerL (b0 0) x)
    simpa using this
  have h3 : |U x| ≤ |U 0| + |U x - U 0| := by
    have := abs_add_le (U 0) (U x - U 0)
    simpa using this
  have hA : 0 ≤ |U 0| := abs_nonneg _
  have hNK : 0 ≤ (N : ℝ) * K := by positivity
  nlinarith [mul_nonneg hA hP, mul_nonneg hNK hP]

theorem sb1_symm_bound {U : EucConfig d N → ℝ} {b0 : EucConfig d N → EucConfig d N} {K : ℝ≥0}
    (hU : ∀ x, HasFDerivAt U (-(p4InnerL (b0 x))) x) (hb : LipschitzWith K b0) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ x w : EucConfig d N, U (x + w) + U (x - w) ≤ 2 * U x + 2 * κ * p4j_Phi w := by
  refine ⟨N * K, by positivity, fun x w => ?_⟩
  have h1 := (abs_le.1 (sb1_descent hU hb x w)).2
  have h2 := (abs_le.1 (sb1_descent hU hb x (-w))).2
  have e : x + -w = x - w := by abel
  rw [map_neg, p4j_Phi_neg, e] at h2
  linarith

end HRS.MS.MfeConf
