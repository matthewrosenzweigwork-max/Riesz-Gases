import HRS.MC.E214N10

/-!
# E214N11: the shift identity (`shift_identity_proof`)

`‖K(a+h) - K^{(h)}(a)‖ ≤ C e^{-ca}` where `K^{(h)}` is the window tensor of the shifted `GaussData`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E214N

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213Final
open HRS.MC.E214Plan

variable {d : ℕ}

section Final

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (sd : StatDatum S β₀ m hE)

theorem Kwin_shift_eq (gds : GaussData sd.Ss S.β sd.hEs) (h : ℝ) (hh : 0 ≤ h) (T a : ℝ) :
    (shiftGD_proof sd gds h hh).Kwin T a =
      symm3 (PathSpace d m T)
        (pushforward3 (Iwin sd.Ss S.β sd.hEs T a) (Kinit0 sd.Ss S.β)
          - (3 : ℝ) • bochTensor3 gds.P₀ ((shiftGD_proof sd gds h hh).Dwin T a) (gds.Zwin T (a + h))
              (gds.Zwin T (a + h))
          + (3 : ℝ) • bochTensor21 gds.P₀ ((shiftGD_proof sd gds h hh).Jwin T a) (gds.Zwin T (a + h))) := by
  unfold GaussData.Kwin
  rw [shift_Zwin]
  rfl

theorem Kproj_coe_eq (gd : GaussData sd.Ss S.β sd.hEs) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) :
    ((gd.Kproj T a : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3) = gd.Kwin T a := by
  classical
  unfold GaussData.Kproj
  rw [max_eq_left ha, dif_pos (HRS.MC.E213U11.Kwin_mem_proof gd T hT a ha)]

theorem shift_identity_proof (gds : GaussData sd.Ss S.β sd.hEs) (T : ℝ) (hT : 0 < T) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ a h : ℝ, 0 ≤ a → ∀ hh : 0 ≤ h,
      ‖gds.Kproj T (a + h) - (shiftGD_proof sd gds h hh).Kproj T a‖ ≤ C * Real.exp (-c * a) := by
  classical
  obtain ⟨KD, cD, hKD, hcD, hD⟩ := shift_D_term sd gds T hT
  obtain ⟨KJ, cJ, hKJ, hcJ, hJ⟩ := shift_J_term sd gds T hT
  obtain ⟨CI, cI, hCI, hcI, hI⟩ := Classical.choose_spec (exists_Iwin sd.Ss S.β sd.hEs T)
  obtain ⟨Cg, hCg⟩ := HRS.MC.E213U11.gd_moments_proof gds T hT
  have hK0 : 0 ≤ ‖Kinit0 sd.Ss S.β‖ := ContinuousLinearMap.opNorm_nonneg _
  set c : ℝ := min cD (min cJ cI) with hc
  have hc0 : 0 < c := lt_min hcD (lt_min hcJ hcI)
  refine ⟨2 * CI ^ 3 * ‖Kinit0 sd.Ss S.β‖ + 3 * KD + 3 * KJ + 1, c, by positivity, hc0, fun a h ha hh => ?_⟩
  have ha' : 0 ≤ a + h := add_nonneg ha hh
  obtain ⟨Cg', hCg'⟩ := HRS.MC.E213U11.gd_moments_proof (shiftGD_proof sd gds h hh) T hT
  -- the exponentials
  have e1 : Real.exp (-cD * a) ≤ Real.exp (-c * a) :=
    Real.exp_le_exp.2 (by nlinarith [min_le_left cD (min cJ cI)])
  have e2 : Real.exp (-cJ * a) ≤ Real.exp (-c * a) :=
    Real.exp_le_exp.2 (by nlinarith [(min_le_right cD (min cJ cI)).trans (min_le_left cJ cI)])
  have e3 : Real.exp (-cI * a) ≤ Real.exp (-c * a) :=
    Real.exp_le_exp.2 (by nlinarith [(min_le_right cD (min cJ cI)).trans (min_le_right cJ cI)])
  have hexp0 : 0 < Real.exp (-c * a) := Real.exp_pos _
  -- the integrability data
  obtain ⟨-, hZm, hDm, hJm, hi3, hi21, -, -⟩ := hCg (a + h) ha'
  obtain ⟨-, hZm', hDm', hJm', hi3', hi21', -, -⟩ := hCg' a ha
  rw [shift_Zwin sd gds h hh T a] at hi3' hi21' hZm'
  obtain ⟨dI, dB⟩ := hD h hh a ha
  obtain ⟨jI, jB⟩ := hJ h hh a ha
  -- the combination bound
  have hcomb := comb_sub_le (P := gds.P₀)
    (pushforward3 (Iwin sd.Ss S.β sd.hEs T (a + h)) (Kinit0 sd.Ss S.β))
    (pushforward3 (Iwin sd.Ss S.β sd.hEs T a) (Kinit0 sd.Ss S.β))
    (D := gds.Dwin T (a + h)) (D' := (shiftGD_proof sd gds h hh).Dwin T a) (Z := gds.Zwin T (a + h))
    (J := gds.Jwin T (a + h)) (J' := (shiftGD_proof sd gds h hh).Jwin T a) hDm hDm' hZm hJm hJm' hi3 hi3' dI hi21 hi21' jI
  -- reduce to `Kwin`
  have hnorm : ‖gds.Kproj T (a + h) - (shiftGD_proof sd gds h hh).Kproj T a‖ =
      ‖gds.Kwin T (a + h) - (shiftGD_proof sd gds h hh).Kwin T a‖ := by
    have q1 := Kproj_coe_eq sd gds T hT (a + h) ha'
    have q2 := Kproj_coe_eq sd (shiftGD_proof sd gds h hh) T hT a ha
    show ‖((gds.Kproj T (a + h) : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3) -
      ((shiftGD_proof sd gds h hh).Kproj T a : projTensor (PathSpace d m T) 3)‖ = _
    rw [q1, q2]
  rw [hnorm, Kwin_shift_eq sd gds h hh T a]
  have hKw : gds.Kwin T (a + h) = symm3 (PathSpace d m T)
      (pushforward3 (Iwin sd.Ss S.β sd.hEs T (a + h)) (Kinit0 sd.Ss S.β)
        - (3 : ℝ) • bochTensor3 gds.P₀ (gds.Dwin T (a + h)) (gds.Zwin T (a + h)) (gds.Zwin T (a + h))
        + (3 : ℝ) • bochTensor21 gds.P₀ (gds.Jwin T (a + h)) (gds.Zwin T (a + h))) := rfl
  rw [hKw]
  refine hcomb.trans ?_
  -- the initial tensors
  have hX : ∀ a' : ℝ, a ≤ a' →
      ‖pushforward3 (Iwin sd.Ss S.β sd.hEs T a') (Kinit0 sd.Ss S.β)‖ ≤ CI ^ 3 * ‖Kinit0 sd.Ss S.β‖ * Real.exp (-cI * a) := by
    intro a' haa'
    have ha'0 : 0 ≤ a' := ha.trans haa'
    have h1 : ‖Iwin sd.Ss S.β sd.hEs T a'‖ ≤ CI * Real.exp (-cI * a) := by
      refine (hI a' ha'0).2.trans ?_
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) hCI.le
    refine (HRS.MC.E213U11.u11_norm_pushforward3_apply_le (Iwin sd.Ss S.β sd.hEs T a') (Kinit0 sd.Ss S.β)).trans ?_
    have h2 : ‖Iwin sd.Ss S.β sd.hEs T a'‖ ^ 3 ≤ (CI * Real.exp (-cI * a)) ^ 3 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 3
    have hle1 : Real.exp (-cI * a) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have hep := Real.exp_pos (-cI * a)
    have h3 : (CI * Real.exp (-cI * a)) ^ 3 ≤ CI ^ 3 * Real.exp (-cI * a) := by
      rw [mul_pow]
      have : Real.exp (-cI * a) ^ 3 ≤ Real.exp (-cI * a) := by
        have h4 : Real.exp (-cI * a) ^ 2 ≤ 1 := pow_le_one₀ hep.le hle1
        calc Real.exp (-cI * a) ^ 3 = Real.exp (-cI * a) ^ 2 * Real.exp (-cI * a) := by ring
          _ ≤ 1 * Real.exp (-cI * a) := mul_le_mul_of_nonneg_right h4 hep.le
          _ = _ := one_mul _
      have hCI3 : 0 ≤ CI ^ 3 := by positivity
      nlinarith
    calc ‖Iwin sd.Ss S.β sd.hEs T a'‖ ^ 3 * ‖Kinit0 sd.Ss S.β‖
        ≤ CI ^ 3 * Real.exp (-cI * a) * ‖Kinit0 sd.Ss S.β‖ :=
          mul_le_mul_of_nonneg_right (h2.trans h3) hK0
      _ = _ := by ring
  have hXX : ‖pushforward3 (Iwin sd.Ss S.β sd.hEs T (a + h)) (Kinit0 sd.Ss S.β) -
      pushforward3 (Iwin sd.Ss S.β sd.hEs T a) (Kinit0 sd.Ss S.β)‖ ≤
      2 * (CI ^ 3 * ‖Kinit0 sd.Ss S.β‖ * Real.exp (-cI * a)) := by
    have := norm_sub_le (pushforward3 (Iwin sd.Ss S.β sd.hEs T (a + h)) (Kinit0 sd.Ss S.β))
      (pushforward3 (Iwin sd.Ss S.β sd.hEs T a) (Kinit0 sd.Ss S.β))
    have h1 := hX (a + h) (by linarith)
    have h2 := hX a le_rfl
    linarith
  have hCI3 : 0 ≤ CI ^ 3 * ‖Kinit0 sd.Ss S.β‖ := by positivity
  calc _ ≤ 2 * (CI ^ 3 * ‖Kinit0 sd.Ss S.β‖ * Real.exp (-cI * a)) + 3 * (KD * Real.exp (-cD * a)) +
        3 * (KJ * Real.exp (-cJ * a)) := by linarith
    _ ≤ 2 * (CI ^ 3 * ‖Kinit0 sd.Ss S.β‖ * Real.exp (-c * a)) + 3 * (KD * Real.exp (-c * a)) +
        3 * (KJ * Real.exp (-c * a)) := by gcongr
    _ ≤ _ := by nlinarith

end Final

end HRS.MC.E214N

end
