import HRS.MS.SuppU2Aux7

/-!
# U2 auxiliary 8: the far-field decay `‖D^j (κ * h)(x)‖ ≤ C A |x|^{-(a+j)}` for `|x| ≥ 1`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000

namespace HRS.Whole

variable {d : ℕ}

/-- The full kernel hypotheses. -/
structure U2KerFull (κ : Euc d → ℝ) (a : ℝ) : Prop where
  ker : U2Ker κ a
  sm : ∀ z : Euc d, z ≠ 0 → ContDiffAt ℝ ∞ κ z
  D : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ z : Euc d, z ≠ 0 → ‖iteratedFDeriv ℝ j κ z‖ ≤ C * ‖z‖ ^ (-a - j)

lemma u2_half_rpow {R : ℝ} (hR : 0 < R) (p : ℝ) : (R / 2) ^ (-p) = 2 ^ p * R ^ (-p) := by
  rw [Real.div_rpow hR.le (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2), Real.rpow_neg hR.le]
  field_simp

lemma u2_quarter_rpow {R : ℝ} (hR : 0 < R) (q : ℝ) (hq : 0 ≤ q) :
    (1 + R / 4) ^ (-q) ≤ 4 ^ q * R ^ (-q) := by
  have h1 : (R / 4) ^ (-q) ≤ 4 ^ q * R ^ (-q) := by
    rw [Real.div_rpow hR.le (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 4),
      Real.rpow_neg hR.le]
    field_simp
    exact le_refl _
  exact (Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)).trans h1

theorem u2_far {κ : Euc d → ℝ} {a : ℝ} (hK : U2KerFull κ a) (k : ℕ) {L : ℝ}
    (hL : (d : ℝ) + k + a + 2 < L) :
    ∃ Cf : ℝ, 0 ≤ Cf ∧ ∀ (A : ℝ) (h : Euc d → ℝ), 0 ≤ A → U2Dec k L A h →
      ∀ x0 : Euc d, 1 ≤ ‖x0‖ → ∀ j ≤ k,
        ‖iteratedFDeriv ℝ j (u2Conv κ h) x0‖ ≤ Cf * A * ‖x0‖ ^ (-(a + j)) := by
  have hker := hK.ker
  have hdL : (d : ℝ) < L := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have : 0 ≤ a := hker.a_nonneg
    linarith
  have hL0 : 0 ≤ L := u2_wt_L0 hdL
  obtain ⟨ν, hν⟩ := u2_exists_cutoff d
  obtain ⟨BB, hBB0, hBB⟩ := u2_h2_dec hν k
  obtain ⟨CW, hCW0, hCW⟩ := u2_kerInt_W hker
  choose Cj hCj0 hCj using hK.D
  have hd1 : (d : ℝ) < ((d : ℝ) + 1) := by linarith
  set IL : ℝ := ∫ y, u2Wt (d := d) L y with hIL
  set I1 : ℝ := ∫ y, u2Wt (d := d) ((d : ℝ) + 1) y with hI1
  have hIL0 : 0 ≤ IL := u2_integral_nonneg (fun y => (u2Wt_pos L y).le)
  have hI10 : 0 ≤ I1 := u2_integral_nonneg (fun y => (u2Wt_pos _ y).le)
  set q : ℝ := L - d - 1 with hq
  have hq0 : 0 ≤ q := by
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have : 0 ≤ a := hker.a_nonneg
    linarith
  set Cj' : ℕ → ℝ := fun j => Cj j * 2 ^ (a + j) * (1 + BB) * IL +
    BB * CW * (1 + I1) * 4 ^ q with hCj'
  have hCj'0 : ∀ j, 0 ≤ Cj' j := fun j => by
    have := hCj0 j
    simp only [hCj']
    positivity
  refine ⟨∑ j ∈ Finset.range (k + 1), Cj' j,
    Finset.sum_nonneg fun j _ => hCj'0 j, ?_⟩
  intro A h hA hdec x0 hx0 j hj
  set R : ℝ := ‖x0‖ with hR
  have hR0 : 0 < R := by linarith
  obtain ⟨hh2cd, hh2b⟩ := hBB L A h hA hdec R hx0
  set h2 : Euc d → ℝ := u2_h2 ν R h with hh2
  have hBA : 0 ≤ BB * A := mul_nonneg hBB0 hA
  have hdec2 : U2Dec k L (BB * A) h2 := by
    refine ⟨hh2cd, fun m hm y => ?_⟩
    refine (hh2b m hm y).trans ?_
    have := u2Wt_pos (d := d) L y
    split_ifs
    · exact le_refl _
    · positivity
  set h1 : Euc d → ℝ := fun y => h y - h2 y with hh1
  have hhc : Continuous h := hdec.1.continuous
  have hh2c : Continuous h2 := hh2cd.continuous
  have hh1c : Continuous h1 := hhc.sub hh2c
  have hh1supp : ∀ y : Euc d, R / 2 < ‖y‖ → h1 y = 0 := by
    intro y hy
    have : ν (R⁻¹ • y) = 1 := by
      apply hν.one
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR0)]
      calc (1 : ℝ) / 2 = R⁻¹ * (R / 2) := by field_simp
        _ < R⁻¹ * ‖y‖ := mul_lt_mul_of_pos_left hy (inv_pos.mpr hR0)
    simp only [hh1, hh2, u2_h2, this, one_mul, sub_self]
  have hh0 : ∀ y, ‖h y‖ ≤ A * u2Wt L y := fun y => by
    simpa using hdec.2 0 (Nat.zero_le _) y
  have hh20 : ∀ y, ‖h2 y‖ ≤ (BB * A) * u2Wt L y := fun y => by
    simpa using hdec2.2 0 (Nat.zero_le _) y
  have hh10 : ∀ y, ‖h1 y‖ ≤ ((1 + BB) * A) * u2Wt L y := fun y => by
    calc ‖h1 y‖ ≤ ‖h y‖ + ‖h2 y‖ := norm_sub_le _ _
      _ ≤ A * u2Wt L y + (BB * A) * u2Wt L y := add_le_add (hh0 y) (hh20 y)
      _ = ((1 + BB) * A) * u2Wt L y := by ring
  have hA1 : 0 ≤ (1 + BB) * A := mul_nonneg (by linarith) hA
  -- the decomposition of the convolution
  have hdecomp : ∀ x, u2Conv κ h x = u2Conv κ h1 x + u2Conv κ h2 x := by
    intro x
    unfold u2Conv
    rw [← integral_add (u2_conv_integrable hker hdL hh1c hA1 hh10 x)
      (u2_conv_integrable hker hdL hh2c hBA hh20 x)]
    congr 1
    funext z
    rw [← smul_add]
    congr 1
    simp [hh1]
  obtain ⟨hF_iter, hF_cd⟩ := u2_conv_iter hker hdL hA hdec
  obtain ⟨hF2_iter, hF2_cd⟩ := u2_conv_iter hker hdL hBA hdec2
  have hF1 : u2Conv κ h1 = fun x => u2Conv κ h x - u2Conv κ h2 x := by
    funext x; rw [hdecomp x]; ring
  have hF1cd : ContDiff ℝ k (u2Conv κ h1) := by
    rw [hF1]; exact hF_cd.sub hF2_cd
  have hjk : (j : ℕ∞ω) ≤ (k : ℕ∞ω) := by exact_mod_cast hj
  have hsplit : iteratedFDeriv ℝ j (u2Conv κ h) x0 =
      iteratedFDeriv ℝ j (u2Conv κ h1) x0 + iteratedFDeriv ℝ j (u2Conv κ h2) x0 := by
    have : u2Conv κ h = u2Conv κ h1 + u2Conv κ h2 := funext hdecomp
    rw [this]
    exact iteratedFDeriv_add_apply ((hF1cd.of_le hjk).contDiffAt) ((hF2_cd.of_le hjk).contDiffAt)
  have hr2 : 0 < R / 2 := by linarith
  -- Term 1: kernel-side
  have hT1 := u2_kernel_side_norm hker.a_nonneg hK.sm (hCj0 j) j (hCj j) hK.D hr2 hh1c hh1supp
    (x0 := x0) (by linarith)
  have hint1 : ∫ y, ‖h1 y‖ ≤ ((1 + BB) * A) * IL := by
    have hgi : Integrable h1 volume := u2_integrable_of_support hh1c hh1supp
    calc ∫ y, ‖h1 y‖ ≤ ∫ y, ((1 + BB) * A) * u2Wt L y :=
          integral_mono hgi.norm ((u2_integrable_wt hdL).const_mul _) hh10
      _ = ((1 + BB) * A) * IL := by rw [integral_const_mul]
  have hT1' : ‖iteratedFDeriv ℝ j (u2Conv κ h1) x0‖ ≤
      (Cj j * (R / 2) ^ (-a - j)) * (((1 + BB) * A) * IL) :=
    hT1.trans (mul_le_mul_of_nonneg_left hint1 (mul_nonneg (hCj0 j) (Real.rpow_nonneg hr2.le _)))
  -- Term 2: h-side
  set W : ℝ := (1 + R / 4) ^ (-q) with hW
  have hW0 : 0 ≤ W := (Real.rpow_nonneg (by positivity) _)
  have hD2 : ∀ y, ‖iteratedFDeriv ℝ j h2 y‖ ≤ (BB * A) * (W * u2Wt ((d : ℝ) + 1) y) := by
    intro y
    have hy := hh2b j hj y
    by_cases hyR : R / 4 ≤ ‖y‖
    · rw [if_pos hyR] at hy
      refine hy.trans ?_
      -- wt_L ≤ W * wt_{d+1}
      have : u2Wt L y ≤ W * u2Wt ((d : ℝ) + 1) y := by
        unfold u2Wt
        have h1y : (0 : ℝ) < 1 + ‖y‖ := by positivity
        have : (1 + ‖y‖) ^ (-L) = (1 + ‖y‖) ^ (-q) * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) := by
          rw [← Real.rpow_add h1y]; congr 1; simp only [hq]; ring
        rw [this]
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg h1y.le _)
        exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
      calc BB * A * u2Wt L y ≤ BB * A * (W * u2Wt ((d : ℝ) + 1) y) :=
            mul_le_mul_of_nonneg_left this hBA
        _ = _ := rfl
    · rw [if_neg hyR] at hy
      refine hy.trans ?_
      have := u2Wt_pos (d := d) ((d : ℝ) + 1) y
      positivity
  have hF2j : iteratedFDeriv ℝ j (u2Conv κ h2) x0 = u2Conv κ (iteratedFDeriv ℝ j h2) x0 :=
    hF2_iter j hj x0
  have hwc : Continuous fun z : Euc d => W * u2Wt (d := d) ((d : ℝ) + 1) (x0 - z) :=
    continuous_const.mul ((u2Wt_continuous _).comp (continuous_const.sub continuous_id))
  have hwint : Integrable (fun z : Euc d => W * u2Wt (d := d) ((d : ℝ) + 1) (x0 - z)) volume :=
    ((u2_integrable_wt (by linarith : (d : ℝ) < (d : ℝ) + 1)).comp_sub_left x0).const_mul W
  have hwle : ∀ z : Euc d, W * u2Wt (d := d) ((d : ℝ) + 1) (x0 - z) ≤ W := fun z => by
    have := u2Wt_le_one (d := d) (L := (d : ℝ) + 1) (by positivity) (x0 - z)
    calc W * u2Wt (d := d) ((d : ℝ) + 1) (x0 - z) ≤ W * 1 :=
          mul_le_mul_of_nonneg_left this hW0
      _ = W := mul_one W
  obtain ⟨hki, hkle⟩ := hCW W hW0 (fun z => W * u2Wt (d := d) ((d : ℝ) + 1) (x0 - z))
    hwc.aestronglyMeasurable (fun z => mul_nonneg hW0 (u2Wt_pos _ _).le) hwle hwint
  have hwI : ∫ z : Euc d, W * u2Wt (d := d) ((d : ℝ) + 1) (x0 - z) = W * I1 := by
    rw [integral_const_mul]
    congr 1
    exact integral_sub_left_eq_self (fun y => u2Wt (d := d) ((d : ℝ) + 1) y) volume x0
  rw [hwI] at hkle
  have hT2 : ‖iteratedFDeriv ℝ j (u2Conv κ h2) x0‖ ≤ (BB * A) * (CW * (W + W * I1)) := by
    rw [hF2j]
    unfold u2Conv
    calc ‖∫ z, κ z • iteratedFDeriv ℝ j h2 (x0 - z)‖
        ≤ ∫ z, (BB * A) * (‖κ z‖ * (W * u2Wt (d := d) ((d : ℝ) + 1) (x0 - z))) := by
          refine norm_integral_le_of_norm_le (hki.const_mul _) (Filter.Eventually.of_forall fun z => ?_)
          rw [norm_smul]
          calc ‖κ z‖ * ‖iteratedFDeriv ℝ j h2 (x0 - z)‖
              ≤ ‖κ z‖ * ((BB * A) * (W * u2Wt (d := d) ((d : ℝ) + 1) (x0 - z))) :=
                mul_le_mul_of_nonneg_left (hD2 _) (norm_nonneg _)
            _ = (BB * A) * (‖κ z‖ * (W * u2Wt (d := d) ((d : ℝ) + 1) (x0 - z))) := by ring
      _ = (BB * A) * ∫ z, ‖κ z‖ * (W * u2Wt (d := d) ((d : ℝ) + 1) (x0 - z)) := by
          rw [integral_const_mul]
      _ ≤ (BB * A) * (CW * (W + W * I1)) := mul_le_mul_of_nonneg_left hkle hBA
  -- final assembly
  have hjq : a + (j : ℝ) ≤ q := by
    have : (j : ℝ) ≤ k := by exact_mod_cast hj
    simp only [hq]
    linarith
  have hWle2 : W ≤ 4 ^ q * R ^ (-(a + (j : ℝ))) :=
    (u2_quarter_rpow hR0 q hq0).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hx0 (by linarith)) (by positivity))
  have e1 : (R / 2) ^ (-a - (j : ℝ)) = 2 ^ (a + (j : ℝ)) * R ^ (-(a + (j : ℝ))) := by
    rw [show -a - (j : ℝ) = -(a + (j : ℝ)) by ring]
    exact u2_half_rpow hR0 _
  have hWI : W + W * I1 ≤ (1 + I1) * (4 ^ q * R ^ (-(a + (j : ℝ)))) := by
    calc W + W * I1 = (1 + I1) * W := by ring
      _ ≤ (1 + I1) * (4 ^ q * R ^ (-(a + (j : ℝ)))) :=
          mul_le_mul_of_nonneg_left hWle2 (by linarith)
  have hjle : Cj' j ≤ ∑ j' ∈ Finset.range (k + 1), Cj' j' :=
    Finset.single_le_sum (f := Cj') (fun j' _ => hCj'0 j') (Finset.mem_range.mpr (by omega))
  have hRp : 0 ≤ R ^ (-(a + (j : ℝ))) := Real.rpow_nonneg hR0.le _
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  calc ‖iteratedFDeriv ℝ j (u2Conv κ h1) x0‖ + ‖iteratedFDeriv ℝ j (u2Conv κ h2) x0‖
      ≤ (Cj j * (R / 2) ^ (-a - (j : ℝ))) * (((1 + BB) * A) * IL) +
          (BB * A) * (CW * ((1 + I1) * (4 ^ q * R ^ (-(a + (j : ℝ)))))) := by
        refine add_le_add hT1' (hT2.trans ?_)
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hWI hCW0) hBA
    _ = Cj' j * A * R ^ (-(a + (j : ℝ))) := by
        simp only [hCj']
        rw [e1]
        ring
    _ ≤ (∑ j' ∈ Finset.range (k + 1), Cj' j') * A * R ^ (-(a + (j : ℝ))) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hjle hA) hRp

end HRS.Whole
