import HRS.MH.ScreenedA3a

/-!
# Packet A3b of `B:lem:screened` (S.B.4): row sums and weighted column sums of `kcCoef`.

Row sums use the translation invariance of `ℤ^d` and `1_{|z-z'| ≤ R} ≤ (2+R)^{d+3} ω_{z-z'}`;
column sums use the Peetre bound `ω_z ≤ (2+R)^{d+3} ω_{z'}` for `|z-z'| ≤ R`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MH.Screened

open HRS HRS.Whole

variable {d : ℕ}

lemma a3b_cw_nonneg (z : Fin d → ℤ) : 0 ≤ cellWeight d z := by
  unfold cellWeight jbracket
  exact Real.rpow_nonneg (Real.sqrt_nonneg _) _

lemma a3b_jb_le (x : Euc d) : jbracket x ≤ 1 + ‖x‖ := by
  unfold jbracket
  calc Real.sqrt (1 + ‖x‖ ^ 2) ≤ Real.sqrt ((1 + ‖x‖) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [norm_nonneg x])
    _ = 1 + ‖x‖ := Real.sqrt_sq (by positivity)

lemma a3b_one_le_jb (x : Euc d) : 1 ≤ jbracket x := by
  unfold jbracket
  calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
    _ ≤ Real.sqrt (1 + ‖x‖ ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ‖x‖])

lemma a3b_norm_le_jb (x : Euc d) : ‖x‖ ≤ jbracket x := by
  unfold jbracket
  calc ‖x‖ = Real.sqrt (‖x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (1 + ‖x‖ ^ 2) := Real.sqrt_le_sqrt (by linarith)

lemma a3b_latticePt_sub (z z' : Fin d → ℤ) : latticePt (z - z') = latticePt z - latticePt z' := by
  ext i
  simp [latticePt]

lemma a3b_key_row {R : ℝ} (hR : 0 ≤ R) (z z' : Fin d → ℤ) (h : ‖latticePt z - latticePt z'‖ ≤ R) :
    1 ≤ (2 + R) ^ ((d : ℝ) + 3) * cellWeight d (z - z') := by
  have hx : ‖latticePt (z - z')‖ ≤ R := by rw [a3b_latticePt_sub]; exact h
  have hle : jbracket (latticePt (z - z')) ≤ 2 + R := by
    have := a3b_jb_le (latticePt (z - z')); linarith
  have hpos : 0 < jbracket (latticePt (z - z')) := by
    linarith [a3b_one_le_jb (latticePt (z - z'))]
  have hM : (0 : ℝ) < 2 + R := by linarith
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h1 : (2 + R) ^ (-((d : ℝ) + 3)) ≤ jbracket (latticePt (z - z')) ^ (-((d : ℝ) + 3)) :=
    Real.rpow_le_rpow_of_nonpos hpos hle (by linarith)
  have hK : (2 + R) ^ ((d : ℝ) + 3) * (2 + R) ^ (-((d : ℝ) + 3)) = 1 := by
    rw [← Real.rpow_add hM]; simp
  unfold cellWeight
  calc (1 : ℝ) = (2 + R) ^ ((d : ℝ) + 3) * (2 + R) ^ (-((d : ℝ) + 3)) := hK.symm
    _ ≤ (2 + R) ^ ((d : ℝ) + 3) * jbracket (latticePt (z - z')) ^ (-((d : ℝ) + 3)) :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hM.le _)

lemma a3b_key_col {R : ℝ} (hR : 0 ≤ R) (z z' : Fin d → ℤ) (h : ‖latticePt z - latticePt z'‖ ≤ R) :
    cellWeight d z ≤ (2 + R) ^ ((d : ℝ) + 3) * cellWeight d z' := by
  have ha1 : 1 ≤ jbracket (latticePt z) := a3b_one_le_jb _
  have hna : ‖latticePt z‖ ≤ jbracket (latticePt z) := a3b_norm_le_jb _
  have hb : jbracket (latticePt z') ≤ (2 + R) * jbracket (latticePt z) := by
    have h1 := a3b_jb_le (latticePt z')
    have h2 : ‖latticePt z'‖ ≤ ‖latticePt z‖ + R := by
      have h3 : latticePt z' = latticePt z + (latticePt z' - latticePt z) := by abel
      have h4 := norm_add_le (latticePt z) (latticePt z' - latticePt z)
      have h5 : ‖latticePt z' - latticePt z‖ ≤ R := by rw [norm_sub_rev]; exact h
      rw [← h3] at h4
      linarith
    nlinarith [norm_nonneg (latticePt z)]
  have hb0 : 0 < jbracket (latticePt z') := by linarith [a3b_one_le_jb (latticePt z')]
  have ha0 : 0 < jbracket (latticePt z) := by linarith
  have hM : (0 : ℝ) < 2 + R := by linarith
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h1 : ((2 + R) * jbracket (latticePt z)) ^ (-((d : ℝ) + 3)) ≤
      jbracket (latticePt z') ^ (-((d : ℝ) + 3)) :=
    Real.rpow_le_rpow_of_nonpos hb0 hb (by linarith)
  rw [Real.mul_rpow hM.le ha0.le] at h1
  have hK : (2 + R) ^ ((d : ℝ) + 3) * (2 + R) ^ (-((d : ℝ) + 3)) = 1 := by
    rw [← Real.rpow_add hM]; simp
  unfold cellWeight
  calc jbracket (latticePt z) ^ (-((d : ℝ) + 3))
      = (2 + R) ^ ((d : ℝ) + 3) * (2 + R) ^ (-((d : ℝ) + 3)) * jbracket (latticePt z) ^ (-((d : ℝ) + 3)) := by
        rw [hK, one_mul]
    _ = (2 + R) ^ ((d : ℝ) + 3) * ((2 + R) ^ (-((d : ℝ) + 3)) * jbracket (latticePt z) ^ (-((d : ℝ) + 3))) := by
        rw [mul_assoc]
    _ ≤ (2 + R) ^ ((d : ℝ) + 3) * jbracket (latticePt z') ^ (-((d : ℝ) + 3)) :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hM.le _)

lemma a3b_ind_le {R : ℝ} (hR : 0 ≤ R) (z z' : Fin d → ℤ) :
    ENNReal.ofReal (if ‖latticePt z - latticePt z'‖ ≤ R then (1 : ℝ) else 0) ≤
      ENNReal.ofReal ((2 + R) ^ ((d : ℝ) + 3)) * ENNReal.ofReal (cellWeight d (z - z')) := by
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by linarith) _)]
  apply ENNReal.ofReal_le_ofReal
  split_ifs with h
  · exact a3b_key_row hR z z' h
  · exact mul_nonneg (Real.rpow_nonneg (by linarith) _) (a3b_cw_nonneg _)

theorem kcCoef_sums_proof (hd : 1 ≤ d) (R c₁ c₂ : ℝ) (hR : 0 ≤ R) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) :
    ∃ C : ℝ, 0 ≤ C ∧ (⨆ z : Fin d → ℤ, ∑' z', (kcCoef d R c₁ c₂ z z' : ℝ≥0∞) ≤ ENNReal.ofReal C) ∧
      ∀ z' : Fin d → ℤ, ∑' z : Fin d → ℤ, ENNReal.ofReal (cellWeight d z) * (kcCoef d R c₁ c₂ z z' : ℝ≥0∞) ≤
        ENNReal.ofReal C * ENNReal.ofReal (cellWeight d z') := by
  have hS0 : ∑' z : Fin d → ℤ, ENNReal.ofReal (cellWeight d z) < ⊤ := cellWeight_tsum_lt_top_proof hd
  set S := ∑' z : Fin d → ℤ, ENNReal.ofReal (cellWeight d z) with hSdef
  have hSt : S ≠ ⊤ := hS0.ne
  have hsub_row : ∀ z : Fin d → ℤ, ∑' z', ENNReal.ofReal (cellWeight d (z - z')) = S :=
    fun z => Equiv.tsum_eq (Equiv.subLeft z) (fun w => ENNReal.ofReal (cellWeight d w))
  have hsub_col : ∀ z' : Fin d → ℤ, ∑' z, ENNReal.ofReal (cellWeight d (z - z')) = S :=
    fun z' => Equiv.tsum_eq (Equiv.subRight z') (fun w => ENNReal.ofReal (cellWeight d w))
  set m := ENNReal.ofReal ((2 + R) ^ ((d : ℝ) + 3)) with hm
  set a := ENNReal.ofReal c₁ with ha
  set b := ENNReal.ofReal c₂ with hb
  set Cx := (a * m * m + b) * S + (a * m + b) * S with hCx
  have ha_t : a ≠ ⊤ := ENNReal.ofReal_ne_top
  have hm_t : m ≠ ⊤ := ENNReal.ofReal_ne_top
  have hb_t : b ≠ ⊤ := ENNReal.ofReal_ne_top
  have hCxt : Cx ≠ ⊤ :=
    ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (ENNReal.mul_ne_top ha_t hm_t) hm_t, hb_t⟩) hSt,
        ENNReal.mul_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ha_t hm_t, hb_t⟩) hSt⟩
  -- pointwise bound on the cell coefficient
  have hkc : ∀ z z' : Fin d → ℤ, (kcCoef d R c₁ c₂ z z' : ℝ≥0∞) ≤
      a * ENNReal.ofReal (if ‖latticePt z - latticePt z'‖ ≤ R then (1 : ℝ) else 0) +
        b * ENNReal.ofReal (cellWeight d z') := by
    intro z z'
    show ENNReal.ofReal (c₁ * (if ‖latticePt z - latticePt z'‖ ≤ R then 1 else 0) +
      c₂ * cellWeight d z') ≤ _
    rw [ha, hb, ← ENNReal.ofReal_mul hc₁, ← ENNReal.ofReal_mul hc₂]
    exact ENNReal.ofReal_add_le
  -- row sums
  have hrowind : ∀ z : Fin d → ℤ, ∑' z', ENNReal.ofReal (if ‖latticePt z - latticePt z'‖ ≤ R then (1 : ℝ) else 0)
      ≤ m * S := by
    intro z
    calc ∑' z', ENNReal.ofReal (if ‖latticePt z - latticePt z'‖ ≤ R then (1 : ℝ) else 0)
        ≤ ∑' z', m * ENNReal.ofReal (cellWeight d (z - z')) :=
          ENNReal.tsum_le_tsum fun z' => a3b_ind_le hR z z'
      _ = m * S := by rw [ENNReal.tsum_mul_left, hsub_row z]
  have hrow : ∀ z : Fin d → ℤ, ∑' z', (kcCoef d R c₁ c₂ z z' : ℝ≥0∞) ≤ (a * m + b) * S := by
    intro z
    calc ∑' z', (kcCoef d R c₁ c₂ z z' : ℝ≥0∞)
        ≤ ∑' z', (a * ENNReal.ofReal (if ‖latticePt z - latticePt z'‖ ≤ R then (1 : ℝ) else 0) +
            b * ENNReal.ofReal (cellWeight d z')) := ENNReal.tsum_le_tsum fun z' => hkc z z'
      _ = a * ∑' z', ENNReal.ofReal (if ‖latticePt z - latticePt z'‖ ≤ R then (1 : ℝ) else 0) +
            b * S := by
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
      _ ≤ a * (m * S) + b * S := by
          exact add_le_add (mul_le_mul_of_nonneg_left (hrowind z) (by positivity)) le_rfl
      _ = (a * m + b) * S := by ring
  -- column sums
  have hcolind : ∀ z' : Fin d → ℤ, ∑' z, ENNReal.ofReal (if ‖latticePt z - latticePt z'‖ ≤ R then (1 : ℝ) else 0)
      ≤ m * S := by
    intro z'
    calc ∑' z, ENNReal.ofReal (if ‖latticePt z - latticePt z'‖ ≤ R then (1 : ℝ) else 0)
        ≤ ∑' z, m * ENNReal.ofReal (cellWeight d (z - z')) :=
          ENNReal.tsum_le_tsum fun z => a3b_ind_le hR z z'
      _ = m * S := by rw [ENNReal.tsum_mul_left, hsub_col z']
  have hcol : ∀ z' : Fin d → ℤ, ∑' z, ENNReal.ofReal (cellWeight d z) * (kcCoef d R c₁ c₂ z z' : ℝ≥0∞) ≤
      ENNReal.ofReal (cellWeight d z') * ((a * m * m + b) * S) := by
    intro z'
    set w' := ENNReal.ofReal (cellWeight d z') with hw'
    have hstep1 : ∀ z : Fin d → ℤ, ENNReal.ofReal (cellWeight d z) * (kcCoef d R c₁ c₂ z z' : ℝ≥0∞) ≤
        a * (ENNReal.ofReal (cellWeight d z) * ENNReal.ofReal (if ‖latticePt z - latticePt z'‖ ≤ R then (1 : ℝ) else 0))
          + (b * w') * ENNReal.ofReal (cellWeight d z) := by
      intro z
      calc ENNReal.ofReal (cellWeight d z) * (kcCoef d R c₁ c₂ z z' : ℝ≥0∞)
          ≤ ENNReal.ofReal (cellWeight d z) * (a * ENNReal.ofReal (if ‖latticePt z - latticePt z'‖ ≤ R then (1 : ℝ) else 0) + b * w') :=
            mul_le_mul_of_nonneg_left (hkc z z') (by positivity)
        _ = _ := by ring
    have hpt : ∀ z : Fin d → ℤ, ENNReal.ofReal (cellWeight d z) * ENNReal.ofReal (if ‖latticePt z - latticePt z'‖ ≤ R then (1 : ℝ) else 0)
        ≤ (m * w') * ENNReal.ofReal (if ‖latticePt z - latticePt z'‖ ≤ R then (1 : ℝ) else 0) := by
      intro z
      by_cases h : ‖latticePt z - latticePt z'‖ ≤ R
      · rw [if_pos h, ENNReal.ofReal_one, mul_one, mul_one, hm, hw', ← ENNReal.ofReal_mul (Real.rpow_nonneg (by linarith) _)]
        exact ENNReal.ofReal_le_ofReal (by
          have := a3b_key_col hR z z' h
          exact this)
      · rw [if_neg h, ENNReal.ofReal_zero, mul_zero, mul_zero]
    have hsum2 : ∑' z : Fin d → ℤ, ENNReal.ofReal (cellWeight d z) * ENNReal.ofReal (if ‖latticePt z - latticePt z'‖ ≤ R then (1 : ℝ) else 0)
        ≤ (m * w') * (m * S) := by
      calc ∑' z : Fin d → ℤ, ENNReal.ofReal (cellWeight d z) * ENNReal.ofReal (if ‖latticePt z - latticePt z'‖ ≤ R then (1 : ℝ) else 0)
          ≤ ∑' z : Fin d → ℤ, (m * w') * ENNReal.ofReal (if ‖latticePt z - latticePt z'‖ ≤ R then (1 : ℝ) else 0) :=
            ENNReal.tsum_le_tsum hpt
        _ = (m * w') * ∑' z : Fin d → ℤ, ENNReal.ofReal (if ‖latticePt z - latticePt z'‖ ≤ R then (1 : ℝ) else 0) :=
            ENNReal.tsum_mul_left
        _ ≤ (m * w') * (m * S) := mul_le_mul_of_nonneg_left (hcolind z') (by positivity)
    calc ∑' z : Fin d → ℤ, ENNReal.ofReal (cellWeight d z) * (kcCoef d R c₁ c₂ z z' : ℝ≥0∞)
        ≤ ∑' z : Fin d → ℤ, (a * (ENNReal.ofReal (cellWeight d z) * ENNReal.ofReal (if ‖latticePt z - latticePt z'‖ ≤ R then (1 : ℝ) else 0))
            + (b * w') * ENNReal.ofReal (cellWeight d z)) := ENNReal.tsum_le_tsum hstep1
      _ = a * ∑' z : Fin d → ℤ, (ENNReal.ofReal (cellWeight d z) * ENNReal.ofReal (if ‖latticePt z - latticePt z'‖ ≤ R then (1 : ℝ) else 0))
            + (b * w') * S := by
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
      _ ≤ a * ((m * w') * (m * S)) + (b * w') * S := by
          exact add_le_add (mul_le_mul_of_nonneg_left hsum2 (by positivity)) le_rfl
      _ = w' * ((a * m * m + b) * S) := by ring
  refine ⟨Cx.toReal, ENNReal.toReal_nonneg, ?_, ?_⟩
  · rw [ENNReal.ofReal_toReal hCxt]
    refine iSup_le fun z => ?_
    exact (hrow z).trans (le_add_self)
  · intro z'
    rw [ENNReal.ofReal_toReal hCxt]
    calc ∑' z : Fin d → ℤ, ENNReal.ofReal (cellWeight d z) * (kcCoef d R c₁ c₂ z z' : ℝ≥0∞)
        ≤ ENNReal.ofReal (cellWeight d z') * ((a * m * m + b) * S) := hcol z'
      _ ≤ Cx * ENNReal.ofReal (cellWeight d z') := by
          rw [mul_comm Cx]
          exact mul_le_mul_of_nonneg_left (le_self_add) (by positivity)

end HRS.MH.Screened
