import HRS.Commutator.Torus.NRSTAux26

/-!
# NRS-T, part 27: upper bound `‖φ(·/N) G(mk ·)‖_p ≲ N^{d/p} ‖G‖_p`
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace
  ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS HRS.Commutator.TorusNote.NRST

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

theorem nrstr_upper (hd : 1 ≤ d) {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) {p : ℝ} (hp : 1 ≤ p) :
    ∃ CU : ℝ, 0 < CU ∧ ∀ (M : ℕ) {G : Torus d → ℂ}, Continuous G →
      eLpNorm (fun y : 𝔼 => nrstr_phi (d := d) ((((d : ℝ) * ((M : ℝ) + 1) / r)⁻¹) • y) *
        G (Torus.mk y)) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal CU * (ENNReal.ofReal ((((d : ℝ) * ((M : ℝ) + 1) / r)) ^ d)) ^ (1 / p) *
          eLpNorm G (ENNReal.ofReal p) volume := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hp0 : 0 < p := by linarith
  obtain ⟨Cφ, hCφ0, hCφ⟩ := nrstr_phi_decay (d := d) (d + 1)
  set Bc : ℝ := Cφ / (r / (2 * d)) ^ (d + 1) with hBc
  have hBc0 : 0 ≤ Bc := by rw [hBc]; positivity
  set A : ℝ := (Bc ^ p * 4 ^ d * (r / d) ^ d) with hA
  have hA0 : 0 ≤ A := by rw [hA]; have := Real.rpow_nonneg hBc0 p; positivity
  refine ⟨(2 * A) ^ (1 / p) + 1, by positivity, fun M G hG => ?_⟩
  set N : ℝ := (d : ℝ) * ((M : ℝ) + 1) / r with hN
  have hNpos : 0 < N := by rw [hN]; positivity
  have hpne : ENNReal.ofReal p ≠ 0 := by simp [hp0]
  have hpt : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmeas1 : AEStronglyMeasurable (fun y : 𝔼 => nrstr_phi (d := d) (N⁻¹ • y) * G (Torus.mk y)) volume :=
    (((nrstr_phi (d := d)).continuous.comp (continuous_const_smul N⁻¹)).mul
      (hG.comp HRS.Torus.continuous_mk)).aestronglyMeasurable
  have hmeasG : AEStronglyMeasurable G (volume : Measure (Torus d)) := hG.aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpne hpt hmeas1,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hpne hpt hmeasG, ENNReal.toReal_ofReal hp0.le]
  set I : ℝ≥0∞ := ∫⁻ x, ‖G x‖ₑ ^ p with hI
  have hΨ : Measurable (fun x : Torus d => ‖G x‖ₑ ^ p) := hG.enorm.measurable.pow_const _
  -- box sets
  set Bj : ℕ → Set 𝔼 := fun j => leibt_boxN d (((2 ^ j * (M + 1) : ℕ) : ℝ) + 1 / 2) with hBj
  set aj : ℕ → ℝ := fun j => Bc * ((1 / 2 : ℝ) ^ j) ^ (d + 1) with haj
  have hstep1 : ∫⁻ y, ‖nrstr_phi (d := d) (N⁻¹ • y) * G (Torus.mk y)‖ₑ ^ p ≤
      ∫⁻ y, ∑' j, ENNReal.ofReal ((aj j) ^ p) * (Bj j).indicator (fun y => ‖G (Torus.mk y)‖ₑ ^ p) y := by
    refine lintegral_mono fun y => ?_
    obtain ⟨j, hjmem, hjb⟩ := nrstr_shell hd hr hr1 hCφ0 hCφ M y
    refine le_trans ?_ (ENNReal.le_tsum j)
    rw [Set.indicator_of_mem hjmem, enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
    refine mul_le_mul' ?_ le_rfl
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le]
    exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (norm_nonneg _) hjb hp0.le)
  have hstep2 : ∫⁻ y, ∑' j, ENNReal.ofReal ((aj j) ^ p) * (Bj j).indicator (fun y => ‖G (Torus.mk y)‖ₑ ^ p) y =
      ∑' j, ENNReal.ofReal ((aj j) ^ p) * (ENNReal.ofReal ((2 * (((2 ^ j * (M + 1) : ℕ) : ℝ) + 1 / 2)) ^ d) * I) := by
    rw [lintegral_tsum]
    · refine tsum_congr fun j => ?_
      rw [lintegral_const_mul]
      · congr 1
        rw [lintegral_indicator (leibt_measurableSet_boxN _)]
        have := leibt_lintegral_boxN (d := d) (η := 1) one_pos (2 ^ j * (M + 1)) (fun x => ‖G x‖ₑ ^ p) hΨ
        simp only [one_smul, div_one] at this
        exact this
      · exact (hΨ.comp HRS.Torus.continuous_mk.measurable).indicator (leibt_measurableSet_boxN _)
    · intro j
      exact ((hΨ.comp HRS.Torus.continuous_mk.measurable).indicator
        (leibt_measurableSet_boxN _)).const_mul _ |>.aemeasurable
  have hstep3 : ∑' j, ENNReal.ofReal ((aj j) ^ p) *
      (ENNReal.ofReal ((2 * (((2 ^ j * (M + 1) : ℕ) : ℝ) + 1 / 2)) ^ d) * I) ≤
      ENNReal.ofReal (2 * A * N ^ d) * I := by
    have hterm : ∀ j : ℕ, ENNReal.ofReal ((aj j) ^ p) *
        (ENNReal.ofReal ((2 * (((2 ^ j * (M + 1) : ℕ) : ℝ) + 1 / 2)) ^ d) * I) ≤
        ENNReal.ofReal (A * N ^ d * (1 / 2 : ℝ) ^ j) * I := by
      intro j
      rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg (by positivity) _)]
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
      have := nrstr_term d hd hr hCφ0 hp M j
      simpa [haj, hBc, hA, hN, mul_assoc, mul_comm, mul_left_comm] using this
    refine (ENNReal.tsum_le_tsum hterm).trans ?_
    rw [ENNReal.tsum_mul_right]
    refine mul_le_mul' (le_of_eq ?_) le_rfl
    have hsum : Summable fun j : ℕ => A * N ^ d * (1 / 2 : ℝ) ^ j :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hsum, tsum_mul_left,
      tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    congr 1
    norm_num
    ring
  have hmain : ∫⁻ y, ‖nrstr_phi (d := d) (N⁻¹ • y) * G (Torus.mk y)‖ₑ ^ p ≤ ENNReal.ofReal (2 * A * N ^ d) * I :=
    hstep1.trans (hstep2.le.trans hstep3)
  calc (∫⁻ y, ‖nrstr_phi (d := d) (N⁻¹ • y) * G (Torus.mk y)‖ₑ ^ p) ^ (1 / p)
      ≤ (ENNReal.ofReal (2 * A * N ^ d) * I) ^ (1 / p) := ENNReal.rpow_le_rpow hmain (by positivity)
    _ = ENNReal.ofReal ((2 * A) ^ (1 / p)) * ENNReal.ofReal (N ^ d) ^ (1 / p) * I ^ (1 / p) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ENNReal.ofReal_rpow_of_nonneg (by positivity)
            (by positivity)]
    _ ≤ ENNReal.ofReal ((2 * A) ^ (1 / p) + 1) * ENNReal.ofReal (N ^ d) ^ (1 / p) * I ^ (1 / p) := by
        gcongr
        linarith

end HRS.Commutator.TorusNote
