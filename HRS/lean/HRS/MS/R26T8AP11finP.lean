import HRS.MS.R26T8AP11fin
import HRS.MS.R26T8AP11sfP

/-!
# S8.2 nonlocal layer: dyadic sum of the nested jets of the annular pieces for the PURE conormal class (any sign of the order)
Copies of the `Conormal`/`0 <= sigma` versions with `ConormalP` (see `R26T8AP01p`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

theorem r26t8a_loc_sum_nestP (d : ℕ) (hd : 2 ≤ d) (k b : ℕ) (alpha M sigma : ℝ)
    (halpha : 0 < alpha) (had : alpha < d) (hM : 0 ≤ M) (hsd : sigma < d)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : Euc d → Euc d → ℝ, ∀ A : ℝ, 0 ≤ A → ConormalP k b M sigma A F →
      ∀ X z : Euc d, z ≠ 0 → ‖z‖ ≤ 2 → ∀ p q : ℕ, p + q ≤ k → ∀ N : ℕ,
        ∑ n ∈ Finset.range N, ‖r26t8a_nest p q
          (fun Yw : Euc d × Euc d => r26t8a_locV alpha chi ((1 / 2 : ℝ) ^ n) F Yw.1 Yw.2) X z‖ ≤
          C * A * jbracket X ^ (2 * M) *
            (1 + ‖z‖ ^ (alpha - sigma - q) * (1 + |Real.log ‖z‖|) ^ (b + 1)) := by
  obtain ⟨Cn, hCn0, hCn⟩ := r26t8a_locV_nearP d hd k b alpha M sigma halpha had hM chi hchi
  obtain ⟨Cf, hCf0, hCf⟩ := r26t8a_locV_farP d hd k b alpha M sigma halpha had hM chi hchi
  have hδ : 0 < (d : ℝ) - sigma := by linarith
  have hsb : ∀ q : ℕ, ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ r : ℝ, 0 < r → r ≤ 2 → ∀ N : ℕ,
      ∑ n ∈ Finset.range N, (if r ≤ 4 * ((1 : ℝ) / 2) ^ n then
          (((1 : ℝ) / 2) ^ n) ^ (alpha - sigma - (q : ℝ)) * (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b
        else (((1 : ℝ) / 2) ^ n) ^ ((d : ℝ) - sigma) * r ^ ((alpha - sigma - (q : ℝ)) - ((d : ℝ) - sigma)) *
          (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b) ≤
        Cs * (1 + r ^ (alpha - sigma - (q : ℝ)) * (1 + |Real.log r|) ^ (b + 1)) :=
    fun q => r26t8a_sum_bound b hδ (alpha - sigma - (q : ℝ))
  choose Cs hCs0 hCs using hsb
  refine ⟨(Cn + Cf) * ∑ q ∈ Finset.range (k + 1), Cs q,
    mul_nonneg (add_nonneg hCn0 hCf0) (Finset.sum_nonneg fun q _ => hCs0 q), ?_⟩
  intro F A hA hF X z hz0 hz2 p q hpq N
  have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hjb0 : 0 ≤ jbracket X ^ (2 * M) := Real.rpow_nonneg (s83_jb_pos X).le _
  have hterm : ∀ n ∈ Finset.range N, ‖r26t8a_nest p q
      (fun Yw : Euc d × Euc d => r26t8a_locV alpha chi ((1 / 2 : ℝ) ^ n) F Yw.1 Yw.2) X z‖ ≤
      ((Cn + Cf) * A * jbracket X ^ (2 * M)) * (if ‖z‖ ≤ 4 * ((1 : ℝ) / 2) ^ n then
          (((1 : ℝ) / 2) ^ n) ^ (alpha - sigma - (q : ℝ)) * (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b
        else (((1 : ℝ) / 2) ^ n) ^ ((d : ℝ) - sigma) * ‖z‖ ^ ((alpha - sigma - (q : ℝ)) - ((d : ℝ) - sigma)) *
          (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b) := by
    intro n _
    have hR : 0 < ((1 : ℝ) / 2) ^ n := by positivity
    have hR1 : ((1 : ℝ) / 2) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hbase : 0 ≤ (Cn + Cf) * A * jbracket X ^ (2 * M) := by positivity
    split_ifs with hnear
    · have h := hCn F A hA hF _ hR hR1 X z hnear p q hpq
      calc _ ≤ Cn * A * jbracket X ^ (2 * M) * (((1 : ℝ) / 2) ^ n) ^ (alpha - sigma - (q : ℝ)) *
            (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b := h
        _ ≤ _ := by
          have hp : 0 ≤ (((1 : ℝ) / 2) ^ n) ^ (alpha - sigma - (q : ℝ)) * (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b := by
            positivity
          have : Cn * A * jbracket X ^ (2 * M) ≤ (Cn + Cf) * A * jbracket X ^ (2 * M) := by
            have := mul_nonneg (mul_nonneg hCf0 hA) hjb0
            nlinarith
          calc Cn * A * jbracket X ^ (2 * M) * (((1 : ℝ) / 2) ^ n) ^ (alpha - sigma - (q : ℝ)) *
                (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b
              = (Cn * A * jbracket X ^ (2 * M)) * ((((1 : ℝ) / 2) ^ n) ^ (alpha - sigma - (q : ℝ)) *
                (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right this hp
    · push Not at hnear
      have h := hCf F A hA hF _ hR hR1 X z hz0 hz2 (by linarith) p q hpq
      have e : ‖z‖ ^ ((alpha - sigma - (q : ℝ)) - ((d : ℝ) - sigma)) = ‖z‖ ^ (alpha - (d : ℝ) - q) := by
        congr 1; ring
      rw [e]
      calc _ ≤ Cf * A * jbracket X ^ (2 * M) * ((((1 : ℝ) / 2) ^ n) ^ ((d : ℝ) - sigma) *
            ‖z‖ ^ (alpha - (d : ℝ) - q)) * (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b := h
        _ ≤ _ := by
          have hp : 0 ≤ (((1 : ℝ) / 2) ^ n) ^ ((d : ℝ) - sigma) * ‖z‖ ^ (alpha - (d : ℝ) - q) *
              (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b := by positivity
          have : Cf * A * jbracket X ^ (2 * M) ≤ (Cn + Cf) * A * jbracket X ^ (2 * M) := by
            have := mul_nonneg (mul_nonneg hCn0 hA) hjb0
            nlinarith
          calc Cf * A * jbracket X ^ (2 * M) * ((((1 : ℝ) / 2) ^ n) ^ ((d : ℝ) - sigma) *
                ‖z‖ ^ (alpha - (d : ℝ) - q)) * (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b
              = (Cf * A * jbracket X ^ (2 * M)) * ((((1 : ℝ) / 2) ^ n) ^ ((d : ℝ) - sigma) *
                ‖z‖ ^ (alpha - (d : ℝ) - q) * (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right this hp
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have h1 := hCs q ‖z‖ hzpos hz2 N
  have hbase : 0 ≤ (Cn + Cf) * A * jbracket X ^ (2 * M) := by positivity
  have hqs : Cs q ≤ ∑ q' ∈ Finset.range (k + 1), Cs q' :=
    Finset.single_le_sum (f := Cs) (fun i _ => hCs0 i) (Finset.mem_range.2 (by omega))
  have h2 : 0 ≤ 1 + ‖z‖ ^ (alpha - sigma - (q : ℝ)) * (1 + |Real.log ‖z‖|) ^ (b + 1) := by positivity
  calc (Cn + Cf) * A * jbracket X ^ (2 * M) * _ ≤ (Cn + Cf) * A * jbracket X ^ (2 * M) *
        (Cs q * (1 + ‖z‖ ^ (alpha - sigma - (q : ℝ)) * (1 + |Real.log ‖z‖|) ^ (b + 1))) :=
        mul_le_mul_of_nonneg_left h1 hbase
    _ ≤ (Cn + Cf) * A * jbracket X ^ (2 * M) *
        ((∑ q' ∈ Finset.range (k + 1), Cs q') * (1 + ‖z‖ ^ (alpha - sigma - (q : ℝ)) * (1 + |Real.log ‖z‖|) ^ (b + 1))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hqs h2) hbase
    _ = _ := by ring

end HRS.MS.R26T8A
