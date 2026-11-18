import HRS.MS.SA12V3Q
import HRS.MH.ScreenedA3a

/-!
# S.A.12 C2 (SA12V3 worker), part R: the weighted bound `varpiNormE (periodicDatum …) ≤ C varpiNormE φ`

From the master cell bound (part O), the weight comparison (part Q), the Cauchy-Schwarz and fibre lemmas (part P)
and `∑' k, ⟨k⟩^{-(d+3)} < ∞`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Pointwise

namespace HRS.MH.AdjointRd.Phase2SA12V3

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
  HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

theorem sa12v3_cellPt_ball_card (hd : 1 ≤ d) (X : Euc d) :
    ∃ B : Finset (Fin d → ℤ), (∀ z : Fin d → ℤ, ‖cellPt d z - X‖ ≤ 1 / 2 → z ∈ B) ∧
      B.card ≤ (⌈Real.sqrt d⌉₊ + 2) ^ d := by
  have hN : (1 : ℝ) ≤ (⌈Real.sqrt d⌉₊ : ℝ) := by
    have : (1 : ℝ) ≤ Real.sqrt d := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hd)
    exact this.trans (Nat.le_ceil _)
  have hNpos : (0 : ℝ) < (⌈Real.sqrt d⌉₊ : ℝ) := by linarith
  obtain ⟨B, hB, hcard⟩ := sa12v3_box_card ((⌈Real.sqrt d⌉₊ : ℝ)⁻¹) (inv_pos.2 hNpos) X (1 / 2) (by norm_num)
  refine ⟨B, fun z hz => hB z fun i => ?_, ?_⟩
  · have h1 := PiLp.norm_apply_le (cellPt d z - X) i
    have e : (cellPt d z - X) i = (⌈Real.sqrt d⌉₊ : ℝ)⁻¹ * (z i : ℝ) - X i := by
      rw [sa12v3_cellPt_eq]; simp [HRS.MS.UlocCut.uc_fp, latticePt]
    rw [e, Real.norm_eq_abs] at h1
    exact h1.trans hz
  · have e : 2 * (1 / 2 : ℝ) / (⌈Real.sqrt d⌉₊ : ℝ)⁻¹ + 2 = (⌈Real.sqrt d⌉₊ : ℝ) + 2 := by
      field_simp
    rw [e] at hcard
    exact_mod_cast hcard

theorem sa12v3_pd_varpi (hd : 1 ≤ d) {η χ ζ : Euc d → ℝ} (hη : IsMollifier η) (hχ : IsUlocCutoff χ)
    (hζ : HRS.Whole.AppendixALemmas.IsCutoffRad (1 / 4) (1 / 3) ζ) (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ φ : Euc d → ℝ, ulocNormE m χ φ < ⊤ → ∀ L ε : ℝ, 1 ≤ L → 0 < ε →
      varpiNormE m χ (periodicDatum ζ η L ε φ) ≤ ENNReal.ofReal C * varpiNormE m χ φ := by
  classical
  obtain ⟨J, C0, hC0, hmaster⟩ := sa12v3_pd_master hη hχ hζ m
  set Dj : ℝ := ∑ j ∈ J, ‖cellPt d j‖ with hDjdef
  have hDj0 : 0 ≤ Dj := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hDj : ∀ j ∈ J, ‖cellPt d j‖ ≤ Dj := fun j hj =>
    Finset.single_le_sum (f := fun j => ‖cellPt d j‖) (fun _ _ => norm_nonneg _) hj
  obtain ⟨Qw, hQw, hcmp⟩ := sa12v3_weight_cmp (d := d) (1 / 2 + Dj) (by positivity)
  set M : ℕ := (⌈Real.sqrt d⌉₊ + 2) ^ d with hM
  set Scw : ℝ≥0∞ := ∑' k : Fin d → ℤ, ENNReal.ofReal (cellWeight d k) with hScwdef
  have hScw : Scw < ⊤ := HRS.MH.Screened.cellWeight_tsum_lt_top_proof hd
  set N0 : ℕ := 7 ^ d * J.card with hN0
  set Kc : ℝ≥0∞ := (N0 : ℝ≥0∞) * ENNReal.ofReal C0 ^ 2 * (J.card : ℝ≥0∞) * ENNReal.ofReal Qw * (M : ℝ≥0∞) * Scw
    with hKcdef
  have hKc : Kc ≠ ⊤ := by
    simp only [hKcdef]
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.pow_ne_top ENNReal.ofReal_ne_top))
      (ENNReal.natCast_ne_top _)) ENNReal.ofReal_ne_top) (ENNReal.natCast_ne_top _)) hScw.ne
  refine ⟨Kc.toReal ^ (1 / 2 : ℝ) + 1, by positivity, fun φ hφ L ε hL hε => ?_⟩
  have hL0 : 0 < L := lt_of_lt_of_le one_pos hL
  set wz : (Fin d → ℤ) → ℝ≥0∞ := fun z => ENNReal.ofReal (jbracket (cellPt d z) ^ (-((d : ℝ) + 3))) with hwz
  set a : (Fin d → ℤ) → ℝ≥0∞ := fun t => sa12v3_cell m χ (cellPt d t) φ with ha
  have ha_fin : ∀ t, a t ≠ ⊤ := fun t => ne_top_of_le_ne_top hφ.ne
    (le_iSup (fun z : Euc d => sobolevNormE (m : ℝ) fun x => χ (x - z) * φ x) (cellPt d t))
  choose K k₀ hK hKsub hcard hk hle using fun z : Fin d → ℤ => hmaster L ε hL hε (cellPt d z)
  set Vφ : ℝ≥0∞ := ∑' t, wz t * a t ^ 2 with hVφ
  -- Step 1: cell-wise bound
  have step1 : ∀ z, wz z * sa12v3_cell m χ (cellPt d z) (periodicDatum ζ η L ε φ) ^ 2 ≤
      (N0 : ℝ≥0∞) * ENNReal.ofReal C0 ^ 2 * ∑ j ∈ J, ∑' k, (if k ∈ K z then wz z * a (k₀ z k + j) ^ 2 else 0) := by
    intro z
    have h1 := hle z φ
    set f : (Fin d → ℤ) × (Fin d → ℤ) → ℝ≥0∞ := fun p => ENNReal.ofReal C0 * a (k₀ z p.1 + p.2) with hf
    have h1' : sa12v3_cell m χ (cellPt d z) (periodicDatum ζ η L ε φ) ≤ ∑ p ∈ K z ×ˢ J, f p := by
      rw [Finset.sum_product]; exact h1
    have h2 := pow_le_pow_left' h1' 2
    have h3 := sa12v3_sq_sum_le (K z ×ˢ J) f (fun p _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ha_fin _))
    have hcardp : ((K z ×ˢ J).card : ℝ≥0∞) ≤ N0 := by
      rw [Finset.card_product, hN0]
      have : (K z).card ≤ 7 ^ d := by exact_mod_cast hcard z
      exact_mod_cast Nat.mul_le_mul_right _ this
    have h4 : ∑ p ∈ K z ×ˢ J, f p ^ 2 = ENNReal.ofReal C0 ^ 2 * ∑ k ∈ K z, ∑ j ∈ J, a (k₀ z k + j) ^ 2 := by
      rw [Finset.sum_product, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hf, mul_pow]
    have h5 : ∑ k ∈ K z, ∑ j ∈ J, wz z * a (k₀ z k + j) ^ 2 =
        ∑ j ∈ J, ∑' k, (if k ∈ K z then wz z * a (k₀ z k + j) ^ 2 else 0) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [tsum_eq_sum (s := K z) (fun k hk => if_neg hk)]
      exact Finset.sum_congr rfl fun k hk => (if_pos hk).symm
    calc wz z * sa12v3_cell m χ (cellPt d z) (periodicDatum ζ η L ε φ) ^ 2
        ≤ wz z * ((N0 : ℝ≥0∞) * (ENNReal.ofReal C0 ^ 2 * ∑ k ∈ K z, ∑ j ∈ J, a (k₀ z k + j) ^ 2)) :=
          mul_le_mul' le_rfl (h2.trans (h3.trans (by rw [h4]; exact mul_le_mul' hcardp le_rfl)))
      _ = (N0 : ℝ≥0∞) * ENNReal.ofReal C0 ^ 2 * ∑ k ∈ K z, ∑ j ∈ J, wz z * a (k₀ z k + j) ^ 2 := by
          have : ∑ k ∈ K z, ∑ j ∈ J, wz z * a (k₀ z k + j) ^ 2 =
              wz z * ∑ k ∈ K z, ∑ j ∈ J, a (k₀ z k + j) ^ 2 := by
            simp only [← Finset.mul_sum]
          rw [this]; ring
      _ = _ := by rw [h5]
  -- Step 2: fibre bound for fixed (j, k)
  have step2 : ∀ (j : Fin d → ℤ) (k : Fin d → ℤ), j ∈ J →
      ∑' z, (if k ∈ K z then wz z * a (k₀ z k + j) ^ 2 else 0) ≤
        (ENNReal.ofReal Qw * ENNReal.ofReal (cellWeight d k)) * (M : ℝ≥0∞) * Vφ := by
    intro j k hj
    refine sa12v3_fiber_bound (fun z => k ∈ K z) wz wz a (fun z => k₀ z k + j) _ M ?_ ?_
    · intro z hz
      have hc' : ‖cellPt d z - L • latticePt k‖ < 2 + L / 3 := by
        have := hKsub z k hz
        rwa [norm_sub_rev] at this
      have hct : ‖cellPt d (k₀ z k + j) - (cellPt d z - L • latticePt k)‖ ≤ 1 / 2 + Dj := by
        have e : cellPt d (k₀ z k + j) = cellPt d (k₀ z k) + cellPt d j := by
          rw [sa12v3_cellPt_eq, sa12v3_cellPt_eq, sa12v3_cellPt_eq, ← HRS.MS.UlocCut.uc_fp_add]
        have h1 := hk z k
        rw [e]
        calc ‖cellPt d (k₀ z k) + cellPt d j - (cellPt d z - L • latticePt k)‖
            = ‖(cellPt d j) - ((cellPt d z - L • latticePt k) - cellPt d (k₀ z k))‖ := by congr 1; abel
          _ ≤ ‖cellPt d j‖ + ‖(cellPt d z - L • latticePt k) - cellPt d (k₀ z k)‖ := norm_sub_le _ _
          _ ≤ Dj + 1 / 2 := add_le_add (hDj j hj) h1
          _ = _ := by ring
      have h := hcmp L hL k (cellPt d z) (cellPt d (k₀ z k + j)) (cellPt d z - L • latticePt k) (by abel) hc' hct
      have hnn1 : 0 ≤ jbracket (cellPt d (k₀ z k + j)) ^ (-((d : ℝ) + 3)) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
      have hnn2 : 0 ≤ cellWeight d k := Real.rpow_nonneg (Real.sqrt_nonneg _) _
      calc wz z ≤ ENNReal.ofReal (Qw * jbracket (latticePt k : Euc d) ^ (-((d : ℝ) + 3)) *
            jbracket (cellPt d (k₀ z k + j)) ^ (-((d : ℝ) + 3))) := ENNReal.ofReal_le_ofReal h
        _ = (ENNReal.ofReal Qw * ENNReal.ofReal (cellWeight d k)) * wz (k₀ z k + j) := by
            have e : jbracket (latticePt k : Euc d) ^ (-((d : ℝ) + 3)) = cellWeight d k := rfl
            rw [e, ENNReal.ofReal_mul (mul_nonneg hQw.le hnn2), ENNReal.ofReal_mul hQw.le]
    · intro t
      obtain ⟨B, hB, hBc⟩ := sa12v3_cellPt_ball_card hd (L • latticePt k + cellPt d (t - j))
      refine ⟨B, fun z hz => hB z ?_, hBc⟩
      have hz' : k₀ z k + j = t := hz
      have : k₀ z k = t - j := by rw [← hz']; abel
      have h1 := hk z k
      rw [this] at h1
      calc ‖cellPt d z - (L • latticePt k + cellPt d (t - j))‖
          = ‖(cellPt d z - L • latticePt k) - cellPt d (t - j)‖ := by congr 1; abel
        _ ≤ 1 / 2 := h1
  -- Step 3: assembly
  have step3 : ∑' z, wz z * sa12v3_cell m χ (cellPt d z) (periodicDatum ζ η L ε φ) ^ 2 ≤ Kc * Vφ := by
    calc ∑' z, wz z * sa12v3_cell m χ (cellPt d z) (periodicDatum ζ η L ε φ) ^ 2
        ≤ ∑' z, (N0 : ℝ≥0∞) * ENNReal.ofReal C0 ^ 2 *
            ∑ j ∈ J, ∑' k, (if k ∈ K z then wz z * a (k₀ z k + j) ^ 2 else 0) :=
          ENNReal.tsum_le_tsum step1
      _ = (N0 : ℝ≥0∞) * ENNReal.ofReal C0 ^ 2 * ∑' z, ∑ j ∈ J, ∑' k,
            (if k ∈ K z then wz z * a (k₀ z k + j) ^ 2 else 0) := ENNReal.tsum_mul_left
      _ = (N0 : ℝ≥0∞) * ENNReal.ofReal C0 ^ 2 * ∑ j ∈ J, ∑' k, ∑' z,
            (if k ∈ K z then wz z * a (k₀ z k + j) ^ 2 else 0) := by
          rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
          congr 1
          refine Finset.sum_congr rfl fun j _ => ?_
          exact ENNReal.tsum_comm
      _ ≤ (N0 : ℝ≥0∞) * ENNReal.ofReal C0 ^ 2 * ∑ j ∈ J, ∑' k,
            (ENNReal.ofReal Qw * (M : ℝ≥0∞) * Vφ) * ENNReal.ofReal (cellWeight d k) := by
          refine mul_le_mul' le_rfl (Finset.sum_le_sum fun j hj => ENNReal.tsum_le_tsum fun k => ?_)
          refine (step2 j k hj).trans (le_of_eq ?_)
          ring
      _ = Kc * Vφ := by
          simp only [ENNReal.tsum_mul_left, Finset.sum_const, nsmul_eq_mul]
          rw [hKcdef]; rw [← hScwdef]; ring
  -- Step 4: the square root
  have hsq : varpiNormE m χ (periodicDatum ζ η L ε φ) ≤ (Kc * Vφ) ^ (1 / 2 : ℝ) :=
    ENNReal.rpow_le_rpow step3 (by norm_num)
  refine hsq.trans ?_
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  refine mul_le_mul' ?_ le_rfl
  have e : Kc ^ (1 / 2 : ℝ) = ENNReal.ofReal (Kc.toReal ^ (1 / 2 : ℝ)) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num), ENNReal.ofReal_toReal hKc]
  rw [e]
  exact ENNReal.ofReal_le_ofReal (by linarith)

end HRS.MH.AdjointRd.Phase2SA12V3
