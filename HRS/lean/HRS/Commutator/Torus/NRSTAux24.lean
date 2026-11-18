import HRS.Commutator.Torus.NRSTAux23
import HRS.Commutator.Torus.LEIBTAux20

/-!
# NRS-T, part 24: lower bound for `‖φ(·/N) G(mk ·)‖_p` against the torus norm of `G`
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace
  ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS HRS.Commutator.TorusNote.NRST

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma nrstr_phi_lower : ∃ r c : ℝ, 0 < r ∧ r ≤ 1 ∧ 0 < c ∧ ∀ y : 𝔼, ‖y‖ ≤ r → c ≤ ‖nrstr_phi (d := d) y‖ := by
  set P0 : ℝ := ∫ v : 𝔼, ((nrstr_bumpE (d := d)) v : ℝ) with hP0
  have hP : 0 < P0 := nrstr_phi_zero_pos
  have hcont : ContinuousAt (nrstr_phi (d := d)) 0 := (nrstr_phi (d := d)).continuous.continuousAt
  obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.1 hcont (P0 / 2) (by positivity)
  refine ⟨min (δ / 2) 1, P0 / 2, by positivity, min_le_right _ _, by positivity, fun y hy => ?_⟩
  have hy' : dist y 0 < δ := by
    rw [dist_zero_right]
    calc ‖y‖ ≤ min (δ / 2) 1 := hy
      _ ≤ δ / 2 := min_le_left _ _
      _ < δ := by linarith
  have h1 := hδ' hy'
  rw [dist_eq_norm, nrstr_phi_zero] at h1
  have h2 : ‖((P0 : ℝ) : ℂ)‖ = P0 := by rw [Complex.norm_real, Real.norm_of_nonneg hP.le]
  have h3 : ‖((P0 : ℝ) : ℂ)‖ ≤ ‖nrstr_phi (d := d) y‖ + ‖nrstr_phi (d := d) y - ((P0 : ℝ) : ℂ)‖ := by
    have := norm_sub_norm_le ((P0 : ℝ) : ℂ) (nrstr_phi (d := d) y)
    rw [norm_sub_rev] at this
    linarith
  linarith

lemma nrstr_norm_le_of_box (hd : 1 ≤ d) {N0 : ℝ} (hN0 : 0 ≤ N0) {y : 𝔼} (hy : y ∈ leibt_boxN d N0) :
    ‖y‖ ≤ d * N0 := by
  have h1 : ∀ i, |y i| ≤ N0 := by
    intro i
    have := hy i
    rw [mem_Ioc] at this
    exact abs_le.2 ⟨this.1.le, this.2⟩
  have h2 : ‖y‖ ^ 2 = ∑ i, (y i) ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
    simp
  have h3 : ∑ i, (y i) ^ 2 ≤ d * N0 ^ 2 := by
    calc ∑ i, (y i) ^ 2 ≤ ∑ _i : Fin d, N0 ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (h1 i) 2
      _ = d * N0 ^ 2 := by simp
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h4 : ‖y‖ ^ 2 ≤ (d * N0) ^ 2 := by
    rw [h2]
    calc ∑ i, (y i) ^ 2 ≤ d * N0 ^ 2 := h3
      _ ≤ (d : ℝ) ^ 2 * N0 ^ 2 := by nlinarith [sq_nonneg N0]
      _ = (d * N0) ^ 2 := by ring
  exact le_of_sq_le_sq h4 (by positivity) |> fun h => by simpa using h

lemma nrstr_lower_bound (hd : 1 ≤ d) {r c : ℝ} (hr : 0 < r) (hc : 0 < c)
    (hφ : ∀ y : 𝔼, ‖y‖ ≤ r → c ≤ ‖nrstr_phi (d := d) y‖) {p : ℝ≥0∞} (hp : p ≠ 0) (hpt : p ≠ ⊤)
    (M : ℕ) {G : Torus d → ℂ} (hG : Continuous G) :
    ENNReal.ofReal c * (ENNReal.ofReal ((2 * ((M : ℝ) + 1 / 2)) ^ d)) ^ (1 / p.toReal) *
        eLpNorm G p volume ≤
      eLpNorm (fun y : 𝔼 => nrstr_phi (d := d) (((d : ℝ) * ((M : ℝ) + 1) / r)⁻¹ • y) * G (Torus.mk y))
        p volume := by
  have hbox := leibt_eLpNorm_box_eq (d := d) (η := 1) one_pos M (N := ((M : ℝ) + 1 / 2) / 1) rfl hG hp hpt
  simp only [one_smul, div_one] at hbox
  set N : ℝ := (d : ℝ) * ((M : ℝ) + 1) / r with hN
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hNpos : 0 < N := by rw [hN]; positivity
  have hmeas : AEStronglyMeasurable ((c : ℂ) • (leibt_boxN d ((M : ℝ) + 1 / 2)).indicator
      (fun y : 𝔼 => G (Torus.mk y))) volume := by
    refine AEStronglyMeasurable.const_smul ?_ _
    exact (hG.comp HRS.Torus.continuous_mk).aestronglyMeasurable.indicator (leibt_measurableSet_boxN _)
  have hle : eLpNorm ((c : ℂ) • (leibt_boxN d ((M : ℝ) + 1 / 2)).indicator
      (fun y : 𝔼 => G (Torus.mk y))) p volume ≤
      eLpNorm (fun y : 𝔼 => nrstr_phi (d := d) (N⁻¹ • y) * G (Torus.mk y)) p volume := by
    refine eLpNorm_mono hmeas fun y => ?_
    by_cases hy : y ∈ leibt_boxN d ((M : ℝ) + 1 / 2)
    · simp only [Pi.smul_apply, Set.indicator_of_mem hy, smul_eq_mul, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg hc.le]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      refine hφ _ ?_
      rw [norm_smul, norm_inv, Real.norm_of_nonneg hNpos.le, inv_mul_le_iff₀ hNpos]
      have := nrstr_norm_le_of_box hd (by positivity) hy
      rw [hN]
      calc ‖y‖ ≤ d * ((M : ℝ) + 1 / 2) := this
        _ ≤ N * r := by
          rw [hN]
          have : (d : ℝ) * ((M : ℝ) + 1) / r * r = d * ((M : ℝ) + 1) := by field_simp
          rw [this]
          nlinarith
    · rw [Pi.smul_apply, Set.indicator_of_notMem hy, smul_zero, norm_zero]
      positivity
  refine le_trans (le_of_eq ?_) hle
  rw [eLpNorm_const_smul, hbox, ← mul_assoc]
  congr 1
  rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg hc.le]

end HRS.Commutator.TorusNote
