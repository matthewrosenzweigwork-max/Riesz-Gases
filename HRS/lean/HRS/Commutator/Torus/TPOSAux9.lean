import HRS.Commutator.Torus.TPOSAux8

/-!
# T-POS helpers, part 9: coefficient bounds (`tr_coef_bounds`)
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ} {s η : ℝ}

lemma tpos_tScale_pos (hs0 : 0 ≤ s) : 0 < tScale s := by
  unfold tScale
  split_ifs with h
  · exact one_pos
  · exact lt_of_le_of_ne hs0 (Ne.symm h)

lemma tpos_coef_bounds (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ k : Lattice d, k ≠ 0 →
      0 ≤ gTcoef d s η k ∧
      (η * Lattice.enorm k ≤ 8 → c * (2 * Real.pi * Lattice.enorm k) ^ (-((d : ℝ) - s)) ≤ gTcoef d s η k) ∧
      c * η ^ ((d : ℝ) - s) * (1 + 4 * Real.pi ^ 2 * η ^ 2 * Lattice.enorm k ^ 2) ^ (-(Whole.alphaE d s)) ≤
        tScale s * fHatEta d s η (Lattice.toEuc k) := by
  have hts := tpos_tScale_pos hs0
  obtain ⟨cR, hcR, hlow⟩ := Whole.lowcoercive (d := d) (s := s) hd hs0 hsd 8 (by norm_num)
  obtain ⟨cS, hcS, hshort⟩ := Whole.shortcoercive (d := d) (s := s) hd hs0 hsd
  refine ⟨min (tScale s * cR * (2 * Real.pi) ^ ((d : ℝ) - s)) (tScale s * cS),
    lt_min (by positivity) (by positivity), fun η hη hη1 k hk => ?_⟩
  have hr := tpos_toEuc_ne_zero hk
  have hen : Lattice.enorm k = ‖Lattice.toEuc k‖ := rfl
  have hnorm : ‖η • Lattice.toEuc k‖ = η * ‖Lattice.toEuc k‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη]
  have hz : η • Lattice.toEuc k ≠ 0 := by
    intro h
    have := congrArg norm h
    rw [hnorm, norm_zero] at this
    exact absurd this (mul_pos hη hr).ne'
  refine ⟨tpos_gTcoef_nonneg hs0 hsd hη k, fun h8 => ?_, ?_⟩
  · rw [tpos_gTcoef_eq hs0 hsd hη hk]
    have h8' : ‖η • Lattice.toEuc k‖ ≤ 8 := by rw [hnorm]; rw [hen] at h8; exact h8
    have h1 := hlow _ hz h8'
    rw [Whole.alphaE_two_mul, hnorm, Real.mul_rpow hη.le hr.le] at h1
    have hηp : η ^ ((d : ℝ) - s) * η ^ (-((d : ℝ) - s)) = 1 := by
      rw [← Real.rpow_add hη]; simp
    rw [hen, Real.mul_rpow (by positivity) hr.le]
    have hmin : min (tScale s * cR * (2 * Real.pi) ^ ((d : ℝ) - s)) (tScale s * cS) *
        (2 * Real.pi) ^ (-((d : ℝ) - s)) ≤ tScale s * cR := by
      have h2 : (2 * Real.pi) ^ ((d : ℝ) - s) * (2 * Real.pi) ^ (-((d : ℝ) - s)) = 1 := by
        rw [← Real.rpow_add (by positivity)]; simp
      calc min (tScale s * cR * (2 * Real.pi) ^ ((d : ℝ) - s)) (tScale s * cS) *
            (2 * Real.pi) ^ (-((d : ℝ) - s))
          ≤ (tScale s * cR * (2 * Real.pi) ^ ((d : ℝ) - s)) * (2 * Real.pi) ^ (-((d : ℝ) - s)) :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)
        _ = tScale s * cR := by
            calc (tScale s * cR * (2 * Real.pi) ^ ((d : ℝ) - s)) * (2 * Real.pi) ^ (-((d : ℝ) - s))
                = tScale s * cR * ((2 * Real.pi) ^ ((d : ℝ) - s) * (2 * Real.pi) ^ (-((d : ℝ) - s))) := by ring
              _ = _ := by rw [h2, mul_one]
    have hrp : 0 ≤ ‖Lattice.toEuc k‖ ^ (-((d : ℝ) - s)) := Real.rpow_nonneg hr.le _
    calc min (tScale s * cR * (2 * Real.pi) ^ ((d : ℝ) - s)) (tScale s * cS) *
          ((2 * Real.pi) ^ (-((d : ℝ) - s)) * ‖Lattice.toEuc k‖ ^ (-((d : ℝ) - s)))
        = (min (tScale s * cR * (2 * Real.pi) ^ ((d : ℝ) - s)) (tScale s * cS) *
            (2 * Real.pi) ^ (-((d : ℝ) - s))) * ‖Lattice.toEuc k‖ ^ (-((d : ℝ) - s)) := by ring
      _ ≤ (tScale s * cR) * ‖Lattice.toEuc k‖ ^ (-((d : ℝ) - s)) :=
          mul_le_mul_of_nonneg_right hmin hrp
      _ = tScale s * (η ^ ((d : ℝ) - s) * η ^ (-((d : ℝ) - s))) * (cR * ‖Lattice.toEuc k‖ ^ (-((d : ℝ) - s))) := by
          rw [hηp]; ring
      _ = tScale s * η ^ ((d : ℝ) - s) * (cR * (η ^ (-((d : ℝ) - s)) * ‖Lattice.toEuc k‖ ^ (-((d : ℝ) - s)))) := by ring
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left h1 (by positivity)
  · rw [tpos_fHatEta_scale hη]
    have h1 := hshort (η • Lattice.toEuc k)
    rw [hnorm] at h1
    have e : 1 + 4 * Real.pi ^ 2 * (η * ‖Lattice.toEuc k‖) ^ 2 =
        1 + 4 * Real.pi ^ 2 * η ^ 2 * Lattice.enorm k ^ 2 := by rw [hen]; ring
    rw [e] at h1
    have hηp : 0 ≤ η ^ ((d : ℝ) - s) := Real.rpow_nonneg hη.le _
    calc min (tScale s * cR * (2 * Real.pi) ^ ((d : ℝ) - s)) (tScale s * cS) * η ^ ((d : ℝ) - s) *
          (1 + 4 * Real.pi ^ 2 * η ^ 2 * Lattice.enorm k ^ 2) ^ (-(Whole.alphaE d s))
        ≤ (tScale s * cS) * η ^ ((d : ℝ) - s) *
          (1 + 4 * Real.pi ^ 2 * η ^ 2 * Lattice.enorm k ^ 2) ^ (-(Whole.alphaE d s)) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_right _ _) hηp)
            (Real.rpow_nonneg (by positivity) _)
      _ = tScale s * η ^ ((d : ℝ) - s) * (cS * (1 + 4 * Real.pi ^ 2 * η ^ 2 * Lattice.enorm k ^ 2) ^
            (-(Whole.alphaE d s))) := by ring
      _ ≤ tScale s * η ^ ((d : ℝ) - s) * Whole.f1Hat s (η • Lattice.toEuc k) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by ring

end HRS.Commutator.TorusNote
