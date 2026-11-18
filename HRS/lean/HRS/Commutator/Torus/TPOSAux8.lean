import HRS.Commutator.Torus.TPOSAux7

/-!
# T-POS helpers, part 8: `gTcoef`, scaling, decay, summability, coefficient bounds
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ} {s η : ℝ}

lemma tpos_toEuc_ne_zero {k : Lattice d} (hk : k ≠ 0) : 0 < ‖Lattice.toEuc k‖ :=
  lt_of_lt_of_le one_pos (one_le_enorm k hk)

lemma tpos_gTcoef_eq (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (hη : 0 < η) {k : Lattice d}
    (hk : k ≠ 0) :
    gTcoef d s η k = tScale s * η ^ ((d : ℝ) - s) * Whole.g1Hat s (η • Lattice.toEuc k) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hr := tpos_toEuc_ne_zero hk
  set r := ‖Lattice.toEuc k‖ with hr_def
  set m : ℝ := (d : ℝ) - s - 1 with hm
  set F : ℝ → ℝ := fun t => t ^ m * Whole.phiHatR d (t * r) with hF
  have hFint : IntegrableOn F (Set.Ioi 0) := tpos_F_integrable hs0 hsd hr
  have hmell := tpos_rieszCoeff_mellin hs0 hsd k hk
  have hfh : fHatEta d s η (Lattice.toEuc k) = Whole.cPhi d s * ∫ t in Set.Ioc (0 : ℝ) η, F t := by
    rw [tpos_fHatEta_eq]
  have hsplit : ∫ t in Set.Ioi (0 : ℝ), F t =
      (∫ t in Set.Ioc (0 : ℝ) η, F t) + ∫ t in Set.Ioi η, F t := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi hη.le]
    exact setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hFint.mono_set Set.Ioc_subset_Ioi_self) (hFint.mono_set (Set.Ioi_subset_Ioi hη.le))
  have hscale := integral_comp_mul_left_Ioi F 1 hη
  simp only [mul_one, smul_eq_mul] at hscale
  have hnorm : ‖η • Lattice.toEuc k‖ = η * r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη]
  have hg1 : Whole.g1Hat s (η • Lattice.toEuc k) =
      Whole.cPhi d s * ∫ t in Set.Ioi (1 : ℝ), t ^ m * Whole.phiHatR d (t * (η * r)) := by
    rw [Whole.g1Hat_eq, hnorm]
  have hFη : ∀ u : ℝ, 0 < u → F (η * u) = η ^ m * (u ^ m * Whole.phiHatR d (u * (η * r))) := by
    intro u hu
    simp only [hF]
    rw [Real.mul_rpow hη.le hu.le]
    have : η * u * r = u * (η * r) := by ring
    rw [this]; ring
  have hI1 : ∫ t in Set.Ioi (1 : ℝ), F (η * t) =
      η ^ m * ∫ t in Set.Ioi (1 : ℝ), t ^ m * Whole.phiHatR d (t * (η * r)) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
    exact hFη u (lt_trans one_pos hu)
  have hIη : ∫ t in Set.Ioi η, F t = η * (η ^ m * ∫ t in Set.Ioi (1 : ℝ), t ^ m *
      Whole.phiHatR d (t * (η * r))) := by
    rw [← hI1, hscale]
    field_simp
  unfold gTcoef
  rw [if_neg hk, hmell, hfh, hsplit, hIη, hg1]
  have : η * η ^ m = η ^ ((d : ℝ) - s) := by
    rw [hm, show (d : ℝ) - s = ((d : ℝ) - s - 1) + 1 by ring, Real.rpow_add hη, Real.rpow_one]
    simp only [add_sub_cancel_right]
    ring
  calc tScale s * Whole.cPhi d s * ((∫ t in Set.Ioc (0 : ℝ) η, F t) +
        η * (η ^ m * ∫ t in Set.Ioi (1 : ℝ), t ^ m * Whole.phiHatR d (t * (η * r)))) -
        tScale s * (Whole.cPhi d s * ∫ t in Set.Ioc (0 : ℝ) η, F t)
      = tScale s * (η * η ^ m) * (Whole.cPhi d s * ∫ t in Set.Ioi (1 : ℝ),
          t ^ m * Whole.phiHatR d (t * (η * r))) := by ring
    _ = _ := by rw [this]

lemma tpos_gTcoef_nonneg (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (hη : 0 < η) (k : Lattice d) :
    0 ≤ gTcoef d s η k := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  by_cases hk : k = 0
  · simp [gTcoef, hk]
  · rw [tpos_gTcoef_eq hs0 hsd hη hk]
    have hts : 0 ≤ tScale s := by unfold tScale; split_ifs <;> linarith
    exact mul_nonneg (mul_nonneg hts (Real.rpow_nonneg hη.le _))
      (Whole.g1Hat_nonneg hs0 (by linarith) _)

lemma tpos_gTcoef_neg (k : Lattice d) : gTcoef d s η (-k) = gTcoef d s η k := by
  unfold gTcoef
  by_cases hk : k = 0
  · simp [hk]
  · have : ¬ (-k = 0) := fun h => hk (neg_eq_zero.1 h)
    rw [if_neg this, if_neg hk, rieszCoeff_neg]
    have h1 : fHatEta d s η (Lattice.toEuc (-k)) = fHatEta d s η (Lattice.toEuc k) := by
      rw [tpos_fHatEta_eq, tpos_fHatEta_eq]
      have : ‖Lattice.toEuc (-k)‖ = ‖Lattice.toEuc k‖ := by
        have := enorm_neg k
        exact this
      rw [this]
    rw [h1]

lemma tpos_g1Hat_decay (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ζ : Euc d, ζ ≠ 0 → Whole.g1Hat s ζ ≤ C * ‖ζ‖ ^ (-((d : ℝ) + 1)) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hb : (0 : ℝ) < (d : ℝ) + 1 := by linarith
  obtain ⟨Cb, hCb, hdec⟩ := tpos_phiHatR_decay (d := d) hb
  have hs2 : s < 2 * (d : ℝ) + 4 := by linarith
  have hcp := Whole.cPhi_pos d hs0 hs2
  set m : ℝ := (d : ℝ) - s - 1 with hm
  have hJint : IntegrableOn (fun t : ℝ => t ^ (m - ((d : ℝ) + 1))) (Set.Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by rw [hm]; linarith) one_pos
  set J : ℝ := ∫ t in Set.Ioi (1 : ℝ), t ^ (m - ((d : ℝ) + 1)) with hJ
  have hJ0 : 0 ≤ J := setIntegral_nonneg measurableSet_Ioi (fun t ht => by
    have : 0 < t := lt_trans one_pos ht
    positivity)
  refine ⟨Whole.cPhi d s * (Cb * J), by positivity, fun ζ hζ => ?_⟩
  have hρ : 0 < ‖ζ‖ := norm_pos_iff.2 hζ
  rw [Whole.g1Hat_eq]
  have key : ∫ t in Set.Ioi (1 : ℝ), t ^ m * Whole.phiHatR d (t * ‖ζ‖) ≤
      ∫ t in Set.Ioi (1 : ℝ), (Cb * ‖ζ‖ ^ (-((d : ℝ) + 1))) * t ^ (m - ((d : ℝ) + 1)) := by
    refine integral_mono_of_nonneg ?_ (hJint.const_mul _) ?_
    · filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (1 : ℝ)))] with t ht
      have : 0 < t := lt_trans one_pos ht
      have := Whole.phiHatR_pos (d := d) (t * ‖ζ‖)
      show 0 ≤ t ^ m * Whole.phiHatR d (t * ‖ζ‖)
      positivity
    · filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (1 : ℝ)))] with t ht
      have ht0 : 0 < t := lt_trans one_pos ht
      have h1 := hdec (t * ‖ζ‖) (by positivity)
      have h2 : (t * ‖ζ‖) ^ (-((d : ℝ) + 1)) = t ^ (-((d : ℝ) + 1)) * ‖ζ‖ ^ (-((d : ℝ) + 1)) :=
        Real.mul_rpow ht0.le hρ.le
      have h3 : t ^ m * t ^ (-((d : ℝ) + 1)) = t ^ (m - ((d : ℝ) + 1)) := by
        rw [← Real.rpow_add ht0]; congr 1 <;> ring
      show t ^ m * Whole.phiHatR d (t * ‖ζ‖) ≤ (Cb * ‖ζ‖ ^ (-((d : ℝ) + 1))) * t ^ (m - ((d : ℝ) + 1))
      calc t ^ m * Whole.phiHatR d (t * ‖ζ‖) ≤ t ^ m * (Cb * (t * ‖ζ‖) ^ (-((d : ℝ) + 1))) :=
            mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg ht0.le _)
        _ = (Cb * ‖ζ‖ ^ (-((d : ℝ) + 1))) * (t ^ m * t ^ (-((d : ℝ) + 1))) := by rw [h2]; ring
        _ = _ := by rw [h3]
  rw [integral_const_mul] at key
  calc Whole.cPhi d s * ∫ t in Set.Ioi (1 : ℝ), t ^ m * Whole.phiHatR d (t * ‖ζ‖)
      ≤ Whole.cPhi d s * ((Cb * ‖ζ‖ ^ (-((d : ℝ) + 1))) * J) :=
        mul_le_mul_of_nonneg_left key hcp.le
    _ = _ := by ring

lemma tpos_gTcoef_summable (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (hη : 0 < η) :
    Summable (fun k : Lattice d => |gTcoef d s η k|) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  obtain ⟨C, hC, hdec⟩ := tpos_g1Hat_decay (d := d) hs0 hsd
  have hts : 0 ≤ tScale s := by unfold tScale; split_ifs <;> linarith
  have hs := (tpos_summable_rpow (d := d) (r := (d : ℝ) + 1) (by linarith)).mul_left
    (tScale s * η ^ ((d : ℝ) - s) * (C * η ^ (-((d : ℝ) + 1))))
  refine Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_) hs
  by_cases hk : k = 0
  · have : Lattice.toEuc (0 : Lattice d) = 0 := by ext i; simp [Lattice.toEuc]
    subst hk
    have h0 : (0 : ℝ) ^ (-((d : ℝ) + 1)) = 0 := Real.zero_rpow (by linarith)
    have h1 : |gTcoef d s η 0| = 0 := by simp [gTcoef]
    rw [h1, this, norm_zero, h0, mul_zero]
  · have hr := tpos_toEuc_ne_zero hk
    rw [abs_of_nonneg (tpos_gTcoef_nonneg hs0 hsd hη k), tpos_gTcoef_eq hs0 hsd hη hk]
    have hz : η • Lattice.toEuc k ≠ 0 := by
      intro h
      have := congrArg norm h
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη, norm_zero] at this
      exact absurd this (mul_pos hη hr).ne'
    have h1 := hdec _ hz
    have hnorm : ‖η • Lattice.toEuc k‖ = η * ‖Lattice.toEuc k‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hη]
    rw [hnorm, Real.mul_rpow hη.le hr.le] at h1
    calc tScale s * η ^ ((d : ℝ) - s) * Whole.g1Hat s (η • Lattice.toEuc k)
        ≤ tScale s * η ^ ((d : ℝ) - s) * (C * (η ^ (-((d : ℝ) + 1)) *
          ‖Lattice.toEuc k‖ ^ (-((d : ℝ) + 1)))) :=
          mul_le_mul_of_nonneg_left h1 (mul_nonneg hts (Real.rpow_nonneg hη.le _))
      _ = _ := by ring

end HRS.Commutator.TorusNote
