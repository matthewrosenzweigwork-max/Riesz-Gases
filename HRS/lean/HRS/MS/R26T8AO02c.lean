import HRS.MS.R26T8AO02b

/-!
# S8.2 T8A O02 (part c): tameness of `Wb + Pj + Tr`
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82U HRS.MS.S82W HRS.MS.Wad

variable {d N : ℕ}

theorem r26t8a_o02_tame (hd : 2 ≤ d) {M M' : ℝ} (hM : 0 ≤ M) (hM' : 0 ≤ M') :
    u4Tame (fun X : EucConfig d N => r26t8a_o02_Wb M X + r26t8a_o02_Pj M' X + r26t8a_o02_Tr M' X) := by
  have hs : 0 ≤ criticalS d := (u4_crit_pos hd).le
  have hWb : u4Tame (fun X : EucConfig d N => r26t8a_o02_Wb M X) := w_wBq_tame hd hM zero_le_one
  -- pairWeight and pole comparisons
  have hpw : ∀ (X : EucConfig d N) (i j : Fin N), HRS.MS.Phase2S82.pairWeight M' (X i) (X j) ≤ (1 + ‖X‖) ^ (2 * M') := by
    intro X i j
    unfold HRS.MS.Phase2S82.pairWeight
    calc jbracket (X i) ^ M' * jbracket (X j) ^ M' ≤ (1 + ‖X‖) ^ M' * (1 + ‖X‖) ^ M' :=
          mul_le_mul (r26t8a_o02_jb_le hM' X i) (r26t8a_o02_jb_le hM' X j)
            (Real.rpow_nonneg (Real.sqrt_nonneg _) _) (Real.rpow_nonneg (by linarith [norm_nonneg X]) _)
      _ = (1 + ‖X‖) ^ (2 * M') := by
          rw [← Real.rpow_add (by linarith [norm_nonneg X])]; ring_nf
  have hpw0 : ∀ (x y : Euc d), 0 ≤ HRS.MS.Phase2S82.pairWeight M' x y := fun x y =>
    mul_nonneg (Real.rpow_nonneg (s83_jb_pos x).le _) (Real.rpow_nonneg (s83_jb_pos y).le _)
  have hr0 : ∀ (X : EucConfig d N) (i j : Fin N), 0 ≤ 2 + ‖X i - X j‖ ^ (-criticalS d) := fun X i j => by
    linarith [Real.rpow_nonneg (norm_nonneg (X i - X j)) (-criticalS d)]
  have hPj : u4Tame (fun X : EucConfig d N => r26t8a_o02_Pj M' X) := by
    have ht : u4Tame (fun X : EucConfig d N => ∑ i, ∑ j ∈ Finset.univ.erase i,
        (1 + ‖X‖) ^ (2 * M') * ((2 + ‖X i - X j‖ ^ (-criticalS d)) * (2 + ‖X i - X j‖ ^ (-criticalS d)))) := by
      refine u4Tame_sum _ _ fun i _ => u4Tame_sum _ _ fun j hj => ?_
      have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
      have hp := u4Tame_add (u4Tame_const (d := d) (N := N) 2) (u4Tame_pole hij hs)
      exact u4Tame_mul (u4Tame_onePlusNorm _ (by linarith)) (u4Tame_mul hp hp)
    refine u4Tame_of_le' ht fun X hX => ?_
    have hn : 0 ≤ r26t8a_o02_Pj M' X := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (hpw0 _ _) (sq_nonneg _)
    rw [abs_of_nonneg hn, abs_of_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (Real.rpow_nonneg (by linarith [norm_nonneg X]) _) (mul_nonneg (hr0 X i j) (hr0 X i j)))]
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    have hp0 := r26t8a_o02_pole_nonneg (X i) (X j)
    have hp1 := r26t8a_o02_pole_le X i j
    calc HRS.MS.Phase2S82.pairWeight M' (X i) (X j) * pole (X i) (X j) ^ 2
        ≤ (1 + ‖X‖) ^ (2 * M') * ((2 + ‖X i - X j‖ ^ (-criticalS d)) * (2 + ‖X i - X j‖ ^ (-criticalS d))) :=
          mul_le_mul (hpw X i j) (by nlinarith) (sq_nonneg _) (Real.rpow_nonneg (by linarith [norm_nonneg X]) _)
      _ = _ := rfl
  have hTr : u4Tame (fun X : EucConfig d N => r26t8a_o02_Tr M' X) := by
    set R : EucConfig d N → Fin N → Fin N → ℝ := fun X i j => 2 + ‖X i - X j‖ ^ (-criticalS d) with hR
    have ht : u4Tame (fun X : EucConfig d N => ∑ i, ∑ j ∈ Finset.univ.erase i, ∑ k ∈ (Finset.univ.erase i).erase j,
        (1 + ‖X‖) ^ (3 * M') * (R X i j * R X i k + R X i j * R X j k + R X i k * R X j k)) := by
      refine u4Tame_sum _ _ fun i _ => u4Tame_sum _ _ fun j hj => u4Tame_sum _ _ fun k hk => ?_
      have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
      have hki : k ≠ i := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)
      have hkj : k ≠ j := Finset.ne_of_mem_erase hk
      have pij := u4Tame_add (u4Tame_const (d := d) (N := N) 2) (u4Tame_pole hij hs)
      have pik := u4Tame_add (u4Tame_const (d := d) (N := N) 2) (u4Tame_pole hki.symm hs)
      have pjk := u4Tame_add (u4Tame_const (d := d) (N := N) 2) (u4Tame_pole hkj.symm hs)
      exact u4Tame_mul (u4Tame_onePlusNorm _ (by linarith))
        (u4Tame_add (u4Tame_add (u4Tame_mul pij pik) (u4Tame_mul pij pjk)) (u4Tame_mul pik pjk))
    refine u4Tame_of_le' ht fun X hX => ?_
    have hRn : ∀ i j, 0 ≤ R X i j := fun i j => hr0 X i j
    have hone : 0 ≤ (1 + ‖X‖) ^ (3 * M') := Real.rpow_nonneg (by linarith [norm_nonneg X]) _
    have hn : 0 ≤ r26t8a_o02_Tr M' X := by
      refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => ?_
      refine mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg (s83_jb_pos _).le _)
        (Real.rpow_nonneg (s83_jb_pos _).le _)) (Real.rpow_nonneg (s83_jb_pos _).le _)) ?_
      unfold triplePole
      have := r26t8a_o02_pole_nonneg (X i) (X j); have := r26t8a_o02_pole_nonneg (X i) (X k)
      have := r26t8a_o02_pole_nonneg (X j) (X k)
      positivity
    rw [abs_of_nonneg hn, abs_of_nonneg (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      Finset.sum_nonneg fun k _ => mul_nonneg hone (by have := hRn i j; have := hRn i k; have := hRn j k; positivity))]
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun k hk => ?_
    have hij : i ≠ j := (Finset.ne_of_mem_erase hj).symm
    have hki : k ≠ i := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hk)
    have hkj : k ≠ j := Finset.ne_of_mem_erase hk
    have a1 := r26t8a_o02_pole_le X i j
    have a2 := r26t8a_o02_pole_le X i k
    have a3 := r26t8a_o02_pole_le X j k
    have b1 := r26t8a_o02_pole_nonneg (X i) (X j)
    have b2 := r26t8a_o02_pole_nonneg (X i) (X k)
    have b3 := r26t8a_o02_pole_nonneg (X j) (X k)
    have jj : jbracket (X i) ^ M' * jbracket (X j) ^ M' * jbracket (X k) ^ M' ≤ (1 + ‖X‖) ^ (3 * M') := by
      calc jbracket (X i) ^ M' * jbracket (X j) ^ M' * jbracket (X k) ^ M'
          ≤ (1 + ‖X‖) ^ M' * (1 + ‖X‖) ^ M' * (1 + ‖X‖) ^ M' := by
            refine mul_le_mul (mul_le_mul (r26t8a_o02_jb_le hM' X i) (r26t8a_o02_jb_le hM' X j)
              (Real.rpow_nonneg (Real.sqrt_nonneg _) _) (Real.rpow_nonneg (by linarith [norm_nonneg X]) _))
              (r26t8a_o02_jb_le hM' X k) (Real.rpow_nonneg (Real.sqrt_nonneg _) _) (by positivity)
        _ = (1 + ‖X‖) ^ (3 * M') := by
            rw [← Real.rpow_add (by linarith [norm_nonneg X]), ← Real.rpow_add (by linarith [norm_nonneg X])]; ring_nf
    have tp : triplePole (X i) (X j) (X k) ≤ R X i j * R X i k + R X i j * R X j k + R X i k * R X j k := by
      unfold triplePole
      have := mul_le_mul a1 a2 b2 (hRn i j)
      have := mul_le_mul a1 a3 b3 (hRn i j)
      have := mul_le_mul a2 a3 b3 (hRn i k)
      simp only [hR]
      linarith
    have jj0 : 0 ≤ jbracket (X i) ^ M' * jbracket (X j) ^ M' * jbracket (X k) ^ M' :=
      mul_nonneg (mul_nonneg (Real.rpow_nonneg (s83_jb_pos _).le _) (Real.rpow_nonneg (s83_jb_pos _).le _))
        (Real.rpow_nonneg (s83_jb_pos _).le _)
    have tp0 : 0 ≤ triplePole (X i) (X j) (X k) := by
      unfold triplePole; positivity
    exact mul_le_mul jj tp tp0 hone
  exact u4Tame_add (u4Tame_add hWb hPj) hTr

end HRS.MS.R26T8A
