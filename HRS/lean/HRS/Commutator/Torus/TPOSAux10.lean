import HRS.Commutator.Torus.TPOSAux9

/-!
# T-POS helpers, part 10: near-diagonal lower bound of `f_η^𝕋` (`tr_f_lower_near`)
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ} {s η : ℝ}

lemma tpos_fTrunc1_lower (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ z : Euc d, z ≠ 0 → ‖z‖ ≤ 2 * Real.sqrt d → c ≤ Whole.fTrunc s 1 z := by
  obtain ⟨c, C, hc, hC, h⟩ := Whole.fcomparison (d := d) (s := s) hd hs0 hsd
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hsq : 0 < 2 * Real.sqrt d := by positivity
  refine ⟨min c (c * (2 * Real.sqrt d) ^ (-(2 * (d : ℝ) + 4))), lt_min hc (by positivity),
    fun z hz hzd => ?_⟩
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz
  obtain ⟨h1, h2, h3⟩ := h z hz
  by_cases hz1 : ‖z‖ ≤ 1
  · by_cases hs : s = 0
    · have h2' := (h2 hs hz1).1
      have : 1 ≤ 1 + |Real.log ‖z‖| := by linarith [abs_nonneg (Real.log ‖z‖)]
      calc min c (c * (2 * Real.sqrt d) ^ (-(2 * (d : ℝ) + 4))) ≤ c := min_le_left _ _
        _ = c * 1 := (mul_one _).symm
        _ ≤ c * (1 + |Real.log ‖z‖|) := by gcongr
        _ ≤ _ := h2'
    · have hs' : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
      have h1' := (h1 hs' hz1).1
      have : 1 ≤ ‖z‖ ^ (-s) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hzn hz1 (by linarith)
      calc min c (c * (2 * Real.sqrt d) ^ (-(2 * (d : ℝ) + 4))) ≤ c := min_le_left _ _
        _ = c * 1 := (mul_one _).symm
        _ ≤ c * ‖z‖ ^ (-s) := by gcongr
        _ ≤ _ := h1'
  · have hz1' : 1 ≤ ‖z‖ := le_of_lt (not_le.1 hz1)
    have h3' := (h3 hz1').1
    have : (2 * Real.sqrt d) ^ (-(2 * (d : ℝ) + 4)) ≤ ‖z‖ ^ (-(2 * (d : ℝ) + 4)) :=
      Real.rpow_le_rpow_of_nonpos hzn hzd (by linarith)
    calc min c (c * (2 * Real.sqrt d) ^ (-(2 * (d : ℝ) + 4)))
        ≤ c * (2 * Real.sqrt d) ^ (-(2 * (d : ℝ) + 4)) := min_le_right _ _
      _ ≤ c * ‖z‖ ^ (-(2 * (d : ℝ) + 4)) := by gcongr
      _ ≤ _ := h3'

lemma tpos_centeredRep_eq (z : Torus d) :
    ∃ m : Lattice d, KernelGrad.centeredRep z = Torus.rep z + Lattice.toEuc m := by
  refine ⟨fun i => if (Torus.rep z) i ≤ 1 / 2 then 0 else -1, ?_⟩
  ext i
  rw [KernelGrad.centeredRep_apply, tpos_add_apply, tpos_toEuc_apply]
  split_ifs with h <;> simp <;> ring

lemma tpos_perio_ge (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (hη : 0 < η) (x : Torus d) :
    Whole.fTrunc s η (KernelGrad.centeredRep x) ≤ perio (Whole.fTrunc s η : Euc d → ℝ) x := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  obtain ⟨m, hm⟩ := tpos_centeredRep_eq x
  have hsum := tpos_fTrunc_summable hs0 hsd hη (Torus.rep x)
  unfold perio
  rw [hm]
  exact hsum.le_tsum m (fun j _ => tpos_fTrunc_nonneg hs0 (by linarith) η _)

theorem tpos_f_lower_near (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ η₀ c : ℝ, 0 < η₀ ∧ η₀ ≤ 1 ∧ 0 < c ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ → ∀ x : Torus d, x ≠ 0 →
      KernelGrad.tdist x 0 ≤ 2 * η * Real.sqrt d → c * η ^ (-s) ≤ fTorus s η x := by
  have hd0 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hts := tpos_tScale_pos hs0
  obtain ⟨c₁, hc₁, hlow⟩ := tpos_fTrunc1_lower hd hs0 hsd
  set K : ℝ := Whole.cPhi d s * (∫ x : Euc d, Whole.phi x) / ((d : ℝ) - s) with hK
  have hs2 : s < 2 * (d : ℝ) + 4 := by linarith
  have hcp := Whole.cPhi_pos d hs0 hs2
  have hphi : 0 ≤ ∫ x : Euc d, Whole.phi x :=
    integral_nonneg fun x => (Whole.phiR_pos (d := d) _).le
  have hK0 : 0 ≤ K := by
    rw [hK]; have : 0 < (d : ℝ) - s := by linarith
    positivity
  set η₀ : ℝ := min 1 ((c₁ / (2 * (K + 1))) ^ ((d : ℕ) : ℝ)⁻¹) with hη₀
  have hbase : 0 < c₁ / (2 * (K + 1)) := by positivity
  have hη₀pos : 0 < η₀ := lt_min one_pos (Real.rpow_pos_of_pos hbase _)
  have hpow : η₀ ^ d ≤ c₁ / (2 * (K + 1)) := by
    calc η₀ ^ d ≤ ((c₁ / (2 * (K + 1))) ^ ((d : ℕ) : ℝ)⁻¹) ^ d :=
          pow_le_pow_left₀ hη₀pos.le (min_le_right _ _) d
      _ = _ := Real.rpow_inv_natCast_pow hbase.le (by omega)
  refine ⟨η₀, tScale s * (c₁ / 2), hη₀pos, min_le_left _ _, by positivity, fun η hη hηη₀ x hx hxd => ?_⟩
  have hsq : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
  set cr := KernelGrad.centeredRep x with hcr
  have hcr0 : cr ≠ 0 := by
    intro h
    apply hx
    rw [← KernelGrad.mk_centeredRep x, ← hcr, h]
    funext i; simp [Torus.mk]
  have hnorm : ‖cr‖ ≤ 2 * η * Real.sqrt d := by
    rw [← KernelGrad.tdist_zero_right]; exact hxd
  have hn' : ‖η⁻¹ • cr‖ ≤ 2 * Real.sqrt d := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hη, inv_mul_le_iff₀ hη]
    linarith
  have hne : η⁻¹ • cr ≠ 0 := smul_ne_zero (inv_ne_zero hη.ne') hcr0
  have h1 : c₁ ≤ Whole.fTrunc s 1 (η⁻¹ • cr) := hlow _ hne hn'
  have h2 : η ^ (-s) * c₁ ≤ Whole.fTrunc s η cr := by
    rw [tpos_fTrunc_scale hη cr]
    exact mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hη.le _)
  have h3 := tpos_perio_ge hs0 hsd hη x
  have hmean := tpos_integral_perio_fTrunc hs0 hsd hη (d := d)
  have hηd : η ^ d ≤ η₀ ^ d := pow_le_pow_left₀ hη.le hηη₀ d
  have hsplit : η ^ ((d : ℝ) - s) = η ^ (-s) * η ^ d := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hη]; congr 1; ring
  unfold fTorus
  rw [hmean, ← hK, hsplit]
  have hηs : 0 < η ^ (-s) := Real.rpow_pos_of_pos hη _
  have hKη : K * η ^ d ≤ c₁ / 2 := by
    calc K * η ^ d ≤ K * η₀ ^ d := mul_le_mul_of_nonneg_left hηd hK0
      _ ≤ K * (c₁ / (2 * (K + 1))) := mul_le_mul_of_nonneg_left hpow hK0
      _ ≤ c₁ / 2 := by
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
  have : η ^ (-s) * (c₁ / 2) ≤ perio (Whole.fTrunc s η : Euc d → ℝ) x - K * (η ^ (-s) * η ^ d) := by
    nlinarith [mul_le_mul_of_nonneg_left hKη hηs.le]
  calc tScale s * (c₁ / 2) * η ^ (-s) = tScale s * (η ^ (-s) * (c₁ / 2)) := by ring
    _ ≤ tScale s * _ := mul_le_mul_of_nonneg_left this hts.le

end HRS.Commutator.TorusNote
