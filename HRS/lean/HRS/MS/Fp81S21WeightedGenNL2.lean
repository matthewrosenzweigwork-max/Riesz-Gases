import HRS.MS.Fp81S21WeightedGenNL
import HRS.MS.WhoAux5
import HRS.MS.WhoAux12
import HRS.MS.Fp81S21WeightedGen4

/-! Compact tests yield the decay needed to differentiate the nonlocal term. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory
open scoped ENNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.Ul HRS.MS.Who

/-- Finite-order compactly supported smooth functions have bounded jets. -/
theorem fp81s21_b3_compact_cb {d n : ℕ} {f : Euc d → ℝ}
    (hf : ContDiff ℝ n f) (hfc : HasCompactSupport f) : CbCls n f := by
  have key : ∀ i ≤ n, ∃ C : ℝ, ∀ y, ‖iteratedFDeriv ℝ i f y‖ ≤ C := by
    intro i hi
    exact (hf.continuous_iteratedFDeriv (by exact_mod_cast hi)).bounded_above_of_compact_support
      (hfc.iteratedFDeriv i)
  choose C hC using fun i : Fin (n + 1) => key i (by omega)
  refine ⟨hf, ∑ i, max 0 (C i), ?_⟩
  intro i hi y
  let j : Fin (n + 1) := ⟨i, by omega⟩
  calc ‖iteratedFDeriv ℝ i f y‖ ≤ C j := hC j y
    _ ≤ max 0 (C j) := le_max_right _ _
    _ ≤ ∑ i, max 0 (C i) := Finset.single_le_sum (fun _ _ => le_max_left _ _) (Finset.mem_univ j)

/-- Every source has a common polynomial-decay bound through order q+1.
The constant here may depend on the test; it is used only for differentiating. -/
theorem fp81s21_b3_compact_source_decay (p : Parameters) {δ : ℝ}
    (R : Trajectory p δ) (B c : ℝ) (hB : 0 ≤ B) (hc : 0 < c)
    (hdata : fp81s21_b3_Data R B c) (u : ℝ) (hu : 0 ≤ u)
    (f : Euc p.d → ℝ) (hf : ContDiff ℝ (fp81s21_b3_q p + 2) f)
    (hfc : HasCompactSupport f) (N : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ j : Fin p.d,
      U2Dec (fp81s21_b3_q p + 1) (N : ℝ) A (fp81s21_b3_source R u f j) := by
  let q := fp81s21_b3_q p
  obtain ⟨C, hC, hgauss⟩ := HRS.MS.S104e.s104e_u2dec_of_gauss hc (q + 1) N
  obtain ⟨_, _, hρc, hρb⟩ := hdata u hu
  have hρ : U2Dec (q + 1) (N : ℝ) (C * B) (R.ρ u) :=
    hgauss (R.ρ u) B hB (hρc.of_le (by dsimp [q]; exact_mod_cast (by omega : fp81s21_b3_q p + 1 ≤ fp81s21_b3_q p + 2)))
      (fun i hi => hρb i (by dsimp [q] at hi; omega))
  have hfcbs : CbCls (q + 2) f := fp81s21_b3_compact_cb hf hfc
  obtain ⟨_, D, hD⟩ := hfcbs
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD 0 (by omega) 0)
  let M := (r26t3_coeff R).M
  let W : ℝ := ∑ j : Fin p.d, ‖ul1w M j‖
  have hW : 0 ≤ W := Finset.sum_nonneg fun _ _ => norm_nonneg _
  let A := C * B * (D * W) * 2 ^ (q + 1)
  refine ⟨A, by dsimp [A]; positivity, ?_⟩
  intro j
  have hφ := who_dir_cb (n := q + 1) (⟨hf, ⟨D, hD⟩⟩ : CbCls (q + 2) f) (ul1w M j)
  obtain ⟨hφc, E, hE⟩ := hφ
  have hφb : ∀ i ≤ q + 1, ∀ y,
      ‖iteratedFDeriv ℝ i (fun y => fderiv ℝ f y (ul1w M j)) y‖ ≤ D * W := by
    intro i hi y
    have hnorm := norm_iteratedFDeriv_clm_apply_const (N := ((q + 1 : ℕ) : WithTop ℕ∞))
      (c := ul1w M j) (x := y) (n := i) (hf.fderiv_right (by exact_mod_cast (by omega : q + 2 ≤ q + 2))).contDiffAt
      (by exact_mod_cast hi)
    rw [norm_iteratedFDeriv_fderiv] at hnorm
    have hwj : ‖ul1w M j‖ ≤ W := Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
    calc _ ≤ ‖ul1w M j‖ * ‖iteratedFDeriv ℝ (i + 1) f y‖ := hnorm
      _ ≤ W * D := mul_le_mul hwj (hD (i + 1) (by omega) y) (norm_nonneg _) hW
      _ = D * W := by ring
  have hprod := who_u2dec_mul hρ hφc hφb
  have heq : fp81s21_b3_source R u f j = fun y => R.ρ u y * fderiv ℝ f y (ul1w M j) := by
    funext y
    simp only [fp81s21_b3_source, ul1_matVec, M]
  rw [heq]
  exact hprod

/-- Directional differentiation costs one input derivative in the weighted norm. -/
theorem fp81s21_b3_dir_Nsq {d r : ℕ} {P : ℝ} {f : Euc d → ℝ}
    (hf : ContDiff ℝ (r + 1) f) (v : Euc d) :
    Nsq r P (fun y => fderiv ℝ f y v) ≤
      ENNReal.ofReal (‖v‖ ^ 2) * Nsq (r + 1) P f := by
  have hshift : (∑ i ∈ Finset.range (r + 1),
      wSq P (fun y => ‖iteratedFDeriv ℝ (i + 1) f y‖)) ≤ Nsq (r + 1) P f := by
    unfold Nsq
    conv_rhs => rw [Finset.sum_range_succ']
    exact le_add_of_nonneg_right (show (0 : ℝ≥0∞) ≤ _ from bot_le)
  calc Nsq r P (fun y => fderiv ℝ f y v)
      ≤ ENNReal.ofReal (‖v‖ ^ 2) * (∑ i ∈ Finset.range (r + 1),
        wSq P (fun y => ‖iteratedFDeriv ℝ (i + 1) f y‖)) := by
        unfold Nsq
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun i hi => ?_
        have hir : i ≤ r := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        have hpt : ∀ y, ‖iteratedFDeriv ℝ i (fun z => fderiv ℝ f z v) y‖ ^ 2 ≤
            (‖v‖ * ‖iteratedFDeriv ℝ (i + 1) f y‖) ^ 2 := fun y =>
          pow_le_pow_left₀ (norm_nonneg _) (who_dir_norm (hf.of_le (by exact_mod_cast (by omega : i + 1 ≤ r + 1))) v y) 2
        calc wSq P (fun y => ‖iteratedFDeriv ℝ i (fun z => fderiv ℝ f z v) y‖)
            ≤ wSq P (fun y => ‖v‖ * ‖iteratedFDeriv ℝ (i + 1) f y‖) := who_wSq_mono hpt
          _ = ENNReal.ofReal (‖v‖ ^ 2) * wSq P (fun y => ‖iteratedFDeriv ℝ (i + 1) f y‖) := who_wSq_smul P _ _
    _ ≤ ENNReal.ofReal (‖v‖ ^ 2) * Nsq (r + 1) P f := mul_le_mul' le_rfl hshift

/-- Weighted convolution of a decaying coefficient and a directional derivative. -/
theorem fp81s21_b3_Kprod_dir {d : ℕ} (hd : 1 ≤ d) {P : ℝ}
    (hP : 0 ≤ P) (hPd : (d : ℝ) / 2 < P) {κ : Euc d → ℝ} {s : ℝ}
    (hK : UlKer κ s) (hs1 : s + 1 < d) (r : ℕ) {L : ℝ}
    (hLP : (d : ℝ) / 2 < L - P) (hLd : (d : ℝ) < L)
    {A : ℝ} (hA : 0 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ρ f : Euc d → ℝ}, U2Dec (r + 1) L A ρ →
      CbCls (r + 2) f → ∀ (v : Euc d) {i : ℕ}, i ≤ r →
        wSq P (fun x => ‖iteratedFDeriv ℝ i
          (ultK κ (fun y => ρ y * fderiv ℝ f y v)) x‖) ≤
          ENNReal.ofReal C * ENNReal.ofReal (‖v‖ ^ 2) * Nsq (r + 1) P f := by
  obtain ⟨C, hC, hcost⟩ := who_Kprod hd hP hPd hK hs1 r hLP hLd hA
  refine ⟨C, hC, ?_⟩
  intro ρ f hρ hf v i hi
  have hdir : CbCls (r + 1) (fun y => fderiv ℝ f y v) := who_dir_cb hf v
  calc
    _ ≤ ENNReal.ofReal C * Nsq r P (fun y => fderiv ℝ f y v) := hcost hρ hdir hi
    _ ≤ ENNReal.ofReal C * (ENNReal.ofReal (‖v‖ ^ 2) * Nsq (r + 1) P f) :=
      mul_le_mul' le_rfl (fp81s21_b3_dir_Nsq (hf.1.of_le (by exact_mod_cast (by omega : r + 1 ≤ r + 2))) v)
    _ = _ := by ring

/-- Component constants are fixed before the trajectory, time, and test. -/
theorem fp81s21_b3_component_bound (p : Parameters) (B c : ℝ)
    (hB : 0 ≤ B) (hc : 0 < c) :
    ∃ C : Fin p.d → ℝ, (∀ j, 0 ≤ C j) ∧
      ∀ {δ : ℝ} (R : Trajectory p δ), fp81s21_b3_Data R B c →
        ∀ u, 0 ≤ u → ∀ f : Euc p.d → ℝ, CbCls (fp81s21_b3_q p + 2) f →
          ∀ (j : Fin p.d) {i : ℕ}, i ≤ fp81s21_b3_q p →
            wSq (fp81s21_b3_P p) (fun x => ‖iteratedFDeriv ℝ i
              (ultK (u2_kap p.d p.s j) (fp81s21_b3_source R u f j)) x‖) ≤
              ENNReal.ofReal (C j) * Nsq (fp81s21_b3_q p + 1) (fp81s21_b3_P p) f := by
  let q := fp81s21_b3_q p
  let P := fp81s21_b3_P p
  let n : ℕ := 2 * p.d + 4
  have hd : 1 ≤ p.d := le_trans (by decide) p.hd
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  have hP : 0 ≤ P := by dsimp [P, fp81s21_b3_P]; positivity
  have hPd : (p.d : ℝ) / 2 < P := by
    dsimp [P, fp81s21_b3_P]; have := Nat.cast_nonneg (α := ℝ) p.d; linarith
  have hLP : (p.d : ℝ) / 2 < (n : ℝ) - P := by
    dsimp [n, P, fp81s21_b3_P]; push_cast
    have := Nat.cast_nonneg (α := ℝ) p.d; linarith
  have hLd : (p.d : ℝ) < (n : ℝ) := by
    dsimp [n]; push_cast; have := Nat.cast_nonneg (α := ℝ) p.d; linarith
  obtain ⟨D, hD, hgauss⟩ := HRS.MS.S104e.s104e_u2dec_of_gauss hc (q + 1) n
  choose C hC hcost using fun j : Fin p.d => fp81s21_b3_Kprod_dir hd hP hPd
    (ult_ker_kap p.hs0 hsd j) (fp81s21_g4_kernel_exponent p) q hLP hLd
    (mul_nonneg hD hB)
  let v : Fin p.d → Euc p.d := fun j => ul1w (-1 : Matrix (Fin p.d) (Fin p.d) ℝ) j
  refine ⟨fun j => C j * ‖v j‖ ^ 2, fun j => mul_nonneg (hC j) (sq_nonneg _), ?_⟩
  intro δ R hdata u hu f hf j i hi
  obtain ⟨_, _, hρc, hρb⟩ := hdata u hu
  have hρ : U2Dec (q + 1) (n : ℝ) (D * B) (R.ρ u) :=
    hgauss (R.ρ u) B hB (hρc.of_le (by dsimp [q]; exact_mod_cast (by omega : fp81s21_b3_q p + 1 ≤ fp81s21_b3_q p + 2)))
      (fun k hk => hρb k (by dsimp [q] at hk; omega))
  have heq : fp81s21_b3_source R u f j = fun y => R.ρ u y * fderiv ℝ f y (v j) := by
    funext y
    rw [fp81s21_b3_source, ul1_matVec]
    rfl
  rw [heq]
  calc
    _ ≤ ENNReal.ofReal (C j) * ENNReal.ofReal (‖v j‖ ^ 2) * Nsq (q + 1) P f :=
      hcost j hρ hf (v j) hi
    _ = ENNReal.ofReal (C j * ‖v j‖ ^ 2) * Nsq (q + 1) P f := by
      rw [ENNReal.ofReal_mul (hC j)]

/-- Sum the uniform component estimates over derivatives and coordinates. -/
theorem fp81s21_b3_nonlocal_Nsq (p : Parameters) (B c : ℝ)
    (hB : 0 ≤ B) (hc : 0 < c) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {δ : ℝ} (R : Trajectory p δ), fp81s21_b3_Data R B c →
        ∀ u, 0 ≤ u → ∀ f : Euc p.d → ℝ,
          ContDiff ℝ (fp81s21_b3_q p + 2) f → HasCompactSupport f →
          ContDiff ℝ (fp81s21_b3_q p) (fp81s21_g4N p R u f) ∧
          Nsq (fp81s21_b3_q p) (fp81s21_b3_P p) (fp81s21_g4N p R u f) ≤
            ENNReal.ofReal K * Nsq (fp81s21_b3_q p + 1) (fp81s21_b3_P p) f := by
  let q := fp81s21_b3_q p
  let P := fp81s21_b3_P p
  let n : ℕ := 2 * p.d + 4
  have hd : 1 ≤ p.d := le_trans (by decide) p.hd
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  have hLd : (p.d : ℝ) < (n : ℝ) := by
    dsimp [n]; push_cast; have := Nat.cast_nonneg (α := ℝ) p.d; linarith
  obtain ⟨C, hC, hcost⟩ := fp81s21_b3_component_bound p B c hB hc
  let K : ℝ := (q + 1 : ℕ) * (p.d : ℝ) * ∑ j, C j
  have hK : 0 ≤ K := by
    dsimp [K]; exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun j _ => hC j)
  refine ⟨K, hK, ?_⟩
  intro δ R hdata u hu f hf hfc
  have hcb := fp81s21_b3_compact_cb hf hfc
  obtain ⟨A, hA, hdec⟩ := fp81s21_b3_compact_source_decay p R B c hB hc hdata u hu f hf hfc n
  let F : Fin p.d → Euc p.d → ℝ := fun j =>
    ultK (u2_kap p.d p.s j) (fp81s21_b3_source R u f j)
  have hF : ∀ j, ContDiff ℝ q (F j) := fun j =>
    (ult_K_iter hd (ult_ker_kap p.hs0 hsd j) hLd hA (hdec j)).2
  have hN : fp81s21_g4N p R u f = fun x => ∑ j, F j x := by
    funext x
    unfold fp81s21_g4N
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (ult_conv_comp hd p.hs0 hsd hLd hA
      (ult_U2Dec_mono (hdec j) (by omega : 1 ≤ q + 1)) x).2 j
  have hcd : ContDiff ℝ q (fp81s21_g4N p R u f) := by
    rw [hN]; exact ContDiff.sum fun j _ => hF j
  refine ⟨hcd, ?_⟩
  have hper : ∀ i ≤ q,
      wSq P (fun x => ‖iteratedFDeriv ℝ i (fp81s21_g4N p R u f) x‖) ≤
        ENNReal.ofReal ((p.d : ℝ) * ∑ j, C j) * Nsq (q + 1) P f := by
    intro i hi
    have heq : ∀ x, iteratedFDeriv ℝ i (fp81s21_g4N p R u f) x =
        ∑ j, iteratedFDeriv ℝ i (F j) x := by
      intro x
      rw [hN, iteratedFDeriv_fun_sum_apply (fun j _ =>
        ((hF j).of_le (by exact_mod_cast hi)).contDiffAt)]
    have hm : ∀ j, Measurable (fun x => ‖iteratedFDeriv ℝ i (F j) x‖) :=
      fun j => who_iter_meas (hF j) hi
    calc
      _ ≤ wSq P (fun x => ∑ j, ‖iteratedFDeriv ℝ i (F j) x‖) := by
        apply who_wSq_mono
        intro x
        exact pow_le_pow_left₀ (norm_nonneg _) (by rw [heq]; exact norm_sum_le _ _) 2
      _ ≤ (p.d : ℝ≥0∞) * ∑ j, wSq P (fun x => ‖iteratedFDeriv ℝ i (F j) x‖) := by
        simpa using who_wSq_sum_le (Finset.univ : Finset (Fin p.d)) hm
      _ ≤ (p.d : ℝ≥0∞) * ∑ j, (ENNReal.ofReal (C j) * Nsq (q + 1) P f) := by
        gcongr
        exact hcost R hdata u hu f hcb _ hi
      _ = ENNReal.ofReal ((p.d : ℝ) * ∑ j, C j) * Nsq (q + 1) P f := by
        rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
          ENNReal.ofReal_sum_of_nonneg (fun j _ => hC j), ← Finset.sum_mul]
        ring
  unfold Nsq at ⊢
  calc
    _ ≤ ∑ i ∈ Finset.range (q + 1),
        ENNReal.ofReal ((p.d : ℝ) * ∑ j, C j) * Nsq (q + 1) P f := by
      exact Finset.sum_le_sum fun i hi => hper i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
    _ = ENNReal.ofReal K * Nsq (q + 1) P f := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        ← mul_assoc, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 2
      dsimp [K]
      ring

/-- The compact nonlocal map has a trajectory-uniform weighted Sobolev bound. -/
theorem fp81s21_b3_nonlocal_compact (p : Parameters) (B c : ℝ)
    (hB : 0 ≤ B) (hc : 0 < c) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {δ : ℝ} (R : Trajectory p δ),
      fp81s21_b3_Data R B c → ∀ u, 0 ≤ u → ∀ f : Euc p.d → ℝ,
        ContDiff ℝ (fp81s21_b3_q p + 2) f → HasCompactSupport f →
        IsR2WeightedTest (fp81s21_b3_q p) (fp81s21_b3_P p) (fp81s21_g4N p R u f) ∧
        weightedSobolevE (fp81s21_b3_q p) (fp81s21_b3_P p) (fp81s21_g4N p R u f) ≤
          ENNReal.ofReal A * weightedSobolevE (fp81s21_b3_q p + 2) (fp81s21_b3_P p) f := by
  let q := fp81s21_b3_q p
  let P := fp81s21_b3_P p
  have hd : 1 ≤ p.d := le_trans (by decide) p.hd
  have hPd : (p.d : ℝ) / 2 < P := by
    dsimp [P, fp81s21_b3_P]; have := Nat.cast_nonneg (α := ℝ) p.d; linarith
  obtain ⟨K, hK, hN⟩ := fp81s21_b3_nonlocal_Nsq p B c hB hc
  let A : ℝ := Real.sqrt (K * (p.d : ℝ) ^ (q + (q + 2)))
  have hA : 0 ≤ A := Real.sqrt_nonneg _
  refine ⟨A, hA, ?_⟩
  intro δ R hdata u hu f hf hfc
  obtain ⟨hcd, hb⟩ := hN R hdata u hu f hf hfc
  have hb' : Nsq q P (fp81s21_g4N p R u f) ≤
      ENNReal.ofReal K * Nsq (q + 2) P f :=
    hb.trans (mul_le_mul' le_rfl (who_Nsq_mono (by omega) P f))
  have hE := fp81s21_b3_Nsq_to_E hd hK hf hb'
  have hbound : weightedSobolevE q P (fp81s21_g4N p R u f) ≤
      ENNReal.ofReal A * weightedSobolevE (q + 2) P f := by
    simpa [A] using hE
  obtain ⟨_, D, hD⟩ := fp81s21_b3_compact_cb hf hfc
  have hfinN : Nsq (q + 2) P f < ⊤ := who_Nsq_lt_top hPd (fun j hj => ⟨D, hD j hj⟩)
  have hfinE : Esq (q + 2) P f < ⊤ := lt_of_le_of_lt (who_Esq_le hd)
    (ENNReal.mul_lt_top (ENNReal.pow_lt_top (ENNReal.natCast_lt_top p.d)) hfinN)
  have hfin : weightedSobolevE (q + 2) P f < ⊤ := by
    rw [who_E_eq]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hfinE.ne
  exact ⟨⟨hcd, lt_of_le_of_lt hbound (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin)⟩, hbound⟩

#print axioms HRS.Fp81.S21.fp81s21_b3_nonlocal_compact
#print axioms HRS.Fp81.S21.fp81s21_b3_nonlocal_Nsq
#print axioms HRS.Fp81.S21.fp81s21_b3_component_bound
#print axioms HRS.Fp81.S21.fp81s21_b3_Kprod_dir
#print axioms HRS.Fp81.S21.fp81s21_b3_dir_Nsq
#print axioms HRS.Fp81.S21.fp81s21_b3_compact_cb
#print axioms HRS.Fp81.S21.fp81s21_b3_compact_source_decay
end HRS.Fp81.S21
