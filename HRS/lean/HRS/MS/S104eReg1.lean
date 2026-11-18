import HRS.MS.S105rReg2

/-!
# S10.4 (nonlinear), packet S104E-1: `IsRegularMFRd` of the resulting solutions at ANY order `n ≤ 100d + 1000`

`s104e_gauss_reg`, `s104e_leibniz`: the order-`n` versions of `s105r_gauss_reg`, `s105r_leibniz` (S105R, order 3).
`s104e_reg_main`: for `2 ≤ d`, `0 ≤ s < d`, `a, β > 0` and every resulting solution of any thermal equilibrium, the first clause of
`IsRegularMFRd s n Λ T0 ρ` (`MemCb n`, `⟨x⟩^{d+3}`-weighted bound, `C_b^n` norm) with `Λ` independent of `T0`; `s104e_regMF` adds the singular force clause
from `s105r_reg` (order 3), giving `IsRegularMFRd s n Λ T0 ρ`.
Needed for `CoeffHypRd s m Λ T ρ` at `m + 3 = n` (S.A.12 data, uniqueness `Fcau.propagatorW_eq`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S104e

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.S104b HRS.MS.Mov63 HRS.MS.S105r

variable {d : ℕ}

/-- Gaussian weighted derivative bounds up to order `n` give `MemCb n`, the weighted sup norm and the `C_b^n` norm. -/
theorem s104e_gauss_reg {c : ℝ} (hc : 0 < c) (n : ℕ) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ (f : Euc d → ℝ) (K : ℝ), 0 ≤ K → ContDiff ℝ (n : WithTop ℕ∞) f →
      (∀ k ≤ n, ∀ x : Euc d, ‖iteratedFDeriv ℝ k f x‖ ≤ K * Real.exp (-c * ‖x‖ ^ 2)) →
      HRS.MemCb n f ∧ weightedSupE n ((d : ℝ) + 3) f ≤ ENNReal.ofReal (P * K) ∧
        HRS.cbNorm n f ≤ ((n : ℝ) + 1) * K := by
  obtain ⟨P, hP0, hP⟩ := HRS.MS.Thm.rege_poly_gauss_bdd hc (d + 3)
  have hexp : ∀ x : Euc d, Real.exp (-c * ‖x‖ ^ 2) ≤ 1 := fun x => by
    rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg ‖x‖]
  refine ⟨P, hP0.le, fun f K hK hf hb => ⟨⟨hf, fun j hj => ⟨K, ?_⟩⟩, ?_, ?_⟩⟩
  · rintro _ ⟨x, rfl⟩
    refine (hb j hj x).trans ?_
    have := hexp x
    nlinarith
  · unfold weightedSupE derivSupE
    refine iSup_le fun j => iSup_le fun I => iSup_le fun x => ENNReal.ofReal_le_ofReal ?_
    have hj : (j : ℕ) ≤ n := Nat.lt_succ_iff.mp j.2
    have h1 : jbracket x ^ ((d : ℝ) + 3) ≤ (1 + ‖x‖) ^ (d + 3) := by
      have : ((d : ℝ) + 3) = ((d + 3 : ℕ) : ℝ) := by push_cast; ring
      rw [this, Real.rpow_natCast]
      exact pow_le_pow_left₀ (u2_jb_pos x).le (u2_jb_le x) _
    have h2 : |partialDeriv I f x| ≤ K * Real.exp (-c * ‖x‖ ^ 2) :=
      (HRS.MS.Lc.lc4_partial_le (j : ℕ) I x).trans (hb j hj x)
    have h3 := hP ‖x‖ (norm_nonneg _)
    calc jbracket x ^ ((d : ℝ) + 3) * |partialDeriv I f x|
        ≤ (1 + ‖x‖) ^ (d + 3) * (K * Real.exp (-c * ‖x‖ ^ 2)) :=
          mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ = K * ((1 + ‖x‖) ^ (d + 3) * Real.exp (-c * ‖x‖ ^ 2)) := by ring
      _ ≤ K * P := mul_le_mul_of_nonneg_left h3 hK
      _ = P * K := mul_comm _ _
  · unfold HRS.cbNorm
    calc ∑ j ∈ Finset.range (n + 1), ⨆ z : Euc d, ‖iteratedFDeriv ℝ j f z‖
        ≤ ∑ _j ∈ Finset.range (n + 1), K := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          refine ciSup_le fun z => (hb j hjn z).trans ?_
          have := hexp z
          nlinarith
      _ = ((n : ℝ) + 1) * K := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; ring

/-- The Gaussian bounds for `ρ^t = ρ_β + √ρ_β v_t` up to order `n`, uniformly in `v` with uniformly bounded derivatives. -/
theorem s104e_leibniz {ρβ : Euc d → ℝ} {q' : ℝ} {B : Euc d → Euc d} (hq : 0 < q')
    (hR : HRS.MS.Gap.GapRef d ρβ q' B) (n : ℕ) (Cv E : ℝ) (hCv : 0 ≤ Cv) (hE : 0 ≤ E) :
    ∃ c K : ℝ, 0 < c ∧ 0 ≤ K ∧ ∀ v : Euc d → ℝ, ContDiff ℝ (n : WithTop ℕ∞) v →
      (∀ k ≤ n, ∀ x : Euc d, ‖iteratedFDeriv ℝ k v x‖ ≤ Cv * E) →
      ContDiff ℝ (n : WithTop ℕ∞) (fun x => ρβ x + Real.sqrt (ρβ x) * v x) ∧
      ∀ k ≤ n, ∀ x : Euc d, ‖iteratedFDeriv ℝ k (fun x => ρβ x + Real.sqrt (ρβ x) * v x) x‖ ≤
        K * Real.exp (-c * ‖x‖ ^ 2) := by
  obtain ⟨hρs, cρ, hcρ, hρb⟩ := HRS.MS.Mov0.mv0_hgauss_gapref hq hR
  obtain ⟨hss, -, cs, hcs, hsb⟩ := HRS.MS.Mov0.mv0_sqrt_gauss hq hR
  choose Cρ hCρ using hρb
  choose Cs hCs using hsb
  set c0 : ℝ := min cρ cs with hc0
  have hc0pos : 0 < c0 := lt_min hcρ hcs
  set Pρ : ℝ := ∑ k ∈ Finset.range (n + 1), |Cρ k| with hPρ
  set Ps : ℝ := ∑ k ∈ Finset.range (n + 1), |Cs k| with hPs
  have hPρ0 : 0 ≤ Pρ := Finset.sum_nonneg fun k _ => abs_nonneg _
  have hPs0 : 0 ≤ Ps := Finset.sum_nonneg fun k _ => abs_nonneg _
  have hexp1 : ∀ (r : ℝ), Real.exp (-cρ * r ^ 2) ≤ Real.exp (-c0 * r ^ 2) := fun r => by
    apply Real.exp_le_exp.2
    have : c0 ≤ cρ := min_le_left _ _
    nlinarith [sq_nonneg r]
  have hexp2 : ∀ (r : ℝ), Real.exp (-cs * r ^ 2) ≤ Real.exp (-c0 * r ^ 2) := fun r => by
    apply Real.exp_le_exp.2
    have : c0 ≤ cs := min_le_right _ _
    nlinarith [sq_nonneg r]
  have hρk : ∀ k ≤ n, ∀ x : Euc d, ‖iteratedFDeriv ℝ k ρβ x‖ ≤ Pρ * Real.exp (-c0 * ‖x‖ ^ 2) := by
    intro k hk x
    have h1 := hCρ k x
    have h2 : Cρ k ≤ Pρ := by
      calc Cρ k ≤ |Cρ k| := le_abs_self _
        _ ≤ Pρ := Finset.single_le_sum (f := fun k => |Cρ k|) (fun k _ => abs_nonneg _)
            (Finset.mem_range.2 (by omega))
    refine h1.trans ?_
    have h3 := hexp1 ‖x‖
    have h4 : 0 ≤ Real.exp (-c0 * ‖x‖ ^ 2) := (Real.exp_pos _).le
    have h5 : 0 ≤ Real.exp (-cρ * ‖x‖ ^ 2) := (Real.exp_pos _).le
    nlinarith [mul_le_mul h2 h3 h5 hPρ0]
  have hsk : ∀ k ≤ n, ∀ x : Euc d, ‖iteratedFDeriv ℝ k (fun y => Real.sqrt (ρβ y)) x‖ ≤
      Ps * Real.exp (-c0 * ‖x‖ ^ 2) := by
    intro k hk x
    have h1 := hCs k x
    have h2 : Cs k ≤ Ps := by
      calc Cs k ≤ |Cs k| := le_abs_self _
        _ ≤ Ps := Finset.single_le_sum (f := fun k => |Cs k|) (fun k _ => abs_nonneg _)
            (Finset.mem_range.2 (by omega))
    refine h1.trans ?_
    have h3 := hexp2 ‖x‖
    have h5 : 0 ≤ Real.exp (-cs * ‖x‖ ^ 2) := (Real.exp_pos _).le
    nlinarith [mul_le_mul h2 h3 h5 hPs0]
  refine ⟨c0, Pρ + 2 ^ n * (Ps * (Cv * E)), hc0pos, by positivity, fun v hv hvb => ?_⟩
  have hρn : ContDiff ℝ (n : WithTop ℕ∞) ρβ := hρs.of_le (by simp)
  have hsn : ContDiff ℝ (n : WithTop ℕ∞) (fun y => Real.sqrt (ρβ y)) := hss.of_le (by simp)
  have hprod : ContDiff ℝ (n : WithTop ℕ∞) (fun x => Real.sqrt (ρβ x) * v x) := hsn.mul hv
  refine ⟨hρn.add hprod, fun k hk x => ?_⟩
  have hkc : (k : WithTop ℕ∞) ≤ (n : WithTop ℕ∞) := by exact_mod_cast hk
  have hsum : iteratedFDeriv ℝ k (fun x => ρβ x + Real.sqrt (ρβ x) * v x) x =
      iteratedFDeriv ℝ k ρβ x + iteratedFDeriv ℝ k (fun x => Real.sqrt (ρβ x) * v x) x :=
    iteratedFDeriv_add_apply ((hρn.of_le hkc).contDiffAt) ((hprod.of_le hkc).contDiffAt)
  have hL := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) hsn hv x (n := k) (by exact_mod_cast hk)
  have hex0 : 0 ≤ Real.exp (-c0 * ‖x‖ ^ 2) := (Real.exp_pos _).le
  have hterm : ∀ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y => Real.sqrt (ρβ y)) x‖ *
      ‖iteratedFDeriv ℝ (k - i) v x‖ ≤ (k.choose i : ℝ) * (Ps * Real.exp (-c0 * ‖x‖ ^ 2) * (Cv * E)) := by
    intro i hi
    have hik : i ≤ n := by have := Finset.mem_range.1 hi; omega
    have a1 := hsk i hik x
    have a2 := hvb (k - i) (by omega) x
    have : ‖iteratedFDeriv ℝ i (fun y => Real.sqrt (ρβ y)) x‖ * ‖iteratedFDeriv ℝ (k - i) v x‖ ≤
        Ps * Real.exp (-c0 * ‖x‖ ^ 2) * (Cv * E) :=
      mul_le_mul a1 a2 (norm_nonneg _) (by positivity)
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg _)
  have hsumle : ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y => Real.sqrt (ρβ y)) x‖ *
      ‖iteratedFDeriv ℝ (k - i) v x‖ ≤ 2 ^ n * (Ps * (Cv * E)) * Real.exp (-c0 * ‖x‖ ^ 2) := by
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.sum_mul]
    have hch : ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) = 2 ^ k := by
      exact_mod_cast Nat.sum_range_choose k
    have h2k : (2 : ℝ) ^ k ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) hk
    have h8 : 0 ≤ Ps * Real.exp (-c0 * ‖x‖ ^ 2) * (Cv * E) := by positivity
    rw [hch]
    calc (2 : ℝ) ^ k * (Ps * Real.exp (-c0 * ‖x‖ ^ 2) * (Cv * E))
        ≤ 2 ^ n * (Ps * Real.exp (-c0 * ‖x‖ ^ 2) * (Cv * E)) := mul_le_mul_of_nonneg_right h2k h8
      _ = 2 ^ n * (Ps * (Cv * E)) * Real.exp (-c0 * ‖x‖ ^ 2) := by ring
  rw [hsum]
  refine (norm_add_le _ _).trans ?_
  have := hρk k hk x
  nlinarith

end HRS.MS.S104e
