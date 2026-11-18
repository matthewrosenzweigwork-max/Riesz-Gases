import HRS.MS.SA16ZE9

/-!
# S.A.16 (SA16Z) E10: the level-`j` energy estimate for the nonlocal operator `P_μ` (`1 < θ < 2`)

`sa16z_level`: for `μ ≥ 0` in `C_b^∞` with `‖D^kμ‖ ≤ Λ`, `k ≤ j+3`, and `φ ∈ C_c^∞`,
`∫ |D^jφ|^{p-2} ∑_idx ∂^idxφ ∂^idx(P_μ φ) ≤ C_j ∑_{k ≤ j} ∫ |D^kφ|^p`, `C_j = C_j(d,s,p,Λ)`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.BreakdownSA16

section E10
variable {d : ℕ} {s : ℝ}

set_option maxHeartbeats 1600000 in
theorem sa16z_level (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hθ1 : 1 < s + 2 - d) {p : ℝ} (hp : 2 ≤ p)
    (Λ : ℝ) (hΛ : 0 ≤ Λ) (j : ℕ) :
    ∃ Cj : ℝ, 0 ≤ Cj ∧ ∀ {μ φ : Euc d → ℝ}, HRS.S16Frac.S16FracCb μ → (∀ x, 0 ≤ μ x) → IsCcInfty φ →
      sa16z_Cb (j + 3) Λ μ →
      ∫ x, sa16sz_vn φ j x ^ (p - 2) * ∑ idx : Fin j → Fin d, partialDeriv idx φ x *
          partialDeriv idx (sa16z_P s μ φ) x ≤
        Cj * ∑ k ∈ Finset.range (j + 1), ∫ x, sa16sz_vn φ k x ^ p := by
  have hθ2 : s + 2 - (d : ℝ) < 2 := by linarith
  have hθ0 : 0 < s + 2 - (d : ℝ) := by linarith
  have hp0 : 0 < p := by linarith
  obtain ⟨c, hc, hP⟩ := sa16z_P_lap hd hs0 hsd hθ0
  obtain ⟨cθ, hErrb⟩ := sa16z_Err_bound hd hs0 hsd hθ1 hp c
  obtain ⟨K, hK0, hK⟩ := hErrb j
  obtain ⟨Cw, hCw0, hCw⟩ := sa16bd_weighted_leading hd (s + 2 - d) p hθ0 hθ2 hp (Fin j → Fin d)
  have hcc : 0 < sa16bd_convexityConst p := by unfold sa16bd_convexityConst; positivity
  set cs := HRS.CZ.Hls.hlsg_c s with hcs
  set cA := cs - c * cθ with hcA
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  set ε : ℝ := c * sa16bd_convexityConst p / d with hε
  have hε0 : 0 < ε := by positivity
  have hIB := fun l : Fin d => sa16z_IB_bound hd hs0 hsd hθ1 hp Λ hΛ hε0 cA cs l j
  choose CB hCB0 hCB using hIB
  set Bb2 : ℝ := 1 + ((|cA| + |cs| * j) * Real.sqrt (2 * Λ)) ^ 2 with hBb2
  have hBb2pos : 0 < Bb2 := by positivity
  set N : ℝ := (d : ℝ) ^ j with hN
  have hNpos : 0 < N := by positivity
  have hCBs : 0 ≤ ∑ l, CB l := Finset.sum_nonneg fun l _ => hCB0 l
  have hKΛ : 0 ≤ K * Λ := mul_nonneg hK0 hΛ
  refine ⟨c * Cw * (3 * Λ) + (∑ l, CB l) * Bb2 + N * ((p - 1) / p) +
    (1 / p) * N * ((K * Λ) ^ p * ((j : ℝ) + 1) ^ (p - 1)),
    by
      have h1 : 0 ≤ c * Cw * (3 * Λ) := by positivity
      have h2 : 0 ≤ (∑ l, CB l) * Bb2 := mul_nonneg hCBs hBb2pos.le
      have h3 : 0 ≤ N * ((p - 1) / p) := mul_nonneg hNpos.le (div_nonneg (by linarith) hp0.le)
      have h4 : 0 ≤ (1 / p) * N * ((K * Λ) ^ p * ((j : ℝ) + 1) ^ (p - 1)) :=
        mul_nonneg (mul_nonneg (by positivity) hNpos.le)
          (mul_nonneg (Real.rpow_nonneg hKΛ _) (Real.rpow_nonneg (by positivity) _))
      linarith,
    fun {μ φ} hμ hpos hφ hCb => ?_⟩
  have hμs : ContDiff ℝ ∞ μ := hμ.1
  have hCb2 : sa16z_Cb 2 Λ μ := sa16z_Cb_mono (by omega) hCb
  have hmem2 : HRS.MemCb 2 μ := sa16z_memCb hμs hCb2
  have hcb2 : HRS.cbNorm 2 μ ≤ 3 * Λ := by
    have := sa16z_cbNorm_le hCb2; push_cast at this; linarith
  set W := sa16z_Wt hφ j with hW
  obtain ⟨hVint, hAint, hDfin, hlead⟩ := hCw μ hmem2 hpos W
  set D : ℝ := sa16z_Diss d (s + 2 - d) p μ W with hD
  have hD0 : 0 ≤ D := ENNReal.toReal_nonneg
  set V : ℕ → ℝ := fun k => ∫ x, sa16sz_vn φ k x ^ p with hV
  have hV0 : ∀ k, 0 ≤ V k := fun k => integral_nonneg fun x => Real.rpow_nonneg (sa16sz_vn_nonneg φ k x) _
  have hVj : V j ≤ ∑ k ∈ Finset.range (j + 1), V k :=
    Finset.single_le_sum (f := V) (fun k _ => hV0 k) (Finset.mem_range.2 (by omega))
  have hSV : 0 ≤ ∑ k ∈ Finset.range (j + 1), V k := Finset.sum_nonneg fun k _ => hV0 k
  -- the pointwise splitting
  have hP' : ∀ {ψ : Euc d → ℝ}, IsCcInfty ψ → ∀ x : Euc d,
      sa16z_P s μ ψ x = -c * fracLap d (s + 2 - d) (fun y => μ y * ψ y) x +
        HRS.CZ.Hls.hlsg_c s * ∑ i : Fin d, sa16z_pv d (s + 2 - d) i (fun y => sa16z_dm μ i y * ψ y) x :=
    fun {ψ} hψ y => hP hμ hψ y
  have hsplit := fun x => sa16z_I_split hd hs0 hsd (cθ := cθ) hμs hφ hP' p j x
  set I : Euc d → ℝ := fun x => sa16sz_vn φ j x ^ (p - 2) * ∑ idx : Fin j → Fin d, partialDeriv idx φ x *
    partialDeriv idx (sa16z_P s μ φ) x with hI
  set IA : Euc d → ℝ := fun x => μ x * sa16sz_vn φ j x ^ (p - 2) * ∑ idx : Fin j → Fin d, partialDeriv idx φ x *
    fracLap d (s + 2 - d) (partialDeriv idx φ) x with hIA
  set IBd : Fin d → Euc d → ℝ := fun l => sa16z_IBd cA cs μ φ p (s + 2 - d) l j with hIBd
  set IE : Euc d → ℝ := fun x => sa16sz_vn φ j x ^ (p - 2) * ∑ idx : Fin j → Fin d, partialDeriv idx φ x *
    sa16z_Err s c cθ μ φ j idx x with hIE
  have hIAint : Integrable IA := hAint
  have hIi : Integrable I := sa16z_I_int hs0 hsd hμs hφ hp j
  have hIBi : ∀ l, Integrable (IBd l) := fun l => sa16z_IBd_int hd hs0 hsd hθ1 hμs hφ hp cA cs l j
  have hsp : ∀ x, I x = -c * IA x + ∑ l, IBd l x + IE x := hsplit
  have hIEint : Integrable IE := by
    have : IE = fun x => I x - (-c * IA x + ∑ l, IBd l x) := funext fun x => by rw [hsp x]; ring
    rw [this]
    exact hIi.sub ((hIAint.const_mul (-c)).add (integrable_finsetSum _ fun l _ => hIBi l))
  have hint_eq : ∫ x, I x = -c * (∫ x, IA x) + ∑ l, (∫ x, IBd l x) + (∫ x, IE x) := by
    have hS2 : Integrable (fun x => ∑ l, IBd l x) := integrable_finsetSum _ fun l _ => hIBi l
    have hS1 : Integrable (fun x => -c * IA x + ∑ l, IBd l x) := (hIAint.const_mul (-c)).add hS2
    have : (fun x => I x) = fun x => -c * IA x + ∑ l, IBd l x + IE x := funext hsp
    rw [this, integral_add hS1 hIEint, integral_add (hIAint.const_mul (-c)) hS2, integral_const_mul,
      integral_finsetSum _ fun l _ => hIBi l]
  -- leading term
  have hA : -c * ∫ x, IA x ≤ -c * sa16bd_convexityConst p * D + c * Cw * (3 * Λ) * V j := by
    have h1 : -c * ∫ x, IA x ≤ -c * sa16bd_convexityConst p * D + c * Cw * HRS.cbNorm 2 μ * V j :=
      hlead c hc.le
    refine h1.trans ?_
    have : c * Cw * HRS.cbNorm 2 μ * V j ≤ c * Cw * (3 * Λ) * V j :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcb2 (mul_nonneg hc.le hCw0)) (hV0 j)
    linarith
  -- absorbed terms
  have hB : ∀ l : Fin d, ∫ x, IBd l x ≤ ε * D + CB l * Bb2 * V j := fun l =>
    hCB l hφ hμs hpos (sa16z_Cb_mono (by omega) hCb)
  -- the error pairing
  have hSfin : sa16z_S p φ j ≠ ⊤ := by
    unfold sa16z_S
    exact (ENNReal.sum_lt_top.2 fun k _ => sa16z_JJ_lt_top hφ k).ne
  have hErr : ∀ idx : Fin j → Fin d, Integrable (fun x => |sa16z_Err s c cθ μ φ j idx x| ^ p) ∧
      ∫ x, |sa16z_Err s c cθ μ φ j idx x| ^ p ≤ (K * Λ * (sa16z_S p φ j).toReal) ^ p := by
    intro idx
    have hb := hK hμs hφ hΛ hCb idx
    have hne : ENNReal.ofReal (K * Λ) * sa16z_S p φ j ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hSfin
    have := sa16z_rpow_int_of_eLpNorm (sa16z_Err_aesm hd hs0 hsd hθ1 hμs hφ hP' j idx) hp0 hne hb
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hKΛ] at this
    exact this
  set h : Euc d → ℝ := fun x => ∑ idx : Fin j → Fin d, (((p - 1) / p) * sa16sz_vn φ j x ^ p +
    (1 / p) * |sa16z_Err s c cθ μ φ j idx x| ^ p) with hh
  have hyoung : ∀ x, IE x ≤ h x := fun x =>
    sa16z_young_pair hp (fun idx => partialDeriv idx φ x) (fun idx => sa16z_Err s c cθ μ φ j idx x)
  have hh0 : ∀ x, 0 ≤ h x := fun x => Finset.sum_nonneg fun idx _ => add_nonneg
    (mul_nonneg (div_nonneg (by linarith) hp0.le) (Real.rpow_nonneg (sa16sz_vn_nonneg φ j x) _))
    (mul_nonneg (by positivity) (Real.rpow_nonneg (abs_nonneg _) _))
  have hVint' : Integrable (fun x => sa16sz_vn φ j x ^ p) := hVint
  have hInt : ∀ idx : Fin j → Fin d, Integrable (fun x => ((p - 1) / p) * sa16sz_vn φ j x ^ p +
      (1 / p) * |sa16z_Err s c cθ μ φ j idx x| ^ p) := fun idx =>
    (hVint'.const_mul _).add ((hErr idx).1.const_mul _)
  have hhint : Integrable h := integrable_finsetSum _ fun idx _ => hInt idx
  have hE1 : ∫ x, IE x ≤ ∫ x, h x := sa16z_integral_le_of_le hyoung hhint hh0
  have hcard : (Fintype.card (Fin j → Fin d) : ℝ) = N := by simp [hN]
  have hE2 : ∫ x, h x ≤ N * ((p - 1) / p) * V j +
      (1 / p) * N * ((K * Λ) ^ p * ((sa16z_S p φ j).toReal) ^ p) := by
    have e : ∫ x, h x = ∑ idx : Fin j → Fin d, ((((p - 1) / p) * V j) +
        (1 / p) * ∫ x, |sa16z_Err s c cθ μ φ j idx x| ^ p) := by
      simp only [hh]
      rw [integral_finsetSum _ fun idx _ => hInt idx]
      refine Finset.sum_congr rfl fun idx _ => ?_
      rw [integral_add (hVint'.const_mul _) ((hErr idx).1.const_mul _), integral_const_mul, integral_const_mul]
    rw [e]
    calc ∑ idx : Fin j → Fin d, ((((p - 1) / p) * V j) + (1 / p) * ∫ x, |sa16z_Err s c cθ μ φ j idx x| ^ p)
        ≤ ∑ idx : Fin j → Fin d, ((((p - 1) / p) * V j) + (1 / p) * (K * Λ * (sa16z_S p φ j).toReal) ^ p) :=
          Finset.sum_le_sum fun idx _ => by
            have := (hErr idx).2
            have : 0 < 1 / p := by positivity
            nlinarith
      _ = N * ((p - 1) / p) * V j + (1 / p) * N * ((K * Λ) ^ p * ((sa16z_S p φ j).toReal) ^ p) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard,
            Real.mul_rpow hKΛ ENNReal.toReal_nonneg]
          ring
  have hSp := sa16z_S_rpow_le hφ j (by linarith : 1 ≤ p)
  have hE3 : (1 / p) * N * ((K * Λ) ^ p * ((sa16z_S p φ j).toReal) ^ p) ≤
      (1 / p) * N * ((K * Λ) ^ p * ((j : ℝ) + 1) ^ (p - 1)) * ∑ k ∈ Finset.range (j + 1), V k := by
    have h0 : 0 ≤ (1 / p) * N * (K * Λ) ^ p := mul_nonneg (mul_nonneg (by positivity) hNpos.le)
      (Real.rpow_nonneg hKΛ _)
    calc (1 / p) * N * ((K * Λ) ^ p * ((sa16z_S p φ j).toReal) ^ p)
        = ((1 / p) * N * (K * Λ) ^ p) * ((sa16z_S p φ j).toReal) ^ p := by ring
      _ ≤ ((1 / p) * N * (K * Λ) ^ p) * (((j : ℝ) + 1) ^ (p - 1) * ∑ k ∈ Finset.range (j + 1), V k) :=
          mul_le_mul_of_nonneg_left hSp h0
      _ = _ := by ring
  -- assemble
  have hsumB : ∑ l : Fin d, ∫ x, IBd l x ≤ c * sa16bd_convexityConst p * D + (∑ l, CB l) * Bb2 * V j := by
    calc ∑ l : Fin d, ∫ x, IBd l x ≤ ∑ l : Fin d, (ε * D + CB l * Bb2 * V j) := Finset.sum_le_sum fun l _ => hB l
      _ = (d : ℝ) * ε * D + (∑ l, CB l) * Bb2 * V j := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← Finset.sum_mul, ← Finset.sum_mul]
          ring
      _ = _ := by
          have : (d : ℝ) * ε = c * sa16bd_convexityConst p := by rw [hε]; field_simp
          rw [this]
  have hVj' : 0 ≤ ∑ k ∈ Finset.range (j + 1), V k := hSV
  have hfinal : ∫ x, I x ≤ (c * Cw * (3 * Λ) + (∑ l, CB l) * Bb2 + N * ((p - 1) / p) +
      (1 / p) * N * ((K * Λ) ^ p * ((j : ℝ) + 1) ^ (p - 1))) * ∑ k ∈ Finset.range (j + 1), V k := by
    rw [hint_eq]
    have hc1 : 0 ≤ c * Cw * (3 * Λ) := by positivity
    have hc2 : 0 ≤ (∑ l, CB l) * Bb2 := mul_nonneg hCBs hBb2pos.le
    have hc3 : 0 ≤ N * ((p - 1) / p) := mul_nonneg hNpos.le (div_nonneg (by linarith) hp0.le)
    have e1 : c * Cw * (3 * Λ) * V j ≤ c * Cw * (3 * Λ) * ∑ k ∈ Finset.range (j + 1), V k :=
      mul_le_mul_of_nonneg_left hVj hc1
    have e2 : (∑ l, CB l) * Bb2 * V j ≤ (∑ l, CB l) * Bb2 * ∑ k ∈ Finset.range (j + 1), V k :=
      mul_le_mul_of_nonneg_left hVj hc2
    have e3 : N * ((p - 1) / p) * V j ≤ N * ((p - 1) / p) * ∑ k ∈ Finset.range (j + 1), V k :=
      mul_le_mul_of_nonneg_left hVj hc3
    nlinarith [hA, hsumB, hE1, hE2, hE3, e1, e2, e3]
  exact hfinal
