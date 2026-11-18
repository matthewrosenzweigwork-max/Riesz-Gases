import HRS.MS.SA12X2G

/-!
# S.A.12 N9 (SA12X2), part H: the one-sided energy bound for one index tuple (symmetric branch)

`-∫ ω² ∂^{idx}F ∂^{idx}𝒢 ≤ A₁ ∫ W Y` for `d - 2 < s ≤ d - 1`, `Sym M ≤ 0`, `a ≥ 0`, combining
`sa12x2_top` (N5 + N2) and `sa12x2_lower` (first-order local bound).
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqT3

variable {d : ℕ}

/-- The two `L²` comparisons with the weighted jet energy. -/
theorem sa12x2_l2_cmp {c : Euc d} {R : ℝ} {om a W u : Euc d → ℝ} {Ka : ℝ} {e : ℝ}
    (hom : Continuous om) (hW : Continuous W) (hWcs : HasCompactSupport W)
    (hWom : ∀ x, om x ^ 2 ≤ W x) (huc : Continuous u)
    (hKa : ∀ x, |a x| ≤ Ka) (hWa : ∀ x, a x ≠ 0 → 1 ≤ W x)
    (hue : ∫ x, W x * u x ^ 2 ≤ e) (hac : Continuous a) (hacs : HasCompactSupport a)
    (homs : HasCompactSupport om) :
    (∫ x, (om x * u x) ^ 2 ≤ e) ∧ (∫ x, (a x * u x) ^ 2 ≤ Ka ^ 2 * e) := by
  have hW0 : ∀ x, 0 ≤ W x := fun x => (sq_nonneg _).trans (hWom x)
  have hWui : Integrable (fun x => W x * u x ^ 2) volume :=
    (hW.mul (huc.pow 2)).integrable_of_hasCompactSupport hWcs.mul_right
  have hint2 : ∀ {v : Euc d → ℝ}, Continuous v → HasCompactSupport v → Integrable (fun x => v x ^ 2) volume :=
    fun {v} hv hvc => Continuous.integrable_of_hasCompactSupport (f := fun x => v x ^ 2) (hv.pow 2)
      (hvc.comp_left (g := fun t : ℝ => t ^ 2) (by simp))
  refine ⟨?_, ?_⟩
  · refine le_trans (integral_mono (hint2 (hom.mul huc) homs.mul_right) hWui fun x => ?_) hue
    calc (om x * u x) ^ 2 = om x ^ 2 * u x ^ 2 := by ring
      _ ≤ W x * u x ^ 2 := mul_le_mul_of_nonneg_right (hWom x) (sq_nonneg _)
  · have hsq : ∀ y, (a y * u y) ^ 2 ≤ Ka ^ 2 * (W y * u y ^ 2) := by
      intro y
      by_cases hy : a y = 0
      · rw [hy, zero_mul]
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
        exact mul_nonneg (sq_nonneg _) (mul_nonneg (hW0 y) (sq_nonneg _))
      · have hW1 := hWa y hy
        have h1 : a y ^ 2 ≤ Ka ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hKa y) 2
        calc (a y * u y) ^ 2 = a y ^ 2 * u y ^ 2 := by ring
          _ ≤ Ka ^ 2 * (1 * u y ^ 2) := by rw [one_mul]; gcongr
          _ ≤ Ka ^ 2 * (W y * u y ^ 2) := by gcongr
    calc ∫ x, (a x * u x) ^ 2 ≤ ∫ x, Ka ^ 2 * (W x * u x ^ 2) :=
          integral_mono (hint2 (hac.mul huc) hacs.mul_right) (hWui.const_mul _) hsq
      _ = Ka ^ 2 * ∫ x, W x * u x ^ 2 := integral_const_mul _ _
      _ ≤ Ka ^ 2 * e := by gcongr

theorem sa12x2_idx_lower (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs2 : (d : ℝ) - 2 < s)
    (hs1 : s ≤ (d : ℝ) - 1) (m : ℕ) (hm : 1 ≤ m) (MB Ka R Kw : ℝ) (hR : 1 ≤ R)
    (hKa0 : 0 ≤ Ka) (hKw0 : 0 ≤ Kw) :
    ∃ A1 : ℝ, 0 ≤ A1 ∧ ∀ (c : Euc d) (om a W F : Euc d → ℝ) (M : Matrix (Fin d) (Fin d) ℝ),
      PDE.MatBound MB M → Torus.SymNonpos M → Continuous om → HasCompactSupport om →
      Function.support om ⊆ closedBall c R → (∀ x, |om x| ≤ 1) → ContDiff ℝ 2 om →
      (∀ k ≤ 2, ∀ x, ‖iteratedFDeriv ℝ k om x‖ ≤ Kw) →
      Continuous W → HasCompactSupport W → (∀ x, om x ^ 2 ≤ W x) →
      ContDiff ℝ (m + 1) a → HasCompactSupport a → Function.support a ⊆ closedBall c R →
      (∀ k ≤ m + 1, ∀ x, ‖iteratedFDeriv ℝ k a x‖ ≤ Ka) → (∀ x, 0 ≤ a x) →
      (∀ x ∈ tsupport a, 1 ≤ W x) →
      ContDiff ℝ ∞ F → ∀ (n : ℕ), n ≤ m → ∀ (idx : Fin n → Fin d),
      -(∫ x, om x ^ 2 * (partialDeriv idx F x * partialDeriv idx (eucNonlocal s M a F) x)) ≤
        A1 * ∫ x, W x * sa12z3_Y m F x := by
  obtain ⟨A2, hA2, hlow⟩ := sa12x2_lower hd hs0 hs1 m hm MB Ka R hR
  obtain ⟨A3, hA3, htop⟩ := sa12x2_top hd hs0 hs2 hs1 MB R (3 * Ka) ((2 + 1) * Kw) hR
    (by positivity) (by positivity)
  refine ⟨A2 + A3, add_nonneg hA2 hA3, ?_⟩
  intro c om a W F M hM hSN hom homc homs hom1 hom2 hKw hW hWcs hWom ha hac has hKa h0 hWa hF n hn idx
  have hMB : ∀ i j, |M i j| ≤ MB := hM
  have hsd : s < d := by linarith
  set u : Euc d → ℝ := partialDeriv idx F with hu
  have hu_inf : ContDiff ℝ ∞ u := sa12z3_pd_contDiff_inf hF idx
  have huc : Continuous u := hu_inf.continuous
  set Y : Euc d → ℝ := sa12z3_Y m F with hY
  have hYc : Continuous Y := by
    rw [hY]
    unfold sa12z3_Y
    refine continuous_finsetSum _ fun r _ => continuous_finsetSum _ fun γ _ => ?_
    exact ((sa12z3_pd_contDiff_inf hF γ).continuous).pow 2
  have hW0 : ∀ x, 0 ≤ W x := fun x => (sq_nonneg _).trans (hWom x)
  have hWYi : Integrable (fun x => W x * Y x) volume :=
    (hW.mul hYc).integrable_of_hasCompactSupport hWcs.mul_right
  set e : ℝ := ∫ x, W x * Y x with he
  have he0 : 0 ≤ e := integral_nonneg fun x => mul_nonneg (hW0 x) (sa12z3_Y_nonneg _ _ _)
  have hWui : Integrable (fun x => W x * u x ^ 2) volume :=
    (hW.mul (huc.pow 2)).integrable_of_hasCompactSupport hWcs.mul_right
  have hue : ∫ x, W x * u x ^ 2 ≤ e :=
    integral_mono hWui hWYi fun x => mul_le_mul_of_nonneg_left (sa12z3_pd_sq_le_Y hn F x idx) (hW0 x)
  have ha2 : ContDiff ℝ 2 a := ha.of_le (by exact_mod_cast (by omega : 2 ≤ m + 1))
  have hKaabs : ∀ y, |a y| ≤ Ka := fun y => by
    have := hKa 0 (Nat.zero_le _) y
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hWa' : ∀ x, a x ≠ 0 → 1 ≤ W x := fun x hx => hWa x (subset_tsupport _ hx)
  obtain ⟨hc1, hc2⟩ := sa12x2_l2_cmp (c := c) (R := R) hom hW hWcs hWom huc hKaabs hWa' hue
    ha2.continuous hac homc
  have hc2' : ∫ x, (a x * u x) ^ 2 ≤ (3 * Ka) ^ 2 * e := by
    refine hc2.trans ?_
    have : Ka ^ 2 ≤ (3 * Ka) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right this he0
  have hmemom : MemCb 2 om := sa12x2_memCb_of_bdd hom2 hKw
  have hmema : MemCb 2 a := sa12x2_memCb_of_bdd (ha.of_le (by exact_mod_cast (by omega : 2 ≤ m + 1)))
    (fun j hj x => hKa j (by omega) x)
  have hcbom : cbNorm 2 om ≤ (2 + 1) * Kw := by exact_mod_cast sa12x2_cb_le hKw
  have hcba : cbNorm 2 a ≤ 3 * Ka := by
    have := sa12x2_cb_le (k := 2) (f := a) (K := Ka) (fun j hj x => hKa j (by omega) x)
    norm_num at this ⊢
    linarith
  obtain ⟨Z, hZ, hZe⟩ := hlow c om a W F M hMB hom homc homs hom1 hW hWcs hWom ha hac has hKa hWa hF n hn idx
  have hT := htop c om a u M e hMB hSN hmemom hcbom homc homs hmema hcba h0 hac has
    (sa12z3_cd_of_inf hu_inf 2) he0 hc1 hc2'
  rw [hZe]
  have := neg_abs_le Z
  nlinarith [hZ, hT]

end HRS.MH.AdjointRd.Phase2SA12Near
