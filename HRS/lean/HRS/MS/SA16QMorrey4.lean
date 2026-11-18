import HRS.MS.SA16QMorrey3

/-!
# S.A.16 (SA16Q), E11: `compact_cb2_bound`

Dense-domain Morrey estimate `‖u‖_{C_b^2} ≤ C ‖u‖_{W^{m,p}}`, `m > 2 + d/p`, for `u ∈ C_c^∞`.
From `sa16q_morrey_key` applied to `u`, `Du`, `D²u`; the derivative norms are `L^p`-bounded by the
jet norm `wNormE m p u = ‖wJet m u‖_{L^p}` (`sa16j_wNormE_eq`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Nat

namespace HRS.Whole.AppendixA.Phase2SA16Q
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixA.Phase2SA16

section Assembly
variable {d : ℕ}

/-- `L^p` norm of an iterated derivative by the jet norm -/
lemma sa16q_iter_lp {u : Euc d → ℝ} (hu : ContDiff ℝ ∞ u) (hd : 1 ≤ d) (p : ℝ) {m l : ℕ} (hl : l ≤ m) :
    eLpNorm (fun y => ‖iteratedFDeriv ℝ l u y‖) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal ((d : ℝ) ^ m) * eLpNorm (wJet m u) (ENNReal.ofReal p) volume := by
  have hpt : ∀ y, ‖iteratedFDeriv ℝ l u y‖ ≤ (d : ℝ) ^ m * ‖wJet m u y‖ := by
    intro y
    refine (sa16j_norm_iter_le u y l).trans ?_
    have h1 : ∀ r : Fin l → Fin d, |partialDeriv r u y| ≤ ‖wJet m u y‖ :=
      fun r => sa16j_pd_le_jet m u y hl r
    calc ∑ r : Fin l → Fin d, |partialDeriv r u y|
        ≤ ∑ r : Fin l → Fin d, ‖wJet m u y‖ := Finset.sum_le_sum fun r _ => h1 r
      _ = (d : ℝ) ^ l * ‖wJet m u y‖ := by simp [Finset.sum_const, Fintype.card_fun]
      _ ≤ (d : ℝ) ^ m * ‖wJet m u y‖ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by exact_mod_cast hd) hl) (norm_nonneg _)
  have hmeas : AEStronglyMeasurable (fun y => ‖iteratedFDeriv ℝ l u y‖) volume :=
    ((hu.continuous_iteratedFDeriv (m := l) (by exact_mod_cast le_top)).norm).aestronglyMeasurable
  refine (eLpNorm_mono_ae_real hmeas (Eventually.of_forall fun y => (norm_norm _).le.trans (hpt y))).trans ?_
  have : (fun y => (d : ℝ) ^ m * ‖wJet m u y‖) = (d : ℝ) ^ m • (fun y => ‖wJet m u y‖) := by
    funext y; simp
  rw [this, eLpNorm_const_smul, eLpNorm_norm _ (sa16j_jet_cont hu m).aestronglyMeasurable]
  refine le_of_eq ?_
  rw [Real.enorm_eq_ofReal (by positivity)]

lemma sa16q_sup_from_key {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {u : Euc d → ℝ}
    (hu : ContDiff ℝ ∞ u) (hd : 1 ≤ d) (p : ℝ) {m : ℕ} (w : Euc d → F) (j n : ℕ) (hnj : n + j ≤ m)
    (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ x, ‖w x‖ₑ ≤ ENNReal.ofReal C * ∑ k ∈ Finset.range (n + 1),
      eLpNorm (fun y => ‖iteratedFDeriv ℝ k w y‖) (ENNReal.ofReal p) volume)
    (hnorm : ∀ k y, ‖iteratedFDeriv ℝ k w y‖ = ‖iteratedFDeriv ℝ (k + j) u y‖) (x : Euc d) :
    ‖iteratedFDeriv ℝ j u x‖ₑ ≤ ENNReal.ofReal (C * ((n : ℝ) + 1) * (d : ℝ) ^ m) *
      eLpNorm (wJet m u) (ENNReal.ofReal p) volume := by
  have hwj : ‖w x‖ = ‖iteratedFDeriv ℝ j u x‖ := by
    have := hnorm 0 x
    rwa [norm_iteratedFDeriv_zero, zero_add] at this
  have hwe : ‖iteratedFDeriv ℝ j u x‖ₑ = ‖w x‖ₑ := by
    rw [← ofReal_norm_eq_enorm, ← hwj, ofReal_norm_eq_enorm]
  rw [hwe]
  refine (hC x).trans ?_
  have hsum : ∑ k ∈ Finset.range (n + 1),
      eLpNorm (fun y => ‖iteratedFDeriv ℝ k w y‖) (ENNReal.ofReal p) volume ≤
      ((n : ℝ≥0∞) + 1) * (ENNReal.ofReal ((d : ℝ) ^ m) *
        eLpNorm (wJet m u) (ENNReal.ofReal p) volume) := by
    calc ∑ k ∈ Finset.range (n + 1),
          eLpNorm (fun y => ‖iteratedFDeriv ℝ k w y‖) (ENNReal.ofReal p) volume
        ≤ ∑ k ∈ Finset.range (n + 1), (ENNReal.ofReal ((d : ℝ) ^ m) *
            eLpNorm (wJet m u) (ENNReal.ofReal p) volume) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hk' : k ≤ n := by have := Finset.mem_range.1 hk; omega
          have : (fun y => ‖iteratedFDeriv ℝ k w y‖) = fun y => ‖iteratedFDeriv ℝ (k + j) u y‖ :=
            funext fun y => hnorm k y
          rw [this]
          exact sa16q_iter_lp hu hd p (by omega)
      _ = ((n : ℝ≥0∞) + 1) * (ENNReal.ofReal ((d : ℝ) ^ m) *
            eLpNorm (wJet m u) (ENNReal.ofReal p) volume) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  calc ENNReal.ofReal C * ∑ k ∈ Finset.range (n + 1),
        eLpNorm (fun y => ‖iteratedFDeriv ℝ k w y‖) (ENNReal.ofReal p) volume
      ≤ ENNReal.ofReal C * (((n : ℝ≥0∞) + 1) * (ENNReal.ofReal ((d : ℝ) ^ m) *
        eLpNorm (wJet m u) (ENNReal.ofReal p) volume)) := by gcongr
    _ = ENNReal.ofReal (C * ((n : ℝ) + 1) * (d : ℝ) ^ m) *
          eLpNorm (wJet m u) (ENNReal.ofReal p) volume := by
        have : ((n : ℝ≥0∞) + 1) = ENNReal.ofReal ((n : ℝ) + 1) := by
          rw [ENNReal.ofReal_add (by positivity) zero_le_one]; simp
        rw [this, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
        ring

end Assembly

end HRS.Whole.AppendixA.Phase2SA16Q

namespace HRS.Whole.AppendixA.Phase2SA16Evolution
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixA.Phase2SA16 HRS.Whole.AppendixA.Phase2SA16Q

/-- E11: the dense-domain Morrey estimate, separated from completion. -/
theorem compact_cb2_bound (d m : ℕ) (hd : 1 ≤ d) (p : ℝ)
    [Fact (2 ≤ p)] (hmp : 2 + (d : ℝ) / p < m) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : Euc d → ℝ, IsCcInfty u →
      MemCb 2 u ∧ ENNReal.ofReal (cbNorm 2 u) ≤
        ENNReal.ofReal C*wNormE m p u := by
  have hp2 : 2 ≤ p := Fact.out
  have hp : 1 < p := by linarith
  have hp0 : 0 < p := by linarith
  have hdp : (0 : ℝ) ≤ (d : ℝ) / p := by positivity
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := by
    have : 2 < m := by
      have : (2 : ℝ) < m := by linarith
      exact_mod_cast this
    exact ⟨m - 2, by omega⟩
  have hm' : (d : ℝ) / p < m' := by
    have : (2 : ℝ) + d / p < (m' : ℝ) + 2 := by exact_mod_cast hmp
    linarith
  have hm'1 : 1 ≤ m' := by
    have : (0 : ℝ) < m' := lt_of_le_of_lt hdp hm'
    exact_mod_cast this
  obtain ⟨C0, hC0, h0⟩ := sa16q_morrey_key d hd p hp (m' + 2) (by omega) (by
    have : (d : ℝ) / p < ((m' + 2 : ℕ) : ℝ) := by push_cast; linarith
    exact this)
  obtain ⟨C1, hC1, h1⟩ := sa16q_morrey_key d hd p hp (m' + 1) (by omega) (by
    have : (d : ℝ) / p < ((m' + 1 : ℕ) : ℝ) := by push_cast; linarith
    exact this)
  obtain ⟨C2, hC2, h2⟩ := sa16q_morrey_key d hd p hp m' hm'1 hm'
  set K0 : ℝ := C0 * (((m' + 2 : ℕ) : ℝ) + 1) * (d : ℝ) ^ (m' + 2) with hK0
  set K1 : ℝ := C1 * (((m' + 1 : ℕ) : ℝ) + 1) * (d : ℝ) ^ (m' + 2) with hK1
  set K2 : ℝ := C2 * ((m' : ℝ) + 1) * (d : ℝ) ^ (m' + 2) with hK2
  have hK0p : 0 ≤ K0 := by positivity
  have hK1p : 0 ≤ K1 := by positivity
  have hK2p : 0 ≤ K2 := by positivity
  refine ⟨K0 + K1 + K2 + 1, by positivity, fun u hu => ?_⟩
  obtain ⟨hus, huc⟩ := hu
  -- the weak norm
  have hS : MemLp (sa16j_S d (m' + 2) u) (ENNReal.ofReal p) volume := by
    unfold sa16j_S
    refine memLp_finsetSum _ fun j _ => ?_
    exact (((hus.continuous_iteratedFDeriv (m := j) (by exact_mod_cast le_top)).norm).memLp_of_hasCompactSupport
      (huc.iteratedFDeriv j).norm)
  have hW : wNormE (m' + 2) p u = eLpNorm (wJet (m' + 2) u) (ENNReal.ofReal p) volume :=
    sa16j_wNormE_eq d (m' + 2) p hus hS
  set W : ℝ≥0∞ := eLpNorm (wJet (m' + 2) u) (ENNReal.ofReal p) volume with hWdef
  have hWt : W ≠ ⊤ := (sa16j_jet_memLp d (m' + 2) p hus hS).eLpNorm_lt_top.ne
  -- sup bounds
  have hs0 : ∀ x, ‖iteratedFDeriv ℝ 0 u x‖ₑ ≤ ENNReal.ofReal K0 * W := fun x => by
    refine sa16q_sup_from_key (F := ℝ) hus hd p u 0 (m' + 2) (by omega) C0 hC0.le
      (fun x => h0 ℝ u hus x) (fun k y => by simp) x
  have hfd1 : ContDiff ℝ ∞ (fderiv ℝ u) := hus.fderiv_right (by simp)
  have hfd2 : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ u)) := hfd1.fderiv_right (by simp)
  have hs1 : ∀ x, ‖iteratedFDeriv ℝ 1 u x‖ₑ ≤ ENNReal.ofReal K1 * W := fun x => by
    refine sa16q_sup_from_key (F := Euc d →L[ℝ] ℝ) hus hd p (fderiv ℝ u) 1 (m' + 1) (by omega) C1 hC1.le
      (fun x => h1 _ (fderiv ℝ u) hfd1 x) (fun k y => norm_iteratedFDeriv_fderiv) x
  have hs2 : ∀ x, ‖iteratedFDeriv ℝ 2 u x‖ₑ ≤ ENNReal.ofReal K2 * W := fun x => by
    refine sa16q_sup_from_key (F := Euc d →L[ℝ] (Euc d →L[ℝ] ℝ)) hus hd p (fderiv ℝ (fderiv ℝ u)) 2 m' (by omega)
      C2 hC2.le (fun x => h2 _ (fderiv ℝ (fderiv ℝ u)) hfd2 x)
      (fun k y => by rw [norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_fderiv]) x
  have hbd : ∀ (j : ℕ) (K : ℝ), 0 ≤ K → (∀ x, ‖iteratedFDeriv ℝ j u x‖ₑ ≤ ENNReal.ofReal K * W) →
      ∀ x, ‖iteratedFDeriv ℝ j u x‖ ≤ K * W.toReal := by
    intro j K hK h x
    have h1 := h x
    rw [← ofReal_norm_eq_enorm] at h1
    have hW' : W = ENNReal.ofReal W.toReal := (ENNReal.ofReal_toReal hWt).symm
    rw [hW', ← ENNReal.ofReal_mul hK] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hK ENNReal.toReal_nonneg)).1 h1
  have hMem : MemCb 2 u := by
    refine ⟨(contDiff_infty.1 hus) 2, fun j hj => ?_⟩
    obtain ⟨B, hB⟩ := ((hus.continuous_iteratedFDeriv (m := j)
      (by exact_mod_cast le_top)).norm).bounded_above_of_compact_support (huc.iteratedFDeriv j).norm
    exact ⟨B, by rintro _ ⟨x, rfl⟩; simpa using hB x⟩
  refine ⟨hMem, ?_⟩
  have hcb : cbNorm 2 u ≤ (K0 + K1 + K2) * W.toReal := by
    unfold cbNorm
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    have a0 : ⨆ x, ‖iteratedFDeriv ℝ 0 u x‖ ≤ K0 * W.toReal := ciSup_le (hbd 0 K0 hK0p hs0)
    have a1 : ⨆ x, ‖iteratedFDeriv ℝ 1 u x‖ ≤ K1 * W.toReal := ciSup_le (hbd 1 K1 hK1p hs1)
    have a2 : ⨆ x, ‖iteratedFDeriv ℝ 2 u x‖ ≤ K2 * W.toReal := ciSup_le (hbd 2 K2 hK2p hs2)
    linarith
  rw [hW]
  calc ENNReal.ofReal (cbNorm 2 u) ≤ ENNReal.ofReal ((K0 + K1 + K2) * W.toReal) :=
        ENNReal.ofReal_le_ofReal hcb
    _ = ENNReal.ofReal (K0 + K1 + K2) * W := by
        rw [ENNReal.ofReal_mul (add_nonneg (add_nonneg hK0p hK1p) hK2p), ENNReal.ofReal_toReal hWt]
    _ ≤ ENNReal.ofReal (K0 + K1 + K2 + 1) * W :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl

end HRS.Whole.AppendixA.Phase2SA16Evolution
